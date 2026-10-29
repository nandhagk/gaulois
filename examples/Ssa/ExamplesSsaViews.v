(** * SSA graph and variable adapters

    The adapters retain source edge occurrences and their ordered operands.
    For example, two branches to one label keep distinct slots and argument lists.
    Builds on: ExamplesSsaActivation, ExamplesSsaBridge, ViewsSsa and AnalysesDemand. *)

From Stdlib Require Import List ZArith Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderBasic OrderPointwise.
From Gaulois.Graph Require Import GraphCore GraphDominance GraphEdgeDominance.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsSsaPoints ViewsEffects
  ViewsAgreement ViewsDominated.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesDemand.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaActivation ExamplesSsaBridge.
Import List.ListNotations.
Local Open Scope nat_scope.

(** An edge slot preserves one occurrence of a terminator target. *)
Record ssa_edge : Type := SsaEdge {
  esrc : label;
  edst : label;
  eslot : nat
}.

Definition ssa_edge_encoding : encoding ssa_edge.
Proof.
  pose (E := pair_encoding nat_encoding (pair_encoding nat_encoding nat_encoding)).
  refine (Encoding _ (fun e => encode E (esrc e, (edst e, eslot e))) _).
  intros [src dst slot] [src' dst' slot'] Heq.
  apply (encode_injective E) in Heq; cbn in Heq; inversion Heq; reflexivity.
Defined.

Definition ssa_blocks (P : program) (f : func) : list (label * ssa_block) :=
  match find_func P f with
  | Some fd => blocks fd
  | None => []
  end.

Definition ssa_entries (P : program) (f : func) : list label :=
  match find_func P f with
  | Some fd => [fentry fd]
  | None => []
  end.

Fixpoint ssa_enumerate {A} (start : nat) (xs : list A) : list (nat * A) :=
  match xs with
  | [] => []
  | x :: rest => (start, x) :: ssa_enumerate (S start) rest
  end.

Definition ssa_block_edges (l : label) (b : ssa_block) : list ssa_edge :=
  map (fun p => SsaEdge l (fst (snd p)) (fst p)) (ssa_enumerate 0 (term_edges (bterm b))).

Definition ssa_block_graph (P : program) (f : func) : Graph.t label ssa_edge :=
  let bs := ssa_blocks P f in
  let outgoing := Map.of_list nat_encoding
    (map (fun lb => (fst lb, ssa_block_edges (fst lb) (snd lb))) bs) in
  Graph.Make (ssa_entries P f) (map fst bs) (ssa_get nat_encoding outgoing []) esrc edst.

(** Every source value defined by the function occurs once in this canonical universe. *)
Definition values_of (P : program) (f : func) : list vid :=
  FinSet.elements (FinSet.of_list nat_encoding
    (flat_map (fun lb => block_defs (snd lb)) (ssa_blocks P f))).

(** Instructions and terminators share one conservative effects dictionary. *)
Inductive instr_or_term : Type :=
  | AnInstr (i : instr)
  | ATerm (t : terminator).

(** A call site is the function and block that contain its terminator. *)
Definition call_site : Type := (func * label)%type.

(** The flags retain possible full-machine memory traps and resource stops. *)
Definition ssa_effects : effects instr_or_term :=
  {| reads := fun it =>
       match it with
       | AnInstr (IAlloc _ _ | IFree _ | ILoad _ _ _ _ | IStore _ _ _) => true
       | _ => false
       end;
     writes := fun it =>
       match it with
       | AnInstr (IFree _ | IStore _ _ _) => true
       | _ => false
       end;
     may_trap := fun it =>
       match it with
       | AnInstr (IOp _ (OBin _ BDivU | OExt _) _ | IFree _ | ILoad _ _ _ _ |
           IStore _ _ _) | ATerm (TCall _ _ _) => true
       | _ => false
       end;
     may_diverge := fun it =>
       match it with
       | ATerm (TCall _ _ _) => true
       | _ => false
       end;
     may_stop := fun it =>
       match it with
       | AnInstr (IAlloc _ _) | ATerm (TCall _ _ _) => true
       | _ => false
       end;
     allocates := fun it =>
       match it with
       | AnInstr (IAlloc _ _) => true
       | _ => false
       end;
     frees := fun it =>
       match it with
       | AnInstr (IFree _) => true
       | _ => false
       end;
     calls := fun it =>
       match it with
       | ATerm (TCall _ _ _ | TRet _) => true
       | _ => false
       end;
     observes := fun it =>
       match it with
       | AnInstr (IOutput _) | ATerm (TRet _) => true
       | _ => false
       end |}.

Definition ssa_guard (t : terminator) (slot : nat) : list (condition vid cval) :=
  match t with
  | TBr c _ _ _ _ =>
    match slot with
    | 0 => [Condition c GTrue]
    | 1 => [Condition c GFalse]
    | _ => []
    end
  | TSwitch c cases _ _ =>
    match nth_error cases slot with
    | Some ((key, _), _) => [Condition c (GConst (VInt W32 (word_wrap W32 key)))]
    | None => map (fun entry =>
        Condition c (GNotConst (VInt W32 (word_wrap W32 (fst (fst entry)))))) cases
    end
  | _ => []
  end.

Definition ssa_selected_uses (t : terminator) (args : list vid) : list vid :=
  match t with
  | TJump _ _ => args
  | TBr c _ _ _ _ | TSwitch c _ _ _ => c :: args
  | TCall _ _ _ | TRet _ => term_uses t
  end.

Record ssa_block_payload : Type := SsaBlockPayload {
  sbp_args : list vid;
  sbp_guard : list (condition vid cval)
}.

(** The reference rows specify guards by their original edge slots. *)
Local Definition ssa_block_rows_reference (l : label) (b : ssa_block)
    : list (ssa_edge * ssa_block_payload) :=
  map (fun p =>
    let slot := fst p in
    let edge := snd p in
    (SsaEdge l (fst edge) slot, SsaBlockPayload (snd edge) (ssa_guard (bterm b) slot)))
    (ssa_enumerate 0 (term_edges (bterm b))).

Local Fixpoint ssa_switch_case_rows (l : label) (c : vid) (slot : nat)
    (cases : list (Z * label * list vid)) : list (ssa_edge * ssa_block_payload) :=
  match cases with
  | [] => []
  | ((key, dst), args) :: rest =>
    (SsaEdge l dst slot,
      SsaBlockPayload args [Condition c (GConst (VInt W32 (word_wrap W32 key)))]) ::
      ssa_switch_case_rows l c (S slot) rest
  end.

(** Switch guards are emitted with their cases; default exclusions are constructed once. *)
Definition ssa_block_rows (l : label) (b : ssa_block)
    : list (ssa_edge * ssa_block_payload) :=
  match bterm b with
  | TSwitch c cases d da =>
    ssa_switch_case_rows l c 0 cases ++
      [(SsaEdge l d (length cases), SsaBlockPayload da
        (map (fun entry =>
          Condition c (GNotConst (VInt W32 (word_wrap W32 (fst (fst entry)))))) cases))]
  | _ => ssa_block_rows_reference l b
  end.

Definition ssa_block_payloads (P : program) (f : func) : Map.t ssa_edge ssa_block_payload :=
  Map.of_list ssa_edge_encoding
    (flat_map (fun lb => ssa_block_rows (fst lb) (snd lb)) (ssa_blocks P f)).

Definition ssa_parameter_rows (call_targets : FinSet.t label) (l : label) (b : ssa_block)
    : list (vid * (label * definition label vid sop)) :=
  map (fun p => (fst (snd p), (l,
    if FinSet.mem nat_encoding l call_targets then Arbitrary else Param l (fst p))))
    (ssa_enumerate 0 (bparams b)).

Definition ssa_instruction_rows (l : label) (i : instr)
    : list (vid * (label * definition label vid sop)) :=
  match i with
  | IOp x o args => [(x, (l, Op o args))]
  | IAlloc x _ | ILoad x _ _ _ => [(x, (l, Arbitrary))]
  | _ => []
  end.

Definition ssa_definitions (P : program) (f : func)
    : Map.t vid (label * definition label vid sop) :=
  let bs := ssa_blocks P f in
  let call_targets := FinSet.of_list nat_encoding (flat_map (fun lb =>
    match bterm (snd lb) with
    | TCall _ _ k => [k]
    | _ => []
    end) bs) in
  Map.of_list nat_encoding (flat_map (fun lb =>
    ssa_parameter_rows call_targets (fst lb) (snd lb) ++
    flat_map (ssa_instruction_rows (fst lb)) (bbody (snd lb))) bs).

Definition ssa_block_taken (P : program) (f : func) (a : astate)
    (tr : list event) (a' : astate) (e : ssa_edge) : Prop :=
  exists fd b,
    find_func P f = Some fd /\ find_block fd (alabel a) = Some b /\
    apc a = length (bbody b) /\ esrc e = alabel a /\ edst e = alabel a' /\
    apc a' = 0 /\ In e (ssa_block_edges (alabel a) b) /\
    ssa_term_slot (aenv a) (bterm b) = Some (eslot e).

(** The block adapter uses the source environment and retains empty raw call arguments. *)
Definition ssa_block_view (ext : nat -> list cval -> option cval) (P : program) (f : func)
    : ssa_view astate event label ssa_edge vid sop cval :=
  let definitions := ssa_definitions P f in
  let parameter_index := Map.of_list nat_encoding (map (fun lb =>
    (fst lb, map fst (bparams (snd lb)))) (ssa_blocks P f)) in
  let edge_index := ssa_block_payloads P f in
  {| base := GraphView (ssa_block_graph P f) alabel (ssa_block_taken P f)
       (fun a _ a' => alabel a' = alabel a /\ apc a' = S (apc a));
     def := fun x => snd (ssa_get nat_encoding definitions (0, Arbitrary) x);
     home := fun x => fst (ssa_get nat_encoding definitions (0, Arbitrary) x);
     params := ssa_get nat_encoding parameter_index [];
     edge_args := fun e => sbp_args (ssa_get ssa_edge_encoding edge_index
       (SsaBlockPayload [] []) e);
     edge_guard := fun e => sbp_guard (ssa_get ssa_edge_encoding edge_index
       (SsaBlockPayload [] []) e);
     val := aenv;
     ViewsSsa.op_eval := op_eval ext;
     truth := ssa_truth |}.

(** Integer truth in the block adapter is exactly nonzero payload truth. *)
Theorem ssa_truth_nonzero (ext : nat -> list cval -> option cval) (P : program) (f : func)
    (w : iw) (z : Z) :
  truth (ssa_block_view ext P f) (VInt w z) = negb (Z.eqb z 0).
Proof.
  reflexivity.
Qed.

Local Lemma ssa_enumerate_length {A} (xs : list A) start :
  length (ssa_enumerate start xs) = length xs.
Proof.
  revert start; induction xs; intro start; cbn; [reflexivity|rewrite IHxs; reflexivity].
Qed.

Local Lemma ssa_enumerate_lookup {A} (xs : list A) start n x :
  nth_error xs n = Some x -> nth_error (ssa_enumerate start xs) n = Some (start + n, x).
Proof.
  revert start n; induction xs as [|a xs IH]; intros start [|n] Hnth;
    cbn in Hnth; try discriminate.
  - injection Hnth as <-; cbn; f_equal; f_equal; lia.
  - cbn; rewrite (IH (S start) n Hnth); f_equal; f_equal; lia.
Qed.

Local Lemma ssa_enumerate_app {A} (xs ys : list A) start :
  ssa_enumerate start (xs ++ ys) =
    ssa_enumerate start xs ++ ssa_enumerate (start + length xs) ys.
Proof.
  revert start; induction xs as [|x xs IH]; intro start; cbn.
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IH; replace (start + S (length xs)) with (S start + length xs) by lia.
    reflexivity.
Qed.

Local Lemma ssa_switch_case_rows_agrees l c t cases start :
  (forall i key dst args, nth_error cases i = Some ((key, dst), args) ->
    ssa_guard t (start + i) = [Condition c (GConst (VInt W32 (word_wrap W32 key)))]) ->
  ssa_switch_case_rows l c start cases =
    map (fun p => (SsaEdge l (fst (snd p)) (fst p),
      SsaBlockPayload (snd (snd p)) (ssa_guard t (fst p))))
      (ssa_enumerate start (map (fun entry => (snd (fst entry), snd entry)) cases)).
Proof.
  revert start; induction cases as [|[[key dst] args] cases IH]; intros start Hguards;
    cbn [ssa_switch_case_rows map ssa_enumerate fst snd]; [reflexivity|].
  assert (Hhead : ssa_guard t start =
    [Condition c (GConst (VInt W32 (word_wrap W32 key)))]).
  { rewrite <- (Nat.add_0_r start); apply (Hguards 0 key dst args); reflexivity. }
  rewrite Hhead; f_equal; apply IH; intros i key' dst' args' Hnth.
  replace (S start + i) with (start + S i) by lia.
  exact (Hguards (S i) key' dst' args' Hnth).
Qed.

(** Prepared switch rows equal the original slot-indexed specification on every input. *)
Local Lemma ssa_block_rows_agrees l b :
  ssa_block_rows l b = ssa_block_rows_reference l b.
Proof.
  unfold ssa_block_rows; destruct (bterm b) as [dst args|c l1 a1 l2 a2|c cases d da|
    callee args k|x] eqn:Hterm; try reflexivity.
  unfold ssa_block_rows_reference; rewrite Hterm; cbn [term_edges].
  rewrite ssa_enumerate_app, length_map, map_app; cbn [ssa_enumerate map fst snd Nat.add].
  assert (Hend : nth_error cases (length cases) = None) by
    (apply nth_error_None; lia).
  assert (Hdefault : ssa_guard (TSwitch c cases d da) (length cases) =
    map (fun entry =>
      Condition c (GNotConst (VInt W32 (word_wrap W32 (fst (fst entry)))))) cases).
  { unfold ssa_guard; rewrite Hend; reflexivity. }
  rewrite Hdefault; f_equal; apply ssa_switch_case_rows_agrees.
  intros i key dst args Hnth; cbn [ssa_guard Nat.add]; rewrite Hnth; reflexivity.
Qed.

(** Point-edge metadata is prepared once, including each parameter's selected argument. *)
Record ssa_point_payload : Type := SsaPointPayload {
  spp_source : label * nat;
  spp_target : label * nat;
  spp_uses : list vid;
  spp_defs : list vid;
  spp_forced : list vid;
  spp_back : Map.t vid (list vid);
  spp_action : instr_or_term
}.

Definition ssa_instruction_payload (l : label) (pc : nat) (i : instr) : ssa_point_payload :=
  SsaPointPayload (l, pc) (l, S pc) (instr_uses i) (instr_def i)
    (if effectful ssa_effects KeepTraps (AnInstr i) then instr_uses i else [])
    (match i with
     | IOp x _ args => Map.set nat_encoding x args Map.empty
     | _ => Map.empty
     end) (AnInstr i).

(** Reference transfer equations; actual adapters below prepare target metadata once. *)
Definition ssa_transfer_payload (B : Map.t label ssa_block) (l : label)
    (b : ssa_block) (edge : label * list vid) : ssa_point_payload :=
  let t := bterm b in
  let parameters := map fst (bparams (ssa_get nat_encoding B (SBlock [] [] (TRet 0))
    (fst edge))) in
  let reads := ssa_selected_uses t (snd edge) in
  let back := match t with
    | TCall _ _ _ => Map.empty
    | _ => Map.of_list nat_encoding
        (map (fun xy => (fst xy, [snd xy])) (combine parameters (snd edge)))
    end in
  SsaPointPayload (l, length (bbody b)) (fst edge, 0) reads parameters
    (match t with
     | TJump _ _ => []
     | TBr c _ _ _ _ | TSwitch c _ _ _ => [c]
     | _ => reads
     end) back (ATerm t).

(** The raw row specification retains the original instruction and terminator equations. *)
Definition ssa_point_payload_list (B : Map.t label ssa_block) (lb : label * ssa_block)
    : list ssa_point_payload :=
  let l := fst lb in
  let b := snd lb in
  let len := length (bbody b) in
  map (fun pi => ssa_instruction_payload l (fst pi) (snd pi))
    (ssa_enumerate 0 (bbody b)) ++
  match bterm b with
  | TRet x => [SsaPointPayload (l, len) (l, S len) [x] [] [x] Map.empty (ATerm (TRet x))]
  | _ => map (ssa_transfer_payload B l b) (term_edges (bterm b))
  end.

Definition ssa_point_rows (B : Map.t label ssa_block) (lb : label * ssa_block)
    : list (ssa_edge * ssa_point_payload) :=
  map (fun ip => (SsaEdge (fst lb) (fst (spp_target (snd ip))) (fst ip), snd ip))
    (ssa_enumerate 0 (ssa_point_payload_list B lb)).

(** Target parameter lists are prepared outside both block and outgoing-edge traversals. *)
Local Definition ssa_target_parameters (B : Map.t label ssa_block) : Map.t label (list vid) :=
  Map.map (fun b => map fst (bparams b)) B.

Local Definition ssa_transfer_payload_cached (parameters : Map.t label (list vid))
    (l : label) (len : nat) (t : terminator) (edge : label * list vid) : ssa_point_payload :=
  let ps := ssa_get nat_encoding parameters [] (fst edge) in
  let reads := ssa_selected_uses t (snd edge) in
  let back := match t with
    | TCall _ _ _ => Map.empty
    | _ => Map.of_list nat_encoding
        (map (fun xy => (fst xy, [snd xy])) (combine ps (snd edge)))
    end in
  SsaPointPayload (l, len) (fst edge, 0) reads ps
    (match t with
     | TJump _ _ => []
     | TBr c _ _ _ _ | TSwitch c _ _ _ => [c]
     | _ => reads
     end) back (ATerm t).

Local Definition ssa_point_rows_cached (parameters : Map.t label (list vid))
    (lb : label * ssa_block) : list (ssa_edge * ssa_point_payload) :=
  let l := fst lb in
  let b := snd lb in
  let len := length (bbody b) in
  let payloads :=
    map (fun pi => ssa_instruction_payload l (fst pi) (snd pi))
      (ssa_enumerate 0 (bbody b)) ++
    match bterm b with
    | TRet x => [SsaPointPayload (l, len) (l, S len) [x] [] [x] Map.empty (ATerm (TRet x))]
    | t => map (ssa_transfer_payload_cached parameters l len t) (term_edges t)
    end in
  map (fun ip => (SsaEdge l (fst (spp_target (snd ip))) (fst ip), snd ip))
    (ssa_enumerate 0 payloads).

Local Definition ssa_point_all_rows (P : program) (f : func)
    : list (ssa_edge * ssa_point_payload) :=
  let bs := ssa_blocks P f in
  let parameters := ssa_target_parameters (first_index bs) in
  flat_map (ssa_point_rows_cached parameters) bs.

Definition ssa_point_index (P : program) (f : func) : Map.t ssa_edge ssa_point_payload :=
  Map.of_list ssa_edge_encoding (ssa_point_all_rows P f).

Definition ssa_raw_points (lb : label * ssa_block) : list (label * nat) :=
  map (fun pc => (fst lb, pc)) (seq 0 (S (S (length (bbody (snd lb)))))).

Definition ssa_point_graph (P : program) (f : func) : Graph.t (label * nat) ssa_edge :=
  let bs := ssa_blocks P f in
  let rows := ssa_point_all_rows P f in
  ssa_graph_of_rows (pair_encoding nat_encoding nat_encoding) ssa_edge_encoding
    (map (fun l => (l, 0)) (ssa_entries P f)) (flat_map ssa_raw_points bs)
    spp_source spp_target (0, 0) rows.

Definition ssa_point_taken (P : program) (f : func) (a : astate)
    (tr : list event) (a' : astate) (e : ssa_edge) : Prop :=
  exists p, Map.get ssa_edge_encoding e (ssa_point_index P f) = Some p /\
    (alabel a, apc a) = spp_source p /\ (alabel a', apc a') = spp_target p /\
    match spp_action p with
    | AnInstr _ | ATerm (TRet _) => True
    | ATerm t => ssa_term_slot (aenv a) t = Some (eslot e - apc a)
    end.

(** Each raw point edge is one activation step, with no stationary steps. *)
Definition ssa_point_view (ext : nat -> list cval -> option cval) (P : program) (f : func)
    : graph_view astate event (label * nat) ssa_edge :=
  GraphView (ssa_point_graph P f) (fun a => (alabel a, apc a)) (ssa_point_taken P f)
    (fun _ _ _ => False).

Definition ssa_exit_index (P : program) (f : func) : Map.t (label * nat) (list vid) :=
  Map.of_list (pair_encoding nat_encoding nat_encoding) (flat_map (fun lb =>
    map (fun pi => ((fst lb, fst pi),
      if may_trap ssa_effects (AnInstr (snd pi)) then instr_uses (snd pi) else []))
      (ssa_enumerate 0 (bbody (snd lb)))) (ssa_blocks P f)).

(** Raw variable values are optional source bindings, including before their definitions. *)
Definition ssa_var_view (ext : nat -> list cval -> option cval) (P : program) (f : func)
    : var_view astate event (label * nat) ssa_edge vid (option cval) :=
  let index := ssa_point_index P f in
  {| gview := ssa_point_view ext P f;
     uses := fun e => match Map.get ssa_edge_encoding e index with
       | Some p => spp_uses p
       | None => []
       end;
     defs := fun e => match Map.get ssa_edge_encoding e index with
       | Some p => spp_defs p
       | None => []
       end;
     exit_uses := ssa_get (pair_encoding nat_encoding nat_encoding) (ssa_exit_index P f) [];
     vget := aenv |}.

Definition ssa_true_demands (xs : list vid) : list (vid * bool) :=
  map (fun x => (x, true)) xs.

(** Exit demands retain every raw trap operand, including conservative memory operands. *)
Definition ssa_demand_view (ext : nat -> list cval -> option cval) (P : program) (f : func)
    : demand_view astate event (label * nat) ssa_edge vid (option cval) bool :=
  let vv := ssa_var_view ext P f in
  let index := ssa_point_index P f in
  let forced := Map.map (fun p => ssa_true_demands (spp_forced p)) index in
  let backward := Map.map (fun p => Map.map ssa_true_demands (spp_back p)) index in
  let exits := Map.map ssa_true_demands (ssa_exit_index P f) in
  {| dgraph := gview vv;
     ddefs := defs vv;
     dnec := ssa_get ssa_edge_encoding forced [];
     dback := fun e x needed => if needed then
       match Map.get ssa_edge_encoding e backward with
       | Some inputs => ssa_get nat_encoding inputs [] x
       | None => []
       end else [];
     dexit := ssa_get (pair_encoding nat_encoding nat_encoding) exits [];
     dlookup := aenv;
     dvars := values_of P f |}.

(** False backward demand is empty, as required by Boolean neededness leastness. *)
Lemma ssa_dback_false ext P f e x : dback (ssa_demand_view ext P f) e x false = [].
Proof.
  reflexivity.
Qed.

(** The exit-demand list preserves the raw operand list's order and duplicates. *)
Lemma ssa_exit_demands ext P f n :
  dexit (ssa_demand_view ext P f) n =
    map (fun x => (x, true)) (exit_uses (ssa_var_view ext P f) n).
Proof.
  cbn [ssa_demand_view dexit ssa_var_view exit_uses].
  unfold ssa_get; rewrite Map.get_map.
  destruct (Map.get (pair_encoding nat_encoding nat_encoding) n (ssa_exit_index P f));
    reflexivity.
Qed.

(** * Refined syntactic points *)

Record ssa_refined_payload : Type := SsaRefinedPayload {
  srp_source : ssa_refined_point;
  srp_target : ssa_refined_point;
  srp_uses : list ssa_refined_value;
  srp_defs : list ssa_refined_value;
  srp_semantic_uses : list ssa_refined_semantic_var;
  srp_semantic_defs : list ssa_refined_semantic_var
}.

Definition ssa_refined_block_points (lb : label * ssa_block) : list ssa_refined_point :=
  let l := fst lb in
  let b := snd lb in
  SsaBeforeParams l :: map (SsaExecPoint l) (seq 0 (S (length (bbody b)))) ++
  match bterm b with
  | TCall _ _ _ => [SsaCallReady l]
  | TRet _ => [SsaAfterReturn l]
  | _ => []
  end.

Definition ssa_refined_internal_edges (lb : label * ssa_block) : list ssa_refined_edge :=
  let l := fst lb in
  let b := snd lb in
  SsaBindParams l :: map (SsaInstruction l) (seq 0 (length (bbody b))) ++
  match bterm b with
  | TCall _ _ _ => [SsaMakeCallResult l]
  | TRet _ => [SsaReturn l]
  | _ => []
  end.

Definition ssa_refined_instruction_row (l : label) (pi : nat * instr)
    : ssa_refined_edge * ssa_refined_payload :=
  let pc := fst pi in
  let i := snd pi in
  (SsaInstruction l pc,
    SsaRefinedPayload (SsaExecPoint l pc) (SsaExecPoint l (S pc))
      (map SsaSourceValue (instr_uses i)) (map SsaSourceValue (instr_def i))
      (map SsaSourceVar (instr_uses i)) (map SsaSourceVar (instr_def i))).

(** Reference refined transfers specify operands and semantic slots independently of caching. *)
Definition ssa_refined_transfer_row (B : Map.t label ssa_block) (l : label) (b : ssa_block)
    (pe : nat * (label * list vid)) : ssa_refined_edge * ssa_refined_payload :=
  let edge := snd pe in
  let target := fst edge in
  let arity := length (bparams (ssa_get nat_encoding B (SBlock [] [] (TRet 0)) target)) in
  (SsaTransfer l target (fst pe), let '(source, reads, semantic_reads) :=
    match bterm b with
    | TCall _ _ _ => (SsaCallReady l, [SsaCallResult l], [SsaCallVar l])
    | t => (SsaExecPoint l (length (bbody b)),
        map SsaSourceValue (ssa_selected_uses t (snd edge)),
        map SsaSourceVar (ssa_selected_uses t (snd edge)))
    end in
    SsaRefinedPayload source (SsaBeforeParams target) reads [] semantic_reads
      (map SsaPendingVar (seq 0 arity))).

Definition ssa_refined_terminal_rows (B : Map.t label ssa_block) (l : label) (b : ssa_block)
    : list (ssa_refined_edge * ssa_refined_payload) :=
  match bterm b with
  | TRet x => [(SsaReturn l, SsaRefinedPayload (SsaExecPoint l (length (bbody b)))
      (SsaAfterReturn l) [SsaSourceValue x] [] [SsaSourceVar x] [])]
  | t =>
    (match t with
     | TCall _ _ _ => [(SsaMakeCallResult l,
         SsaRefinedPayload (SsaExecPoint l (length (bbody b))) (SsaCallReady l)
           (map SsaSourceValue (term_uses t)) [SsaCallResult l]
           (map SsaSourceVar (term_uses t)) [SsaCallVar l])]
     | _ => []
     end) ++
    map (ssa_refined_transfer_row B l b) (ssa_enumerate 0 (term_edges t))
  end.

(** These reference rows specify the complete order preserved by cached preparation. *)
Definition ssa_refined_rows (B : Map.t label ssa_block) (lb : label * ssa_block)
    : list (ssa_refined_edge * ssa_refined_payload) :=
  let l := fst lb in
  let b := snd lb in
  let ps := map fst (bparams b) in
  (SsaBindParams l, SsaRefinedPayload (SsaBeforeParams l) (SsaExecPoint l 0) []
    (map SsaSourceValue ps) (map SsaPendingVar (seq 0 (length ps)))
    (map SsaSourceVar ps)) ::
  map (ssa_refined_instruction_row l) (ssa_enumerate 0 (bbody b)) ++
  ssa_refined_terminal_rows B l b.

(** Target arities are prepared once, rather than rescanned for each incoming occurrence. *)
Local Definition ssa_target_arities (B : Map.t label ssa_block) : Map.t label nat :=
  Map.map (fun b => length (bparams b)) B.

Local Definition ssa_refined_transfer_cached (arities : Map.t label nat)
    (l : label) (len : nat) (t : terminator) (pe : nat * (label * list vid))
    : ssa_refined_edge * ssa_refined_payload :=
  let edge := snd pe in
  let target := fst edge in
  let arity := ssa_get nat_encoding arities 0 target in
  (SsaTransfer l target (fst pe), let '(source, reads, semantic_reads) :=
    match t with
    | TCall _ _ _ => (SsaCallReady l, [SsaCallResult l], [SsaCallVar l])
    | _ => (SsaExecPoint l len, map SsaSourceValue (ssa_selected_uses t (snd edge)),
        map SsaSourceVar (ssa_selected_uses t (snd edge)))
    end in
    SsaRefinedPayload source (SsaBeforeParams target) reads [] semantic_reads
      (map SsaPendingVar (seq 0 arity))).

Local Definition ssa_refined_rows_cached (arities : Map.t label nat) (lb : label * ssa_block)
    : list (ssa_refined_edge * ssa_refined_payload) :=
  let l := fst lb in
  let b := snd lb in
  let len := length (bbody b) in
  let ps := map fst (bparams b) in
  let terminal := match bterm b with
    | TRet x => [(SsaReturn l, SsaRefinedPayload (SsaExecPoint l len)
        (SsaAfterReturn l) [SsaSourceValue x] [] [SsaSourceVar x] [])]
    | t =>
      (match t with
       | TCall _ _ _ => [(SsaMakeCallResult l,
           SsaRefinedPayload (SsaExecPoint l len) (SsaCallReady l)
             (map SsaSourceValue (term_uses t)) [SsaCallResult l]
             (map SsaSourceVar (term_uses t)) [SsaCallVar l])]
       | _ => []
       end) ++
      map (ssa_refined_transfer_cached arities l len t) (ssa_enumerate 0 (term_edges t))
    end in
  (SsaBindParams l, SsaRefinedPayload (SsaBeforeParams l) (SsaExecPoint l 0) []
    (map SsaSourceValue ps) (map SsaPendingVar (seq 0 (length ps)))
    (map SsaSourceVar ps)) ::
  map (ssa_refined_instruction_row l) (ssa_enumerate 0 (bbody b)) ++ terminal.

Definition ssa_refined_all_rows (P : program) (f : func)
    : list (ssa_refined_edge * ssa_refined_payload) :=
  let bs := ssa_blocks P f in
  let arities := ssa_target_arities (first_index bs) in
  flat_map (ssa_refined_rows_cached arities) bs.

Definition ssa_refined_index (P : program) (f : func)
    : Map.t ssa_refined_edge ssa_refined_payload :=
  Map.of_list ssa_refined_edge_encoding (ssa_refined_all_rows P f).

Definition ssa_refined_graph (P : program) (f : func)
    : Graph.t ssa_refined_point ssa_refined_edge :=
  ssa_graph_of_rows ssa_refined_point_encoding ssa_refined_edge_encoding
    (map SsaBeforeParams (ssa_entries P f))
    (flat_map ssa_refined_block_points (ssa_blocks P f))
    srp_source srp_target (SsaDeadPoint 0) (ssa_refined_all_rows P f).

Definition ssa_refined_exit_uses (P : program) (f : func)
    : ssa_refined_point -> list ssa_refined_value :=
  let index := Map.map (map SsaSourceValue) (ssa_exit_index P f) in
  fun n => match n with
  | SsaExecPoint l pc =>
      ssa_get (pair_encoding nat_encoding nat_encoding) index [] (l, pc)
  | _ => []
  end.

Definition ssa_refined_point_uses (P : program) (f : func)
    : point_uses ssa_refined_point ssa_refined_edge ssa_refined_value :=
  let index := ssa_refined_index P f in
  {| live_graph := ssa_refined_graph P f;
     edge_use := fun e => match Map.get ssa_refined_edge_encoding e index with
       | Some p => srp_uses p
       | None => []
       end;
     edge_def := fun e => match Map.get ssa_refined_edge_encoding e index with
       | Some p => srp_defs p
       | None => []
       end;
     exit_use := ssa_refined_exit_uses P f |}.

(** The strict syntactic carrier shares one point-use record and has no semantic law claim. *)
Definition ssa_refined_var_view (P : program) (f : func)
    : var_view ssa_refined_point event ssa_refined_point ssa_refined_edge
      ssa_refined_value unit :=
  let p := ssa_refined_point_uses P f in
  VarView (GraphView (live_graph p) (fun n => n) (fun _ _ _ _ => False)
    (fun _ _ _ => False)) (edge_use p) (edge_def p) (exit_use p) (fun _ _ => tt).

Definition ssa_refined_definition_rows (lb : label * ssa_block)
    : list (ssa_refined_value * ssa_refined_point) :=
  let l := fst lb in
  let b := snd lb in
  map (fun xt => (SsaSourceValue (fst xt), SsaBeforeParams l)) (bparams b) ++
  flat_map (fun pi => map (fun x => (SsaSourceValue x, SsaExecPoint l (fst pi)))
    (instr_def (snd pi))) (ssa_enumerate 0 (bbody b)) ++
  match bterm b with
  | TCall _ _ _ => [(SsaCallResult l, SsaExecPoint l (length (bbody b)))]
  | _ => []
  end.

(** The refined model delays common parameter definitions until after selected incoming reads. *)
Definition ssa_refined_points (P : program) (f : func)
    : ssa_points label ssa_edge ssa_refined_point ssa_refined_edge ssa_refined_value :=
  let bs := ssa_blocks P f in
  let points := Map.of_list nat_encoding
    (map (fun lb => (fst lb, ssa_refined_block_points lb)) bs) in
  let internal := Map.of_list nat_encoding
    (map (fun lb => (fst lb, ssa_refined_internal_edges lb)) bs) in
  let parameters := Map.of_list nat_encoding
    (map (fun lb => (fst lb, map SsaSourceValue (map fst (bparams (snd lb))))) bs) in
  let arguments := Map.of_list ssa_edge_encoding (flat_map (fun lb =>
    map (fun ep => (fst ep,
      match bterm (snd lb) with
      | TCall _ _ _ => [SsaCallResult (fst lb)]
      | _ => map SsaSourceValue (sbp_args (snd ep))
      end)) (ssa_block_rows (fst lb) (snd lb))) bs) in
  let definitions := Map.of_list ssa_refined_value_encoding
    (flat_map ssa_refined_definition_rows (ssa_blocks P f)) in
  {| point_model := ssa_refined_point_uses P f;
     block_graph := ssa_block_graph P f;
     points_in_block := ssa_get nat_encoding points [];
     instruction_edges := ssa_get nat_encoding internal [];
     parameter_edge := SsaBindParams;
     block_of_point := fun n => match n with
       | SsaBeforeParams l | SsaExecPoint l _ | SsaCallReady l | SsaAfterReturn l |
           SsaDeadPoint l => l
       end;
     block_edge_of := fun e => match e with
       | SsaTransfer src dst slot => Some (SsaEdge src dst slot)
       | _ => None
       end;
     block_params := ssa_get nat_encoding parameters [];
     block_edge_args := ssa_get ssa_edge_encoding arguments [];
     point_definition := fun x => Map.get ssa_refined_value_encoding x definitions |}.

(** Sharing the point-use expression makes this record equality constructive. *)
Theorem ssa_refined_point_model (P : program) (f : func) :
  point_model (ssa_refined_points P f) = var_point_uses (ssa_refined_var_view P f).
Proof.
  reflexivity.
Qed.

(** Raw isolated endpoints outside returning blocks map outside the refined graph. *)
Definition ssa_refine_point (P : program) (f : func) : label * nat -> ssa_refined_point :=
  let B := Map.of_list nat_encoding (map (fun lb => (fst lb,
    (length (bbody (snd lb)), match bterm (snd lb) with TRet _ => true | _ => false end)))
    (ssa_blocks P f)) in
  fun n =>
    match Map.get nat_encoding (fst n) B with
    | Some (len, returns) => if Nat.leb (snd n) len then SsaExecPoint (fst n) (snd n)
        else if returns then SsaAfterReturn (fst n) else SsaDeadPoint (fst n)
    | None => SsaDeadPoint (fst n)
    end.

Definition ssa_refined_selected (P : program) (f : func) (r : ssa_refined_state)
    (e : ssa_refined_edge) : Prop :=
  match e with
  | SsaTransfer src _ slot =>
    match srs_point r with
    | SsaCallReady _ => slot = 0
    | SsaExecPoint _ _ =>
      exists fd b, find_func P f = Some fd /\ find_block fd src = Some b /\
        ssa_term_slot (srs_env r) (bterm b) = Some slot
    | _ => False
    end
  | _ => True
  end.

Definition ssa_refined_taken (P : program) (f : func) (r : ssa_refined_state)
    (tr : list event) (r' : ssa_refined_state) (e : ssa_refined_edge) : Prop :=
  exists p, Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) = Some p /\
    srs_point r = srp_source p /\ srs_point r' = srp_target p /\
    ssa_refined_selected P f r e.

Definition ssa_refined_lookup (r : ssa_refined_state)
    (x : ssa_refined_semantic_var) : option cval :=
  match x with
  | SsaSourceVar x => srs_env r x
  | SsaCallVar l => srs_call_results r l
  | SsaPendingVar i => srs_pending r i
  end.

(** Pending slots are semantic variables with their own incoming definitions and binding uses. *)
Definition ssa_refined_semantic_var_view (ext : nat -> list cval -> option cval)
    (P : program) (f : func)
    : var_view ssa_refined_state event ssa_refined_point ssa_refined_edge
      ssa_refined_semantic_var (option cval) :=
  let index := ssa_refined_index P f in
  let exits := Map.map (map SsaSourceVar) (ssa_exit_index P f) in
  {| gview := GraphView (ssa_refined_graph P f) srs_point (ssa_refined_taken P f)
       (fun _ _ _ => False);
     uses := fun e => match Map.get ssa_refined_edge_encoding e index with
       | Some p => srp_semantic_uses p
       | None => []
       end;
     defs := fun e => match Map.get ssa_refined_edge_encoding e index with
       | Some p => srp_semantic_defs p
       | None => []
       end;
     exit_uses := fun n => match n with
       | SsaExecPoint l pc =>
           ssa_get (pair_encoding nat_encoding nat_encoding) exits [] (l, pc)
       | _ => []
       end;
     vget := ssa_refined_lookup |}.

(** Both refined carriers use the same graph while retaining different variable universes. *)
Theorem ssa_refined_graph_agrees (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  cfg (gview (ssa_refined_semantic_var_view ext P f)) =
    live_graph (point_model (ssa_refined_points P f)).
Proof.
  reflexivity.
Qed.

(** * Cached row agreement *)

Local Lemma ssa_target_parameters_get B dst :
  ssa_get nat_encoding (ssa_target_parameters B) [] dst =
    map fst (bparams (ssa_get nat_encoding B (SBlock [] [] (TRet 0)) dst)).
Proof.
  unfold ssa_target_parameters, ssa_get; rewrite Map.get_map.
  destruct (Map.get nat_encoding dst B); reflexivity.
Qed.

Local Lemma ssa_target_arities_get B dst :
  ssa_get nat_encoding (ssa_target_arities B) 0 dst =
    length (bparams (ssa_get nat_encoding B (SBlock [] [] (TRet 0)) dst)).
Proof.
  unfold ssa_target_arities, ssa_get; rewrite Map.get_map.
  destruct (Map.get nat_encoding dst B); reflexivity.
Qed.

Local Lemma ssa_transfer_payload_cached_agrees B l b edge :
  ssa_transfer_payload_cached (ssa_target_parameters B) l (length (bbody b)) (bterm b) edge =
    ssa_transfer_payload B l b edge.
Proof.
  unfold ssa_transfer_payload_cached, ssa_transfer_payload.
  rewrite ssa_target_parameters_get; reflexivity.
Qed.

Local Lemma ssa_point_rows_cached_agrees B lb :
  ssa_point_rows_cached (ssa_target_parameters B) lb = ssa_point_rows B lb.
Proof.
  destruct lb as [l b].
  assert (Htransfers :
    map (ssa_transfer_payload_cached (ssa_target_parameters B) l (length (bbody b)) (bterm b))
      (term_edges (bterm b)) = map (ssa_transfer_payload B l b) (term_edges (bterm b))).
  { apply map_ext; intro edge; apply ssa_transfer_payload_cached_agrees. }
  unfold ssa_point_rows_cached, ssa_point_rows, ssa_point_payload_list; cbn [fst snd].
  destruct (bterm b); rewrite ?Htransfers; reflexivity.
Qed.

(** Raw prepared rows preserve the complete ordered reference list without input restrictions. *)
Local Lemma ssa_point_all_rows_agrees P f :
  ssa_point_all_rows P f =
    flat_map (ssa_point_rows (first_index (ssa_blocks P f))) (ssa_blocks P f).
Proof.
  unfold ssa_point_all_rows; apply flat_map_ext; intro lb.
  apply ssa_point_rows_cached_agrees.
Qed.

Local Lemma ssa_refined_transfer_cached_agrees B l b pe :
  ssa_refined_transfer_cached (ssa_target_arities B) l (length (bbody b)) (bterm b) pe =
    ssa_refined_transfer_row B l b pe.
Proof.
  unfold ssa_refined_transfer_cached, ssa_refined_transfer_row.
  rewrite ssa_target_arities_get; destruct (bterm b); reflexivity.
Qed.

Local Lemma ssa_refined_rows_cached_agrees B lb :
  ssa_refined_rows_cached (ssa_target_arities B) lb = ssa_refined_rows B lb.
Proof.
  destruct lb as [l b].
  assert (Htransfers :
    map (ssa_refined_transfer_cached (ssa_target_arities B) l (length (bbody b)) (bterm b))
      (ssa_enumerate 0 (term_edges (bterm b))) =
    map (ssa_refined_transfer_row B l b) (ssa_enumerate 0 (term_edges (bterm b)))).
  { apply map_ext; intro pe; apply ssa_refined_transfer_cached_agrees. }
  unfold ssa_refined_rows_cached, ssa_refined_rows, ssa_refined_terminal_rows; cbn [fst snd].
  destruct (bterm b); rewrite ?Htransfers; reflexivity.
Qed.

(** Refined preparation preserves every ordered row, including raw malformed inputs. *)
Local Lemma ssa_refined_all_rows_agrees P f :
  ssa_refined_all_rows P f =
    flat_map (ssa_refined_rows (first_index (ssa_blocks P f))) (ssa_blocks P f).
Proof.
  unfold ssa_refined_all_rows; apply flat_map_ext; intro lb.
  apply ssa_refined_rows_cached_agrees.
Qed.

(** * Prepared-index facts *)

Local Lemma ssa_label_unique {A} (rows : list (nat * A)) k a b :
  NoDup (map fst rows) -> In (k, a) rows -> In (k, b) rows -> a = b.
Proof.
  induction rows as [|[key value] rows IH]; cbn; [tauto|].
  intros Hunique [Heq|Hin] [Heq'|Hin']; inversion Hunique as [|key' keys Hfresh Htail].
  - congruence.
  - injection Heq as <- <-; exfalso; apply Hfresh, in_map_iff.
    exists (key, b); split; [reflexivity|exact Hin'].
  - injection Heq' as <- <-; exfalso; apply Hfresh, in_map_iff.
    exists (key, a); split; [reflexivity|exact Hin].
  - eapply IH; eassumption.
Qed.

Local Lemma ssa_enumerate_fst {A} start (xs : list A) :
  map fst (ssa_enumerate start xs) = seq start (length xs).
Proof.
  revert start; induction xs as [|x xs IH]; intro start; cbn; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

Local Lemma ssa_enumerate_nth {A} (xs : list A) start i x :
  In (i, x) (ssa_enumerate start xs) <->
    exists offset, i = start + offset /\ nth_error xs offset = Some x.
Proof.
  revert start i; induction xs as [|a xs IH]; intros start i; cbn [ssa_enumerate].
  - split; [contradiction|intros [[|offset] [_ Hnth]]; discriminate].
  - split.
    + intros [Heq|Hin].
      * injection Heq as <- <-; exists 0; split; [lia|reflexivity].
      * apply IH in Hin; destruct Hin as [offset [-> Hnth]].
        exists (S offset); split; [lia|exact Hnth].
    + intros [[|offset] [Heq Hnth]].
      * cbn in Hnth; injection Hnth as <-; left; f_equal; lia.
      * right; apply IH; exists offset; split; [lia|exact Hnth].
Qed.

Local Lemma ssa_function_blocks ext P f fd :
  wf_program ext P -> find_func P f = Some fd ->
  ssa_blocks P f = blocks fd /\ NoDup (map fst (blocks fd)).
Proof.
  intros Hwf Hf; split.
  - unfold ssa_blocks; rewrite Hf; reflexivity.
  - exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf))).
Qed.

Local Lemma ssa_block_out ext P f fd l b :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  Graph.out (ssa_block_graph P f) l = ssa_block_edges l b.
Proof.
  intros Hwf Hf Hb.
  destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
  cbn [ssa_block_graph Graph.out]; rewrite Hblocks; unfold ssa_get.
  assert (Hlookup : Map.get nat_encoding l
    (Map.of_list nat_encoding (map (fun lb => (fst lb, ssa_block_edges (fst lb) (snd lb)))
      (blocks fd))) = Some (ssa_block_edges l b)).
  { apply ssa_map_get_complete.
    - apply in_map_iff; exists (l, b); split; [reflexivity|].
      apply first_index_sound; exact Hb.
    - intros other Hmember; apply in_map_iff in Hmember.
      destruct Hmember as [[key block] [Heq Hin]].
      cbn in Heq; injection Heq as <- <-.
      assert (Hblock : block = b).
      { eapply ssa_label_unique; [exact Hunique|exact Hin|].
        apply first_index_sound; exact Hb. }
      subst block; reflexivity. }
  rewrite Hlookup; reflexivity.
Qed.

Local Lemma ssa_block_out_member P f l e :
  In e (Graph.out (ssa_block_graph P f) l) ->
  exists b, In (l, b) (ssa_blocks P f) /\ In e (ssa_block_edges l b).
Proof.
  cbn [ssa_block_graph Graph.out]; unfold ssa_get.
  destruct (Map.get nat_encoding l
    (Map.of_list nat_encoding (map (fun lb =>
      (fst lb, ssa_block_edges (fst lb) (snd lb))) (ssa_blocks P f))))
    as [edges|] eqn:Hout; [|contradiction].
  intro Hedge; apply ssa_map_get_sound in Hout; apply in_map_iff in Hout.
  destruct Hout as [[key b] [Heq Hin]].
  cbn in Heq; injection Heq as <- <-; exists b; split; assumption.
Qed.

Local Lemma ssa_block_edge_source l b e :
  In e (ssa_block_edges l b) -> esrc e = l.
Proof.
  intro Hedge; apply in_map_iff in Hedge.
  destruct Hedge as [[slot [dst args]] [<- Hin]]; reflexivity.
Qed.

Local Lemma ssa_block_edge_target l b e :
  In e (ssa_block_edges l b) -> exists args, In (edst e, args) (term_edges (bterm b)).
Proof.
  intro Hedge; apply in_map_iff in Hedge.
  destruct Hedge as [[slot [dst args]] [<- Hin]].
  apply ssa_enumerate_nth in Hin; destruct Hin as [offset [_ Hnth]].
  exists args; apply nth_error_In with offset; exact Hnth.
Qed.

Local Lemma ssa_typed_target B T dst args :
  typed_jump B T (dst, args) -> exists b, B dst = Some b.
Proof.
  unfold typed_jump; cbn; destruct (B dst) as [b|] eqn:Hb; [exists b; reflexivity|tauto].
Qed.

Local Lemma ssa_term_target ext P f fd l b dst args :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  In (dst, args) (term_edges (bterm b)) -> exists target, find_block fd dst = Some target.
Proof.
  intros Hwf Hf Hb Hedge.
  destruct (wf_block ext P f fd l b Hwf Hf Hb) as [_ [_ [Htyped _]]].
  destruct (bterm b) as [target actual|c l1 a1 l2 a2|c cases d da|c actual k|x];
    cbn [term_typed] in Htyped.
  - apply ssa_typed_target with (T := static_ty P f) (args := args).
    exact (proj1 (Forall_forall _ _) Htyped _ Hedge).
  - apply ssa_typed_target with (T := static_ty P f) (args := args).
    exact (proj1 (Forall_forall _ _) (proj2 Htyped) _ Hedge).
  - apply ssa_typed_target with (T := static_ty P f) (args := args).
    exact (proj1 (Forall_forall _ _) (proj2 Htyped) _ Hedge).
  - cbn [term_edges] in Hedge; destruct Hedge as [Heq|Hfalse]; [|contradiction].
    injection Heq as <- <-.
    destruct (callee_sig P (static_ty P f) c) as [[ps result]|]; [|contradiction].
    destruct (find_block fd k) as [target|] eqn:Htarget; [exists target; reflexivity|tauto].
  - contradiction.
Qed.

Local Lemma ssa_block_graph_wf ext P f :
  wf_program ext P -> In f (map fst (funcs P)) -> graph_wf (ssa_block_graph P f).
Proof.
  intros Hwf Hfunction.
  apply in_map_iff in Hfunction; destruct Hfunction as [[key fd] [Hkey Hmember]].
  cbn in Hkey; subst key.
  assert (Hf : find_func P f = Some fd).
  { apply first_index_complete; [exact (proj1 (proj2 Hwf))|exact Hmember]. }
  destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
  constructor.
  - change (NoDup (map fst (ssa_blocks P f))); rewrite Hblocks; exact Hunique.
  - intros l Hin; change (In l (ssa_entries P f)) in Hin.
    unfold ssa_entries in Hin; rewrite Hf in Hin; destruct Hin as [<-|Hfalse];
      [|contradiction].
    destruct (proj1 (wf_function ext P f fd Hwf Hf)) as [b Hb].
    change (In (fentry fd) (map fst (ssa_blocks P f))); rewrite Hblocks.
    apply in_map_iff; exists (fentry fd, b); split; [reflexivity|].
    apply first_index_sound; exact Hb.
  - intros l e Hedge.
    destruct (ssa_block_out_member P f l e Hedge) as [b [_ Hlocal]].
    exact (ssa_block_edge_source l b e Hlocal).
  - intros l e Hnode Hedge.
    destruct (ssa_block_out_member P f l e Hedge) as [b [Hmember' Hlocal]].
    rewrite Hblocks in Hmember'.
    assert (Hb : find_block fd l = Some b).
    { apply first_index_complete; assumption. }
    destruct (ssa_block_edge_target l b e Hlocal) as [args Htarget].
    destruct (ssa_term_target ext P f fd l b (edst e) args Hwf Hf Hb Htarget)
      as [target Hlookup].
    change (In (edst e) (map fst (ssa_blocks P f))); rewrite Hblocks.
    apply in_map_iff; exists (edst e, target); split; [reflexivity|].
    apply first_index_sound; exact Hlookup.
Qed.

Local Lemma ssa_block_taken_intro P f a tr a' t dst args slot :
  at_term P (activation_frame f a) t -> alabel a' = dst -> apc a' = 0 ->
  nth_error (term_edges t) slot = Some (dst, args) ->
  ssa_term_slot (aenv a) t = Some slot ->
  ssa_block_taken P f a tr a' (SsaEdge (alabel a) dst slot).
Proof.
  intros [fd [b [Hf [Hb [Hpc Hterm]]]]] Htarget Hzero Hedge Hslot.
  exists fd, b; split; [exact Hf|]; split; [exact Hb|];
    split; [exact Hpc|]; split; [reflexivity|]; split; [symmetry; exact Htarget|].
  split; [exact Hzero|]; split; [|rewrite Hterm; exact Hslot].
  unfold ssa_block_edges; apply in_map_iff; exists (slot, (dst, args));
    split; [reflexivity|].
  apply ssa_enumerate_nth; exists slot; split; [lia|rewrite Hterm; exact Hedge].
Qed.

Local Lemma ssa_block_steps_covered ext P f a tr a' :
  step (activation ext P f) a tr a' ->
  (alabel a' = alabel a /\ apc a' = S (apc a)) \/
    exists e, ssa_block_taken P f a tr a' e.
Proof.
  intro Hstep.
  destruct Hstep as
    [a x o args cs v Hat Hread Heval
    |a x n block offset Hat
    |a p Hat
    |a x t sz p v Hat Htype Hvalid
    |a sz p x Hat
    |a x v Hat Hvalue
    |a l args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z l args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases d da z l args cs env Hat Hcond Hchoice Hread Hbind
    |a c args k ps r cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a x v Hat Hvalue]; try (left; split; reflexivity).
  - right; exists (SsaEdge (alabel a) l 0).
    eapply ssa_block_taken_intro with (t := TJump l args) (args := args);
      try reflexivity; exact Hat.
  - right; exists (SsaEdge (alabel a) l (if Z.eqb z 0 then 1 else 0)).
    eapply ssa_block_taken_intro with (t := TBr c l1 a1 l2 a2) (args := args);
      try reflexivity; [exact Hat| |].
    + cbn [term_edges]; destruct (Z.eqb z 0); injection Hchoice as <- <-; reflexivity.
    + cbn [ssa_term_slot]; rewrite Hcond; reflexivity.
  - right; exists (SsaEdge (alabel a) l (ssa_switch_slot z cases)).
    eapply ssa_block_taken_intro with (t := TSwitch c cases d da) (args := args);
      try reflexivity; [exact Hat| |].
    + rewrite <- Hchoice; exact (ssa_switch_slot_target z cases d da).
    + cbn [ssa_term_slot]; rewrite Hcond; reflexivity.
  - right; exists (SsaEdge (alabel a) k 0).
    eapply ssa_block_taken_intro with (t := TCall c args k) (args := []);
      try reflexivity; exact Hat.
Qed.

Local Lemma ssa_block_graph_laws ext P f :
  wf_program ext P -> In f (map fst (funcs P)) ->
  graph_view_laws (activation ext P f) (base (ssa_block_view ext P f)).
Proof.
  intros Hwf Hfunction; constructor.
  - exact (ssa_block_graph_wf ext P f Hwf Hfunction).
  - intros a [fd [b [cs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]].
    change (In (fentry fd) (ssa_entries P f)); unfold ssa_entries; rewrite Hf.
    left; reflexivity.
  - intros a tr a' Hreachable Hstep; exact (ssa_block_steps_covered ext P f a tr a' Hstep).
  - intros a tr a' e Hreachable Hstep [fd [b [Hf [Hb [Hpc [Hsrc [Hdst
      [Hzero [Hedge Hslot]]]]]]]]].
    split.
    + change (In e (Graph.out (ssa_block_graph P f) (alabel a))).
      rewrite (ssa_block_out ext P f fd (alabel a) b Hwf Hf Hb); exact Hedge.
    + exact Hdst.
  - intros a tr a' Hreachable Hstep [Hlabel Hpc]; exact Hlabel.
Qed.

Local Lemma ssa_point_row_coordinate B lb e p :
  In (e, p) (ssa_point_rows B lb) ->
  esrc e = fst lb /\ nth_error (ssa_point_payload_list B lb) (eslot e) = Some p.
Proof.
  intro Hrow; apply in_map_iff in Hrow.
  destruct Hrow as [[slot payload] [Heq Hin]]; cbn in Heq.
  injection Heq as <- <-; cbn; split; [reflexivity|].
  apply ssa_enumerate_nth in Hin; destruct Hin as [offset [Hslot Hnth]].
  cbn in Hslot; subst slot; exact Hnth.
Qed.

Local Lemma ssa_point_rows_unique B bs :
  NoDup (map fst bs) ->
  forall e p q, In (e, p) (flat_map (ssa_point_rows B) bs) ->
    In (e, q) (flat_map (ssa_point_rows B) bs) -> p = q.
Proof.
  intros Hunique e p q Hp Hq.
  apply in_flat_map in Hp; destruct Hp as [[l b] [Hblock Hp]].
  apply in_flat_map in Hq; destruct Hq as [[l' b'] [Hblock' Hq]].
  destruct (ssa_point_row_coordinate B (l, b) e p Hp) as [Hsource Hp'].
  destruct (ssa_point_row_coordinate B (l', b') e q Hq) as [Hsource' Hq'].
  cbn in Hsource, Hsource'; subst l'; subst l.
  assert (Heq : b = b') by (eapply ssa_label_unique; eassumption).
  subst b'; rewrite Hp' in Hq'; injection Hq' as Heq; exact Heq.
Qed.

Local Lemma ssa_raw_point_in bs l b pc :
  In (l, b) bs -> pc <= S (length (bbody b)) ->
  In (l, pc) (flat_map ssa_raw_points bs).
Proof.
  intros Hblock Hpc; apply in_flat_map; exists (l, b); split; [exact Hblock|].
  unfold ssa_raw_points; apply in_map_iff; exists pc; split; [reflexivity|].
  apply in_seq; cbn; lia.
Qed.

Local Lemma ssa_pair_points_nodup (l : label) (pcs : list nat) :
  NoDup pcs -> NoDup (map (fun pc => (l, pc)) pcs).
Proof.
  intro Hunique; induction Hunique as [|pc pcs Hfresh Hunique IH]; [constructor|].
  cbn; constructor; [|exact IH].
  intro Hin; apply in_map_iff in Hin; destruct Hin as [other [Heq Hin]].
  injection Heq as <-; exact (Hfresh Hin).
Qed.

Local Lemma ssa_raw_points_nodup bs :
  NoDup (map fst bs) -> NoDup (flat_map ssa_raw_points bs).
Proof.
  induction bs as [|[l b] bs IH]; [constructor|].
  intro Hunique; inversion Hunique as [|head labels Hfresh Htail].
  cbn [flat_map]; apply NoDup_app; repeat split.
  - unfold ssa_raw_points; apply ssa_pair_points_nodup, seq_NoDup.
  - exact (IH Htail).
  - intros [key pc] Hin Hother.
    apply in_map_iff in Hin; destruct Hin as [index [Heq Hin]].
    cbn in Heq; injection Heq as <- <-.
    apply in_flat_map in Hother; destruct Hother as [[other block] [Hblock Hpoint]].
    apply in_map_iff in Hpoint; destruct Hpoint as [index' [Heq Hindex]].
    cbn in Heq; injection Heq as Hlabel Hpc; subst other.
    apply Hfresh, in_map_iff; exists (l, block); split; [reflexivity|exact Hblock].
Qed.

Local Lemma ssa_point_payload_target ext P f fd B l b p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  In p (ssa_point_payload_list B (l, b)) ->
  In (spp_target p) (flat_map ssa_raw_points (blocks fd)).
Proof.
  intros Hwf Hf Hb Hin; unfold ssa_point_payload_list in Hin; cbn [fst snd] in Hin.
  apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
  - apply in_map_iff in Hin; destruct Hin as [[pc i] [<- Hposition]].
    apply ssa_enumerate_nth in Hposition; destruct Hposition as [offset [Hpc Hnth]].
    cbn in Hpc; subst pc; apply ssa_raw_point_in with (b := b).
    + apply first_index_sound; exact Hb.
    + assert (Hbound : offset < length (bbody b)).
      { apply nth_error_Some; rewrite Hnth; discriminate. }
      cbn [ssa_instruction_payload spp_target fst snd]; lia.
  - destruct (bterm b) as [dst args|c l1 a1 l2 a2|c cases d da|c args k|x] eqn:Hterm;
      try (apply in_map_iff in Hin; destruct Hin as [[dst' args'] [<- Hedge]]).
    all: try (destruct (ssa_term_target ext P f fd l b dst' args' Hwf Hf Hb)
      as [target Htarget]; [rewrite Hterm; exact Hedge|];
      cbn [ssa_transfer_payload spp_target]; apply ssa_raw_point_in with (b := target);
      [apply first_index_sound; exact Htarget|lia]).
    cbn in Hin; destruct Hin as [<-|Hfalse]; [|contradiction].
    cbn [spp_target]; apply ssa_raw_point_in with (b := b).
    + apply first_index_sound; exact Hb.
    + lia.
Qed.

Local Lemma ssa_point_graph_wf ext P f :
  wf_program ext P -> In f (map fst (funcs P)) -> graph_wf (ssa_point_graph P f).
Proof.
  intros Hwf Hfunction.
  apply in_map_iff in Hfunction; destruct Hfunction as [[key fd] [Hkey Hmember]].
  cbn in Hkey; subst key.
  assert (Hf : find_func P f = Some fd).
  { apply first_index_complete; [exact (proj1 (proj2 Hwf))|exact Hmember]. }
  destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
  unfold ssa_point_graph; rewrite ssa_point_all_rows_agrees; apply ssa_graph_of_rows_wf.
  - apply ssa_raw_points_nodup; rewrite Hblocks; exact Hunique.
  - intros n Hin; apply in_map_iff in Hin; destruct Hin as [l [<- Hentry]].
    unfold ssa_entries in Hentry; rewrite Hf in Hentry.
    destruct Hentry as [<-|Hfalse]; [|contradiction].
    destruct (proj1 (wf_function ext P f fd Hwf Hf)) as [b Hb].
    apply ssa_raw_point_in with (b := b); [rewrite Hblocks; apply first_index_sound;
      exact Hb|lia].
  - apply ssa_point_rows_unique; rewrite Hblocks; exact Hunique.
  - intros e p Hrow; apply in_flat_map in Hrow.
    destruct Hrow as [[l b] [Hmember' Hlocal]].
    rewrite Hblocks in Hmember'.
    assert (Hb : find_block fd l = Some b) by (apply first_index_complete; assumption).
    destruct (ssa_point_row_coordinate _ (l, b) e p Hlocal) as [_ Hnth].
    rewrite Hblocks; eapply ssa_point_payload_target; try eassumption.
    apply nth_error_In with (eslot e); exact Hnth.
Qed.

Local Lemma ssa_point_index_complete ext P f fd l b n p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (ssa_point_payload_list (first_index (ssa_blocks P f)) (l, b)) n = Some p ->
  Map.get ssa_edge_encoding (SsaEdge l (fst (spp_target p)) n) (ssa_point_index P f) = Some p.
Proof.
  intros Hwf Hf Hb Hnth.
  destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
  assert (Hrow : In (SsaEdge l (fst (spp_target p)) n, p)
    (flat_map (ssa_point_rows (first_index (ssa_blocks P f))) (ssa_blocks P f))).
  { apply in_flat_map; exists (l, b); split.
    - rewrite Hblocks; apply first_index_sound; exact Hb.
    - unfold ssa_point_rows; apply in_map_iff; exists (n, p); split; [reflexivity|].
      apply ssa_enumerate_nth; exists n; split; [lia|exact Hnth]. }
  unfold ssa_point_index; rewrite ssa_point_all_rows_agrees.
  apply ssa_map_get_complete; [exact Hrow|].
  intros q Hq; eapply ssa_point_rows_unique with (bs := ssa_blocks P f);
    [rewrite Hblocks; exact Hunique|exact Hq|].
  exact Hrow.
Qed.

Local Lemma ssa_point_instruction_lookup B l b pc i :
  nth_error (bbody b) pc = Some i ->
  nth_error (ssa_point_payload_list B (l, b)) pc = Some (ssa_instruction_payload l pc i).
Proof.
  intro Hnth; unfold ssa_point_payload_list; cbn [fst snd].
  rewrite nth_error_app1 by (rewrite length_map, ssa_enumerate_length;
    apply nth_error_Some; rewrite Hnth; discriminate).
  rewrite nth_error_map, (ssa_enumerate_lookup _ 0 pc i Hnth); reflexivity.
Qed.

Local Lemma ssa_point_term_lookup B l b slot target args :
  (forall x, bterm b <> TRet x) ->
  nth_error (term_edges (bterm b)) slot = Some (target, args) ->
  nth_error (ssa_point_payload_list B (l, b)) (length (bbody b) + slot) =
    Some (ssa_transfer_payload B l b (target, args)).
Proof.
  intros Hnot Hnth; unfold ssa_point_payload_list; cbn [fst snd].
  rewrite nth_error_app2 by (rewrite length_map, ssa_enumerate_length; lia).
  rewrite length_map, ssa_enumerate_length; replace
    (length (bbody b) + slot - length (bbody b)) with slot by lia.
  destruct (bterm b); try (rewrite nth_error_map, Hnth; reflexivity).
  exfalso; eapply Hnot; reflexivity.
Qed.

Local Lemma ssa_point_return_lookup B l b x :
  bterm b = TRet x ->
  nth_error (ssa_point_payload_list B (l, b)) (length (bbody b)) =
    Some (SsaPointPayload (l, length (bbody b)) (l, S (length (bbody b)))
      [x] [] [x] Map.empty (ATerm (TRet x))).
Proof.
  intro Hterm; unfold ssa_point_payload_list; cbn [fst snd].
  rewrite nth_error_app2 by (rewrite length_map, ssa_enumerate_length; lia).
  rewrite length_map, ssa_enumerate_length, Nat.sub_diag, Hterm; reflexivity.
Qed.

Local Lemma ssa_point_instruction_taken ext P f a tr a' i :
  wf_program ext P -> at_instr P (activation_frame f a) i ->
  alabel a' = alabel a -> apc a' = S (apc a) ->
  exists e, ssa_point_taken P f a tr a' e.
Proof.
  intros Hwf [fd [b [Hf [Hb Hnth]]]] Hlabel Hpc.
  cbn [activation_frame ffunc flabel fpc] in Hf, Hb, Hnth.
  exists (SsaEdge (alabel a) (alabel a) (apc a)).
  exists (ssa_instruction_payload (alabel a) (apc a) i).
  split.
  - apply ssa_point_index_complete with (ext := ext) (fd := fd) (b := b)
      (p := ssa_instruction_payload (alabel a) (apc a) i);
      try assumption; apply ssa_point_instruction_lookup; exact Hnth.
  - split; [reflexivity|]; split; [cbn; congruence|exact I].
Qed.

Local Lemma ssa_point_term_taken ext P f a tr a' t dst args slot :
  wf_program ext P -> at_term P (activation_frame f a) t ->
  (forall x, t <> TRet x) -> alabel a' = dst -> apc a' = 0 ->
  nth_error (term_edges t) slot = Some (dst, args) ->
  ssa_term_slot (aenv a) t = Some slot ->
  exists e, ssa_point_taken P f a tr a' e.
Proof.
  intros Hwf [fd [b [Hf [Hb [Hpc Hterm]]]]] Hnot Hdst Hzero Hnth Hslot.
  cbn [activation_frame ffunc flabel fpc] in Hf, Hb, Hpc.
  exists (SsaEdge (alabel a) dst (length (bbody b) + slot)).
  exists (ssa_transfer_payload (first_index (ssa_blocks P f)) (alabel a) b (dst, args)).
  split.
  - apply ssa_point_index_complete with (ext := ext) (fd := fd) (b := b)
      (p := ssa_transfer_payload (first_index (ssa_blocks P f)) (alabel a) b (dst, args));
      try assumption; apply ssa_point_term_lookup; rewrite Hterm; assumption.
  - split; [cbn; congruence|]; split; [cbn; congruence|].
    cbn [ssa_transfer_payload spp_action eslot]; rewrite Hterm.
    replace (length (bbody b) + slot - apc a) with slot by lia.
    destruct t; try exact Hslot; exfalso; eapply Hnot; reflexivity.
Qed.

Local Lemma ssa_point_return_taken ext P f a tr a' x :
  wf_program ext P -> at_term P (activation_frame f a) (TRet x) ->
  alabel a' = alabel a -> apc a' = S (apc a) ->
  exists e, ssa_point_taken P f a tr a' e.
Proof.
  intros Hwf [fd [b [Hf [Hb [Hpc Hterm]]]]] Hlabel Hnext.
  cbn [activation_frame ffunc flabel fpc] in Hf, Hb, Hpc.
  exists (SsaEdge (alabel a) (alabel a) (length (bbody b))).
  exists (SsaPointPayload (alabel a, length (bbody b))
    (alabel a, S (length (bbody b))) [x] [] [x] Map.empty (ATerm (TRet x))); split.
  - apply ssa_point_index_complete with (ext := ext) (fd := fd) (b := b)
      (p := SsaPointPayload (alabel a, length (bbody b))
        (alabel a, S (length (bbody b))) [x] [] [x] Map.empty (ATerm (TRet x)));
      try assumption; apply ssa_point_return_lookup; exact Hterm.
  - split; [cbn; congruence|]; split; [cbn; congruence|exact I].
Qed.

Local Lemma ssa_point_steps_covered ext P f a tr a' :
  wf_program ext P -> step (activation ext P f) a tr a' ->
  exists e, ssa_point_taken P f a tr a' e.
Proof.
  intros Hwf Hstep; destruct Hstep as
    [a x o args cs v Hat Hread Heval
    |a x n block offset Hat
    |a p Hat
    |a x t sz p v Hat Htype Hvalid
    |a sz p x Hat
    |a x v Hat Hvalue
    |a l args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z l args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases d da z l args cs env Hat Hcond Hchoice Hread Hbind
    |a c args k ps r cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a x v Hat Hvalue].
  all: try (eapply ssa_point_instruction_taken; [exact Hwf|exact Hat|reflexivity|reflexivity]).
  - eapply ssa_point_term_taken with (t := TJump l args) (dst := l) (args := args) (slot := 0);
      try reflexivity; [exact Hwf|exact Hat|intros x Hfalse; discriminate].
  - eapply ssa_point_term_taken with (t := TBr c l1 a1 l2 a2) (dst := l) (args := args)
      (slot := if Z.eqb z 0 then 1 else 0); try reflexivity;
      [exact Hwf|exact Hat|intros x Hfalse; discriminate| |].
    + cbn [term_edges]; destruct (Z.eqb z 0); injection Hchoice as <- <-; reflexivity.
    + cbn [ssa_term_slot]; rewrite Hcond; reflexivity.
  - eapply ssa_point_term_taken with (t := TSwitch c cases d da) (dst := l) (args := args)
      (slot := ssa_switch_slot z cases); try reflexivity;
      [exact Hwf|exact Hat|intros x Hfalse; discriminate| |].
    + rewrite <- Hchoice; exact (ssa_switch_slot_target z cases d da).
    + cbn [ssa_term_slot]; rewrite Hcond; reflexivity.
  - eapply ssa_point_term_taken with (t := TCall c args k) (dst := k) (args := []) (slot := 0);
      try reflexivity; [exact Hwf|exact Hat|intros x Hfalse; discriminate].
  - eapply ssa_point_return_taken; [exact Hwf|exact Hat|reflexivity|reflexivity].
Qed.

Local Lemma ssa_point_graph_laws ext P f :
  wf_program ext P -> In f (map fst (funcs P)) ->
  graph_view_laws (activation ext P f) (ssa_point_view ext P f).
Proof.
  intros Hwf Hfunction; constructor.
  - exact (ssa_point_graph_wf ext P f Hwf Hfunction).
  - intros a [fd [b [cs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]].
    change (In (fentry fd, 0) (map (fun l => (l, 0)) (ssa_entries P f))).
    apply in_map_iff; exists (fentry fd); split; [reflexivity|].
    unfold ssa_entries; rewrite Hf; left; reflexivity.
  - intros a tr a' Hreachable Hstep; right; exact (ssa_point_steps_covered ext P f a tr a'
      Hwf Hstep).
  - intros a tr a' e Hreachable Hstep [p [Hindex [Hsource [Htarget Haction]]]].
    split.
    + change (In e (ssa_get (pair_encoding nat_encoding nat_encoding)
        (ssa_outgoing_index (pair_encoding nat_encoding nat_encoding) spp_source
          (ssa_point_all_rows P f)) []
        (alabel a, apc a))).
      apply ssa_outgoing_member; exists p; split;
        [exact (ssa_map_get_sound ssa_edge_encoding _ e p Hindex)|].
      symmetry; exact Hsource.
    + change (match Map.get ssa_edge_encoding e (ssa_point_index P f) with
        | Some p => spp_target p | None => (0, 0) end = (alabel a', apc a')).
      rewrite Hindex; symmetry; exact Htarget.
  - intros a tr a' Hreachable Hstep Hfalse; contradiction.
Qed.

(** Local row classification retains the original ordered edge occurrence. *)
Inductive ssa_point_local (B : Map.t label ssa_block) (l : label) (b : ssa_block)
    : ssa_edge -> ssa_point_payload -> Prop :=
  | SsaLocalInstruction : forall pc i, nth_error (bbody b) pc = Some i ->
      ssa_point_local B l b (SsaEdge l l pc) (ssa_instruction_payload l pc i)
  | SsaLocalTransfer : forall slot dst args,
      (forall x, bterm b <> TRet x) ->
      nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
      ssa_point_local B l b (SsaEdge l dst (length (bbody b) + slot))
        (ssa_transfer_payload B l b (dst, args))
  | SsaLocalReturn : forall x, bterm b = TRet x ->
      ssa_point_local B l b (SsaEdge l l (length (bbody b)))
        (SsaPointPayload (l, length (bbody b)) (l, S (length (bbody b)))
          [x] [] [x] Map.empty (ATerm (TRet x))).

Local Lemma ssa_point_row_local B l b e p :
  In (e, p) (ssa_point_rows B (l, b)) -> ssa_point_local B l b e p.
Proof.
  intro Hrow; unfold ssa_point_rows in Hrow; apply in_map_iff in Hrow.
  destruct Hrow as [[n payload] [Heq Hmember]]; cbn in Heq; injection Heq as <- <-.
  apply ssa_enumerate_nth in Hmember; destruct Hmember as [offset [Hn Hnth]].
  cbn in Hn; subst n; unfold ssa_point_payload_list in Hnth; cbn [fst snd] in Hnth.
  destruct (lt_dec offset (length (bbody b))) as [Hbefore|Hafter].
  - rewrite nth_error_app1 in Hnth by (rewrite length_map, ssa_enumerate_length; lia).
    destruct (nth_error (bbody b) offset) as [i|] eqn:Hi.
    + rewrite nth_error_map, (ssa_enumerate_lookup _ 0 offset i Hi) in Hnth.
      cbn in Hnth; injection Hnth as <-; apply SsaLocalInstruction; exact Hi.
    + apply nth_error_None in Hi; lia.
  - rewrite nth_error_app2 in Hnth by (rewrite length_map, ssa_enumerate_length; lia).
    rewrite length_map, ssa_enumerate_length in Hnth.
    destruct (bterm b) as [dst args|c l1 a1 l2 a2|c cases d da|c args k|x] eqn:Hterm.
    all: try (rewrite nth_error_map in Hnth;
      destruct (nth_error (term_edges (bterm b)) (offset - length (bbody b)))
        as [[target actual]|] eqn:Hedge;
      [rewrite Hterm in Hedge; rewrite Hedge in Hnth; cbn in Hnth;
        injection Hnth as <-; replace offset with
          (length (bbody b) + (offset - length (bbody b))) at 1 by lia;
        apply SsaLocalTransfer; [intros y Hfalse; rewrite Hterm in Hfalse; discriminate|
          rewrite Hterm; exact Hedge]
      |rewrite Hterm in Hedge; rewrite Hedge in Hnth; discriminate]).
    cbn in Hnth; destruct (offset - length (bbody b)) as [|rest] eqn:Hoffset.
    + injection Hnth as <-; replace offset with (length (bbody b)) by lia.
      apply SsaLocalReturn; exact Hterm.
    + destruct rest; discriminate.
Qed.

Local Lemma ssa_point_index_local ext P f e p :
  wf_program ext P -> Map.get ssa_edge_encoding e (ssa_point_index P f) = Some p ->
  exists fd l b, find_func P f = Some fd /\ find_block fd l = Some b /\
    ssa_point_local (first_index (ssa_blocks P f)) l b e p.
Proof.
  intros Hwf Hget; apply (ssa_map_get_sound ssa_edge_encoding) in Hget.
  rewrite ssa_point_all_rows_agrees in Hget.
  apply in_flat_map in Hget; destruct Hget as [[l b] [Hblock Hrow]].
  unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
    [|contradiction].
  exists fd, l, b; split; [reflexivity|]; split.
  - apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
      exact Hblock].
  - apply ssa_point_row_local; exact Hrow.
Qed.

Local Lemma ssa_taken_instruction_index ext P f a tr a' e i :
  wf_program ext P -> at_instr P (activation_frame f a) i ->
  ssa_point_taken P f a tr a' e ->
  Map.get ssa_edge_encoding e (ssa_point_index P f) =
    Some (ssa_instruction_payload (alabel a) (apc a) i).
Proof.
  intros Hwf Hat [p [Hget [Hsource [Htarget Haction]]]].
  destruct (ssa_point_index_local ext P f e p Hwf Hget)
    as [fd [l [b [Hf [Hb Hlocal]]]]].
  destruct Hlocal as [pc j Hnth|slot dst args Hnot Hnth|x Hterm].
  - cbn [ssa_instruction_payload spp_source] in Hsource.
    injection Hsource as Hlabel Hpc.
    assert (Hj : at_instr P (activation_frame f a) j).
    { exists fd, b; cbn [activation_frame ffunc flabel fpc]; rewrite Hlabel, Hpc.
      repeat split; assumption. }
    pose proof (ssa_at_instr_unique P _ i j Hat Hj) as ->.
    rewrite Hlabel, Hpc; exact Hget.
  - cbn [ssa_transfer_payload spp_source] in Hsource.
    injection Hsource as Hlabel Hpc.
    pose proof (ssa_at_instr_before P _ i fd b Hat Hf) as Hbefore.
    cbn [activation_frame flabel fpc] in Hbefore.
    specialize (Hbefore ltac:(rewrite Hlabel; exact Hb)); lia.
  - cbn [spp_source] in Hsource; injection Hsource as Hlabel Hpc.
    pose proof (ssa_at_instr_before P _ i fd b Hat Hf) as Hbefore.
    cbn [activation_frame flabel fpc] in Hbefore.
    specialize (Hbefore ltac:(rewrite Hlabel; exact Hb)); lia.
Qed.

Local Lemma ssa_taken_term_local ext P f a tr a' e t :
  wf_program ext P -> at_term P (activation_frame f a) t ->
  ssa_point_taken P f a tr a' e ->
  exists fd b p, find_func P f = Some fd /\ find_block fd (alabel a) = Some b /\
    apc a = length (bbody b) /\ bterm b = t /\
    Map.get ssa_edge_encoding e (ssa_point_index P f) = Some p /\
    (alabel a', apc a') = spp_target p /\
    ((exists dst args, (forall x, t <> TRet x) /\
        p = ssa_transfer_payload (first_index (ssa_blocks P f)) (alabel a) b (dst, args)) \/
     (exists x, t = TRet x /\ p = SsaPointPayload (alabel a, apc a)
        (alabel a, S (apc a)) [x] [] [x] Map.empty (ATerm t))).
Proof.
  intros Hwf Hat [p [Hget [Hsource [Htarget Haction]]]].
  destruct (ssa_point_index_local ext P f e p Hwf Hget)
    as [fd [l [b [Hf [Hb Hlocal]]]]].
  destruct Hlocal as [pc j Hnth|slot dst args Hnot Hnth|x Hterm].
  - cbn [ssa_instruction_payload spp_source] in Hsource; injection Hsource as Hlabel Hpc.
    pose proof (ssa_at_term_end P _ t fd b Hat Hf) as Hend.
    cbn [activation_frame flabel fpc] in Hend.
    specialize (Hend ltac:(rewrite Hlabel; exact Hb)).
    assert (Hbefore : pc < length (bbody b)).
    { apply nth_error_Some; rewrite Hnth; discriminate. }
    lia.
  - cbn [ssa_transfer_payload spp_source] in Hsource;
      injection Hsource as Hlabel Hpc.
    assert (Ht : bterm b = t).
    { eapply ssa_at_term_unique; [|exact Hat].
      exists fd, b; cbn [activation_frame ffunc flabel fpc]; rewrite Hlabel.
      repeat split; assumption. }
    exists fd, b, (ssa_transfer_payload (first_index (ssa_blocks P f)) l b (dst, args)).
    repeat split; try assumption; try (rewrite Hlabel; exact Hb).
    left; exists dst, args; split; [rewrite <- Ht; exact Hnot|rewrite Hlabel; reflexivity].
  - cbn [spp_source] in Hsource; injection Hsource as Hlabel Hpc.
    assert (Ht : TRet x = t).
    { eapply ssa_at_term_unique; [|exact Hat].
      exists fd, b; cbn [activation_frame ffunc flabel fpc]; rewrite Hlabel.
      repeat split; assumption. }
    exists fd, b, (SsaPointPayload (l, length (bbody b)) (l, S (length (bbody b)))
      [x] [] [x] Map.empty (ATerm (TRet x))).
    split; [exact Hf|]; split; [rewrite Hlabel; exact Hb|].
    split; [exact Hpc|]; split; [congruence|].
    split; [exact Hget|]; split; [exact Htarget|].
    right; exists x; split; [symmetry; exact Ht|rewrite Hlabel, Hpc, <- Ht; reflexivity].
Qed.

Local Lemma ssa_transfer_defs_frame ext P f a tr dst cs env e t x :
  wf_program ext P -> at_term P (activation_frame f a) t ->
  (forall y, t <> TRet y) ->
  ssa_point_taken P f a tr (activation_enter dst env) e ->
  jump_env P (activation_frame f a) dst cs = Some env ->
  ~ In x (defs (ssa_var_view ext P f) e) -> env x = aenv a x.
Proof.
  intros Hwf Hat Hnot Htaken Hjump Houtside.
  destruct (ssa_taken_term_local ext P f a tr _ e t Hwf Hat Htaken)
    as [fd [b [p [Hf [Hb [Hpc [Ht [Hget [Htarget Hcases]]]]]]]]].
  destruct Hcases as [[target [args [_ ->]]]|[y [Hreturn Hpayload]]];
    [|exfalso; exact (Hnot y Hreturn)].
  cbn [ssa_transfer_payload spp_target activation_enter alabel apc fst snd] in Htarget.
  injection Htarget as Hdst; subst target.
  cbn [ssa_var_view defs] in Houtside; rewrite Hget in Houtside.
  cbn [ssa_transfer_payload spp_defs fst snd] in Houtside.
  unfold jump_env in Hjump; cbn [activation_frame ffunc fenv] in Hjump; rewrite Hf in Hjump.
  destruct (find_block fd dst) as [target|] eqn:Hblock; [|discriminate].
  assert (Hlookup : Map.get nat_encoding dst (first_index (ssa_blocks P f)) = Some target).
  { unfold ssa_blocks; rewrite Hf; exact Hblock. }
  unfold ssa_get in Houtside; rewrite Hlookup in Houtside.
  exact (ssa_bind_frame _ _ _ _ x Hjump Houtside).
Qed.

Local Lemma ssa_raw_defs_frame ext P f a tr a' e x :
  wf_program ext P -> step (activation ext P f) a tr a' ->
  ssa_point_taken P f a tr a' e -> ~ In x (defs (ssa_var_view ext P f) e) ->
  aenv a' x = aenv a x.
Proof.
  intros Hwf Hstep Htaken Houtside; destruct Hstep as
    [a y o args cs v Hat Hread Heval
    |a y n block offset Hat
    |a p Hat
    |a y t sz p v Hat Htype Hvalid
    |a sz p y Hat
    |a y v Hat Hvalue
    |a dst args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases d da z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c args dst ps r cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a y v Hat Hvalue].
  - pose proof (ssa_taken_instruction_index ext P f a [] _ e _ Hwf Hat Htaken) as Hindex.
    cbn [ssa_var_view defs] in Houtside; rewrite Hindex in Houtside.
    cbn [ssa_instruction_payload spp_defs instr_def] in Houtside.
    cbn [activation_advance aenv]; unfold env_set.
    destruct (Nat.eq_dec x y) as [->|Hdifferent]; [exfalso; apply Houtside; left; reflexivity|
      reflexivity].
  - pose proof (ssa_taken_instruction_index ext P f a [] _ e _ Hwf Hat Htaken) as Hindex.
    cbn [ssa_var_view defs] in Houtside; rewrite Hindex in Houtside.
    cbn [ssa_instruction_payload spp_defs instr_def] in Houtside.
    cbn [activation_advance aenv]; unfold env_set.
    destruct (Nat.eq_dec x y) as [->|Hdifferent]; [exfalso; apply Houtside; left; reflexivity|
      reflexivity].
  - reflexivity.
  - pose proof (ssa_taken_instruction_index ext P f a [] _ e _ Hwf Hat Htaken) as Hindex.
    cbn [ssa_var_view defs] in Houtside; rewrite Hindex in Houtside.
    cbn [ssa_instruction_payload spp_defs instr_def] in Houtside.
    cbn [activation_advance aenv]; unfold env_set.
    destruct (Nat.eq_dec x y) as [->|Hdifferent]; [exfalso; apply Houtside; left; reflexivity|
      reflexivity].
  - reflexivity.
  - reflexivity.
  - eapply ssa_transfer_defs_frame; try eassumption; intros y Hfalse; discriminate.
  - eapply ssa_transfer_defs_frame; try eassumption; intros y Hfalse; discriminate.
  - eapply ssa_transfer_defs_frame; try eassumption; intros y Hfalse; discriminate.
  - eapply ssa_transfer_defs_frame; try eassumption; intros y Hfalse; discriminate.
  - reflexivity.
Qed.

Local Lemma ssa_exit_instruction ext P f a i :
  wf_program ext P -> at_instr P (activation_frame f a) i ->
  Map.get (pair_encoding nat_encoding nat_encoding) (alabel a, apc a)
    (ssa_exit_index P f) = Some
      (if may_trap ssa_effects (AnInstr i) then instr_uses i else []).
Proof.
  intros Hwf [fd [b [Hf [Hb Hi]]]].
  cbn [activation_frame ffunc flabel fpc] in Hf, Hb, Hi.
  destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
  unfold ssa_exit_index; apply ssa_map_get_complete.
  - apply in_flat_map; exists (alabel a, b); split.
    + rewrite Hblocks; apply first_index_sound; exact Hb.
    + apply in_map_iff; exists (apc a, i); split; [reflexivity|].
      apply ssa_enumerate_nth; exists (apc a); split; [lia|exact Hi].
  - intros other Hrow; apply in_flat_map in Hrow.
    destruct Hrow as [[l block] [Hmember Hrow]]; rewrite Hblocks in Hmember.
    apply in_map_iff in Hrow; destruct Hrow as [[pc j] [Heq Henum]].
    cbn in Heq; injection Heq as Hlabel Hpc Hother; subst l pc other.
    assert (Hblock : block = b).
    { eapply ssa_label_unique; [exact Hunique|exact Hmember|].
      apply first_index_sound; exact Hb. }
    subst block; cbn [fst snd] in Henum.
    apply ssa_enumerate_nth in Henum; destruct Henum as [n [Hn Hj]].
    cbn in Hn; subst n; rewrite Hi in Hj; injection Hj as <-; reflexivity.
Qed.

Local Lemma ssa_raw_trap_operands ext P f a x o args cs :
  wf_program ext P -> reachable_state (activation ext P f) a ->
  at_instr P (activation_frame f a) (IOp x o args) ->
  read_args (aenv a) args = Some cs -> op_eval ext o cs = None ->
  exit_uses (ssa_var_view ext P f) (alabel a, apc a) = args.
Proof.
  intros Hwf Hreachable Hat Hread Hfail.
  destruct (activation_typed_operands ext P f a x o args Hwf Hreachable Hat)
    as [actual [ps [r [Hactual [Hsig [Htypes Hvalid]]]]]].
  rewrite Hread in Hactual; injection Hactual as <-.
  destruct (proj2 (op_eval_typed ext P o cs ps r
    (proj2 (proj2 (proj2 (proj2 Hwf)))) Hsig Htypes Hvalid) Hfail)
    as [[w ->]|[tag ->]].
  all: cbn [ssa_var_view exit_uses]; unfold ssa_get;
    rewrite (ssa_exit_instruction ext P f a _ Hwf Hat); reflexivity.
Qed.

Local Lemma ssa_raw_trap_agrees ext P f a t :
  wf_program ext P -> reachable_state (activation ext P f) a ->
  (alabel t, apc t) = (alabel a, apc a) ->
  (forall x, In x (exit_uses (ssa_var_view ext P f) (alabel a, apc a)) ->
    aenv a x = aenv t x) -> activation_trapped ext P f a -> activation_trapped ext P f t.
Proof.
  intros Hwf Hreachable Hpoint Hagree [x [o [args [cs [Hat [Hread Hfail]]]]]].
  exists x, o, args, cs; split.
  - injection Hpoint as Hlabel Hpc.
    apply (proj1 (ssa_at_instr_coordinates P (activation_frame f a)
      (activation_frame f t) _ eq_refl (eq_sym Hlabel) (eq_sym Hpc))); exact Hat.
  - split; [|exact Hfail].
    rewrite (ssa_raw_trap_operands ext P f a x o args cs Hwf Hreachable Hat Hread Hfail)
      in Hagree.
    cbn [activation_frame fenv].
    rewrite <- (ssa_read_equal_on (aenv a) (aenv t) args Hagree); exact Hread.
Qed.

Local Lemma ssa_raw_exits_determine ext P f a t :
  wf_program ext P -> reachable_state (activation ext P f) a ->
  reachable_state (activation ext P f) t -> (alabel t, apc t) = (alabel a, apc a) ->
  (forall x, In x (exit_uses (ssa_var_view ext P f) (alabel a, apc a)) ->
    aenv a x = aenv t x) ->
  (activation_final P f a <-> activation_final P f t) /\
  (activation_trapped ext P f a <-> activation_trapped ext P f t) /\ (False <-> False).
Proof.
  intros Hwf Ha Ht Hpoint Hagree; split.
  - unfold activation_final, ssa_frame_final; cbn [activation_frame ffunc flabel fpc].
    injection Hpoint as Hlabel Hpc; rewrite Hlabel, Hpc; reflexivity.
  - split; [|reflexivity]; split.
    + eapply ssa_raw_trap_agrees; eassumption.
    + eapply ssa_raw_trap_agrees; [exact Hwf|exact Ht|symmetry; exact Hpoint|].
      intros x Hx; symmetry; apply Hagree; rewrite <- Hpoint; exact Hx.
Qed.

Local Lemma ssa_instruction_matches ext P f a tr a' t i :
  at_instr P (activation_frame f a) i -> step (activation ext P f) a tr a' ->
  (alabel t, apc t) = (alabel a, apc a) ->
  (forall x, In x (instr_uses i) -> aenv a x = aenv t x) ->
  exists t', step (activation ext P f) t tr t' /\
    (alabel t', apc t') = (alabel a', apc a') /\
    forall x, In x (instr_def i) -> aenv a' x = aenv t' x.
Proof.
  intros Hi Hstep Hpoint Hagree; injection Hpoint as Hlabel Hpc.
  assert (Hat : at_instr P (activation_frame f t) i).
  { apply (proj1 (ssa_at_instr_coordinates P (activation_frame f a)
      (activation_frame f t) i eq_refl (eq_sym Hlabel) (eq_sym Hpc))); exact Hi. }
  destruct Hstep as
    [a y o args cs v Hlocal Hread Heval
    |a y n block offset Hlocal
    |a p Hlocal
    |a y ty sz p v Hlocal Htype Hvalid
    |a sz p y Hlocal
    |a y v Hlocal Hvalue
    |a dst args cs env Hlocal Hread Hbind
    |a c l1 a1 l2 a2 z dst args cs env Hlocal Hcond Hchoice Hread Hbind
    |a c cases d da z dst args cs env Hlocal Hcond Hchoice Hread Hbind
    |a c args dst ps r cs v env Hlocal Hsig Hread Htype Hvalid Hbind
    |a y v Hlocal Hvalue].
  all: try (exfalso; exact (ssa_at_instr_not_term P _ _ _ Hi Hlocal)).
  all: pose proof (ssa_at_instr_unique P _ _ _ Hi Hlocal) as ->.
  - exists (activation_advance t (env_set (aenv t) y v)); split.
    + eapply AOp; [exact Hat| |exact Heval].
      rewrite <- (ssa_read_equal_on (aenv a) (aenv t) args Hagree); exact Hread.
    + split; [cbn; congruence|]; intros x [<-|Hfalse]; [|contradiction].
      cbn [activation_advance aenv]; unfold env_set.
      destruct (Nat.eq_dec y y); [reflexivity|contradiction].
  - exists (activation_advance t (env_set (aenv t) y (VPtr block offset))); split.
    + eapply AAlloc; exact Hat.
    + split; [cbn; congruence|]; intros x [<-|Hfalse]; [|contradiction].
      cbn [activation_advance aenv]; unfold env_set.
      destruct (Nat.eq_dec y y); [reflexivity|contradiction].
  - exists (activation_advance t (aenv t)); split; [eapply AFree; exact Hat|].
    split; [cbn; congruence|intros x Hfalse; contradiction].
  - exists (activation_advance t (env_set (aenv t) y v)); split.
    + eapply ALoad; [exact Hat|exact Htype|exact Hvalid].
    + split; [cbn; congruence|]; intros x [<-|Hfalse]; [|contradiction].
      cbn [activation_advance aenv]; unfold env_set.
      destruct (Nat.eq_dec y y); [reflexivity|contradiction].
  - exists (activation_advance t (aenv t)); split; [eapply AStore; exact Hat|].
    split; [cbn; congruence|intros x Hfalse; contradiction].
  - exists (activation_advance t (aenv t)); split.
    + eapply AOutput; [exact Hat|].
      rewrite <- (Hagree y (or_introl eq_refl)); exact Hvalue.
    + split; [cbn; congruence|intros x Hfalse; contradiction].
Qed.

Local Lemma ssa_taken_transfer_index ext P f a tr a' e t slot dst args :
  wf_program ext P -> at_term P (activation_frame f a) t ->
  (forall x, t <> TRet x) -> ssa_term_slot (aenv a) t = Some slot ->
  nth_error (term_edges t) slot = Some (dst, args) -> ssa_point_taken P f a tr a' e ->
  exists fd b, find_func P f = Some fd /\ find_block fd (alabel a) = Some b /\
    bterm b = t /\ Map.get ssa_edge_encoding e (ssa_point_index P f) =
      Some (ssa_transfer_payload (first_index (ssa_blocks P f)) (alabel a) b (dst, args)).
Proof.
  intros Hwf Hat Hnot Hslot Hedge [p [Hget [Hsource [Htarget Haction]]]].
  destruct (ssa_point_index_local ext P f e p Hwf Hget)
    as [fd [l [b [Hf [Hb Hlocal]]]]].
  destruct Hlocal as [pc i Hnth|selected target actual Hnot' Hnth|x Hterm].
  - cbn [ssa_instruction_payload spp_source] in Hsource; injection Hsource as Hlabel Hpc.
    pose proof (ssa_at_term_end P _ t fd b Hat Hf) as Hend.
    cbn [activation_frame flabel fpc] in Hend.
    specialize (Hend ltac:(rewrite Hlabel; exact Hb)).
    assert (Hbefore : pc < length (bbody b)).
    { apply nth_error_Some; rewrite Hnth; discriminate. }
    lia.
  - cbn [ssa_transfer_payload spp_source] in Hsource;
      injection Hsource as Hlabel Hpc.
    assert (Ht : bterm b = t).
    { eapply ssa_at_term_unique; [|exact Hat].
      exists fd, b; cbn [activation_frame ffunc flabel fpc]; rewrite Hlabel.
      repeat split; assumption. }
    cbn [ssa_transfer_payload spp_action eslot] in Haction; rewrite Ht, Hpc in Haction.
    replace (length (bbody b) + selected - length (bbody b)) with selected in Haction by lia.
    assert (Hselected : ssa_term_slot (aenv a) t = Some selected).
    { destruct t; try exact Haction; exfalso; eapply Hnot; reflexivity. }
    rewrite Hslot in Hselected; injection Hselected as <-.
    rewrite Ht, Hedge in Hnth; injection Hnth as <- <-.
    exists fd, b; split; [exact Hf|]; split; [rewrite Hlabel; exact Hb|].
    split; [exact Ht|rewrite Hlabel; exact Hget].
  - cbn [spp_source] in Hsource; injection Hsource as Hlabel Hpc.
    exfalso; apply (Hnot x); symmetry; eapply ssa_at_term_unique; [|exact Hat].
    exists fd, b; cbn [activation_frame ffunc flabel fpc]; rewrite Hlabel.
    repeat split; assumption.
Qed.

Local Lemma ssa_taken_return_index ext P f a tr a' e x :
  wf_program ext P -> at_term P (activation_frame f a) (TRet x) ->
  ssa_point_taken P f a tr a' e ->
  Map.get ssa_edge_encoding e (ssa_point_index P f) =
    Some (SsaPointPayload (alabel a, apc a) (alabel a, S (apc a))
      [x] [] [x] Map.empty (ATerm (TRet x))).
Proof.
  intros Hwf Hat Htaken.
  destruct (ssa_taken_term_local ext P f a tr a' e (TRet x) Hwf Hat Htaken)
    as [fd [b [p [Hf [Hb [Hpc [Ht [Hget [Htarget Hcases]]]]]]]]].
  destruct Hcases as [[dst [args [Hnot _]]]|[y [Heq ->]]];
    [exfalso; exact (Hnot x eq_refl)|].
  injection Heq as <-; exact Hget.
Qed.

Local Lemma ssa_taken_same_points P f a tr a' t t' e p :
  ssa_point_taken P f a tr a' e ->
  Map.get ssa_edge_encoding e (ssa_point_index P f) = Some p ->
  (alabel t, apc t) = (alabel a, apc a) ->
  (alabel t', apc t') = (alabel a', apc a') ->
  (forall term, spp_action p = ATerm term ->
    ssa_term_slot (aenv a) term = ssa_term_slot (aenv t) term) ->
  ssa_point_taken P f t tr t' e.
Proof.
  intros [q [Hget [Hsource [Htarget Haction]]]] Hindex Hpoint Hpoint' Hslot.
  rewrite Hindex in Hget; injection Hget as <-.
  exists p; split; [exact Hindex|]; split; [rewrite Hpoint; exact Hsource|].
  split; [rewrite Hpoint'; exact Htarget|].
  injection Hpoint as Hlabel Hpc; rewrite Hpc.
  destruct (spp_action p) as [i|term] eqn:Haction_kind; [exact I|].
  destruct term; try exact I; rewrite <- (Hslot _ eq_refl); exact Haction.
Qed.

Local Lemma ssa_raw_instruction_matches ext P f a tr a' t e i :
  wf_program ext P -> at_instr P (activation_frame f a) i ->
  step (activation ext P f) a tr a' -> ssa_point_taken P f a tr a' e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  (forall x, In x (uses (ssa_var_view ext P f) e) -> aenv a x = aenv t x) ->
  exists t', step (activation ext P f) t tr t' /\ ssa_point_taken P f t tr t' e /\
    forall x, In x (defs (ssa_var_view ext P f) e) -> aenv a' x = aenv t' x.
Proof.
  intros Hwf Hat Hstep Htaken Hpoint Hagree.
  pose proof (ssa_taken_instruction_index ext P f a tr a' e i Hwf Hat Htaken) as Hindex.
  cbn [ssa_var_view uses] in Hagree; rewrite Hindex in Hagree.
  destruct (ssa_instruction_matches ext P f a tr a' t i Hat Hstep Hpoint Hagree)
    as [t' [Hstep' [Hpoint' Hwritten]]].
  exists t'; split; [exact Hstep'|]; split.
  - eapply ssa_taken_same_points; try eassumption; intros term Hfalse; discriminate.
  - cbn [ssa_var_view defs]; rewrite Hindex; exact Hwritten.
Qed.

Local Lemma ssa_jump_matches P f a t dst cs env :
  jump_env P (activation_frame f a) dst cs = Some env ->
  exists env', jump_env P (activation_frame f t) dst cs = Some env' /\
    forall x, In x (map fst (bparams (ssa_get nat_encoding
      (first_index (ssa_blocks P f)) (SBlock [] [] (TRet 0)) dst))) -> env x = env' x.
Proof.
  unfold jump_env; cbn [activation_frame ffunc fenv].
  destruct (find_func P f) as [fd|] eqn:Hf; [|discriminate].
  destruct (find_block fd dst) as [b|] eqn:Hb; [|discriminate].
  intro Hbind; destruct (ssa_bind_exists (aenv t) (bparams b) cs
    (ssa_bind_length _ _ _ _ Hbind)) as [env' Hbind'].
  exists env'; split; [exact Hbind'|].
  change (Map.get nat_encoding dst (first_index (blocks fd)) = Some b) in Hb.
  unfold ssa_blocks, ssa_get; rewrite Hf, Hb.
  exact (ssa_bind_written _ _ _ _ _ _ Hbind Hbind').
Qed.

Local Lemma ssa_raw_uses_determine ext P f a tr a' t e :
  wf_program ext P -> step (activation ext P f) a tr a' ->
  ssa_point_taken P f a tr a' e -> (alabel t, apc t) = (alabel a, apc a) ->
  (forall x, In x (uses (ssa_var_view ext P f) e) -> aenv a x = aenv t x) ->
  exists t', step (activation ext P f) t tr t' /\ ssa_point_taken P f t tr t' e /\
    forall x, In x (defs (ssa_var_view ext P f) e) -> aenv a' x = aenv t' x.
Proof.
  intros Hwf Hstep Htaken Hpoint Hagree; pose proof Hstep as Horiginal.
  assert (Hterm : forall term, at_term P (activation_frame f a) term ->
    at_term P (activation_frame f t) term).
  { intros term Hat; injection Hpoint as Hlabel Hpc.
    apply (proj1 (ssa_at_term_coordinates P (activation_frame f a)
      (activation_frame f t) term eq_refl (eq_sym Hlabel) (eq_sym Hpc))); exact Hat. }
  destruct Hstep as
    [a x o args cs v Hat Hread Heval
    |a x n block offset Hat
    |a p Hat
    |a x ty sz p v Hat Htype Hvalid
    |a sz p x Hat
    |a x v Hat Hvalue
    |a dst args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases d da z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c args dst ps r cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a x v Hat Hvalue].
  all: try solve [eapply ssa_raw_instruction_matches; eassumption].
  - destruct (ssa_taken_transfer_index ext P f a [] _ e (TJump dst args) 0 dst args
      Hwf Hat ltac:(intros y Hfalse; discriminate) eq_refl eq_refl Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    cbn [ssa_var_view uses] in Hagree; rewrite Hindex in Hagree.
    cbn [ssa_transfer_payload spp_uses] in Hagree; rewrite Ht in Hagree.
    cbn [ssa_selected_uses fst snd] in Hagree.
    destruct (ssa_jump_matches P f a t dst cs env Hbind) as [env' [Hbind' Hwritten]].
    exists (activation_enter dst env'); split.
    + eapply AJump; [apply Hterm; exact Hat| |exact Hbind'].
      rewrite <- (ssa_read_equal_on (aenv a) (aenv t) args Hagree); exact Hread.
    + split.
      * eapply ssa_taken_same_points; try eassumption; [reflexivity|].
        intros term Heq; cbn [ssa_transfer_payload spp_action] in Heq.
        rewrite Ht in Heq; injection Heq as <-; reflexivity.
      * cbn [ssa_var_view defs]; rewrite Hindex; exact Hwritten.
  - assert (Hslot : ssa_term_slot (aenv a) (TBr c l1 a1 l2 a2) =
        Some (if Z.eqb z 0 then 1 else 0)).
    { cbn [ssa_term_slot]; rewrite Hcond; reflexivity. }
    assert (Hedge : nth_error (term_edges (TBr c l1 a1 l2 a2))
        (if Z.eqb z 0 then 1 else 0) = Some (dst, args)).
    { cbn [term_edges]; destruct (Z.eqb z 0); injection Hchoice as <- <-; reflexivity. }
    destruct (ssa_taken_transfer_index ext P f a [] _ e _ _ dst args Hwf Hat
      ltac:(intros y Hfalse; discriminate) Hslot Hedge Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    cbn [ssa_var_view uses] in Hagree; rewrite Hindex in Hagree.
    cbn [ssa_transfer_payload spp_uses] in Hagree; rewrite Ht in Hagree.
    cbn [ssa_selected_uses fst snd] in Hagree.
    assert (Hcontrol : aenv a c = aenv t c) by (apply Hagree; left; reflexivity).
    destruct (ssa_jump_matches P f a t dst cs env Hbind) as [env' [Hbind' Hwritten]].
    exists (activation_enter dst env'); split.
    + eapply ABranch; [apply Hterm; exact Hat|rewrite <- Hcontrol; exact Hcond|
        exact Hchoice| |exact Hbind'].
      rewrite <- (ssa_read_equal_on (aenv a) (aenv t) args); [exact Hread|].
      intros x Hx; apply Hagree; right; exact Hx.
    + split.
      * eapply ssa_taken_same_points; try eassumption; [reflexivity|].
        intros term Heq; cbn [ssa_transfer_payload spp_action] in Heq.
        rewrite Ht in Heq; injection Heq as <-; cbn [ssa_term_slot]; rewrite Hcontrol;
          reflexivity.
      * cbn [ssa_var_view defs]; rewrite Hindex; exact Hwritten.
  - assert (Hslot : ssa_term_slot (aenv a) (TSwitch c cases d da) =
        Some (ssa_switch_slot z cases)).
    { cbn [ssa_term_slot]; rewrite Hcond; reflexivity. }
    assert (Hedge : nth_error (term_edges (TSwitch c cases d da))
        (ssa_switch_slot z cases) = Some (dst, args)).
    { rewrite <- Hchoice; exact (ssa_switch_slot_target z cases d da). }
    destruct (ssa_taken_transfer_index ext P f a [] _ e _ _ dst args Hwf Hat
      ltac:(intros y Hfalse; discriminate) Hslot Hedge Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    cbn [ssa_var_view uses] in Hagree; rewrite Hindex in Hagree.
    cbn [ssa_transfer_payload spp_uses] in Hagree; rewrite Ht in Hagree.
    cbn [ssa_selected_uses fst snd] in Hagree.
    assert (Hcontrol : aenv a c = aenv t c) by (apply Hagree; left; reflexivity).
    destruct (ssa_jump_matches P f a t dst cs env Hbind) as [env' [Hbind' Hwritten]].
    exists (activation_enter dst env'); split.
    + eapply ASwitch; [apply Hterm; exact Hat|rewrite <- Hcontrol; exact Hcond|
        exact Hchoice| |exact Hbind'].
      rewrite <- (ssa_read_equal_on (aenv a) (aenv t) args); [exact Hread|].
      intros x Hx; apply Hagree; right; exact Hx.
    + split.
      * eapply ssa_taken_same_points; try eassumption; [reflexivity|].
        intros term Heq; cbn [ssa_transfer_payload spp_action] in Heq.
        rewrite Ht in Heq; injection Heq as <-; cbn [ssa_term_slot]; rewrite Hcontrol;
          reflexivity.
      * cbn [ssa_var_view defs]; rewrite Hindex; exact Hwritten.
  - destruct (ssa_taken_transfer_index ext P f a [] _ e (TCall c args dst) 0 dst []
      Hwf Hat ltac:(intros y Hfalse; discriminate) eq_refl eq_refl Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    cbn [ssa_var_view uses] in Hagree; rewrite Hindex in Hagree.
    cbn [ssa_transfer_payload spp_uses] in Hagree; rewrite Ht in Hagree.
    cbn [ssa_selected_uses fst snd] in Hagree.
    destruct (ssa_jump_matches P f a t dst [v] env Hbind) as [env' [Hbind' Hwritten]].
    exists (activation_enter dst env'); split.
    + eapply ACall; [apply Hterm; exact Hat|exact Hsig| |exact Htype|exact Hvalid|
        exact Hbind'].
      rewrite <- (ssa_read_equal_on (aenv a) (aenv t) _ Hagree); exact Hread.
    + split.
      * eapply ssa_taken_same_points; try eassumption; [reflexivity|].
        intros term Heq; cbn [ssa_transfer_payload spp_action] in Heq.
        rewrite Ht in Heq; injection Heq as <-; reflexivity.
      * cbn [ssa_var_view defs]; rewrite Hindex; exact Hwritten.
  - pose proof (ssa_taken_return_index ext P f a [EvRet v] _ e x Hwf Hat Htaken)
      as Hindex.
    cbn [ssa_var_view uses] in Hagree; rewrite Hindex in Hagree.
    exists (activation_advance t (aenv t)); split.
    + eapply AReturn; [apply Hterm; exact Hat|].
      rewrite <- (Hagree x (or_introl eq_refl)); exact Hvalue.
    + split.
      * eapply ssa_taken_same_points; try eassumption.
        -- injection Hpoint as Hlabel Hpc; cbn; congruence.
        -- intros term Heq; cbn [spp_action] in Heq; injection Heq as <-; reflexivity.
      * cbn [ssa_var_view defs]; rewrite Hindex; intros x' Hfalse; contradiction.
Qed.

(** Every checked raw function satisfies the semantic variable-view laws. *)
Theorem ssa_var_view_laws (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  var_view_laws (activation ext P f) (activation_endings ext P f) (ssa_var_view ext P f).
Proof.
  intros Hwf Hfunction; constructor.
  - exact (ssa_point_graph_laws ext P f Hwf Hfunction).
  - intros a tr a' Hfalse; contradiction.
  - intros a tr a' e x Hreachable Hstep Htaken Houtside.
    exact (ssa_raw_defs_frame ext P f a tr a' e x Hwf Hstep Htaken Houtside).
  - intros a tr a' t e Ha Ht Hpoint Hstep Htaken Hagree.
    exact (ssa_raw_uses_determine ext P f a tr a' t e Hwf Hstep Htaken Hpoint Hagree).
  - intros a t Ha Ht Hpoint Hagree; exact
      (ssa_raw_exits_determine ext P f a t Hwf Ha Ht Hpoint Hagree).
Qed.

(** The canonical universe includes definitions from every original block. *)
Local Lemma ssa_values_member P f l b x :
  In (l, b) (ssa_blocks P f) -> In x (block_defs b) -> In x (values_of P f).
Proof.
  intros Hblock Hx; unfold values_of.
  apply (proj2 (FinSet.elements_spec nat_encoding x _ (demand_universe_wf _ _))).
  apply FinSet.of_list_spec, in_flat_map; exists (l, b); split; assumption.
Qed.

Local Lemma ssa_values_nodup P f : NoDup (values_of P f).
Proof.
  apply (FinSet.elements_nodup nat_encoding), demand_universe_wf.
Qed.

Local Lemma ssa_static_value P f x ty :
  static_ty P f x = Some ty -> In x (values_of P f).
Proof.
  unfold static_ty; destruct (find_func P f) as [fd|] eqn:Hf; [|discriminate].
  intro Htype; apply first_index_sound in Htype.
  unfold function_bindings, function_bindings_with in Htype; apply in_flat_map in Htype.
  destruct Htype as [[l b] [Hblock Hbinding]]; cbn [snd] in Hbinding.
  eapply ssa_values_member with (l := l) (b := b).
  - unfold ssa_blocks; rewrite Hf; exact Hblock.
  - unfold block_defs, body_defs; apply in_app_iff in Hbinding; apply in_or_app.
    destruct Hbinding as [Hparam|Hinstruction].
    + left; apply in_map_iff; exists (x, ty); split; [reflexivity|exact Hparam].
    + right; apply in_flat_map in Hinstruction; destruct Hinstruction as [i [Hi Hbinding]].
      apply in_flat_map; exists i; split; [exact Hi|].
      destruct i; cbn [instr_binding_with instr_def] in Hbinding |- *;
        try contradiction.
      * destruct (op_sig P o) as [[ps result]|]; [|contradiction].
        destruct Hbinding as [Heq|Hfalse]; [injection Heq as <- <-; left; reflexivity|
          contradiction].
      * destruct Hbinding as [Heq|Hfalse]; [injection Heq as <- <-; left; reflexivity|
          contradiction].
      * destruct Hbinding as [Heq|Hfalse]; [injection Heq as <- <-; left; reflexivity|
          contradiction].
Qed.

Local Lemma ssa_instruction_values ext P f fd l b i :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  In i (bbody b) -> Forall (fun x => In x (values_of P f)) (instr_uses i ++ instr_def i).
Proof.
  intros Hwf Hf Hb Hi; apply Forall_app; split.
  - pose proof (proj1 (proj2 (wf_block ext P f fd l b Hwf Hf Hb))) as Hbody.
    pose proof (proj1 (Forall_forall _ _) Hbody i Hi) as Htyped.
    pose proof (ssa_instruction_types_defined P _ i Htyped) as Hdefined.
    apply Forall_forall; intros x Hx; destruct (proj1 (Forall_forall _ _) Hdefined x Hx)
      as [ty Htype]; exact (ssa_static_value P f x ty Htype).
  - apply Forall_forall; intros x Hx; eapply ssa_values_member with (l := l) (b := b).
    + unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
    + unfold block_defs, body_defs; apply in_or_app; right; apply in_flat_map.
      exists i; split; assumption.
Qed.

Local Lemma ssa_selected_values ext P f fd l b dst args :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  In (dst, args) (term_edges (bterm b)) ->
  Forall (fun x => In x (values_of P f)) (ssa_selected_uses (bterm b) args).
Proof.
  intros Hwf Hf Hb Hedge.
  pose proof (proj1 (proj2 (proj2 (wf_block ext P f fd l b Hwf Hf Hb)))) as Htyped.
  pose proof (ssa_term_edge_types_defined P fd _ _ _ dst args Htyped Hedge) as Hargs.
  assert (Hdefined : Forall (fun x => exists ty, static_ty P f x = Some ty)
    (ssa_selected_uses (bterm b) args)).
  { destruct (bterm b) as [target actual|c l1 a1 l2 a2|c cases d da|c actual k|x];
      cbn [ssa_selected_uses] in *.
    - exact Hargs.
    - constructor; [exists TyI32; exact (proj1 Htyped)|exact Hargs].
    - constructor; [exists TyI32; exact (proj1 Htyped)|exact Hargs].
    - eapply ssa_call_types_defined; exact Htyped.
    - constructor; [eexists; exact Htyped|constructor]. }
  apply Forall_forall; intros x Hx.
  destruct (proj1 (Forall_forall _ _) Hdefined x Hx) as [ty Htype].
  exact (ssa_static_value P f x ty Htype).
Qed.

Local Lemma ssa_target_parameter_values ext P f fd dst b :
  wf_program ext P -> find_func P f = Some fd -> find_block fd dst = Some b ->
  Forall (fun x => In x (values_of P f)) (map fst (bparams b)).
Proof.
  intros Hwf Hf Hb; apply Forall_forall; intros x Hx.
  eapply ssa_values_member with (l := dst) (b := b).
  - unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
  - unfold block_defs; apply in_or_app; left; exact Hx.
Qed.

Local Lemma ssa_payload_values ext P f e p :
  wf_program ext P -> Map.get ssa_edge_encoding e (ssa_point_index P f) = Some p ->
  Forall (fun x => In x (values_of P f)) (spp_uses p ++ spp_defs p).
Proof.
  intros Hwf Hget; destruct (ssa_point_index_local ext P f e p Hwf Hget)
    as [fd [l [b [Hf [Hb Hlocal]]]]].
  destruct Hlocal as [pc i Hi|slot dst args Hnot Hedge|x Hterm].
  - apply ssa_instruction_values with (ext := ext) (fd := fd) (l := l) (b := b);
      try assumption; apply nth_error_In with pc; exact Hi.
  - cbn [ssa_transfer_payload spp_uses spp_defs fst snd]; apply Forall_app; split.
    + eapply ssa_selected_values; try eassumption; apply nth_error_In with slot; exact Hedge.
    + destruct (ssa_term_target ext P f fd l b dst args Hwf Hf Hb
        (nth_error_In _ slot Hedge)) as [target Htarget].
      assert (Hlookup : Map.get nat_encoding dst (first_index (ssa_blocks P f)) =
          Some target).
      { unfold ssa_blocks; rewrite Hf; exact Htarget. }
      unfold ssa_get; rewrite Hlookup.
      eapply ssa_target_parameter_values; eassumption.
  - cbn [spp_uses spp_defs app]; constructor; [|constructor].
    pose proof (proj1 (proj2 (proj2 (wf_block ext P f fd l b Hwf Hf Hb)))) as Htyped.
    rewrite Hterm in Htyped; eapply ssa_static_value; exact Htyped.
Qed.

Local Lemma ssa_payload_dependencies B l b e p :
  ssa_point_local B l b e p ->
  (forall x, In x (spp_forced p) -> In x (spp_uses p)) /\
  (forall x ys y, Map.get nat_encoding x (spp_back p) = Some ys ->
    In y ys -> In y (spp_uses p)).
Proof.
  intro Hlocal; destruct Hlocal as [pc i Hi|slot dst args Hnot Hedge|x Hterm].
  - split.
    + cbn [ssa_instruction_payload spp_forced spp_uses];
        destruct (effectful ssa_effects KeepTraps (AnInstr i)); [tauto|contradiction].
    + destruct i as [result op args|result n|pointer|result ty size pointer|
        size pointer value|value]; cbn [ssa_instruction_payload spp_back spp_uses];
        intros x' ys y Hget Hy; try (rewrite Map.get_empty in Hget; discriminate).
      destruct (Nat.eq_dec x' result) as [->|Hdifferent].
      * rewrite Map.get_set_same in Hget; injection Hget as <-; exact Hy.
      * rewrite Map.get_set_other, Map.get_empty in Hget by exact Hdifferent; discriminate.
  - split.
    + cbn [ssa_transfer_payload spp_forced spp_uses].
      destruct (bterm b); cbn [ssa_selected_uses In]; tauto.
    + cbn [ssa_transfer_payload spp_back spp_uses].
      destruct (bterm b) as [target actual|c l1 a1 l2 a2|c cases d da|c actual k|x]
        eqn:Hterm; intros x' ys y Hget Hy;
        try (rewrite Map.get_empty in Hget; discriminate).
      * exact (ssa_parameter_back_uses _ _ _ _ _ Hget Hy).
      * right; exact (ssa_parameter_back_uses _ _ _ _ _ Hget Hy).
      * right; exact (ssa_parameter_back_uses _ _ _ _ _ Hget Hy).
      * exfalso; eapply Hnot; reflexivity.
  - split; [tauto|intros x' ys y Hget Hy; cbn [spp_back] in Hget;
      rewrite Map.get_empty in Hget; discriminate].
Qed.

Local Lemma ssa_exit_values ext P f n :
  wf_program ext P -> Forall (fun x => In x (values_of P f))
    (exit_uses (ssa_var_view ext P f) n).
Proof.
  intro Hwf; cbn [ssa_var_view exit_uses]; unfold ssa_get.
  destruct (Map.get (pair_encoding nat_encoding nat_encoding) n (ssa_exit_index P f))
    as [xs|] eqn:Hget; [|constructor].
  apply (ssa_map_get_sound (pair_encoding nat_encoding nat_encoding)) in Hget.
  apply in_flat_map in Hget; destruct Hget as [[l b] [Hblock Hrow]].
  apply in_map_iff in Hrow; destruct Hrow as [[pc i] [Heq Henum]].
  cbn in Heq; injection Heq as <- <-.
  change (Forall (fun x => In x (values_of P f))
    (if may_trap ssa_effects (AnInstr i) then instr_uses i else [])).
  destruct (may_trap ssa_effects (AnInstr i)); [|constructor].
  unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
    [|contradiction].
  assert (Hb : find_block fd l = Some b).
  { apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
      exact Hblock]. }
  apply ssa_enumerate_nth in Henum; destruct Henum as [offset [_ Hi]].
  pose proof (ssa_instruction_values ext P f fd l b i Hwf Hf Hb
    (nth_error_In _ offset Hi)) as Hvalues.
  apply Forall_app in Hvalues; exact (proj1 Hvalues).
Qed.

Local Lemma ssa_forced_demands ext P f e :
  dnec (ssa_demand_view ext P f) e =
    match Map.get ssa_edge_encoding e (ssa_point_index P f) with
    | Some p => ssa_true_demands (spp_forced p)
    | None => []
    end.
Proof.
  cbn [ssa_demand_view dnec]; unfold ssa_get; rewrite Map.get_map.
  destruct (Map.get ssa_edge_encoding e (ssa_point_index P f)); reflexivity.
Qed.

Local Lemma ssa_backward_demands ext P f e x :
  dback (ssa_demand_view ext P f) e x true =
    match Map.get ssa_edge_encoding e (ssa_point_index P f) with
    | Some p => ssa_true_demands (ssa_get nat_encoding (spp_back p) [] x)
    | None => []
    end.
Proof.
  cbn [ssa_demand_view dback]; unfold ssa_get; rewrite Map.get_map.
  destruct (Map.get ssa_edge_encoding e (ssa_point_index P f)) as [p|]; [|reflexivity].
  cbn; rewrite Map.get_map; destruct (Map.get nat_encoding x (spp_back p)); reflexivity.
Qed.

(** Every demand operand is supported, even at unreachable nodes or malformed queries. *)
Lemma ssa_demand_vars ext P f :
  wf_program ext P -> demand_vars_ok (ssa_demand_view ext P f).
Proof.
  intro Hwf; split; [apply ssa_values_nodup|]; split.
  - intros e x needed y demand Hin; apply in_app_iff in Hin.
    destruct Hin as [Hforced|Hback].
    + rewrite ssa_forced_demands in Hforced.
      destruct (Map.get ssa_edge_encoding e (ssa_point_index P f)) as [p|] eqn:Hindex;
        [|contradiction].
      apply in_map_iff in Hforced; destruct Hforced as [z [Heq Hz]];
        injection Heq as <- <-.
      destruct (ssa_point_index_local ext P f e p Hwf Hindex)
        as [fd [l [b [Hf [Hb Hlocal]]]]].
      pose proof (ssa_payload_values ext P f e p Hwf Hindex) as Hvalues.
      apply (proj1 (Forall_forall _ _) Hvalues); apply in_or_app; left.
      exact (proj1 (ssa_payload_dependencies _ _ _ _ _ Hlocal) z Hz).
    + destruct needed; [|contradiction].
      rewrite ssa_backward_demands in Hback.
      destruct (Map.get ssa_edge_encoding e (ssa_point_index P f)) as [p|] eqn:Hindex;
        [|contradiction].
      unfold ssa_get in Hback; destruct (Map.get nat_encoding x (spp_back p))
        as [ys|] eqn:Hinputs; [|contradiction].
      apply in_map_iff in Hback; destruct Hback as [z [Heq Hz]]; injection Heq as <- <-.
      destruct (ssa_point_index_local ext P f e p Hwf Hindex)
        as [fd [l [b [Hf [Hb Hlocal]]]]].
      pose proof (ssa_payload_values ext P f e p Hwf Hindex) as Hvalues.
      apply (proj1 (Forall_forall _ _) Hvalues); apply in_or_app; left.
      exact (proj2 (ssa_payload_dependencies _ _ _ _ _ Hlocal) x ys z Hinputs Hz).
  - split.
    + intros n y needed Hin; rewrite ssa_exit_demands in Hin.
      apply in_map_iff in Hin; destruct Hin as [z [Heq Hz]]; injection Heq as <- <-.
      exact (proj1 (Forall_forall _ _) (ssa_exit_values ext P f n Hwf) z Hz).
    + intros e x Hin; cbn [ssa_demand_view ddefs ssa_var_view defs] in Hin.
      destruct (Map.get ssa_edge_encoding e (ssa_point_index P f)) as [p|] eqn:Hindex;
        [|contradiction].
      apply (proj1 (Forall_forall _ _) (ssa_payload_values ext P f e p Hwf Hindex)).
      apply in_or_app; right; exact Hin.
Qed.

Local Lemma ssa_demand_forced_inputs ext P f e p d a t :
  wf_program ext P -> Map.get ssa_edge_encoding e (ssa_point_index P f) = Some p ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f))
    (demand_transfer nat_encoding bool_demand (ssa_demand_view ext P f) e d) a t ->
  forall x, In x (spp_forced p) -> aenv a x = aenv t x.
Proof.
  intros Hwf Hindex Hagree x Hx.
  apply (ssa_bool_forced_agrees nat_encoding (ssa_demand_view ext P f) e d a t x
    (ssa_demand_vars ext P f Hwf) Hagree).
  rewrite ssa_forced_demands, Hindex; apply in_map_iff; exists x; split; [reflexivity|exact Hx].
Qed.

Local Lemma ssa_demand_back_inputs ext P f e p d a t x :
  wf_program ext P -> Map.get ssa_edge_encoding e (ssa_point_index P f) = Some p ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f))
    (demand_transfer nat_encoding bool_demand (ssa_demand_view ext P f) e d) a t ->
  In x (spp_defs p) -> dget nat_encoding bool_lattice d x = true ->
  forall y, In y (ssa_get nat_encoding (spp_back p) [] x) -> aenv a y = aenv t y.
Proof.
  intros Hwf Hindex Hagree Hdef Hneeded y Hy.
  apply (ssa_bool_backward_agrees nat_encoding (ssa_demand_view ext P f) e d a t x y
    (ssa_demand_vars ext P f Hwf) Hagree).
  - cbn [ssa_demand_view ddefs ssa_var_view defs]; rewrite Hindex; exact Hdef.
  - exact Hneeded.
  - rewrite ssa_backward_demands, Hindex; apply in_map_iff; exists y;
      split; [reflexivity|exact Hy].
Qed.

Local Lemma ssa_demand_outputs ext P f a tr a' t t' e d :
  wf_program ext P -> step (activation ext P f) a tr a' -> ssa_point_taken P f a tr a' e ->
  step (activation ext P f) t tr t' -> ssa_point_taken P f t tr t' e ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f))
    (demand_transfer nat_encoding bool_demand (ssa_demand_view ext P f) e d) a t ->
  (forall x, In x (defs (ssa_var_view ext P f) e) -> dget nat_encoding bool_lattice d x = true ->
    aenv a' x = aenv t' x) ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f)) d a' t'.
Proof.
  intros Hwf Hstep Htaken Hstep' Htaken' Hagree Hwritten x Hneeded.
  change (aenv a' x = aenv t' x).
  destruct (in_dec Nat.eq_dec x (defs (ssa_var_view ext P f) e)) as [Hdef|Houtside].
  - exact (Hwritten x Hdef Hneeded).
  - rewrite (ssa_raw_defs_frame ext P f a tr a' e x Hwf Hstep Htaken Houtside),
      (ssa_raw_defs_frame ext P f t tr t' e x Hwf Hstep' Htaken' Houtside).
    exact (ssa_bool_frame_agrees nat_encoding (ssa_demand_view ext P f) e d a t x
      Hagree Houtside Hneeded).
Qed.

Local Lemma ssa_demand_all_inputs ext P f a tr a' t e d :
  wf_program ext P -> step (activation ext P f) a tr a' -> ssa_point_taken P f a tr a' e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f))
    (demand_transfer nat_encoding bool_demand (ssa_demand_view ext P f) e d) a t ->
  (forall x, In x (uses (ssa_var_view ext P f) e) -> aenv a x = aenv t x) ->
  exists t', step (activation ext P f) t tr t' /\ ssa_point_taken P f t tr t' e /\
    agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f)) d a' t'.
Proof.
  intros Hwf Hstep Htaken Hpoint Hagree Hinputs.
  destruct (ssa_raw_uses_determine ext P f a tr a' t e Hwf Hstep Htaken Hpoint Hinputs)
    as [t' [Hstep' [Htaken' Hwritten]]].
  exists t'; split; [exact Hstep'|]; split; [exact Htaken'|].
  eapply ssa_demand_outputs; try eassumption; intros x Hx Hneeded; exact (Hwritten x Hx).
Qed.

Local Lemma ssa_demand_effectful_instruction ext P f a tr a' t e d i :
  wf_program ext P -> at_instr P (activation_frame f a) i ->
  step (activation ext P f) a tr a' -> ssa_point_taken P f a tr a' e ->
  (alabel t, apc t) = (alabel a, apc a) -> effectful ssa_effects KeepTraps (AnInstr i) = true ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f))
    (demand_transfer nat_encoding bool_demand (ssa_demand_view ext P f) e d) a t ->
  exists t', step (activation ext P f) t tr t' /\ ssa_point_taken P f t tr t' e /\
    agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f)) d a' t'.
Proof.
  intros Hwf Hat Hstep Htaken Hpoint Hflag Hagree.
  pose proof (ssa_taken_instruction_index ext P f a tr a' e i Hwf Hat Htaken) as Hindex.
  apply (ssa_demand_all_inputs ext P f a tr a' t e d Hwf Hstep Htaken Hpoint Hagree).
  cbn [ssa_var_view uses]; rewrite Hindex; intros x Hx.
  apply (ssa_demand_forced_inputs ext P f e _ d a t Hwf Hindex Hagree x).
  cbn [ssa_instruction_payload spp_forced]; rewrite Hflag; exact Hx.
Qed.

Local Lemma ssa_pure_operation_progress ext P f t x o args :
  wf_program ext P -> reachable_state (activation ext P f) t ->
  at_instr P (activation_frame f t) (IOp x o args) ->
  may_trap ssa_effects (AnInstr (IOp x o args)) = false ->
  exists cs v, read_args (aenv t) args = Some cs /\ op_eval ext o cs = Some v.
Proof.
  intros Hwf Hreachable Hat Hflag.
  destruct (activation_typed_operands ext P f t x o args Hwf Hreachable Hat)
    as [cs [ps [r [Hread [Hsig [Htypes Hvalid]]]]]].
  destruct (op_eval ext o cs) as [v|] eqn:Heval;
    [exists cs, v; split; assumption|].
  destruct (proj2 (op_eval_typed ext P o cs ps r
    (proj2 (proj2 (proj2 (proj2 Hwf)))) Hsig Htypes Hvalid) Heval)
    as [[w ->]|[tag ->]]; discriminate Hflag.
Qed.

Local Lemma ssa_demand_operation_matches ext P f a t e d x o args cs v :
  wf_program ext P -> reachable_state (activation ext P f) t ->
  at_instr P (activation_frame f a) (IOp x o args) -> read_args (aenv a) args = Some cs ->
  op_eval ext o cs = Some v ->
  ssa_point_taken P f a [] (activation_advance a (env_set (aenv a) x v)) e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f))
    (demand_transfer nat_encoding bool_demand (ssa_demand_view ext P f) e d) a t ->
  exists t', step (activation ext P f) t [] t' /\ ssa_point_taken P f t [] t' e /\
    agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f)) d
      (activation_advance a (env_set (aenv a) x v)) t'.
Proof.
  intros Hwf Hreachable Hat Hread Heval Htaken Hpoint Hagree.
  assert (Hstep : step (activation ext P f) a []
    (activation_advance a (env_set (aenv a) x v))) by (eapply AOp; eassumption).
  pose proof (ssa_taken_instruction_index ext P f a [] _ e _ Hwf Hat Htaken) as Hindex.
  destruct (dget nat_encoding bool_lattice d x) eqn:Hneeded.
  - apply (ssa_demand_all_inputs ext P f a [] _ t e d Hwf Hstep Htaken Hpoint Hagree).
    cbn [ssa_var_view uses]; rewrite Hindex; intros y Hy.
    apply (ssa_demand_back_inputs ext P f e _ d a t x Hwf Hindex Hagree
      (or_introl eq_refl) Hneeded y).
    cbn [ssa_instruction_payload spp_back]; unfold ssa_get; rewrite Map.get_set_same; exact Hy.
  - destruct (effectful ssa_effects KeepTraps (AnInstr (IOp x o args))) eqn:Hflag.
    + exact (ssa_demand_effectful_instruction ext P f a [] _ t e d _ Hwf Hat Hstep Htaken
        Hpoint Hflag Hagree).
    + assert (Hat' : at_instr P (activation_frame f t) (IOp x o args)).
      { injection Hpoint as Hlabel Hpc.
        apply (proj1 (ssa_at_instr_coordinates P (activation_frame f a)
          (activation_frame f t) _ eq_refl (eq_sym Hlabel) (eq_sym Hpc))); exact Hat. }
      destruct (ssa_pure_operation_progress ext P f t x o args Hwf Hreachable Hat'
        (ssa_effectful_false_trap _ _ Hflag)) as [cs' [v' [Hread' Heval']]].
      assert (Hstep' : step (activation ext P f) t []
        (activation_advance t (env_set (aenv t) x v'))) by (eapply AOp; eassumption).
      assert (Htaken' : ssa_point_taken P f t []
        (activation_advance t (env_set (aenv t) x v')) e).
      { eapply ssa_taken_same_points; try eassumption.
        - injection Hpoint as Hlabel Hpc; cbn; congruence.
        - intros term Hfalse; discriminate. }
      exists (activation_advance t (env_set (aenv t) x v')); split; [exact Hstep'|].
      split; [exact Htaken'|].
      eapply ssa_demand_outputs; try eassumption.
      cbn [ssa_var_view defs]; rewrite Hindex; intros y [<-|Hfalse] Hlive;
        [rewrite Hneeded in Hlive; discriminate|contradiction].
Qed.

Local Lemma ssa_selected_arguments_bound ext P f t term dst args :
  wf_program ext P -> reachable_state (activation ext P f) t ->
  at_term P (activation_frame f t) term -> In (dst, args) (term_edges term) ->
  exists cs, read_args (aenv t) args = Some cs.
Proof.
  intros Hwf Hreachable Hat Hedge; apply read_args_exists; intros x Hx.
  exact (ssa_term_operands_bound ext P (activation_frame f t) term Hwf
    (proj2 (activation_reachable_good ext P f t Hwf Hreachable)) Hat x
    (ssa_edge_argument_use term dst args x Hedge Hx)).
Qed.

Local Lemma ssa_jump_reread P f a t dst args cs cs' env :
  read_args (aenv a) args = Some cs -> jump_env P (activation_frame f a) dst cs = Some env ->
  read_args (aenv t) args = Some cs' ->
  exists env', jump_env P (activation_frame f t) dst cs' = Some env'.
Proof.
  intros Hread; unfold jump_env; cbn [activation_frame ffunc fenv].
  destruct (find_func P f) as [fd|]; [|discriminate].
  destruct (find_block fd dst) as [b|]; [|discriminate].
  intros Hbind Hread'; apply ssa_bind_exists.
  pose proof (ssa_bind_length _ _ _ _ Hbind).
  pose proof (ssa_read_length _ _ _ Hread); pose proof (ssa_read_length _ _ _ Hread'); lia.
Qed.

Local Lemma ssa_demand_binding_outputs ext P f a t e d l b dst args cs cs' env env' :
  wf_program ext P ->
  Map.get ssa_edge_encoding e (ssa_point_index P f) =
    Some (ssa_transfer_payload (first_index (ssa_blocks P f)) l b (dst, args)) ->
  (match bterm b with TCall _ _ _ => False | _ => True end) ->
  read_args (aenv a) args = Some cs -> read_args (aenv t) args = Some cs' ->
  jump_env P (activation_frame f a) dst cs = Some env ->
  jump_env P (activation_frame f t) dst cs' = Some env' ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f))
    (demand_transfer nat_encoding bool_demand (ssa_demand_view ext P f) e d) a t ->
  forall x, In x (defs (ssa_var_view ext P f) e) -> dget nat_encoding bool_lattice d x = true ->
    env x = env' x.
Proof.
  intros Hwf Hindex Hordinary Hread Hread' Hjump Hjump' Hagree x Hdef Hneeded.
  unfold jump_env in Hjump, Hjump'; cbn [activation_frame ffunc fenv] in Hjump, Hjump'.
  destruct (find_func P f) as [fd|] eqn:Hf; [|discriminate].
  destruct (find_block fd dst) as [target|] eqn:Htarget; [|discriminate].
  assert (Hlookup : Map.get nat_encoding dst (first_index (ssa_blocks P f)) = Some target).
  { unfold ssa_blocks; rewrite Hf; exact Htarget. }
  pose proof (ssa_parameter_nodup ext P f fd dst target Hwf Hf Htarget) as Hunique.
  cbn [ssa_var_view defs] in Hdef; rewrite Hindex in Hdef.
  cbn [ssa_transfer_payload spp_defs fst snd] in Hdef; unfold ssa_get in Hdef;
    rewrite Hlookup in Hdef.
  assert (Hlength : length (map fst (bparams target)) = length args).
  { rewrite length_map; pose proof (ssa_bind_length _ _ _ _ Hjump).
    pose proof (ssa_read_length _ _ _ Hread); lia. }
  destruct (ssa_parameter_back_argument _ _ x Hunique Hlength Hdef) as [y [Hback Hpair]].
  rewrite (ssa_bind_argument _ _ _ _ _ _ x y Hunique Hjump Hread Hpair),
    (ssa_bind_argument _ _ _ _ _ _ x y Hunique Hjump' Hread' Hpair).
  apply (ssa_demand_back_inputs ext P f e _ d a t x Hwf Hindex Hagree).
  - cbn [ssa_transfer_payload spp_defs fst snd]; unfold ssa_get; rewrite Hlookup; exact Hdef.
  - exact Hneeded.
  - cbn [ssa_transfer_payload spp_back fst snd]; unfold ssa_get; rewrite Hlookup.
    destruct (bterm b); try contradiction; rewrite Hback; left; reflexivity.
Qed.

Local Lemma ssa_demand_ordinary_transfer ext P f a t e d term slot dst args cs env :
  wf_program ext P -> reachable_state (activation ext P f) t ->
  at_term P (activation_frame f a) term ->
  (match term with TCall _ _ _ | TRet _ => False | _ => True end) ->
  ssa_term_slot (aenv a) term = Some slot -> ssa_term_slot (aenv t) term = Some slot ->
  nth_error (term_edges term) slot = Some (dst, args) ->
  read_args (aenv a) args = Some cs -> jump_env P (activation_frame f a) dst cs = Some env ->
  step (activation ext P f) a [] (activation_enter dst env) ->
  ssa_point_taken P f a [] (activation_enter dst env) e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f))
    (demand_transfer nat_encoding bool_demand (ssa_demand_view ext P f) e d) a t ->
  (forall cs' env', read_args (aenv t) args = Some cs' ->
    jump_env P (activation_frame f t) dst cs' = Some env' ->
    step (activation ext P f) t [] (activation_enter dst env')) ->
  exists t', step (activation ext P f) t [] t' /\ ssa_point_taken P f t [] t' e /\
    agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f)) d
      (activation_enter dst env) t'.
Proof.
  intros Hwf Hreachable Hat Hordinary Hslot Hslot' Hedge Hread Hjump Hstep Htaken Hpoint
    Hagree Hconstruct.
  assert (Hnot : forall x, term <> TRet x).
  { intros x ->; contradiction. }
  destruct (ssa_taken_transfer_index ext P f a [] _ e term slot dst args
    Hwf Hat Hnot Hslot Hedge Htaken) as [fd [b [Hf [Hb [Ht Hindex]]]]].
  assert (Hat' : at_term P (activation_frame f t) term).
  { injection Hpoint as Hlabel Hpc.
    apply (proj1 (ssa_at_term_coordinates P (activation_frame f a)
      (activation_frame f t) term eq_refl (eq_sym Hlabel) (eq_sym Hpc))); exact Hat. }
  destruct (ssa_selected_arguments_bound ext P f t term dst args Hwf Hreachable Hat'
    (nth_error_In _ slot Hedge)) as [cs' Hread'].
  destruct (ssa_jump_reread P f a t dst args cs cs' env Hread Hjump Hread')
    as [env' Hjump'].
  pose proof (Hconstruct cs' env' Hread' Hjump') as Hstep'.
  assert (Htaken' : ssa_point_taken P f t [] (activation_enter dst env') e).
  { eapply ssa_taken_same_points; try eassumption; [reflexivity|].
    intros selected Heq; cbn [ssa_transfer_payload spp_action] in Heq.
    rewrite Ht in Heq; injection Heq as <-; rewrite Hslot, Hslot'; reflexivity. }
  exists (activation_enter dst env'); split; [exact Hstep'|]; split; [exact Htaken'|].
  apply (ssa_demand_outputs ext P f a [] (activation_enter dst env) t
    (activation_enter dst env') e d Hwf Hstep Htaken Hstep' Htaken' Hagree).
  apply (ssa_demand_binding_outputs ext P f a t e d (alabel a) b dst args cs cs' env env'
    Hwf Hindex); try assumption.
  rewrite Ht; destruct term; try contradiction; exact I.
Qed.

Local Lemma ssa_demand_steps ext P f a tr a' t e d :
  wf_program ext P -> reachable_state (activation ext P f) t ->
  step (activation ext P f) a tr a' -> ssa_point_taken P f a tr a' e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f))
    (demand_transfer nat_encoding bool_demand (ssa_demand_view ext P f) e d) a t ->
  exists t', step (activation ext P f) t tr t' /\ ssa_point_taken P f t tr t' e /\
    agree (demand_agreement nat_encoding bool_demand (ssa_demand_view ext P f)) d a' t'.
Proof.
  intros Hwf Hreachable Hstep Htaken Hpoint Hagree; pose proof Hstep as Horiginal.
  assert (Hterm : forall term, at_term P (activation_frame f a) term ->
    at_term P (activation_frame f t) term).
  { intros term Hat; injection Hpoint as Hlabel Hpc.
    apply (proj1 (ssa_at_term_coordinates P (activation_frame f a)
      (activation_frame f t) term eq_refl (eq_sym Hlabel) (eq_sym Hpc))); exact Hat. }
  destruct Hstep as
    [a x o args cs v Hat Hread Heval
    |a x n block offset Hat
    |a p Hat
    |a x ty sz p v Hat Htype Hvalid
    |a sz p x Hat
    |a x v Hat Hvalue
    |a dst args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases def da z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c args dst ps r cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a x v Hat Hvalue].
  all: try solve [eapply ssa_demand_effectful_instruction; try eassumption; reflexivity].
  - exact (ssa_demand_operation_matches ext P f a t e d x o args cs v Hwf Hreachable
      Hat Hread Heval Htaken Hpoint Hagree).
  - apply (ssa_demand_ordinary_transfer ext P f a t e d (TJump dst args) 0 dst args cs env
      Hwf Hreachable Hat I eq_refl eq_refl eq_refl Hread Hbind Horiginal Htaken Hpoint Hagree).
    intros cs' env' Hread' Hbind'; eapply AJump; [apply Hterm; exact Hat|exact Hread'|
      exact Hbind'].
  - assert (Hslot : ssa_term_slot (aenv a) (TBr c l1 a1 l2 a2) =
        Some (if Z.eqb z 0 then 1 else 0)).
    { cbn [ssa_term_slot]; rewrite Hcond; reflexivity. }
    assert (Hedge : nth_error (term_edges (TBr c l1 a1 l2 a2))
        (if Z.eqb z 0 then 1 else 0) = Some (dst, args)).
    { cbn [term_edges]; destruct (Z.eqb z 0); injection Hchoice as <- <-; reflexivity. }
    destruct (ssa_taken_transfer_index ext P f a [] _ e _ _ dst args Hwf Hat
      ltac:(intros y Hfalse; discriminate) Hslot Hedge Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    assert (Hcontrol : aenv a c = aenv t c).
    { apply (ssa_demand_forced_inputs ext P f e _ d a t Hwf Hindex Hagree c).
      cbn [ssa_transfer_payload spp_forced]; rewrite Ht; left; reflexivity. }
    assert (Hslot' : ssa_term_slot (aenv t) (TBr c l1 a1 l2 a2) =
        Some (if Z.eqb z 0 then 1 else 0)).
    { cbn [ssa_term_slot]; rewrite <- Hcontrol, Hcond; reflexivity. }
    apply (ssa_demand_ordinary_transfer ext P f a t e d _ _ dst args cs env Hwf Hreachable
      Hat I Hslot Hslot' Hedge Hread Hbind Horiginal Htaken Hpoint Hagree).
    intros cs' env' Hread' Hbind'; eapply ABranch; [apply Hterm; exact Hat|
      rewrite <- Hcontrol; exact Hcond|exact Hchoice|exact Hread'|exact Hbind'].
  - assert (Hslot : ssa_term_slot (aenv a) (TSwitch c cases def da) =
        Some (ssa_switch_slot z cases)).
    { cbn [ssa_term_slot]; rewrite Hcond; reflexivity. }
    assert (Hedge : nth_error (term_edges (TSwitch c cases def da))
        (ssa_switch_slot z cases) = Some (dst, args)).
    { rewrite <- Hchoice; exact (ssa_switch_slot_target z cases def da). }
    destruct (ssa_taken_transfer_index ext P f a [] _ e _ _ dst args Hwf Hat
      ltac:(intros y Hfalse; discriminate) Hslot Hedge Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    assert (Hcontrol : aenv a c = aenv t c).
    { apply (ssa_demand_forced_inputs ext P f e _ d a t Hwf Hindex Hagree c).
      cbn [ssa_transfer_payload spp_forced]; rewrite Ht; left; reflexivity. }
    assert (Hslot' : ssa_term_slot (aenv t) (TSwitch c cases def da) =
        Some (ssa_switch_slot z cases)).
    { cbn [ssa_term_slot]; rewrite <- Hcontrol, Hcond; reflexivity. }
    apply (ssa_demand_ordinary_transfer ext P f a t e d _ _ dst args cs env Hwf Hreachable
      Hat I Hslot Hslot' Hedge Hread Hbind Horiginal Htaken Hpoint Hagree).
    intros cs' env' Hread' Hbind'; eapply ASwitch; [apply Hterm; exact Hat|
      rewrite <- Hcontrol; exact Hcond|exact Hchoice|exact Hread'|exact Hbind'].
  - destruct (ssa_taken_transfer_index ext P f a [] _ e (TCall c args dst) 0 dst []
      Hwf Hat ltac:(intros y Hfalse; discriminate) eq_refl eq_refl Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    apply (ssa_demand_all_inputs ext P f a [] _ t e d Hwf Horiginal Htaken Hpoint Hagree).
    cbn [ssa_var_view uses]; rewrite Hindex; intros x Hx.
    apply (ssa_demand_forced_inputs ext P f e _ d a t Hwf Hindex Hagree x).
    cbn [ssa_transfer_payload spp_forced spp_uses] in Hx |- *; rewrite Ht in Hx |- *.
    exact Hx.
  - pose proof (ssa_taken_return_index ext P f a [EvRet v] _ e x Hwf Hat Htaken)
      as Hindex.
    apply (ssa_demand_all_inputs ext P f a _ _ t e d Hwf Horiginal Htaken Hpoint Hagree).
    cbn [ssa_var_view uses]; rewrite Hindex; intros y Hy.
    apply (ssa_demand_forced_inputs ext P f e _ d a t Hwf Hindex Hagree y); exact Hy.
Qed.

(** Every checked raw function satisfies demand laws with all raw exit operands retained. *)
Theorem ssa_demand_view_laws (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  demand_laws (activation ext P f) (activation_endings ext P f)
    (reachable_state (activation ext P f)) var_encoding bool_demand (ssa_demand_view ext P f).
Proof.
  intros Hwf Hfunction; constructor.
  - exact (ssa_point_graph_laws ext P f Hwf Hfunction).
  - intros a tr a' Hfalse; contradiction.
  - intros a tr a' e x Ha Hstep Htaken Houtside.
    exact (ssa_raw_defs_frame ext P f a tr a' e x Hwf Hstep Htaken Houtside).
  - exact (ssa_bool_demand_agreement var_encoding (ssa_demand_view ext P f)).
  - intros u v Hfalse; discriminate Hfalse.
  - intros e x; reflexivity.
  - exact (ssa_demand_vars ext P f Hwf).
  - intros a tr a' t e d Ha Ht Hpoint Hstep Htaken Hagree.
    exact (ssa_demand_steps ext P f a tr a' t e d Hwf Ht Hstep Htaken Hpoint Hagree).
  - intros a t Ha Ht Hpoint Hagree.
    apply (ssa_raw_exits_determine ext P f a t Hwf Ha Ht Hpoint).
    intros x Hx; apply (ssa_bool_exit_agrees var_encoding (ssa_demand_view ext P f)
      (alabel a, apc a) a t x (ssa_demand_vars ext P f Hwf) Hagree).
    rewrite ssa_exit_demands; apply in_map_iff; exists x; split; [reflexivity|exact Hx].
Qed.

(** * Refined row and point invariants *)

Inductive ssa_refined_local (B : Map.t label ssa_block) (l : label) (b : ssa_block)
    : ssa_refined_edge -> ssa_refined_payload -> Prop :=
  | SsaRefinedLocalBind : ssa_refined_local B l b (SsaBindParams l)
      (SsaRefinedPayload (SsaBeforeParams l) (SsaExecPoint l 0) []
        (map SsaSourceValue (map fst (bparams b)))
        (map SsaPendingVar (seq 0 (length (map fst (bparams b)))))
        (map SsaSourceVar (map fst (bparams b))))
  | SsaRefinedLocalInstruction : forall pc i, nth_error (bbody b) pc = Some i ->
      ssa_refined_local B l b (SsaInstruction l pc)
        (snd (ssa_refined_instruction_row l (pc, i)))
  | SsaRefinedLocalMakeCall : forall c args k, bterm b = TCall c args k ->
      ssa_refined_local B l b (SsaMakeCallResult l)
        (SsaRefinedPayload (SsaExecPoint l (length (bbody b))) (SsaCallReady l)
          (map SsaSourceValue (term_uses (TCall c args k))) [SsaCallResult l]
          (map SsaSourceVar (term_uses (TCall c args k))) [SsaCallVar l])
  | SsaRefinedLocalTransfer : forall slot dst args,
      nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
      ssa_refined_local B l b (SsaTransfer l dst slot)
        (snd (ssa_refined_transfer_row B l b (slot, (dst, args))))
  | SsaRefinedLocalReturn : forall x, bterm b = TRet x ->
      ssa_refined_local B l b (SsaReturn l)
        (SsaRefinedPayload (SsaExecPoint l (length (bbody b))) (SsaAfterReturn l)
          [SsaSourceValue x] [] [SsaSourceVar x] []).

Definition ssa_refined_edge_owner (e : ssa_refined_edge) : label :=
  match e with
  | SsaBindParams l | SsaInstruction l _ | SsaMakeCallResult l | SsaTransfer l _ _ |
      SsaReturn l => l
  end.

Local Lemma ssa_refined_transfer_member B l b t e p :
  bterm b = t ->
  In (e, p) (map (ssa_refined_transfer_row B l b) (ssa_enumerate 0 (term_edges t))) ->
  ssa_refined_local B l b e p.
Proof.
  intros Hterm Hrow; apply in_map_iff in Hrow.
  destruct Hrow as [[slot [dst args]] [Heq Henum]].
  change ((SsaTransfer l dst slot,
    snd (ssa_refined_transfer_row B l b (slot, (dst, args)))) = (e, p)) in Heq.
  injection Heq as <- <-; apply SsaRefinedLocalTransfer.
  apply ssa_enumerate_nth in Henum; destruct Henum as [offset [Hslot Hnth]].
  cbn in Hslot; subst slot; rewrite Hterm; exact Hnth.
Qed.

Local Lemma ssa_refined_row_local B l b e p :
  In (e, p) (ssa_refined_rows B (l, b)) -> ssa_refined_local B l b e p.
Proof.
  unfold ssa_refined_rows, ssa_refined_terminal_rows; cbn [fst snd]; intros [Heq|Hrow].
  - injection Heq as <- <-; apply SsaRefinedLocalBind.
  - apply in_app_iff in Hrow; destruct Hrow as [Hinstruction|Hterm].
    + apply in_map_iff in Hinstruction; destruct Hinstruction as [[pc i] [Heq Henum]].
      change ((SsaInstruction l pc, snd (ssa_refined_instruction_row l (pc, i))) =
        (e, p)) in Heq.
      injection Heq as <- <-; apply SsaRefinedLocalInstruction.
      apply ssa_enumerate_nth in Henum; destruct Henum as [offset [Hpc Hnth]].
      cbn in Hpc; subst pc; exact Hnth.
    + destruct (bterm b) as [dst args|c l1 a1 l2 a2|c cases d da|c args k|x] eqn:Ht;
        cbn [app] in Hterm.
      * eapply ssa_refined_transfer_member; eassumption.
      * eapply ssa_refined_transfer_member; eassumption.
      * eapply ssa_refined_transfer_member; eassumption.
      * destruct Hterm as [Heq|Hrow].
        -- injection Heq as <- <-; eapply SsaRefinedLocalMakeCall; exact Ht.
        -- eapply ssa_refined_transfer_member; eassumption.
      * destruct Hterm as [Heq|Hfalse]; [|contradiction].
        injection Heq as <- <-; apply SsaRefinedLocalReturn; exact Ht.
Qed.

Local Lemma ssa_refined_local_owner B l b e p :
  ssa_refined_local B l b e p -> ssa_refined_edge_owner e = l.
Proof.
  intro Hlocal; destruct Hlocal; reflexivity.
Qed.

Local Lemma ssa_refined_local_unique B l b e p q :
  ssa_refined_local B l b e p -> ssa_refined_local B l b e q -> p = q.
Proof.
  intros Hp Hq; destruct Hp; inversion Hq; subst; congruence.
Qed.

Local Lemma ssa_refined_rows_unique B bs :
  NoDup (map fst bs) -> forall e p q,
  In (e, p) (flat_map (ssa_refined_rows B) bs) ->
  In (e, q) (flat_map (ssa_refined_rows B) bs) -> p = q.
Proof.
  intros Hunique e p q Hp Hq; apply in_flat_map in Hp; apply in_flat_map in Hq.
  destruct Hp as [[l b] [Hblock Hp]], Hq as [[l' b'] [Hblock' Hq]].
  apply ssa_refined_row_local in Hp; apply ssa_refined_row_local in Hq.
  pose proof (ssa_refined_local_owner _ _ _ _ _ Hp) as Howner.
  pose proof (ssa_refined_local_owner _ _ _ _ _ Hq) as Howner'; cbn in Howner, Howner'.
  assert (Hlabel : l = l') by congruence; rewrite <- Hlabel in Hblock', Hq.
  assert (Hblockeq : b = b') by
    (exact (ssa_label_unique bs l b b' Hunique Hblock Hblock')).
  subst b'; eapply ssa_refined_local_unique; eassumption.
Qed.

Definition ssa_refined_point_owner (n : ssa_refined_point) : label :=
  match n with
  | SsaBeforeParams l | SsaExecPoint l _ | SsaCallReady l | SsaAfterReturn l |
      SsaDeadPoint l => l
  end.

Local Lemma ssa_refined_block_owner l b n :
  In n (ssa_refined_block_points (l, b)) -> ssa_refined_point_owner n = l.
Proof.
  unfold ssa_refined_block_points; cbn [fst snd]; intros [<-|Hin]; [reflexivity|].
  apply in_app_iff in Hin; destruct Hin as [Hbody|Hend].
  - apply in_map_iff in Hbody; destruct Hbody as [pc [<- Hpc]]; reflexivity.
  - destruct (bterm b); cbn in Hend; try contradiction;
      (destruct Hend as [<-|Hfalse]; [reflexivity|contradiction]).
Qed.

Local Lemma ssa_refined_block_nodup l b : NoDup (ssa_refined_block_points (l, b)).
Proof.
  unfold ssa_refined_block_points; cbn [fst snd]; constructor.
  - intro Hin; apply in_app_iff in Hin; destruct Hin as [Hbody|Hend].
    + apply in_map_iff in Hbody; destruct Hbody as [pc [Hfalse Hpc]]; discriminate.
    + destruct (bterm b); cbn in Hend; intuition discriminate.
  - apply NoDup_app.
    + apply ssa_map_nodup; [intros x y Heq; injection Heq as Heq; exact Heq|apply seq_NoDup].
    + destruct (bterm b); cbn; repeat constructor; tauto.
    + intros n Hbody Hend; apply in_map_iff in Hbody; destruct Hbody as [pc [<- Hpc]].
      destruct (bterm b); cbn in Hend; intuition discriminate.
Qed.

Local Lemma ssa_refined_nodes_nodup bs :
  NoDup (map fst bs) -> NoDup (flat_map ssa_refined_block_points bs).
Proof.
  induction bs as [|[l b] bs IH]; [constructor|].
  intro Hunique; inversion Hunique as [|head labels Hfresh Htail]; subst.
  cbn [flat_map]; apply NoDup_app; [apply ssa_refined_block_nodup|exact (IH Htail)|].
  intros n Hhere Hrest; apply in_flat_map in Hrest.
  destruct Hrest as [[other block] [Hblock Hpoint]].
  pose proof (ssa_refined_block_owner l b n Hhere) as Howner.
  pose proof (ssa_refined_block_owner other block n Hpoint) as Howner'.
  assert (Heq : other = l) by congruence; rewrite Heq in Hblock.
  apply Hfresh, in_map_iff; exists (l, block); split; [reflexivity|exact Hblock].
Qed.

Local Lemma ssa_refined_before_member bs l b :
  In (l, b) bs -> In (SsaBeforeParams l) (flat_map ssa_refined_block_points bs).
Proof.
  intro Hblock; apply in_flat_map; exists (l, b); split; [exact Hblock|left; reflexivity].
Qed.

Local Lemma ssa_refined_exec_member bs l b pc :
  In (l, b) bs -> pc <= length (bbody b) ->
  In (SsaExecPoint l pc) (flat_map ssa_refined_block_points bs).
Proof.
  intros Hblock Hpc; apply in_flat_map; exists (l, b); split; [exact Hblock|].
  right; apply in_or_app; left; apply in_map_iff; exists pc; split; [reflexivity|].
  apply in_seq; cbn [fst snd]; lia.
Qed.

Local Lemma ssa_refined_call_member bs l b c args k :
  In (l, b) bs -> bterm b = TCall c args k ->
  In (SsaCallReady l) (flat_map ssa_refined_block_points bs).
Proof.
  intros Hblock Hterm; apply in_flat_map; exists (l, b); split; [exact Hblock|].
  right; apply in_or_app; right; cbn [fst snd]; rewrite Hterm; left; reflexivity.
Qed.

Local Lemma ssa_refined_return_member bs l b x :
  In (l, b) bs -> bterm b = TRet x ->
  In (SsaAfterReturn l) (flat_map ssa_refined_block_points bs).
Proof.
  intros Hblock Hterm; apply in_flat_map; exists (l, b); split; [exact Hblock|].
  right; apply in_or_app; right; cbn [fst snd]; rewrite Hterm; left; reflexivity.
Qed.

Local Lemma ssa_refined_target_member ext P f fd B l b e p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refined_local B l b e p ->
  In (srp_target p) (flat_map ssa_refined_block_points (blocks fd)).
Proof.
  intros Hwf Hf Hb Hlocal; destruct Hlocal as [|pc i Hi|c args k Hterm|
    slot dst args Hedge|x Hterm].
  - change (In (SsaExecPoint l 0) (flat_map ssa_refined_block_points (blocks fd))).
    apply ssa_refined_exec_member with (b := b); [apply first_index_sound; exact Hb|lia].
  - change (In (SsaExecPoint l (S pc)) (flat_map ssa_refined_block_points (blocks fd))).
    apply ssa_refined_exec_member with (b := b); [apply first_index_sound; exact Hb|].
    assert (Hpc : pc < length (bbody b)).
    { apply nth_error_Some; rewrite Hi; discriminate. }
    lia.
  - eapply ssa_refined_call_member; [apply first_index_sound; exact Hb|exact Hterm].
  - assert (Htarget : srp_target (snd (ssa_refined_transfer_row B l b
        (slot, (dst, args)))) = SsaBeforeParams dst).
    { unfold ssa_refined_transfer_row; cbn [fst snd]; destruct (bterm b); reflexivity. }
    rewrite Htarget.
    destruct (ssa_term_target ext P f fd l b dst args Hwf Hf Hb
      (nth_error_In _ slot Hedge)) as [target Hblock].
    apply ssa_refined_before_member with (b := target); apply first_index_sound; exact Hblock.
  - eapply ssa_refined_return_member; [apply first_index_sound; exact Hb|exact Hterm].
Qed.

Local Lemma ssa_refined_graph_wf ext P f :
  wf_program ext P -> In f (map fst (funcs P)) -> graph_wf (ssa_refined_graph P f).
Proof.
  intros Hwf Hfunction; apply in_map_iff in Hfunction.
  destruct Hfunction as [[key fd] [Heq Hmember]]; cbn in Heq; subst key.
  assert (Hf : find_func P f = Some fd).
  { apply first_index_complete; [exact (proj1 (proj2 Hwf))|exact Hmember]. }
  destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
  unfold ssa_refined_graph; rewrite ssa_refined_all_rows_agrees; apply ssa_graph_of_rows_wf.
  - apply ssa_refined_nodes_nodup; rewrite Hblocks; exact Hunique.
  - intros n Hin; apply in_map_iff in Hin; destruct Hin as [entry [<- Hentry]].
    unfold ssa_entries in Hentry; rewrite Hf in Hentry.
    destruct Hentry as [<-|Hfalse]; [|contradiction].
    destruct (proj1 (wf_function ext P f fd Hwf Hf)) as [b Hb].
    apply ssa_refined_before_member with (b := b); rewrite Hblocks.
    apply first_index_sound; exact Hb.
  - apply ssa_refined_rows_unique; rewrite Hblocks; exact Hunique.
  - intros e p Hrow; apply in_flat_map in Hrow.
    destruct Hrow as [[l b] [Hmember' Hlocal]]; rewrite Hblocks in Hmember'.
    assert (Hb : find_block fd l = Some b) by (apply first_index_complete; assumption).
    rewrite Hblocks; eapply ssa_refined_target_member; try eassumption.
    apply ssa_refined_row_local; exact Hlocal.
Qed.

Local Lemma ssa_block_data_get {A} ext P f fd l b (h : label * ssa_block -> A) :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  Map.get nat_encoding l (Map.of_list nat_encoding
    (map (fun lb => (fst lb, h lb)) (ssa_blocks P f))) = Some (h (l, b)).
Proof.
  intros Hwf Hf Hb; apply ssa_map_get_complete.
  - apply in_map_iff; exists (l, b); split; [reflexivity|].
    unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
  - intros value Hrow; apply in_map_iff in Hrow.
    destruct Hrow as [[key block] [Heq Hmember]]; cbn in Heq.
    injection Heq as Hkey Hvalue; subst key value.
    destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
    rewrite Hblocks in Hmember.
    assert (Hblock : block = b).
    { exact (ssa_label_unique (blocks fd) l block b Hunique Hmember
        (first_index_sound _ _ _ Hb)). }
    subst block; reflexivity.
Qed.

Local Lemma ssa_block_data_lookup {A} ext P f fd l b (h : label * ssa_block -> A) fallback :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_get nat_encoding (Map.of_list nat_encoding
    (map (fun lb => (fst lb, h lb)) (ssa_blocks P f))) fallback l = h (l, b).
Proof.
  intros Hwf Hf Hb; unfold ssa_get; rewrite (ssa_block_data_get ext P f fd l b h Hwf Hf Hb).
  reflexivity.
Qed.

Local Lemma ssa_refined_block_data ext P f fd l b :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  points_in_block (ssa_refined_points P f) l = ssa_refined_block_points (l, b) /\
  instruction_edges (ssa_refined_points P f) l = ssa_refined_internal_edges (l, b) /\
  block_params (ssa_refined_points P f) l = map SsaSourceValue (map fst (bparams b)).
Proof.
  intros Hwf Hf Hb; split; [|split].
  - exact (ssa_block_data_lookup ext P f fd l b ssa_refined_block_points [] Hwf Hf Hb).
  - exact (ssa_block_data_lookup ext P f fd l b ssa_refined_internal_edges [] Hwf Hf Hb).
  - exact (ssa_block_data_lookup ext P f fd l b
      (fun lb => map SsaSourceValue (map fst (bparams (snd lb)))) [] Hwf Hf Hb).
Qed.

Local Lemma ssa_refined_instruction_key l xs e :
  In e (map fst (map (ssa_refined_instruction_row l) xs)) ->
  exists pc, e = SsaInstruction l pc.
Proof.
  rewrite map_map; intro Hin; apply in_map_iff in Hin.
  destruct Hin as [[pc i] [Heq Hmember]]; exists pc; symmetry; exact Heq.
Qed.

Local Lemma ssa_refined_transfer_key B l b xs e :
  In e (map fst (map (ssa_refined_transfer_row B l b) xs)) ->
  exists dst slot, e = SsaTransfer l dst slot.
Proof.
  rewrite map_map; intro Hin; apply in_map_iff in Hin.
  destruct Hin as [[slot [dst args]] [Heq Hmember]].
  exists dst, slot; symmetry; exact Heq.
Qed.

Local Lemma ssa_refined_instruction_keys_nodup l code :
  NoDup (map fst (map (ssa_refined_instruction_row l) (ssa_enumerate 0 code))).
Proof.
  apply (NoDup_map_inv (fun e => match e with SsaInstruction _ pc => pc | _ => 0 end)).
  rewrite !map_map; change (NoDup (map fst (ssa_enumerate 0 code))).
  rewrite ssa_enumerate_fst; apply seq_NoDup.
Qed.

Local Lemma ssa_refined_transfer_keys_nodup B l b edges :
  NoDup (map fst (map (ssa_refined_transfer_row B l b) (ssa_enumerate 0 edges))).
Proof.
  apply (NoDup_map_inv (fun e => match e with SsaTransfer _ _ slot => slot | _ => 0 end)).
  rewrite !map_map; change (NoDup (map fst (ssa_enumerate 0 edges))).
  rewrite ssa_enumerate_fst; apply seq_NoDup.
Qed.

Local Lemma ssa_refined_terminal_key B l b e :
  In e (map fst (ssa_refined_terminal_rows B l b)) ->
  (exists dst slot, e = SsaTransfer l dst slot) \/
    e = SsaMakeCallResult l \/ e = SsaReturn l.
Proof.
  unfold ssa_refined_terminal_rows; destruct (bterm b); intro Hin.
  - left; eapply ssa_refined_transfer_key; exact Hin.
  - left; eapply ssa_refined_transfer_key; exact Hin.
  - left; eapply ssa_refined_transfer_key; exact Hin.
  - change (SsaMakeCallResult l = e \/ In e
      (map fst (map (ssa_refined_transfer_row B l b)
        (ssa_enumerate 0 (term_edges (TCall c args k)))))) in Hin.
    destruct Hin as [<-|Hin]; [right; left; reflexivity|].
    left; eapply ssa_refined_transfer_key; exact Hin.
  - cbn in Hin; destruct Hin as [<-|Hfalse]; [right; right; reflexivity|contradiction].
Qed.

Local Lemma ssa_refined_terminal_keys_nodup B l b :
  NoDup (map fst (ssa_refined_terminal_rows B l b)).
Proof.
  unfold ssa_refined_terminal_rows; destruct (bterm b).
  - apply ssa_refined_transfer_keys_nodup.
  - apply ssa_refined_transfer_keys_nodup.
  - apply ssa_refined_transfer_keys_nodup.
  - change (NoDup (SsaMakeCallResult l :: map fst
      (map (ssa_refined_transfer_row B l b) (ssa_enumerate 0 (term_edges (TCall c args k)))))).
    constructor; [|apply ssa_refined_transfer_keys_nodup].
    intro Hin; apply ssa_refined_transfer_key in Hin; destruct Hin as [dst [slot Hfalse]];
      discriminate.
  - cbn; constructor; [tauto|constructor].
Qed.

Local Lemma ssa_refined_block_keys_nodup B l b :
  NoDup (map fst (ssa_refined_rows B (l, b))).
Proof.
  unfold ssa_refined_rows; cbn [fst snd map]; rewrite map_app; constructor.
  - intro Hin; apply in_app_iff in Hin; destruct Hin as [Hbody|Hend].
    + apply ssa_refined_instruction_key in Hbody; destruct Hbody as [pc Hfalse]; discriminate.
    + apply ssa_refined_terminal_key in Hend; destruct Hend as [[dst [slot Hfalse]]|
        [Hfalse|Hfalse]]; discriminate.
  - apply NoDup_app; [apply ssa_refined_instruction_keys_nodup|
      apply ssa_refined_terminal_keys_nodup|].
    intros e Hbody Hend; apply ssa_refined_instruction_key in Hbody;
      destruct Hbody as [pc ->].
    apply ssa_refined_terminal_key in Hend; destruct Hend as [[dst [slot Hfalse]]|
      [Hfalse|Hfalse]]; discriminate.
Qed.

Local Lemma ssa_refined_all_keys_nodup B bs :
  NoDup (map fst bs) -> NoDup (map fst (flat_map (ssa_refined_rows B) bs)).
Proof.
  induction bs as [|[l b] bs IH]; [constructor|].
  intro Hunique; inversion Hunique as [|head labels Hfresh Htail]; subst.
  cbn [flat_map]; rewrite map_app; apply NoDup_app.
  - apply ssa_refined_block_keys_nodup.
  - exact (IH Htail).
  - intros e Hhere Hrest; apply in_map_iff in Hhere; apply in_map_iff in Hrest.
    destruct Hhere as [[edge p] [Heq Hrow]], Hrest as [[edge' q] [Heq' Hrow']].
    cbn in Heq, Heq'; subst edge edge'; apply ssa_refined_row_local in Hrow.
    apply in_flat_map in Hrow'; destruct Hrow' as [[other block] [Hblock Hlocal]].
    apply ssa_refined_row_local in Hlocal.
    pose proof (ssa_refined_local_owner _ _ _ _ _ Hrow) as Howner.
    pose proof (ssa_refined_local_owner _ _ _ _ _ Hlocal) as Howner'.
    assert (Heq : other = l) by congruence; rewrite Heq in Hblock.
    apply Hfresh, in_map_iff; exists (l, block); split; [reflexivity|exact Hblock].
Qed.

Local Lemma ssa_refined_out_nodup ext P f :
  wf_program ext P -> forall n, NoDup (Graph.out (ssa_refined_graph P f) n).
Proof.
  intros Hwf n; apply ssa_outgoing_nodup; rewrite ssa_refined_all_rows_agrees.
  apply ssa_refined_all_keys_nodup.
  unfold ssa_blocks; destruct (find_func P f) as [fd|] eqn:Hf; [|constructor].
  exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf))).
Qed.

Local Lemma ssa_block_out_nodup P f l : NoDup (Graph.out (ssa_block_graph P f) l).
Proof.
  cbn [ssa_block_graph Graph.out]; unfold ssa_get.
  destruct (Map.get nat_encoding l (Map.of_list nat_encoding
    (map (fun lb => (fst lb, ssa_block_edges (fst lb) (snd lb))) (ssa_blocks P f))))
    as [edges|] eqn:Hget; [|constructor].
  apply (ssa_map_get_sound nat_encoding) in Hget; apply in_map_iff in Hget.
  destruct Hget as [[key b] [Heq Hmember]]; cbn in Heq; injection Heq as <- <-.
  apply (NoDup_map_inv eslot); unfold ssa_block_edges; rewrite map_map.
  change (NoDup (map fst (ssa_enumerate 0 (term_edges (bterm b))))).
  rewrite ssa_enumerate_fst; apply seq_NoDup.
Qed.

Local Lemma ssa_block_data_sound {A} P f l (h : label * ssa_block -> A) value :
  Map.get nat_encoding l (Map.of_list nat_encoding
    (map (fun lb => (fst lb, h lb)) (ssa_blocks P f))) = Some value ->
  exists b, In (l, b) (ssa_blocks P f) /\ value = h (l, b).
Proof.
  intro Hget; apply (ssa_map_get_sound nat_encoding) in Hget; apply in_map_iff in Hget.
  destruct Hget as [[key b] [Heq Hmember]]; cbn in Heq; injection Heq as Hkey Hvalue.
  subst key value; exists b; split; [exact Hmember|reflexivity].
Qed.

Local Lemma ssa_refined_points_unique P f l :
  NoDup (points_in_block (ssa_refined_points P f) l).
Proof.
  cbn [ssa_refined_points points_in_block]; unfold ssa_get.
  destruct (Map.get nat_encoding l (Map.of_list nat_encoding
    (map (fun lb => (fst lb, ssa_refined_block_points lb)) (ssa_blocks P f))))
    as [points|] eqn:Hget; [|constructor].
  destruct (ssa_block_data_sound P f l ssa_refined_block_points points Hget)
    as [b [Hmember ->]]; apply ssa_refined_block_nodup.
Qed.

Local Lemma ssa_refined_transfer_row_in B l b edges slot dst args :
  nth_error edges slot = Some (dst, args) ->
  In (SsaTransfer l dst slot, snd (ssa_refined_transfer_row B l b (slot, (dst, args))))
    (map (ssa_refined_transfer_row B l b) (ssa_enumerate 0 edges)).
Proof.
  intro Hnth; apply in_map_iff; exists (slot, (dst, args)); split; [reflexivity|].
  apply ssa_enumerate_nth; exists slot; split; [lia|exact Hnth].
Qed.

Local Lemma ssa_refined_local_row B l b e p :
  ssa_refined_local B l b e p -> In (e, p) (ssa_refined_rows B (l, b)).
Proof.
  intro Hlocal; destruct Hlocal as [|pc i Hi|c args k Hterm|slot dst args Hedge|x Hterm];
    unfold ssa_refined_rows; cbn [fst snd].
  - left; reflexivity.
  - right; apply in_or_app; left; apply in_map_iff; exists (pc, i); split; [reflexivity|].
    apply ssa_enumerate_nth; exists pc; split; [lia|exact Hi].
  - right; apply in_or_app; right; unfold ssa_refined_terminal_rows; rewrite Hterm.
    left; reflexivity.
  - right; apply in_or_app; right; unfold ssa_refined_terminal_rows.
    destruct (bterm b); try (apply ssa_refined_transfer_row_in; exact Hedge).
    + right; apply ssa_refined_transfer_row_in; exact Hedge.
    + destruct slot; discriminate.
  - right; apply in_or_app; right; unfold ssa_refined_terminal_rows; rewrite Hterm.
    left; reflexivity.
Qed.

Local Lemma ssa_refined_index_complete ext P f fd l b e p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refined_local (first_index (ssa_blocks P f)) l b e p ->
  Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) = Some p.
Proof.
  intros Hwf Hf Hb Hlocal.
  assert (Hin : In (e, p) (ssa_refined_all_rows P f)).
  { rewrite ssa_refined_all_rows_agrees; apply in_flat_map; exists (l, b); split.
    - unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
    - apply ssa_refined_local_row; exact Hlocal. }
  unfold ssa_refined_index; apply ssa_map_get_complete; [exact Hin|].
  rewrite ssa_refined_all_rows_agrees in Hin |- *.
  intros q Hq; eapply ssa_refined_rows_unique with (bs := ssa_blocks P f);
    [|exact Hq|exact Hin].
  unfold ssa_blocks; rewrite Hf; exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf))).
Qed.

Local Lemma ssa_block_node ext P f l :
  wf_program ext P -> In l (Graph.nodes (ssa_block_graph P f)) ->
  exists fd b, find_func P f = Some fd /\ find_block fd l = Some b.
Proof.
  intros Hwf Hnode; apply in_map_iff in Hnode.
  destruct Hnode as [[key b] [Heq Hblock]]; cbn in Heq; subst key.
  unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
    [|contradiction].
  exists fd, b; split; [reflexivity|]; apply first_index_complete;
    [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|exact Hblock].
Qed.

Local Lemma ssa_refined_points_covered ext P f n :
  wf_program ext P ->
  (In n (Graph.nodes (ssa_refined_graph P f)) <->
    exists l, In l (Graph.nodes (ssa_block_graph P f)) /\
      In n (points_in_block (ssa_refined_points P f) l)).
Proof.
  intro Hwf; split.
  - intro Hnode; apply in_flat_map in Hnode; destruct Hnode as [[l b] [Hblock Hpoint]].
    assert (Hnode : In l (Graph.nodes (ssa_block_graph P f))).
    { apply in_map_iff; exists (l, b); split; [reflexivity|exact Hblock]. }
    destruct (ssa_block_node ext P f l Hwf Hnode) as [fd [block [Hf Hb]]].
    assert (Hsame : b = block).
    { destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
      rewrite Hblocks in Hblock.
      exact (ssa_label_unique _ l b block Hunique Hblock (first_index_sound _ _ _ Hb)). }
    subst block; exists l; split; [exact Hnode|].
    rewrite (proj1 (ssa_refined_block_data ext P f fd l b Hwf Hf Hb)); exact Hpoint.
  - intros [l [Hnode Hpoint]].
    destruct (ssa_block_node ext P f l Hwf Hnode) as [fd [b [Hf Hb]]].
    rewrite (proj1 (ssa_refined_block_data ext P f fd l b Hwf Hf Hb)) in Hpoint.
    apply in_flat_map; exists (l, b); split; [|exact Hpoint].
    unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
Qed.

Local Lemma ssa_refined_local_source B l b e p :
  ssa_refined_local B l b e p -> ssa_refined_point_owner (srp_source p) = l.
Proof.
  intro Hlocal; destruct Hlocal; try reflexivity.
  unfold ssa_refined_transfer_row; cbn [fst snd]; destruct (bterm b); reflexivity.
Qed.

Local Lemma ssa_refined_local_edge ext P f fd l b e p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refined_local (first_index (ssa_blocks P f)) l b e p ->
  In e (Graph.out (ssa_refined_graph P f) (srp_source p)) /\
    Graph.target (ssa_refined_graph P f) e = srp_target p.
Proof.
  intros Hwf Hf Hb Hlocal; split.
  - apply ssa_outgoing_member; exists p; split; [|reflexivity].
    rewrite ssa_refined_all_rows_agrees.
    apply in_flat_map; exists (l, b); split.
    + unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
    + apply ssa_refined_local_row; exact Hlocal.
  - change (match Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) with
      | Some p => srp_target p | None => SsaDeadPoint 0 end = srp_target p).
    rewrite (ssa_refined_index_complete ext P f fd l b e p Hwf Hf Hb Hlocal); reflexivity.
Qed.

Local Lemma ssa_refined_local_internal B l b e p :
  ssa_refined_local B l b e p ->
  (match e with SsaTransfer _ _ _ => False | _ => True end) ->
  In e (ssa_refined_internal_edges (l, b)).
Proof.
  intros Hlocal Hinternal; destruct Hlocal as [|pc i Hnth|c args k Hterm|
    slot dst args Hedge|x Hterm]; try contradiction.
  - left; reflexivity.
  - right; apply in_or_app; left; apply in_map_iff; exists pc; split; [reflexivity|].
    apply in_seq; cbn [fst snd]; split; [lia|apply nth_error_Some; rewrite Hnth; discriminate].
  - right; apply in_or_app; right; cbn [fst snd]; rewrite Hterm; left; reflexivity.
  - right; apply in_or_app; right; cbn [fst snd]; rewrite Hterm; left; reflexivity.
Qed.

Local Lemma ssa_refined_index_local ext P f e p :
  wf_program ext P ->
  Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) = Some p ->
  exists fd l b, find_func P f = Some fd /\ find_block fd l = Some b /\
    ssa_refined_local (first_index (ssa_blocks P f)) l b e p.
Proof.
  intros Hwf Hget; apply (ssa_map_get_sound ssa_refined_edge_encoding) in Hget.
  rewrite ssa_refined_all_rows_agrees in Hget.
  apply in_flat_map in Hget; destruct Hget as [[l b] [Hblock Hrow]].
  unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
    [|contradiction].
  exists fd, l, b; split; [reflexivity|]; split.
  - apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
      exact Hblock].
  - apply ssa_refined_row_local; exact Hrow.
Qed.

Local Lemma ssa_refined_taken_local ext P f fd l b r tr r' e p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refined_local (first_index (ssa_blocks P f)) l b e p ->
  srs_point r = srp_source p -> srs_point r' = srp_target p ->
  ssa_refined_selected P f r e -> ssa_refined_taken P f r tr r' e.
Proof.
  intros Hwf Hf Hb Hlocal Hsource Htarget Hselected.
  exists p; split; [eapply ssa_refined_index_complete; eassumption|].
  split; [exact Hsource|]; split; assumption.
Qed.

Local Lemma ssa_refined_steps_covered ext P f r tr r' :
  wf_program ext P -> step (ssa_refined_activation ext P f) r tr r' ->
  exists e, ssa_refined_taken P f r tr r' e.
Proof.
  intros Hwf Hstep; destruct Hstep as
    [r l fd b cs env Hpoint Hf Hb Hread Hbind
    |r l pc i tr env Hpoint Hat Hraw
    |r l pc term dst args slot cs env Hpoint Hat Hordinary Hslot Hedge Hread Hjump
    |r l pc c args k ps result cs v env Hpoint Hat Hsig Hread Htype Hvalid Hjump
    |r l fd b c args k v env Hpoint Hf Hb Hterm Hvalue Hjump
    |r l pc x v Hpoint Hat Hvalue].
  - exists (SsaBindParams l); eapply ssa_refined_taken_local;
      [exact Hwf|exact Hf|exact Hb|apply SsaRefinedLocalBind|exact Hpoint|reflexivity|exact I].
  - destruct Hat as [fd [b [Hf [Hb Hi]]]]; cbn [activation_frame ssa_refined_raw ffunc flabel
      fpc] in Hf, Hb, Hi.
    exists (SsaInstruction l pc); eapply ssa_refined_taken_local;
      [exact Hwf|exact Hf|exact Hb|apply SsaRefinedLocalInstruction; exact Hi|
       exact Hpoint|reflexivity|exact I].
  - destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]];
      cbn [activation_frame ssa_refined_raw ffunc flabel fpc] in Hf, Hb, Hpc.
    exists (SsaTransfer l dst slot); eapply ssa_refined_taken_local with
      (ext := ext) (fd := fd) (l := l) (b := b)
      (p := snd (ssa_refined_transfer_row (first_index (ssa_blocks P f)) l b
        (slot, (dst, args)))); try assumption.
    + apply SsaRefinedLocalTransfer; rewrite Hterm; exact Hedge.
    + unfold ssa_refined_transfer_row; cbn [fst snd]; rewrite Hterm.
      destruct term; try contradiction; cbn [srp_source]; rewrite <- Hpc; exact Hpoint.
    + unfold ssa_refined_transfer_row; cbn [fst snd]; rewrite Hterm.
      destruct term; reflexivity.
    + cbn [ssa_refined_selected]; rewrite Hpoint; exists fd, b; split; [exact Hf|].
      split; [exact Hb|rewrite Hterm; exact Hslot].
  - destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]];
      cbn [activation_frame ssa_refined_raw ffunc flabel fpc] in Hf, Hb, Hpc.
    exists (SsaMakeCallResult l); eapply ssa_refined_taken_local;
      [exact Hwf|exact Hf|exact Hb|eapply SsaRefinedLocalMakeCall; exact Hterm|
       cbn [srp_source]; rewrite <- Hpc; exact Hpoint|reflexivity|exact I].
  - exists (SsaTransfer l k 0); eapply ssa_refined_taken_local with
      (ext := ext) (fd := fd) (l := l) (b := b)
      (p := snd (ssa_refined_transfer_row (first_index (ssa_blocks P f)) l b (0, (k, []))));
      try assumption.
    + apply SsaRefinedLocalTransfer; rewrite Hterm; reflexivity.
    + unfold ssa_refined_transfer_row; cbn [fst snd]; rewrite Hterm; exact Hpoint.
    + unfold ssa_refined_transfer_row; cbn [fst snd]; rewrite Hterm; reflexivity.
    + cbn [ssa_refined_selected]; rewrite Hpoint; reflexivity.
  - destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]];
      cbn [activation_frame ssa_refined_raw ffunc flabel fpc] in Hf, Hb, Hpc.
    exists (SsaReturn l); eapply ssa_refined_taken_local;
      [exact Hwf|exact Hf|exact Hb|apply SsaRefinedLocalReturn; exact Hterm|
       cbn [srp_source]; rewrite <- Hpc; exact Hpoint|reflexivity|exact I].
Qed.

Local Lemma ssa_refined_graph_view_laws ext P f :
  wf_program ext P -> In f (map fst (funcs P)) ->
  graph_view_laws (ssa_refined_activation ext P f)
    (gview (ssa_refined_semantic_var_view ext P f)).
Proof.
  intros Hwf Hfunction; constructor.
  - exact (ssa_refined_graph_wf ext P f Hwf Hfunction).
  - intros r [fd [b [cs [Hf [Hb [Htypes [Hvalid ->]]]]]]].
    change (In (SsaBeforeParams (fentry fd)) (map SsaBeforeParams (ssa_entries P f))).
    apply in_map_iff; exists (fentry fd); split; [reflexivity|].
    unfold ssa_entries; rewrite Hf; left; reflexivity.
  - intros r tr r' Hreachable Hstep; right; exact (ssa_refined_steps_covered ext P f r tr r'
      Hwf Hstep).
  - intros r tr r' e Hreachable Hstep [p [Hindex [Hsource [Htarget Hselected]]]].
    split.
    + apply ssa_outgoing_member; exists p; split;
        [exact (ssa_map_get_sound ssa_refined_edge_encoding _ e p Hindex)|].
      symmetry; exact Hsource.
    + change (match Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) with
        | Some p => srp_target p | None => SsaDeadPoint 0 end = srs_point r').
      rewrite Hindex; symmetry; exact Htarget.
  - intros r tr r' Hreachable Hstep Hfalse; contradiction.
Qed.

Local Lemma ssa_refined_internal_kind l b e :
  In e (ssa_refined_internal_edges (l, b)) ->
  match e with SsaTransfer _ _ _ => False | _ => True end.
Proof.
  unfold ssa_refined_internal_edges; cbn [fst snd]; intros [<-|Hin]; [exact I|].
  apply in_app_iff in Hin; destruct Hin as [Hbody|Hend].
  - apply in_map_iff in Hbody; destruct Hbody as [pc [<- Hpc]]; exact I.
  - destruct (bterm b); cbn in Hend; try contradiction;
      (destruct Hend as [<-|Hfalse]; [exact I|contradiction]).
Qed.

Local Lemma ssa_refined_out_local ext P f n e :
  wf_program ext P -> In e (Graph.out (ssa_refined_graph P f) n) ->
  exists fd l b p, find_func P f = Some fd /\ find_block fd l = Some b /\
    ssa_refined_local (first_index (ssa_blocks P f)) l b e p /\ srp_source p = n.
Proof.
  intros Hwf Hout; apply ssa_outgoing_member in Hout.
  destruct Hout as [p [Hrow Hsource]]; rewrite ssa_refined_all_rows_agrees in Hrow.
  apply in_flat_map in Hrow.
  destruct Hrow as [[l b] [Hblock Hrow]].
  unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
    [|contradiction].
  exists fd, l, b, p; split; [reflexivity|]; split.
  - apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
      exact Hblock].
  - split; [apply ssa_refined_row_local; exact Hrow|exact Hsource].
Qed.

Local Lemma ssa_refined_terminal_chain ext P f fd l b :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  point_chain (ssa_refined_graph P f)
    (SsaExecPoint l (length (bbody b)) ::
      match bterm b with TCall _ _ _ => [SsaCallReady l] | TRet _ => [SsaAfterReturn l] |
        _ => [] end)
    (match bterm b with TCall _ _ _ => [SsaMakeCallResult l] | TRet _ => [SsaReturn l] |
      _ => [] end).
Proof.
  intros Hwf Hf Hb; destruct (bterm b) as [dst args|c l1 a1 l2 a2|c cases d da|c args k|x]
    eqn:Hterm; try apply point_chain_one.
  - pose proof (ssa_refined_local_edge ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalMakeCall _ _ _ c args k Hterm)) as [Hout Htarget].
    eapply point_chain_step; [exact Hout|exact Htarget|apply point_chain_one].
  - pose proof (ssa_refined_local_edge ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalReturn _ _ _ x Hterm)) as [Hout Htarget].
    eapply point_chain_step; [exact Hout|exact Htarget|apply point_chain_one].
Qed.

Local Lemma ssa_refined_block_chain ext P f fd l b :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  point_chain (ssa_refined_graph P f) (ssa_refined_block_points (l, b))
    (ssa_refined_internal_edges (l, b)).
Proof.
  intros Hwf Hf Hb.
  pose proof (ssa_refined_local_edge ext P f fd l b _ _ Hwf Hf Hb
    (SsaRefinedLocalBind _ _ _)) as [Hbind Hbind_target].
  unfold ssa_refined_block_points, ssa_refined_internal_edges; cbn [fst snd seq map app].
  eapply point_chain_step; [exact Hbind|exact Hbind_target|].
  apply ssa_point_chain_prefix with (start := 0) (count := length (bbody b)).
  - intros pc Hpc.
    destruct (nth_error (bbody b) pc) as [i|] eqn:Hnth.
    + exact (ssa_refined_local_edge ext P f fd l b _ _ Hwf Hf Hb
        (SsaRefinedLocalInstruction _ _ _ pc i Hnth)).
    + apply nth_error_None in Hnth; lia.
  - exact (ssa_refined_terminal_chain ext P f fd l b Hwf Hf Hb).
Qed.

Local Lemma ssa_block_row_coordinate l b e p :
  In (e, p) (ssa_block_rows l b) -> esrc e = l /\
    nth_error (term_edges (bterm b)) (eslot e) = Some (edst e, sbp_args p) /\
    p = SsaBlockPayload (sbp_args p) (ssa_guard (bterm b) (eslot e)).
Proof.
  intro Hrow; rewrite ssa_block_rows_agrees in Hrow.
  unfold ssa_block_rows_reference in Hrow; apply in_map_iff in Hrow.
  destruct Hrow as [[slot [dst args]] [Heq Henum]]; cbn in Heq; injection Heq as <- <-.
  cbn; split; [reflexivity|]; split; [|reflexivity].
  apply ssa_enumerate_nth in Henum; destruct Henum as [offset [Hslot Hnth]].
  cbn in Hslot; subst slot; exact Hnth.
Qed.

Local Lemma ssa_block_row_complete l b slot dst args :
  nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
  In (SsaEdge l dst slot, SsaBlockPayload args (ssa_guard (bterm b) slot)) (ssa_block_rows l b).
Proof.
  intro Hnth; rewrite ssa_block_rows_agrees; unfold ssa_block_rows_reference.
  apply in_map_iff; exists (slot, (dst, args));
    split; [reflexivity|].
  apply ssa_enumerate_nth; exists slot; split; [lia|exact Hnth].
Qed.

Local Lemma ssa_refined_edge_arguments ext P f fd l b slot dst args :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
  block_edge_args (ssa_refined_points P f) (SsaEdge l dst slot) =
    match bterm b with TCall _ _ _ => [SsaCallResult l] | _ => map SsaSourceValue args end.
Proof.
  intros Hwf Hf Hb Hedge; cbn [ssa_refined_points block_edge_args]; unfold ssa_get.
  assert (Hget : Map.get ssa_edge_encoding (SsaEdge l dst slot)
    (Map.of_list ssa_edge_encoding (flat_map (fun lb =>
      map (fun ep => (fst ep, match bterm (snd lb) with
        | TCall _ _ _ => [SsaCallResult (fst lb)]
        | _ => map SsaSourceValue (sbp_args (snd ep)) end))
        (ssa_block_rows (fst lb) (snd lb))) (ssa_blocks P f))) =
    Some (match bterm b with TCall _ _ _ => [SsaCallResult l] |
      _ => map SsaSourceValue args end)).
  { apply ssa_map_get_complete.
    - apply in_flat_map; exists (l, b); split.
      + unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
      + apply in_map_iff; exists (SsaEdge l dst slot,
          SsaBlockPayload args (ssa_guard (bterm b) slot)); split; [reflexivity|].
        apply ssa_block_row_complete; exact Hedge.
    - intros value Hrow; apply in_flat_map in Hrow.
      destruct Hrow as [[key block] [Hblock Hrow]]; apply in_map_iff in Hrow.
      destruct Hrow as [[e payload] [Heq Hlocal]]; cbn [fst snd] in Heq.
      injection Heq as Hkey Hvalue; subst e value.
      destruct (ssa_block_row_coordinate key block _ _ Hlocal) as [Hsrc [Hnth Hpayload]].
      cbn [esrc eslot edst] in Hsrc, Hnth; subst key.
      destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
      rewrite Hblocks in Hblock.
      assert (Hsame : block = b).
      { exact (ssa_label_unique _ l block b Hunique Hblock (first_index_sound _ _ _ Hb)). }
      subst block; rewrite Hedge in Hnth; injection Hnth as Hargs.
      cbn [fst snd]; rewrite <- Hargs; reflexivity. }
  rewrite Hget; reflexivity.
Qed.

Local Lemma ssa_block_edge_nth l b e :
  In e (ssa_block_edges l b) -> esrc e = l /\
    exists args, nth_error (term_edges (bterm b)) (eslot e) = Some (edst e, args).
Proof.
  unfold ssa_block_edges; intro Hin; apply in_map_iff in Hin.
  destruct Hin as [[slot [dst args]] [Heq Henum]]; cbn in Heq; subst e.
  split; [reflexivity|exists args].
  apply ssa_enumerate_nth in Henum; destruct Henum as [offset [Hslot Hnth]].
  cbn in Hslot; subst slot; exact Hnth.
Qed.

Local Lemma ssa_block_edge_local ext P f e :
  wf_program ext P -> In e (edges_of (ssa_block_graph P f)) ->
  exists fd b args, find_func P f = Some fd /\ find_block fd (esrc e) = Some b /\
    nth_error (term_edges (bterm b)) (eslot e) = Some (edst e, args).
Proof.
  intros Hwf Hin; apply in_flat_map in Hin; destruct Hin as [l [Hnode Hout]].
  destruct (ssa_block_out_member P f l e Hout) as [b [Hblock Hlocal]].
  destruct (ssa_block_edge_nth l b e Hlocal) as [Hsource [args Hedge]].
  unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
    [|contradiction].
  exists fd, b, args; split; [reflexivity|]; split; [|exact Hedge].
  rewrite Hsource; apply first_index_complete;
    [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|exact Hblock].
Qed.

Local Lemma ssa_refined_argument_arity ext P f fd l b slot dst args target :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
  find_block fd dst = Some target ->
  length (match bterm b with TCall _ _ _ => [SsaCallResult l] |
    _ => map SsaSourceValue args end) = length (map SsaSourceValue (map fst (bparams target))).
Proof.
  intros Hwf Hf Hb Hedge Htarget.
  pose proof (proj1 (proj2 (proj2 (wf_block ext P f fd l b Hwf Hf Hb)))) as Htyped.
  pose proof (nth_error_In _ slot Hedge) as Hmember.
  rewrite !length_map.
  destruct (bterm b) as [dst' actual|c l1 a1 l2 a2|c cases d da|c actual k|x] eqn:Hterm.
  - rewrite length_map; eapply ssa_typed_jump_arity; [|exact Htarget].
    exact (proj1 (Forall_forall _ _) Htyped _ Hmember).
  - rewrite length_map; eapply ssa_typed_jump_arity; [|exact Htarget].
    exact (proj1 (Forall_forall _ _) (proj2 Htyped) _ Hmember).
  - rewrite length_map; eapply ssa_typed_jump_arity; [|exact Htarget].
    exact (proj1 (Forall_forall _ _) (proj2 Htyped) _ Hmember).
  - cbn [term_edges] in Hmember; destruct Hmember as [Heq|Hfalse]; [|contradiction].
    injection Heq as Hdst Hargs; subst dst args.
    cbn [term_typed] in Htyped; rewrite Htarget in Htyped.
    destruct (callee_sig P (static_ty P f) c) as [[ps result]|]; [|contradiction].
    pose proof (f_equal (@length ty) (proj2 Htyped)) as Hlength.
    rewrite length_map in Hlength; cbn in Hlength |- *; lia.
  - destruct slot; discriminate.
Qed.

Local Lemma ssa_refined_last_exec l len default :
  last (SsaBeforeParams l :: map (SsaExecPoint l) (seq 0 (S len))) default = SsaExecPoint l len.
Proof.
  rewrite seq_S, map_app; cbn [map Nat.add].
  change (last ((SsaBeforeParams l :: map (SsaExecPoint l) (seq 0 len)) ++
    [SsaExecPoint l len]) default = SsaExecPoint l len).
  apply last_last.
Qed.

Local Lemma ssa_refined_transfer_last B l b slot dst args :
  nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
  let source := srp_source (snd (ssa_refined_transfer_row B l b (slot, (dst, args)))) in
  last (ssa_refined_block_points (l, b)) source = source.
Proof.
  intro Hedge; unfold ssa_refined_block_points, ssa_refined_transfer_row; cbn [fst snd].
  destruct (bterm b); cbn [srp_source].
  - rewrite app_nil_r; apply ssa_refined_last_exec.
  - rewrite app_nil_r; apply ssa_refined_last_exec.
  - rewrite app_nil_r; apply ssa_refined_last_exec.
  - change (last ((SsaBeforeParams l :: map (SsaExecPoint l)
      (seq 0 (S (length (bbody b))))) ++ [SsaCallReady l]) (SsaCallReady l) = SsaCallReady l).
    apply last_last.
  - destruct slot; discriminate.
Qed.

Local Lemma ssa_refined_edge_projection ext P f n e :
  wf_program ext P -> In e (Graph.out (ssa_refined_graph P f) n) ->
  match e with
  | SsaTransfer src dst slot =>
    In (SsaEdge src dst slot) (Graph.out (ssa_block_graph P f) (ssa_refined_point_owner n)) /\
    dst = ssa_refined_point_owner (Graph.target (ssa_refined_graph P f) e) /\
    last (points_in_block (ssa_refined_points P f) (ssa_refined_point_owner n)) n = n /\
    nth_error (points_in_block (ssa_refined_points P f) dst) 0 =
      Some (Graph.target (ssa_refined_graph P f) e)
  | _ => ssa_refined_point_owner n =
      ssa_refined_point_owner (Graph.target (ssa_refined_graph P f) e)
  end.
Proof.
  intros Hwf Hout; destruct (ssa_refined_out_local ext P f n e Hwf Hout)
    as [fd [l [b [p [Hf [Hb [Hlocal Hsource]]]]]]].
  pose proof (ssa_refined_local_source _ _ _ _ _ Hlocal) as Howner.
  pose proof (proj2 (ssa_refined_local_edge ext P f fd l b e p Hwf Hf Hb Hlocal)) as Htarget.
  rewrite Htarget, <- Hsource.
  destruct Hlocal as [|pc i Hnth|c args k Hterm|slot dst args Hedge|x Hterm];
    try reflexivity.
  assert (Hdst : srp_target (snd (ssa_refined_transfer_row (first_index (ssa_blocks P f))
      l b (slot, (dst, args)))) = SsaBeforeParams dst).
  { unfold ssa_refined_transfer_row; cbn [fst snd]; destruct (bterm b); reflexivity. }
  rewrite Howner, Hdst; cbn [ssa_refined_point_owner]; split.
  - rewrite (ssa_block_out ext P f fd l b Hwf Hf Hb).
    unfold ssa_block_edges; apply in_map_iff; exists (slot, (dst, args));
      split; [reflexivity|].
    apply ssa_enumerate_nth; exists slot; split; [lia|exact Hedge].
  - split; [reflexivity|]; split.
    + rewrite (proj1 (ssa_refined_block_data ext P f fd l b Hwf Hf Hb)).
      apply ssa_refined_transfer_last; exact Hedge.
    + destruct (ssa_term_target ext P f fd l b dst args Hwf Hf Hb
        (nth_error_In _ slot Hedge)) as [target Hblock].
      rewrite (proj1 (ssa_refined_block_data ext P f fd dst target Hwf Hf Hblock)); reflexivity.
Qed.

Local Lemma ssa_refined_phi_arguments_length ext P f be :
  wf_program ext P -> In be (edges_of (ssa_block_graph P f)) ->
  length (block_edge_args (ssa_refined_points P f) be) =
    length (block_params (ssa_refined_points P f) (edst be)).
Proof.
  intros Hwf Hin; destruct be as [src dst slot].
  destruct (ssa_block_edge_local ext P f (SsaEdge src dst slot) Hwf Hin)
    as [fd [b [args [Hf [Hb Hedge]]]]].
  cbn [esrc eslot edst] in Hb, Hedge |- *.
  destruct (ssa_term_target ext P f fd src b dst args Hwf Hf Hb
    (nth_error_In _ slot Hedge)) as [target Htarget].
  rewrite (ssa_refined_edge_arguments ext P f fd src b slot dst args Hwf Hf Hb Hedge),
    (proj2 (proj2 (ssa_refined_block_data ext P f fd dst target Hwf Hf Htarget))).
  exact (ssa_refined_argument_arity ext P f fd src b slot dst args target Hwf Hf Hb Hedge
    Htarget).
Qed.

Local Lemma ssa_refined_phi_edge_use ext P f n e be :
  wf_program ext P -> In e (Graph.out (ssa_refined_graph P f) n) ->
  block_edge_of (ssa_refined_points P f) e = Some be ->
  forall x, In x (block_edge_args (ssa_refined_points P f) be) ->
    In x (edge_use (point_model (ssa_refined_points P f)) e).
Proof.
  intros Hwf Hout Hproject x Hx.
  destruct (ssa_refined_out_local ext P f n e Hwf Hout)
    as [fd [l [b [p [Hf [Hb [Hlocal Hsource]]]]]]].
  pose proof (ssa_refined_index_complete ext P f fd l b e p Hwf Hf Hb Hlocal) as Hindex.
  destruct Hlocal as [|pc i Hnth|c args k Hterm|slot dst args Hedge|y Hterm];
    cbn [ssa_refined_points block_edge_of] in Hproject; try discriminate.
  injection Hproject as <-.
  rewrite (ssa_refined_edge_arguments ext P f fd l b slot dst args Hwf Hf Hb Hedge) in Hx.
  cbn [ssa_refined_points point_model ssa_refined_point_uses edge_use]; rewrite Hindex.
  unfold ssa_refined_transfer_row; cbn [fst snd]; destruct (bterm b);
    cbn [srp_uses ssa_selected_uses] in Hx |- *; try exact Hx.
  - apply in_map_iff in Hx; destruct Hx as [z [<- Hz]]; apply in_map_iff; exists z;
      split; [reflexivity|right; exact Hz].
  - apply in_map_iff in Hx; destruct Hx as [z [<- Hz]]; apply in_map_iff; exists z;
      split; [reflexivity|right; exact Hz].
  - destruct slot; discriminate.
Qed.

Local Lemma ssa_refined_source_member ext P f fd B l b e p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refined_local B l b e p ->
  In (srp_source p) (flat_map ssa_refined_block_points (blocks fd)).
Proof.
  intros Hwf Hf Hb Hlocal; destruct Hlocal as [|pc i Hnth|c args k Hterm|
    slot dst args Hedge|x Hterm].
  - apply ssa_refined_before_member with (b := b); apply first_index_sound; exact Hb.
  - change (In (SsaExecPoint l pc) (flat_map ssa_refined_block_points (blocks fd))).
    apply ssa_refined_exec_member with (b := b); [apply first_index_sound; exact Hb|].
    assert (Hpc : pc < length (bbody b)).
    { apply nth_error_Some; rewrite Hnth; discriminate. }
    lia.
  - apply ssa_refined_exec_member with (b := b); [apply first_index_sound; exact Hb|lia].
  - unfold ssa_refined_transfer_row; cbn [fst snd]; destruct (bterm b) eqn:Hterm;
      cbn [srp_source]; try (apply ssa_refined_exec_member with (b := b);
        [apply first_index_sound; exact Hb|lia]).
    eapply ssa_refined_call_member; [apply first_index_sound; exact Hb|exact Hterm].
  - apply ssa_refined_exec_member with (b := b); [apply first_index_sound; exact Hb|lia].
Qed.

Local Lemma ssa_refined_block_edge_covered ext P f be :
  wf_program ext P -> In be (edges_of (ssa_block_graph P f)) ->
  exists n e, In n (Graph.nodes (ssa_refined_graph P f)) /\
    In e (Graph.out (ssa_refined_graph P f) n) /\
    block_edge_of (ssa_refined_points P f) e = Some be.
Proof.
  intros Hwf Hin; destruct be as [src dst slot].
  destruct (ssa_block_edge_local ext P f (SsaEdge src dst slot) Hwf Hin)
    as [fd [b [args [Hf [Hb Hedge]]]]].
  cbn [esrc eslot edst] in Hb, Hedge.
  pose (p := snd (ssa_refined_transfer_row (first_index (ssa_blocks P f)) src b
    (slot, (dst, args)))).
  assert (Hlocal : ssa_refined_local (first_index (ssa_blocks P f)) src b
      (SsaTransfer src dst slot) p) by (apply SsaRefinedLocalTransfer; exact Hedge).
  exists (srp_source p), (SsaTransfer src dst slot); split.
  - change (In (srp_source p) (flat_map ssa_refined_block_points (ssa_blocks P f))).
    unfold ssa_blocks; rewrite Hf; eapply ssa_refined_source_member; eassumption.
  - split; [exact (proj1 (ssa_refined_local_edge ext P f fd src b _ p Hwf Hf Hb Hlocal))|
      reflexivity].
Qed.

(** The refined syntactic model preserves every original block and ordered edge occurrence. *)
Theorem ssa_refined_point_laws (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  ssa_point_laws (ssa_refined_points P f).
Proof.
  intros Hwf Hfunction; constructor.
  - exact (ssa_refined_graph_wf ext P f Hwf Hfunction).
  - exact (ssa_refined_out_nodup ext P f Hwf).
  - exact (ssa_block_graph_wf ext P f Hwf Hfunction).
  - exact (ssa_block_out_nodup P f).
  - intro n; exact (ssa_refined_points_covered ext P f n Hwf).
  - intro l; exact (ssa_refined_points_unique P f l).
  - intros l n Hnode Hin; destruct (ssa_block_node ext P f l Hwf Hnode)
      as [fd [b [Hf Hb]]].
    rewrite (proj1 (ssa_refined_block_data ext P f fd l b Hwf Hf Hb)) in Hin.
    exact (ssa_refined_block_owner l b n Hin).
  - intros l Hnode; destruct (ssa_block_node ext P f l Hwf Hnode) as [fd [b [Hf Hb]]].
    rewrite (proj1 (ssa_refined_block_data ext P f fd l b Hwf Hf Hb)); discriminate.
  - intros l Hnode; destruct (ssa_block_node ext P f l Hwf Hnode) as [fd [b [Hf Hb]]].
    destruct (ssa_refined_block_data ext P f fd l b Hwf Hf Hb) as [Hpoints [Hedges Hparams]].
    rewrite Hpoints, Hedges; exact (ssa_refined_block_chain ext P f fd l b Hwf Hf Hb).
  - intros l e Hnode Hin; destruct (ssa_block_node ext P f l Hwf Hnode)
      as [fd [b [Hf Hb]]].
    rewrite (proj1 (proj2 (ssa_refined_block_data ext P f fd l b Hwf Hf Hb))) in Hin.
    pose proof (ssa_refined_internal_kind l b e Hin) as Hkind; destruct e;
      try reflexivity; contradiction.
  - intros n e Hnode Hout Hnone.
    destruct (ssa_refined_out_local ext P f n e Hwf Hout)
      as [fd [l [b [p [Hf [Hb [Hlocal Hsource]]]]]]].
    assert (Howner : ssa_refined_point_owner n = l).
    { rewrite <- Hsource; exact (ssa_refined_local_source _ _ _ _ _ Hlocal). }
    change (In e (instruction_edges (ssa_refined_points P f) (ssa_refined_point_owner n))).
    rewrite Howner, (proj1 (proj2 (ssa_refined_block_data ext P f fd l b Hwf Hf Hb))).
    apply (ssa_refined_local_internal _ _ _ _ _ Hlocal).
    destruct e; cbn [ssa_refined_points block_edge_of] in Hnone; try discriminate; exact I.
  - intros l Hnode; destruct (ssa_block_node ext P f l Hwf Hnode) as [fd [b [Hf Hb]]].
    rewrite (proj1 (proj2 (ssa_refined_block_data ext P f fd l b Hwf Hf Hb))); reflexivity.
  - intros l x Hnode; destruct (ssa_block_node ext P f l Hwf Hnode) as [fd [b [Hf Hb]]].
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalBind _ _ _)) as Hget.
    rewrite (proj2 (proj2 (ssa_refined_block_data ext P f fd l b Hwf Hf Hb))).
    cbn [ssa_refined_points point_model ssa_refined_point_uses edge_def parameter_edge].
    rewrite Hget; reflexivity.
  - intros n e Hnode Hout.
    pose proof (ssa_refined_edge_projection ext P f n e Hwf Hout) as Hproject.
    destruct e; exact Hproject.
  - intros be Hin; exact (ssa_refined_phi_arguments_length ext P f be Hwf Hin).
  - intros n e be Hnode Hout Hproject x Hx.
    exact (ssa_refined_phi_edge_use ext P f n e be Hwf Hout Hproject x Hx).
  - intros be Hin; exact (ssa_refined_block_edge_covered ext P f be Hwf Hin).
  - intros e1 e2 be Hmember Hmember' Hproject Hproject'.
    destruct e1, e2; cbn [ssa_refined_points block_edge_of] in Hproject, Hproject';
      try discriminate; congruence.
Qed.

(** Stable refined operation operands inherit the source typing and word-validity invariant. *)
Local Lemma ssa_refined_typed_operands ext P f r l pc x o args :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_state (ssa_refined_activation ext P f) r -> srs_point r = SsaExecPoint l pc ->
  at_instr P (activation_frame f (ssa_refined_raw r l pc)) (IOp x o args) ->
  exists cs ps result, read_args (srs_env r) args = Some cs /\
    op_sig P o = Some (ps, result) /\ map ty_of cs = ps /\ Forall valid_cval cs.
Proof.
  intros Hwf Hfunction Hreachable Hpoint Hat.
  assert (Hstable : ssa_refined_stable r) by
    (unfold ssa_refined_stable; rewrite Hpoint; exact I).
  destruct (ssa_refined_reachable_relation ext P f r Hwf Hfunction Hreachable Hstable)
    as [a [Ha [[fd [b [Hf [Hb Hposition]]]] Henv]]].
  destruct Hposition as [[Hpc Hexec]|[y [Hterm [Hpc Hafter]]]];
    [|rewrite Hpoint in Hafter; discriminate].
  rewrite Hpoint in Hexec; injection Hexec as Hlabel Hpc'.
  assert (Hat' : at_instr P (activation_frame f a) (IOp x o args)).
  { apply (proj1 (ssa_at_instr_coordinates P (activation_frame f (ssa_refined_raw r l pc))
      (activation_frame f a) _ eq_refl Hlabel Hpc')); exact Hat. }
  destruct (activation_typed_operands ext P f a x o args Hwf Ha Hat')
    as [cs [ps [result [Hread [Hsig [Htypes Hvalid]]]]]].
  exists cs, ps, result; split.
  - rewrite <- (ssa_read_agrees (aenv a) (srs_env r) args Henv); exact Hread.
  - repeat split; assumption.
Qed.

(** Refined trap exits inject exactly the raw operand list, preserving order and duplicates. *)
Lemma ssa_refined_exit_agrees ext P f l pc :
  exit_use (point_model (ssa_refined_points P f)) (SsaExecPoint l pc) =
    map SsaSourceValue (exit_uses (ssa_var_view ext P f) (l, pc)) /\
  exit_uses (ssa_refined_semantic_var_view ext P f) (SsaExecPoint l pc) =
    map SsaSourceVar (exit_uses (ssa_var_view ext P f) (l, pc)).
Proof.
  split; cbn [ssa_refined_points point_model ssa_refined_point_uses exit_use
    ssa_refined_exit_uses ssa_refined_semantic_var_view exit_uses ssa_var_view];
    unfold ssa_get; rewrite Map.get_map;
    destruct (Map.get (pair_encoding nat_encoding nat_encoding) (l, pc) (ssa_exit_index P f));
    reflexivity.
Qed.

Local Lemma ssa_refined_trap_operands ext P f r l pc x o args cs :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_state (ssa_refined_activation ext P f) r -> srs_point r = SsaExecPoint l pc ->
  at_instr P (activation_frame f (ssa_refined_raw r l pc)) (IOp x o args) ->
  read_args (srs_env r) args = Some cs -> op_eval ext o cs = None ->
  exit_uses (ssa_var_view ext P f) (l, pc) = args.
Proof.
  intros Hwf Hfunction Hreachable Hpoint Hat Hread Hfail.
  destruct (ssa_refined_typed_operands ext P f r l pc x o args Hwf Hfunction Hreachable Hpoint Hat)
    as [actual [ps [result [Hactual [Hsig [Htypes Hvalid]]]]]].
  rewrite Hread in Hactual; injection Hactual as <-.
  destruct (proj2 (op_eval_typed ext P o cs ps result
    (proj2 (proj2 (proj2 (proj2 Hwf)))) Hsig Htypes Hvalid) Hfail)
    as [[w ->]|[tag ->]].
  all: pose proof (ssa_exit_instruction ext P f (ssa_refined_raw r l pc) _ Hwf Hat) as Hindex;
    cbn [ssa_refined_raw alabel apc] in Hindex;
    cbn [ssa_var_view exit_uses]; unfold ssa_get; rewrite Hindex; reflexivity.
Qed.

Local Lemma ssa_refined_trap_agrees ext P f r t :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_state (ssa_refined_activation ext P f) r -> srs_point t = srs_point r ->
  (forall x, In x (exit_uses (ssa_refined_semantic_var_view ext P f) (srs_point r)) ->
    ssa_refined_lookup r x = ssa_refined_lookup t x) ->
  ssa_refined_trapped ext P f r -> ssa_refined_trapped ext P f t.
Proof.
  intros Hwf Hfunction Hreachable Hsame Hagree [l [pc [Hpoint [x [o [args [cs
    [Hat [Hread Hfail]]]]]]]]].
  exists l, pc; split; [rewrite Hsame; exact Hpoint|]; exists x, o, args, cs; split.
  - apply (proj1 (ssa_at_instr_coordinates P (activation_frame f (ssa_refined_raw r l pc))
      (activation_frame f (ssa_refined_raw t l pc)) _ eq_refl eq_refl eq_refl)); exact Hat.
  - split; [|exact Hfail]; cbn [activation_frame ssa_refined_raw aenv fenv] in Hread |- *.
    rewrite <- (ssa_read_equal_on (srs_env r) (srs_env t) args); [exact Hread|].
    intros y Hy; apply (Hagree (SsaSourceVar y)).
    rewrite Hpoint, (proj2 (ssa_refined_exit_agrees ext P f l pc)),
      (ssa_refined_trap_operands ext P f r l pc x o args cs Hwf Hfunction Hreachable Hpoint Hat
        Hread Hfail).
    apply in_map_iff; exists y; split; [reflexivity|exact Hy].
Qed.

Local Lemma ssa_refined_exits_determine ext P f r t :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_state (ssa_refined_activation ext P f) r ->
  reachable_state (ssa_refined_activation ext P f) t -> srs_point t = srs_point r ->
  (forall x, In x (exit_uses (ssa_refined_semantic_var_view ext P f) (srs_point r)) ->
    ssa_refined_lookup r x = ssa_refined_lookup t x) ->
  (ssa_refined_final r <-> ssa_refined_final t) /\
  (ssa_refined_trapped ext P f r <-> ssa_refined_trapped ext P f t) /\ (False <-> False).
Proof.
  intros Hwf Hfunction Hr Ht Hpoint Hagree; split.
  - unfold ssa_refined_final; rewrite Hpoint; reflexivity.
  - split; [|reflexivity]; split.
    + eapply ssa_refined_trap_agrees; eassumption.
    + eapply ssa_refined_trap_agrees; [exact Hwf|exact Hfunction|exact Ht|
        symmetry; exact Hpoint|].
      intros x Hx; symmetry; apply Hagree; rewrite <- Hpoint; exact Hx.
Qed.

Definition ssa_refined_edge_target (e : ssa_refined_edge) : ssa_refined_point :=
  match e with
  | SsaBindParams l => SsaExecPoint l 0
  | SsaInstruction l pc => SsaExecPoint l (S pc)
  | SsaMakeCallResult l => SsaCallReady l
  | SsaTransfer _ dst _ => SsaBeforeParams dst
  | SsaReturn l => SsaAfterReturn l
  end.

Local Lemma ssa_refined_local_target B l b e p :
  ssa_refined_local B l b e p -> srp_target p = ssa_refined_edge_target e.
Proof.
  intro Hlocal; destruct Hlocal; try reflexivity.
  unfold ssa_refined_transfer_row; cbn [fst snd]; destruct (bterm b); reflexivity.
Qed.

Local Lemma ssa_refined_taken_shape ext P f r tr r' e :
  wf_program ext P -> ssa_refined_taken P f r tr r' e ->
  ssa_refined_edge_target e = srs_point r' /\
  ssa_refined_edge_owner e = ssa_refined_point_owner (srs_point r) /\
  ssa_refined_selected P f r e.
Proof.
  intros Hwf [p [Hget [Hsource [Htarget Hselected]]]].
  destruct (ssa_refined_index_local ext P f e p Hwf Hget)
    as [fd [l [b [Hf [Hb Hlocal]]]]].
  split; [rewrite <- (ssa_refined_local_target _ _ _ _ _ Hlocal); symmetry; exact Htarget|].
  split; [|exact Hselected].
  rewrite Hsource, (ssa_refined_local_source _ _ _ _ _ Hlocal).
  exact (ssa_refined_local_owner _ _ _ _ _ Hlocal).
Qed.

Local Lemma ssa_refined_taken_bind ext P f r tr r' e l :
  wf_program ext P -> ssa_refined_taken P f r tr r' e ->
  srs_point r' = SsaExecPoint l 0 -> e = SsaBindParams l.
Proof.
  intros Hwf Htaken Hpoint.
  pose proof (proj1 (ssa_refined_taken_shape ext P f r tr r' e Hwf Htaken)) as Htarget.
  rewrite Hpoint in Htarget; destruct e; cbn [ssa_refined_edge_target] in Htarget; congruence.
Qed.

Local Lemma ssa_refined_taken_instruction ext P f r tr r' e l pc :
  wf_program ext P -> ssa_refined_taken P f r tr r' e ->
  srs_point r' = SsaExecPoint l (S pc) -> e = SsaInstruction l pc.
Proof.
  intros Hwf Htaken Hpoint.
  pose proof (proj1 (ssa_refined_taken_shape ext P f r tr r' e Hwf Htaken)) as Htarget.
  rewrite Hpoint in Htarget; destruct e; cbn [ssa_refined_edge_target] in Htarget; congruence.
Qed.

Local Lemma ssa_refined_taken_make_call ext P f r tr r' e l :
  wf_program ext P -> ssa_refined_taken P f r tr r' e ->
  srs_point r' = SsaCallReady l -> e = SsaMakeCallResult l.
Proof.
  intros Hwf Htaken Hpoint.
  pose proof (proj1 (ssa_refined_taken_shape ext P f r tr r' e Hwf Htaken)) as Htarget.
  rewrite Hpoint in Htarget; destruct e; cbn [ssa_refined_edge_target] in Htarget; congruence.
Qed.

Local Lemma ssa_refined_taken_return ext P f r tr r' e l :
  wf_program ext P -> ssa_refined_taken P f r tr r' e ->
  srs_point r' = SsaAfterReturn l -> e = SsaReturn l.
Proof.
  intros Hwf Htaken Hpoint.
  pose proof (proj1 (ssa_refined_taken_shape ext P f r tr r' e Hwf Htaken)) as Htarget.
  rewrite Hpoint in Htarget; destruct e; cbn [ssa_refined_edge_target] in Htarget; congruence.
Qed.

Local Lemma ssa_refined_taken_transfer ext P f r tr r' e l pc fd b term dst slot :
  wf_program ext P -> ssa_refined_taken P f r tr r' e ->
  srs_point r = SsaExecPoint l pc -> srs_point r' = SsaBeforeParams dst ->
  find_func P f = Some fd -> find_block fd l = Some b -> bterm b = term ->
  ssa_term_slot (srs_env r) term = Some slot -> e = SsaTransfer l dst slot.
Proof.
  intros Hwf Htaken Hpoint Hpoint' Hf Hb Hterm Hslot.
  destruct (ssa_refined_taken_shape ext P f r tr r' e Hwf Htaken)
    as [Htarget [Howner Hselected]].
  rewrite Hpoint' in Htarget; rewrite Hpoint in Howner.
  destruct e; cbn [ssa_refined_edge_target ssa_refined_edge_owner ssa_refined_point_owner]
    in Htarget, Howner; try discriminate.
  injection Htarget as Hdst; subst dst0; rewrite Howner in Hselected.
  cbn [ssa_refined_selected] in Hselected; rewrite Hpoint in Hselected.
  destruct Hselected as [fd' [b' [Hf' [Hb' Hchosen]]]].
  rewrite Hf in Hf'; injection Hf' as <-; rewrite Hb in Hb'; injection Hb' as <-.
  rewrite Hterm, Hslot in Hchosen; injection Hchosen as Hslot'; subst slot0; congruence.
Qed.

Local Lemma ssa_refined_taken_call_transfer ext P f r tr r' e l dst :
  wf_program ext P -> ssa_refined_taken P f r tr r' e ->
  srs_point r = SsaCallReady l -> srs_point r' = SsaBeforeParams dst ->
  e = SsaTransfer l dst 0.
Proof.
  intros Hwf Htaken Hpoint Hpoint'.
  destruct (ssa_refined_taken_shape ext P f r tr r' e Hwf Htaken)
    as [Htarget [Howner Hselected]].
  rewrite Hpoint' in Htarget; rewrite Hpoint in Howner.
  destruct e; cbn [ssa_refined_edge_target ssa_refined_edge_owner ssa_refined_point_owner]
    in Htarget, Howner; try discriminate.
  cbn [ssa_refined_selected] in Hselected; rewrite Hpoint in Hselected; congruence.
Qed.

Local Lemma ssa_refined_taken_copy P f r tr r' t t' e :
  ssa_refined_taken P f r tr r' e -> srs_point t = srs_point r ->
  srs_point t' = srs_point r' -> ssa_refined_selected P f t e ->
  ssa_refined_taken P f t tr t' e.
Proof.
  intros [p [Hindex [Hsource [Htarget Hselected]]]] Hpoint Hpoint' Hselected'.
  exists p; split; [exact Hindex|]; split; [rewrite Hpoint; exact Hsource|].
  split; [rewrite Hpoint'; exact Htarget|exact Hselected'].
Qed.

Local Lemma ssa_jump_arity P f a dst cs env :
  jump_env P (activation_frame f a) dst cs = Some env ->
  length cs = length (bparams (ssa_get nat_encoding (first_index (ssa_blocks P f))
    (SBlock [] [] (TRet 0)) dst)).
Proof.
  unfold jump_env; cbn [activation_frame ffunc fenv].
  destruct (find_func P f) as [fd|] eqn:Hf; [|discriminate].
  destruct (find_block fd dst) as [b|] eqn:Hb; [|discriminate].
  intro Hbind; change (Map.get nat_encoding dst (first_index (blocks fd)) = Some b) in Hb.
  unfold ssa_blocks, ssa_get; rewrite Hf, Hb; symmetry; exact (ssa_bind_length _ _ _ _ Hbind).
Qed.

Local Lemma ssa_instruction_frame ext P f a tr a' i x :
  wf_program ext P -> at_instr P (activation_frame f a) i ->
  step (activation ext P f) a tr a' -> ~ In x (instr_def i) -> aenv a' x = aenv a x.
Proof.
  intros Hwf Hat Hstep Houtside.
  destruct (ssa_point_steps_covered ext P f a tr a' Hwf Hstep) as [e Htaken].
  apply (ssa_raw_defs_frame ext P f a tr a' e x Hwf Hstep Htaken).
  cbn [ssa_var_view defs]; rewrite (ssa_taken_instruction_index ext P f a tr a' e i Hwf
    Hat Htaken); exact Houtside.
Qed.

Local Lemma ssa_ordinary_selected_agrees env env' term args :
  (match term with TCall _ _ _ | TRet _ => False | _ => True end) ->
  (forall x, In x (ssa_selected_uses term args) -> env x = env' x) ->
  ssa_term_slot env term = ssa_term_slot env' term /\ read_args env args = read_args env' args.
Proof.
  intros Hordinary Hagree; destruct term; try contradiction; split.
  - reflexivity.
  - apply ssa_read_equal_on; exact Hagree.
  - cbn [ssa_term_slot]; rewrite (Hagree c (or_introl eq_refl)); reflexivity.
  - apply ssa_read_equal_on; intros x Hx; apply Hagree; right; exact Hx.
  - cbn [ssa_term_slot]; rewrite (Hagree c (or_introl eq_refl)); reflexivity.
  - apply ssa_read_equal_on; intros x Hx; apply Hagree; right; exact Hx.
Qed.

Local Lemma ssa_refined_defs_frame ext P f r tr r' e v :
  wf_program ext P -> step (ssa_refined_activation ext P f) r tr r' ->
  ssa_refined_taken P f r tr r' e ->
  ~ In v (defs (ssa_refined_semantic_var_view ext P f) e) ->
  ssa_refined_lookup r' v = ssa_refined_lookup r v.
Proof.
  intros Hwf Hstep Htaken Houtside; destruct Hstep as
    [r l fd b cs env Hpoint Hf Hb Hread Hbind
    |r l pc i tr env Hpoint Hat Hraw
    |r l pc term dst args slot cs env Hpoint Hat Hordinary Hslot Hedge Hread Hjump
    |r l pc c args k ps result cs value env Hpoint Hat Hsig Hread Htype Hvalid Hjump
    |r l fd b c args k value env Hpoint Hf Hb Hterm Hvalue Hjump
    |r l pc x value Hpoint Hat Hvalue].
  - pose proof (ssa_refined_taken_bind ext P f r [] _ e l Hwf Htaken eq_refl) as ->.
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalBind _ _ _)) as Hindex.
    destruct v as [x|site|slot]; try reflexivity.
    apply (ssa_bind_frame _ _ _ _ x Hbind); intro Hin; apply Houtside.
    cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex.
    apply in_map_iff; exists x; split; [reflexivity|exact Hin].
  - pose proof (ssa_refined_taken_instruction ext P f r tr _ e l pc Hwf Htaken eq_refl) as ->.
    destruct Hat as [fd [b [Hf [Hb Hnth]]]].
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalInstruction _ _ _ pc i Hnth)) as Hindex.
    destruct v as [x|site|slot]; try reflexivity.
    apply (ssa_instruction_frame ext P f (ssa_refined_raw r l pc) tr (AState l (S pc) env) i x
      Hwf ltac:(exists fd, b; repeat split; assumption) Hraw).
    intro Hin; apply Houtside; cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex.
    apply in_map_iff; exists x; split; [reflexivity|exact Hin].
  - destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]].
    pose proof (ssa_refined_taken_transfer ext P f r [] _ e l pc fd b term dst slot Hwf Htaken
      Hpoint eq_refl Hf Hb Hterm Hslot) as ->.
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalTransfer _ _ _ slot dst args ltac:(rewrite Hterm; exact Hedge))) as Hindex.
    destruct v as [x|site|index]; try reflexivity; apply ssa_pending_write_frame.
    pose proof (ssa_jump_arity P f (ssa_refined_raw r l pc) dst cs env Hjump) as Hlength.
    destruct (lt_dec index (length cs)) as [Hin|Hout]; [|lia].
    exfalso; apply Houtside; cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex.
    unfold ssa_refined_transfer_row; cbn [fst snd]; rewrite Hterm.
    destruct term; cbn [srp_semantic_defs];
      (apply in_map_iff; exists index; split; [reflexivity|apply in_seq; cbn; lia]).
  - pose proof (ssa_refined_taken_make_call ext P f r [] _ e l Hwf Htaken eq_refl) as ->.
    destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]].
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalMakeCall _ _ _ c args k Hterm)) as Hindex.
    destruct v as [x|site|slot]; try reflexivity.
    cbn [ssa_refined_lookup srs_call_results]; unfold env_set.
    destruct (Nat.eq_dec site l) as [->|Hdifferent]; [|reflexivity].
    exfalso; apply Houtside; cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex;
      left; reflexivity.
  - pose proof (ssa_refined_taken_call_transfer ext P f r [] _ e l k Hwf Htaken Hpoint eq_refl)
      as ->.
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalTransfer _ _ _ 0 k [] ltac:(rewrite Hterm; reflexivity))) as Hindex.
    destruct v as [x|site|index]; try reflexivity; apply ssa_pending_write_frame.
    pose proof (ssa_jump_arity P f (ssa_refined_raw r l (length (bbody b))) k [value] env Hjump)
      as Hlength.
    destruct index; [|cbn; lia]; exfalso; apply Houtside.
    cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex.
    unfold ssa_refined_transfer_row; cbn [fst snd]; rewrite Hterm.
    apply in_map_iff; exists 0; split; [reflexivity|apply in_seq; cbn in Hlength |- *; lia].
  - destruct v; reflexivity.
Qed.

Local Lemma ssa_refined_source_inputs r t xs :
  (forall v, In v (map SsaSourceVar xs) -> ssa_refined_lookup r v = ssa_refined_lookup t v) ->
  forall x, In x xs -> srs_env r x = srs_env t x.
Proof.
  intros Hagree x Hx; apply (Hagree (SsaSourceVar x)); apply in_map_iff;
    exists x; split; [reflexivity|exact Hx].
Qed.

Local Lemma ssa_refined_transfer_defs B l b slot dst args :
  srp_semantic_defs (snd (ssa_refined_transfer_row B l b (slot, (dst, args)))) =
    map SsaPendingVar (seq 0 (length (bparams (ssa_get nat_encoding B
      (SBlock [] [] (TRet 0)) dst)))).
Proof.
  unfold ssa_refined_transfer_row; cbn [fst snd]; destruct (bterm b); reflexivity.
Qed.

Local Lemma ssa_refined_pending_outputs old old' cs arity :
  length cs = arity -> forall v, In v (map SsaPendingVar (seq 0 arity)) ->
  match v with SsaPendingVar i => ssa_pending_write old cs i = ssa_pending_write old' cs i |
    _ => False end.
Proof.
  intros Hlength v Hin; apply in_map_iff in Hin; destruct Hin as [i [<- Hi]].
  apply in_seq in Hi; rewrite !ssa_pending_write_lookup by lia; reflexivity.
Qed.

Local Lemma ssa_refined_uses_determine ext P f r tr r' t e :
  wf_program ext P -> step (ssa_refined_activation ext P f) r tr r' ->
  ssa_refined_taken P f r tr r' e -> srs_point t = srs_point r ->
  (forall v, In v (uses (ssa_refined_semantic_var_view ext P f) e) ->
    ssa_refined_lookup r v = ssa_refined_lookup t v) ->
  exists t', step (ssa_refined_activation ext P f) t tr t' /\
    ssa_refined_taken P f t tr t' e /\
    forall v, In v (defs (ssa_refined_semantic_var_view ext P f) e) ->
      ssa_refined_lookup r' v = ssa_refined_lookup t' v.
Proof.
  intros Hwf Hstep Htaken Hsame Hagree; destruct Hstep as
    [r l fd b cs env Hpoint Hf Hb Hread Hbind
    |r l pc i tr env Hpoint Hat Hraw
    |r l pc term dst args slot cs env Hpoint Hat Hordinary Hslot Hedge Hread Hjump
    |r l pc c args k ps result cs value env Hpoint Hat Hsig Hread Htype Hvalid Hjump
    |r l fd b c args k value env Hpoint Hf Hb Hterm Hvalue Hjump
    |r l pc x value Hpoint Hat Hvalue].
  - pose proof (ssa_refined_taken_bind ext P f r [] _ e l Hwf Htaken eq_refl) as ->.
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalBind _ _ _)) as Hindex.
    cbn [ssa_refined_semantic_var_view uses] in Hagree; rewrite Hindex in Hagree.
    cbn [srp_semantic_uses] in Hagree; rewrite length_map in Hagree.
    assert (Hread' : read_args (srs_pending t) (seq 0 (length (bparams b))) = Some cs).
    { rewrite <- (ssa_read_equal_on (srs_pending r) (srs_pending t) _); [exact Hread|].
      intros i Hi; apply (Hagree (SsaPendingVar i)); apply in_map_iff;
        exists i; split; [reflexivity|exact Hi]. }
    destruct (ssa_bind_exists (srs_env t) (bparams b) cs (ssa_bind_length _ _ _ _ Hbind))
      as [env' Hbind'].
    exists (SsaRefinedState (SsaExecPoint l 0) env' (srs_call_results t) (srs_pending t)); split.
    + eapply SsaStepBind; [rewrite Hsame; exact Hpoint|exact Hf|exact Hb|exact Hread'|
        exact Hbind'].
    + split; [eapply ssa_refined_taken_copy; [exact Htaken|exact Hsame|reflexivity|exact I]|].
      cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex; intros v Hv.
      apply in_map_iff in Hv; destruct Hv as [x [<- Hx]].
      exact (ssa_bind_written _ _ _ _ _ _ Hbind Hbind' x Hx).
  - pose proof (ssa_refined_taken_instruction ext P f r tr _ e l pc Hwf Htaken eq_refl) as ->.
    pose proof Hat as Hat'; destruct Hat as [fd [b [Hf [Hb Hnth]]]].
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalInstruction _ _ _ pc i Hnth)) as Hindex.
    cbn [ssa_refined_semantic_var_view uses] in Hagree; rewrite Hindex in Hagree.
    pose proof (ssa_refined_source_inputs r t (instr_uses i) Hagree) as Hinputs.
    destruct (ssa_instruction_matches ext P f (ssa_refined_raw r l pc) tr
      (AState l (S pc) env) (ssa_refined_raw t l pc) i Hat' Hraw eq_refl Hinputs)
      as [[label' pc' env'] [Hraw' [Hposition Hwritten]]].
    cbn [alabel apc ssa_refined_raw] in Hposition; injection Hposition as Hlabel Hpc;
      subst label' pc'.
    exists (SsaRefinedState (SsaExecPoint l (S pc)) env' (srs_call_results t) (srs_pending t));
      split.
    + eapply SsaStepInstruction with (i := i); [rewrite Hsame; exact Hpoint| |exact Hraw'].
      apply (proj1 (ssa_at_instr_coordinates P (activation_frame f (ssa_refined_raw r l pc))
        (activation_frame f (ssa_refined_raw t l pc)) i eq_refl eq_refl eq_refl)); exact Hat'.
    + split; [eapply ssa_refined_taken_copy; [exact Htaken|exact Hsame|reflexivity|exact I]|].
      cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex; intros v Hv.
      apply in_map_iff in Hv; destruct Hv as [x [<- Hx]]; exact (Hwritten x Hx).
  - pose proof Hat as Hat'; destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]].
    pose proof (ssa_refined_taken_transfer ext P f r [] _ e l pc fd b term dst slot Hwf Htaken
      Hpoint eq_refl Hf Hb Hterm Hslot) as ->.
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalTransfer _ _ _ slot dst args ltac:(rewrite Hterm; exact Hedge))) as Hindex.
    cbn [ssa_refined_semantic_var_view uses] in Hagree; rewrite Hindex in Hagree.
    assert (Hinputs : forall x, In x (ssa_selected_uses term args) ->
        srs_env r x = srs_env t x).
    { unfold ssa_refined_transfer_row in Hagree; cbn [fst snd] in Hagree;
        rewrite Hterm in Hagree.
      destruct term; try contradiction; apply ssa_refined_source_inputs; exact Hagree. }
    destruct (ssa_ordinary_selected_agrees _ _ term args Hordinary Hinputs)
      as [Hslot_eq Hread_eq].
    assert (Hread' : read_args (srs_env t) args = Some cs) by (rewrite <- Hread_eq; exact Hread).
    destruct (ssa_jump_matches P f (ssa_refined_raw r l pc) (ssa_refined_raw t l pc) dst cs env
      Hjump) as [env' [Hjump' Hwritten]].
    exists (SsaRefinedState (SsaBeforeParams dst) (srs_env t) (srs_call_results t)
      (ssa_pending_write (srs_pending t) cs)); split.
    + eapply SsaStepTransfer with (t := term) (env := env');
        [rewrite Hsame; exact Hpoint| |exact Hordinary|rewrite <- Hslot_eq; exact Hslot|
         exact Hedge|exact Hread'|exact Hjump'].
      apply (proj1 (ssa_at_term_coordinates P (activation_frame f (ssa_refined_raw r l pc))
        (activation_frame f (ssa_refined_raw t l pc)) term eq_refl eq_refl eq_refl)); exact Hat'.
    + split.
      * eapply ssa_refined_taken_copy; [exact Htaken|exact Hsame|reflexivity|].
        cbn [ssa_refined_selected]; rewrite Hsame, Hpoint; exists fd, b.
        split; [exact Hf|]; split; [exact Hb|rewrite Hterm, <- Hslot_eq; exact Hslot].
      * cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex, ssa_refined_transfer_defs.
        intros v Hv; pose proof (ssa_refined_pending_outputs (srs_pending r) (srs_pending t) cs _
          (ssa_jump_arity P f (ssa_refined_raw r l pc) dst cs env Hjump) v Hv) as Hslots.
        destruct v; try contradiction; exact Hslots.
  - pose proof (ssa_refined_taken_make_call ext P f r [] _ e l Hwf Htaken eq_refl) as ->.
    pose proof Hat as Hat'; destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]].
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalMakeCall _ _ _ c args k Hterm)) as Hindex.
    cbn [ssa_refined_semantic_var_view uses] in Hagree; rewrite Hindex in Hagree.
    pose proof (ssa_refined_source_inputs r t _ Hagree) as Hinputs.
    assert (Hread' : read_args (srs_env t) (term_uses (TCall c args k)) = Some cs).
    { rewrite <- (ssa_read_equal_on (srs_env r) (srs_env t) _ Hinputs); exact Hread. }
    destruct (ssa_jump_matches P f (ssa_refined_raw r l pc) (ssa_refined_raw t l pc) k [value]
      env Hjump) as [env' [Hjump' Hwritten]].
    exists (SsaRefinedState (SsaCallReady l) (srs_env t)
      (env_set (srs_call_results t) l value) (srs_pending t)); split.
    + eapply SsaStepMakeCall with (env := env');
        [rewrite Hsame; exact Hpoint| |exact Hsig|exact Hread'|exact Htype|exact Hvalid|
         exact Hjump'].
      apply (proj1 (ssa_at_term_coordinates P (activation_frame f (ssa_refined_raw r l pc))
        (activation_frame f (ssa_refined_raw t l pc)) _ eq_refl eq_refl eq_refl)); exact Hat'.
    + split; [eapply ssa_refined_taken_copy; [exact Htaken|exact Hsame|reflexivity|exact I]|].
      cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex; intros v [<-|Hfalse];
        [|contradiction].
      cbn [ssa_refined_lookup srs_call_results]; unfold env_set;
        destruct (Nat.eq_dec l l); [reflexivity|contradiction].
  - pose proof (ssa_refined_taken_call_transfer ext P f r [] _ e l k Hwf Htaken Hpoint eq_refl)
      as ->.
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalTransfer _ _ _ 0 k [] ltac:(rewrite Hterm; reflexivity))) as Hindex.
    cbn [ssa_refined_semantic_var_view uses] in Hagree; rewrite Hindex in Hagree.
    unfold ssa_refined_transfer_row in Hagree; cbn [fst snd] in Hagree;
      rewrite Hterm in Hagree.
    assert (Hvalue' : srs_call_results t l = Some value).
    { pose proof (Hagree (SsaCallVar l) (or_introl eq_refl)) as Hcall.
      change (srs_call_results r l = srs_call_results t l) in Hcall.
      rewrite <- Hcall; exact Hvalue. }
    destruct (ssa_jump_matches P f (ssa_refined_raw r l (length (bbody b)))
      (ssa_refined_raw t l (length (bbody b))) k [value] env Hjump)
      as [env' [Hjump' Hwritten]].
    exists (SsaRefinedState (SsaBeforeParams k) (srs_env t) (srs_call_results t)
      (ssa_pending_write (srs_pending t) [value])); split.
    + eapply SsaStepCallTransfer with (env := env');
        [rewrite Hsame; exact Hpoint|exact Hf|exact Hb|exact Hterm|exact Hvalue'|exact Hjump'].
    + split.
      * eapply ssa_refined_taken_copy; [exact Htaken|exact Hsame|reflexivity|].
        cbn [ssa_refined_selected]; rewrite Hsame, Hpoint; reflexivity.
      * cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex, ssa_refined_transfer_defs.
        intros v Hv; pose proof (ssa_refined_pending_outputs
          (srs_pending r) (srs_pending t) [value] _
          (ssa_jump_arity P f (ssa_refined_raw r l (length (bbody b))) k [value] env Hjump) v Hv)
          as Hslots.
        destruct v; try contradiction; exact Hslots.
  - pose proof (ssa_refined_taken_return ext P f r _ _ e l Hwf Htaken eq_refl) as ->.
    pose proof Hat as Hat'; destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]].
    pose proof (ssa_refined_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (SsaRefinedLocalReturn _ _ _ x Hterm)) as Hindex.
    cbn [ssa_refined_semantic_var_view uses] in Hagree; rewrite Hindex in Hagree.
    exists (SsaRefinedState (SsaAfterReturn l) (srs_env t) (srs_call_results t) (srs_pending t));
      split.
    + eapply SsaStepReturn; [rewrite Hsame; exact Hpoint| |].
      * apply (proj1 (ssa_at_term_coordinates P (activation_frame f (ssa_refined_raw r l pc))
          (activation_frame f (ssa_refined_raw t l pc)) _ eq_refl eq_refl eq_refl)); exact Hat'.
      * change (ssa_refined_lookup t (SsaSourceVar x) = Some value).
        rewrite <- (Hagree (SsaSourceVar x) (or_introl eq_refl)); exact Hvalue.
    + split; [eapply ssa_refined_taken_copy; [exact Htaken|exact Hsame|reflexivity|exact I]|].
      cbn [ssa_refined_semantic_var_view defs]; rewrite Hindex; intros v Hfalse; contradiction.
Qed.

(** Source, call and pending variables describe actual refined steps and all declared endings. *)
Theorem ssa_refined_semantic_var_laws (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  var_view_laws (ssa_refined_activation ext P f) (ssa_refined_endings ext P f)
    (ssa_refined_semantic_var_view ext P f).
Proof.
  intros Hwf Hfunction; constructor.
  - exact (ssa_refined_graph_view_laws ext P f Hwf Hfunction).
  - intros r tr r' Hfalse; contradiction.
  - intros r tr r' e v Hreachable Hstep Htaken Houtside.
    exact (ssa_refined_defs_frame ext P f r tr r' e v Hwf Hstep Htaken Houtside).
  - intros r tr r' t e Hr Ht Hpoint Hstep Htaken Hagree.
    exact (ssa_refined_uses_determine ext P f r tr r' t e Hwf Hstep Htaken Hpoint Hagree).
  - intros r t Hr Ht Hpoint Hagree.
    exact (ssa_refined_exits_determine ext P f r t Hwf Hfunction Hr Ht Hpoint Hagree).
Qed.

Local Lemma ssa_refine_point_at ext P f fd l b pc :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refine_point P f (l, pc) =
    if Nat.leb pc (length (bbody b)) then SsaExecPoint l pc else
      match bterm b with TRet _ => SsaAfterReturn l | _ => SsaDeadPoint l end.
Proof.
  intros Hwf Hf Hb; unfold ssa_refine_point; cbn [fst snd].
  rewrite (ssa_block_data_get ext P f fd l b (fun lb =>
    (length (bbody (snd lb)), match bterm (snd lb) with TRet _ => true | _ => false end))
    Hwf Hf Hb).
  cbn; destruct (Nat.leb pc (length (bbody b))); [reflexivity|destruct (bterm b); reflexivity].
Qed.

Local Lemma ssa_refine_point_exec ext P f fd l b pc :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  pc <= length (bbody b) -> ssa_refine_point P f (l, pc) = SsaExecPoint l pc.
Proof.
  intros Hwf Hf Hb Hpc; rewrite (ssa_refine_point_at ext P f fd l b pc Hwf Hf Hb).
  assert (Htest : Nat.leb pc (length (bbody b)) = true) by (apply Nat.leb_le; exact Hpc).
  rewrite Htest; reflexivity.
Qed.

Local Lemma ssa_refine_point_endpoint ext P f fd l b :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refine_point P f (l, S (length (bbody b))) =
    match bterm b with TRet _ => SsaAfterReturn l | _ => SsaDeadPoint l end.
Proof.
  intros Hwf Hf Hb; rewrite (ssa_refine_point_at ext P f fd l b _ Hwf Hf Hb).
  assert (Htest : Nat.leb (S (length (bbody b))) (length (bbody b)) = false) by
    (apply Nat.leb_gt; lia).
  rewrite Htest; reflexivity.
Qed.

Definition ssa_refined_inactive (n : ssa_refined_point) : Prop :=
  match n with SsaAfterReturn _ | SsaDeadPoint _ => True | _ => False end.

Local Lemma ssa_refined_inactive_out P f n :
  ssa_refined_inactive n -> Graph.out (ssa_refined_graph P f) n = [].
Proof.
  intro Hinactive; destruct (Graph.out (ssa_refined_graph P f) n) as [|e rest] eqn:Hout;
    [reflexivity|].
  assert (Hmember : In e (Graph.out (ssa_refined_graph P f) n)) by
    (rewrite Hout; left; reflexivity).
  apply ssa_outgoing_member in Hmember; destruct Hmember as [p [Hrow Hsource]].
  rewrite ssa_refined_all_rows_agrees in Hrow.
  apply in_flat_map in Hrow; destruct Hrow as [[l b] [Hblock Hrow]].
  apply ssa_refined_row_local in Hrow; rewrite <- Hsource in Hinactive.
  destruct Hrow; cbn [ssa_refined_inactive srp_source ssa_refined_instruction_row fst snd]
    in Hinactive; try contradiction.
  unfold ssa_refined_transfer_row in Hinactive; cbn [fst snd] in Hinactive;
    destruct (bterm b); contradiction.
Qed.

Local Lemma ssa_refined_inactive_dead P f n x :
  ssa_refined_inactive n ->
  ~ syntactic_live (point_model (ssa_refined_points P f)) x n.
Proof.
  intro Hinactive; apply ssa_no_syntactic_live.
  - exact (ssa_refined_inactive_out P f n Hinactive).
  - destruct n; try contradiction; reflexivity.
Qed.

Local Lemma ssa_raw_out_local ext P f n e :
  wf_program ext P -> In e (Graph.out (ssa_point_graph P f) n) ->
  exists fd l b p, find_func P f = Some fd /\ find_block fd l = Some b /\
    ssa_point_local (first_index (ssa_blocks P f)) l b e p /\ spp_source p = n.
Proof.
  intros Hwf Hout; apply ssa_outgoing_member in Hout.
  destruct Hout as [p [Hrow Hsource]]; rewrite ssa_point_all_rows_agrees in Hrow.
  apply in_flat_map in Hrow.
  destruct Hrow as [[l b] [Hblock Hrow]].
  unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
    [|contradiction].
  exists fd, l, b, p; split; [reflexivity|]; split.
  - apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
      exact Hblock].
  - split; [apply ssa_point_row_local; exact Hrow|exact Hsource].
Qed.

Local Lemma ssa_raw_out_after ext P f fd l b pc :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  length (bbody b) < pc -> Graph.out (ssa_point_graph P f) (l, pc) = [].
Proof.
  intros Hwf Hf Hb Hpast.
  destruct (Graph.out (ssa_point_graph P f) (l, pc)) as [|e rest] eqn:Hout; [reflexivity|].
  assert (Hin : In e (Graph.out (ssa_point_graph P f) (l, pc))) by
    (rewrite Hout; left; reflexivity).
  destruct (ssa_raw_out_local ext P f (l, pc) e Hwf Hin)
    as [fd' [label' [block [p [Hf' [Hb' [Hlocal Hsource]]]]]]].
  assert (Hlabel : label' = l).
  { assert (Howner : fst (spp_source p) = label') by (destruct Hlocal; reflexivity).
    rewrite Hsource in Howner; cbn in Howner; symmetry; exact Howner. }
  rewrite Hlabel in Hb', Hlocal.
  rewrite Hf in Hf'; injection Hf' as Hfd; subst fd'.
  rewrite Hb in Hb'; injection Hb' as Hblock; rewrite <- Hblock in Hlocal.
  exfalso; destruct Hlocal as [position i Hnth|slot dst args Hnot Hedge|x Hterm];
    apply (f_equal snd) in Hsource;
    cbn [spp_source ssa_instruction_payload ssa_transfer_payload snd] in Hsource; try lia.
  assert (Hbefore : position < length (bbody b)).
  { apply nth_error_Some; rewrite Hnth; discriminate. }
  lia.
Qed.

Local Lemma ssa_raw_exit_after ext P f fd l b pc :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  length (bbody b) < pc -> exit_uses (ssa_var_view ext P f) (l, pc) = [].
Proof.
  intros Hwf Hf Hb Hpast; cbn [ssa_var_view exit_uses]; unfold ssa_get.
  destruct (Map.get (pair_encoding nat_encoding nat_encoding) (l, pc) (ssa_exit_index P f))
    as [xs|] eqn:Hget; [|reflexivity].
  apply (ssa_map_get_sound (pair_encoding nat_encoding nat_encoding)) in Hget.
  apply in_flat_map in Hget; destruct Hget as [[label' block] [Hblock Hrow]].
  apply in_map_iff in Hrow; destruct Hrow as [[position i] [Heq Henum]].
  apply (f_equal fst) in Heq; cbn [fst snd] in Heq; injection Heq as Hlabel Hposition;
    subst label' position.
  destruct (ssa_function_blocks ext P f fd Hwf Hf) as [Hblocks Hunique].
  rewrite Hblocks in Hblock.
  assert (Hsame : block = b) by
    (exact (ssa_label_unique _ l block b Hunique Hblock (first_index_sound _ _ _ Hb))).
  subst block; cbn [fst snd] in Henum.
  apply ssa_enumerate_nth in Henum; destruct Henum as [offset [Hpc Hnth]].
  cbn in Hpc; subst offset.
  assert (Hbefore : pc < length (bbody b)).
  { apply nth_error_Some; rewrite Hnth; discriminate. }
  lia.
Qed.

(** One-past-terminator nodes are dead in both liveness descriptions, even in unreachable blocks. *)
Local Lemma ssa_refined_endpoint_liveness ext P f fd l b x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  (syntactic_live (var_point_uses (ssa_var_view ext P f)) x (l, S (length (bbody b))) <->
    syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
      (ssa_refine_point P f (l, S (length (bbody b))))).
Proof.
  intros Hwf Hf Hb.
  assert (Hraw : ~ syntactic_live (var_point_uses (ssa_var_view ext P f)) x
    (l, S (length (bbody b)))).
  { apply ssa_no_syntactic_live.
    - exact (ssa_raw_out_after ext P f fd l b (S (length (bbody b))) Hwf Hf Hb ltac:(lia)).
    - exact (ssa_raw_exit_after ext P f fd l b (S (length (bbody b))) Hwf Hf Hb ltac:(lia)). }
  assert (Hrefined : ~ syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
    (ssa_refine_point P f (l, S (length (bbody b))))).
  { apply ssa_refined_inactive_dead.
    rewrite (ssa_refine_point_endpoint ext P f fd l b Hwf Hf Hb); destruct (bterm b); exact I. }
  tauto.
Qed.

Local Lemma ssa_instruction_no_parameter l instr x home b i :
  ~ In (x, (home, Param b i)) (ssa_instruction_rows l instr).
Proof.
  intro Hin; destruct instr; cbn [ssa_instruction_rows] in Hin; try contradiction;
    (destruct Hin as [Heq|Hfalse]; [discriminate|contradiction]).
Qed.

Local Lemma ssa_parameter_definition ext P f x b i :
  wf_program ext P -> def (ssa_block_view ext P f) x = Param b i ->
  nth_error (params (ssa_block_view ext P f) b) i = Some x.
Proof.
  intros Hwf Hdef; cbn [ssa_block_view def] in Hdef; unfold ssa_get in Hdef.
  destruct (Map.get nat_encoding x (ssa_definitions P f)) as [[home definition]|] eqn:Hget;
    [|discriminate].
  cbn [snd] in Hdef; subst definition.
  apply (ssa_map_get_sound nat_encoding) in Hget; apply in_flat_map in Hget.
  destruct Hget as [[l block] [Hblock Hrow]]; apply in_app_iff in Hrow.
  destruct Hrow as [Hparameter|Hinstruction].
  - unfold ssa_parameter_rows in Hparameter; apply in_map_iff in Hparameter.
    destruct Hparameter as [[slot [key ty]] [Heq Henum]]; cbn [fst snd] in Heq.
    match type of Heq with context [if ?test then _ else _] => destruct test eqn:Hcall end;
      [discriminate|].
    injection Heq as Hkey Hhome Hlabel Hindex; subst key home l slot.
    cbn [fst snd] in Henum; apply ssa_enumerate_nth in Henum.
    destruct Henum as [offset [Hslot Hnth]]; cbn in Hslot; subst offset.
    unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
      [|contradiction].
    assert (Hb : find_block fd b = Some block).
    { apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
        exact Hblock]. }
    change (nth_error (ssa_get nat_encoding (Map.of_list nat_encoding
      (map (fun lb => (fst lb, map fst (bparams (snd lb)))) (ssa_blocks P f))) [] b) i = Some x).
    rewrite (ssa_block_data_lookup ext P f fd b block (fun lb => map fst (bparams (snd lb))) []
      Hwf Hf Hb).
    cbn [fst snd]; rewrite nth_error_map, Hnth; reflexivity.
  - apply in_flat_map in Hinstruction; destruct Hinstruction as [instr [Hin Hrow]].
    exfalso; exact (ssa_instruction_no_parameter l instr x home b i Hrow).
Qed.

(** * Source liveness across administrative edges *)

Local Lemma ssa_raw_local_index ext P f fd l b e p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_point_local (first_index (ssa_blocks P f)) l b e p ->
  Map.get ssa_edge_encoding e (ssa_point_index P f) = Some p.
Proof.
  intros Hwf Hf Hb Hlocal.
  destruct Hlocal as [pc i Hnth|slot dst args Hnot Hedge|x Hterm].
  - exact (ssa_point_index_complete ext P f fd l b pc _ Hwf Hf Hb
      (ssa_point_instruction_lookup _ l b pc i Hnth)).
  - exact (ssa_point_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (ssa_point_term_lookup _ l b slot dst args Hnot Hedge)).
  - exact (ssa_point_index_complete ext P f fd l b _ _ Hwf Hf Hb
      (ssa_point_return_lookup _ l b x Hterm)).
Qed.

Local Lemma ssa_raw_local_edge ext P f fd l b e p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_point_local (first_index (ssa_blocks P f)) l b e p ->
  In e (Graph.out (ssa_point_graph P f) (spp_source p)) /\
    Graph.target (ssa_point_graph P f) e = spp_target p.
Proof.
  intros Hwf Hf Hb Hlocal.
  pose proof (ssa_raw_local_index ext P f fd l b e p Hwf Hf Hb Hlocal) as Hindex.
  split.
  - apply ssa_outgoing_member; exists p; split; [|reflexivity].
    apply (ssa_map_get_sound ssa_edge_encoding); exact Hindex.
  - change (match Map.get ssa_edge_encoding e (ssa_point_index P f) with
      | Some q => spp_target q | None => (0, 0) end = spp_target p).
    rewrite Hindex; reflexivity.
Qed.

Local Lemma ssa_raw_live_use ext P f fd l b e p x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_point_local (first_index (ssa_blocks P f)) l b e p -> In x (spp_uses p) ->
  syntactic_live (var_point_uses (ssa_var_view ext P f)) x (spp_source p).
Proof.
  intros Hwf Hf Hb Hlocal Huse; eapply live_edge_use.
  - exact (proj1 (ssa_raw_local_edge ext P f fd l b e p Hwf Hf Hb Hlocal)).
  - change (In x (match Map.get ssa_edge_encoding e (ssa_point_index P f) with
      | Some q => spp_uses q | None => [] end)).
    rewrite (ssa_raw_local_index ext P f fd l b e p Hwf Hf Hb Hlocal); exact Huse.
Qed.

Local Lemma ssa_raw_live_next ext P f fd l b e p x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_point_local (first_index (ssa_blocks P f)) l b e p -> ~ In x (spp_defs p) ->
  syntactic_live (var_point_uses (ssa_var_view ext P f)) x (spp_target p) ->
  syntactic_live (var_point_uses (ssa_var_view ext P f)) x (spp_source p).
Proof.
  intros Hwf Hf Hb Hlocal Hkill Hlive.
  destruct (ssa_raw_local_edge ext P f fd l b e p Hwf Hf Hb Hlocal) as [Hout Htarget].
  eapply live_edge_next; [exact Hout| |].
  2: change (syntactic_live (var_point_uses (ssa_var_view ext P f)) x
    (Graph.target (ssa_point_graph P f) e)); rewrite Htarget; exact Hlive.
  change (~ In x (match Map.get ssa_edge_encoding e (ssa_point_index P f) with
    | Some q => spp_defs q | None => [] end)).
  rewrite (ssa_raw_local_index ext P f fd l b e p Hwf Hf Hb Hlocal); exact Hkill.
Qed.

Local Lemma ssa_refined_live_use ext P f fd l b e p x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refined_local (first_index (ssa_blocks P f)) l b e p -> In x (srp_uses p) ->
  syntactic_live (point_model (ssa_refined_points P f)) x (srp_source p).
Proof.
  intros Hwf Hf Hb Hlocal Huse; eapply live_edge_use.
  - exact (proj1 (ssa_refined_local_edge ext P f fd l b e p Hwf Hf Hb Hlocal)).
  - change (In x (match Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) with
      | Some q => srp_uses q | None => [] end)).
    rewrite (ssa_refined_index_complete ext P f fd l b e p Hwf Hf Hb Hlocal); exact Huse.
Qed.

Local Lemma ssa_refined_live_next ext P f fd l b e p x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refined_local (first_index (ssa_blocks P f)) l b e p -> ~ In x (srp_defs p) ->
  syntactic_live (point_model (ssa_refined_points P f)) x (srp_target p) ->
  syntactic_live (point_model (ssa_refined_points P f)) x (srp_source p).
Proof.
  intros Hwf Hf Hb Hlocal Hkill Hlive.
  destruct (ssa_refined_local_edge ext P f fd l b e p Hwf Hf Hb Hlocal)
    as [Hout Htarget].
  eapply live_edge_next; [exact Hout| |].
  2: change (syntactic_live (point_model (ssa_refined_points P f)) x
    (Graph.target (ssa_refined_graph P f) e)); rewrite Htarget; exact Hlive.
  change (~ In x (match Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) with
    | Some q => srp_defs q | None => [] end)).
  rewrite (ssa_refined_index_complete ext P f fd l b e p Hwf Hf Hb Hlocal); exact Hkill.
Qed.

Local Lemma ssa_block_index_at P f fd l b :
  find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_get nat_encoding (first_index (ssa_blocks P f)) (SBlock [] [] (TRet 0)) l = b.
Proof.
  intros Hf Hb; unfold ssa_blocks, ssa_get; rewrite Hf.
  change (Map.get nat_encoding l (first_index (blocks fd)) = Some b) in Hb.
  rewrite Hb; reflexivity.
Qed.

Local Lemma ssa_refined_bind_live ext P f fd dst target x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd dst = Some target ->
  ~ In x (map fst (bparams target)) ->
  syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
    (SsaExecPoint dst 0) ->
  syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
    (SsaBeforeParams dst).
Proof.
  intros Hwf Hf Htarget Hkill Hlive.
  eapply (ssa_refined_live_next ext P f fd dst target _ _ _ Hwf Hf Htarget
    (SsaRefinedLocalBind _ _ _)); [|exact Hlive].
  cbn [srp_defs]; intro Hin; apply in_map_iff in Hin.
  destruct Hin as [y [Heq Hy]]; injection Heq as <-; exact (Hkill Hy).
Qed.

Local Lemma ssa_transfer_live_forward ext P f fd l b slot dst args x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
  (In x (spp_uses (ssa_transfer_payload (first_index (ssa_blocks P f)) l b (dst, args))) \/
    (~ In x (spp_defs (ssa_transfer_payload (first_index (ssa_blocks P f)) l b (dst, args))) /\
      syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
        (ssa_refine_point P f (dst, 0)))) ->
  syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
    (SsaExecPoint l (length (bbody b))).
Proof.
  intros Hwf Hf Hb Hedge Hlive.
  destruct (ssa_term_target ext P f fd l b dst args Hwf Hf Hb
    (nth_error_In _ slot Hedge)) as [target Htarget].
  assert (Hbind : ~ In x (spp_defs (ssa_transfer_payload
    (first_index (ssa_blocks P f)) l b (dst, args))) ->
    syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
      (ssa_refine_point P f (dst, 0)) ->
    syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
      (SsaBeforeParams dst)).
  { intros Hkill Hnext; apply (ssa_refined_bind_live ext P f fd dst target x Hwf Hf Htarget).
    - change (~ In x (map fst (bparams (ssa_get nat_encoding
        (first_index (ssa_blocks P f)) (SBlock [] [] (TRet 0)) dst)))) in Hkill.
      rewrite (ssa_block_index_at P f fd dst target Hf Htarget) in Hkill; exact Hkill.
    - rewrite (ssa_refine_point_exec ext P f fd dst target 0 Hwf Hf Htarget ltac:(lia))
        in Hnext; exact Hnext. }
  pose proof (ssa_refined_live_use ext P f fd l b _ _ (SsaSourceValue x) Hwf Hf Hb
    (SsaRefinedLocalTransfer _ _ _ slot dst args Hedge)) as HtransferUse.
  pose proof (ssa_refined_live_next ext P f fd l b _ _ (SsaSourceValue x) Hwf Hf Hb
    (SsaRefinedLocalTransfer _ _ _ slot dst args Hedge)) as HtransferNext.
  cbn [ssa_refined_transfer_row snd srp_source srp_target srp_uses srp_defs]
    in HtransferUse, HtransferNext.
  cbn [ssa_transfer_payload spp_uses spp_defs spp_target] in Hlive.
  destruct (bterm b) as [to actual|c l1 a1 l2 a2|c cases d da|c actual k|ret] eqn:Hterm.
  all: try solve [destruct Hlive as [Huse|[Hkill Hnext]];
    [apply HtransferUse; apply in_map; exact Huse|
     apply HtransferNext; [intro Hin; exact Hin|exact (Hbind Hkill Hnext)]]].
  - destruct Hlive as [Huse|[Hkill Hnext]].
    + eapply (ssa_refined_live_use ext P f fd l b _ _ _ Hwf Hf Hb
        (SsaRefinedLocalMakeCall _ _ _ c actual k Hterm)).
      apply in_map; exact Huse.
    + eapply (ssa_refined_live_next ext P f fd l b _ _ _ Hwf Hf Hb
        (SsaRefinedLocalMakeCall _ _ _ c actual k Hterm)).
      * cbn; intros [Hfalse|Hfalse]; [discriminate|contradiction].
      * apply HtransferNext; [intro Hin; exact Hin|exact (Hbind Hkill Hnext)].
Qed.

Local Lemma ssa_raw_local_live_forward ext P f fd l b e p x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_point_local (first_index (ssa_blocks P f)) l b e p ->
  (In x (spp_uses p) \/ (~ In x (spp_defs p) /\
    syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
      (ssa_refine_point P f (spp_target p)))) ->
  syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
    (ssa_refine_point P f (spp_source p)).
Proof.
  intros Hwf Hf Hb Hlocal Hlive.
  destruct Hlocal as [pc i Hnth|slot dst args Hnot Hedge|y Hterm].
  - cbn [spp_source ssa_instruction_payload].
    assert (Hpc : pc < length (bbody b)) by
      (apply nth_error_Some; rewrite Hnth; discriminate).
    rewrite (ssa_refine_point_exec ext P f fd l b pc Hwf Hf Hb ltac:(lia)).
    destruct Hlive as [Huse|[Hkill Hnext]].
    + eapply (ssa_refined_live_use ext P f fd l b _ _ _ Hwf Hf Hb
        (SsaRefinedLocalInstruction _ _ _ pc i Hnth)).
      apply in_map; exact Huse.
    + eapply (ssa_refined_live_next ext P f fd l b _ _ _ Hwf Hf Hb
        (SsaRefinedLocalInstruction _ _ _ pc i Hnth)).
      * cbn [ssa_refined_instruction_row srp_defs snd]; intro Hin.
        apply in_map_iff in Hin; destruct Hin as [y [Heq Hy]];
          injection Heq as <-; exact (Hkill Hy).
      * cbn [ssa_instruction_payload spp_target] in Hnext.
        rewrite (ssa_refine_point_exec ext P f fd l b (S pc) Hwf Hf Hb ltac:(lia)) in Hnext.
        exact Hnext.
  - cbn [spp_source ssa_transfer_payload].
    rewrite (ssa_refine_point_exec ext P f fd l b (length (bbody b)) Hwf Hf Hb ltac:(lia)).
    exact (ssa_transfer_live_forward ext P f fd l b slot dst args x Hwf Hf Hb Hedge Hlive).
  - cbn [spp_source].
    rewrite (ssa_refine_point_exec ext P f fd l b (length (bbody b)) Hwf Hf Hb ltac:(lia)).
    destruct Hlive as [Huse|[Hkill Hnext]].
    + eapply (ssa_refined_live_use ext P f fd l b _ _ _ Hwf Hf Hb
        (SsaRefinedLocalReturn _ _ _ y Hterm)).
      cbn in Huse |- *; destruct Huse as [<-|Hfalse]; [left; reflexivity|contradiction].
    + cbn [spp_target] in Hnext.
      rewrite (ssa_refine_point_endpoint ext P f fd l b Hwf Hf Hb), Hterm in Hnext.
      exfalso; exact (ssa_refined_inactive_dead P f (SsaAfterReturn l)
        (SsaSourceValue x) I Hnext).
Qed.

Local Lemma ssa_raw_exit_location ext P f n x :
  wf_program ext P -> In x (exit_uses (ssa_var_view ext P f) n) ->
  exists fd l b pc, find_func P f = Some fd /\ find_block fd l = Some b /\
    n = (l, pc) /\ pc < length (bbody b).
Proof.
  intros Hwf Huse.
  change (In x (ssa_get (pair_encoding nat_encoding nat_encoding) (ssa_exit_index P f) [] n))
    in Huse.
  unfold ssa_get in Huse.
  destruct (Map.get (pair_encoding nat_encoding nat_encoding) n (ssa_exit_index P f))
    as [xs|] eqn:Hget; [|contradiction].
  apply (ssa_map_get_sound (pair_encoding nat_encoding nat_encoding)) in Hget.
  apply in_flat_map in Hget; destruct Hget as [[l b] [Hblock Hrow]].
  apply in_map_iff in Hrow; destruct Hrow as [[pc i] [Heq Henum]].
  apply (f_equal fst) in Heq; cbn [fst snd] in Heq; subst n.
  unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
    [|contradiction].
  apply ssa_enumerate_nth in Henum; destruct Henum as [offset [Hpc Hnth]].
  cbn [fst snd] in Hpc, Hnth; replace offset with pc in Hnth by lia.
  exists fd, l, b, pc; split; [reflexivity|]; split.
  - apply first_index_complete;
      [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|exact Hblock].
  - split; [reflexivity|apply nth_error_Some; rewrite Hnth; discriminate].
Qed.

Local Lemma ssa_source_liveness_forward ext P f x n :
  wf_program ext P -> syntactic_live (var_point_uses (ssa_var_view ext P f)) x n ->
  syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
    (ssa_refine_point P f n).
Proof.
  intros Hwf Hlive; induction Hlive as [n Huse|n e Hout Huse|n e Hout Hkill Hlive IH].
  - destruct (ssa_raw_exit_location ext P f n x Hwf Huse)
      as [fd [l [b [pc [Hf [Hb [-> Hpc]]]]]]].
    rewrite (ssa_refine_point_exec ext P f fd l b pc Hwf Hf Hb ltac:(lia)).
    apply live_exit; rewrite (proj1 (ssa_refined_exit_agrees ext P f l pc)).
    apply in_map; exact Huse.
  - destruct (ssa_raw_out_local ext P f n e Hwf Hout)
      as [fd [l [b [p [Hf [Hb [Hlocal Hsource]]]]]]].
    rewrite <- Hsource; apply (ssa_raw_local_live_forward ext P f fd l b e p x
      Hwf Hf Hb Hlocal); left.
    change (In x (match Map.get ssa_edge_encoding e (ssa_point_index P f) with
      | Some p => spp_uses p | None => [] end)) in Huse.
    rewrite (ssa_raw_local_index ext P f fd l b e p Hwf Hf Hb Hlocal) in Huse;
      exact Huse.
  - destruct (ssa_raw_out_local ext P f n e Hwf Hout)
      as [fd [l [b [p [Hf [Hb [Hlocal Hsource]]]]]]].
    rewrite <- Hsource; apply (ssa_raw_local_live_forward ext P f fd l b e p x
      Hwf Hf Hb Hlocal); right; split.
    + change (~ In x (match Map.get ssa_edge_encoding e (ssa_point_index P f) with
        | Some p => spp_defs p | None => [] end)) in Hkill.
      rewrite (ssa_raw_local_index ext P f fd l b e p Hwf Hf Hb Hlocal) in Hkill;
        exact Hkill.
    + change (syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
        (ssa_refine_point P f (Graph.target (ssa_point_graph P f) e))) in IH.
      rewrite (proj2 (ssa_raw_local_edge ext P f fd l b e p Hwf Hf Hb Hlocal)) in IH;
        exact IH.
Qed.

Local Definition ssa_raw_live_at ext P f x (n : ssa_refined_point) : Prop :=
  match n with
  | SsaExecPoint l pc => syntactic_live (var_point_uses (ssa_var_view ext P f)) x (l, pc)
  | SsaBeforeParams l => exists fd b,
      find_func P f = Some fd /\ find_block fd l = Some b /\
      ~ In x (map fst (bparams b)) /\
      syntactic_live (var_point_uses (ssa_var_view ext P f)) x (l, 0)
  | SsaCallReady l => exists fd b,
      find_func P f = Some fd /\ find_block fd l = Some b /\
      syntactic_live (var_point_uses (ssa_var_view ext P f)) x (l, length (bbody b))
  | SsaAfterReturn _ | SsaDeadPoint _ => False
  end.

Local Lemma ssa_raw_transfer_live ext P f fd l b slot dst args x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
  (In x (ssa_selected_uses (bterm b) args) \/
    (~ In x (map fst (bparams (ssa_get nat_encoding (first_index (ssa_blocks P f))
      (SBlock [] [] (TRet 0)) dst))) /\
      syntactic_live (var_point_uses (ssa_var_view ext P f)) x (dst, 0))) ->
  syntactic_live (var_point_uses (ssa_var_view ext P f)) x (l, length (bbody b)).
Proof.
  intros Hwf Hf Hb Hedge Hlive.
  assert (Hnot : forall y, bterm b <> TRet y).
  { intros y Hterm; rewrite Hterm in Hedge; destruct slot; discriminate. }
  pose proof (SsaLocalTransfer (first_index (ssa_blocks P f)) l b slot dst args Hnot Hedge)
    as Hlocal.
  destruct Hlive as [Huse|[Hkill Hnext]].
  - exact (ssa_raw_live_use ext P f fd l b _ _ x Hwf Hf Hb Hlocal Huse).
  - exact (ssa_raw_live_next ext P f fd l b _ _ x Hwf Hf Hb Hlocal Hkill Hnext).
Qed.

Local Lemma ssa_refined_use_backward ext P f fd l b e p x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refined_local (first_index (ssa_blocks P f)) l b e p ->
  In (SsaSourceValue x) (srp_uses p) -> ssa_raw_live_at ext P f x (srp_source p).
Proof.
  intros Hwf Hf Hb Hlocal Huse.
  destruct Hlocal as [|pc i Hnth|c args k Hterm|slot dst args Hedge|y Hterm].
  - contradiction.
  - apply in_map_iff in Huse; destruct Huse as [y [Heq Hy]]; injection Heq as Heq; subst y.
    exact (ssa_raw_live_use ext P f fd l b _ _ x Hwf Hf Hb
      (SsaLocalInstruction _ _ _ pc i Hnth) Hy).
  - apply in_map_iff in Huse; destruct Huse as [y [Heq Hy]]; injection Heq as Heq; subst y.
    apply (ssa_raw_transfer_live ext P f fd l b 0 k [] x Hwf Hf Hb).
    + rewrite Hterm; reflexivity.
    + left; rewrite Hterm; exact Hy.
  - cbn [ssa_refined_transfer_row snd srp_source srp_uses] in Huse |- *.
    pose proof (ssa_raw_transfer_live ext P f fd l b slot dst args x Hwf Hf Hb Hedge)
      as Hraw.
    destruct (bterm b); try (apply Hraw; left; apply in_map_iff in Huse;
      destruct Huse as [y [Heq Hy]]; injection Heq as <-; exact Hy).
    cbn in Huse; destruct Huse as [Hfalse|Hfalse]; [discriminate|contradiction].
  - cbn in Huse; destruct Huse as [Heq|Hfalse];
      [injection Heq as Heq; subst y|contradiction].
    exact (ssa_raw_live_use ext P f fd l b _ _ x Hwf Hf Hb
      (SsaLocalReturn _ _ _ x Hterm) (or_introl eq_refl)).
Qed.

Local Lemma ssa_refined_next_backward ext P f fd l b e p x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  ssa_refined_local (first_index (ssa_blocks P f)) l b e p ->
  ~ In (SsaSourceValue x) (srp_defs p) -> ssa_raw_live_at ext P f x (srp_target p) ->
  ssa_raw_live_at ext P f x (srp_source p).
Proof.
  intros Hwf Hf Hb Hlocal Hkill Hnext.
  destruct Hlocal as [|pc i Hnth|c args k Hterm|slot dst args Hedge|y Hterm].
  - exists fd, b; split; [exact Hf|]; split; [exact Hb|]; split; [|exact Hnext].
    intro Hin; apply Hkill; apply in_map; exact Hin.
  - eapply (ssa_raw_live_next ext P f fd l b _ _ x Hwf Hf Hb
      (SsaLocalInstruction _ _ _ pc i Hnth)); [|exact Hnext].
    intro Hin; apply Hkill; apply in_map; exact Hin.
  - destruct Hnext as [fd' [b' [Hf' [Hb' Hlive]]]].
    rewrite Hf in Hf'; injection Hf' as <-; rewrite Hb in Hb'; injection Hb' as <-.
    exact Hlive.
  - assert (Htargeteq : srp_target (snd (ssa_refined_transfer_row
      (first_index (ssa_blocks P f)) l b (slot, (dst, args)))) = SsaBeforeParams dst).
    { unfold ssa_refined_transfer_row; cbn [fst snd]; destruct (bterm b); reflexivity. }
    rewrite Htargeteq in Hnext.
    change (exists fd' target, find_func P f = Some fd' /\
      find_block fd' dst = Some target /\ ~ In x (map fst (bparams target)) /\
      syntactic_live (var_point_uses (ssa_var_view ext P f)) x (dst, 0)) in Hnext.
    destruct Hnext as [fd' [target [Hf' [Htarget [Hparams Hlive]]]]].
    rewrite Hf in Hf'; injection Hf' as <-.
    assert (Hraw : syntactic_live (var_point_uses (ssa_var_view ext P f)) x
      (l, length (bbody b))).
    { apply (ssa_raw_transfer_live ext P f fd l b slot dst args x Hwf Hf Hb Hedge).
      right; split; [|exact Hlive].
      rewrite (ssa_block_index_at P f fd dst target Hf Htarget); exact Hparams. }
    cbn [ssa_refined_transfer_row snd srp_source ssa_raw_live_at].
    destruct (bterm b); try exact Hraw.
    exists fd, b; repeat split; assumption.
  - exfalso; exact Hnext.
Qed.

Local Lemma ssa_source_liveness_backward ext P f x n :
  wf_program ext P -> syntactic_live (point_model (ssa_refined_points P f))
    (SsaSourceValue x) n -> ssa_raw_live_at ext P f x n.
Proof.
  intros Hwf Hlive.
  induction Hlive as [n Huse|n e Hout Huse|n e Hout Hkill Hlive IH].
  - destruct n as [l|l pc|l|l|l]; try contradiction.
    rewrite (proj1 (ssa_refined_exit_agrees ext P f l pc)) in Huse.
    apply in_map_iff in Huse; destruct Huse as [y [Heq Hy]]; injection Heq as <-.
    apply live_exit; exact Hy.
  - destruct (ssa_refined_out_local ext P f n e Hwf Hout)
      as [fd [l [b [p [Hf [Hb [Hlocal Hsource]]]]]]].
    rewrite <- Hsource; apply (ssa_refined_use_backward ext P f fd l b e p x
      Hwf Hf Hb Hlocal).
    change (In (SsaSourceValue x) (match Map.get ssa_refined_edge_encoding e
      (ssa_refined_index P f) with | Some q => srp_uses q | None => [] end)) in Huse.
    rewrite (ssa_refined_index_complete ext P f fd l b e p Hwf Hf Hb Hlocal) in Huse;
      exact Huse.
  - destruct (ssa_refined_out_local ext P f n e Hwf Hout)
      as [fd [l [b [p [Hf [Hb [Hlocal Hsource]]]]]]].
    rewrite <- Hsource; apply (ssa_refined_next_backward ext P f fd l b e p x
      Hwf Hf Hb Hlocal).
    + change (~ In (SsaSourceValue x) (match Map.get ssa_refined_edge_encoding e
        (ssa_refined_index P f) with | Some q => srp_defs q | None => [] end)) in Hkill.
      rewrite (ssa_refined_index_complete ext P f fd l b e p Hwf Hf Hb Hlocal) in Hkill;
        exact Hkill.
    + change (ssa_raw_live_at ext P f x (Graph.target (ssa_refined_graph P f) e)) in IH.
      rewrite (proj2 (ssa_refined_local_edge ext P f fd l b e p Hwf Hf Hb Hlocal)) in IH;
        exact IH.
Qed.

(** Source-variable liveness agrees at every listed raw point, including unreachable blocks. *)
Theorem ssa_refined_liveness (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  forall n x, In n (Graph.nodes (cfg (ssa_point_view ext P f))) ->
  (syntactic_live (var_point_uses (ssa_var_view ext P f)) x n <->
   syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
     (ssa_refine_point P f n)).
Proof.
  intros Hwf Hfunction n x Hnode; split.
  - exact (ssa_source_liveness_forward ext P f x n Hwf).
  - change (In n (flat_map ssa_raw_points (ssa_blocks P f))) in Hnode.
    apply in_flat_map in Hnode; destruct Hnode as [[l b] [Hblock Hnode]].
    apply in_map_iff in Hnode; destruct Hnode as [pc [Heq Hpc]];
      cbn [fst snd] in Heq; subst n.
    apply in_seq in Hpc; cbn [fst snd] in Hpc.
    unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
      [|contradiction].
    assert (Hb : find_block fd l = Some b).
    { apply first_index_complete;
        [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|exact Hblock]. }
    destruct (le_dec pc (length (bbody b))) as [Hbefore|Hafter].
    + rewrite (ssa_refine_point_exec ext P f fd l b pc Hwf Hf Hb Hbefore).
      exact (ssa_source_liveness_backward ext P f x (SsaExecPoint l pc) Hwf).
    + replace pc with (S (length (bbody b))) by lia.
      exact (proj2 (ssa_refined_endpoint_liveness ext P f fd l b x Hwf Hf Hb)).
Qed.

(** * Unique source-definition occurrences *)

(** Proof occurrences distinguish parameter arrivals from instruction sources. *)
Local Definition ssa_source_occurrences (lb : label * ssa_block)
    : list (vid * ((label * nat) * option instr)) :=
  map (fun x => (x, ((fst lb, 0), None))) (map fst (bparams (snd lb))) ++
  flat_map (fun pi => map (fun x => (x, ((fst lb, fst pi), Some (snd pi))))
    (instr_def (snd pi))) (ssa_enumerate 0 (bbody (snd lb))).

Local Lemma ssa_enumerate_flat_map {A B} (h : A -> list B) xs start :
  flat_map (fun pi => h (snd pi)) (ssa_enumerate start xs) = flat_map h xs.
Proof.
  revert start; induction xs as [|a xs IH]; intro start; cbn; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

Local Lemma ssa_map_flat_map {A B C} (f : B -> C) (h : A -> list B) xs :
  map f (flat_map h xs) = flat_map (fun x => map f (h x)) xs.
Proof.
  induction xs as [|x xs IH]; cbn; [reflexivity|rewrite map_app, IH; reflexivity].
Qed.

Local Lemma ssa_source_occurrence_keys lb :
  map fst (ssa_source_occurrences lb) = block_defs (snd lb).
Proof.
  unfold ssa_source_occurrences, block_defs, body_defs.
  rewrite map_app, map_map, ssa_map_flat_map; cbn [fst snd].
  rewrite (flat_map_ext _ (fun pi => instr_def (snd pi))).
  - rewrite ssa_enumerate_flat_map, map_id; reflexivity.
  - intro pi; rewrite map_map; apply map_id.
Qed.

Local Lemma ssa_source_all_keys bs :
  map fst (flat_map ssa_source_occurrences bs) = flat_map (fun lb => block_defs (snd lb)) bs.
Proof.
  induction bs as [|lb bs IH]; cbn [flat_map]; [reflexivity|].
  rewrite map_app, ssa_source_occurrence_keys, IH; reflexivity.
Qed.

Local Lemma ssa_function_definitions_nodup ext P f fd :
  wf_program ext P -> find_func P f = Some fd ->
  NoDup (flat_map (fun lb => block_defs (snd lb)) (blocks fd)).
Proof.
  intros [_ [_ [Hunique _]]] Hf.
  exact (ssa_flat_map_nodup_member _ _ (f, fd) Hunique (first_index_sound _ _ _ Hf)).
Qed.

Local Lemma ssa_source_occurrence_unique ext P f x p q :
  wf_program ext P ->
  In (x, p) (flat_map ssa_source_occurrences (ssa_blocks P f)) ->
  In (x, q) (flat_map ssa_source_occurrences (ssa_blocks P f)) -> p = q.
Proof.
  intros Hwf Hp Hq.
  apply (ssa_label_unique (flat_map ssa_source_occurrences (ssa_blocks P f)) x p q);
    try assumption.
  rewrite ssa_source_all_keys; unfold ssa_blocks.
  destruct (find_func P f) as [fd|] eqn:Hf; [|constructor].
  exact (ssa_function_definitions_nodup ext P f fd Hwf Hf).
Qed.

Local Lemma ssa_source_parameter_occurrence P f fd l b x :
  find_func P f = Some fd -> find_block fd l = Some b -> In x (map fst (bparams b)) ->
  In (x, ((l, 0), None)) (flat_map ssa_source_occurrences (ssa_blocks P f)).
Proof.
  intros Hf Hb Hx; apply in_flat_map; exists (l, b); split.
  - unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
  - apply in_or_app; left; apply in_map_iff; exists x; split; [reflexivity|exact Hx].
Qed.

Local Lemma ssa_source_instruction_occurrence P f fd l b pc i x :
  find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (bbody b) pc = Some i -> In x (instr_def i) ->
  In (x, ((l, pc), Some i)) (flat_map ssa_source_occurrences (ssa_blocks P f)).
Proof.
  intros Hf Hb Hnth Hx; apply in_flat_map; exists (l, b); split.
  - unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
  - apply in_or_app; right; apply in_flat_map; exists (pc, i); split.
    + apply ssa_enumerate_nth; exists pc; split; [lia|exact Hnth].
    + apply in_map_iff; exists x; split; [reflexivity|exact Hx].
Qed.

Local Lemma ssa_enumerate_map {A B} (h : A -> B) xs start :
  map (fun pi => h (snd pi)) (ssa_enumerate start xs) = map h xs.
Proof.
  revert start; induction xs as [|a xs IH]; intro start; cbn; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

Local Definition ssa_call_targets P f := FinSet.of_list nat_encoding (flat_map (fun lb =>
  match bterm (snd lb) with TCall _ _ k => [k] | _ => [] end) (ssa_blocks P f)).

Local Definition ssa_definition_rows targets (lb : label * ssa_block) :=
  ssa_parameter_rows targets (fst lb) (snd lb) ++
    flat_map (ssa_instruction_rows (fst lb)) (bbody (snd lb)).

Local Lemma ssa_definition_row_keys targets lb :
  map fst (ssa_definition_rows targets lb) = block_defs (snd lb).
Proof.
  unfold ssa_definition_rows, ssa_parameter_rows, block_defs, body_defs.
  rewrite map_app, map_map, ssa_map_flat_map; cbn [fst snd].
  rewrite ssa_enumerate_map.
  f_equal; apply flat_map_ext; intro i; destruct i; reflexivity.
Qed.

Local Lemma ssa_definition_all_keys targets bs :
  map fst (flat_map (ssa_definition_rows targets) bs) =
    flat_map (fun lb => block_defs (snd lb)) bs.
Proof.
  induction bs as [|lb bs IH]; cbn [flat_map]; [reflexivity|].
  rewrite map_app, ssa_definition_row_keys, IH; reflexivity.
Qed.

Local Lemma ssa_definition_lookup ext P f x value :
  wf_program ext P ->
  In (x, value) (flat_map (ssa_definition_rows (ssa_call_targets P f)) (ssa_blocks P f)) ->
  Map.get nat_encoding x (ssa_definitions P f) = Some value.
Proof.
  intros Hwf Hin; apply ssa_map_get_complete; [exact Hin|].
  intros other Hother; apply (ssa_label_unique
    (flat_map (ssa_definition_rows (ssa_call_targets P f)) (ssa_blocks P f)) x other value);
    try assumption.
  rewrite ssa_definition_all_keys; unfold ssa_blocks.
  destruct (find_func P f) as [fd|] eqn:Hf; [|constructor].
  exact (ssa_function_definitions_nodup ext P f fd Hwf Hf).
Qed.

Local Lemma ssa_instruction_definition ext P f fd l b pc i x definition :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (bbody b) pc = Some i -> In (x, (l, definition)) (ssa_instruction_rows l i) ->
  def (ssa_block_view ext P f) x = definition.
Proof.
  intros Hwf Hf Hb Hnth Hrow; change
    (snd (ssa_get nat_encoding (ssa_definitions P f) (0, Arbitrary) x) = definition).
  unfold ssa_get; rewrite (ssa_definition_lookup ext P f x (l, definition) Hwf);
    [reflexivity|].
  apply in_flat_map; exists (l, b); split.
  - unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
  - apply in_or_app; right; apply in_flat_map; exists i;
      split; [exact (nth_error_In _ pc Hnth)|exact Hrow].
Qed.

Local Lemma ssa_parameter_definition_at ext P f fd l b i x ty :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (bparams b) i = Some (x, ty) ->
  def (ssa_block_view ext P f) x =
    if FinSet.mem nat_encoding l (ssa_call_targets P f) then Arbitrary else Param l i.
Proof.
  intros Hwf Hf Hb Hnth; change (snd (ssa_get nat_encoding (ssa_definitions P f)
    (0, Arbitrary) x) =
      if FinSet.mem nat_encoding l (ssa_call_targets P f) then Arbitrary else Param l i).
  unfold ssa_get; rewrite (ssa_definition_lookup ext P f x
    (l, if FinSet.mem nat_encoding l (ssa_call_targets P f) then Arbitrary else Param l i)
    Hwf); [reflexivity|].
  apply in_flat_map; exists (l, b); split.
  - unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
  - apply in_or_app; left; unfold ssa_parameter_rows; apply in_map_iff;
      exists (i, (x, ty)); split; [reflexivity|].
    apply ssa_enumerate_nth; exists i; split; [lia|exact Hnth].
Qed.

Local Lemma ssa_block_payload_rows_unique ext P f e p q :
  wf_program ext P -> In (e, p) (flat_map (fun lb =>
    ssa_block_rows (fst lb) (snd lb)) (ssa_blocks P f)) ->
  In (e, q) (flat_map (fun lb => ssa_block_rows (fst lb) (snd lb)) (ssa_blocks P f)) -> p = q.
Proof.
  intros Hwf Hp Hq; apply in_flat_map in Hp; apply in_flat_map in Hq.
  destruct Hp as [[l b] [Hblock Hp]], Hq as [[l' b'] [Hblock' Hq]].
  destruct (ssa_block_row_coordinate l b e p Hp) as [Hsrc [Hnth Hpayload]].
  destruct (ssa_block_row_coordinate l' b' e q Hq) as [Hsrc' [Hnth' Hpayload']].
  assert (Hlabel : l' = l) by congruence; rewrite Hlabel in Hblock', Hq.
  unfold ssa_blocks in Hblock, Hblock'; destruct (find_func P f) as [fd|] eqn:Hf;
    [|contradiction].
  assert (Hb : b' = b).
  { exact (ssa_label_unique (blocks fd) l b' b
      (proj1 (proj2 (wf_function ext P f fd Hwf Hf))) Hblock' Hblock). }
  subst b'; rewrite Hnth in Hnth'; injection Hnth' as Hargs.
  rewrite Hpayload, Hpayload', Hargs; reflexivity.
Qed.

Local Lemma ssa_block_payload_at ext P f fd l b slot dst args :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
  ssa_get ssa_edge_encoding (ssa_block_payloads P f) (SsaBlockPayload [] [])
    (SsaEdge l dst slot) = SsaBlockPayload args (ssa_guard (bterm b) slot).
Proof.
  intros Hwf Hf Hb Hedge; unfold ssa_get, ssa_block_payloads.
  rewrite (ssa_map_get_complete ssa_edge_encoding _ _
    (SsaBlockPayload args (ssa_guard (bterm b) slot))); [reflexivity| |].
  - apply in_flat_map; exists (l, b); split.
    + unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
    + apply ssa_block_row_complete; exact Hedge.
  - intros p Hp; eapply ssa_block_payload_rows_unique; [exact Hwf|exact Hp|].
    apply in_flat_map; exists (l, b); split.
    + unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
    + apply ssa_block_row_complete; exact Hedge.
Qed.

Local Lemma ssa_switch_guards ext P f a c cases d da z :
  aenv a c = Some (VInt W32 z) ->
  Forall (cond_holds (ssa_block_view ext P f) a)
    (ssa_guard (TSwitch c cases d da) (ssa_switch_slot z cases)).
Proof.
  intro Hvalue; unfold ssa_guard; induction cases as [|[[key dst] args] cases IH].
  - constructor.
  - cbn [ssa_switch_slot]; destruct (Z.eqb z (word_wrap W32 key)) eqn:Hkey.
    + apply Z.eqb_eq in Hkey; constructor; [|constructor].
      exists (VInt W32 z); split; [exact Hvalue|].
      change (VInt W32 z = VInt W32 (word_wrap W32 key)); f_equal; exact Hkey.
    + cbn [nth_error]; destruct (nth_error cases (ssa_switch_slot z cases))
        as [[[key' dst'] args']|] eqn:Hnth; [exact IH|].
      constructor; [|exact IH].
      exists (VInt W32 z); split; [exact Hvalue|].
      change (VInt W32 z <> VInt W32 (word_wrap W32 key)); intro Heq; injection Heq as Heq.
      apply Z.eqb_neq in Hkey; exact (Hkey Heq).
Qed.

Local Lemma ssa_selected_guards ext P f a t slot :
  ssa_term_slot (aenv a) t = Some slot ->
  Forall (cond_holds (ssa_block_view ext P f) a) (ssa_guard t slot).
Proof.
  destruct t as [dst args|c l1 a1 l2 a2|c cases d da|callee args k|x];
    cbn [ssa_term_slot ssa_guard]; try (intro Hslot; constructor).
  - destruct (aenv a c) as [value|] eqn:Hvalue; [|discriminate].
    destruct value as [[|] z|block offset|callee|bits|bits]; try discriminate.
    destruct (Z.eqb z 0) eqn:Hzero.
    + intro Hslot; injection Hslot as Hslot; subst slot; constructor; [|constructor].
      exists (VInt W32 z); split; [exact Hvalue|].
      change (negb (Z.eqb z 0) = false); rewrite Hzero; reflexivity.
    + intro Hslot; injection Hslot as Hslot; subst slot; constructor; [|constructor].
      exists (VInt W32 z); split; [exact Hvalue|].
      change (negb (Z.eqb z 0) = true); rewrite Hzero; reflexivity.
  - destruct (aenv a c) as [value|] eqn:Hvalue; [|discriminate].
    destruct value as [[|] z|block offset|callee|bits|bits]; try discriminate.
    intro Hslot; injection Hslot as <-.
    exact (ssa_switch_guards ext P f a c cases d da z Hvalue).
Qed.

Local Lemma ssa_block_guards_ok ext P f a tr a' e :
  wf_program ext P -> ssa_block_taken P f a tr a' e ->
  Forall (cond_holds (ssa_block_view ext P f) a) (edge_guard (ssa_block_view ext P f) e).
Proof.
  intros Hwf [fd [b [Hf [Hb [Hpc [Hsrc [Hdst [Hzero [Hedge Hslot]]]]]]]]].
  destruct (ssa_block_edge_nth _ _ _ Hedge) as [_ [args Hnth]].
  destruct e as [src dst slot]; cbn [esrc edst eslot] in *; subst src.
  change (Forall (cond_holds (ssa_block_view ext P f) a)
    (sbp_guard (ssa_get ssa_edge_encoding (ssa_block_payloads P f)
      (SsaBlockPayload [] []) (SsaEdge (alabel a) dst slot)))).
  rewrite (ssa_block_payload_at ext P f fd (alabel a) b slot dst args Hwf Hf Hb Hnth).
  exact (ssa_selected_guards ext P f a (bterm b) slot Hslot).
Qed.

(** * Availability and static definition dominance *)

(** A certificate's available values are read through the prepared source block lookup. *)
Local Definition ssa_available (fd : fdef) (R : requirements) (n : label * nat) : list vid :=
  match find_block fd (fst n) with
  | Some b => available_at b R (fst n) (snd n)
  | None => []
  end.

Local Lemma ssa_available_at fd R l b pc :
  find_block fd l = Some b -> ssa_available fd R (l, pc) = available_at b R l pc.
Proof.
  intro Hb; unfold ssa_available; cbn [fst snd]; rewrite Hb; reflexivity.
Qed.

Local Lemma ssa_available_local ext P f fd R l b e p x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  availability_certificate fd R ->
  ssa_point_local (first_index (ssa_blocks P f)) l b e p ->
  In x (ssa_available fd R (spp_target p)) ->
  In x (ssa_available fd R (spp_source p)) \/ In x (spp_defs p).
Proof.
  intros Hwf Hf Hb Hcert Hlocal.
  destruct Hlocal as [pc i Hnth|slot dst args Hnot Hedge|y Hterm].
  - change (In x (ssa_available fd R (l, S pc)) ->
      In x (ssa_available fd R (l, pc)) \/ In x (instr_def i)).
    rewrite (ssa_available_at fd R l b pc Hb), (ssa_available_at fd R l b (S pc) Hb).
    unfold available_at, prefix_defs; rewrite (firstn_step _ _ _ Hnth), flat_map_app.
    cbn [flat_map]; rewrite app_nil_r, !in_app_iff; tauto.
  - destruct (ssa_term_target ext P f fd l b dst args Hwf Hf Hb
      (nth_error_In _ slot Hedge)) as [target Htarget].
    change (In x (ssa_available fd R (dst, 0)) ->
      In x (ssa_available fd R (l, length (bbody b))) \/
      In x (map fst (bparams (ssa_get nat_encoding (first_index (ssa_blocks P f))
        (SBlock [] [] (TRet 0)) dst)))).
    rewrite (ssa_available_at fd R dst target 0 Htarget),
      (ssa_available_at fd R l b (length (bbody b)) Hb),
      (ssa_block_index_at P f fd dst target Hf Htarget).
    unfold available_at, prefix_defs; cbn [firstn flat_map app]; rewrite firstn_all.
    intros Hin; apply in_app_iff in Hin; destruct Hin as [Hparam|Hrequired];
      [right; exact Hparam|left].
    destruct (certificate_block fd R l b Hcert Hb) as [_ [_ Hedges]].
    exact (proj1 (Forall_forall _ _)
      (proj1 (Forall_forall _ _) Hedges (dst, args) (nth_error_In _ slot Hedge)) x Hrequired).
  - change (In x (ssa_available fd R (l, S (length (bbody b)))) ->
      In x (ssa_available fd R (l, length (bbody b))) \/ In x []).
    rewrite (ssa_available_at fd R l b _ Hb), (ssa_available_at fd R l b _ Hb).
    unfold available_at, prefix_defs; rewrite firstn_all2 by lia.
    rewrite firstn_all; intro Hin; left; exact Hin.
Qed.

Local Lemma ssa_available_edge ext P f fd R e x :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  In e (Graph.out (ssa_point_graph P f) (Graph.source (ssa_point_graph P f) e)) ->
  In x (ssa_available fd R (Graph.target (ssa_point_graph P f) e)) ->
  In x (ssa_available fd R (Graph.source (ssa_point_graph P f) e)) \/
    In x (defs (ssa_var_view ext P f) e).
Proof.
  intros Hwf Hf Hcert Hout Havailable.
  destruct (ssa_raw_out_local ext P f _ e Hwf Hout)
    as [fd' [l [b [p [Hf' [Hb [Hlocal Hsource]]]]]]].
  rewrite Hf in Hf'; injection Hf' as Hfd; subst fd'.
  rewrite (proj2 (ssa_raw_local_edge ext P f fd l b e p Hwf Hf Hb Hlocal)) in Havailable.
  destruct (ssa_available_local ext P f fd R l b e p x Hwf Hf Hb Hcert Hlocal Havailable)
    as [Hin|Hin].
  - left; rewrite <- Hsource; exact Hin.
  - right; change (In x (match Map.get ssa_edge_encoding e (ssa_point_index P f) with
      | Some p => spp_defs p | None => [] end)).
    rewrite (ssa_raw_local_index ext P f fd l b e p Hwf Hf Hb Hlocal); exact Hin.
Qed.

Local Lemma ssa_available_path ext P f fd R n es m :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  path (ssa_point_graph P f) n es m ->
  forall x, In x (ssa_available fd R m) ->
  In x (ssa_available fd R n) \/ exists e, In e es /\ In x (defs (ssa_var_view ext P f) e).
Proof.
  intros Hwf Hf Hcert Hpath; induction Hpath as [n|e es m Hout Hpath IH]; intros x Hx.
  - left; exact Hx.
  - destruct (IH x Hx) as [Hin|[a [Hin Hdef]]].
    + destruct (ssa_available_edge ext P f fd R e x Hwf Hf Hcert Hout Hin)
        as [Hbefore|Hdef].
      * left; exact Hbefore.
      * right; exists e; split; [left; reflexivity|exact Hdef].
    + right; exists a; split; [right; exact Hin|exact Hdef].
Qed.

Local Lemma ssa_raw_definition_edge ext P f x home origin e :
  wf_program ext P ->
  In (x, (home, origin)) (flat_map ssa_source_occurrences (ssa_blocks P f)) ->
  In x (defs (ssa_var_view ext P f) e) ->
  match origin with
  | Some i => e = SsaEdge (fst home) (fst home) (snd home) /\
      Graph.source (ssa_point_graph P f) e = home
  | None => Graph.target (ssa_point_graph P f) e = home
  end.
Proof.
  intros Hwf Hsite Hdef.
  change (In x (match Map.get ssa_edge_encoding e (ssa_point_index P f) with
    | Some p => spp_defs p | None => [] end)) in Hdef.
  destruct (Map.get ssa_edge_encoding e (ssa_point_index P f)) as [p|] eqn:Hindex;
    [|contradiction].
  destruct (ssa_point_index_local ext P f e p Hwf Hindex)
    as [fd [l [b [Hf [Hb Hlocal]]]]].
  destruct Hlocal as [pc i Hnth|slot dst args Hnot Hedge|y Hterm].
  - pose proof (ssa_source_occurrence_unique ext P f x (home, origin) ((l, pc), Some i)
      Hwf Hsite (ssa_source_instruction_occurrence P f fd l b pc i x Hf Hb Hnth Hdef))
      as Heq.
    injection Heq as Hhome Horigin; subst home origin; split; [reflexivity|].
    change (match Map.get ssa_edge_encoding (SsaEdge l l pc) (ssa_point_index P f) with
      | Some p => spp_source p | None => (0, 0) end = (l, pc)).
    rewrite Hindex; reflexivity.
  - destruct (ssa_term_target ext P f fd l b dst args Hwf Hf Hb
      (nth_error_In _ slot Hedge)) as [target Htarget].
    change (In x (map fst (bparams (ssa_get nat_encoding (first_index (ssa_blocks P f))
      (SBlock [] [] (TRet 0)) dst)))) in Hdef.
    rewrite (ssa_block_index_at P f fd dst target Hf Htarget) in Hdef.
    pose proof (ssa_source_occurrence_unique ext P f x (home, origin) ((dst, 0), None)
      Hwf Hsite (ssa_source_parameter_occurrence P f fd dst target x Hf Htarget Hdef)) as Heq.
    injection Heq as Hhome Horigin; subst home origin.
    change (match Map.get ssa_edge_encoding (SsaEdge l dst (length (bbody b) + slot))
      (ssa_point_index P f) with | Some p => spp_target p | None => (0, 0) end = (dst, 0)).
    rewrite Hindex; reflexivity.
  - contradiction.
Qed.

Local Lemma ssa_path_source_occurs {N E} (g : Graph.t N E) s es n e :
  path g s es n -> In e es ->
  Graph.source g e = s \/ exists a, In a es /\ Graph.target g a = Graph.source g e.
Proof.
  intro Hpath; induction Hpath as [s|a es n Hout Hpath IH]; intro Hin;
    [contradiction|].
  destruct Hin as [Heq|Hin]; [subst e; left; reflexivity|].
  destruct (IH Hin) as [Heq|[b [Hb Htarget]]]; right.
  - exists a; split; [left; reflexivity|symmetry; exact Heq].
  - exists b; split; [right; exact Hb|exact Htarget].
Qed.

Local Lemma ssa_available_entry_site ext P f fd R x home origin s :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  In (x, (home, origin)) (flat_map ssa_source_occurrences (ssa_blocks P f)) ->
  In s (Graph.entries (ssa_point_graph P f)) -> In x (ssa_available fd R s) ->
  (home, origin) = (s, None).
Proof.
  intros Hwf Hf Hcert Hsite Hentry Havailable.
  change (In s (map (fun l => (l, 0)) (ssa_entries P f))) in Hentry.
  unfold ssa_entries in Hentry; rewrite Hf in Hentry; cbn in Hentry.
  destruct Hentry as [Heq|Hfalse]; [subst s|contradiction].
  destruct (proj1 (wf_function ext P f fd Hwf Hf)) as [b Hb].
  rewrite (ssa_available_at fd R (fentry fd) b 0 Hb) in Havailable.
  unfold available_at, prefix_defs in Havailable; cbn in Havailable.
  rewrite (proj1 Hcert), app_nil_r in Havailable.
  exact (ssa_source_occurrence_unique ext P f x (home, origin) ((fentry fd, 0), None)
    Hwf Hsite (ssa_source_parameter_occurrence P f fd (fentry fd) b x Hf Hb Havailable)).
Qed.

Local Lemma ssa_available_dominance ext P f fd R x home origin n :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  In (x, (home, origin)) (flat_map ssa_source_occurrences (ssa_blocks P f)) ->
  In x (ssa_available fd R n) -> dominates (ssa_point_graph P f) home n.
Proof.
  intros Hwf Hf Hcert Hsite Havailable s es Hentry Hpath.
  destruct (ssa_available_path ext P f fd R s es n Hwf Hf Hcert Hpath x Havailable)
    as [Hstart|[e [Hin Hdef]]].
  - pose proof (ssa_available_entry_site ext P f fd R x home origin s
      Hwf Hf Hcert Hsite Hentry Hstart) as Heq.
    injection Heq as Hhome Horigin; left; exact Hhome.
  - pose proof (ssa_raw_definition_edge ext P f x home origin e Hwf Hsite Hdef) as Hposition.
    destruct origin as [i|].
    + destruct Hposition as [_ Hsource].
      destruct (ssa_path_source_occurs _ _ _ _ e Hpath Hin) as [Heq|[a [Ha Htarget]]].
      * left; rewrite <- Hsource; exact Heq.
      * right; exists a; split; [exact Ha|rewrite <- Hsource; exact Htarget].
    + right; exists e; split; [exact Hin|exact Hposition].
Qed.

Local Lemma ssa_available_operation_edge ext P f fd R x home i n :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  In (x, (home, Some i)) (flat_map ssa_source_occurrences (ssa_blocks P f)) ->
  In x (ssa_available fd R n) ->
  edge_dominates (ssa_point_graph P f) (SsaEdge (fst home) (fst home) (snd home)) n.
Proof.
  intros Hwf Hf Hcert Hsite Havailable s es Hentry Hpath.
  destruct (ssa_available_path ext P f fd R s es n Hwf Hf Hcert Hpath x Havailable)
    as [Hstart|[e [Hin Hdef]]].
  - pose proof (ssa_available_entry_site ext P f fd R x home (Some i) s
      Hwf Hf Hcert Hsite Hentry Hstart) as Hfalse; discriminate.
  - destruct (ssa_raw_definition_edge ext P f x home (Some i) e Hwf Hsite Hdef)
      as [Heq Hsource]; rewrite <- Heq; exact Hin.
Qed.

Local Lemma ssa_source_site_exists P f x :
  In x (values_of P f) ->
  exists home origin, In (x, (home, origin))
    (flat_map ssa_source_occurrences (ssa_blocks P f)).
Proof.
  intro Hvalue; unfold values_of in Hvalue.
  apply (proj1 (FinSet.elements_spec nat_encoding x _ (demand_universe_wf _ _))) in Hvalue.
  apply FinSet.of_list_spec in Hvalue; rewrite <- ssa_source_all_keys in Hvalue.
  apply in_map_iff in Hvalue; destruct Hvalue as [[y [home origin]] [Heq Hin]];
    cbn in Heq; subst y; exists home, origin; exact Hin.
Qed.

Local Lemma ssa_operation_location ext P f x o args :
  wf_program ext P -> def (ssa_block_view ext P f) x = Op o args ->
  exists fd l b pc, find_func P f = Some fd /\ find_block fd l = Some b /\
    nth_error (bbody b) pc = Some (IOp x o args).
Proof.
  intros Hwf Hdef; change (snd (ssa_get nat_encoding (ssa_definitions P f)
    (0, Arbitrary) x) = Op o args) in Hdef.
  unfold ssa_get in Hdef; destruct (Map.get nat_encoding x (ssa_definitions P f))
    as [[home definition]|] eqn:Hget; [|discriminate].
  cbn [snd] in Hdef; subst definition.
  apply (ssa_map_get_sound nat_encoding) in Hget; apply in_flat_map in Hget.
  destruct Hget as [[l b] [Hblock Hrow]]; apply in_app_iff in Hrow.
  destruct Hrow as [Hparam|Hinstruction].
  - apply in_map_iff in Hparam; destruct Hparam as [[slot [key ty]] [Heq Hin]].
    cbn [fst snd] in Heq.
    match type of Heq with context [if ?test then _ else _] => destruct test end;
      discriminate.
  - apply in_flat_map in Hinstruction; destruct Hinstruction as [i [Hi Hrow]].
    destruct i; cbn [ssa_instruction_rows] in Hrow; try contradiction;
      destruct Hrow as [Heq|Hfalse]; try contradiction; try discriminate.
    injection Heq as Hx Hhome Ho Hargs; subst x home o args.
    apply In_nth_error in Hi; destruct Hi as [pc Hnth].
    unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
      [|contradiction].
    exists fd, l, b, pc; split; [reflexivity|]; split; [|exact Hnth].
    apply first_index_complete;
      [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|exact Hblock].
Qed.

Local Lemma ssa_source_frame_away ext P f x home origin a tr a' :
  wf_program ext P -> In f (map fst (funcs P)) ->
  In (x, (home, origin)) (flat_map ssa_source_occurrences (ssa_blocks P f)) ->
  reachable_state (activation ext P f) a ->
  exec_in (activation ext P f)
    (fun s => point (ssa_point_view ext P f) s <> home) a tr a' ->
  aenv a' x = aenv a x.
Proof.
  intros Hwf Hfunction Hsite Hreachable Hrun; revert Hreachable.
  induction Hrun as [a Haway|a tr a' tail a'' Haway Hstep Hrun IH]; intro Hreachable.
  - reflexivity.
  - assert (Hreachable' : reachable_state (activation ext P f) a') by
      (eapply reachable_state_step; eassumption).
    rewrite (IH Hreachable').
    destruct (ssa_point_steps_covered ext P f a tr a' Hwf Hstep) as [e Htaken].
    apply (ssa_raw_defs_frame ext P f a tr a' e x Hwf Hstep Htaken).
    intro Hdef; pose proof (ssa_raw_definition_edge ext P f x home origin e Hwf Hsite Hdef)
      as Hposition.
    destruct (view_taken_edge (activation ext P f) (ssa_point_view ext P f) a tr a' e
      (ssa_point_graph_laws ext P f Hwf Hfunction) Hreachable Hstep Htaken)
      as [Hedge [Hsource Htarget]].
    change (Graph.source (ssa_point_graph P f) e = point (ssa_point_view ext P f) a)
      in Hsource.
    change (Graph.target (ssa_point_graph P f) e = point (ssa_point_view ext P f) a')
      in Htarget.
    destruct origin as [i|].
    + destruct Hposition as [_ Hhome]; apply Haway; rewrite <- Hsource; exact Hhome.
    + pose proof (exec_in_start (activation ext P f) _ a' tail a'' Hrun) as Haway'.
      apply Haway'; rewrite <- Htarget; exact Hposition.
Qed.

Local Lemma ssa_operation_step_value ext P f a tr a' x o args :
  at_instr P (activation_frame f a) (IOp x o args) ->
  step (activation ext P f) a tr a' ->
  exists cs value, read_args (aenv a) args = Some cs /\ op_eval ext o cs = Some value /\
    aenv a' x = Some value.
Proof.
  intros Hat Hstep.
  destruct Hstep as
    [a y op inputs cs value Hrule Hread Heval
    |a y n block offset Hrule
    |a p Hrule
    |a y ty sz p value Hrule Htype Hvalid
    |a sz p y Hrule
    |a y value Hrule Hvalue
    |a dst inputs cs env Hrule Hread Hbind
    |a c l1 a1 l2 a2 z dst inputs cs env Hrule Hcond Hchoice Hread Hbind
    |a c cases d da z dst inputs cs env Hrule Hcond Hchoice Hread Hbind
    |a c inputs k ps result cs value env Hrule Hsig Hread Htype Hvalid Hbind
    |a y value Hrule Hvalue].
  all: try solve [exfalso; eapply ssa_at_instr_not_term; [exact Hat|exact Hrule]].
  all: try solve [pose proof (ssa_at_instr_unique P _ _ _ Hat Hrule) as Hfalse; discriminate].
  pose proof (ssa_at_instr_unique P _ _ _ Hat Hrule) as Heq.
  injection Heq as Hx Ho Hargs; subst y op inputs.
  exists cs, value; split; [exact Hread|]; split; [exact Heval|].
  cbn [activation_advance aenv]; unfold env_set; destruct (Nat.eq_dec x x);
    [reflexivity|contradiction].
Qed.

Local Lemma ssa_operation_taken_at ext P f fd l b pc x o args a tr a' :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  nth_error (bbody b) pc = Some (IOp x o args) ->
  ssa_point_taken P f a tr a' (SsaEdge l l pc) ->
  at_instr P (activation_frame f a) (IOp x o args).
Proof.
  intros Hwf Hf Hb Hnth [p [Hget [Hsource [Htarget Haction]]]].
  pose proof (ssa_raw_local_index ext P f fd l b _ _ Hwf Hf Hb
    (SsaLocalInstruction _ _ _ pc (IOp x o args) Hnth)) as Hindex.
  rewrite Hindex in Hget; injection Hget as Hp; subst p.
  cbn [ssa_instruction_payload spp_source] in Hsource; injection Hsource as Hl Hpc.
  exists fd, b; cbn [activation_frame ffunc flabel fpc]; rewrite Hl, Hpc.
  repeat split; assumption.
Qed.

Local Lemma ssa_operation_operands_preserved ext P f fd R l b pc x o args a u tr v tail :
  wf_program ext P -> In f (map fst (funcs P)) ->
  find_func P f = Some fd -> find_block fd l = Some b -> availability_certificate fd R ->
  nth_error (bbody b) pc = Some (IOp x o args) ->
  In (x, ((l, pc), Some (IOp x o args)))
    (flat_map ssa_source_occurrences (ssa_blocks P f)) ->
  Graph.source (ssa_point_graph P f) (SsaEdge l l pc) = (l, pc) ->
  reachable (ssa_point_graph P f) (Graph.source (ssa_point_graph P f) (SsaEdge l l pc)) ->
  edge_dominates (ssa_point_graph P f) (SsaEdge l l pc)
    (point (ssa_point_view ext P f) a) ->
  reachable_state (activation ext P f) v ->
  at_instr P (activation_frame f u) (IOp x o args) ->
  step (activation ext P f) u tr v ->
  exec_in (activation ext P f) (fun s => point (ssa_point_view ext P f) s <>
    Graph.source (ssa_point_graph P f) (SsaEdge l l pc)) v tail a ->
  forall y, In y args -> aenv a y = aenv u y.
Proof.
  intros Hwf Hfunction Hf Hb Hcert Hnth Hsite Hsource HsourceReach Hdom Hv Hat Hstep Htail.
  pose proof (ssa_point_graph_laws ext P f Hwf Hfunction) as Hview.
  intros y Hy.
  pose proof (body_available_use _ _ pc (IOp x o args)
    (proj1 (certificate_block fd R l b Hcert Hb)) Hnth) as Huses.
  assert (Hyavailable : In y (ssa_available fd R (l, pc))).
  { rewrite (ssa_available_at fd R l b pc Hb).
    exact (proj1 (Forall_forall _ _) Huses y Hy). }
  assert (Hdifferent : y <> x).
  { intro Heq; subst y; apply (edge_source_not_dominated (ssa_point_graph P f)
      (SsaEdge l l pc) HsourceReach).
    rewrite Hsource; exact (ssa_available_operation_edge ext P f fd R x (l, pc)
      (IOp x o args) (l, pc) Hwf Hf Hcert Hsite Hyavailable). }
  pose proof (ssa_instruction_types_defined P (static_ty P f) (IOp x o args)
    (wf_instruction ext P (SFrame f l pc (aenv u) 0) (IOp x o args) Hwf
      (ex_intro _ fd (ex_intro _ b (conj Hf (conj Hb Hnth)))))) as Htyped.
  destruct (proj1 (Forall_forall _ _) Htyped y Hy) as [ty Htype].
  destruct (ssa_source_site_exists P f y (ssa_static_value P f y ty Htype))
    as [home [origin Hysite]].
  pose proof (ssa_available_dominance ext P f fd R y home origin (l, pc)
    Hwf Hf Hcert Hysite Hyavailable) as Hydom.
  assert (Haway : exec_in (activation ext P f)
    (fun s => point (ssa_point_view ext P f) s <> home) v tail a).
  { eapply exec_in_away_home; [exact Hview|exact HsourceReach| |exact Hdom|exact Hv|
      exact Htail].
    change (dominates (ssa_point_graph P f) home
      (Graph.source (ssa_point_graph P f) (SsaEdge l l pc))).
    rewrite Hsource; exact Hydom. }
  rewrite (ssa_source_frame_away ext P f y home origin v tail a
    Hwf Hfunction Hysite Hv Haway).
  apply (ssa_instruction_frame ext P f u tr v (IOp x o args) y Hwf Hat Hstep).
  cbn [instr_def]; intros [Heq|Hfalse]; [apply Hdifferent; symmetry; exact Heq|contradiction].
Qed.

Local Lemma ssa_operation_consistent ext P f fd R l b pc x o args a :
  wf_program ext P -> In f (map fst (funcs P)) ->
  find_func P f = Some fd -> find_block fd l = Some b -> availability_certificate fd R ->
  nth_error (bbody b) pc = Some (IOp x o args) ->
  reachable_state (activation ext P f) a ->
  In x (ssa_available fd R (point (ssa_point_view ext P f) a)) ->
  exists cs value, Forall2 (fun y c => aenv a y = Some c) args cs /\
    aenv a x = Some value /\ op_eval ext o cs = Some value.
Proof.
  intros Hwf Hfunction Hf Hb Hcert Hnth Hreachable Havailable.
  pose proof (ssa_source_instruction_occurrence P f fd l b pc (IOp x o args) x Hf Hb Hnth
    (or_introl eq_refl)) as Hsite.
  pose proof (ssa_point_graph_laws ext P f Hwf Hfunction) as Hview.
  pose proof (ssa_available_operation_edge ext P f fd R x (l, pc) (IOp x o args)
    (point (ssa_point_view ext P f) a) Hwf Hf Hcert Hsite Havailable) as Hdom.
  assert (Hsource : Graph.source (ssa_point_graph P f) (SsaEdge l l pc) = (l, pc)).
  { change (match Map.get ssa_edge_encoding (SsaEdge l l pc) (ssa_point_index P f) with
      | Some p => spp_source p | None => (0, 0) end = (l, pc)).
    rewrite (ssa_raw_local_index ext P f fd l b _ _ Hwf Hf Hb
      (SsaLocalInstruction _ _ _ pc (IOp x o args) Hnth)); reflexivity. }
  assert (HsourceReach : reachable (ssa_point_graph P f)
    (Graph.source (ssa_point_graph P f) (SsaEdge l l pc))).
  { apply (dominated_edge_source_reachable _ _ _
      (view_point_reachable _ _ a Hview Hreachable) Hdom). }
  destruct (last_dominating_edge (activation ext P f) (ssa_point_view ext P f) a
    (SsaEdge l l pc) Hview Hreachable Hdom)
    as [u [tr [v [tail [Hu [Hstep [Htaken Htail]]]]]]].
  pose proof (ssa_operation_taken_at ext P f fd l b pc x o args u tr v
    Hwf Hf Hb Hnth Htaken) as Hat.
  destruct (ssa_operation_step_value ext P f u tr v x o args Hat Hstep)
    as [cs [value [Hread [Heval Hwritten]]]].
  assert (Hv : reachable_state (activation ext P f) v) by
    (eapply reachable_state_step; eassumption).
  pose proof (ssa_operation_operands_preserved ext P f fd R l b pc x o args a u tr v tail
    Hwf Hfunction Hf Hb Hcert Hnth Hsite Hsource HsourceReach Hdom Hv Hat Hstep Htail) as Hsame.
  exists cs, value; split.
  - apply read_args_sound; rewrite (ssa_read_equal_on (aenv a) (aenv u) args Hsame); exact Hread.
  - split; [|exact Heval].
    assert (Htail' : exec_in (activation ext P f)
      (fun s => point (ssa_point_view ext P f) s <> (l, pc)) v tail a).
    { change (exec_in (activation ext P f) (fun s => point (ssa_point_view ext P f) s <>
        Graph.source (ssa_point_graph P f) (SsaEdge l l pc)) v tail a) in Htail.
      rewrite Hsource in Htail; exact Htail. }
    rewrite (ssa_source_frame_away ext P f x (l, pc) (Some (IOp x o args)) v tail a
      Hwf Hfunction Hsite Hv Htail'); exact Hwritten.
Qed.

Local Lemma ssa_guard_subject_used t slot cd :
  In cd (ssa_guard t slot) -> In (subject cd) (term_uses t).
Proof.
  destruct t as [dst args|c l1 a1 l2 a2|c cases d da|callee args k|x];
    cbn [ssa_guard]; try contradiction.
  - destruct slot as [|[|slot]]; cbn; try contradiction.
    all: intros [Heq|Hfalse]; [subst cd; left; reflexivity|contradiction].
  - destruct (nth_error cases slot) as [[[key dst] args]|] eqn:Hnth.
    + intros [Heq|Hfalse]; [subst cd; left; reflexivity|contradiction].
    + intro Hin; apply in_map_iff in Hin; destruct Hin as [entry [Heq Hin]];
        subst cd; left; reflexivity.
Qed.

Local Lemma ssa_block_guard_operations ext P f a tr a' e :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_state (activation ext P f) a -> ssa_block_taken P f a tr a' e ->
  guard_ops_consistent (ssa_block_view ext P f) a e.
Proof.
  intros Hwf Hfunction Hreachable Htaken cd o args Hcd Hdef.
  destruct Htaken as [fd [b [Hf [Hb [Hpc [Hsrc [Hdst [Hzero [Hedge Hslot]]]]]]]]].
  destruct (ssa_block_edge_nth _ _ _ Hedge) as [_ [actual Hnth]].
  destruct e as [src dst slot]; cbn [esrc edst eslot] in *; subst src.
  change (In cd (sbp_guard (ssa_get ssa_edge_encoding (ssa_block_payloads P f)
    (SsaBlockPayload [] []) (SsaEdge (alabel a) dst slot)))) in Hcd.
  rewrite (ssa_block_payload_at ext P f fd (alabel a) b slot dst actual Hwf Hf Hb Hnth)
    in Hcd; cbn [sbp_guard] in Hcd.
  destruct (ssa_operation_location ext P f (subject cd) o args Hwf Hdef)
    as [fd' [l [operation_block [pc [Hf' [Hoperation HoperationNth]]]]]].
  rewrite Hf in Hf'; injection Hf' as Hfd; subst fd'.
  destruct (wf_function ext P f fd Hwf Hf) as [_ [_ [_ [R Hcert]]]].
  apply (ssa_operation_consistent ext P f fd R l operation_block pc (subject cd) o args a
    Hwf Hfunction Hf Hoperation Hcert HoperationNth Hreachable).
  change (In (subject cd) (ssa_available fd R (alabel a, apc a))).
  rewrite Hpc, (ssa_available_at fd R (alabel a) b (length (bbody b)) Hb).
  unfold available_at, prefix_defs; rewrite firstn_all.
  exact (proj1 (Forall_forall _ _)
    (proj1 (proj2 (certificate_block fd R (alabel a) b Hcert Hb))) (subject cd)
    (ssa_guard_subject_used (bterm b) slot cd Hcd)).
Qed.

(** This source-form alias retains the block view's four constructive origin alternatives. *)
Local Definition ssa_binding_origin ext P f a tr a' x c : Prop :=
  aenv a x = Some c \/
  (exists o args cs, def (ssa_block_view ext P f) x = Op o args /\
    Forall2 (fun y d => aenv a y = Some d) args cs /\ op_eval ext o cs = Some c) \/
  (exists e b i z, def (ssa_block_view ext P f) x = Param b i /\
    ssa_block_taken P f a tr a' e /\ edst e = b /\
    nth_error (edge_args (ssa_block_view ext P f) e) i = Some z /\ aenv a z = Some c) \/
  def (ssa_block_view ext P f) x = Arbitrary.

Local Lemma ssa_combine_nth {A B} (xs : list A) (ys : list B) i x y :
  nth_error xs i = Some x -> nth_error ys i = Some y -> In (x, y) (combine xs ys).
Proof.
  revert xs ys; induction i as [|i IH]; intros [|a xs] [|b ys] Hx Hy;
    cbn in Hx, Hy; try discriminate.
  - injection Hx as Hx; injection Hy as Hy; subst a b; left; reflexivity.
  - right; exact (IH xs ys Hx Hy).
Qed.

Local Lemma ssa_at_instruction_definition ext P f a i x definition :
  wf_program ext P -> at_instr P (activation_frame f a) i ->
  In (x, (alabel a, definition)) (ssa_instruction_rows (alabel a) i) ->
  def (ssa_block_view ext P f) x = definition.
Proof.
  intros Hwf [fd [b [Hf [Hb Hnth]]]] Hrow.
  exact (ssa_instruction_definition ext P f fd (alabel a) b (apc a) i x definition
    Hwf Hf Hb Hnth Hrow).
Qed.

Local Lemma ssa_transfer_value_origin ext P f a tr t dst args slot cs env x c :
  wf_program ext P -> at_term P (activation_frame f a) t ->
  nth_error (term_edges t) slot = Some (dst, args) ->
  ssa_term_slot (aenv a) t = Some slot -> read_args (aenv a) args = Some cs ->
  jump_env P (activation_frame f a) dst cs = Some env -> env x = Some c ->
  ssa_binding_origin ext P f a tr (activation_enter dst env) x c.
Proof.
  intros Hwf Hat Hedge Hslot Hread Hjump Hvalue.
  destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]].
  change (find_func P f = Some fd) in Hf.
  unfold jump_env in Hjump; cbn [activation_frame ffunc fenv] in Hjump; rewrite Hf in Hjump.
  destruct (find_block fd dst) as [target|] eqn:Htarget; [|discriminate].
  destruct (in_dec Nat.eq_dec x (map fst (bparams target))) as [Hparam|Houtside].
  - apply in_map_iff in Hparam; destruct Hparam as [[y ty] [Heq Hparam]];
      cbn in Heq; subst y.
    apply In_nth_error in Hparam; destruct Hparam as [i Hparam].
    pose proof (ssa_parameter_definition_at ext P f fd dst target i x ty
      Hwf Hf Htarget Hparam) as Hdefinition.
    destruct (FinSet.mem nat_encoding dst (ssa_call_targets P f)) eqn:Hcall.
    + right; right; right; exact Hdefinition.
    + assert (Hbound : i < length args).
      { pose proof (ssa_bind_length _ _ _ _ Hjump) as Hlength.
        pose proof (ssa_read_length _ _ _ Hread) as Hlength'.
        assert (i < length (bparams target)) by
          (apply nth_error_Some; rewrite Hparam; discriminate).
        lia. }
      destruct (nth_error args i) as [z|] eqn:Harg;
        [|apply nth_error_None in Harg; lia].
      right; right; left; exists (SsaEdge (alabel a) dst slot), dst, i, z.
      split; [exact Hdefinition|]; split.
      * eapply ssa_block_taken_intro with (t := t) (args := args);
          [exists fd, b; repeat split; assumption|reflexivity|reflexivity|exact Hedge|
           exact Hslot].
      * split; [reflexivity|]; split.
        -- change (nth_error (sbp_args (ssa_get ssa_edge_encoding (ssa_block_payloads P f)
            (SsaBlockPayload [] []) (SsaEdge (alabel a) dst slot))) i = Some z).
           rewrite (ssa_block_payload_at ext P f fd (alabel a) b slot dst args
             Hwf Hf Hb ltac:(rewrite Hterm; exact Hedge)); exact Harg.
        -- rewrite <- (ssa_bind_argument (aenv a) (aenv a) (bparams target) args cs env x z
             (ssa_parameter_nodup ext P f fd dst target Hwf Hf Htarget) Hjump Hread).
           ++ exact Hvalue.
           ++ apply (ssa_combine_nth (map fst (bparams target)) args i x z);
                [rewrite nth_error_map, Hparam; reflexivity|exact Harg].
  - left; rewrite <- (ssa_bind_frame _ _ _ _ x Hjump Houtside); exact Hvalue.
Qed.

Local Lemma ssa_arbitrary_value_origin ext P f a tr a' y value x c :
  def (ssa_block_view ext P f) y = Arbitrary ->
  env_set (aenv a) y value x = Some c -> ssa_binding_origin ext P f a tr a' x c.
Proof.
  intros Hdef Hvalue; unfold env_set in Hvalue; destruct (Nat.eq_dec x y) as [Heq|Hdifferent].
  - subst x; right; right; right; exact Hdef.
  - left; exact Hvalue.
Qed.

Local Lemma ssa_operation_value_origin ext P f a tr a' y o args cs value x c :
  wf_program ext P -> at_instr P (activation_frame f a) (IOp y o args) ->
  read_args (aenv a) args = Some cs -> op_eval ext o cs = Some value ->
  env_set (aenv a) y value x = Some c -> ssa_binding_origin ext P f a tr a' x c.
Proof.
  intros Hwf Hat Hread Heval Hvalue; unfold env_set in Hvalue.
  destruct (Nat.eq_dec x y) as [Heq|Hdifferent].
  - subst x; injection Hvalue as Hvalue; subst c.
    right; left; exists o, args, cs; split.
    + exact (ssa_at_instruction_definition ext P f a (IOp y o args) y (Op o args)
        Hwf Hat (or_introl eq_refl)).
    + split; [exact (read_args_sound _ _ _ Hread)|exact Heval].
  - left; exact Hvalue.
Qed.

Local Lemma ssa_call_value_origin ext P f a tr callee args k value env x c :
  wf_program ext P -> at_term P (activation_frame f a) (TCall callee args k) ->
  jump_env P (activation_frame f a) k [value] = Some env -> env x = Some c ->
  ssa_binding_origin ext P f a tr (activation_enter k env) x c.
Proof.
  intros Hwf [fd [b [Hf [Hb [Hpc Hterm]]]]] Hjump Hvalue.
  change (find_func P f = Some fd) in Hf.
  unfold jump_env in Hjump; cbn [activation_frame ffunc fenv] in Hjump; rewrite Hf in Hjump.
  destruct (find_block fd k) as [target|] eqn:Htarget; [|discriminate].
  destruct (in_dec Nat.eq_dec x (map fst (bparams target))) as [Hparam|Houtside].
  - apply in_map_iff in Hparam; destruct Hparam as [[y ty] [Heq Hparam]];
      cbn in Heq; subst y.
    apply In_nth_error in Hparam; destruct Hparam as [i Hparam].
    right; right; right.
    rewrite (ssa_parameter_definition_at ext P f fd k target i x ty Hwf Hf Htarget Hparam).
    assert (Hcall : FinSet.mem nat_encoding k (ssa_call_targets P f) = true).
    { apply FinSet.of_list_spec, in_flat_map; exists (alabel a, b); split.
      - unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
      - cbn [snd]; rewrite Hterm; left; reflexivity. }
    rewrite Hcall; reflexivity.
  - left; rewrite <- (ssa_bind_frame _ _ _ _ x Hjump Houtside); exact Hvalue.
Qed.

Local Lemma ssa_block_value_origin ext P f a tr a' x c :
  wf_program ext P -> step (activation ext P f) a tr a' -> aenv a' x = Some c ->
  ssa_binding_origin ext P f a tr a' x c.
Proof.
  intros Hwf Hstep Hvalue.
  destruct Hstep as
    [a y o args cs value Hat Hread Heval
    |a y n block offset Hat
    |a p Hat
    |a y ty sz p value Hat Htype Hvalid
    |a sz p y Hat
    |a y value Hat Houtput
    |a dst args cs env Hat Hread Hjump
    |a cond l1 a1 l2 a2 z dst args cs env Hat Hcond Hchoice Hread Hjump
    |a cond cases d da z dst args cs env Hat Hcond Hchoice Hread Hjump
    |a callee args k ps result cs value env Hat Hsig Hread Htype Hvalid Hjump
    |a y value Hat Hreturn].
  - exact (ssa_operation_value_origin ext P f a [] _ y o args cs value x c
      Hwf Hat Hread Heval Hvalue).
  - apply (ssa_arbitrary_value_origin ext P f a [] _ y (VPtr block offset) x c);
      [|exact Hvalue].
    exact (ssa_at_instruction_definition ext P f a (IAlloc y n) y Arbitrary
      Hwf Hat (or_introl eq_refl)).
  - left; exact Hvalue.
  - apply (ssa_arbitrary_value_origin ext P f a [] _ y value x c); [|exact Hvalue].
    exact (ssa_at_instruction_definition ext P f a (ILoad y ty sz p) y Arbitrary
      Hwf Hat (or_introl eq_refl)).
  - left; exact Hvalue.
  - left; exact Hvalue.
  - exact (ssa_transfer_value_origin ext P f a [] (TJump dst args) dst args 0 cs env x c
      Hwf Hat eq_refl eq_refl Hread Hjump Hvalue).
  - apply (ssa_transfer_value_origin ext P f a [] (TBr cond l1 a1 l2 a2) dst args
      (if Z.eqb z 0 then 1 else 0) cs env x c Hwf Hat); try assumption.
    + cbn [term_edges]; destruct (Z.eqb z 0); injection Hchoice as <- <-; reflexivity.
    + cbn [ssa_term_slot]; rewrite Hcond; reflexivity.
  - apply (ssa_transfer_value_origin ext P f a [] (TSwitch cond cases d da) dst args
      (ssa_switch_slot z cases) cs env x c Hwf Hat); try assumption.
    + rewrite <- Hchoice; exact (ssa_switch_slot_target z cases d da).
    + cbn [ssa_term_slot]; rewrite Hcond; reflexivity.
  - exact (ssa_call_value_origin ext P f a [] callee args k value env x c
      Hwf Hat Hjump Hvalue).
  - left; exact Hvalue.
Qed.

(** The block SSA adapter preserves guards and gives every present binding a constructive origin. *)
Theorem ssa_block_view_laws (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  ssa_view_laws (activation ext P f) (ssa_block_view ext P f).
Proof.
  intros Hwf Hfunction; constructor.
  - exact (ssa_block_graph_laws ext P f Hwf Hfunction).
  - intros x b i Hdef; exact (ssa_parameter_definition ext P f x b i Hwf Hdef).
  - intros a tr a' e Hreachable Hstep Htaken.
    exact (ssa_block_guards_ok ext P f a tr a' e Hwf Htaken).
  - intros a tr a' e Hreachable Hstep Htaken.
    exact (ssa_block_guard_operations ext P f a tr a' e Hwf Hfunction Hreachable Htaken).
  - intros a tr a' x c Hreachable Hstep Hvalue.
    exact (ssa_block_value_origin ext P f a tr a' x c Hwf Hstep Hvalue).
Qed.
