(** * SSA pointer origins and zero-byte observations

    Pointer effects include block bindings and external roots, and observations retain all frames.
    For example, a dangling pointer fragment stays tracked across allocation and partial writes.
    Builds on: ExamplesSsaMemory, ExamplesSsaEffects and AnalysesPointsTo. *)

From Stdlib Require Import List Bool ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemory ViewsCalls.
From Gaulois.Analyses Require Import AnalysesPointsTo.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaViews ExamplesSsaBridge ExamplesSsaEffects
  ExamplesSsaMemory.
Import List.ListNotations.
Local Open Scope nat_scope.

(** * Prepared static pointer effects *)

Definition ssa_allocations (P : program) : list vid :=
  flat_map (fun flb => flat_map (fun i => match i with
    | IAlloc x _ => [x]
    | _ => []
    end) (bbody (snd flb))) (full_program_blocks P).

Definition ssa_allocation_sites (P : program) : list vid :=
  FinSet.elements (FinSet.of_list nat_encoding (ssa_allocations P)).

Definition ssa_pointer_seeds (sites : list vid) (x : vid) : list (ptr_op vid vid) :=
  map (PAlloc x) sites.

Fixpoint ssa_pointer_copies (ps : list (vid * ty)) (args : list vid) :
    list (ptr_op vid vid) :=
  match ps, args with
  | (x, TyPtr) :: ps, y :: args => PCopy x y :: ssa_pointer_copies ps args
  | _ :: ps, _ :: args => ssa_pointer_copies ps args
  | _, _ => []
  end.

Definition ssa_pointer_instruction (signature : sop -> option (list ty * ty))
    (types : vid -> option ty) (sites : list vid) (i : instr) : list (ptr_op vid vid) :=
  match i with
  | IAlloc x _ => [PAlloc x x]
  | IOp x OPtrAdd (p :: _) => [PCopy x p]
  | IOp x (OConst (VPtr _ _)) _ => ssa_pointer_seeds sites x
  | IOp x (OExt tag) _ =>
    match signature (OExt tag) with
    | Some (_, TyPtr) => ssa_pointer_seeds sites x
    | _ => []
    end
  | ILoad x TyPtr _ p => [PLoad x p]
  | IStore _ p y =>
    match types y with
    | Some TyPtr => [PStore p y]
    | _ => []
    end
  | IOutput x =>
    match types x with
    | Some TyPtr => [PEscape x]
    | _ => []
    end
  | _ => []
  end.

Definition ssa_pointer_jump (blocks : label -> option ssa_block) (edge : label * list vid) :
    list (ptr_op vid vid) :=
  match blocks (fst edge) with
  | Some b => ssa_pointer_copies (bparams b) (snd edge)
  | None => []
  end.

Definition ssa_pointer_entry (functions : func -> option fdef)
    (block_index : func -> label -> option ssa_block) (f : func) : list (vid * ty) :=
  match functions f with
  | Some fd =>
    match block_index f (fentry fd) with
    | Some b => bparams b
    | None => []
    end
  | None => []
  end.

Definition ssa_pointer_call (entries : func -> list (vid * ty))
    (resolve : call_site -> list func) (types : vid -> option ty)
    (site : call_site) (c : callee) (args : list vid) : list (ptr_op vid vid) :=
  flat_map (fun f => ssa_pointer_copies (entries f) args) (resolve site) ++
  match c with
  | CDirect _ => []
  | CIndirect _ _ _ => flat_map (fun x => match types x with
    | Some TyPtr => [PEscape x]
    | _ => []
    end) args
  end.

(** Return destinations are indexed once by the callee they can receive a result from. *)
Definition ssa_pointer_return_rows (P : program) (resolve : call_site -> list func)
    (block_index : func -> label -> option ssa_block) : list (func * vid) :=
  flat_map (fun flb => match bterm (snd flb) with
    | TCall _ _ cont =>
      match block_index (fst (fst flb)) cont with
      | Some b => flat_map (fun f => flat_map (fun xt => match snd xt with
        | TyPtr => [(f, fst xt)]
        | _ => []
        end) (bparams b)) (resolve (fst (fst flb), snd (fst flb)))
      | None => []
      end
    | _ => []
    end) (full_program_blocks P).

Definition ssa_pointer_blocks (P : program) : func -> label -> option ssa_block :=
  let functions := first_index (funcs P) in
  let tables := Map.map (fun fd => first_index (blocks fd)) functions in
  fun f l => match Map.get nat_encoding f tables with
    | Some table => Map.get nat_encoding l table
    | None => None
    end.

Definition ssa_pointer_types (P : program) : func -> vid -> option ty :=
  let signature := op_sig P in
  let tables := Map.map (fun fd => first_index (function_bindings_with signature fd))
    (first_index (funcs P)) in
  fun f x => match Map.get nat_encoding f tables with
    | Some table => Map.get nat_encoding x table
    | None => None
    end.

Definition ssa_pointer_terminator (entries : func -> list (vid * ty))
    (resolve : call_site -> list func) (block_index : func -> label -> option ssa_block)
    (returns : func -> list vid) (types : vid -> option ty) (f : func) (l : label)
    (t : terminator) : list (ptr_op vid vid) :=
  match t with
  | TCall c args _ => ssa_pointer_call entries resolve types (f, l) c args
  | TRet x => map (fun y => PCopy y x) (returns f)
  | _ => flat_map (ssa_pointer_jump (block_index f)) (term_edges t)
  end.

Definition ssa_pointer_return_index (P : program) (resolve : call_site -> list func)
    (blocks : func -> label -> option ssa_block) : func -> list vid :=
  ssa_get nat_encoding
    (ssa_outgoing_index nat_encoding (fun f => f)
      (map (fun fx => (snd fx, fst fx))
        (ssa_pointer_return_rows P resolve blocks))) [].

Definition ssa_pointer_returns (P : program) : func -> list vid :=
  ssa_pointer_return_index P (ssa_resolver P) (ssa_pointer_blocks P).

(** The inventory preserves occurrences while sharing the resolver and lookup indexes. *)
Definition ssa_ptr_ops (P : program) : list (ptr_op vid vid) :=
  let signature := op_sig P in
  let sites := ssa_allocation_sites P in
  let blocks := ssa_pointer_blocks P in
  let types := ssa_pointer_types P in
  let resolve := ssa_resolver P in
  let entries := ssa_pointer_entry (find_func P) blocks in
  let returns := ssa_pointer_return_index P resolve blocks in
  flat_map (fun flb =>
    flat_map (ssa_pointer_instruction signature (types (fst (fst flb))) sites)
      (bbody (snd flb)) ++
    ssa_pointer_terminator entries resolve blocks returns (types (fst (fst flb)))
      (fst (fst flb)) (snd (fst flb)) (bterm (snd flb))) (full_program_blocks P) ++
  flat_map (fun xt => match snd xt with
    | TyPtr => ssa_pointer_seeds sites (fst xt)
    | _ => []
    end) (entries (main P)).

(** * Concrete and relational observations *)

Definition ssa_pointer_owners (P : program) : Map.t vid func :=
  first_index (flat_map (fun ffd =>
    map (fun xt => (fst xt, fst ffd)) (function_bindings P (snd ffd))) (funcs P)).

Fixpoint ssa_frame_value (f : func) (x : vid) (frames : list sframe) : option cval :=
  match frames with
  | [] => None
  | fr :: rest =>
    if Nat.eq_dec (ffunc fr) f then fenv fr x else ssa_frame_value f x rest
  end.

Definition ssa_pointer_value (owners : Map.t vid func) (s : state) (x : vid) : option cval :=
  match Map.get nat_encoding x owners with
  | Some f => ssa_frame_value f x (stack s)
  | None => None
  end.

Definition ssa_pointer_held (s : state) (c : cval) : option cval :=
  match c with
  | VPtr b off => match mem s b with
    | Some mb => memory_load TyPtr M8 mb off
    | None => None
    end
  | _ => None
  end.

Definition ssa_pointer_byte (s : state) (c : cval) : option nat :=
  match c with
  | VPtr b off => match mem s b with
    | Some mb =>
      if access_ok mb off M1 then match mbytes mb off with
        | MInt z => Some (Z.to_nat z)
        | _ => None
        end else None
    | None => None
    end
  | _ => None
  end.

Definition ssa_pointer_dynamic_term (P : program) (blocks : func -> label -> option ssa_block)
    (entries : func -> list (vid * ty)) (types : vid -> option ty)
    (fr : sframe) (rest : list sframe) (term : terminator) : list (ptr_op vid vid) :=
  match term with
  | TJump dst args => ssa_pointer_jump (blocks (ffunc fr)) (dst, args)
  | TBr c l1 a1 l2 a2 => match fenv fr c with
    | Some (VInt W32 z) =>
      ssa_pointer_jump (blocks (ffunc fr)) (if Z.eqb z 0 then (l2, a2) else (l1, a1))
    | _ => []
    end
  | TSwitch c cases d da => match fenv fr c with
    | Some (VInt W32 z) =>
      ssa_pointer_jump (blocks (ffunc fr)) (switch_target z cases d da)
    | _ => []
    end
  | TCall callee args _ => match callee_def P (fenv fr) callee with
    | Some (f, _, _) => ssa_pointer_copies (entries f) args ++
      match callee with
      | CDirect _ => []
      | CIndirect _ _ _ => flat_map (fun x => match types x with
        | Some TyPtr => [PEscape x]
        | _ => []
        end) args
      end
    | None => []
    end
  | TRet x => match rest with
    | caller :: _ => match blocks (ffunc caller) (fret caller) with
      | Some b => ssa_pointer_copies (bparams b) [x]
      | None => []
      end
    | [] => []
    end
  end.

(** Step effects use the involved frame's function and the prepared syntax inventory. *)
Definition ssa_pointer_pop (P : program) : state -> list (ptr_op vid vid) :=
  let signature := op_sig P in
  let sites := ssa_allocation_sites P in
  let blocks := ssa_pointer_blocks P in
  let types := ssa_pointer_types P in
  let entries := ssa_pointer_entry (find_func P) blocks in
  let current := ssa_current P in
  fun s => match stack s, current s with
    | fr :: _, Some (AnInstr i) =>
      ssa_pointer_instruction signature (types (ffunc fr)) sites i
    | fr :: rest, Some (ATerm t) =>
      ssa_pointer_dynamic_term P blocks entries (types (ffunc fr)) fr rest t
    | _, _ => []
    end.

(** Concrete values select the innermost activation of the value's defining function. *)
Definition ssa_ptr_view (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
    ptr_view state vid cval nat vid :=
  let owners := ssa_pointer_owners P in
  PtrView (ssa_mem_view ext P lim) (ssa_pointer_value owners) (ssa_pointer_pop P)
    ssa_pointer_held ssa_pointer_byte.

(** Unknown block numbers permit every program site; retained blocks use their historical site. *)
Definition ssa_raw_site (P : program) (s : state) (c : cval) (t : vid) : Prop :=
  In t (ssa_allocation_sites P) /\
  match c with
  | VPtr b _ => match mem s b with
    | Some mb => msite mb = t
    | None => True
    end
  | _ => False
  end.

(** Values include all active frames; heap facts include individual fragments of retained blocks. *)
Definition ssa_rel_ptr_view (P : program) : relational_ptr_view state vid vid :=
  RelationalPtrView
    (fun s x t => exists fr c, In fr (stack s) /\ fenv fr x = Some c /\ ssa_raw_site P s c t)
    (fun s t0 t => exists b mb off c i,
      mem s b = Some mb /\ msite mb = t0 /\ mbytes mb off = MFrag c i /\
      ssa_raw_site P s c t).

Definition ssa_pointer_writes (action : instr_or_term) : bool :=
  match action with
  | AnInstr (IAlloc _ _) | AnInstr (IStore _ _ _) | AnInstr (IFree _) |
      ATerm (TCall _ _ _) => true
  | _ => false
  end.

Definition ssa_pointer_action (P : program) : full_node -> instr_or_term :=
  let index := Map.map (fun fd => Map.map ssa_action_index (first_index (blocks fd)))
    (first_index (funcs P)) in
  fun n => match Map.get nat_encoding (fst (fst n)) index with
    | Some blocks => match Map.get nat_encoding (snd (fst n)) blocks with
      | Some code => ssa_get nat_encoding code (ATerm (TRet 0)) (snd n)
      | None => ATerm (TRet 0)
      end
    | None => ATerm (TRet 0)
    end.

(** Every possible write conservatively covers each allocated site's full address range. *)
Definition ssa_footprints (P : program) : full_edge -> list (footprint vid) :=
  let actions := ssa_pointer_action P in
  let ranges := map (fun site => Footprint site 0%Z (2 ^ 64)%Z) (ssa_allocation_sites P) in
  fun e => if ssa_pointer_writes (actions (fsrc e)) then ranges else [].

(** * Inventory agreement *)

Lemma ssa_pointer_types_agree P f x : ssa_pointer_types P f x = static_ty P f x.
Proof.
  unfold ssa_pointer_types; rewrite Map.get_map.
  change (Map.get nat_encoding f (first_index (funcs P))) with (find_func P f).
  unfold static_ty; destruct (find_func P f); reflexivity.
Qed.

Lemma ssa_pointer_blocks_agree P f fd l : find_func P f = Some fd ->
  ssa_pointer_blocks P f l = find_block fd l.
Proof.
  intro Hfunction; unfold ssa_pointer_blocks; rewrite Map.get_map.
  change (Map.get nat_encoding f (first_index (funcs P))) with (find_func P f).
  rewrite Hfunction; reflexivity.
Qed.

Lemma ssa_allocation_member P x :
  In x (ssa_allocation_sites P) <-> In x (ssa_allocations P).
Proof.
  unfold ssa_allocation_sites; rewrite (FinSet.elements_spec nat_encoding);
    [apply FinSet.of_list_spec|apply FinSet.wf_fold_add, Map.wf_empty].
Qed.

Lemma ssa_allocation_at P fr x n : at_instr P fr (IAlloc x n) ->
  In x (ssa_allocation_sites P).
Proof.
  intros [fd [b [Hfunction [Hblock Hnth]]]]; apply ssa_allocation_member.
  apply in_flat_map; exists (ffunc fr, flabel fr, b); split.
  - eapply full_block_member; eassumption.
  - apply in_flat_map; exists (IAlloc x n); split; [eapply nth_error_In; exact Hnth|].
    left; reflexivity.
Qed.

Lemma ssa_pointer_body_listed P fr i op : at_instr P fr i ->
  In op (ssa_pointer_instruction (op_sig P) (ssa_pointer_types P (ffunc fr))
    (ssa_allocation_sites P) i) -> In op (ssa_ptr_ops P).
Proof.
  intros [fd [b [Hfunction [Hblock Hnth]]]] Hop; unfold ssa_ptr_ops.
  apply in_or_app; left; apply in_flat_map; exists (ffunc fr, flabel fr, b); split.
  - eapply full_block_member; eassumption.
  - apply in_or_app; left; apply in_flat_map; exists i; split;
      [eapply nth_error_In; exact Hnth|exact Hop].
Qed.

Lemma ssa_pointer_term_listed P fr term op : at_term P fr term ->
  In op (ssa_pointer_terminator
    (ssa_pointer_entry (find_func P) (ssa_pointer_blocks P)) (ssa_resolver P)
    (ssa_pointer_blocks P) (ssa_pointer_returns P) (ssa_pointer_types P (ffunc fr))
    (ffunc fr) (flabel fr) term) -> In op (ssa_ptr_ops P).
Proof.
  intros [fd [b [Hfunction [Hblock [Hpc Hterm]]]]] Hop; unfold ssa_ptr_ops.
  apply in_or_app; left; apply in_flat_map; exists (ffunc fr, flabel fr, b); split.
  - eapply full_block_member; eassumption.
  - apply in_or_app; right; cbn [fst snd]; rewrite Hterm; exact Hop.
Qed.

Lemma ssa_pointer_entry_agree P f fd b :
  find_func P f = Some fd -> find_block fd (fentry fd) = Some b ->
  ssa_pointer_entry (find_func P) (ssa_pointer_blocks P) f = bparams b.
Proof.
  intros Hfunction Hblock; unfold ssa_pointer_entry; rewrite Hfunction.
  rewrite (ssa_pointer_blocks_agree P f fd _ Hfunction), Hblock; reflexivity.
Qed.

Lemma ssa_pointer_copy_parameter ps : forall args x y,
  In (PCopy x y) (ssa_pointer_copies ps args) ->
  In (x, TyPtr) ps /\ In y args.
Proof.
  induction ps as [|[p pt] ps IH]; intros args x y Hin.
  - destruct args; contradiction.
  - destruct args as [|a args]; [destruct pt; contradiction|].
    destruct pt; cbn [ssa_pointer_copies] in Hin.
    all: try solve [destruct (IH _ _ _ Hin) as [Hparam Harg]; split; now right].
    destruct Hin as [Heq|Hin].
    + injection Heq as <- <-; split; now left.
    + destruct (IH _ _ _ Hin) as [Hparam Harg]; split; now right.
Qed.

Lemma ssa_pointer_copies_only ps : forall args op,
  In op (ssa_pointer_copies ps args) -> exists x y, op = PCopy x y.
Proof.
  induction ps as [|[p pt] ps IH]; intros args op Hin.
  - destruct args; contradiction.
  - destruct args as [|a args]; [destruct pt; contradiction|].
    destruct pt; cbn [ssa_pointer_copies] in Hin;
      try solve [eapply IH; exact Hin].
    destruct Hin as [<-|Hin]; [eauto|eapply IH; exact Hin].
Qed.

Lemma ssa_pointer_main_seed P fd b x t :
  find_func P (main P) = Some fd -> find_block fd (fentry fd) = Some b ->
  In (x, TyPtr) (bparams b) -> In t (ssa_allocation_sites P) ->
  In (PAlloc x t) (ssa_ptr_ops P).
Proof.
  intros Hfunction Hblock Hparam Hsite; unfold ssa_ptr_ops; apply in_or_app; right.
  rewrite (ssa_pointer_entry_agree P _ fd b Hfunction Hblock).
  apply in_flat_map; exists (x, TyPtr); split; [exact Hparam|].
  apply in_map; exact Hsite.
Qed.

Lemma ssa_bind_pointer_origin envread ps : forall env0 args cs env' x c,
  read_args envread args = Some cs -> map ty_of cs = map snd ps ->
  bind_params env0 ps cs = Some env' -> ty_of c = TyPtr -> env' x = Some c ->
  env0 x = Some c \/ exists y,
    In (PCopy x y) (ssa_pointer_copies ps args) /\ envread y = Some c.
Proof.
  induction ps as [|[p pt] ps IH]; intros env0 args cs env' x c Hread Htypes Hbind Hptr Hvalue.
  - destruct cs; [|discriminate]; cbn [bind_params] in Hbind.
    injection Hbind as <-; now left.
  - destruct cs as [|v vs]; [discriminate|].
    destruct args as [|a args]; [discriminate|].
    cbn [read_args] in Hread; destruct (envread a) as [av|] eqn:Harg; [|discriminate].
    destruct (read_args envread args) as [values|] eqn:Hrest; [|discriminate].
    injection Hread as <- <-; cbn [map] in Htypes; injection Htypes as Htype Htypes.
    cbn [bind_params] in Hbind.
    destruct (IH (env_set env0 p av) args values env' x c
      Hrest Htypes Hbind Hptr Hvalue) as [Hold|[y [Hcopy Hy]]].
    + unfold env_set in Hold; destruct (Nat.eq_dec x p) as [->|Hne].
      * injection Hold as <-; rewrite Hptr in Htype; subst pt.
        right; exists a; split; [left; reflexivity|exact Harg].
      * now left.
    + right; exists y; split; [|exact Hy].
      destruct pt; cbn [ssa_pointer_copies]; try exact Hcopy; right; exact Hcopy.
Qed.

Lemma ssa_bind_parameter_origin ps : forall env0 vs env' x c,
  map ty_of vs = map snd ps -> bind_params env0 ps vs = Some env' ->
  ty_of c = TyPtr -> env' x = Some c ->
  env0 x = Some c \/ In (x, TyPtr) ps.
Proof.
  induction ps as [|[p pt] ps IH]; intros env0 [|v vs] env' x c Htypes Hbind Hptr Hvalue;
    cbn [map bind_params] in *; try discriminate.
  - injection Hbind as <-; now left.
  - injection Htypes as Htype Htypes.
    destruct (IH (env_set env0 p v) vs env' x c Htypes Hbind Hptr Hvalue)
      as [Hold|Hparam]; [|right; now right].
    unfold env_set in Hold; destruct (Nat.eq_dec x p) as [->|Hne]; [|now left].
    injection Hold as <-; rewrite Hptr in Htype; subst pt; right; now left.
Qed.

(** * Historical blocks and individual fragments *)

Definition ssa_pointer_memory (P : program) (s : state) : Prop :=
  forall b mb, mem s b = Some mb ->
    In (msite mb) (ssa_allocation_sites P) /\ (Z.of_nat (msz mb) < 2 ^ 64)%Z.

Lemma ssa_pointer_memory_step ext P lim s tr s' :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  ssa_pointer_memory P s -> step_s ext P lim s tr s' -> ssa_pointer_memory P s'.
Proof.
  intros Hwf Hreach Hmemory Hstep; destruct Hstep;
    unfold ssa_pointer_memory in *; cbn [mem] in *; try exact Hmemory.
  - intros a block Hget; unfold memory_set in Hget.
    destruct (Nat.eq_dec a nb) as [->|Hne]; [|eapply Hmemory; exact Hget].
    injection Hget as <-; cbn [msite msz]; split; [eapply ssa_allocation_at; eassumption|].
    assert (Htyped : typed_env P (ffunc fr) (fenv fr)).
    { eapply typed_state_reachable; [exact Hwf|exact Hreach|now left]. }
    match goal with Hvalue : fenv fr n = Some (VInt W64 z) |- _ =>
      destruct (Htyped n _ Hvalue) as [_ Hz] end.
    cbn [valid_cval] in Hz; rewrite Z2Nat.id by lia; lia.
  - intros a block Hget; unfold memory_set in Hget.
    destruct (Nat.eq_dec a b) as [->|Hne]; [|eapply Hmemory; exact Hget].
    injection Hget as <-; cbn [msite msz]; eapply Hmemory; eassumption.
  - intros a block Hget; unfold memory_set in Hget.
    destruct (Nat.eq_dec a b) as [->|Hne]; [|eapply Hmemory; exact Hget].
    injection Hget as <-.
    match goal with Hstore : memory_store sz mb off v = Some mb' |- _ =>
      unfold memory_store in Hstore; destruct (access_ok mb off sz && store_shape sz v);
      [injection Hstore as <-|discriminate] end.
    cbn [msite msz]; eapply Hmemory; eassumption.
Qed.

Lemma ssa_pointer_memory_reachable ext P lim s :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s -> ssa_pointer_memory P s.
Proof.
  intros Hwf [s0 [tr [Hinitial Hrun]]].
  assert (Hmemory : ssa_pointer_memory P s0).
  { destruct Hinitial as [fd [b [vs [env [_ [_ [_ [_ [_ ->]]]]]]]]].
    intros a mb Hget; discriminate. }
  assert (Hstart : reachable_state (ssa_semantics ext P lim) s0).
  { exists s0, []; split; [exact Hinitial|constructor]. }
  clear Hinitial; revert Hstart Hmemory.
  induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intros Hreach Hmemory.
  - exact Hmemory.
  - apply IH; [eapply reachable_state_step; eassumption|].
    eapply ssa_pointer_memory_step; eassumption.
Qed.

(** Speculation can only narrow when a previously absent identity is allocated. *)
Lemma ssa_raw_site_back ext P lim s tr s' c t :
  reachable_state (ssa_semantics ext P lim) s -> step_s ext P lim s tr s' ->
  ssa_raw_site P s' c t -> ssa_raw_site P s c t.
Proof.
  intros Hreach Hstep [Hsite Hraw]; split; [exact Hsite|].
  destruct c; try contradiction.
  destruct (mem s b) as [mb|] eqn:Hbefore; [|exact I].
  assert (Hstable : option_map msite (mem s' b) = Some (msite mb)).
  { eapply full_site_step; [eapply full_memory_fresh_reachable; exact Hreach|
      exact Hstep|rewrite Hbefore; reflexivity]. }
  destruct (mem s' b) as [mb'|]; [cbn in Hstable; congruence|discriminate].
Qed.

Lemma ssa_raw_site_offset P s b off off' t :
  ssa_raw_site P s (VPtr b off) t -> ssa_raw_site P s (VPtr b off') t.
Proof.
  exact (fun H => H).
Qed.

Lemma ssa_pointer_load_fragment ty sz mb off b offset :
  memory_load ty sz mb off = Some (VPtr b offset) ->
  ty = TyPtr /\ sz = M8 /\ mbytes mb off = MFrag (VPtr b offset) 0.
Proof.
  unfold memory_load; destruct (access_ok mb off sz); [|discriminate].
  destruct ty, sz; try discriminate;
    try (destruct (integer_bytes _ _ _); discriminate).
  destruct (mbytes mb off) as [z|c i] eqn:Hbyte; [discriminate|].
  destruct c; try discriminate; destruct i; [|discriminate].
  destruct (fragments_ok _ _ _ _ _); [|discriminate].
  intro Heq; injection Heq as <- <-; auto.
Qed.

(** A write either retains an individual fragment or writes a fragment of its source value. *)
Lemma ssa_pointer_store_fragment sz mb off v mb' k c i :
  memory_store sz mb off v = Some mb' -> mbytes mb' k = MFrag c i ->
  mbytes mb k = MFrag c i \/ c = v.
Proof.
  unfold memory_store; destruct (access_ok mb off sz && store_shape sz v);
    [|discriminate].
  intro Heq; injection Heq as <-; cbn [mbytes].
  destruct ((off <=? k) && (k <? off + Z.of_nat (size_bytes sz)))%Z;
    [|now left].
  destruct v; cbn [value_byte]; try discriminate;
    intro Heq; injection Heq; intros; subst; right; reflexivity.
Qed.

Lemma ssa_raw_site_pointer P s c t : ssa_raw_site P s c t ->
  exists b off, c = VPtr b off.
Proof.
  intros [_ Hraw]; destruct c; try contradiction; eauto.
Qed.

Lemma ssa_rel_value_frame P s fr x c t :
  In fr (stack s) -> fenv fr x = Some c -> ssa_raw_site P s c t ->
  rel_value (ssa_rel_ptr_view P) s x t.
Proof.
  intros Hframe Hvalue Hraw; exists fr, c; auto.
Qed.

(** The heap origin proof tracks each fragment, including ones no complete load can reconstruct. *)
Lemma ssa_rel_heap_step ext P lim s tr s' t0 t :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  step_s ext P lim s tr s' -> rel_heap (ssa_rel_ptr_view P) s' t0 t ->
  rel_heap (ssa_rel_ptr_view P) s t0 t \/
  exists p y, In (PStore p y) (ssa_ptr_ops P) /\
    rel_value (ssa_rel_ptr_view P) s p t0 /\ rel_value (ssa_rel_ptr_view P) s y t.
Proof.
  intros Hwf Hreach Hstep [a [block [k [c [i [Hget [Hsite [Hfragment Hraw]]]]]]]].
  pose proof (ssa_raw_site_back ext P lim s tr s' c t Hreach Hstep Hraw) as Hbefore.
  pose proof (ssa_pointer_memory_reachable ext P lim s Hwf Hreach) as Hmemory.
  destruct Hstep as
    [fr rest m nb x o args cs v Hat Hread Heval
    |fr rest m nb x n z Hat Hvalue Hlimit
    |fr rest m nb p b mb Hat Hvalue Hblock Hlive
    |fr rest m nb x ty sz p b off mb v Hat Hvalue Hblock Hload
    |fr rest m nb sz p y b off mb v mb' Hat Hpointer Hvalue Hblock Hstore
    |fr rest m nb x v Hat Hvalue
    |fr rest m nb l args cs env Hat Hread Hjump
    |fr rest m nb cond l1 a1 l2 a2 z l args cs env Hat Hvalue Hselect Hread Hjump
    |fr rest m nb cond cases d da z l args cs env Hat Hvalue Hselect Hread Hjump
    |fr rest m nb callee args cont cs f fd entry env Hat Hread Hcallee Hbind Hlimit
    |fr caller rest m nb x v env Hat Hvalue Hjump
    |fr m nb x v Hat Hvalue]; cbn [mem] in Hget.
  all: try solve [left; exists a, block, k, c, i; repeat first [assumption|split]].
  - unfold memory_set in Hget; destruct (Nat.eq_dec a nb) as [->|Hne].
    + injection Hget as <-; discriminate.
    + left; exists a, block, k, c, i; repeat first [assumption|split].
  - unfold memory_set in Hget; destruct (Nat.eq_dec a b) as [->|Hne].
    + injection Hget as <-; left; exists b, mb, k, c, i; repeat first [assumption|split].
    + left; exists a, block, k, c, i; repeat first [assumption|split].
  - unfold memory_set in Hget; destruct (Nat.eq_dec a b) as [->|Hne].
    + injection Hget as <-.
      pose proof (full_store_site sz mb off v mb' Hstore) as Hsame.
      rewrite Hsame in Hsite.
      destruct (ssa_pointer_store_fragment sz mb off v mb' k c i Hstore Hfragment)
        as [Hold | Hsource].
      * left; exists b, mb, k, c, i; repeat first [assumption|split].
      * subst c; destruct (ssa_raw_site_pointer P _ _ _ Hbefore) as [vb [vo ->]].
        assert (Htype : static_ty P (ffunc fr) y = Some TyPtr).
        { exact (proj1 (typed_state_reachable ext P lim _ Hwf Hreach fr
            (or_introl eq_refl) y _ Hvalue)). }
        right; exists p, y; split.
        -- eapply ssa_pointer_body_listed; [exact Hat|].
           cbn [ssa_pointer_instruction]; rewrite ssa_pointer_types_agree, Htype; now left.
        -- split.
           ++ eapply ssa_rel_value_frame; [now left|exact Hpointer|].
              split; [rewrite <- Hsite; exact (proj1 (Hmemory b mb Hblock))|].
              cbn [mem]; rewrite Hblock; exact Hsite.
           ++ eapply ssa_rel_value_frame; [now left|exact Hvalue|exact Hbefore].
    + left; exists a, block, k, c, i; repeat first [assumption|split].
Qed.

(** This predicate states the four independent static origins for one value observation. *)
Definition ssa_pointer_origin (P : program) (s : state) (x t : vid) : Prop :=
  rel_value (ssa_rel_ptr_view P) s x t \/ In (PAlloc x t) (ssa_ptr_ops P) \/
  (exists y, In (PCopy x y) (ssa_ptr_ops P) /\ rel_value (ssa_rel_ptr_view P) s y t) \/
  (exists p t0, In (PLoad x p) (ssa_ptr_ops P) /\
    rel_value (ssa_rel_ptr_view P) s p t0 /\ rel_heap (ssa_rel_ptr_view P) s t0 t).

Lemma ssa_pointer_old P s fr x c t :
  In fr (stack s) -> fenv fr x = Some c -> ssa_raw_site P s c t ->
  ssa_pointer_origin P s x t.
Proof.
  intros Hframe Hvalue Hraw; left; eapply ssa_rel_value_frame; eassumption.
Qed.

Lemma ssa_pointer_copied P s fr x y c t :
  In (PCopy x y) (ssa_ptr_ops P) -> In fr (stack s) ->
  fenv fr y = Some c -> ssa_raw_site P s c t -> ssa_pointer_origin P s x t.
Proof.
  intros Hcopy Hframe Hvalue Hraw; right; right; left; exists y; split; [exact Hcopy|].
  eapply ssa_rel_value_frame; eassumption.
Qed.

Lemma ssa_operation_pointer_signature ext P lim fr rest m nb x o args cs v :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  at_instr P fr (IOp x o args) -> read_args (fenv fr) args = Some cs ->
  op_eval ext o cs = Some v -> ty_of v = TyPtr ->
  exists ps, op_sig P o = Some (ps, TyPtr).
Proof.
  intros Hwf Hreach Hat Hread Heval Hptr.
  pose proof (wf_instruction ext P fr _ Hwf Hat) as Hlocal.
  unfold instr_typed, instr_sig, instr_sig_with in Hlocal; cbn beta iota zeta in Hlocal.
  destruct (op_sig P o) as [[ps r]|] eqn:Hsig; [|contradiction].
  destruct Hlocal as [Htypes Hresult].
  pose proof (typed_state_reachable ext P lim _ Hwf Hreach fr (or_introl eq_refl)) as Htyped.
  destruct (read_args_typed P _ _ _ _ _ Htyped Hread Htypes) as [Hmap Hvalid].
  destruct Hwf as [_ [_ [_ [_ Hext]]]].
  pose proof (proj1 (op_eval_typed ext P o cs ps r Hext Hsig Hmap Hvalid) v Heval) as Hr.
  rewrite Hptr in Hr; subst r; exists ps; reflexivity.
Qed.

Lemma ssa_pointer_operation_origin ext P lim fr rest m nb x o args cs v t :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  at_instr P fr (IOp x o args) -> read_args (fenv fr) args = Some cs ->
  op_eval ext o cs = Some v -> ssa_raw_site P (State (fr :: rest) m nb) v t ->
  ssa_pointer_origin P (State (fr :: rest) m nb) x t.
Proof.
  intros Hwf Hreach Hat Hread Heval Hraw.
  destruct (ssa_raw_site_pointer P _ _ _ Hraw) as [b [off ->]].
  destruct (ssa_operation_pointer_signature ext P lim fr rest m nb x o args cs _
    Hwf Hreach Hat Hread Heval eq_refl) as [ps Hsig].
  destruct o as [constant|w bin| | | |tag].
  - destruct constant; cbn [op_sig ty_of] in Hsig;
      try discriminate; try solve [destruct w; discriminate].
    right; left; eapply ssa_pointer_body_listed; [exact Hat|].
    cbn [ssa_pointer_instruction]; apply in_map; exact (proj1 Hraw).
  - destruct w, bin; discriminate.
  - discriminate.
  - discriminate.
  - pose proof (wf_instruction ext P fr _ Hwf Hat) as Hlocal.
    change (types_of (static_ty P (ffunc fr)) args = Some [TyPtr; TyI64] /\
      static_ty P (ffunc fr) x = Some TyPtr) in Hlocal.
    pose proof (typed_state_reachable ext P lim _ Hwf Hreach fr (or_introl eq_refl)) as Htyped.
    destruct (read_args_typed P _ _ _ _ _ Htyped Hread (proj1 Hlocal)) as [Htypes Hvalid].
    destruct (typed_pointer_pair cs Htypes) as [pb [po [k Hcs]]]; subst cs.
    cbn [op_eval] in Heval; injection Heval as <- <-.
    destruct args as [|p args]; [discriminate|].
    cbn [read_args] in Hread; destruct (fenv fr p) as [value|] eqn:Hp; [|discriminate].
    destruct (read_args (fenv fr) args) as [values|]; [|discriminate].
    injection Hread as Hvalue Hvalues; subst value.
    eapply ssa_pointer_copied; [|now left|exact Hp|].
    + eapply ssa_pointer_body_listed; [exact Hat|left; reflexivity].
    + eapply ssa_raw_site_offset; exact Hraw.
  - right; left; eapply ssa_pointer_body_listed; [exact Hat|].
    cbn [ssa_pointer_instruction]; rewrite Hsig; apply in_map; exact (proj1 Hraw).
Qed.

Lemma ssa_pointer_load_origin ext P lim fr rest m nb x ty sz p b off mb v t :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  at_instr P fr (ILoad x ty sz p) -> fenv fr p = Some (VPtr b off) ->
  m b = Some mb -> memory_load ty sz mb off = Some v ->
  ssa_raw_site P (State (fr :: rest) m nb) v t ->
  ssa_pointer_origin P (State (fr :: rest) m nb) x t.
Proof.
  intros Hwf Hreach Hat Hp Hblock Hload Hraw.
  destruct (ssa_raw_site_pointer P _ _ _ Hraw) as [vb [vo ->]].
  destruct (ssa_pointer_load_fragment ty sz mb off vb vo Hload) as [-> [-> Hfragment]].
  right; right; right; exists p, (msite mb); split.
  - eapply ssa_pointer_body_listed; [exact Hat|now left].
  - split.
    + eapply ssa_rel_value_frame; [now left|exact Hp|].
      split; [|cbn [mem]; rewrite Hblock; reflexivity].
      exact (proj1 (ssa_pointer_memory_reachable ext P lim _ Hwf Hreach b mb Hblock)).
    + exists b, mb, off, (VPtr vb vo), 0; repeat first [assumption|split].
Qed.

Lemma ssa_pointer_jump_listed P fr term dst args fd b op :
  at_term P fr term -> (forall c xs cont, term <> TCall c xs cont) ->
  (forall x, term <> TRet x) -> In (dst, args) (term_edges term) ->
  find_func P (ffunc fr) = Some fd -> find_block fd dst = Some b ->
  In op (ssa_pointer_copies (bparams b) args) -> In op (ssa_ptr_ops P).
Proof.
  intros Hat Hcall Hreturn Hedge Hfunction Hblock Hop.
  eapply ssa_pointer_term_listed; [exact Hat|].
  destruct term; try solve [exfalso; eapply Hcall; reflexivity];
    try solve [exfalso; eapply Hreturn; reflexivity];
    cbn [ssa_pointer_terminator]; apply in_flat_map; exists (dst, args); split;
    [exact Hedge| |exact Hedge| |exact Hedge|];
    unfold ssa_pointer_jump; cbn [fst snd];
    rewrite (ssa_pointer_blocks_agree P _ fd _ Hfunction), Hblock; exact Hop.
Qed.

Lemma ssa_pointer_jump_origin ext P lim fr rest m nb term dst args cs env x c t :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  at_term P fr term -> (forall callee xs cont, term <> TCall callee xs cont) ->
  (forall y, term <> TRet y) -> In (dst, args) (term_edges term) ->
  read_args (fenv fr) args = Some cs -> jump_env P fr dst cs = Some env ->
  env x = Some c -> ssa_raw_site P (State (fr :: rest) m nb) c t ->
  ssa_pointer_origin P (State (fr :: rest) m nb) x t.
Proof.
  intros Hwf Hreach Hat Hcall Hreturn Hedge Hread Hjump Hvalue Hraw.
  destruct (wf_terminator ext P fr term Hwf Hat) as [fd [Hfunction Htyped]].
  assert (Htypededge : typed_jump (find_block fd) (static_ty P (ffunc fr)) (dst, args)).
  { destruct term; try solve [exfalso; eapply Hcall; reflexivity];
      try solve [exfalso; eapply Hreturn; reflexivity]; cbn [term_typed] in Htyped.
    - exact (proj1 (Forall_forall _ _) Htyped _ Hedge).
    - exact (proj1 (Forall_forall _ _) (proj2 Htyped) _ Hedge).
    - exact (proj1 (Forall_forall _ _) (proj2 Htyped) _ Hedge). }
  unfold typed_jump in Htypededge; cbn [fst snd] in Htypededge.
  destruct (find_block fd dst) as [b|] eqn:Hblock; [|contradiction].
  pose proof (typed_state_reachable ext P lim _ Hwf Hreach fr (or_introl eq_refl)) as Henv.
  destruct (read_args_typed P _ _ _ _ _ Henv Hread Htypededge) as [Htypes Hvalid].
  unfold jump_env in Hjump; rewrite Hfunction, Hblock in Hjump.
  destruct (ssa_raw_site_pointer P _ _ _ Hraw) as [vb [vo Heq]].
  assert (Hptr : ty_of c = TyPtr) by (rewrite Heq; reflexivity).
  destruct (ssa_bind_pointer_origin (fenv fr) (bparams b) (fenv fr) args cs env x c
    Hread Htypes Hjump Hptr Hvalue) as [Hold|[y [Hcopy Hy]]].
  - eapply ssa_pointer_old; [now left|exact Hold|exact Hraw].
  - eapply ssa_pointer_copied; [|now left|exact Hy|exact Hraw].
    eapply ssa_pointer_jump_listed; eassumption.
Qed.

Lemma ssa_pointer_call_origin ext P lim fr rest m nb callee args cont cs f fd b env x c t :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  at_term P fr (TCall callee args cont) -> read_args (fenv fr) args = Some cs ->
  callee_def P (fenv fr) callee = Some (f, fd, b) ->
  bind_params (fun _ => None) (bparams b) cs = Some env -> env x = Some c ->
  ssa_raw_site P (State (fr :: rest) m nb) c t ->
  ssa_pointer_origin P (State (fr :: rest) m nb) x t.
Proof.
  intros Hwf Hreach Hat Hread Hcallee Hbind Hvalue Hraw.
  destruct (call_typed ext P fr callee args cont Hwf Hat) as
    [callerfd [ps [r [continuation [Hcaller [Hsig [Hcont [Hargs Hparams]]]]]]]].
  destruct (callee_def_target P (fenv fr) callee f fd b Hcallee)
    as [Hfunction [Hblock Hmatches]].
  destruct (Hmatches _ _ _ Hsig) as [Hps Hr].
  pose proof (typed_state_reachable ext P lim _ Hwf Hreach fr (or_introl eq_refl)) as Htyped.
  destruct (read_args_typed P _ _ _ _ _ Htyped Hread Hargs) as [Htypes Hvalid].
  rewrite Hps in Htypes.
  destruct (ssa_raw_site_pointer P _ _ _ Hraw) as [vb [vo Heq]].
  assert (Hptr : ty_of c = TyPtr) by (rewrite Heq; reflexivity).
  destruct (ssa_bind_pointer_origin (fenv fr) (bparams b) (fun _ => None) args cs env x c
    Hread Htypes Hbind Hptr Hvalue) as [Hnone|[y [Hcopy Hy]]]; [discriminate|].
  eapply ssa_pointer_copied; [|now left|exact Hy|exact Hraw].
  eapply ssa_pointer_term_listed; [exact Hat|].
  cbn [ssa_pointer_terminator ssa_pointer_call]; apply in_or_app; left.
  apply in_flat_map; exists f; split; [eapply ssa_call_resolved; eassumption|].
  rewrite (ssa_pointer_entry_agree P f fd b Hfunction Hblock); exact Hcopy.
Qed.

Lemma ssa_pointer_return_destination P caller callee args cont f fd b x :
  at_term P caller (TCall callee args cont) -> fret caller = cont ->
  In f (ssa_resolver P (ffunc caller, flabel caller)) ->
  find_func P (ffunc caller) = Some fd -> find_block fd cont = Some b ->
  In (x, TyPtr) (bparams b) -> In x (ssa_pointer_returns P f).
Proof.
  intros Hat Hcont Hresolve Hfunction Hblock Hparam.
  unfold ssa_pointer_returns, ssa_pointer_return_index; apply ssa_outgoing_member.
  exists f; split; [|reflexivity].
  apply in_map_iff; exists (f, x); split; [reflexivity|].
  unfold ssa_pointer_return_rows; apply in_flat_map.
  destruct Hat as [source [block [Hsource [Hcurrent [Hpc Hterm]]]]].
  exists (ffunc caller, flabel caller, block); split.
  - exact (full_block_member P _ source _ block Hsource Hcurrent).
  - cbn [fst snd]; rewrite Hterm,
      (ssa_pointer_blocks_agree P _ fd _ Hfunction), Hblock.
    apply in_flat_map; exists f; split; [exact Hresolve|].
    apply in_flat_map; exists (x, TyPtr); split; [exact Hparam|now left].
Qed.

Lemma ssa_pointer_return_origin ext P lim fr caller rest m nb value v env x c t :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: caller :: rest) m nb) ->
  at_term P fr (TRet value) -> fenv fr value = Some v ->
  jump_env P caller (fret caller) [v] = Some env -> env x = Some c ->
  ssa_raw_site P (State (fr :: caller :: rest) m nb) c t ->
  ssa_pointer_origin P (State (fr :: caller :: rest) m nb) x t.
Proof.
  intros Hwf Hreach Hat Hvalue Hjump Hlookup Hraw.
  destruct (reachable_good ext P lim _ Hwf Hreach) as [Hgood Hlinks].
  cbn [stack stack_links] in Hlinks.
  destruct (proj1 Hlinks) as [childfd [callee [args [cont [ps
    [Hchild [Hcall [Hret Hsignature]]]]]]]].
  destruct (wf_terminator ext P fr _ Hwf Hat) as [fd [Hfunction Htyped]].
  rewrite Hchild in Hfunction; injection Hfunction as <-.
  cbn [term_typed] in Htyped.
  pose proof (typed_state_reachable ext P lim _ Hwf Hreach fr (or_introl eq_refl)) as Henv.
  pose proof (proj1 (Henv value v Hvalue)) as Hvtype.
  rewrite Hvtype in Htyped; injection Htyped as Htype.
  destruct (call_typed ext P caller callee args cont Hwf Hcall) as
    [callerfd [ps' [r [b [Hcaller [Hsignature' [Hblock [Hargs Hparams]]]]]]]].
  rewrite Hsignature in Hsignature'; injection Hsignature' as <- <-.
  assert (Htypes : map ty_of [v] = map snd (bparams b)).
  { cbn [map]; rewrite Hparams, Htype; reflexivity. }
  unfold jump_env in Hjump; rewrite Hcaller, Hret, Hblock in Hjump.
  assert (Hread : read_args (fenv fr) [value] = Some [v]).
  { cbn [read_args]; rewrite Hvalue; reflexivity. }
  destruct (ssa_raw_site_pointer P _ _ _ Hraw) as [vb [vo Heq]].
  assert (Hptr : ty_of c = TyPtr) by (rewrite Heq; reflexivity).
  destruct (ssa_bind_pointer_origin (fenv fr) (bparams b) (fenv caller) [value] [v]
    env x c Hread Htypes Hjump Hptr Hlookup) as [Hold|[y [Hcopy Hy]]].
  - eapply ssa_pointer_old; [right; now left|exact Hold|exact Hraw].
  - destruct (ssa_pointer_copy_parameter (bparams b) [value] x y Hcopy)
      as [Hparameter Harg].
    destruct Harg as [Heqy|[]]; subst y.
    assert (Hresolved : In (ffunc fr) (ssa_resolver P (ffunc caller, flabel caller))).
    { pose proof (ssa_frame_chain ext P lim _ Hwf Hreach) as Hchain.
      cbn [ssa_calls here frames ssa_suspended stack tl map frames_linked] in Hchain.
      exact (proj1 (proj2 (proj2 Hchain))). }
    assert (Hdestination : In x (ssa_pointer_returns P (ffunc fr))).
    { eapply ssa_pointer_return_destination; eassumption. }
    eapply ssa_pointer_copied; [|now left|exact Hy|exact Hraw].
    eapply ssa_pointer_term_listed; [exact Hat|].
    cbn [ssa_pointer_terminator]; apply in_map_iff; exists x; auto.
Qed.

(** All active frames contribute origins, including callers suspended below recursive callees. *)
Lemma ssa_rel_value_step ext P lim s tr s' x t :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  step_s ext P lim s tr s' -> rel_value (ssa_rel_ptr_view P) s' x t ->
  ssa_pointer_origin P s x t.
Proof.
  intros Hwf Hreach Hstep [observed [c [Hframe [Hlookup Hraw]]]].
  pose proof (ssa_raw_site_back ext P lim s tr s' c t Hreach Hstep Hraw) as Hbefore.
  destruct Hstep as
    [fr rest m nb dst o args cs v Hat Hread Heval
    |fr rest m nb dst n z Hat Hvalue Hlimit
    |fr rest m nb p b mb Hat Hvalue Hblock Hlive
    |fr rest m nb dst ty sz p b off mb v Hat Hvalue Hblock Hload
    |fr rest m nb sz p y b off mb v mb' Hat Hpointer Hvalue Hblock Hstore
    |fr rest m nb y v Hat Hvalue
    |fr rest m nb l args cs env Hat Hread Hjump
    |fr rest m nb cond l1 a1 l2 a2 z l args cs env Hat Hvalue Hselect Hread Hjump
    |fr rest m nb cond cases d da z l args cs env Hat Hvalue Hselect Hread Hjump
    |fr rest m nb callee args cont cs f fd entry env Hat Hread Hcallee Hbind Hlimit
    |fr caller rest m nb value v env Hat Hvalue Hjump
    |fr m nb value v Hat Hvalue]; cbn [stack] in Hframe.
  - destruct Hframe as [Heq|Htail].
    + subst observed; cbn [advance fenv] in Hlookup; unfold env_set in Hlookup.
      destruct (Nat.eq_dec x dst) as [->|Hne].
      * injection Hlookup as <-; eapply ssa_pointer_operation_origin; eassumption.
      * eapply ssa_pointer_old; [now left|exact Hlookup|exact Hbefore].
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|Htail].
    + subst observed; cbn [advance fenv] in Hlookup; unfold env_set in Hlookup.
      destruct (Nat.eq_dec x dst) as [->|Hne].
      * injection Hlookup as <-.
        destruct Hraw as [Hsite Hraw]; cbn [mem] in Hraw; unfold memory_set in Hraw.
        destruct (Nat.eq_dec nb nb); [|contradiction].
        cbn [msite] in Hraw; subst t; right; left.
        eapply ssa_pointer_body_listed; [exact Hat|now left].
      * eapply ssa_pointer_old; [now left|exact Hlookup|exact Hbefore].
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|Htail].
    + subst observed; eapply ssa_pointer_old; [now left|exact Hlookup|exact Hbefore].
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|Htail].
    + subst observed; cbn [advance fenv] in Hlookup; unfold env_set in Hlookup.
      destruct (Nat.eq_dec x dst) as [->|Hne].
      * injection Hlookup as <-; eapply ssa_pointer_load_origin; eassumption.
      * eapply ssa_pointer_old; [now left|exact Hlookup|exact Hbefore].
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|Htail].
    + subst observed; eapply ssa_pointer_old; [now left|exact Hlookup|exact Hbefore].
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|Htail].
    + subst observed; eapply ssa_pointer_old; [now left|exact Hlookup|exact Hbefore].
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|Htail].
    + subst observed; eapply ssa_pointer_jump_origin with (term := TJump l args).
      all: try eassumption; try discriminate; now left.
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|Htail].
    + subst observed; eapply ssa_pointer_jump_origin with (term := TBr cond l1 a1 l2 a2).
      all: try eassumption; try discriminate.
      cbn [term_edges]; destruct (Z.eqb z 0); injection Hselect as <- <-.
      * right; left; reflexivity.
      * left; reflexivity.
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|Htail].
    + subst observed; eapply ssa_pointer_jump_origin with
        (term := TSwitch cond cases d da).
      all: try eassumption; try discriminate.
      exact (switch_target_edge z cases d da l args Hselect).
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|[Hcaller|Htail]].
    + subst observed; eapply ssa_pointer_call_origin; eassumption.
    + subst observed; eapply ssa_pointer_old; [now left|exact Hlookup|exact Hbefore].
    + eapply ssa_pointer_old; [right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|Htail].
    + subst observed; eapply ssa_pointer_return_origin; eassumption.
    + eapply ssa_pointer_old; [right; right; exact Htail|exact Hlookup|exact Hbefore].
  - destruct Hframe as [Heq|[]]; subst observed.
    eapply ssa_pointer_old; [now left|exact Hlookup|exact Hbefore].
Qed.

(** Static root seeds establish initial value observations; initial memory has no fragments. *)
Theorem ssa_rel_ptr_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (ops : list (ptr_op vid vid)) :
  wf_program ext P -> incl (ssa_ptr_ops P) ops ->
  relational_ptr_laws (ssa_semantics ext P lim) (ssa_rel_ptr_view P) ops.
Proof.
  intros Hwf Hin; constructor.
  - intros s x t [fd [b [vs [env [Hfunction [Hblock [Htypes [Hvalid [Hbind ->]]]]]]]]]
      [fr [c [Hframe [Hvalue Hraw]]]].
    cbn [stack] in Hframe; destruct Hframe as [Heq|[]]; subst fr.
    destruct (ssa_raw_site_pointer P _ _ _ Hraw) as [vb [vo Heq]].
    assert (Hptr : ty_of c = TyPtr) by (rewrite Heq; reflexivity).
    destruct (ssa_bind_parameter_origin (bparams b) (fun _ => None) vs env x c
      Htypes Hbind Hptr Hvalue) as [Hnone|Hparam]; [discriminate|].
    apply Hin; eapply ssa_pointer_main_seed; [exact Hfunction|exact Hblock|exact Hparam|].
    exact (proj1 Hraw).
  - intros s t0 t [fd [b [vs [env [Hfunction [Hblock [Htypes [Hvalid [Hbind ->]]]]]]]]]
      [a [mb [off [c [i [Hget Hrest]]]]]]; discriminate.
  - intros s tr s' x t Hreach Hstep Hvalue.
    destruct (ssa_rel_value_step ext P lim s tr s' x t Hwf Hreach Hstep Hvalue)
      as [Hold|[Halloc|[[y [Hcopy Hy]]|[p [t0 [Hload [Hp Hheap]]]]]]].
    + now left.
    + right; left; apply Hin; exact Halloc.
    + right; right; left; exists y; split; [apply Hin; exact Hcopy|exact Hy].
    + right; right; right; exists p, t0; split; [apply Hin; exact Hload|auto].
  - intros s tr s' t0 t Hreach Hstep Hheap.
    destruct (ssa_rel_heap_step ext P lim s tr s' t0 t Hwf Hreach Hstep Hheap)
      as [Hold|[p [y [Hstore [Hp Hy]]]]].
    + now left.
    + right; exists p, y; split; [apply Hin; exact Hstore|auto].
Qed.

Lemma ssa_frame_value_present f x frames c : ssa_frame_value f x frames = Some c ->
  exists fr, In fr frames /\ fenv fr x = Some c.
Proof.
  induction frames as [|fr rest IH]; [discriminate|].
  cbn [ssa_frame_value]; destruct (Nat.eq_dec (ffunc fr) f).
  - intro Hvalue; exists fr; split; [now left|exact Hvalue].
  - intro Hvalue; destruct (IH Hvalue) as [observed [Hin Hget]].
    exists observed; split; [now right|exact Hget].
Qed.

(** Every recognized concrete binding is among the relational value observations. *)
Theorem ssa_rel_value_covers (ext : nat -> list cval -> option cval)
    (P : program) (lim : limits) :
  wf_program ext P -> forall s x t, reachable_state (ssa_semantics ext P lim) s ->
  pts_of (ssa_ptr_view ext P lim) s x = Some t -> rel_value (ssa_rel_ptr_view P) s x t.
Proof.
  intros Hwf s x t Hreach Hpts; unfold pts_of in Hpts.
  change (match ssa_pointer_value (ssa_pointer_owners P) s x with
    | Some c => match loc_of (ssa_mem_view ext P lim) s c with
      | Some l => loc_site (ssa_mem_view ext P lim) s l
      | None => None
      end
    | None => None
    end = Some t) in Hpts.
  unfold ssa_pointer_value in Hpts.
  destruct (Map.get nat_encoding x (ssa_pointer_owners P)) as [f|]; [|discriminate].
  destruct (ssa_frame_value f x (stack s)) as [c|] eqn:Hvalue; [|discriminate].
  destruct (ssa_frame_value_present f x _ c Hvalue) as [fr [Hframe Hget]].
  destruct c; cbn [ssa_mem_view loc_of] in Hpts; try discriminate.
  destruct (mem s b) as [mb|] eqn:Hblock; [|discriminate].
  cbn [ssa_mem_view loc_site] in Hpts; rewrite Hblock in Hpts; injection Hpts as <-.
  eapply ssa_rel_value_frame; [exact Hframe|exact Hget|].
  split; [exact (proj1 (ssa_pointer_memory_reachable ext P lim s Hwf Hreach b mb Hblock))|].
  rewrite Hblock; reflexivity.
Qed.

(** A successfully reconstructed heap pointer exposes one of its individual fragments. *)
Theorem ssa_rel_heap_covers (ext : nat -> list cval -> option cval)
    (P : program) (lim : limits) :
  wf_program ext P -> forall s t0 t, reachable_state (ssa_semantics ext P lim) s ->
  heap_pts (ssa_ptr_view ext P lim) s t0 t -> rel_heap (ssa_rel_ptr_view P) s t0 t.
Proof.
  intros Hwf s t0 t Hreach [c [c' [a [a' [Hloc [Hsite [Hheld [Hloc' Hsite']]]]]]]].
  destruct c; cbn [ssa_ptr_view pmem ssa_mem_view loc_of] in Hloc; try discriminate.
  destruct (mem s b) as [mb|] eqn:Hblock; [|discriminate]; injection Hloc as <-.
  cbn [ssa_ptr_view pmem ssa_mem_view loc_site] in Hsite;
    rewrite Hblock in Hsite; injection Hsite as <-.
  cbn [ssa_ptr_view held ssa_pointer_held] in Hheld; rewrite Hblock in Hheld.
  destruct c'; cbn [ssa_ptr_view pmem ssa_mem_view loc_of] in Hloc'; try discriminate.
  destruct (mem s b0) as [mb'|] eqn:Hblock'; [|discriminate]; injection Hloc' as <-.
  cbn [ssa_ptr_view pmem ssa_mem_view loc_site] in Hsite';
    rewrite Hblock' in Hsite'; injection Hsite' as <-.
  pose proof (proj2 (proj2 (ssa_pointer_load_fragment TyPtr M8 mb o b0 o0 Hheld))) as Hfragment.
  exists b, mb, o, (VPtr b0 o0), 0; split; [exact Hblock|].
  split; [reflexivity|]; split; [exact Hfragment|].
  split; [exact (proj1 (ssa_pointer_memory_reachable ext P lim s Hwf Hreach b0 mb' Hblock'))|].
  rewrite Hblock'; reflexivity.
Qed.

Lemma ssa_pointer_jump_effect_listed P fr term dst args op :
  at_term P fr term -> (forall c xs cont, term <> TCall c xs cont) ->
  (forall x, term <> TRet x) -> In (dst, args) (term_edges term) ->
  In op (ssa_pointer_jump (ssa_pointer_blocks P (ffunc fr)) (dst, args)) ->
  In op (ssa_ptr_ops P).
Proof.
  intros Hat Hcall Hreturn Hedge Hop.
  pose proof Hat as Hpoint; destruct Hpoint as [fd [source [Hfunction Hrest]]].
  unfold ssa_pointer_jump in Hop; cbn [fst snd] in Hop.
  rewrite (ssa_pointer_blocks_agree P _ fd _ Hfunction) in Hop.
  destruct (find_block fd dst) as [b|] eqn:Hblock; [|contradiction].
  eapply ssa_pointer_jump_listed; eassumption.
Qed.

Lemma ssa_pointer_dynamic_listed ext P lim fr rest m nb term op :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  at_term P fr term ->
  In op (ssa_pointer_dynamic_term P (ssa_pointer_blocks P)
    (ssa_pointer_entry (find_func P) (ssa_pointer_blocks P))
    (ssa_pointer_types P (ffunc fr)) fr rest term) -> In op (ssa_ptr_ops P).
Proof.
  intros Hwf Hreach Hat Hop; destruct term as
    [dst args|c l1 a1 l2 a2|c cases d da|callee args cont|value];
    cbn [ssa_pointer_dynamic_term] in Hop.
  - eapply ssa_pointer_jump_effect_listed; [exact Hat|discriminate|discriminate|now left|exact Hop].
  - destruct (fenv fr c) as [v|]; [|contradiction].
    destruct v as [[|] z| | | |]; try contradiction.
    destruct (Z.eqb z 0) eqn:Hselect;
      eapply ssa_pointer_jump_effect_listed with (term := TBr c l1 a1 l2 a2);
      [exact Hat|discriminate|discriminate|right; now left|exact Hop|
       exact Hat|discriminate|discriminate|now left|exact Hop].
  - destruct (fenv fr c) as [v|]; [|contradiction].
    destruct v as [[|] z| | | |]; try contradiction.
    destruct (switch_target z cases d da) as [dst args] eqn:Hselect.
    eapply ssa_pointer_jump_effect_listed with (term := TSwitch c cases d da);
      [exact Hat|discriminate|discriminate| |exact Hop].
    exact (switch_target_edge z cases d da dst args Hselect).
  - destruct (callee_def P (fenv fr) callee) as [[[f fd] b]|] eqn:Hcallee; [|contradiction].
    eapply ssa_pointer_term_listed; [exact Hat|].
    cbn [ssa_pointer_terminator ssa_pointer_call]; apply in_app_or in Hop.
    destruct Hop as [Hcopy|Hescape].
    + apply in_or_app; left; apply in_flat_map; exists f; split;
        [eapply ssa_call_resolved; eassumption|exact Hcopy].
    + apply in_or_app; now right.
  - destruct rest as [|caller tail]; [contradiction|].
    destruct (reachable_good ext P lim _ Hwf Hreach) as [_ Hlinks].
    cbn [stack stack_links] in Hlinks.
    destruct (proj1 Hlinks) as [childfd [callee [args [cont [ps
      [Hchild [Hcall [Hret Hsignature]]]]]]]].
    pose proof Hcall as Hpoint; destruct Hpoint as [fd [source [Hfunction Hrest]]].
    rewrite (ssa_pointer_blocks_agree P _ fd _ Hfunction) in Hop.
    destruct (find_block fd (fret caller)) as [b|] eqn:Hblock; [|contradiction].
    assert (Hresolved : In (ffunc fr) (ssa_resolver P (ffunc caller, flabel caller))).
    { pose proof (ssa_frame_chain ext P lim _ Hwf Hreach) as Hchain.
      cbn [ssa_calls here frames ssa_suspended stack tl map frames_linked] in Hchain.
      exact (proj1 (proj2 (proj2 Hchain))). }
    destruct (ssa_pointer_copies_only (bparams b) [value] op Hop) as [x [y ->]].
    destruct (ssa_pointer_copy_parameter (bparams b) [value] x y Hop) as [Hparam Harg].
    destruct Harg as [Heq|[]]; subst y.
    eapply ssa_pointer_term_listed; [exact Hat|]; cbn [ssa_pointer_terminator].
    apply in_map_iff; exists x; split; [reflexivity|].
    eapply ssa_pointer_return_destination; [exact Hcall|exact Hret|exact Hresolved|
      exact Hfunction|rewrite <- Hret; exact Hblock|exact Hparam].
Qed.

(** Every next-step effect occurs in the global syntax inventory. *)
Theorem ssa_ptr_pop_listed (ext : nat -> list cval -> option cval)
    (P : program) (lim : limits) (ops : list (ptr_op vid vid)) :
  wf_program ext P -> incl (ssa_ptr_ops P) ops ->
  forall s op, reachable_state (ssa_semantics ext P lim) s ->
  In op (pop (ssa_ptr_view ext P lim) s) -> In op ops.
Proof.
  intros Hwf Hin [frames m nb] op Hreach Hop; apply Hin.
  destruct frames as [|fr rest]; [contradiction|].
  change (In op (ssa_pointer_pop P (State (fr :: rest) m nb))) in Hop.
  unfold ssa_pointer_pop in Hop; cbn [stack] in Hop.
  destruct (ssa_current P (State (fr :: rest) m nb)) as [[i|term]|] eqn:Hcurrent;
    [| |contradiction].
  - apply ssa_current_sound in Hcurrent; eapply ssa_pointer_body_listed; eassumption.
  - apply ssa_current_sound in Hcurrent; eapply ssa_pointer_dynamic_listed; eassumption.
Qed.

(** * Full-range footprints and zero bytes *)

Lemma ssa_pointer_action_current P fr rest m nb action :
  ssa_current P (State (fr :: rest) m nb) = Some action ->
  ssa_pointer_action P (full_frame_point fr) = action.
Proof.
  unfold ssa_current, ssa_pointer_action, full_frame_point; cbn [stack fst snd].
  destruct (Map.get nat_encoding (ffunc fr)
    (Map.map (fun fd => Map.map ssa_action_index (first_index (blocks fd)))
      (first_index (funcs P)))) as [bs|]; [|discriminate].
  destruct (Map.get nat_encoding (flabel fr) bs) as [code|]; [|discriminate].
  intro Hcurrent; unfold ssa_get; rewrite Hcurrent; reflexivity.
Qed.

Lemma ssa_footprints_current ext P lim fr rest m nb tr s' e action :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  step_s ext P lim (State (fr :: rest) m nb) tr s' ->
  taken (ssa_full_view ext P lim) (State (fr :: rest) m nb) tr s' e ->
  ssa_current P (State (fr :: rest) m nb) = Some action ->
  ssa_footprints P e = if ssa_pointer_writes action then
    map (fun site => Footprint site 0%Z (2 ^ 64)%Z) (ssa_allocation_sites P) else [].
Proof.
  intros Hwf Hreach Hstep Htaken Hcurrent.
  destruct (view_taken_edge _ _ _ _ _ _ (ssa_full_view_laws ext P lim Hwf)
    Hreach Hstep Htaken) as [_ [Hsource Htarget]].
  change (fsrc e = full_frame_point fr) in Hsource.
  unfold ssa_footprints; rewrite Hsource,
    (ssa_pointer_action_current P fr rest m nb action Hcurrent); reflexivity.
Qed.

Lemma ssa_pointer_full_range P site off :
  In site (ssa_allocation_sites P) -> (0 <= off < 2 ^ 64)%Z ->
  covered (map (fun t => Footprint t 0%Z (2 ^ 64)%Z) (ssa_allocation_sites P)) site off 1.
Proof.
  intros Hsite Hbounds k Hk; exists (Footprint site 0%Z (2 ^ 64)%Z).
  split; [apply in_map_iff; exists site; split; [reflexivity|exact Hsite]|].
  cbn [fp_site fp_lo fp_hi]; split; [reflexivity|].
  cbn in Hk; lia.
Qed.

Lemma ssa_pointer_readable s b off n : ssa_pointer_byte s (VPtr b off) = Some n ->
  exists mb, mem s b = Some mb /\ (0 <= off < Z.of_nat (msz mb))%Z.
Proof.
  unfold ssa_pointer_byte; destruct (mem s b) as [mb|] eqn:Hblock; [|discriminate].
  destruct (access_ok mb off M1) eqn:Haccess; [|discriminate].
  intro Hbyte; exists mb; split; [reflexivity|].
  unfold access_ok in Haccess; apply andb_true_iff in Haccess as [Hprefix Hhi].
  apply andb_true_iff in Hprefix as [Hlive Hlo].
  apply Z.leb_le in Hlo; apply Z.leb_le in Hhi; cbn [size_bytes] in Hhi; lia.
Qed.

Lemma ssa_pointer_fresh_zero ext P lim s tr s' c l0 t n :
  reachable_state (ssa_semantics ext P lim) s -> step_s ext P lim s tr s' ->
  loc_of (ssa_mem_view ext P lim) s c = None ->
  loc_of (ssa_mem_view ext P lim) s' c = Some l0 ->
  loc_site (ssa_mem_view ext P lim) s' l0 = Some t ->
  ssa_pointer_byte s' c = Some n -> n = 0.
Proof.
  intros Hreach Hstep Hnone Hloc Hsite Hbyte.
  destruct c; cbn [ssa_mem_view loc_of] in Hloc, Hnone; try discriminate.
  destruct Hstep; cbn [mem] in Hnone, Hloc; try congruence.
  - unfold memory_set in Hloc; destruct (Nat.eq_dec b nb) as [->|Hne].
    + cbn [ssa_pointer_byte mem] in Hbyte; unfold memory_set in Hbyte.
      destruct (Nat.eq_dec nb nb); [|contradiction].
      destruct (access_ok _ _ _); [injection Hbyte as <-; reflexivity|discriminate].
    + destruct (m b); congruence.
  - unfold memory_set in Hloc; destruct (Nat.eq_dec b b0) as [->|Hne].
    + match goal with Hblock : m b0 = Some mb |- _ => rewrite Hblock in Hnone end.
      discriminate.
    + destruct (m b); congruence.
  - unfold memory_set in Hloc; destruct (Nat.eq_dec b b0) as [->|Hne].
    + match goal with Hblock : m b0 = Some mb |- _ => rewrite Hblock in Hnone end.
      discriminate.
    + destruct (m b); congruence.
Qed.

Lemma ssa_pointer_address ext P lim s tr s' c l0 l1 t :
  reachable_state (ssa_semantics ext P lim) s -> step_s ext P lim s tr s' ->
  loc_of (ssa_mem_view ext P lim) s c = Some l0 ->
  loc_of (ssa_mem_view ext P lim) s' c = Some l1 ->
  loc_site (ssa_mem_view ext P lim) s' l1 = Some t ->
  loc_site (ssa_mem_view ext P lim) s l0 = Some t /\
  loc_offset (ssa_mem_view ext P lim) s c = loc_offset (ssa_mem_view ext P lim) s' c.
Proof.
  intros Hreach Hstep Hbefore Hafter Hsite.
  destruct c; cbn [ssa_mem_view loc_of] in Hbefore, Hafter; try discriminate.
  destruct (mem s b) as [mb|] eqn:Hblock; [|discriminate]; injection Hbefore as <-.
  destruct (mem s' b) as [mb'|] eqn:Hblock'; [|discriminate]; injection Hafter as <-.
  split; [|reflexivity].
  assert (Hstable : option_map msite (mem s' b) = Some (msite mb)).
  { eapply full_site_step; [eapply full_memory_fresh_reachable; exact Hreach|exact Hstep|].
    rewrite Hblock; reflexivity. }
  change (option_map msite (mem s' b) = Some t) in Hsite.
  change (option_map msite (mem s b) = Some t).
  rewrite Hblock' in Hsite, Hstable; rewrite Hblock.
  cbn in *; congruence.
Qed.

Lemma ssa_pointer_kept_zero ext P lim s tr s' e c l0 t :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  step_s ext P lim s tr s' -> taken (ssa_full_view ext P lim) s tr s' e ->
  loc_of (ssa_mem_view ext P lim) s c = Some l0 ->
  loc_site (ssa_mem_view ext P lim) s l0 = Some t ->
  ~ covered (ssa_footprints P e) t (loc_offset (ssa_mem_view ext P lim) s c) 1 ->
  (forall n, ssa_pointer_byte s c = Some n -> n = 0) ->
  forall n, ssa_pointer_byte s' c = Some n -> n = 0.
Proof.
  intros Hwf Hreach Hstep Htaken Hloc Hsite Houtside Hzero n Hbyte.
  destruct c; cbn [ssa_mem_view loc_of] in Hloc; try discriminate.
  destruct (mem s b) as [old|] eqn:Hold; [|discriminate]; injection Hloc as <-.
  cbn [ssa_mem_view loc_site] in Hsite; rewrite Hold in Hsite; injection Hsite as Hsite.
  cbn [ssa_mem_view loc_offset] in Houtside.
  pose proof (ssa_pointer_memory_reachable ext P lim s Hwf Hreach b old Hold) as Hmemory.
  pose proof Hstep as Htransition; destruct Hstep;
    try solve [apply Hzero; exact Hbyte].
  - assert (Hfresh : m nb = None).
    { apply (full_memory_fresh_reachable ext P lim _ Hreach nb); cbn; lia. }
    cbn [mem] in Hold; assert (Hne : b <> nb) by congruence.
    unfold ssa_pointer_byte in Hbyte; cbn [mem] in Hbyte.
    unfold memory_set in Hbyte; destruct (Nat.eq_dec b nb); [contradiction|].
    apply Hzero; exact Hbyte.
  - unfold ssa_pointer_byte in Hbyte; cbn [mem] in Hbyte; unfold memory_set in Hbyte.
    destruct (Nat.eq_dec b b0) as [->|Hne].
    + cbn [access_ok mlive andb] in Hbyte; discriminate.
    + apply Hzero; exact Hbyte.
  - exfalso; apply Houtside.
    match goal with Hat : at_instr P fr (IStore sz p x) |- _ =>
      rewrite (ssa_footprints_current ext P lim fr k m nb _ _ e _ Hwf Hreach
        Htransition Htaken (ssa_current_instr P fr k m nb _ Hat)) end.
    cbn [ssa_pointer_writes].
    destruct (ssa_pointer_readable _ b o n Hbyte) as [post [Hpost Hbounds]].
    destruct (ssa_pointer_memory_reachable ext P lim _ Hwf
      (reachable_state_step _ _ _ _ Hreach Htransition) b post Hpost) as [Hsites Hsize].
    assert (Hpostsite : msite post = t).
    { cbn [mem] in Hold; pose proof (full_site_step ext P lim _ _ _ b t
        (full_memory_fresh_reachable ext P lim _ Hreach) Htransition) as Hstable.
      specialize (Hstable ltac:(cbn [mem]; rewrite Hold; cbn; now rewrite Hsite)).
      cbn [mem] in Hpost, Hstable.
      rewrite Hpost in Hstable; cbn in Hstable; congruence. }
    apply ssa_pointer_full_range; [rewrite <- Hpostsite; exact Hsites|lia].
Qed.

(** The actual SSA memory and coarse footprints satisfy all C59 zero-byte obligations. *)
Theorem ssa_zero_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P ->
  zero_laws (ssa_semantics ext P lim) (ssa_full_view ext P lim) (ssa_ptr_view ext P lim)
    (ssa_footprints P).
Proof.
  intro Hwf; constructor.
  - apply ssa_full_view_laws; exact Hwf.
  - intros s l s' Hstay; exact Hstay.
  - intros s c l0 t n [fd [b [vs [env [_ [_ [_ [_ [_ ->]]]]]]]]] Hloc Hsite Hbyte.
    destruct c; discriminate.
  - intros s tr s' e c l0 t n Hreach Hstep Htaken Hnone Hloc Hsite Hbyte.
    eapply ssa_pointer_fresh_zero; eassumption.
  - intros s tr s' e c l0 l1 t Hreach Hstep Htaken Hbefore Hafter Hsite.
    eapply ssa_pointer_address; eassumption.
  - intros s tr s' e c l0 t Hreach Hstep Htaken Hloc Hsite Houtside Hzero n Hbyte.
    eapply ssa_pointer_kept_zero; eassumption.
Qed.
