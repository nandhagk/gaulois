(** * Dense analyses and executable While fixtures

    While adapters specialize generic soundness theorems and execute the shared engines.
    For example, the factorial loop carries a live counter whose value is never observed.
    Builds on: While views, dense analyses and the total worklist engine. *)

From Stdlib Require Import List Bool Arith ZArith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderPowerset OrderLift OrderPointwise.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointTotal FixpointSchedule FixpointWorklist.
From Gaulois.Domains Require Import DomainsEquality.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSkeleton ViewsStructured
  ViewsForward.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesAvailable AnalysesDemand.
From Gaulois.Examples.While Require Import ExamplesWhileSyntax ExamplesWhileSemantics
  ExamplesWhileSkeleton ExamplesWhileViews.
Import List.ListNotations.

Local Open Scope nat_scope.

(** Unary operator tags are injective constructor indices. *)
Definition while_unop_encoding : encoding unop.
Proof.
  refine (Encoding unop (fun o => match o with Neg => 1 | BNot => 2 | LNot => 3 end)%positive _).
  intros [] [] Heq; discriminate || reflexivity.
Defined.

(** Binary operator tags are injective constructor indices. *)
Definition while_binop_encoding : encoding binop.
Proof.
  refine (Encoding binop (fun o => match o with
    | Add => 1 | Sub => 2 | Mul => 3 | And => 4 | Or => 5 | Xor => 6 | Shl => 7 | ShrU => 8
    | ShrS => 9 | Eq => 10 | Ne => 11 | LtU => 12 | LeU => 13 | LtS => 14 | LeS => 15
    end)%positive _).
  intros [] [] Heq; discriminate || reflexivity.
Defined.

(** Expression codes pair constructor-tagged payloads and recursive operand codes. *)
Fixpoint while_expr_code (e : expr) : positive :=
  match e with
  | EConst z => xO (xO (encode Z_encoding z))
  | EVar x => xO (xI (encode var_encoding x))
  | EUn o e => xI (xO (encode (pair_encoding positive_encoding positive_encoding)
      (encode while_unop_encoding o, while_expr_code e)))
  | EBin o e1 e2 => xI (xI (encode (pair_encoding positive_encoding positive_encoding)
      (encode while_binop_encoding o, encode (pair_encoding positive_encoding positive_encoding)
        (while_expr_code e1, while_expr_code e2))))
  end.

(** Expression codes preserve operators, constant payloads and ordered operands. *)
Lemma while_expr_code_injective e : forall f, while_expr_code e = while_expr_code f -> e = f.
Proof.
  induction e as [z|x|o e IH|o e1 IH1 e2 IH2]; intros [w|y|u f|b f1 f2] Hcode;
    cbn [while_expr_code] in Hcode; try discriminate; injection Hcode as Hcode.
  - apply (encode_injective Z_encoding) in Hcode; subst; reflexivity.
  - apply (encode_injective var_encoding) in Hcode; subst; reflexivity.
  - change (encode (pair_encoding positive_encoding positive_encoding)
      (encode while_unop_encoding o, while_expr_code e) =
      encode (pair_encoding positive_encoding positive_encoding)
      (encode while_unop_encoding u, while_expr_code f)) in Hcode.
    apply (encode_injective (pair_encoding positive_encoding positive_encoding)) in Hcode.
    injection Hcode as Hop Harg.
    pose proof (encode_injective while_unop_encoding o u Hop) as Heq; subst u.
    apply IH in Harg; subst; reflexivity.
  - change (encode (pair_encoding positive_encoding positive_encoding)
      (encode while_binop_encoding o, encode (pair_encoding positive_encoding positive_encoding)
        (while_expr_code e1, while_expr_code e2)) =
      encode (pair_encoding positive_encoding positive_encoding)
      (encode while_binop_encoding b, encode (pair_encoding positive_encoding positive_encoding)
        (while_expr_code f1, while_expr_code f2))) in Hcode.
    apply (encode_injective (pair_encoding positive_encoding positive_encoding)) in Hcode.
    injection Hcode as Hop Hargs.
    pose proof (encode_injective while_binop_encoding o b Hop) as Heq; subst b.
    change (encode (pair_encoding positive_encoding positive_encoding)
      (while_expr_code e1, while_expr_code e2) =
      encode (pair_encoding positive_encoding positive_encoding)
      (while_expr_code f1, while_expr_code f2)) in Hargs.
    apply (encode_injective (pair_encoding positive_encoding positive_encoding)) in Hargs.
    injection Hargs as Hfirst Hsecond; apply IH1 in Hfirst; apply IH2 in Hsecond.
    subst; reflexivity.
Qed.

(** Expressions use canonical positive codes, without quotienting word-equivalent constants. *)
Definition expr_encoding : encoding expr := Encoding expr while_expr_code while_expr_code_injective.

(** Dense liveness is the result of the generic total solver at the requested skeleton point. *)
Definition while_live_at (prog : stmt) (n : skel_point) :
    live_set var_encoding (while_var_view prog word_stores) :=
  proj1_sig (solve_liveness skel_point_encoding skel_edge_encoding var_encoding
    (while_var_view prog word_stores)) n.

(** Neededness is the engine's total closed Boolean demand. *)
Definition while_needed (prog : stmt) :
    finite_map var_encoding (dvars (while_demand_view prog word_stores)) bool :=
  needed_values var_encoding (while_demand_view prog word_stores).

(** A variable is dead when the engine's closed demand does not need its value. *)
Definition while_dead_var (prog : stmt) (x : var) : bool :=
  dead_value var_encoding (while_demand_view prog word_stores) x.

(** This point is the factorial loop's body entry after its two label entries. *)
Definition loop_head : skel_point := PEntry [DSecond; DFirst; DBody; DBody].

(** Code motion extends generation while retaining the source graph, kills and evaluation. *)
Definition lcm_extended_view (prog : stmt) (r : lcm_result (skel_edge atom expr) skel_point expr) :
    genkill_view (mstate store) Z skel_point (skel_edge atom expr) expr Z :=
  let original := while_genkill_view prog word_stores in
  {| gkview := gkview original;
     gen := fun e => gen original e ++ insert r e;
     kill := kill original;
     uval := uval original |}.

(** Every expression universe is duplicate-free because it is enumerated from a canonical set. *)
Lemma while_expr_universe_nodup (gk : genkill_view (mstate store) Z skel_point
    (skel_edge atom expr) expr Z) : NoDup (expr_universe expr_encoding gk).
Proof.
  apply (FinSet.elements_nodup expr_encoding), FinSet.wf_fold_add, Map.wf_empty.
Qed.

(** Availability executes the total solver over its forward must-analysis constraints. *)
Definition while_solve_available (gk : genkill_view (mstate store) Z skel_point
    (skel_edge atom expr) expr Z) : skel_point -> avail_set expr_encoding gk :=
  let L := avail_lattice expr_encoding gk in
  let sys := available_system expr_encoding gk in
  let static := forward_static (cfg (gkview gk)) (fun _ =>
    finite_clamp expr_encoding (expr_universe expr_encoding gk) FinSet.empty)
    (avail_transfer expr_encoding gk) in
  proj1_sig (solve_total skel_point_encoding (dense_constraint_encoding skel_point_encoding
    skel_edge_encoding) L (finite_must_laws _ _) (rpo_scheduler skel_point_encoding sys static)
    Joining sys static (inhabits (base_height (finite_must_height _ _
      (while_expr_universe_nodup gk))))).

(** Source availability comes from the engine without client-supplied candidate facts. *)
Definition lcm_avail (prog : stmt) :
    skel_point -> avail_set expr_encoding (while_genkill_view prog word_stores) :=
  while_solve_available (while_genkill_view prog word_stores).

(** Anticipation executes the total solver over the backward very-busy constraints. *)
Definition lcm_busy (prog : stmt) :
    skel_point -> avail_set expr_encoding (while_genkill_view prog word_stores) :=
  let gk := while_genkill_view prog word_stores in
  let L := avail_lattice expr_encoding gk in
  let sys := busy_system expr_encoding gk in
  let static := backward_static (cfg (gkview gk)) (fun n =>
    match Graph.out (cfg (gkview gk)) n with
    | [] => finite_clamp expr_encoding (expr_universe expr_encoding gk) FinSet.empty
    | _ => bot L
    end) (avail_transfer expr_encoding gk) in
  proj1_sig (solve_total skel_point_encoding (dense_constraint_encoding skel_point_encoding
    skel_edge_encoding) L (finite_must_laws _ _) (rpo_scheduler skel_point_encoding sys static)
    Joining sys static (inhabits (base_height (finite_must_height _ _
      (while_expr_universe_nodup gk))))).

(** Availability after insertions is computed from the extended view by the same engine. *)
Definition lcm_avail2 (prog : stmt) (r : lcm_result (skel_edge atom expr) skel_point expr) :
    skel_point -> avail_set expr_encoding (lcm_extended_view prog r) :=
  while_solve_available (lcm_extended_view prog r).

(** The factorial fixture keeps p in variable zero, x in one and the unused counter in two. *)
Definition factorial_while : stmt :=
  SSeq (SAssign 0 (EConst 1%Z))
    (SSeq (SLoop (SSeq (SAssign 0 (EBin Mul (EVar 0) (EVar 1)))
      (SSeq (SAssign 2 (EBin Add (EVar 2) (EConst 1%Z)))
        (SSeq (SAssign 1 (EBin Sub (EVar 1) (EConst 1%Z)))
          (SIf (EBin LtU (EConst 0%Z) (EVar 1)) (SContinue 0) (SBreak 0))))))
      (SOutput (EVar 0))).

(** The expected erasure retains the loop and replaces only the unused counter assignment. *)
Definition factorial_while_dce : stmt :=
  SSeq (SAssign 0 (EConst 1%Z))
    (SSeq (SLoop (SSeq (SAssign 0 (EBin Mul (EVar 0) (EVar 1)))
      (SSeq SSkip
        (SSeq (SAssign 1 (EBin Sub (EVar 1) (EConst 1%Z)))
          (SIf (EBin LtU (EConst 0%Z) (EVar 1)) (SContinue 0) (SBreak 0))))))
      (SOutput (EVar 0))).

(** The counter is read by its own update but never affects observable output. *)
Definition z_var : var := 2.

(** The diamond recomputes a+b after an arm that may already have computed it. *)
Definition lcm_prog : stmt :=
  SSeq (SIf (EVar 0) (SAssign 1 (EBin Add (EVar 3) (EVar 4))) SSkip)
    (SAssign 2 (EBin Add (EVar 3) (EVar 4))).

(** Insert on the empty arm and delete the later recomputation at its actual entry. *)
Definition lcm_result_ex : lcm_result (skel_edge atom expr) skel_point expr :=
  {| insert := fun e =>
       if Pos.eqb (encode skel_edge_encoding e)
         (encode skel_edge_encoding
           (SkelEdge (PEntry [DFirst; DSecond]) 0 : skel_edge atom expr))
       then [EBin Add (EVar 3) (EVar 4)] else [];
     delete := fun n =>
       if Pos.eqb (encode skel_point_encoding n) (encode skel_point_encoding (PEntry [DSecond]))
       then [EBin Add (EVar 3) (EVar 4)] else [] |}.

(** Agreement on dense live inputs preserves every source While behaviour. *)
Theorem while_liveness_sound (prog : stmt)
    (sigma : skel_point -> live_set var_encoding (while_var_view prog word_stores))
    (c0 c1 : config) :
  post_solution (live_lattice var_encoding (while_var_view prog word_stores))
    (liveness_system var_encoding (while_var_view prog word_stores)) sigma ->
  initial (while_semantics prog word_stores) c0 -> initial (while_semantics prog word_stores) c1 ->
  (forall x, fmem var_encoding x (sigma (PEntry nil)) = true ->
     store_of_config c0 x = store_of_config c1 x) ->
  same_behaviour (while_semantics prog word_stores) while_endings c0
    (while_semantics prog word_stores) while_endings c1.
Proof.
  intros Hpost [st0 [Hinit0 ->]] [st1 [Hinit1 ->]] Hagree.
  eapply while_behaviour_transport with (m0 := Go [] [] st0) (m1 := Go [] [] st1).
  - apply match_run, wc_root.
  - apply match_run, wc_root.
  - eapply (liveness_sound _ _ var_encoding (while_var_view prog word_stores) sigma).
    + apply while_var_view_laws.
    + exact Hpost.
    + exists st0; split; [reflexivity|exact Hinit0].
    + exists st1; split; [reflexivity|exact Hinit1].
    + reflexivity.
    + exact Hagree.
Qed.

(** Every last writer on a source-machine run is represented by the reaching solution. *)
Theorem while_reaching_sound (prog : stmt)
    (sigma : skel_point -> reach_set var_encoding skel_edge_encoding
      (while_var_view prog word_stores)) :
  post_solution (reach_lattice var_encoding skel_edge_encoding (while_var_view prog word_stores))
    (reaching_system var_encoding skel_edge_encoding (while_var_view prog word_stores)) sigma ->
  forall s0 es s x d,
    initial (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s0 ->
    run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
      (gview (while_var_view prog word_stores)) s0 es s ->
    last_writer (fun e y => mentions var_encoding y (defs (while_var_view prog word_stores) e)) es x
      = Some d ->
    fmem (pair_encoding var_encoding skel_edge_encoding) (x, d)
      (sigma (point (gview (while_var_view prog word_stores)) s)) = true.
Proof.
  intro Hpost; exact (reaching_sound _ _ var_encoding skel_edge_encoding
    (while_var_view prog word_stores) sigma (while_var_view_laws prog word_stores) Hpost).
Qed.

(** Variables proved untouched since entry retain their initialized zero value. *)
Theorem while_zero_since_entry_sound (prog : stmt) (locals : list var) (zero : Z)
    (sigma : skel_point -> live_set var_encoding (while_var_view prog word_stores)) :
  (forall s x, initial (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s ->
    In x locals -> vget (while_var_view prog word_stores) s x = zero) ->
  post_solution (zero_lattice var_encoding (while_var_view prog word_stores))
    (zero_since_entry_system var_encoding (while_var_view prog word_stores) locals) sigma ->
  forall s x, reachable_state
    (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s ->
    fmem var_encoding x (sigma (point (gview (while_var_view prog word_stores)) s)) = true ->
    vget (while_var_view prog word_stores) s x = zero.
Proof.
  intros Hinitial Hpost; exact (zero_since_entry_sound _ _ var_encoding
    (while_var_view prog word_stores) locals zero sigma
    (while_var_view_laws prog word_stores) Hinitial Hpost).
Qed.

(** Variables in one inferred equality class have the same actual value. *)
Theorem while_equality_sound (prog : stmt) (sigma : skel_point -> partition var_encoding) :
  post_solution (partition_lattice var_encoding)
    (equality_system var_encoding (while_copy_view prog word_stores)) sigma ->
  forall s x y, reachable_state
    (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s ->
    partition_equiv var_encoding (sigma (point (gview (while_var_view prog word_stores)) s)) x y ->
    vget (while_var_view prog word_stores) s x = vget (while_var_view prog word_stores) s y.
Proof.
  intro Hpost; exact (equality_sound _ _ var_encoding (while_copy_view prog word_stores)
    sigma (while_var_view_laws prog word_stores) (while_copy_sound prog word_stores) Hpost).
Qed.
(** An available expression was computed earlier with its current value. *)
Theorem while_available_sound (prog : stmt)
    (sigma : skel_point -> avail_set expr_encoding (while_genkill_view prog word_stores)) :
  post_solution (avail_lattice expr_encoding (while_genkill_view prog word_stores))
    (available_system expr_encoding (while_genkill_view prog word_stores)) sigma ->
  forall s0 es s u,
    initial (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s0 ->
    run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
      (gkview (while_genkill_view prog word_stores)) s0 es s ->
    fmem expr_encoding u (sigma (point (gkview (while_genkill_view prog word_stores)) s)) = true ->
    exists es1 s1 e es2, es = es1 ++ e :: es2 /\
      run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
        (gkview (while_genkill_view prog word_stores)) s0 es1 s1 /\
      run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
        (gkview (while_genkill_view prog word_stores)) s1 (e :: es2) s /\
      In u (gen (while_genkill_view prog word_stores) e) /\
      uval (while_genkill_view prog word_stores) s u =
        uval (while_genkill_view prog word_stores) s1 u.
Proof.
  intro Hpost; exact (available_sound _ _ expr_encoding (while_genkill_view prog word_stores)
    sigma (while_genkill_laws prog word_stores) Hpost).
Qed.

(** An anticipated expression is computed before it is killed on every terminating run. *)
Theorem while_busy_sound (prog : stmt)
    (sigma : skel_point -> avail_set expr_encoding (while_genkill_view prog word_stores)) :
  post_solution (avail_lattice expr_encoding (while_genkill_view prog word_stores))
    (busy_system expr_encoding (while_genkill_view prog word_stores)) sigma ->
  forall s es t u,
    reachable_state (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s ->
    run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
      (gkview (while_genkill_view prog word_stores)) s es t ->
    final (skeleton_endings (to_skeleton prog) (while_client word_stores)) t ->
    fmem expr_encoding u (sigma (point (gkview (while_genkill_view prog word_stores)) s)) = true ->
    exists es1 e es2, es = es1 ++ e :: es2 /\
      In u (gen (while_genkill_view prog word_stores) e) /\
      forall e', In e' es1 -> kill (while_genkill_view prog word_stores) e' u = false.
Proof.
  intro Hpost; exact (busy_sound _ _ expr_encoding (while_genkill_view prog word_stores)
    sigma (while_genkill_laws prog word_stores) Hpost).
Qed.

