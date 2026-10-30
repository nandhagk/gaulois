(** * Common executable SSA analysis clients

    The clients instantiate the shared engines on SSA instruction points and source values.
    For example, factorial's auxiliary counter is live but has no observable demand.
    Builds on: ExamplesSsaViews, AnalysesLiveness and DomainsConst. *)

From Stdlib Require Import List Bool ZArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderConcrete OrderFlat OrderPointwise
  OrderLift.
From Gaulois.Bits Require Import BitsWord.
From Gaulois.Domains Require Import DomainsNumeric DomainsConst.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesDemand AnalysesEgraph
  AnalysesValues AnalysesPaths AnalysesPointsTo.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsAgreement ViewsSsa ViewsDominated.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaActivation ExamplesSsaViews
  ExamplesSsaBridge ExamplesSsaStrict ExamplesSsaPointers.
Import List.ListNotations.
Local Open Scope nat_scope.

(** Labels use the shared injective natural-number encoding. *)
Definition label_encoding : encoding label := nat_encoding.

Definition ssa_bop_code (o : bop) : nat :=
  match o with
  | BAdd => 0
  | BSub => 1
  | BMul => 2
  | BDivU => 3
  | BAnd => 4
  | BOr => 5
  | BXor => 6
  | BShl => 7
  | BShrU => 8
  | BEq => 9
  | BLtU => 10
  | BLtS => 11
  end.

Local Lemma ssa_bop_code_injective o p : ssa_bop_code o = ssa_bop_code p -> o = p.
Proof.
  destruct o, p; cbn; intro Heq; discriminate || reflexivity.
Qed.

Definition ssa_cval_code (c : cval) : nat * (nat * Z) :=
  match c with
  | VInt W32 z => (0, (0, z))
  | VInt W64 z => (1, (0, z))
  | VPtr b off => (2, (b, off))
  | VFun f => (3, (f, 0%Z))
  | VF32 bits => (4, (0, bits))
  | VF64 bits => (5, (0, bits))
  end.

Local Lemma ssa_cval_code_injective c d : ssa_cval_code c = ssa_cval_code d -> c = d.
Proof.
  destruct c as [[|] z|b off|f|z|z], d as [[|] z'|b' off'|f'|z'|z'];
    cbn; intro Heq; inversion Heq; reflexivity.
Qed.

Definition ssa_cval_encoding : encoding cval.
Proof.
  pose (E := pair_encoding nat_encoding (pair_encoding nat_encoding Z_encoding)).
  refine (Encoding _ (fun c => encode E (ssa_cval_code c)) _).
  intros c d Heq; apply ssa_cval_code_injective, (encode_injective E); exact Heq.
Defined.

Definition ssa_sop_code (o : sop) : (cval + ((nat * nat) + (nat * nat)))%type :=
  match o with
  | OConst c => inl c
  | OBin w op => inr (inl ((match w with W32 => 0 | W64 => 1 end), ssa_bop_code op))
  | OZext => inr (inr (0, 0))
  | OTrunc => inr (inr (1, 0))
  | OPtrAdd => inr (inr (2, 0))
  | OExt tag => inr (inr (3, tag))
  end.

(** Operation codes preserve tags, integer widths and every concrete constant payload. *)
Definition sop_encoding : encoding sop.
Proof.
  pose (E := sum_encoding ssa_cval_encoding
    (sum_encoding (pair_encoding nat_encoding nat_encoding)
      (pair_encoding nat_encoding nat_encoding))).
  refine (Encoding _ (fun o => encode E (ssa_sop_code o)) _).
  intros [c|w o| | | |tag] [d|w' p| | | |tag'] Heq;
    apply (encode_injective E) in Heq; cbn [ssa_sop_code] in Heq;
    try discriminate; try reflexivity; try (injection Heq as ->; reflexivity).
  destruct w, w'; cbn in Heq; try discriminate;
    injection Heq as Hcode; apply ssa_bop_code_injective in Hcode; subst p; reflexivity.
Defined.

(** The constant client uses the tagged flat integer domain. *)
Definition const_numeric : numeric_domain (tagged (flat Z)) := tagged_domain const_domain.

(** Constant concretisation retains the width tag and canonical word range. *)
Definition const_conc : concretisation (tagged (flat Z)) word := tagged_gamma const_gamma.

(** Raw liveness is the fact returned by the total shared dataflow engine. *)
Definition liveness_at (P : program) (pt : label * nat)
    : live_set var_encoding (ssa_var_view (fun _ _ => None) P 0) :=
  proj1_sig (solve_liveness (pair_encoding label_encoding nat_encoding) ssa_edge_encoding
    var_encoding (ssa_var_view (fun _ _ => None) P 0)) pt.

(** A closed demand permits changing one undemanded value at a reachable common point. *)
Theorem ssa_dead_value_removable (ext : nat -> list cval -> option cval) (P : program) (f : func)
    (d : finite_map var_encoding (dvars (ssa_demand_view ext P f)) bool) (x : vid) (s t : astate) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  demand_closed var_encoding bool_demand (ssa_demand_view ext P f) d ->
  dget var_encoding bool_lattice d x = false ->
  reachable_state (activation ext P f) s -> reachable_state (activation ext P f) t ->
  point (ssa_point_view ext P f) t = point (ssa_point_view ext P f) s ->
  (forall y, y <> x -> aenv s y = aenv t y) ->
  same_behaviour (activation ext P f) (activation_endings ext P f) s
    (activation ext P f) (activation_endings ext P f) t.
Proof.
  intros Hwf Hfunction Hclosed Hdead Hs Ht Hpoint Hsame.
  apply (dead_value_removable (activation ext P f) (activation_endings ext P f)
    (reachable_state (activation ext P f)) var_encoding bool_demand (ssa_demand_view ext P f)
    d x (ssa_demand_view_laws ext P f Hwf Hfunction)).
  - apply reachable_invariant.
  - exact Hclosed.
  - exact Hdead.
  - exact Hs.
  - exact Ht.
  - exact Hpoint.
  - exact Hsame.
Qed.

(** Factorial carries a separate counter whose increments are pure typed additions. *)
Definition factorial_ssa : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32)]
      [IOp 1 (OConst (VInt W32 1)) []; IOp 2 (OConst (VInt W32 0)) []]
      (TJump 1 [1; 0; 2]));
     (1, SBlock [(3, TyI32); (4, TyI32); (5, TyI32)]
      [IOp 6 (OBin W32 BMul) [3; 4];
       IOp 7 (OConst (VInt W32 1)) [];
       IOp 8 (OBin W32 BAdd) [5; 7];
       IOp 9 (OBin W32 BSub) [4; 7];
       IOp 10 (OConst (VInt W32 0)) [];
       IOp 11 (OBin W32 BLtU) [10; 9]]
      (TBr 11 1 [6; 9; 8] 2 [6]));
     (2, SBlock [(12, TyI32)] [IOutput 12] (TRet 12))] TyI32)] 0 [].

(** The auxiliary loop counter is source value five. *)
Definition z_value : vid := 5.

(** The observable accumulator is source value three. *)
Definition p_value : vid := 3.

(** Raw loop liveness is queried before the first loop instruction. *)
Definition loop_header_point : label * nat := (1, 0).

(** * Checked multiplication-by-one rewriting *)

(** Every variable in this environment holds a canonical unsigned 32-bit integer. *)
Definition ok_i32 (env : nat -> option cval) : Prop :=
  forall i, exists z, env i = Some (VInt W32 z) /\ (0 <= z < 4294967296)%Z.

Local Definition ssa_i32_operator (o : sop) : bool :=
  match o with
  | OConst (VInt W32 _) => true
  | OBin W32 _ => true
  | _ => false
  end.

Local Fixpoint ssa_i32_term (t : term sop) : bool :=
  match t with
  | TVar _ => true
  | TApp o args => ssa_i32_operator o && forallb ssa_i32_term args
  end.

Local Lemma ssa_i32_operation_result ext o cs v :
  ssa_i32_operator o = true -> op_eval ext o cs = Some v ->
  exists z, v = VInt W32 z /\ (0 <= z < 4294967296)%Z.
Proof.
  destruct o as [c|w operation| | | |tag]; cbn [ssa_i32_operator]; try discriminate.
  - destruct c as [[|] z|b off|f|z|z]; try discriminate.
    intros Hoperator Heval; destruct cs; cbn [op_eval] in Heval; [|discriminate].
    injection Heval as <-; exists (word_wrap W32 z); split; [reflexivity|].
    exact (word_wrap_valid W32 z).
  - destruct w; [|discriminate]; intros Hoperator Heval.
    destruct cs as [|first rest]; [discriminate|].
    destruct first as [wa a|block offset|f|bits|bits]; try discriminate.
    destruct rest as [|second rest]; [discriminate|].
    destruct second as [wb b|block offset|f|bits|bits]; try discriminate.
    destruct rest as [|extra rest]; [|discriminate].
    cbn [op_eval] in Heval.
    destruct (iw_eq_dec W32 wa) as [Hwa|Hwa]; [subst wa|discriminate].
    destruct (iw_eq_dec W32 wb) as [Hwb|Hwb]; [subst wb|discriminate].
    destruct (word_ok W32 a && word_ok W32 b); [|discriminate].
    pose proof (bin_eval_type W32 operation a b v Heval) as Htype.
    pose proof (bin_eval_valid W32 operation a b v Heval) as Hvalid.
    destruct operation; cbn [bin_result] in Htype;
      destruct v as [[|] z|block offset|f|bits|bits]; try discriminate.
    all: exists z; split; [reflexivity|exact Hvalid].
Qed.

Local Lemma ssa_i32_term_result ext env t v :
  ok_i32 env -> ssa_i32_term t = true -> denote (op_eval ext) env t = Some v ->
  exists z, v = VInt W32 z /\ (0 <= z < 4294967296)%Z.
Proof.
  intros Henv Hterm Heval; destruct t as [i|o args].
  - destruct (Henv i) as [z [Hget Hrange]].
    change (env i = Some v) in Heval; rewrite Hget in Heval; injection Heval as <-; eauto.
  - apply andb_true_iff in Hterm; destruct Hterm as [Hoperator Hchildren].
    rewrite denote_app in Heval.
    destruct (denote_args (op_eval ext) env args); [|discriminate].
    eapply ssa_i32_operation_result; [exact Hoperator|exact Heval].
Qed.

(** The demonstration term is the rule's multiplication-by-one left pattern. *)
Definition mul_one_term : term sop :=
  TApp (OBin W32 BMul) [TVar 0; TApp (OConst (VInt W32 1)) []].

(** The guard admits precisely terms built from variables, 32-bit constants and arithmetic. *)
Definition mul_one_rules : list (rewrite_rule sop) :=
  [RewriteRule mul_one_term (TVar 0) (fun sub => ssa_i32_term (sub 0))].

(** Every operator occurrence contributes one unit to the materialized tree objective. *)
Definition unit_cost : sop -> nat := fun _ => 1.

(** The guarded multiplication rule preserves the full result, including undefined evaluation. *)
Theorem mul_one_rules_sound (ext : nat -> list cval -> option cval) :
  Forall (rule_sound (op_eval ext) ok_i32) mul_one_rules.
Proof.
  constructor; [|constructor]; intros sub Hguard env Henv.
  change (denote (op_eval ext) env
    (TApp (OBin W32 BMul) [sub 0; TApp (OConst (VInt W32 1)) []]) =
    denote (op_eval ext) env (sub 0)).
  rewrite denote_binary.
  change (match denote (op_eval ext) env (sub 0) with
    | Some v => op_eval ext (OBin W32 BMul) [v; VInt W32 1]
    | None => None
    end = denote (op_eval ext) env (sub 0)).
  destruct (denote (op_eval ext) env (sub 0)) as [v|] eqn:Heval; [|reflexivity].
  destruct (ssa_i32_term_result ext env (sub 0) v Henv Hguard Heval) as [z [-> Hrange]].
  assert (Hword : word_ok W32 z = true) by (apply word_ok_valid; exact Hrange).
  cbn [op_eval]; rewrite Hword; cbn [bin_eval].
  rewrite Z.mul_1_r; unfold word_wrap; rewrite Z.mod_small by exact Hrange; reflexivity.
Qed.

(** * Numeric and dominated-guard clients *)

Local Definition ssa_numeric_problem ext P f :=
  numeric_problem const_numeric const_conc ssa_bridge TAny (ssa_block_view ext P f)
    (values_of P f) (fun _ => TAny).

Local Lemma ssa_numeric_laws ext :
  sparse_domain_laws (sparse_of_numeric const_numeric const_conc ssa_bridge TAny)
    ssa_truth (op_eval ext).
Proof.
  apply sparse_of_numeric_laws.
  - apply tagged_numeric_laws, const_word_laws.
  - apply ssa_bridge_laws.
  - intros w z Hword. exact I.
  - reflexivity.
Qed.

Local Lemma ssa_numeric_coverage ext P f s x c :
  wf_program ext P -> reachable_state (activation ext P f) s ->
  val (ssa_block_view ext P f) s x = Some c -> In x (values_of P f).
Proof.
  intros Hwf Hreachable Hval.
  pose proof (proj1 (activation_reachable_good ext P f s Hwf Hreachable) x c Hval) as Htyped.
  exact (ExamplesSsaViews.ssa_static_value P f x (ty_of c) (proj1 Htyped)).
Qed.

Local Lemma ssa_numeric_initial_origin ext P f s x c :
  wf_program ext P -> initial (activation ext P f) s ->
  val (ssa_block_view ext P f) s x = Some c ->
  def (ssa_block_view ext P f) x = Arbitrary \/
    exists b i, def (ssa_block_view ext P f) x = Param b i /\
      In b (Graph.entries (cfg (base (ssa_block_view ext P f)))).
Proof.
  intros Hwf [fd [b [cs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]] Hval.
  change (env x = Some c) in Hval.
  assert (Hin : In x (map fst (bparams b))).
  { destruct (in_dec Nat.eq_dec x (map fst (bparams b))) as [Hin|Houtside]; [exact Hin|].
    rewrite (ssa_bind_frame _ _ _ _ _ Hbind Houtside) in Hval. discriminate. }
  apply in_map_iff in Hin. destruct Hin as [[y ty] [Hxy Hin]]. cbn in Hxy; subst y.
  apply In_nth_error in Hin. destruct Hin as [i Hnth].
  pose proof (ExamplesSsaViews.ssa_parameter_definition_at ext P f fd (fentry fd) b i x ty
    Hwf Hf Hb Hnth) as Hdef.
  destruct (FinSet.mem nat_encoding (fentry fd) (ExamplesSsaViews.ssa_call_targets P f)).
  - left. exact Hdef.
  - right. exists (fentry fd), i. split; [exact Hdef|].
    change (In (fentry fd) (ssa_entries P f)). unfold ssa_entries; rewrite Hf.
    left; reflexivity.
Qed.

Local Lemma ssa_numeric_initial ext P f sigma :
  wf_program ext P -> In f (map fst (funcs P)) ->
  post_solution (lift_bot_lattice (lat const_numeric))
    (sparse_system label_encoding var_encoding (ssa_numeric_problem ext P f)) sigma ->
  forall s, initial (activation ext P f) s ->
    sparse_invariant (ssa_numeric_problem ext P f) sigma s.
Proof.
  intros Hwf Hfunction Hpost s Hinitial. split.
  - exact (sparse_entry_block label_encoding var_encoding (activation ext P f)
      (ssa_numeric_problem ext P f) sigma (ssa_block_view_laws ext P f Hwf Hfunction)
      Hpost s Hinitial).
  - intros x c Hval.
    assert (Hreachable : reachable_state (activation ext P f) s).
    { exists s, []; split; [exact Hinitial|constructor]. }
    pose proof (ssa_numeric_coverage ext P f s x c Hwf Hreachable Hval) as Hx.
    destruct (ssa_numeric_initial_origin ext P f s x c Hwf Hinitial Hval)
      as [Harbitrary|[b [i [Hdef Hentry]]]].
    + exact (sparse_arbitrary_value label_encoding var_encoding (ssa_numeric_problem ext P f)
        sigma (ssa_numeric_laws ext) Hpost x c Hx Harbitrary).
    + assert (Hr : In (CEntryFact x) (SsaSystem.rows label_encoding
        (ssa_numeric_problem ext P f))).
      { apply (SsaSystem.value_row label_encoding (ssa_numeric_problem ext P f) x);
          [exact Hx|].
        unfold SsaSystem.value_rows. cbn [ssa_numeric_problem numeric_problem view].
        rewrite Hdef, (proj2 (FinSet.of_list_spec label_encoding b _) Hentry).
        left; reflexivity. }
      eapply (sparse_gamma_upper _ _ _ (Some TAny) _ c (ssa_numeric_laws ext)).
      * exact (sparse_row_bound label_encoding var_encoding (ssa_numeric_problem ext P f)
          sigma Hpost (CEntryFact x) Hr).
      * exact (top_sound (ssa_numeric_laws ext) c).
Qed.

(** The constant sparse analysis contains every reachable SSA activation binding. *)
Theorem ssa_sccp_sound (ext : nat -> list cval -> option cval) (P : program) (f : func)
    (sigma : sparse_unknown label ssa_edge vid -> lift_bot (tagged (flat Z))) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  post_solution (lift_bot_lattice (lat const_numeric))
    (sparse_system label_encoding var_encoding
       (numeric_problem const_numeric const_conc ssa_bridge TAny
         (ssa_block_view ext P f) (values_of P f) (fun _ => TAny))) sigma ->
  forall s x c, reachable_state (activation ext P f) s ->
    val (ssa_block_view ext P f) s x = Some c ->
    gamma (lift_bot_gamma (fact_conc (sparse_of_numeric const_numeric const_conc ssa_bridge TAny)))
      (sigma (UVal x)) c.
Proof.
  intros Hwf Hfunction Hpost s x c [s0 [tr [Hstart Hrun]]].
  assert (Hreachable : reachable_state (activation ext P f) s0).
  { exists s0, []; split; [exact Hstart|constructor]. }
  pose proof (ssa_numeric_initial ext P f sigma Hwf Hfunction Hpost s0 Hstart) as Hinv.
  assert (Hfinal : sparse_invariant (ssa_numeric_problem ext P f) sigma s).
  { clear Hstart. revert Hreachable Hinv.
    induction Hrun as [a|a events a' rest t Hstep Hrun IH]; intros Hreachable Hinv.
    - exact Hinv.
    - apply IH.
      + eapply reachable_state_step; eassumption.
      + eapply (sparse_invariant_step label_encoding var_encoding (activation ext P f)
          (ssa_numeric_problem ext P f) sigma
          (ssa_block_view_laws ext P f Hwf Hfunction) (ssa_numeric_laws ext));
          [intros a0 y d; apply ssa_numeric_coverage; exact Hwf|exact Hpost|
            exact Hreachable|exact Hstep|exact Hinv]. }
  exact (proj2 Hfinal x c).
Qed.

(** Every dominating SSA branch condition remains true at the current reachable block. *)
Theorem ssa_guard_chain_sound (ext : nat -> list cval -> option cval) (P : program)
    (f : func) (s : astate) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_state (activation ext P f) s ->
  Forall (cond_holds (ssa_block_view ext P f) s)
    (guard_chain (ssa_block_view ext P f) label_encoding
      (point (base (ssa_block_view ext P f)) s)).
Proof.
  intros Hwf Hfunction Hreachable.
  exact (guard_chain_holds (activation ext P f) (ssa_block_view ext P f) label_encoding
    (ssa_block_view_laws ext P f Hwf Hfunction) (ssa_strict_laws ext P f Hwf Hfunction)
    s Hreachable).
Qed.

(** * Full-machine pointer analyses *)

Section SsaPointerWrappers.
Context (ext : nat -> list cval -> option cval) (P : program) (lim : limits).

(** Every recognized SSA pointer and stored pointer belongs to any inclusion post-solution. *)
Theorem ssa_andersen_sound (sigma : pts_key vid vid -> pts_set var_encoding (ssa_ptr_ops P)) :
  wf_program ext P ->
  post_solution (pts_lattice var_encoding (ssa_ptr_ops P))
    (andersen_system var_encoding var_encoding (ssa_ptr_ops P)) sigma ->
  forall s, reachable_state (ssa_semantics ext P lim) s ->
    (forall x t, pts_of (ssa_ptr_view ext P lim) s x = Some t ->
      fmem var_encoding t (sigma (PVal x)) = true) /\
    (forall t0 t, heap_pts (ssa_ptr_view ext P lim) s t0 t ->
      fmem var_encoding t (sigma (PHeap t0)) = true).
Proof.
  intros Hwf Hpost s Hreach.
  destruct (relational_andersen_sound (ssa_semantics ext P lim) (ssa_rel_ptr_view P)
    var_encoding var_encoding (ssa_ptr_ops P) sigma
    (ssa_rel_ptr_laws ext P lim (ssa_ptr_ops P) Hwf (fun _ Hin => Hin)) Hpost s Hreach)
    as [Hvalues Hheap].
  split.
  - intros x t Hpts; apply Hvalues; eapply ssa_rel_value_covers; eassumption.
  - intros t0 t Hpts; apply Hheap; eapply ssa_rel_heap_covers; eassumption.
Qed.

(** SSA values pointing into one site have unified Steensgaard pointee classes. *)
Theorem ssa_steensgaard_sound :
  wf_program ext P ->
  forall s x y t, reachable_state (ssa_semantics ext P lim) s ->
    pts_of (ssa_ptr_view ext P lim) s x = Some t ->
    pts_of (ssa_ptr_view ext P lim) s y = Some t ->
    may_alias (steensgaard var_encoding var_encoding (ssa_ptr_ops P)) x y.
Proof.
  intros Hwf s x y t Hreach Hx Hy.
  destruct (ssa_andersen_sound (andersen_delta var_encoding var_encoding (ssa_ptr_ops P))
    Hwf (proj1 (andersen_delta_least var_encoding var_encoding (ssa_ptr_ops P))) s Hreach)
    as [Hvalues Hheap].
  eapply steensgaard_coarser; [apply andersen_delta_least|apply Hvalues; exact Hx|
    apply Hvalues; exact Hy].
Qed.

(** Actual escaping values and their stored pointers belong to the computed least closure. *)
Theorem ssa_escape_sound (sigma : pts_key vid vid -> pts_set var_encoding (ssa_ptr_ops P)) :
  wf_program ext P ->
  post_solution (pts_lattice var_encoding (ssa_ptr_ops P))
    (andersen_system var_encoding var_encoding (ssa_ptr_ops P)) sigma ->
  forall s x t t', reachable_state (ssa_semantics ext P lim) s ->
    In (PEscape x) (pop (ssa_ptr_view ext P lim) s) ->
    pts_of (ssa_ptr_view ext P lim) s x = Some t ->
    FinSet.mem var_encoding t (escaped_sites var_encoding (ssa_ptr_ops P) sigma) = true /\
    (heap_pts (ssa_ptr_view ext P lim) s t t' ->
      FinSet.mem var_encoding t' (escaped_sites var_encoding (ssa_ptr_ops P) sigma) = true).
Proof.
  intros Hwf Hpost s x t t' Hreach Hescape Hpts.
  destruct (ssa_andersen_sound sigma Hwf Hpost s Hreach) as [Hvalues Hheap].
  assert (Hroot : FinSet.mem var_encoding t (escaped_sites var_encoding (ssa_ptr_ops P) sigma)
    = true).
  { eapply escaped_sites_root.
    - exact (ssa_ptr_pop_listed ext P lim (ssa_ptr_ops P) Hwf (fun _ Hin => Hin)
        s (PEscape x) Hreach Hescape).
    - apply Hvalues; exact Hpts. }
  split; [exact Hroot|].
  intro Hstored; eapply escaped_sites_step; [exact Hroot|apply Hheap; exact Hstored].
Qed.

End SsaPointerWrappers.
