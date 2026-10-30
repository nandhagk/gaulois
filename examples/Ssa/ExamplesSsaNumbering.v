(** * Concrete SSA value-numbering observations

    These clients connect checked symbolic classes to actual activation histories.
    For example, two separately bound additions agree at a later dominated use.
    Builds on: ExamplesSsaAnalysisBase, ExamplesSsaStrict and AnalysesNumbering. *)

From Stdlib Require Import List Bool Arith Lia ZArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphDominators.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsSsaPoints ViewsDominated.
From Gaulois.Analyses Require Import AnalysesNumbering.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping ExamplesSsaSemantics
  ExamplesSsaTypingProofs ExamplesSsaBridge ExamplesSsaActivation ExamplesSsaViews
  ExamplesSsaStrict ExamplesSsaAnalysisBase.
Import List.ListNotations.
Local Open Scope nat_scope.

(** The toy purity predicate excludes exactly external operations. *)
Definition gvn_pure (o : sop) : bool :=
  match o with
  | OExt _ => false
  | _ => true
  end.

Local Definition gvn_zero : cval := VInt W32 0%Z.
Local Definition gvn_one : cval := VInt W32 1%Z.
Local Definition gvn_no_ext : nat -> list cval -> option cval := fun _ _ => None.

Local Lemma gvn_checked P : ext_sigs P = [] -> wf_check P = true -> wf_program gvn_no_ext P.
Proof.
  intros Hext Hcheck; apply wf_check_sound; [apply ext_respects_nil; exact Hext|exact Hcheck].
Qed.

Local Lemma gvn_dominates P d n : wf_program gvn_no_ext P ->
  In 0 (map fst (funcs P)) ->
  dominates_b label_encoding (dominator_tree (prepare label_encoding (ssa_block_graph P 0)))
    d n = true -> dominates (ssa_block_graph P 0) d n.
Proof.
  intros Hwf Hmain Hchecked.
  pose proof (ssa_refined_point_laws gvn_no_ext P 0 Hwf Hmain) as Hpoints.
  pose proof (prepare_ready label_encoding (ssa_block_graph P 0)
    (blocks_graph_wf Hpoints) (blocks_out_nodup Hpoints)) as Hready.
  exact (proj1 (proj2 (proj2 (dominator_tree_sound _ _ _ Hready))) d n Hchecked).
Qed.

Local Lemma gvn_step_support P f s tr t : step (activation gvn_no_ext P f) s tr t ->
  support_le (aenv s) (aenv t).
Proof.
  intro Hstep; inversion Hstep; subst; cbn [activation_advance activation_enter aenv];
    try apply env_set_support; try (intros z d Hd; exists d; exact Hd).
  all: match goal with
    | H : jump_env _ _ _ _ = Some _ |- _ =>
      exact (proj1 (jump_env_support _ _ _ _ _ H))
    end.
Qed.

(** Actual source operations give the pure-binding law, including preservation of definedness. *)
Local Lemma gvn_pure_bindings P f : wf_program gvn_no_ext P -> In f (map fst (funcs P)) ->
  numbering_loop_laws (activation gvn_no_ext P f)
    (NumberingProblem (ssa_block_view gvn_no_ext P f) gvn_pure (values_of P f)).
Proof.
  intros Hwf Hmain; constructor; intros s tr t x o args Hr Hstep Hdef Hp Hchanged.
  pose proof (ssa_block_view_laws gvn_no_ext P f Hwf Hmain) as Hssa.
  change (aenv t x <> aenv s x) in Hchanged.
  destruct (aenv t x) as [c|] eqn:Hpost.
  - destruct (value_origin Hssa s tr t x c Hr Hstep Hpost) as [Hsame|Horigin].
    + change (aenv s x = Some c) in Hsame; exfalso; apply Hchanged; congruence.
    + destruct Horigin as [[o' [args' [cs [Hdef' [Hargs Heval]]]]]|[Hparam|Harbitrary]].
      * change (def (ssa_block_view gvn_no_ext P f) x = Op o args) in Hdef.
        rewrite Hdef in Hdef'; injection Hdef' as <- <-.
        exists cs, c; repeat split; assumption.
      * destruct Hparam as [e [b [i [z [Hparam _]]]]].
        change (def (ssa_block_view gvn_no_ext P f) x = Op o args) in Hdef.
        rewrite Hdef in Hparam; discriminate.
      * change (def (ssa_block_view gvn_no_ext P f) x = Op o args) in Hdef.
        rewrite Hdef in Harbitrary; discriminate.
  - destruct (aenv s x) as [c|] eqn:Hpre.
    + destruct (gvn_step_support P f s tr t Hstep x c Hpre) as [d Hd].
      rewrite Hpost in Hd; discriminate.
    + exfalso; apply Hchanged; congruence.
Qed.

(** * Two separately executed additions *)

(** The original two-block program computes the same addition at two distinct binding sites. *)
Definition gvn_prog : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32); (1, TyI32)] [IOp 2 (OBin W32 BAdd) [0; 1]] (TJump 1 []));
     (1, SBlock [] [IOp 3 (OBin W32 BAdd) [0; 1]; IOutput 3] (TRet 3))] TyI32)] 0 [].

Definition gvn_first : vid := 2.
Definition gvn_second : vid := 3.

(** The adapter retains the source view, purity predicate and complete source inventory. *)
Definition gvn_problem : numbering_problem astate event label ssa_edge vid sop cval :=
  NumberingProblem (ssa_block_view gvn_no_ext gvn_prog 0) gvn_pure (values_of gvn_prog 0).

Local Definition gvn_arguments : vid -> option cval :=
  env_set (env_set (fun _ => None) 0 gvn_zero) 1 gvn_zero.
Local Definition gvn_start := AState 0 0 gvn_arguments.
Local Definition gvn_first_state :=
  activation_advance gvn_start (env_set (aenv gvn_start) gvn_first gvn_zero).
Local Definition gvn_second_start := activation_enter 1 (aenv gvn_first_state).

(** Both additions have been independently bound by their actual instruction steps. *)
Definition gvn_binding_state : astate :=
  activation_advance gvn_second_start (env_set (aenv gvn_second_start) gvn_second gvn_zero).

(** All four values are ready; operation operands have rank zero and the two results rank one. *)
Definition gvn_binding_observation : numbering_observation unit astate label ssa_edge vid :=
  NumberingObservation (fun _ => gvn_binding_state) (fun _ x => In x [0; 1; 2; 3])
    (fun _ x => if Nat.ltb x 2 then 0 else 1) (fun _ _ => None).

Local Lemma gvn_wf : wf_program gvn_no_ext gvn_prog.
Proof.
  apply gvn_checked; [reflexivity|vm_compute; reflexivity].
Qed.

Local Lemma gvn_start_initial : initial (activation gvn_no_ext gvn_prog 0) gvn_start.
Proof.
  unfold activation, activation_initial; cbn [initial].
  exists (FDef 0
    [(0, SBlock [(0, TyI32); (1, TyI32)] [IOp 2 (OBin W32 BAdd) [0; 1]] (TJump 1 []));
     (1, SBlock [] [IOp 3 (OBin W32 BAdd) [0; 1]; IOutput 3] (TRet 3))] TyI32),
    (SBlock [(0, TyI32); (1, TyI32)] [IOp 2 (OBin W32 BAdd) [0; 1]] (TJump 1 [])),
    [gvn_zero; gvn_zero], gvn_arguments.
  repeat split; try reflexivity; repeat constructor; cbn [gvn_zero valid_cval]; lia.
Qed.

Local Lemma gvn_first_step : step (activation gvn_no_ext gvn_prog 0) gvn_start [] gvn_first_state.
Proof.
  apply (AOp gvn_no_ext gvn_prog 0 gvn_start 2 (OBin W32 BAdd) [0; 1]
    [gvn_zero; gvn_zero] gvn_zero).
  - unfold at_instr; eexists; eexists; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Local Lemma gvn_jump_step :
  step (activation gvn_no_ext gvn_prog 0) gvn_first_state [] gvn_second_start.
Proof.
  apply (AJump gvn_no_ext gvn_prog 0 gvn_first_state 1 [] [] (aenv gvn_first_state)).
  - unfold at_term; eexists; eexists; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Local Lemma gvn_second_step :
  step (activation gvn_no_ext gvn_prog 0) gvn_second_start [] gvn_binding_state.
Proof.
  apply (AOp gvn_no_ext gvn_prog 0 gvn_second_start 3 (OBin W32 BAdd) [0; 1]
    [gvn_zero; gvn_zero] gvn_zero).
  - unfold at_instr; eexists; eexists; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The concrete observation equations hold without assuming the two result values equal. *)
Theorem gvn_binding_observation_laws :
  numbering_observation_laws (activation (fun _ _ => None) gvn_prog 0)
    gvn_problem gvn_binding_observation.
Proof.
  constructor.
  - intros [] x o args c Hready Hdef Hp Hval.
    change (In x [0; 1; 2; 3]) in Hready.
    destruct Hready as [<-|[<-|[<-|[<-|Hnone]]]]; try contradiction;
      vm_compute in Hdef; try discriminate; injection Hdef as <- <-;
      change (Some gvn_zero = Some c) in Hval; injection Hval as <-.
    all: exists [gvn_zero; gvn_zero]; split; [|reflexivity].
    all: constructor; [repeat split; cbn; tauto || lia || reflexivity|];
      constructor; [repeat split; cbn; tauto || lia || reflexivity|constructor].
  - intros [] x b i c Hready Hdef Hentry Hval.
    change (In x [0; 1; 2; 3]) in Hready.
    destruct Hready as [<-|[<-|[<-|[<-|Hnone]]]]; try contradiction;
      vm_compute in Hdef; try discriminate; injection Hdef as <- <-;
      exfalso; apply Hentry; left; reflexivity.
Qed.

(** The binding witness supplies independent values, readiness and the actual preceding step. *)
Theorem gvn_binding_witness :
  observation_state gvn_binding_observation tt = gvn_binding_state /\
  observation_ready gvn_binding_observation tt gvn_first /\
  observation_ready gvn_binding_observation tt gvn_second /\
  exists s l c d, reachable_state (activation (fun _ _ => None) gvn_prog 0) s /\
    step (activation (fun _ _ => None) gvn_prog 0) s l gvn_binding_state /\
    val (nsv gvn_problem) gvn_binding_state gvn_second = Some c /\
    val (nsv gvn_problem) s gvn_second <> Some c /\
    val (nsv gvn_problem) gvn_binding_state gvn_first = Some d.
Proof.
  split; [reflexivity|split; [cbn; tauto|split; [cbn; tauto|]]].
  exists gvn_second_start, [], gvn_zero, gvn_zero; split.
  - exists gvn_start, []; split; [exact gvn_start_initial|].
    exact (exec_step _ [] _ [] _ gvn_first_step
      (exec_step _ [] _ [] _ gvn_jump_step (exec_refl _))).
  - split; [exact gvn_second_step|split; [reflexivity|split; [discriminate|reflexivity]]].
Qed.

(** The first computation home strictly dominates the second one. *)
Theorem gvn_binding_home_dominates :
  strictly_dominates (cfg (base (nsv gvn_problem)))
    (home (nsv gvn_problem) gvn_first) (home (nsv gvn_problem) gvn_second).
Proof.
  split.
  - apply (gvn_dominates gvn_prog 0 1 gvn_wf); [left; reflexivity|vm_compute; reflexivity].
  - discriminate.
Qed.

Local Lemma gvn_representatives :
  dominator_numbering label_encoding var_encoding sop_encoding gvn_problem gvn_second =
    dominator_numbering label_encoding var_encoding sop_encoding gvn_problem gvn_first.
Proof.
  vm_compute; reflexivity.
Qed.

(** Generic binding soundness identifies the two independently witnessed concrete results. *)
Theorem gvn_binding_equal :
  exists c d, val (nsv gvn_problem) gvn_binding_state gvn_second = Some c /\
    val (nsv gvn_problem) gvn_binding_state gvn_first = Some d /\ c = d.
Proof.
  destruct gvn_binding_witness as [_ [Hrfirst [Hrsecond
    [s [l [c [d [Hreachable [Hstep [Hsecond [Hnew Hfirst]]]]]]]]]]].
  assert (Hequal : val (nsv gvn_problem) gvn_binding_state gvn_first = Some c).
  { eapply (numbering_check_sound (activation gvn_no_ext gvn_prog 0)
      label_encoding var_encoding sop_encoding gvn_problem gvn_binding_observation
      (dominator_numbering label_encoding var_encoding sop_encoding gvn_problem));
      [apply ssa_block_view_laws; [exact gvn_wf|left; reflexivity]|
       apply ssa_strict_laws; [exact gvn_wf|left; reflexivity]|
       exact gvn_binding_observation_laws|apply dominator_numbering_checked|
       exact gvn_representatives|exact Hreachable|exact Hstep|
       cbn; tauto|cbn; tauto|exact Hsecond|exact Hnew|left;
       exact gvn_binding_home_dominates|].
    exists tt, d; repeat split; assumption || reflexivity. }
  exists c, d; repeat split; try assumption; congruence.
Qed.

(** * A third, strictly dominated use block *)

(** A separate block after both additions makes both home-dominance premises strict. *)
Definition gvn_use_prog : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32); (1, TyI32)] [IOp 2 (OBin W32 BAdd) [0; 1]] (TJump 1 []));
     (1, SBlock [] [IOp 3 (OBin W32 BAdd) [0; 1]] (TJump 2 []));
     (2, SBlock [] [IOutput 3] (TRet 3))] TyI32)] 0 [].

Definition gvn_use_problem : numbering_problem astate event label ssa_edge vid sop cval :=
  NumberingProblem (ssa_block_view gvn_no_ext gvn_use_prog 0) gvn_pure
    (values_of gvn_use_prog 0).

(** The use observes the source environment after the second jump. *)
Definition gvn_use_state : astate := activation_enter 2 (aenv gvn_binding_state).

Definition gvn_use_observation : numbering_observation unit astate label ssa_edge vid :=
  NumberingObservation (fun _ => gvn_use_state) (fun _ x => In x [0; 1; 2; 3])
    (fun _ x => if Nat.ltb x 2 then 0 else 1) (fun _ _ => None).

Local Lemma gvn_use_wf : wf_program gvn_no_ext gvn_use_prog.
Proof.
  apply gvn_checked; [reflexivity|vm_compute; reflexivity].
Qed.

(** The dominated-use observation supplies its own local operation equations. *)
Theorem gvn_use_observation_laws :
  numbering_observation_laws (activation (fun _ _ => None) gvn_use_prog 0)
    gvn_use_problem gvn_use_observation.
Proof.
  constructor.
  - intros [] x o args c Hready Hdef Hp Hval.
    change (In x [0; 1; 2; 3]) in Hready.
    destruct Hready as [<-|[<-|[<-|[<-|Hnone]]]]; try contradiction;
      vm_compute in Hdef; try discriminate; injection Hdef as <- <-;
      change (Some gvn_zero = Some c) in Hval; injection Hval as <-.
    all: exists [gvn_zero; gvn_zero]; split; [|reflexivity].
    all: constructor; [repeat split; cbn; tauto || lia || reflexivity|];
      constructor; [repeat split; cbn; tauto || lia || reflexivity|constructor].
  - intros [] x b i c Hready Hdef Hentry Hval.
    change (In x [0; 1; 2; 3]) in Hready.
    destruct Hready as [<-|[<-|[<-|[<-|Hnone]]]]; try contradiction;
      vm_compute in Hdef; try discriminate; injection Hdef as <- <-;
      exfalso; apply Hentry; left; reflexivity.
Qed.

Local Lemma gvn_use_reachable : reachable_state (activation gvn_no_ext gvn_use_prog 0)
  gvn_use_state.
Proof.
  exists gvn_start, []; split.
  - unfold activation, activation_initial; cbn [initial].
    eexists; eexists; exists [gvn_zero; gvn_zero], gvn_arguments.
    repeat split; try reflexivity; repeat constructor; cbn [gvn_zero valid_cval]; lia.
  - eapply exec_step with (l := []) (s' := gvn_first_state); [|].
    + apply (AOp gvn_no_ext gvn_use_prog 0 gvn_start 2 (OBin W32 BAdd) [0; 1]
        [gvn_zero; gvn_zero] gvn_zero); try reflexivity.
      unfold at_instr; eexists; eexists; repeat split; reflexivity.
    + eapply exec_step with (l := []) (s' := gvn_second_start).
      * apply (AJump gvn_no_ext gvn_use_prog 0 gvn_first_state 1 [] []
          (aenv gvn_first_state)); try reflexivity.
        unfold at_term; eexists; eexists; repeat split; reflexivity.
      * eapply exec_step with (l := []) (s' := gvn_binding_state).
        -- apply (AOp gvn_no_ext gvn_use_prog 0 gvn_second_start 3 (OBin W32 BAdd) [0; 1]
             [gvn_zero; gvn_zero] gvn_zero); try reflexivity.
           unfold at_instr; eexists; eexists; repeat split; reflexivity.
        -- eapply exec_step with (l := []) (s' := gvn_use_state); [|constructor].
           apply (AJump gvn_no_ext gvn_use_prog 0 gvn_binding_state 2 [] []
             (aenv gvn_binding_state)); try reflexivity.
           unfold at_term; eexists; eexists; repeat split; reflexivity.
Qed.

(** Actual execution reaches a third block with both values ready, defined and strictly
    dominated. *)
Theorem gvn_use_witness :
  reachable_state (activation (fun _ _ => None) gvn_use_prog 0) gvn_use_state /\
  observation_state gvn_use_observation tt = gvn_use_state /\
  observation_ready gvn_use_observation tt gvn_first /\
  observation_ready gvn_use_observation tt gvn_second /\
  strictly_dominates (cfg (base (nsv gvn_use_problem)))
    (home (nsv gvn_use_problem) gvn_first) (point (base (nsv gvn_use_problem)) gvn_use_state) /\
  strictly_dominates (cfg (base (nsv gvn_use_problem)))
    (home (nsv gvn_use_problem) gvn_second) (point (base (nsv gvn_use_problem)) gvn_use_state) /\
  (exists c, val (nsv gvn_use_problem) gvn_use_state gvn_first = Some c) /\
  (exists d, val (nsv gvn_use_problem) gvn_use_state gvn_second = Some d).
Proof.
  split; [exact gvn_use_reachable|split; [reflexivity|split; [cbn; tauto|split;
    [cbn; tauto|split]]]].
  - split; [apply (gvn_dominates gvn_use_prog 0 2 gvn_use_wf);
      [left; reflexivity|vm_compute; reflexivity]|discriminate].
  - split.
    + split; [apply (gvn_dominates gvn_use_prog 1 2 gvn_use_wf);
        [left; reflexivity|vm_compute; reflexivity]|discriminate].
    + split; exists gvn_zero; reflexivity.
Qed.

(** The dominated-use equality follows from the generic soundness theorem and independent
    witness. *)
Theorem gvn_use_equal :
  exists c, val (nsv gvn_use_problem) gvn_use_state gvn_first = Some c /\
    val (nsv gvn_use_problem) gvn_use_state gvn_second = Some c.
Proof.
  destruct gvn_use_witness as [Hr [Hstate [Hfirst [Hsecond [Hd1 [Hd2 [[c Hc] [d Hd]]]]]]]].
  eapply (numbering_use_sound (activation gvn_no_ext gvn_use_prog 0)
    label_encoding var_encoding sop_encoding gvn_use_problem gvn_use_observation
    (dominator_numbering label_encoding var_encoding sop_encoding gvn_use_problem));
    [apply ssa_block_view_laws; [exact gvn_use_wf|left; reflexivity]|
     apply ssa_strict_laws; [exact gvn_use_wf|left; reflexivity]|
     exact gvn_use_observation_laws|apply dominator_numbering_checked|
     vm_compute; reflexivity|exact Hr|cbn; tauto|cbn; tauto|exact Hd1|exact Hd2|].
  exists tt, c, d; repeat split; assumption.
Qed.

(** * A cyclic two-position phi class with finite incoming histories *)

(** Two loop parameters receive the same entry seed and carry themselves on the back edge. *)
Definition gvn_phi_prog : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32)] [IOp 1 (OConst gvn_one) []] (TJump 1 [0; 0; 1]));
     (1, SBlock [(3, TyI32); (4, TyI32); (5, TyI32)] [IOp 6 (OConst gvn_zero) []]
       (TBr 5 1 [3; 4; 6] 2 []));
     (2, SBlock [] [IOutput 3] (TRet 4))] TyI32)] 0 [].

Definition gvn_phi_problem : numbering_problem astate event label ssa_edge vid sop cval :=
  NumberingProblem (ssa_block_view gvn_no_ext gvn_phi_prog 0) gvn_pure
    (values_of gvn_phi_prog 0).

Definition gvn_phi_left : vid := 3.
Definition gvn_phi_right : vid := 4.

Local Definition gvn_phi_initial := AState 0 0 (env_set (fun _ => None) 0 gvn_zero).
Local Definition gvn_phi_entry_source :=
  activation_advance gvn_phi_initial (env_set (aenv gvn_phi_initial) 1 gvn_one).
Local Definition gvn_phi_first_header := activation_enter 1
  (env_set (env_set (env_set (aenv gvn_phi_entry_source) 3 gvn_zero) 4 gvn_zero) 5 gvn_one).
Local Definition gvn_phi_back_source :=
  activation_advance gvn_phi_first_header (env_set (aenv gvn_phi_first_header) 6 gvn_zero).
Local Definition gvn_phi_second_header := activation_enter 1
  (env_set (env_set (env_set (aenv gvn_phi_back_source) 3 gvn_zero) 4 gvn_zero) 5 gvn_zero).
Local Definition gvn_phi_exit_source :=
  activation_advance gvn_phi_second_header (env_set (aenv gvn_phi_second_header) 6 gvn_zero).
Local Definition gvn_phi_exit := activation_enter 2 (aenv gvn_phi_exit_source).
Local Definition gvn_phi_entry_edge := SsaEdge 0 1 0.
Local Definition gvn_phi_back_edge := SsaEdge 1 1 0.

(** Three contexts record the entry predecessor, the first back edge and the dominated exit. *)
Definition gvn_phi_observation : numbering_observation nat astate label ssa_edge vid :=
  NumberingObservation
    (fun h => match h with
      | 0 => gvn_phi_entry_source
      | 1 => gvn_phi_back_source
      | 2 => gvn_phi_exit
      | _ => gvn_phi_initial
      end)
    (fun h x => match h with
      | 0 => In x [0; 1]
      | 1 | 2 => In x [0; 1; 3; 4; 5; 6]
      | _ => False
      end)
    (fun h x => if Nat.eqb x 3 || Nat.eqb x 4 || Nat.eqb x 5 then h else 0)
    (fun h b => if Nat.eqb b 1 then match h with
      | 1 => Some (gvn_phi_entry_edge, 0)
      | 2 => Some (gvn_phi_back_edge, 1)
      | _ => None
      end else None).

Local Lemma gvn_phi_wf : wf_program gvn_no_ext gvn_phi_prog.
Proof.
  apply gvn_checked; [reflexivity|vm_compute; reflexivity].
Qed.

Local Lemma gvn_phi_initial_ok : initial (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_initial.
Proof.
  unfold activation, activation_initial; cbn [initial].
  eexists; eexists; exists [gvn_zero], (aenv gvn_phi_initial).
  repeat split; try reflexivity; repeat constructor; cbn [gvn_zero valid_cval]; lia.
Qed.

Local Lemma gvn_phi_seed_step :
  step (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_initial [] gvn_phi_entry_source.
Proof.
  apply (AOp gvn_no_ext gvn_phi_prog 0 gvn_phi_initial 1 (OConst gvn_one) [] [] gvn_one);
    try reflexivity.
  unfold at_instr; eexists; eexists; repeat split; reflexivity.
Qed.

Local Lemma gvn_phi_entry_step :
  step (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_entry_source [] gvn_phi_first_header.
Proof.
  apply (AJump gvn_no_ext gvn_phi_prog 0 gvn_phi_entry_source 1 [0; 0; 1]
    [gvn_zero; gvn_zero; gvn_one] (aenv gvn_phi_first_header)); try reflexivity.
  unfold at_term; eexists; eexists; repeat split; reflexivity.
Qed.

Local Lemma gvn_phi_first_zero_step :
  step (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_first_header [] gvn_phi_back_source.
Proof.
  apply (AOp gvn_no_ext gvn_phi_prog 0 gvn_phi_first_header 6 (OConst gvn_zero) [] [] gvn_zero);
    try reflexivity.
  unfold at_instr; eexists; eexists; repeat split; reflexivity.
Qed.

Local Lemma gvn_phi_back_step :
  step (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_back_source [] gvn_phi_second_header.
Proof.
  apply (ABranch gvn_no_ext gvn_phi_prog 0 gvn_phi_back_source 5 1 [3; 4; 6] 2 [] 1%Z
    1 [3; 4; 6] [gvn_zero; gvn_zero; gvn_zero] (aenv gvn_phi_second_header));
    try reflexivity.
  unfold at_term; eexists; eexists; repeat split; reflexivity.
Qed.

Local Lemma gvn_phi_second_zero_step :
  step (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_second_header [] gvn_phi_exit_source.
Proof.
  apply (AOp gvn_no_ext gvn_phi_prog 0 gvn_phi_second_header 6 (OConst gvn_zero) [] [] gvn_zero);
    try reflexivity.
  unfold at_instr; eexists; eexists; repeat split; reflexivity.
Qed.

Local Lemma gvn_phi_exit_step :
  step (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_exit_source [] gvn_phi_exit.
Proof.
  apply (ABranch gvn_no_ext gvn_phi_prog 0 gvn_phi_exit_source 5 1 [3; 4; 6] 2 [] 0%Z
    2 [] [] (aenv gvn_phi_exit_source)); try reflexivity.
  unfold at_term; eexists; eexists; repeat split; reflexivity.
Qed.

Local Lemma gvn_phi_entry_reachable :
  reachable_state (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_entry_source.
Proof.
  exists gvn_phi_initial, []; split; [exact gvn_phi_initial_ok|].
  exact (exec_step _ [] _ [] _ gvn_phi_seed_step (exec_refl _)).
Qed.

Local Lemma gvn_phi_first_history : exec (activation gvn_no_ext gvn_phi_prog 0)
  gvn_phi_first_header [] gvn_phi_back_source.
Proof.
  exact (exec_step _ [] _ [] _ gvn_phi_first_zero_step (exec_refl _)).
Qed.

Local Lemma gvn_phi_back_reachable :
  reachable_state (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_back_source.
Proof.
  eapply reachable_state_exec; [|exact gvn_phi_first_history].
  eapply reachable_state_step; [exact gvn_phi_entry_reachable|exact gvn_phi_entry_step].
Qed.

Local Lemma gvn_phi_second_history : exec (activation gvn_no_ext gvn_phi_prog 0)
  gvn_phi_second_header [] gvn_phi_exit.
Proof.
  exact (exec_step _ [] _ [] _ gvn_phi_second_zero_step
    (exec_step _ [] _ [] _ gvn_phi_exit_step (exec_refl _))).
Qed.

Local Lemma gvn_phi_exit_reachable :
  reachable_state (activation gvn_no_ext gvn_phi_prog 0) gvn_phi_exit.
Proof.
  eapply reachable_state_exec; [|exact gvn_phi_second_history].
  eapply reachable_state_step; [exact gvn_phi_back_reachable|exact gvn_phi_back_step].
Qed.

Local Lemma gvn_phi_entry_taken : taken (base (nsv gvn_phi_problem))
  gvn_phi_entry_source [] gvn_phi_first_header gvn_phi_entry_edge.
Proof.
  unfold taken, base, nsv, gvn_phi_problem, ssa_block_view; cbn.
  unfold ssa_block_taken; eexists; eexists; repeat split; try reflexivity; cbn; tauto.
Qed.

Local Lemma gvn_phi_back_taken : taken (base (nsv gvn_phi_problem))
  gvn_phi_back_source [] gvn_phi_second_header gvn_phi_back_edge.
Proof.
  unfold taken, base, nsv, gvn_phi_problem, ssa_block_view; cbn.
  unfold ssa_block_taken; eexists; eexists; repeat split; try reflexivity; cbn; tauto.
Qed.

(** Every ready phi reads its position on the actual shared entry or back-edge history. *)
Theorem gvn_phi_observation_laws :
  numbering_observation_laws (activation (fun _ _ => None) gvn_phi_prog 0)
    gvn_phi_problem gvn_phi_observation.
Proof.
  constructor.
  - intros h x o args c Hready Hdef Hp Hval.
    destruct h as [|[|[|h]]]; cbn [gvn_phi_observation observation_ready In] in Hready;
      try contradiction.
    all: repeat match type of Hready with
      | _ \/ _ => destruct Hready as [<-|Hready]
      end; try contradiction;
      vm_compute in Hdef; try discriminate; injection Hdef as <- <-;
      vm_compute in Hval; injection Hval as <-; exists [].
    all: split; apply Forall2_nil || reflexivity.
  - intros h x b i c Hready Hdef Hentry Hval.
    destruct h as [|[|[|h]]]; cbn [gvn_phi_observation observation_ready In] in Hready;
      try contradiction.
    all: repeat match type of Hready with
      | _ \/ _ => destruct Hready as [<-|Hready]
      end; try contradiction; vm_compute in Hdef; try discriminate; injection Hdef as <- <-;
      try (exfalso; apply Hentry; left; reflexivity);
      vm_compute in Hval; injection Hval as <-.
    + exists gvn_phi_entry_edge, 0, 0, [], gvn_phi_first_header, [].
      repeat split; try exact gvn_phi_entry_reachable; try exact gvn_phi_entry_step;
        try exact gvn_phi_entry_taken; try exact gvn_phi_first_history;
        vm_compute; tauto || lia || reflexivity.
    + exists gvn_phi_entry_edge, 0, 0, [], gvn_phi_first_header, [].
      repeat split; try exact gvn_phi_entry_reachable; try exact gvn_phi_entry_step;
        try exact gvn_phi_entry_taken; try exact gvn_phi_first_history;
        vm_compute; tauto || lia || reflexivity.
    + exists gvn_phi_entry_edge, 0, 1, [], gvn_phi_first_header, [].
      repeat split; try exact gvn_phi_entry_reachable; try exact gvn_phi_entry_step;
        try exact gvn_phi_entry_taken; try exact gvn_phi_first_history;
        vm_compute; tauto || lia || reflexivity.
    + exists gvn_phi_back_edge, 1, 3, [], gvn_phi_second_header, [].
      repeat split; try exact gvn_phi_back_reachable; try exact gvn_phi_back_step;
        try exact gvn_phi_back_taken; try exact gvn_phi_second_history;
        vm_compute; tauto || lia || reflexivity.
    + exists gvn_phi_back_edge, 1, 4, [], gvn_phi_second_header, [].
      repeat split; try exact gvn_phi_back_reachable; try exact gvn_phi_back_step;
        try exact gvn_phi_back_taken; try exact gvn_phi_second_history;
        vm_compute; tauto || lia || reflexivity.
    + exists gvn_phi_back_edge, 1, 6, [], gvn_phi_second_header, [].
      repeat split; try exact gvn_phi_back_reachable; try exact gvn_phi_back_step;
        try exact gvn_phi_back_taken; try exact gvn_phi_second_history;
        vm_compute; tauto || lia || reflexivity.
Qed.

(** Optimistic numbering accepts the actual cyclic two-position phi class. *)
Theorem gvn_phi_checked : numbering_check label_encoding var_encoding sop_encoding
  gvn_phi_problem
  (optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem) = true.
Proof.
  apply optimistic_numbering_checked.
Qed.

(** A finite unrolling retains both actual incoming edges and independently defined phi values. *)
Theorem gvn_phi_witness : exists h h' h'' e entry c d,
  def (nsv gvn_phi_problem) gvn_phi_left = Param 1 0 /\
  def (nsv gvn_phi_problem) gvn_phi_right = Param 1 1 /\
  observation_previous gvn_phi_observation h 1 = Some (e, h') /\
  observation_previous gvn_phi_observation h' 1 = Some (entry, h'') /\ e <> entry /\
  (exists seed, nth_error (edge_args (nsv gvn_phi_problem) entry) 0 = Some seed /\
    nth_error (edge_args (nsv gvn_phi_problem) entry) 1 = Some seed) /\
  nth_error (edge_args (nsv gvn_phi_problem) e) 0 = Some gvn_phi_left /\
  nth_error (edge_args (nsv gvn_phi_problem) e) 1 = Some gvn_phi_right /\
  observation_ready gvn_phi_observation h gvn_phi_left /\
  observation_ready gvn_phi_observation h gvn_phi_right /\
  observation_ready gvn_phi_observation h' gvn_phi_left /\
  observation_ready gvn_phi_observation h' gvn_phi_right /\
  observation_rank gvn_phi_observation h' gvn_phi_left <
    observation_rank gvn_phi_observation h gvn_phi_left /\
  observation_rank gvn_phi_observation h' gvn_phi_right <
    observation_rank gvn_phi_observation h gvn_phi_right /\
  reachable_state (activation (fun _ _ => None) gvn_phi_prog 0)
    (observation_state gvn_phi_observation h) /\
  strictly_dominates (cfg (base (nsv gvn_phi_problem))) 1
    (point (base (nsv gvn_phi_problem)) (observation_state gvn_phi_observation h)) /\
  val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_left = Some c /\
  val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_right = Some d /\
  optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem gvn_phi_left =
    optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem gvn_phi_right.
Proof.
  exists 2, 1, 0, gvn_phi_back_edge, gvn_phi_entry_edge, gvn_zero, gvn_zero.
  repeat split; try reflexivity; try discriminate; try exact gvn_phi_exit_reachable;
    try (cbn; tauto); try (cbn; lia).
  - exists 0; split; reflexivity.
  - apply (gvn_dominates gvn_phi_prog 1 2 gvn_phi_wf); [left; reflexivity|vm_compute; reflexivity].
Qed.

(** Generic dominated-use soundness establishes equality for the actual cyclic phi client. *)
Theorem gvn_phi_equal : forall h c d,
  observation_ready gvn_phi_observation h gvn_phi_left ->
  observation_ready gvn_phi_observation h gvn_phi_right ->
  reachable_state (activation (fun _ _ => None) gvn_phi_prog 0)
    (observation_state gvn_phi_observation h) ->
  strictly_dominates (cfg (base (nsv gvn_phi_problem))) 1
    (point (base (nsv gvn_phi_problem)) (observation_state gvn_phi_observation h)) ->
  val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_left = Some c ->
  val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_right = Some d ->
  c = d.
Proof.
  intros h c d Hleft Hright Hr Hdom Hc Hd.
  assert (Hequal : exists v,
    val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_left = Some v /\
    val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_right = Some v).
  { eapply (numbering_use_sound (activation gvn_no_ext gvn_phi_prog 0)
      label_encoding var_encoding sop_encoding gvn_phi_problem gvn_phi_observation
      (optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem));
      [apply ssa_block_view_laws; [exact gvn_phi_wf|left; reflexivity]|
       apply ssa_strict_laws; [exact gvn_phi_wf|left; reflexivity]|
       exact gvn_phi_observation_laws|exact gvn_phi_checked|
       vm_compute; reflexivity|exact Hr|vm_compute; tauto|vm_compute; tauto|
       exact Hdom|exact Hdom|].
    exists h, c, d; repeat split; assumption || reflexivity. }
  destruct Hequal as [v [Hvl Hvr]]; congruence.
Qed.

(** * Repeated execution with stable direct operands *)

(** The loop recomputes an inside-body addition of two independently bound entry arguments. *)
Definition gvn_loop_prog : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32); (1, TyI32)] [] (TJump 1 []));
     (1, SBlock [] [IOp 2 (OBin W32 BAdd) [0; 1]] (TJump 1 []))] TyI32)] 0 [].

Definition gvn_loop_problem : numbering_problem astate event label ssa_edge vid sop cval :=
  NumberingProblem (ssa_block_view gvn_no_ext gvn_loop_prog 0) gvn_pure
    (values_of gvn_loop_prog 0).

Definition gvn_loop_info : loop_info label := LoopInfo 1 (fun n => Nat.eqb n 1).
Definition gvn_loop_value : vid := 2.

Local Lemma gvn_loop_program_wf : wf_program gvn_no_ext gvn_loop_prog.
Proof.
  apply gvn_checked; [reflexivity|vm_compute; reflexivity].
Qed.

(** The concrete source semantics never changes a pure result to an undefined value. *)
Theorem gvn_loop_laws :
  numbering_loop_laws (activation (fun _ _ => None) gvn_loop_prog 0) gvn_loop_problem.
Proof.
  apply gvn_pure_bindings; [exact gvn_loop_program_wf|left; reflexivity].
Qed.

(** The sole loop block is its own dominating header and every incoming edge enters there. *)
Theorem gvn_loop_wf : loop_info_wf (cfg (base (nsv gvn_loop_problem))) gvn_loop_info.
Proof.
  constructor; [reflexivity| |].
  - intros n Hn; change (Nat.eqb n 1 = true) in Hn; apply Nat.eqb_eq in Hn; subst n.
    apply dominates_refl.
  - intros e He Htarget Hsource; change (Nat.eqb (edst e) 1 = true) in Htarget.
    now apply Nat.eqb_eq.
Qed.

(** The inside-body addition is recursively invariant because both arguments live outside. *)
Theorem gvn_loop_invariant : invariant_in gvn_loop_problem gvn_loop_info gvn_loop_value = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Positive SSA frames keep each direct entry operand stable throughout every loop run. *)
Theorem gvn_loop_stability :
  loop_operands_stable (activation (fun _ _ => None) gvn_loop_prog 0)
    gvn_loop_problem gvn_loop_info gvn_loop_value.
Proof.
  intros o args y s tr t Hbody Hdef Hp Hy Hr Hrun.
  vm_compute in Hdef; injection Hdef as <- <-.
  destruct Hy as [<-|[<-|Hnone]]; [| |contradiction]; symmetry.
  all: eapply (numbering_outside_frame (activation gvn_no_ext gvn_loop_prog 0)
    gvn_loop_problem gvn_loop_info); [apply ssa_block_view_laws;
      [exact gvn_loop_program_wf|left; reflexivity]|apply ssa_strict_laws;
      [exact gvn_loop_program_wf|left; reflexivity]|reflexivity|exact Hr|exact Hrun].
Qed.

Local Definition gvn_loop_entry := activation_enter 1 gvn_arguments.
Local Definition gvn_loop_first :=
  activation_advance gvn_loop_entry (env_set (aenv gvn_loop_entry) 2 gvn_zero).
Local Definition gvn_loop_again := activation_enter 1 (aenv gvn_loop_first).
Local Definition gvn_loop_second :=
  activation_advance gvn_loop_again (env_set (aenv gvn_loop_again) 2 gvn_zero).

Local Lemma gvn_loop_entry_reachable :
  reachable_state (activation gvn_no_ext gvn_loop_prog 0) gvn_loop_entry.
Proof.
  exists gvn_start, []; split.
  - unfold activation, activation_initial; cbn [initial].
    eexists; eexists; exists [gvn_zero; gvn_zero], gvn_arguments.
    repeat split; try reflexivity; repeat constructor; cbn [gvn_zero valid_cval]; lia.
  - eapply exec_step with (l := []) (s' := gvn_loop_entry); [|constructor].
    apply (AJump gvn_no_ext gvn_loop_prog 0 gvn_start 1 [] [] gvn_arguments);
      try reflexivity.
    unfold at_term; eexists; eexists; repeat split; reflexivity.
Qed.

Local Lemma gvn_loop_first_step :
  step (activation gvn_no_ext gvn_loop_prog 0) gvn_loop_entry [] gvn_loop_first.
Proof.
  apply (AOp gvn_no_ext gvn_loop_prog 0 gvn_loop_entry 2 (OBin W32 BAdd) [0; 1]
    [gvn_zero; gvn_zero] gvn_zero); try reflexivity.
  unfold at_instr; eexists; eexists; repeat split; reflexivity.
Qed.

Local Lemma gvn_loop_back_step :
  step (activation gvn_no_ext gvn_loop_prog 0) gvn_loop_first [] gvn_loop_again.
Proof.
  apply (AJump gvn_no_ext gvn_loop_prog 0 gvn_loop_first 1 [] [] (aenv gvn_loop_first));
    try reflexivity.
  unfold at_term; eexists; eexists; repeat split; reflexivity.
Qed.

Local Lemma gvn_loop_second_step :
  step (activation gvn_no_ext gvn_loop_prog 0) gvn_loop_again [] gvn_loop_second.
Proof.
  apply (AOp gvn_no_ext gvn_loop_prog 0 gvn_loop_again 2 (OBin W32 BAdd) [0; 1]
    [gvn_zero; gvn_zero] gvn_zero); try reflexivity.
  unfold at_instr; eexists; eexists; repeat split; reflexivity.
Qed.

(** A reachable inside-body instruction gives an actual nonempty restricted loop execution. *)
Theorem gvn_loop_run : exists s tr t,
  reachable_state (activation (fun _ _ => None) gvn_loop_prog 0) s /\
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) s tr t /\
  s <> t.
Proof.
  exists gvn_loop_entry, [], gvn_loop_first; split; [exact gvn_loop_entry_reachable|split].
  - exact (exec_in_step _ [] _ [] _ eq_refl gvn_loop_first_step
      (exec_in_refl _ eq_refl)).
  - intro Hsame; apply (f_equal apc) in Hsame; discriminate.
Qed.

(** The same operation executes twice, and its second execution preserves the first result. *)
Theorem gvn_loop_recomputed : exists a b c d tr o args,
  reachable_state (activation (fun _ _ => None) gvn_loop_prog 0) a /\
  def (nsv gvn_loop_problem) gvn_loop_value = Op o args /\
  at_instr gvn_loop_prog (activation_frame 0 a) (IOp gvn_loop_value o args) /\
  step (activation (fun _ _ => None) gvn_loop_prog 0) a [] b /\
  val (nsv gvn_loop_problem) a gvn_loop_value <>
    val (nsv gvn_loop_problem) b gvn_loop_value /\
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) b tr c /\
  at_instr gvn_loop_prog (activation_frame 0 c) (IOp gvn_loop_value o args) /\
  step (activation (fun _ _ => None) gvn_loop_prog 0) c [] d /\
  body gvn_loop_info (point (base (nsv gvn_loop_problem)) a) = true /\
  body gvn_loop_info (point (base (nsv gvn_loop_problem)) d) = true /\
  val (nsv gvn_loop_problem) c gvn_loop_value = val (nsv gvn_loop_problem) d gvn_loop_value.
Proof.
  exists gvn_loop_entry, gvn_loop_first, gvn_loop_again, gvn_loop_second, [],
    (OBin W32 BAdd), [0; 1].
  split; [exact gvn_loop_entry_reachable|split; [reflexivity|split]].
  - unfold at_instr; eexists; eexists; repeat split; reflexivity.
  - split; [exact gvn_loop_first_step|split; [discriminate|split]].
    + exact (exec_in_step _ [] _ [] _ eq_refl gvn_loop_back_step
        (exec_in_refl _ eq_refl)).
    + split.
      * unfold at_instr; eexists; eexists; repeat split; reflexivity.
      * split; [exact gvn_loop_second_step|repeat split; reflexivity].
Qed.

(** The generic loop theorem applies to the actual repeated-operation client. *)
Theorem gvn_loop_sound : forall s tr1 u1 tr2 u2 tr3 u3,
  reachable_state (activation (fun _ _ => None) gvn_loop_prog 0) s ->
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) s tr1 u1 ->
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) u1 tr2 u2 ->
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) u2 tr3 u3 ->
  val (nsv gvn_loop_problem) u1 gvn_loop_value <>
    val (nsv gvn_loop_problem) u2 gvn_loop_value ->
  val (nsv gvn_loop_problem) u2 gvn_loop_value =
    val (nsv gvn_loop_problem) u3 gvn_loop_value.
Proof.
  apply loop_invariant_sound.
  - apply ssa_block_view_laws; [exact gvn_loop_program_wf|left; reflexivity].
  - apply ssa_strict_laws; [exact gvn_loop_program_wf|left; reflexivity].
  - exact gvn_loop_laws.
  - exact gvn_loop_wf.
  - exact gvn_loop_invariant.
  - exact gvn_loop_stability.
Qed.
