(** * Scalar evolution of an actual SSA counted loop

    The count-up program increments a 32-bit header parameter while it is below its entry bound.
    For example, bound five gives the recurrence zero plus the arrival index and trip count five.
    Builds on: ExamplesSsaAnalysisBase, ExamplesSsaActivation and AnalysesScev. *)

From Stdlib Require Import List Bool Arith Lia ZArith NArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Bits Require Import BitsWord.
From Gaulois.Graph Require Import GraphCore GraphEdgeDominance.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsDominated.
From Gaulois.Analyses Require Import AnalysesScev.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping ExamplesSsaSemantics
  ExamplesSsaTypingProofs ExamplesSsaBridge ExamplesSsaActivation ExamplesSsaViews ExamplesSsaStrict
  ExamplesSsaAnalysisBase.
Import List.ListNotations.
Local Open Scope nat_scope.

(** This program implements the unsigned loop from zero to its entry parameter. *)
Definition count_up : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32)]
      [IOp 1 (OConst (VInt W32 0%Z)) []; IOp 2 (OConst (VInt W32 1%Z)) []]
      (TJump 1 [1]));
     (1, SBlock [(3, TyI32)] [IOp 4 (OBin W32 BLtU) [3; 0]] (TBr 4 2 [] 3 []));
     (2, SBlock [] [IOp 5 (OBin W32 BAdd) [3; 2]] (TJump 1 [5]));
     (3, SBlock [] [] (TRet 3))] TyI32)] 0 [].

(** The entry parameter is the invariant upper bound. *)
Definition count_up_n : vid := 0.

(** The recognized header recurrence starts at the entry zero and adds the entry one. *)
Definition count_up_chrec : chrec vid := CRec (CInv (IVar 1)) (CInv (IVar 2)).

(** The five-trip fixture records the actual mathematical values of its three invariants. *)
Definition count_up_inv (x : vid) : Z :=
  match x with
  | 0 => 5%Z
  | 2 => 1%Z
  | _ => 0%Z
  end.

(** The inventory contains every source value defined by the count-up function. *)
Definition count_up_inventory : list vid := [0; 1; 2; 3; 4; 5].

(** The adapter recognizes the toy's 32-bit arithmetic and word constants. *)
Definition count_up_ops : scev_ops sop cval :=
  {| width_of := 32%positive;
     to_Z := fun c =>
       match c with
       | VInt W32 z => wrap 32%positive z
       | _ => 0%Z
       end;
     add_op := fun o =>
       match o with
       | OBin W32 BAdd => true
       | _ => false
       end;
     mul_op := fun o =>
       match o with
       | OBin W32 BMul => true
       | _ => false
       end;
     const_op := fun o =>
       match o with
       | OConst (VInt W32 z) => Some z
       | _ => None
       end |}.

(** The loop body contains the header and increment blocks with their actual incoming edges. *)
Definition count_up_loop : loop_view astate event label ssa_edge vid sop cval :=
  {| lssa := ssa_block_view (fun _ _ => None) count_up 0;
     lheader := 1;
     lbody := fun n => Nat.eqb n 1 || Nat.eqb n 2;
     lentry := SsaEdge 0 1 0;
     lback := SsaEdge 2 1 0;
     ltest := Some {| t_cmp := CmpLt; t_sign := Unsigned; t_lhs := 3;
       t_bound := IVar count_up_n |} |}.

(** The actual count-up source passes the toy's complete well-formedness checker. *)
Theorem count_up_wf : wf_program (fun _ _ => None) count_up.
Proof.
  apply wf_check_sound; [apply ext_respects_nil; reflexivity|vm_compute; reflexivity].
Qed.

(** Every observation is canonical and each flagged operation obeys the wrapped equations. *)
Theorem count_up_ops_laws :
  scev_ops_laws count_up_ops (ViewsSsa.op_eval (lssa count_up_loop)).
Proof.
  constructor.
  - intros c; destruct c as [w z|b off|f|bits|bits]; try (symmetry; apply wrap_0).
    destruct w; [symmetry; apply wrap_wrap|symmetry; apply wrap_0].
  - intros o a b r Hflag Heval.
    destruct o as [c|w op| | | |tag]; try discriminate.
    destruct w, op; try discriminate.
    destruct a as [wa za|pa oa|fa|ba|ba], b as [wb zb|pb ob|fb|bb|bb]; try discriminate.
    destruct wa, wb; try discriminate.
    change ((if word_ok W32 za && word_ok W32 zb then
      Some (VInt W32 (word_wrap W32 (za + zb))) else None) = Some r) in Heval.
    destruct (word_ok W32 za && word_ok W32 zb); [|discriminate].
    inversion Heval; subst r.
    change (wrap 32%positive (wrap 32%positive (za + zb)) =
      wrap 32%positive (wrap 32%positive za + wrap 32%positive zb))%Z.
    rewrite wrap_wrap; apply wrap_add.
  - intros o a b r Hflag Heval.
    destruct o as [c|w op| | | |tag]; try discriminate.
    destruct w, op; try discriminate.
    destruct a as [wa za|pa oa|fa|ba|ba], b as [wb zb|pb ob|fb|bb|bb]; try discriminate.
    destruct wa, wb; try discriminate.
    change ((if word_ok W32 za && word_ok W32 zb then
      Some (VInt W32 (word_wrap W32 (za * zb))) else None) = Some r) in Heval.
    destruct (word_ok W32 za && word_ok W32 zb); [|discriminate].
    inversion Heval; subst r.
    change (wrap 32%positive (wrap 32%positive (za * zb)) =
      wrap 32%positive (wrap 32%positive za * wrap 32%positive zb))%Z.
    rewrite wrap_wrap; apply wrap_mul.
  - intros o z r Hflag Heval.
    destruct o as [c|w op| | | |tag]; try discriminate.
    destruct c as [w a|b off|f|bits|bits]; try discriminate; destruct w; try discriminate.
    inversion Hflag; subst z; inversion Heval; subst r.
    apply wrap_wrap.
Qed.

(** The underlying block adapter satisfies its complete SSA laws for every reachable prefix. *)
Theorem count_up_ssa_laws :
  ssa_view_laws (activation (fun _ _ => None) count_up 0) (lssa count_up_loop).
Proof.
  apply ssa_block_view_laws; [exact count_up_wf|left; reflexivity].
Qed.

(** The actual source definitions obey all positive strict-SSA frame equations. *)
Theorem count_up_strict_laws :
  strict_ssa_laws (activation (fun _ _ => None) count_up 0) (lssa count_up_loop).
Proof.
  apply ssa_strict_laws; [exact count_up_wf|left; reflexivity].
Qed.

(** The initial source state binds only its arbitrary unsigned bound. *)
Definition count_up_start (n : Z) : astate :=
  AState 0 0 (env_set (fun _ => None) 0 (VInt W32 n)).

Local Definition count_up_zero_state n :=
  activation_advance (count_up_start n)
    (env_set (aenv (count_up_start n)) 1 (VInt W32 0%Z)).

Local Definition count_up_one_state n :=
  activation_advance (count_up_zero_state n)
    (env_set (aenv (count_up_zero_state n)) 2 (VInt W32 1%Z)).

(** The first header arrival has the parameter copied from the actual zero argument. *)
Definition count_up_header_zero n :=
  activation_enter 1 (env_set (aenv (count_up_one_state n)) 3 (VInt W32 0%Z)).

Local Definition count_up_test_state n :=
  activation_advance (count_up_header_zero n)
    (env_set (aenv (count_up_header_zero n)) 4 (bool_value (0 <? n)%Z)).

Local Definition count_up_body_start n := activation_enter 2 (aenv (count_up_test_state n)).

Local Definition count_up_incremented n :=
  activation_advance (count_up_body_start n)
    (env_set (aenv (count_up_body_start n)) 5 (VInt W32 1%Z)).

(** One actual feedback step produces the next header parameter by parallel argument binding. *)
Definition count_up_header_one n :=
  activation_enter 1 (env_set (aenv (count_up_incremented n)) 3 (VInt W32 1%Z)).

(** The zero-bound execution enters the return block with the zero parameter unchanged. *)
Definition count_up_zero_exit := activation_enter 3 (aenv (count_up_test_state 0%Z)).

Lemma count_up_start_initial n : (0 <= n < modulus 32%positive)%Z ->
  initial (activation (fun _ _ => None) count_up 0) (count_up_start n).
Proof.
  intro Hn; unfold activation, activation_initial; cbn [initial].
  eexists; eexists; exists [VInt W32 n], (aenv (count_up_start n)).
  repeat split; try reflexivity.
  constructor; [change (0 <= n < 4294967296)%Z; exact Hn|constructor].
Qed.

Local Lemma count_up_zero_step n :
  step (activation (fun _ _ => None) count_up 0) (count_up_start n) [] (count_up_zero_state n).
Proof.
  apply (AOp (fun _ _ => None) count_up 0 (count_up_start n) 1
    (OConst (VInt W32 0%Z)) [] [] (VInt W32 0%Z)).
  - unfold at_instr; eexists; eexists; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Local Lemma count_up_one_step n :
  step (activation (fun _ _ => None) count_up 0) (count_up_zero_state n) [] (count_up_one_state n).
Proof.
  apply (AOp (fun _ _ => None) count_up 0 (count_up_zero_state n) 2
    (OConst (VInt W32 1%Z)) [] [] (VInt W32 1%Z)).
  - unfold at_instr; eexists; eexists; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Local Lemma count_up_entry_step n :
  step (activation (fun _ _ => None) count_up 0) (count_up_one_state n) []
    (count_up_header_zero n).
Proof.
  apply (AJump (fun _ _ => None) count_up 0 (count_up_one_state n) 1 [1]
    [VInt W32 0%Z] (aenv (count_up_header_zero n))).
  - unfold at_term; eexists; eexists; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Every valid bound reaches the header through two instruction stays and the actual entry edge. *)
Theorem count_up_entry_run n :
  run_edges (activation (fun _ _ => None) count_up 0) (base (lssa count_up_loop))
    (count_up_start n) [SsaEdge 0 1 0] (count_up_header_zero n).
Proof.
  eapply run_stay; [exact (count_up_zero_step n)|split; reflexivity|].
  eapply run_stay; [exact (count_up_one_step n)|split; reflexivity|].
  eapply run_cons; [exact (count_up_entry_step n)| |constructor].
  change (ssa_block_taken count_up 0 (count_up_one_state n) [] (count_up_header_zero n)
    (SsaEdge 0 1 0)).
  unfold ssa_block_taken; eexists; eexists; repeat split; try reflexivity.
  left; reflexivity.
Qed.

Local Lemma count_up_test_step n : (0 <= n < modulus 32%positive)%Z ->
  step (activation (fun _ _ => None) count_up 0) (count_up_header_zero n) []
    (count_up_test_state n).
Proof.
  intro Hn; apply (AOp (fun _ _ => None) count_up 0 (count_up_header_zero n) 4
    (OBin W32 BLtU) [3; 0] [VInt W32 0%Z; VInt W32 n] (bool_value (0 <? n)%Z)).
  - unfold at_instr; eexists; eexists; repeat split; reflexivity.
  - reflexivity.
  - assert (Hok : word_ok W32 n = true).
    { unfold word_ok; apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt];
        exact (proj1 Hn) || exact (proj2 Hn). }
    change ((if word_ok W32 0 && word_ok W32 n then
      Some (bool_value (0 <? n)%Z) else None) = Some (bool_value (0 <? n)%Z)).
    rewrite Hok; reflexivity.
Qed.

Local Lemma count_up_true_step n : (0 < n)%Z ->
  step (activation (fun _ _ => None) count_up 0) (count_up_test_state n) []
    (count_up_body_start n).
Proof.
  intro Hpositive; apply (ABranch (fun _ _ => None) count_up 0 (count_up_test_state n)
    4 2 [] 3 [] 1%Z 2 [] [] (aenv (count_up_test_state n))).
  - unfold at_term; eexists; eexists; repeat split; reflexivity.
  - assert (Htest : (0 <? n)%Z = true) by (apply Z.ltb_lt; exact Hpositive).
    change (Some (bool_value (0 <? n)%Z) = Some (VInt W32 1%Z)); rewrite Htest; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Local Lemma count_up_increment_step n :
  step (activation (fun _ _ => None) count_up 0) (count_up_body_start n) []
    (count_up_incremented n).
Proof.
  apply (AOp (fun _ _ => None) count_up 0 (count_up_body_start n) 5
    (OBin W32 BAdd) [3; 2] [VInt W32 0%Z; VInt W32 1%Z] (VInt W32 1%Z)).
  - unfold at_instr; eexists; eexists; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Local Lemma count_up_back_step n :
  step (activation (fun _ _ => None) count_up 0) (count_up_incremented n) []
    (count_up_header_one n).
Proof.
  apply (AJump (fun _ _ => None) count_up 0 (count_up_incremented n) 1 [5]
    [VInt W32 1%Z] (aenv (count_up_header_one n))).
  - unfold at_term; eexists; eexists; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Every positive valid bound admits an actual nonempty counted stay with one feedback arrival. *)
Theorem count_up_positive_run n : (0 < n < modulus 32%positive)%Z ->
  initial (activation (fun _ _ => None) count_up 0) (count_up_start n) /\
  run_edges (activation (fun _ _ => None) count_up 0) (base (lssa count_up_loop))
    (count_up_start n) [SsaEdge 0 1 0; SsaEdge 1 2 0; SsaEdge 2 1 0]
    (count_up_header_one n) /\
  stay_arrivals ssa_edge_encoding count_up_loop
    [SsaEdge 0 1 0; SsaEdge 1 2 0; SsaEdge 2 1 0] = 1 /\
  aenv (count_up_header_one n) 3 = Some (VInt W32 1%Z).
Proof.
  intro Hn; assert (Hrange : (0 <= n < modulus 32%positive)%Z) by lia.
  split; [apply count_up_start_initial; exact Hrange|]; split.
  - eapply run_edges_app with (es1 := [SsaEdge 0 1 0])
      (es2 := [SsaEdge 1 2 0; SsaEdge 2 1 0]); [exact (count_up_entry_run n)|].
    eapply run_stay; [apply count_up_test_step; exact Hrange|split; reflexivity|].
    eapply run_cons; [apply count_up_true_step; exact (proj1 Hn)| |].
    + change (ssa_block_taken count_up 0 (count_up_test_state n) []
        (count_up_body_start n) (SsaEdge 1 2 0)).
      assert (Htest : (0 <? n)%Z = true) by (apply Z.ltb_lt; exact (proj1 Hn)).
      unfold ssa_block_taken; eexists; eexists; repeat split; try reflexivity.
      * left; reflexivity.
      * change (Some (if Z.eqb (if (0 <? n)%Z then 1%Z else 0%Z) 0%Z then
          1 else 0) = Some 0).
        rewrite Htest; reflexivity.
    + eapply run_stay; [exact (count_up_increment_step n)|split; reflexivity|].
      eapply run_cons; [exact (count_up_back_step n)| |constructor].
      change (ssa_block_taken count_up 0 (count_up_incremented n) []
        (count_up_header_one n) (SsaEdge 2 1 0)).
      unfold ssa_block_taken; eexists; eexists; repeat split; try reflexivity.
      left; reflexivity.
  - split; reflexivity.
Qed.

(** Bound zero follows the false guard to exit without taking the feedback edge. *)
Theorem count_up_zero_run :
  initial (activation (fun _ _ => None) count_up 0) (count_up_start 0%Z) /\
  run_edges (activation (fun _ _ => None) count_up 0) (base (lssa count_up_loop))
    (count_up_start 0%Z) [SsaEdge 0 1 0; SsaEdge 1 3 1] count_up_zero_exit /\
  aenv count_up_zero_exit 3 = Some (VInt W32 0%Z).
Proof.
  split; [apply count_up_start_initial; change (0 <= 0 < 4294967296)%Z; lia|].
  split; [|reflexivity].
  eapply run_edges_app with (es1 := [SsaEdge 0 1 0]) (es2 := [SsaEdge 1 3 1]);
    [exact (count_up_entry_run 0%Z)|].
  eapply run_stay;
    [apply count_up_test_step; change (0 <= 0 < 4294967296)%Z; lia|split; reflexivity|].
  eapply run_cons; [| |constructor].
  - apply (ABranch (fun _ _ => None) count_up 0 (count_up_test_state 0%Z)
      4 2 [] 3 [] 0%Z 3 [] [] (aenv (count_up_test_state 0%Z))).
    + unfold at_term; eexists; eexists; repeat split; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - change (ssa_block_taken count_up 0 (count_up_test_state 0%Z) [] count_up_zero_exit
      (SsaEdge 1 3 1)).
    unfold ssa_block_taken; eexists; eexists; repeat split; try reflexivity.
    right; left; reflexivity.
Qed.

(** This finite plan records the actual header parameter and increment definition. *)
Definition count_up_plan : scev_plan vid :=
  ScevPlan [ScevBinding 3 1 5 SAddUpdate (Some (SOutside 2)) true] 3.

(** The indexed checker accepts the actual count-up source shape. *)
Theorem count_up_plan_checked :
  scev_plan_check label_encoding nat_encoding count_up_inventory count_up_loop count_up_ops
    count_up_plan = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Translating the actual checked plan yields the documented count-up recurrence. *)
Theorem count_up_plan_compiled :
  scev_compile_plan nat_encoding count_up_plan = Some count_up_chrec.
Proof.
  vm_compute; reflexivity.
Qed.

(** Recognition of the actual source program returns the documented header recurrence. *)
Theorem count_up_recognise :
  recognise label_encoding nat_encoding count_up_inventory count_up_loop count_up_ops 3 =
    Some count_up_chrec.
Proof.
  vm_compute; reflexivity.
Qed.

(** * Complete activation adapter *)

Local Definition count_up_fd : fdef :=
  match funcs count_up with
  | (_, fd) :: _ => fd
  | [] => FDef 0 [] TyI32
  end.

Local Definition count_up_requirements : requirements :=
  Map.of_list nat_encoding [(0, []); (1, [0; 1; 2]);
    (2, [0; 1; 2; 3; 4]); (3, [0; 1; 2; 3; 4])].

Local Lemma count_up_certificate : availability_certificate count_up_fd count_up_requirements.
Proof.
  apply certificate_check_sound; vm_compute; reflexivity.
Qed.

Local Lemma count_up_back_coordinates s tr t :
  taken (base (lssa count_up_loop)) s tr t (lback count_up_loop) ->
  alabel s = 2 /\ apc s = 1.
Proof.
  intros [fd [b [Hf [Hb [Hpc [Hsrc Hrest]]]]]].
  change (find_func count_up 0 = Some fd) in Hf.
  assert (Hfunction : find_func count_up 0 = Some count_up_fd) by reflexivity.
  rewrite Hfunction in Hf; inversion Hf; subst fd.
  change (2 = alabel s) in Hsrc; split; [symmetry; exact Hsrc|].
  rewrite <- Hsrc in Hb; vm_compute in Hb; inversion Hb; subst b; exact Hpc.
Qed.

Local Lemma count_up_operation_equation s x o args c :
  reachable_state (activation (fun _ _ => None) count_up 0) s ->
  alabel s = 2 -> apc s = 1 -> In x count_up_inventory ->
  def (lssa count_up_loop) x = Op o args -> aenv s x = Some c ->
  exists cs, Forall2 (fun y d => aenv s y = Some d) args cs /\
    ExamplesSsaSemantics.op_eval (fun _ _ => None) o cs = Some c.
Proof.
  intros Hreachable Hlabel Hpc Hin Hdef Hvalue.
  destruct (ExamplesSsaViews.ssa_operation_location (fun _ _ => None) count_up 0 x o args
    count_up_wf Hdef) as [fd [l [b [pc [Hf [Hb Hnth]]]]]].
  assert (Hfunction : find_func count_up 0 = Some count_up_fd) by reflexivity.
  rewrite Hfunction in Hf; inversion Hf; subst fd.
  destruct (ExamplesSsaViews.ssa_operation_consistent (fun _ _ => None) count_up 0
    count_up_fd count_up_requirements l b pc x o args s count_up_wf
    (or_introl eq_refl) Hfunction Hb count_up_certificate Hnth Hreachable)
    as [cs [value [Hargs [Hactual Heval]]]].
  - change (In x (ExamplesSsaViews.ssa_available count_up_fd count_up_requirements
      (alabel s, apc s))).
    rewrite Hlabel, Hpc; change (In x [5; 0; 1; 2; 3; 4]).
    cbn [count_up_inventory In] in Hin; cbn [In]; tauto.
  - assert (value = c) by congruence; subst value; exists cs; split; assumption.
Qed.

Local Lemma count_up_header_edges e :
  In e (edges_of (cfg (base (lssa count_up_loop)))) ->
  Graph.target (cfg (base (lssa count_up_loop))) e = 1 ->
  e = SsaEdge 0 1 0 \/ e = SsaEdge 2 1 0.
Proof.
  vm_compute; intros [Heq|[Heq|[Heq|[Heq|Hbad]]]] Htarget;
    try contradiction; subst e; cbn in Htarget; intuition discriminate.
Qed.

Local Lemma count_up_jump_coordinates s tr t e :
  taken (base (lssa count_up_loop)) s tr t e ->
  (e = SsaEdge 0 1 0 -> alabel s = 0 /\ apc s = 2) /\
  (e = SsaEdge 2 1 0 -> alabel s = 2 /\ apc s = 1).
Proof.
  intros [fd [b [Hf [Hb [Hpc [Hsrc Hrest]]]]]].
  change (find_func count_up 0 = Some fd) in Hf.
  assert (Hfunction : find_func count_up 0 = Some count_up_fd) by reflexivity.
  rewrite Hfunction in Hf; inversion Hf; subst fd.
  split; intro Heq; subst e; cbn [esrc] in Hsrc.
  - split; [symmetry; exact Hsrc|].
    rewrite <- Hsrc in Hb; vm_compute in Hb; inversion Hb; subst b; exact Hpc.
  - split; [symmetry; exact Hsrc|].
    rewrite <- Hsrc in Hb; vm_compute in Hb; inversion Hb; subst b; exact Hpc.
Qed.

Local Lemma count_up_header_instruction s instruction : alabel s = 1 ->
  at_instr count_up (activation_frame 0 s) instruction ->
  instruction = IOp 4 (OBin W32 BLtU) [3; 0].
Proof.
  intros Hlabel [fd [b [Hf [Hb Hnth]]]].
  change (find_func count_up 0 = Some fd) in Hf.
  assert (Hfunction : find_func count_up 0 = Some count_up_fd) by reflexivity.
  rewrite Hfunction in Hf; inversion Hf; subst fd.
  change (find_block count_up_fd (alabel s) = Some b) in Hb.
  rewrite Hlabel in Hb; vm_compute in Hb; inversion Hb; subst b.
  change (nth_error [IOp 4 (OBin W32 BLtU) [3; 0]] (apc s) = Some instruction) in Hnth.
  destruct (apc s) as [|pc]; [inversion Hnth; reflexivity|].
  destruct pc; discriminate.
Qed.

Local Lemma count_up_header_terminator s terminator : alabel s = 1 ->
  at_term count_up (activation_frame 0 s) terminator -> terminator = TBr 4 2 [] 3 [].
Proof.
  intros Hlabel [fd [b [Hf [Hb [Hpc Hterm]]]]].
  change (find_func count_up 0 = Some fd) in Hf.
  assert (Hfunction : find_func count_up 0 = Some count_up_fd) by reflexivity.
  rewrite Hfunction in Hf; inversion Hf; subst fd.
  change (find_block count_up_fd (alabel s) = Some b) in Hb.
  rewrite Hlabel in Hb; vm_compute in Hb; inversion Hb; subst b.
  symmetry; exact Hterm.
Qed.

Local Lemma count_up_jump_parameter s tr t arg :
  at_term count_up (activation_frame 0 s) (TJump 1 [arg]) ->
  step (activation (fun _ _ => None) count_up 0) s tr t -> aenv t 3 = aenv s arg.
Proof.
  intros Hat Hstep; destruct Hstep as
    [s x o args cs value Hrule Hread Heval|s x n block offset Hrule|s p Hrule|
    s x ty size p value Hrule Htype Hvalid|s size p x Hrule|s x value Hrule Hvalue|
    s dst args cs env Hrule Hread Hjump|
    s cond l1 a1 l2 a2 z dst args cs env Hrule Hcond Hchoice Hread Hjump|
    s cond cases dst da z target args cs env Hrule Hcond Hchoice Hread Hjump|
    s callee args next ps result cs value env Hrule Hsig Hread Htype Hvalid Hjump|
    s x value Hrule Hvalue].
  all: try solve [exfalso; eapply ssa_at_instr_not_term; [exact Hrule|exact Hat]].
  all: try solve [pose proof (ssa_at_term_unique count_up _ _ _ Hat Hrule) as Hbad;
    discriminate].
  pose proof (ssa_at_term_unique count_up _ _ _ Hat Hrule) as Heq.
  inversion Heq; subst dst args.
  change (match aenv s arg with Some c => Some [c] | None => None end = Some cs) in Hread.
  destruct (aenv s arg) as [value|] eqn:Harg; [|discriminate].
  inversion Hread; subst cs.
  change (Some (env_set (aenv s) 3 value) = Some env) in Hjump.
  inversion Hjump; subst env; reflexivity.
Qed.

Local Lemma count_up_parameter_stay s tr t :
  step (activation (fun _ _ => None) count_up 0) s tr t ->
  stays (base (lssa count_up_loop)) s tr t -> alabel s = 1 -> aenv t 3 = aenv s 3.
Proof.
  intros Hstep Hstay Hlabel; destruct Hstep as
    [s x o args cs value Hrule Hread Heval|s x n block offset Hrule|s p Hrule|
    s x ty size p value Hrule Htype Hvalid|s size p x Hrule|s x value Hrule Hvalue|
    s dst args cs env Hrule Hread Hjump|
    s cond l1 a1 l2 a2 z dst args cs env Hrule Hcond Hchoice Hread Hjump|
    s cond cases dst da z target args cs env Hrule Hcond Hchoice Hread Hjump|
    s callee args next ps result cs value env Hrule Hsig Hread Htype Hvalid Hjump|
    s x value Hrule Hvalue].
  all: try solve [pose proof (count_up_header_instruction s _ Hlabel Hrule) as Hbad;
    discriminate].
  all: try solve [pose proof (count_up_header_terminator s _ Hlabel Hrule) as Hbad;
    discriminate].
  - pose proof (count_up_header_instruction s _ Hlabel Hrule) as Heq.
    inversion Heq; subst x o args; reflexivity.
  - pose proof (count_up_header_terminator s _ Hlabel Hrule) as Heq.
    inversion Heq; subst cond l1 a1 l2 a2.
    destruct (Z.eqb z 0) eqn:Hz; inversion Hchoice; subst dst args;
      destruct Hstay as [Hsame Hpc]; change (3 = alabel s) in Hsame ||
        change (2 = alabel s) in Hsame; congruence.
Qed.

Local Lemma count_up_true_edge_dominates :
  edge_dominates (cfg (base (lssa count_up_loop))) (SsaEdge 1 2 0) 2.
Proof.
  apply (dominating_edges_in_sound nat_encoding (cfg (base (lssa count_up_loop))) 2
    (SsaEdge 1 2 0)).
  - exact (cfg_wf (base_laws count_up_ssa_laws)).
  - exact (ExamplesSsaViews.ssa_block_out_nodup count_up 0).
  - vm_compute; tauto.
Qed.

Local Lemma count_up_back_guard s tr t :
  reachable_state (activation (fun _ _ => None) count_up 0) s ->
  taken (base (lssa count_up_loop)) s tr t (lback count_up_loop) ->
  exists c, aenv s 3 = Some c /\
    test_holds 32%positive Unsigned CmpLt (to_Z count_up_ops c)
      (eval_iexpr (inv_env count_up_loop count_up_ops s) (IVar count_up_n)).
Proof.
  intros Hreachable Htaken.
  destruct (count_up_back_coordinates s tr t Htaken) as [Hlabel Hpc].
  assert (Hdom : edge_dominates (cfg (base (lssa count_up_loop))) (SsaEdge 1 2 0)
    (point (base (lssa count_up_loop)) s)).
  { change (edge_dominates (cfg (base (lssa count_up_loop))) (SsaEdge 1 2 0) (alabel s)).
    rewrite Hlabel; exact count_up_true_edge_dominates. }
  destruct (dominated_guard_holds (activation (fun _ _ => None) count_up 0)
    (lssa count_up_loop) count_up_ssa_laws count_up_strict_laws s (SsaEdge 1 2 0)
    Hreachable Hdom) as [Hguards Hoperations].
  assert (Hguard_member : In (Condition 4 GTrue)
    (edge_guard (lssa count_up_loop) (SsaEdge 1 2 0))) by (vm_compute; left; reflexivity).
  pose proof (proj1 (Forall_forall _ _) Hguards _ Hguard_member) as Hguard.
  destruct Hguard as [condition_value [Hcondition Htruth]].
  assert (Hcompare_def : def (lssa count_up_loop) 4 = Op (OBin W32 BLtU) [3; 0]) by
    (vm_compute; reflexivity).
  destruct (Hoperations (Condition 4 GTrue) (OBin W32 BLtU) [3; 0] Hguard_member Hcompare_def)
    as [values [result [Hvalues [Hresult Heval]]]].
  destruct (scev_forall2_pair _ _ _ values Hvalues) as [a [b [Hlist [Ha Hb]]]]; subst values.
  assert (Hsame : result = condition_value) by congruence; subst condition_value.
  change (ExamplesSsaSemantics.op_eval (fun _ _ => None) (OBin W32 BLtU) [a; b] =
    Some result) in Heval.
  destruct a as [wa za|pa oa|fa|ba|ba], b as [wb zb|pb ob|fb|bb|bb];
    try discriminate Heval; destruct wa, wb; try discriminate Heval.
  change ((if word_ok W32 za && word_ok W32 zb then Some (bool_value (za <? zb)%Z)
    else None) = Some result) in Heval.
  destruct (word_ok W32 za && word_ok W32 zb) eqn:Hwords; [|discriminate].
  inversion Heval; subst result.
  change (ssa_truth (bool_value (za <? zb)%Z) = true) in Htruth.
  destruct (za <? zb)%Z eqn:Hlt; [|discriminate].
  apply Z.ltb_lt in Hlt; apply Bool.andb_true_iff in Hwords; destruct Hwords as [Haok Hbok].
  apply word_ok_valid in Haok; apply word_ok_valid in Hbok.
  exists (VInt W32 za); split; [exact Ha|].
  unfold test_holds, view_z, inv_env; cbn [eval_iexpr count_up_n count_up_ops to_Z].
  change (wrap 32%positive (wrap 32%positive za) <
    wrap 32%positive (match aenv s 0%nat with
      | Some (VInt W32 z) => wrap 32%positive z
      | _ => 0%Z
      end))%Z.
  change (aenv s 0 = Some (VInt W32 zb)) in Hb; rewrite Hb, !wrap_wrap.
  rewrite (wrap_id 32%positive za Haok), (wrap_id 32%positive zb Hbok); exact Hlt.
Qed.

Local Lemma count_up_phi_equation s tr t e x i :
  reachable_state (activation (fun _ _ => None) count_up 0) s ->
  step (activation (fun _ _ => None) count_up 0) s tr t ->
  taken (base (lssa count_up_loop)) s tr t e ->
  Graph.target (cfg (base (lssa count_up_loop))) e = 1 ->
  def (lssa count_up_loop) x = Param 1 i ->
  aenv t x = match nth_error (edge_args (lssa count_up_loop) e) i with
    | Some y => aenv s y
    | None => None
    end.
Proof.
  intros Hreachable Hstep Htaken Htarget Hdef.
  pose proof (param_defs count_up_ssa_laws x 1 i Hdef) as Hparam.
  change (nth_error [3] i = Some x) in Hparam.
  destruct i as [|i]; [inversion Hparam; subst x|destruct i; discriminate].
  destruct (view_taken_edge (activation (fun _ _ => None) count_up 0)
    (base (lssa count_up_loop)) s tr t e (base_laws count_up_ssa_laws)
    Hreachable Hstep Htaken) as [Hlisted Hrest].
  destruct (count_up_jump_coordinates s tr t e Htaken) as [Hentry Hback].
  destruct (count_up_header_edges e Hlisted Htarget) as [Heq|Heq]; subst e.
  - destruct (Hentry eq_refl) as [Hlabel Hpc].
    change (aenv t 3 = aenv s 1); apply (count_up_jump_parameter s tr t 1); [|exact Hstep].
    unfold at_term; cbn [activation_frame ffunc flabel fpc]; rewrite Hlabel, Hpc.
    eexists; eexists; repeat split; reflexivity.
  - destruct (Hback eq_refl) as [Hlabel Hpc].
    change (aenv t 3 = aenv s 5); apply (count_up_jump_parameter s tr t 5); [|exact Hstep].
    unfold at_term; cbn [activation_frame ffunc flabel fpc]; rewrite Hlabel, Hpc.
    eexists; eexists; repeat split; reflexivity.
Qed.

(** The actual counted loop satisfies every local loop law on every reachable activation prefix. *)
Theorem count_up_loop_laws :
  loop_view_laws (activation (fun _ _ => None) count_up 0)
    label_encoding nat_encoding count_up_inventory count_up_ops count_up_loop.
Proof.
  constructor.
  - exact count_up_ssa_laws.
  - exact count_up_strict_laws.
  - vm_compute; intuition discriminate.
  - vm_compute; tauto.
  - vm_compute; tauto.
  - exact count_up_header_edges.
  - reflexivity.
  - intros n Hin; change (In n [0]) in Hin; destruct Hin as [Heq|Hbad];
      [subst n; reflexivity|contradiction].
  - intros e Hin Houtside Hinside.
    vm_compute in Hin; destruct Hin as [Heq|[Heq|[Heq|[Heq|Hbad]]]];
      try contradiction; subst e; try reflexivity; vm_compute in Houtside, Hinside; congruence.
  - exact count_up_phi_equation.
  - intros s tr t x i Hreachable Hstep Hstay Hpoint Hdef.
    pose proof (param_defs count_up_ssa_laws x 1 i Hdef) as Hparam.
    change (nth_error [3] i = Some x) in Hparam.
    destruct i as [|i]; [inversion Hparam; subst x|destruct i; discriminate].
    exact (count_up_parameter_stay s tr t Hstep Hstay Hpoint).
  - intros tst y Htest Hin; inversion Htest; subst tst.
    change (In y [0]) in Hin; destruct Hin as [Heq|Hbad];
      [subst y; reflexivity|contradiction].
  - intros s tr t tst Hreachable Hstep Htaken Htest; inversion Htest; subst tst.
    exact (count_up_back_guard s tr t Hreachable Htaken).
  - intros s tr t p x o args c Hreachable Hstep Htaken Hchecked Hin Hdef Hvalue.
    destruct (count_up_back_coordinates s tr t Htaken) as [Hlabel Hpc].
    apply (count_up_operation_equation s x o args c Hreachable Hlabel Hpc);
      [eapply scev_plan_operations_inventory; eassumption|exact Hdef|exact Hvalue].
Qed.

(** The actual activation's recognized header value is the generic recurrence on every valid run. *)
Theorem count_up_recurrence : forall s0 es s c,
  initial (activation (fun _ _ => None) count_up 0) s0 ->
  run_edges (activation (fun _ _ => None) count_up 0) (base (lssa count_up_loop)) s0 es s ->
  point (base (lssa count_up_loop)) s = lheader count_up_loop ->
  val (lssa count_up_loop) s 3 = Some c ->
  to_Z count_up_ops c = wrap (width_of count_up_ops)
    (eval_chrec (inv_env count_up_loop count_up_ops s) count_up_chrec
      (stay_arrivals ssa_edge_encoding count_up_loop es)).
Proof.
  exact (scev_sound (activation (fun _ _ => None) count_up 0) label_encoding ssa_edge_encoding
    nat_encoding count_up_inventory count_up_loop count_up_ops 3 count_up_chrec
    count_up_loop_laws count_up_ops_laws count_up_recognise).
Qed.

(** The generic exact-trip theorem bounds every valid actual count-up activation prefix. *)
Theorem count_up_trip_bound : forall s0 es s t,
  initial (activation (fun _ _ => None) count_up 0) s0 ->
  run_edges (activation (fun _ _ => None) count_up 0) (base (lssa count_up_loop)) s0 es s ->
  point (base (lssa count_up_loop)) s = lheader count_up_loop ->
  trip_count (signed_inv_env count_up_loop count_up_ops Unsigned s) 32%positive Unsigned CmpLt
    (signed_chrec 32%positive Unsigned count_up_chrec)
    (signed_iexpr 32%positive Unsigned (IVar count_up_n)) = Some t ->
  nowrap_check 32%positive Unsigned (signed_inv_env count_up_loop count_up_ops Unsigned s)
    (signed_chrec 32%positive Unsigned count_up_chrec)
    (signed_iexpr 32%positive Unsigned (IVar count_up_n)) t = true ->
  (N.of_nat (stay_arrivals ssa_edge_encoding count_up_loop es) <= t)%N.
Proof.
  intros s0 es s t.
  exact (loop_trip_sound (activation (fun _ _ => None) count_up 0) label_encoding
    ssa_edge_encoding nat_encoding count_up_inventory count_up_loop count_up_ops
    (LoopTest CmpLt Unsigned 3 (IVar count_up_n)) count_up_chrec t count_up_loop_laws
    count_up_ops_laws eq_refl count_up_recognise s0 es s).
Qed.
