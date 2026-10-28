(** * Total indexed worklist iteration

    Accessibility turns the indexed engine into a total solver without executable fuel.
    For example, joining around a finite-height cycle returns its reached post-solution.
    Builds on: FixpointWorklist, FixpointCycles, FixpointLeast and OrderLattice. *)

From Stdlib Require Import List Bool Arith PArith Lia Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCycles
  FixpointLeast FixpointWorklist.
Import List.ListNotations.

(** Joining needs finite height; widening needs ranks and a cut of every static flow cycle. *)
Definition terminates {X C A} {S : System.t X C A} (L : lattice A) (SS : System.static S)
  (sch : scheduler X) (st : strategy) : Prop :=
  match st with
  | Joining => inhabited (height L)
  | Widening => inhabited (widening_rank L) /\ cuts_every_cycle SS (widening_point sch)
  end.

(** * Finite proof measures *)

Fixpoint total_sum {B} (f : B -> nat) (xs : list B) : nat :=
  match xs with
  | [] => 0
  | x :: ys => f x + total_sum f ys
  end.

Lemma total_sum_ext {B} (f g : B -> nat) (xs : list B) :
  (forall x, In x xs -> f x = g x) -> total_sum f xs = total_sum g xs.
Proof.
  intro Heq; induction xs as [|x xs IH]; cbn [total_sum]; [reflexivity|].
  rewrite (Heq x (or_introl eq_refl)); rewrite IH; [reflexivity|].
  intros y Hy; apply Heq; now right.
Qed.

Lemma total_sum_le {B} (f g : B -> nat) (xs : list B) :
  (forall x, In x xs -> f x <= g x) -> total_sum f xs <= total_sum g xs.
Proof.
  intro Hle; induction xs as [|x xs IH]; cbn [total_sum]; [lia|].
  assert (Hhead := Hle x (or_introl eq_refl)).
  assert (Htail : total_sum f xs <= total_sum g xs).
  { apply IH; intros y Hy; apply Hle; now right. }
  lia.
Qed.

Lemma total_sum_lt {B} (f g : B -> nat) (xs : list B) :
  (forall x, In x xs -> f x <= g x) ->
  (exists x, In x xs /\ f x < g x) -> total_sum f xs < total_sum g xs.
Proof.
  intros Hle [y [Hy Hlt]]; induction xs as [|x xs IH]; [contradiction|].
  cbn [total_sum]; destruct Hy as [Heq|Hy].
  - subst y; pose proof (total_sum_le f g xs (fun z Hz => Hle z (or_intror Hz))); lia.
  - assert (Hhead := Hle x (or_introl eq_refl)).
    assert (Htail : total_sum f xs < total_sum g xs).
    { apply IH; [intros z Hz; apply Hle; now right|exact Hy]. }
    lia.
Qed.

Lemma total_sum_app {B} (f : B -> nat) (xs ys : list B) :
  total_sum f (xs ++ ys) = total_sum f xs + total_sum f ys.
Proof.
  induction xs as [|x xs IH]; cbn [app total_sum]; [reflexivity|rewrite IH; lia].
Qed.

Lemma total_sum_flat_map {B D} (f : D -> nat) (g : B -> list D) (xs : list B) :
  total_sum f (flat_map g xs) = total_sum (fun x => total_sum f (g x)) xs.
Proof.
  induction xs as [|x xs IH]; cbn [flat_map total_sum]; [reflexivity|].
  rewrite total_sum_app, IH; reflexivity.
Qed.

Lemma total_sum_filter {B} (f : B -> nat) (p : B -> bool) (xs : list B) :
  total_sum f (filter p xs) = total_sum (fun x => if p x then f x else 0) xs.
Proof.
  induction xs as [|x xs IH]; cbn [filter total_sum]; [reflexivity|].
  destruct (p x); cbn [total_sum]; rewrite IH; reflexivity.
Qed.

Lemma total_sum_incl {B} (f : B -> nat) (xs ys : list B) :
  NoDup xs -> incl xs ys -> total_sum f xs <= total_sum f ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys Hnodup Hincl; [cbn [total_sum]; lia|].
  inversion Hnodup as [|? ? Hfresh Htail]; subst.
  destruct (in_split x ys (Hincl x (or_introl eq_refl))) as [before [after Heq]].
  subst ys; rewrite total_sum_app; cbn [total_sum].
  assert (Hincl' : incl xs (before ++ after)).
  { intros y Hy; specialize (Hincl y (or_intror Hy)).
    apply in_app_or in Hincl; apply in_or_app; destruct Hincl as [Hin|[Heq|Hin]];
      [now left|subst y; contradiction|now right]. }
  specialize (IH (before ++ after) Htail Hincl').
  rewrite total_sum_app in IH; cbn [total_sum]; lia.
Qed.

Section FiniteAccessibility.
Context {B : Type} (R : B -> B -> Prop) (universe : list B).
Hypothesis Hclosed : forall y x, R y x -> In y universe.
Hypothesis Hacyclic : forall x, ~ clos_trans B R x x.

Fixpoint total_path (x : B) (xs : list B) : Prop :=
  match xs with
  | [] => True
  | y :: ys => R y x /\ total_path y ys
  end.

Lemma total_path_member (x y : B) (xs : list B) :
  total_path x xs -> In y xs -> clos_trans B R y x.
Proof.
  revert x; induction xs as [|z xs IH]; intros x Hpath Hin; [contradiction|].
  destruct Hpath as [Hz Hpath]; destruct Hin as [Heq|Hin].
  - subst y; apply t_step; exact Hz.
  - eapply t_trans; [apply (IH z Hpath Hin)|apply t_step; exact Hz].
Qed.

Lemma total_path_nodup (x : B) (xs : list B) :
  total_path x xs -> NoDup (x :: xs).
Proof.
  revert x; induction xs as [|y xs IH]; intros x Hpath.
  - constructor; [intro Hin; exact Hin|constructor].
  - destruct Hpath as [Hy Hpath]; constructor.
    + intro Hin; apply (Hacyclic x); apply (total_path_member x x (y :: xs)).
      * split; assumption.
      * exact Hin.
    + apply IH; exact Hpath.
Qed.

Lemma total_path_closed (x : B) (xs : list B) :
  total_path x xs -> incl xs universe.
Proof.
  revert x; induction xs as [|y xs IH]; intros x Hpath z Hin; [contradiction|].
  destruct Hpath as [Hy Hpath]; destruct Hin as [Heq|Hin].
  - subst z; eapply Hclosed; exact Hy.
  - apply (IH y Hpath z Hin).
Qed.

Lemma total_bounded_path_acc (n : nat) (x : B) :
  (forall xs, length xs = n -> ~ total_path x xs) -> Acc R x.
Proof.
  revert x; induction n as [|n IH]; intros x Hbound.
  - exfalso; apply (Hbound [] eq_refl); exact I.
  - constructor; intros y Hy; apply IH; intros xs Hlength Hpath.
    apply (Hbound (y :: xs)); [cbn; now rewrite Hlength|split; assumption].
Qed.

Lemma total_finite_wf : well_founded R.
Proof.
  intro x; apply (total_bounded_path_acc (Datatypes.S (length universe))).
  intros xs Hlength Hpath.
  pose proof (total_path_nodup x xs Hpath) as Hnodup.
  inversion Hnodup as [|? ? Hfresh Htail]; subst.
  pose proof (NoDup_incl_length Htail (total_path_closed x xs Hpath)); lia.
Qed.

End FiniteAccessibility.

Fixpoint total_evidence_sum {B} (xs : list B) :
  (forall x, In x xs -> nat) -> nat :=
  match xs as ys return (forall x, In x ys -> nat) -> nat with
  | [] => fun _ => 0
  | x :: ys => fun f => f x (or_introl eq_refl) +
      total_evidence_sum ys (fun y Hy => f y (or_intror Hy))
  end.

Lemma total_evidence_sum_ext {B} (xs : list B) (f g : forall x, In x xs -> nat) :
  (forall x Hx, f x Hx = g x Hx) -> total_evidence_sum xs f = total_evidence_sum xs g.
Proof.
  revert f g; induction xs as [|x xs IH]; intros f g Heq; cbn [total_evidence_sum].
  - reflexivity.
  - f_equal; [apply Heq|apply IH; intros y Hy; apply Heq].
Qed.

Lemma total_evidence_sum_plain {B} (xs : list B) (f : B -> nat) :
  total_evidence_sum xs (fun x _ => f x) = total_sum f xs.
Proof.
  induction xs as [|x xs IH]; cbn [total_evidence_sum total_sum];
    [reflexivity|rewrite IH; reflexivity].
Qed.

Definition total_outputs {X C A} {S : System.t X C A} (SS : System.static S) (c : C) :
  list X := System.target S c :: side_targets SS c.

Definition total_unknowns {X C A} {S : System.t X C A} (SS : System.static S) : list X :=
  flat_map (total_outputs SS) (System.constraints S).

Lemma total_run_outputs {X C A} {S : System.t X C A} (SS : System.static S)
  (c : C) (s : X -> A) (x : X) (a : A) :
  In (x, a) ((System.target S c, Query.eval (System.rhs S c) s) ::
    Query.sides (System.rhs S c) s) -> In x (total_outputs SS c).
Proof.
  intros [Heq|Hin]; [inversion Heq; now left|].
  right; apply (System.sides_within SS c s).
  apply in_map_iff; exists (x, a); split; [reflexivity|exact Hin].
Qed.

Lemma total_run_unknowns {X C A} {S : System.t X C A} (SS : System.static S)
  (c : C) (s : X -> A) : In c (System.constraints S) -> forall x a,
  In (x, a) ((System.target S c, Query.eval (System.rhs S c) s) ::
    Query.sides (System.rhs S c) s) -> In x (total_unknowns SS).
Proof.
  intros Hc x a Hin; apply in_flat_map; exists c; split; [exact Hc|].
  apply (total_run_outputs SS c s x a Hin).
Qed.

Section WideningWeights.
Context {X C A : Type} (EX : encoding X) (S : System.t X C A) (SS : System.static S)
  (ix : sys_index X C) (W : X -> bool).
Hypothesis Hix : sys_index_laws EX S SS ix.
Hypothesis Hcut : cuts_every_cycle SS W.

Definition total_nonwidening_outputs (c : C) : list X :=
  filter (fun x => negb (W x)) (total_outputs SS c).

Definition total_next (x : X) : list X :=
  flat_map total_nonwidening_outputs (readers_of EX ix x).

Lemma total_next_flow (x y : X) :
  In y (total_next x) -> flows SS x y /\ W y = false.
Proof.
  intro Hin; apply in_flat_map in Hin; destruct Hin as [c [Hreader Hout]].
  apply (readers_agree Hix) in Hreader; destruct Hreader as [Hc Hread].
  apply filter_In in Hout; destruct Hout as [Hout HW]; apply negb_true_iff in HW.
  split; [exists c; split; [exact Hc|]; split; [exact Hread|]|exact HW].
  destruct Hout as [Heq|Hin]; [now left|now right].
Qed.

Lemma total_next_closed (x y : X) : In y (total_next x) -> In y (total_unknowns SS).
Proof.
  intro Hin; apply in_flat_map in Hin; destruct Hin as [c [Hreader Hout]].
  apply (readers_agree Hix) in Hreader; apply filter_In in Hout.
  apply in_flat_map; exists c; split; [exact (proj1 Hreader)|exact (proj1 Hout)].
Qed.

Lemma total_next_wf : well_founded (fun y x => In y (total_next x)).
Proof.
  apply (total_finite_wf _ (total_unknowns SS)); [intros y x; apply total_next_closed|].
  intros x Hcycle; apply (Hcut x).
  assert (Hreverse : forall a b,
    clos_trans X (fun y x => In y (total_next x)) a b ->
    clos_trans X (fun y z => flows SS y z /\ W z = false) b a).
  { intros a b Hpath; induction Hpath as [a b Hedge|a b c Hab IH1 Hbc IH2].
    - apply t_step; apply total_next_flow; exact Hedge.
    - eapply t_trans; [exact IH2|exact IH1]. }
  apply (Hreverse x x Hcycle).
Qed.

Definition total_weight_body (x : X) (rec : forall y, In y (total_next x) -> nat) : nat :=
  length (readers_of EX ix x) + total_evidence_sum (total_next x) rec.

Definition total_unknown_weight : X -> nat :=
  Fix total_next_wf (fun _ => nat) total_weight_body.

Lemma total_unknown_weight_eq (x : X) :
  total_unknown_weight x = length (readers_of EX ix x) +
    total_sum total_unknown_weight (total_next x).
Proof.
  unfold total_unknown_weight at 1; rewrite Fix_eq.
  - unfold total_weight_body; rewrite total_evidence_sum_plain; reflexivity.
  - intros y f g Heq; unfold total_weight_body; f_equal.
    apply total_evidence_sum_ext; exact Heq.
Qed.

Definition total_constraint_weight (c : C) : nat :=
  1 + total_sum total_unknown_weight (total_nonwidening_outputs c).

Lemma total_reader_weight (x : X) :
  total_sum total_constraint_weight (readers_of EX ix x) = total_unknown_weight x.
Proof.
  rewrite (total_unknown_weight_eq x); unfold total_next; rewrite total_sum_flat_map.
  change (total_sum (fun c => 1 +
    total_sum total_unknown_weight (total_nonwidening_outputs c)) (readers_of EX ix x) =
    length (readers_of EX ix x) +
    total_sum (fun c => total_sum total_unknown_weight (total_nonwidening_outputs c))
      (readers_of EX ix x)).
  induction (readers_of EX ix x) as [|c cs IH]; cbn [total_sum length]; lia.
Qed.

Lemma total_constraint_weight_dominates (c : C) :
  total_sum total_constraint_weight
    (flat_map (readers_of EX ix) (total_nonwidening_outputs c)) <
    total_constraint_weight c.
Proof.
  rewrite total_sum_flat_map; unfold total_constraint_weight at 2.
  assert (Heq : total_sum (fun x => total_sum total_constraint_weight (readers_of EX ix x))
    (total_nonwidening_outputs c) =
    total_sum total_unknown_weight (total_nonwidening_outputs c)).
  { apply total_sum_ext; intros x Hx; apply total_reader_weight. }
  rewrite Heq; lia.
Qed.

End WideningWeights.

(** * Queue support and value-change credit *)

Definition total_present {C} (EC : encoding C) (q : PQueue.t C) (c : C) : bool :=
  match PQueue.priority EC c q with
  | Some _ => true
  | None => false
  end.

Lemma total_present_spec {C} (EC : encoding C) (q : PQueue.t C) (c : C) :
  total_present EC q c = true <-> PQueue.priority EC c q <> None.
Proof.
  unfold total_present; destruct (PQueue.priority EC c q); intuition discriminate.
Qed.

Lemma total_present_pop {C} (EC : encoding C) (q q' : PQueue.t C) (p : positive) (c d : C) :
  PQueue.wf EC q -> PQueue.pop EC q = Some (p, c, q') ->
  total_present EC q' d = true -> total_present EC q d = true.
Proof.
  intros Hwf Hpop Hpending.
  destruct (PQueue.pop_rest EC q q' p c Hwf Hpop) as [Hnone [Hother Hsize]].
  destruct (Pos.eq_dec (encode EC d) (encode EC c)) as [Heq|Hne].
  - apply (encode_injective EC) in Heq; subst d.
    apply total_present_spec in Hpending; contradiction.
  - unfold total_present in *; rewrite Hother in Hpending; [exact Hpending|].
    intro Heq; subst d; contradiction.
Qed.

Definition total_queue_weight {C} (EC : encoding C) (cs : list C) (w : C -> nat)
  (q : PQueue.t C) : nat := total_sum w (filter (total_present EC q) cs).

Lemma total_queue_weight_bound {C} (EC : encoding C) (cs : list C) (w : C -> nat)
  (q q' : PQueue.t C) (adds : list C) :
  NoDup cs ->
  (forall c, total_present EC q' c = true -> total_present EC q c = true \/ In c adds) ->
  total_queue_weight EC cs w q' <= total_queue_weight EC cs w q + total_sum w adds.
Proof.
  intros Hnodup Hsupport; unfold total_queue_weight; rewrite <- total_sum_app.
  apply total_sum_incl; [apply NoDup_filter; exact Hnodup|].
  intros c Hin; apply filter_In in Hin; destruct Hin as [Hc Hpending].
  apply in_or_app; destruct (Hsupport c Hpending) as [Hkeep|Hadd].
  - left; apply filter_In; split; assumption.
  - now right.
Qed.

Lemma total_queue_weight_pop {C} (EC : encoding C) (cs : list C) (w : C -> nat)
  (q q' : PQueue.t C) (p : positive) (c : C) :
  NoDup cs -> In c cs -> PQueue.wf EC q -> PQueue.pop EC q = Some (p, c, q') ->
  total_queue_weight EC cs w q = w c + total_queue_weight EC cs w q'.
Proof.
  intros Hnodup Hc Hwf Hpop.
  destruct (PQueue.pop_rest EC q q' p c Hwf Hpop) as [Hnone [Hother Hsize]].
  destruct (PQueue.pop_min EC q q' p c Hwf Hpop) as [Hsome Hmin].
  unfold total_queue_weight; rewrite !total_sum_filter.
  induction cs as [|d cs IH]; [contradiction|].
  inversion Hnodup as [|? ? Hfresh Htail]; subst.
  destruct Hc as [Heq|Hc].
  - subst d; cbn [total_sum].
    assert (Hyes : total_present EC q c = true) by (unfold total_present; now rewrite Hsome).
    assert (Hno : total_present EC q' c = false) by (unfold total_present; now rewrite Hnone).
    rewrite Hyes, Hno; cbn.
    assert (Heq : total_sum (fun d => if total_present EC q d then w d else 0) cs =
      total_sum (fun d => if total_present EC q' d then w d else 0) cs).
    { apply total_sum_ext; intros d Hd; unfold total_present.
      rewrite Hother; [reflexivity|intro Heq; subst d; contradiction]. }
    rewrite Heq; lia.
  - assert (Hdc : d <> c) by (intro Heq; subst d; contradiction).
    assert (Heq : total_present EC q' d = total_present EC q d).
    { unfold total_present; rewrite Hother by exact Hdc; reflexivity. }
    cbn [total_sum]; rewrite Heq; specialize (IH Htail Hc); lia.
Qed.

Section TerminationInvariant.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (ix : sys_index X C) (dep : dependencies S).
Hypothesis Hix : sys_index_laws EX S SS ix.

Definition total_recorded_valid (r : Map.t X (FinSet.t C)) : Prop :=
  recorded_wf EX EC r /\ forall x c,
    FinSet.mem EC c (recorded_at EX r x) = true ->
    In c (System.constraints S) /\ In x (deps SS c).

Hypothesis Hreaders : forall r, total_recorded_valid r -> forall x,
  incl (engine_readers EX dep r x) (readers_of EX ix x).

Definition total_state_valid (e : Engine.t X C A) : Prop :=
  PQueue.wf EC (Engine.queue e) /\ total_recorded_valid (Engine.recorded e) /\
  forall c, total_present EC (Engine.queue e) c = true -> In c (System.constraints S).

Lemma total_initial_valid : total_state_valid (initial_state EC sch S).
Proof.
  split; [apply enqueue_wf, PQueue.wf_empty|]; split.
  - split; [apply recorded_empty_wf|].
    intros x c Hin; change (FinSet.mem EC c (recorded_at EX Map.empty x) = true) in Hin.
    unfold recorded_at in Hin; rewrite Map.get_empty in Hin.
    rewrite FinSet.mem_empty in Hin; discriminate.
  - intros c Hpending; apply total_present_spec in Hpending.
    cbn [initial_state Engine.queue] in Hpending.
    apply enqueue_member in Hpending; [|apply PQueue.wf_empty].
    destruct Hpending as [Hin|Hbad]; [exact Hin|].
    rewrite PQueue.priority_empty in Hbad; contradiction.
Qed.

Lemma total_learn_valid (c : C) (s : X -> A) (r : Map.t X (FinSet.t C)) :
  In c (System.constraints S) -> total_recorded_valid r ->
  total_recorded_valid
    (learn_reads EX EC S dep c (Query.reads (System.rhs S c) s) r).
Proof.
  intros Hc [Hwf Hvalid]; unfold learn_reads; destruct dep; [now split|].
  split; [apply record_reads_wf; exact Hwf|].
  intros x d Hin; apply record_reads_member in Hin.
  destruct Hin as [[Heq Hread]|Hin].
  - subst d; split; [exact Hc|apply (System.reads_within SS c s); exact Hread].
  - apply Hvalid; exact Hin.
Qed.

Variables (tracked : X -> bool) (credit : X -> A -> nat).
Hypothesis Hprogress : forall x old a, In x (total_unknowns SS) -> leb L a old = false ->
  credit x (update_value L sch st x old a) <= credit x old /\
  (credit x (update_value L sch st x old a) = credit x old -> tracked x = false).

Definition total_credit (m : assignment X A) : nat :=
  total_sum (fun x => credit x (lookup EX L m x)) (total_unknowns SS).

Lemma total_credit_set (m : assignment X A) (x : X) (v : A) :
  In x (total_unknowns SS) -> credit x v <= credit x (lookup EX L m x) ->
  total_credit (Map.set EX x v m) <= total_credit m /\
  (total_credit (Map.set EX x v m) = total_credit m ->
    credit x v = credit x (lookup EX L m x)).
Proof.
  intros Hx Hle.
  assert (Hpoint : forall y, In y (total_unknowns SS) ->
    credit y (lookup EX L (Map.set EX x v m) y) <= credit y (lookup EX L m y)).
  { intros y Hy; destruct (Pos.eq_dec (encode EX y) (encode EX x)) as [Heq|Hne].
    - apply (encode_injective EX) in Heq; subst y; rewrite lookup_set_same; exact Hle.
    - rewrite lookup_set_other; [lia|intro Heq; subst y; contradiction]. }
  split; [apply total_sum_le; exact Hpoint|].
  intro Heq; destruct (Nat.eq_dec (credit x v) (credit x (lookup EX L m x))) as [Hsame|Hne];
    [exact Hsame|].
  assert (Hstrict : total_credit (Map.set EX x v m) < total_credit m).
  { apply total_sum_lt; [exact Hpoint|exists x; split; [exact Hx|]].
    rewrite lookup_set_same; lia. }
  lia.
Qed.

Lemma total_update_measure (r : Map.t X (FinSet.t C)) (x : X) (a : A)
  (m m' : assignment X A) (q q' : PQueue.t C) :
  total_recorded_valid r -> In x (total_unknowns SS) -> PQueue.wf EC q ->
  engine_update EX EC L sch st S dep r (x, a) (m, q) = (m', q') ->
  PQueue.wf EC q' /\ total_credit m' <= total_credit m /\
  forall d, total_present EC q' d = true -> total_present EC q d = true \/
    (In d (readers_of EX ix x) /\ (total_credit m' = total_credit m -> tracked x = false)).
Proof.
  intros Hr Hx Hwf Hupdate; unfold engine_update in Hupdate; cbn in Hupdate.
  destruct (leb L a (lookup EX L m x)) eqn:Hbelow; inversion Hupdate; subst m' q'.
  - split; [exact Hwf|]; split; [lia|intros d Hd; now left].
  - destruct (Hprogress x (lookup EX L m x) a Hx Hbelow) as [Hle Htracked].
    destruct (total_credit_set m x _ Hx Hle) as [Hsum Hsame].
    split; [apply enqueue_wf; exact Hwf|]; split; [exact Hsum|].
    intros d Hd; apply total_present_spec in Hd.
    apply enqueue_member in Hd; [|exact Hwf].
    destruct Hd as [Hreader|Hold].
    + right; split; [apply (Hreaders r Hr x d Hreader)|].
      intro Heq; apply Htracked, Hsame; exact Heq.
    + left; apply total_present_spec; exact Hold.
Qed.

Lemma total_updates_measure (r : Map.t X (FinSet.t C)) (ups : list (X * A))
  (m m' : assignment X A) (q q' : PQueue.t C) :
  total_recorded_valid r -> (forall x a, In (x, a) ups -> In x (total_unknowns SS)) ->
  PQueue.wf EC q -> engine_updates EX EC L sch st S dep r ups (m, q) = (m', q') ->
  PQueue.wf EC q' /\ total_credit m' <= total_credit m /\
  forall d, total_present EC q' d = true -> total_present EC q d = true \/
    exists x a, In (x, a) ups /\ In d (readers_of EX ix x) /\
      (total_credit m' = total_credit m -> tracked x = false).
Proof.
  revert m q; induction ups as [|[x a] ups IH]; intros m q Hr Houtputs Hwf Hupdates.
  - cbn [engine_updates] in Hupdates; inversion Hupdates; subst m' q'.
    split; [exact Hwf|]; split; [lia|intros d Hd; now left].
  - change (engine_updates EX EC L sch st S dep r ups
      (engine_update EX EC L sch st S dep r (x, a) (m, q)) = (m', q')) in Hupdates.
    destruct (engine_update EX EC L sch st S dep r (x, a) (m, q)) as [m1 q1] eqn:Hone.
    destruct (total_update_measure r x a m m1 q q1 Hr (Houtputs x a (or_introl eq_refl))
      Hwf Hone) as [Hwf1 [Hle1 Hsupport1]].
    destruct (IH m1 q1 Hr (fun y b Hb => Houtputs y b (or_intror Hb)) Hwf1 Hupdates)
      as [Hwf' [Hle2 Hsupport2]].
    split; [exact Hwf'|]; split; [lia|].
    intros d Hd; destruct (Hsupport2 d Hd) as [Hkeep|[y [b [Hin [Hreader Htracked]]]]].
    + destruct (Hsupport1 d Hkeep) as [Hold|[Hreader Htracked]]; [now left|].
      right; exists x, a; split; [now left|]; split; [exact Hreader|].
      intro Heq; apply Htracked; lia.
    + right; exists y, b; split; [now right|]; split; [exact Hreader|].
      intro Heq; apply Htracked; lia.
Qed.

Definition total_constraints : list C :=
  FinSet.elements (FinSet.of_list EC (System.constraints S)).

Lemma total_constraints_wf : FinSet.wf EC (FinSet.of_list EC (System.constraints S)).
Proof.
  unfold FinSet.of_list; apply FinSet.wf_fold_add, Map.wf_empty.
Qed.

Lemma total_constraints_nodup : NoDup total_constraints.
Proof.
  apply (FinSet.elements_nodup EC), total_constraints_wf.
Qed.

Lemma total_constraints_spec (c : C) : In c total_constraints <-> In c (System.constraints S).
Proof.
  unfold total_constraints; rewrite (FinSet.elements_spec EC c _ total_constraints_wf).
  apply FinSet.of_list_spec.
Qed.

Variable weight : C -> nat.
Hypothesis Hweight : forall c, In c (System.constraints S) ->
  total_sum weight (flat_map (readers_of EX ix)
    (filter (fun x => negb (tracked x)) (total_outputs SS c))) < weight c.

Lemma total_unchanged_queue_weight (c : C) (s : X -> A)
  (m m' : assignment X A) (q q' : PQueue.t C) :
  (forall d, total_present EC q' d = true -> total_present EC q d = true \/
    exists x a, In (x, a)
      ((System.target S c, Query.eval (System.rhs S c) s) :: Query.sides (System.rhs S c) s) /\
      In d (readers_of EX ix x) /\ (total_credit m' = total_credit m -> tracked x = false)) ->
  total_credit m' = total_credit m ->
  total_queue_weight EC total_constraints weight q' <=
    total_queue_weight EC total_constraints weight q +
    total_sum weight (flat_map (readers_of EX ix)
      (filter (fun x => negb (tracked x)) (total_outputs SS c))).
Proof.
  intros Hsupport Heq; apply total_queue_weight_bound; [apply total_constraints_nodup|].
  intros d Hd; destruct (Hsupport d Hd) as [Hkeep|[x [a [Hin [Hreader Htracked]]]]];
    [now left|right].
  apply in_flat_map; exists x; split; [apply filter_In; split|exact Hreader].
  - apply (total_run_outputs SS c s x a Hin).
  - apply negb_true_iff, Htracked; exact Heq.
Qed.

Lemma total_step_measure (e e' : Engine.t X C A) :
  total_state_valid e -> engine_step EX EC L sch st S dep e = Some e' ->
  total_state_valid e' /\
  (total_credit (Engine.current e') < total_credit (Engine.current e) \/
    (total_credit (Engine.current e') = total_credit (Engine.current e) /\
      total_queue_weight EC total_constraints weight (Engine.queue e') <
      total_queue_weight EC total_constraints weight (Engine.queue e))).
Proof.
  intros [Hwf [Hr Hqueue]] Hstep; unfold engine_step in Hstep.
  destruct (PQueue.pop EC (Engine.queue e)) as [[[p c] q]|] eqn:Hpop; [|discriminate].
  assert (Hc : In c (System.constraints S)).
  { apply Hqueue, total_present_spec; destruct (PQueue.pop_min EC _ _ _ _ Hwf Hpop)
      as [Hsome Hmin]; congruence. }
  rewrite run_spec in Hstep.
  set (s := lookup EX L (Engine.current e)) in *.
  set (r := learn_reads EX EC S dep c (Query.reads (System.rhs S c) s)
    (Engine.recorded e)).
  change ((let '(m', q') := engine_updates EX EC L sch st S dep r
    ((System.target S c, Query.eval (System.rhs S c) s) :: Query.sides (System.rhs S c) s)
    (Engine.current e, q) in Some (Engine.State m' q' r)) = Some e') in Hstep.
  destruct (engine_updates EX EC L sch st S dep r
    ((System.target S c, Query.eval (System.rhs S c) s) :: Query.sides (System.rhs S c) s)
    (Engine.current e, q)) as [m' q'] eqn:Hupdates.
  inversion Hstep; subst e'; clear Hstep.
  assert (Hr' : total_recorded_valid r) by (apply total_learn_valid; assumption).
  destruct (total_updates_measure r _ _ _ _ _ Hr' (total_run_unknowns SS c s Hc)
    (PQueue.wf_pop EC _ _ _ _ Hwf Hpop) Hupdates) as [Hwf' [Hle Hsupport]].
  split.
  - split; [exact Hwf'|]; split; [exact Hr'|].
    intros d Hd; destruct (Hsupport d Hd) as [Hkeep|[x [a [Hin [Hreader Htracked]]]]].
    + apply Hqueue, (total_present_pop EC _ _ _ _ d Hwf Hpop Hkeep).
    + apply (readers_agree Hix) in Hreader; exact (proj1 Hreader).
  - cbn [Engine.current Engine.queue] in *.
    destruct (Nat.lt_ge_cases (total_credit m') (total_credit (Engine.current e)))
      as [Hlt|Hge]; [now left|right].
    assert (Heq : total_credit m' = total_credit (Engine.current e)) by lia.
    split; [exact Heq|].
    pose proof (total_unchanged_queue_weight c s _ _ _ _ Hsupport Heq) as Hbound.
    pose proof (total_queue_weight_pop EC total_constraints weight _ _ _ c
      total_constraints_nodup (proj2 (total_constraints_spec c) Hc) Hwf Hpop) as Hpopweight.
    pose proof (Hweight c Hc) as Hdominates; lia.
Qed.

Lemma total_valid_acc (e : Engine.t X C A) :
  total_state_valid e -> Acc (engine_rel EX EC L sch st S dep) e.
Proof.
  assert (Hcredit : forall n e, total_credit (Engine.current e) = n ->
    total_state_valid e -> Acc (engine_rel EX EC L sch st S dep) e).
  { intro n; induction n as [n IHcredit] using lt_wf_ind.
    assert (Hqueue : forall k e, total_credit (Engine.current e) = n ->
      total_queue_weight EC total_constraints weight (Engine.queue e) = k ->
      total_state_valid e -> Acc (engine_rel EX EC L sch st S dep) e).
    { intro k; induction k as [k IHqueue] using lt_wf_ind.
      intros a Hn Hk Hvalid; constructor; intros b Hstep.
      destruct (total_step_measure a b Hvalid Hstep) as [Hvalid' [Hless|[Heq Hless]]].
      - apply (IHcredit (total_credit (Engine.current b))); [lia|reflexivity|exact Hvalid'].
      - apply (IHqueue (total_queue_weight EC total_constraints weight (Engine.queue b)));
          [lia|lia|reflexivity|exact Hvalid']. }
    intros a Hn Hvalid; eapply Hqueue; [exact Hn|reflexivity|exact Hvalid]. }
  intro Hvalid; eapply Hcredit; [reflexivity|exact Hvalid].
Qed.

End TerminationInvariant.

(** * Accessibility from height or widening evidence *)

Lemma total_height_progress {X A} (L : lattice A) (HL : lattice_laws L)
  (H : height L) (sch : scheduler X) (x : X) (old a : A) :
  leb L a old = false ->
  bound H - rank H (update_value L sch Joining x old a) <= bound H - rank H old /\
  (bound H - rank H (update_value L sch Joining x old a) = bound H - rank H old ->
    true = false).
Proof.
  intro Hbelow.
  assert (Hstrict : leb L (join L old a) old = false).
  { destruct (leb L (join L old a) old) eqn:Hjoin; [|reflexivity].
    pose proof (leb_trans HL a (join L old a) old (join_upper_r HL old a) Hjoin).
    congruence. }
  pose proof (join_rank_grows H old a Hstrict).
  pose proof (rank_bounded H old); pose proof (rank_bounded H (join L old a)).
  cbn [update_value]; split; [lia|intro Heq; exfalso; lia].
Qed.

Lemma total_join_weight {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (c : C) :
  total_sum (fun _ : C => 1) (flat_map (readers_of EX ix)
    (filter (fun _ : X => negb true) (total_outputs SS c))) < 1.
Proof.
  assert (Hnil : filter (fun _ : X => negb true) (total_outputs SS c) = []).
  { induction (total_outputs SS c) as [|x xs IH]; cbn [filter negb]; assumption || reflexivity. }
  rewrite Hnil; cbn [flat_map total_sum]; lia.
Qed.

Section EvidenceAccessibility.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (S : System.t X C A) (sch : scheduler X) (st : strategy)
  (SS : System.static S) (ix : sys_index X C).
Hypotheses (HL : lattice_laws L) (HT : terminates L SS sch st)
  (Hix : sys_index_laws EX S SS ix).

Lemma total_evidence_acc (dep : dependencies S) :
  (forall r, total_recorded_valid EX EC S SS r -> forall x,
    incl (engine_readers EX dep r x) (readers_of EX ix x)) ->
  Acc (engine_rel EX EC L sch st S dep) (initial_state EC sch S).
Proof.
  intro Hreaders; destruct st.
  - destruct HT as [Hheight].
    eapply (total_valid_acc EX EC L sch Joining S SS ix dep Hix Hreaders
      (fun _ => true) (fun _ a => bound Hheight - rank Hheight a)).
    + intros x old a Hx Hbelow; apply (total_height_progress L HL Hheight sch x old a Hbelow).
    + intros c Hc; apply total_join_weight.
    + apply total_initial_valid.
  - destruct HT as [[W] Hcut].
    assert (Hprogress : forall x old a, In x (total_unknowns SS) -> leb L a old = false ->
      (if widening_point sch x then wrank W (update_value L sch Widening x old a) else 0) <=
        (if widening_point sch x then wrank W old else 0) /\
      ((if widening_point sch x then wrank W (update_value L sch Widening x old a) else 0) =
        (if widening_point sch x then wrank W old else 0) -> widening_point sch x = false)).
    { intros x old a Hx Hbelow; unfold update_value.
      destruct (widening_point sch x) eqn:Hpoint; cbn.
      - pose proof (widen_rank_progress W old a Hbelow); split; [lia|intro Heq; exfalso; lia].
      - split; [lia|reflexivity]. }
    eapply (total_valid_acc EX EC L sch Widening S SS ix dep Hix Hreaders
      (widening_point sch)
      (fun x a => if widening_point sch x then wrank W a else 0) Hprogress
      (total_constraint_weight EX S SS ix (widening_point sch) Hix Hcut)).
    + intros c Hc; apply total_constraint_weight_dominates.
    + apply total_initial_valid.
Qed.

End EvidenceAccessibility.

Lemma total_sigma_projection {B D} (P : D -> Prop) (o : option B)
  (some : B -> D) (none : D) (Hsome : forall b, o = Some b -> P (some b)) (Hnone : P none) :
  proj1_sig ((match o as result return o = result -> {d : D | P d} with
    | Some b => fun Heq => exist _ (some b) (Hsome b Heq)
    | None => fun _ => exist _ none Hnone
    end) eq_refl) = match o with
    | Some b => some b
    | None => none
    end.
Proof.
  destruct o; reflexivity.
Qed.

Section TotalLaws.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (S : System.t X C A).
Variables (sch : scheduler X) (st : strategy).

(** Termination evidence makes both declared and recorded engine chains accessible. *)
Theorem engine_acc (SS : System.static S) (ix : sys_index X C) : lattice_laws L ->
  terminates L SS sch st -> sys_index_laws EX S SS ix ->
  Acc (engine_rel EX EC L sch st S (Declared SS ix)) (initial_state EC sch S) /\
  Acc (engine_rel EX EC L sch st S Recorded) (initial_state EC sch S).
Proof.
  intros HL HT Hix; split; apply (total_evidence_acc EX EC L S sch st SS ix HL HT Hix).
  - intros r Hr x d Hd; exact Hd.
  - intros r [Hwf Hvalid] x d Hd; apply (readers_agree Hix).
    apply Hvalid, (FinSet.elements_spec EC); [apply Hwf|exact Hd].
Qed.

(** Above some positive fuel threshold, both dependency modes finish. *)
Theorem run_worklist_adequate (SS : System.static S) :
  lattice_laws L -> terminates L SS sch st ->
  (exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S (Declared SS (index_system EX S SS)) fuel = Some m') /\
  (exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S Recorded fuel = Some m').
Proof.
  intros HL HT.
  destruct (engine_acc SS (index_system EX S SS) HL HT (index_system_laws EX S SS))
    as [Hdeclared Hrecorded].
  split; apply run_worklist_acc; assumption.
Qed.

(** Enough fuel selects the recorded engine result rather than the top fallback. *)
Theorem solve_fuel_exact (T : top L) (HL : lattice_laws L) (SS : System.static S) :
  terminates L SS sch st -> exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S Recorded fuel = Some m' /\
    proj1_sig (solve_fuel EX EC L HL T sch st S fuel) = lookup EX L m'.
Proof.
  intro HT; destruct (run_worklist_adequate SS HL HT) as [_ [f Hfuel]].
  exists f; intros fuel Hge; destruct (Hfuel fuel Hge) as [m Hrun].
  exists m; split; [exact Hrun|].
  unfold solve_fuel; rewrite total_sigma_projection, Hrun; reflexivity.
Qed.

End TotalLaws.

(** * Accessibility-based execution *)

Section TotalExecution.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (dep : dependencies S) (Hdep : dependencies_ok EX dep).
Local Abbreviation step := (engine_step EX EC L sch st S dep).
Local Abbreviation reachable := (engine_reachable EX EC L sch st S dep).

Lemma total_reachable_step (e e' : Engine.t X C A) :
  reachable e -> step e = Some e' -> reachable e'.
Proof.
  intros Hreach Hstep; eapply rt_trans; [exact Hreach|apply rt_step; exact Hstep].
Qed.

(* The map is computational; the post-solution and finite trace are both erased proofs.
   Retaining the trace avoids any equality principle for accessibility or proof fields. *)
Definition total_result (e : Engine.t X C A) : Type :=
  reachable e -> {m : assignment X A | post_solution L S (lookup EX L m) /\
    exists n e', engine_steps EX EC L sch st S dep n e e' /\
      step e' = None /\ Engine.current e' = m}.

Definition total_body (e : Engine.t X C A)
  (rec : forall e', engine_rel EX EC L sch st S dep e' e -> total_result e') : total_result e.
Proof.
  intro Hreach; destruct (step e) as [e'|] eqn:Hstep.
  - destruct (rec e' Hstep (total_reachable_step e e' Hreach Hstep)) as [m Hm].
    refine (exist _ m _); destruct Hm as [Hpost [n [e'' [Hsteps [Hnone Hcurrent]]]]].
    split; [exact Hpost|]; exists (Datatypes.S n), e''; split.
    + apply (engine_steps_cons EX EC L sch st S dep n e e' e'' Hstep Hsteps).
    + split; assumption.
  - refine (exist _ (Engine.current e) _); split.
    + apply (engine_finished_sound EX EC L S sch st dep e HL Hdep Hreach Hstep).
    + exists 0, e; split; [constructor|split; [exact Hstep|reflexivity]].
Defined.

Definition total_execute (e : Engine.t X C A)
  (Hacc : Acc (engine_rel EX EC L sch st S dep) e) : total_result e :=
  Fix_F total_result total_body Hacc.

End TotalExecution.

Definition total_solver_map {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (HT : terminates L SS sch st) :=
  total_execute EX EC L HL sch st S (Declared SS (index_system EX S SS))
    (index_system_laws EX S SS) (initial_state EC sch S)
    (proj1 (engine_acc EX EC L S sch st SS (index_system EX S SS) HL HT
      (index_system_laws EX S SS))) (rt_refl _ _ _).

(** The total solver follows engine steps by Fix on their accessibility proof. *)
Definition solve_total {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (HT : terminates L SS sch st) : {s : X -> A | post_solution L S s} :=
  let result := total_solver_map EX EC L HL sch st S SS HT in
  exist _ (lookup EX L (proj1_sig result)) (proj1 (proj2_sig result)).

(** Every sufficiently long declared fuel run returns the total solver's exact function. *)
Theorem solve_total_run {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (S : System.t X C A) (sch : scheduler X) (st : strategy) (HL : lattice_laws L)
  (SS : System.static S) (HT : terminates L SS sch st) :
  exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S (Declared SS (index_system EX S SS)) fuel = Some m' /\
    proj1_sig (solve_total EX EC L HL sch st S SS HT) = lookup EX L m'.
Proof.
  set (result := total_solver_map EX EC L HL sch st S SS HT).
  destruct (proj2_sig result) as [Hpost [n [e [Hsteps [Hnone Hcurrent]]]]].
  exists (Pos.of_succ_nat n); intros fuel Hge; exists (proj1_sig result); split.
  - apply run_worklist_spec; exists n, e; split.
    + apply Pos2Nat.inj_le in Hge; rewrite SuccNat2Pos.id_succ in Hge; lia.
    + split; [exact Hsteps|split; assumption].
  - reflexivity.
Qed.

Lemma total_completed_runs_unique {X C A} (EX : encoding X) (EC : encoding C)
  (L : lattice A) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (dep : dependencies S) (fuel fuel' : positive) (m m' : assignment X A) :
  run_worklist EX EC L sch st S dep fuel = Some m ->
  run_worklist EX EC L sch st S dep fuel' = Some m' -> m = m'.
Proof.
  intros Hrun Hrun'; apply run_worklist_spec in Hrun; apply run_worklist_spec in Hrun'.
  destruct Hrun as [n [e [Hlt [Hsteps [Hnone Hcurrent]]]]].
  destruct Hrun' as [n' [e' [Hlt' [Hsteps' [Hnone' Hcurrent']]]]].
  pose proof (finished_steps_budget EX EC L sch st S dep (Datatypes.S (n + n')) n
    _ e ltac:(lia) Hsteps Hnone) as Hbudget.
  pose proof (finished_steps_budget EX EC L sch st S dep (Datatypes.S (n + n')) n'
    _ e' ltac:(lia) Hsteps' Hnone') as Hbudget'.
  pose proof (budget_run_unique EX EC L sch st S dep _ _ _ _ Hbudget Hbudget') as Heq.
  rewrite Hcurrent, Hcurrent' in Heq; now inversion Heq.
Qed.

(** * Joining follows the constraint-run semantics *)

Section JoiningRuns.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (S : System.t X C A) (dep : dependencies S).

Lemma total_join_update_lookup (r : Map.t X (FinSet.t C)) (x : X) (a : A)
  (m m' : assignment X A) (q q' : PQueue.t C) :
  engine_update EX EC L sch Joining S dep r (x, a) (m, q) = (m', q') ->
  forall y, lookup EX L m' y = join_update EX L x a (lookup EX L m) y.
Proof.
  intro Hupdate; unfold engine_update in Hupdate; cbn in Hupdate.
  destruct (leb L a (lookup EX L m x)) eqn:Hbelow; inversion Hupdate; subst m' q';
    intro y; unfold join_update;
    destruct (Pos.eqb (encode EX x) (encode EX y)) eqn:Hxy.
  - apply Pos.eqb_eq in Hxy; apply (encode_injective EX) in Hxy; subst y.
    rewrite Hbelow; reflexivity.
  - reflexivity.
  - apply Pos.eqb_eq in Hxy; apply (encode_injective EX) in Hxy; subst y.
    rewrite lookup_set_same, Hbelow; reflexivity.
  - apply lookup_set_other; intro Heq; subst y; rewrite Pos.eqb_refl in Hxy; discriminate.
Qed.

Lemma total_apply_updates_ext (ups : list (X * A)) (s t : X -> A) :
  (forall y, s y = t y) -> forall y, apply_updates EX L ups s y = apply_updates EX L ups t y.
Proof.
  revert s t; induction ups as [|[x a] ups IH]; intros s t Heq y.
  - apply Heq.
  - change (apply_updates EX L ups (join_update EX L x a s) y =
      apply_updates EX L ups (join_update EX L x a t) y).
    apply IH; intro z; unfold join_update; rewrite Heq; reflexivity.
Qed.

Lemma total_join_updates_lookup (r : Map.t X (FinSet.t C)) (ups : list (X * A))
  (m m' : assignment X A) (q q' : PQueue.t C) :
  engine_updates EX EC L sch Joining S dep r ups (m, q) = (m', q') ->
  forall y, lookup EX L m' y = apply_updates EX L ups (lookup EX L m) y.
Proof.
  revert m q; induction ups as [|[x a] ups IH]; intros m q Hupdates y.
  - cbn [engine_updates] in Hupdates; inversion Hupdates; subst m' q'; reflexivity.
  - change (engine_updates EX EC L sch Joining S dep r ups
      (engine_update EX EC L sch Joining S dep r (x, a) (m, q)) = (m', q')) in Hupdates.
    destruct (engine_update EX EC L sch Joining S dep r (x, a) (m, q))
      as [m1 q1] eqn:Hone.
    change (lookup EX L m' y =
      apply_updates EX L ups (join_update EX L x a (lookup EX L m)) y).
    rewrite (IH m1 q1 Hupdates y); apply total_apply_updates_ext.
    intro z; apply (total_join_update_lookup r x a m m1 q q1 Hone z).
Qed.

End JoiningRuns.

Section DeclaredJoiningRuns.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (Hix : sys_index_laws EX S SS ix)
  (Hheight : height L).
Local Abbreviation dep := (Declared SS ix).
Local Abbreviation step := (engine_step EX EC L sch Joining S dep).

Lemma total_join_step_valid (e e' : Engine.t X C A) :
  total_state_valid EX EC S SS e -> step e = Some e' -> total_state_valid EX EC S SS e'.
Proof.
  intros Hvalid Hstep.
  apply (proj1 (total_step_measure EX EC L sch Joining S SS ix dep Hix
    (fun r Hr x d Hd => Hd) (fun _ => true) (fun _ a => bound Hheight - rank Hheight a)
    (fun x old a Hx Hbelow => total_height_progress L HL Hheight sch x old a Hbelow)
    (fun _ => 1) (fun c Hc => total_join_weight EX S SS ix c) e e' Hvalid Hstep)).
Qed.

Lemma total_join_step_raise (e e' : Engine.t X C A) :
  total_state_valid EX EC S SS e -> step e = Some e' ->
  raise EX L S (lookup EX L (Engine.current e)) (lookup EX L (Engine.current e')).
Proof.
  intros [Hwf [Hr Hqueue]] Hstep; unfold engine_step in Hstep.
  destruct (PQueue.pop EC (Engine.queue e)) as [[[p c] q]|] eqn:Hpop; [|discriminate].
  assert (Hc : In c (System.constraints S)).
  { apply Hqueue, total_present_spec.
    destruct (PQueue.pop_min EC _ _ _ _ Hwf Hpop) as [Hsome Hmin]; congruence. }
  rewrite run_spec in Hstep.
  destruct (engine_updates EX EC L sch Joining S dep (Engine.recorded e)
    ((System.target S c, Query.eval (System.rhs S c) (lookup EX L (Engine.current e))) ::
      Query.sides (System.rhs S c) (lookup EX L (Engine.current e))) (Engine.current e, q))
    as [m' q'] eqn:Hupdates.
  inversion Hstep; subst e'; clear Hstep.
  exists c; split; [exact Hc|]; intro y; unfold run_updates; rewrite run_spec.
  apply (total_join_updates_lookup EX EC L sch S dep _ _ _ _ _ _ Hupdates y).
Qed.

Lemma total_join_steps_reached (n : nat) (e : Engine.t X C A) :
  engine_steps EX EC L sch Joining S dep n (initial_state EC sch S) e ->
  total_state_valid EX EC S SS e /\ reached EX L S (lookup EX L (Engine.current e)).
Proof.
  intro Hsteps; remember (initial_state EC sch S) as start eqn:Hstart in Hsteps.
  revert Hstart; induction Hsteps as [e|n a b c Hsteps IH Hstep]; intro Hstart.
  - subst e; split; [apply total_initial_valid|].
    exists (lookup EX L (Engine.current (initial_state EC sch S))); split.
    + intro x; change (lookup EX L Map.empty x = bot L).
      unfold lookup; rewrite Map.get_empty; reflexivity.
    + apply rt_refl.
  - destruct (IH Hstart) as [Hvalid [s0 [Hbot Hpath]]]; split.
    + apply (total_join_step_valid b c Hvalid Hstep).
    + exists s0; split; [exact Hbot|].
      eapply rt_trans; [exact Hpath|apply rt_step; apply total_join_step_raise; assumption].
Qed.

End DeclaredJoiningRuns.

(** Every value returned by the joining total solver is reached from bottom by constraint runs. *)
Theorem solve_total_reached {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (S : System.t X C A) (sch : scheduler X) (HL : lattice_laws L) (SS : System.static S)
  (HT : terminates L SS sch Joining) :
  reached EX L S (proj1_sig (solve_total EX EC L HL sch Joining S SS HT)).
Proof.
  set (result := total_solver_map EX EC L HL sch Joining S SS HT).
  change (reached EX L S (lookup EX L (proj1_sig result))).
  destruct (proj2_sig result) as [Hpost [n [e [Hsteps [Hnone Hcurrent]]]]].
  rewrite <- Hcurrent; destruct HT as [Hheight].
  apply (proj2 (total_join_steps_reached EX EC L HL sch S SS (index_system EX S SS)
    (index_system_laws EX S SS) Hheight n e Hsteps)).
Qed.

(** With least-upper-bound laws and monotonicity, the joining result is the least solution. *)
Theorem solve_total_least {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (S : System.t X C A) (sch : scheduler X) (HL : lattice_laws L) (SS : System.static S)
  (HT : terminates L SS sch Joining) :
  lub_laws L -> monotone_system L S ->
  least_solution L S (proj1_sig (solve_total EX EC L HL sch Joining S SS HT)).
Proof.
  intros Hlub Hmonotone; apply (reached_least EX L S _ HL Hlub Hmonotone).
  - apply solve_total_reached.
  - exact (proj2_sig (solve_total EX EC L HL sch Joining S SS HT)).
Qed.
