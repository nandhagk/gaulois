(** * Indexed worklist iteration

    The engine records reads before raising target and side values, and queues their readers.
    For example, a self-reading constraint is queued again when its own value changes.
    Builds on: FixpointQuery, FixpointSystem, FixpointIndex and CollectionsHeap. *)

From Stdlib Require Import List Bool Arith PArith Lia Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex.
Import List.ListNotations.

(** A scheduler selects priorities and the sites that widen. *)
Record scheduler (X : Type) : Type := Scheduler {
  priority : X -> positive;
  widening_point : X -> bool
}.

Arguments Scheduler {X}.
Arguments priority {X}.
Arguments widening_point {X}.

(** Joining uses joins everywhere; widening uses the scheduler's widening sites. *)
Inductive strategy : Type :=
  | Joining
  | Widening.

(** Dependencies are prepared static readers or accumulated observed readers. *)
Inductive dependencies {X C A} (S : System.t X C A) : Type :=
  | Declared (SS : System.static S) (ix : sys_index X C)
  | Recorded.

Arguments Declared {X C A S}.
Arguments Recorded {X C A S}.

(** Declared reader indexes must agree with their static system. *)
Definition dependencies_ok {X C A} (EX : encoding X) {S : System.t X C A}
  (dep : dependencies S) : Prop :=
  match dep with
  | Declared SS ix => sys_index_laws EX S SS ix
  | Recorded => True
  end.

Module Engine.

(** Engine states contain the assignment, pending constraints and recorded readers. *)
Record t (X C A : Type) : Type := State {
  current : assignment X A;
  queue : PQueue.t C;
  recorded : Map.t X (FinSet.t C)
}.

Arguments State {X C A}.
Arguments current {X C A}.
Arguments queue {X C A}.
Arguments recorded {X C A}.

End Engine.
Import Engine.

Definition enqueue {X C A} (EC : encoding C) (sch : scheduler X) (S : System.t X C A)
  (cs : list C) (q : PQueue.t C) : PQueue.t C :=
  fold_left (fun q c => PQueue.push EC (priority sch (System.target S c)) c q) cs q.

(** Every listed constraint starts pending, with bottom values and no observed readers. *)
Definition initial_state {X C A} (EC : encoding C) (sch : scheduler X)
  (S : System.t X C A) : Engine.t X C A :=
  Engine.State Map.empty (enqueue EC sch S (System.constraints S) PQueue.empty) Map.empty.

Definition recorded_at {X C} (EX : encoding X) (r : Map.t X (FinSet.t C)) (x : X) :
  FinSet.t C :=
  match Map.get EX x r with
  | Some cs => cs
  | None => FinSet.empty
  end.

Definition record_reads {X C} (EX : encoding X) (EC : encoding C) (c : C) (rs : list X)
  (r : Map.t X (FinSet.t C)) : Map.t X (FinSet.t C) :=
  fold_left (fun r x => Map.set EX x (FinSet.add EC c (recorded_at EX r x)) r) rs r.

Definition engine_readers {X C A} (EX : encoding X) {S : System.t X C A}
  (dep : dependencies S) (r : Map.t X (FinSet.t C)) (x : X) : list C :=
  match dep with
  | Declared _ ix => readers_of EX ix x
  | Recorded => FinSet.elements (recorded_at EX r x)
  end.

Definition update_value {X A} (L : lattice A) (sch : scheduler X) (st : strategy)
  (x : X) (old a : A) : A :=
  match st with
  | Joining => join L old a
  | Widening => if widening_point sch x then widen L old a else join L old a
  end.

Definition engine_update {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S)
  (r : Map.t X (FinSet.t C)) (xa : X * A) (mq : assignment X A * PQueue.t C) :
  assignment X A * PQueue.t C :=
  let '(m, q) := mq in
  let '(x, a) := xa in
  let old := lookup EX L m x in
  if leb L a old then (m, q)
  else (Map.set EX x (update_value L sch st x old a) m,
    enqueue EC sch S (engine_readers EX dep r x) q).

Definition engine_updates {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S)
  (r : Map.t X (FinSet.t C)) (ups : list (X * A))
  (mq : assignment X A * PQueue.t C) : assignment X A * PQueue.t C :=
  fold_left (fun mq xa => engine_update EX EC L sch st S dep r xa mq) ups mq.

(** A step pops one constraint, runs it once, records its reads and raises all its outputs. *)
Definition engine_step {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S)
  (e : Engine.t X C A) : option (Engine.t X C A) :=
  match PQueue.pop EC (Engine.queue e) with
  | None => None
  | Some (_, c, q) =>
    let '(v, rs, ss) := Query.run (System.rhs S c) (lookup EX L (Engine.current e)) in
    let r := match dep with
      | Declared _ _ => Engine.recorded e
      | Recorded => record_reads EX EC c rs (Engine.recorded e)
      end in
    let '(m', q') := engine_updates EX EC L sch st S dep r
      ((System.target S c, v) :: ss) (Engine.current e, q) in
    Some (Engine.State m' q' r)
  end.

(** The relation orders a successor before its predecessor, as required by accessibility. *)
Definition engine_rel {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S)
  (e' e : Engine.t X C A) : Prop := engine_step EX EC L sch st S dep e = Some e'.

(** Finite runs count successful engine transitions. *)
Inductive engine_steps {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S) :
  nat -> Engine.t X C A -> Engine.t X C A -> Prop :=
  | steps_zero : forall e, engine_steps EX EC L sch st S dep 0 e e
  | steps_succ : forall n e e' e'', engine_steps EX EC L sch st S dep n e e' ->
      engine_rel EX EC L sch st S dep e'' e' ->
      engine_steps EX EC L sch st S dep (Datatypes.S n) e e''.

Arguments steps_zero {X C A EX EC L sch st S dep}.
Arguments steps_succ {X C A EX EC L sch st S dep}.

(** Reachable states follow forward transitions from the initialized engine. *)
Definition engine_reachable {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S)
  (e : Engine.t X C A) : Prop :=
  clos_refl_trans _ (fun from to => engine_rel EX EC L sch st S dep to from)
    (initial_state EC sch S) e.

(** A finished outcome holds the assignment; a pending one holds the resumable state. *)
Inductive outcome (X C A : Type) : Type :=
  | Done (m : assignment X A)
  | Pending (e : Engine.t X C A).

Arguments Done {X C A}.
Arguments Pending {X C A}.

(** Composition retains finished results and continues pending runs. *)
Definition then_run {X C A} (f : Engine.t X C A -> outcome X C A)
  (o : outcome X C A) : outcome X C A :=
  match o with
  | Done m => Done m
  | Pending e => f e
  end.

(** Binary recursion spends one transition probe per fuel unit, stopping early on completion. *)
Fixpoint loop {X C A} (step : Engine.t X C A -> outcome X C A) (p : positive)
  (e : Engine.t X C A) : outcome X C A :=
  match p with
  | xH => step e
  | xO p' => then_run (loop step p') (loop step p' e)
  | xI p' => then_run step (then_run (loop step p') (loop step p' e))
  end.

Definition step_outcome {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S)
  (e : Engine.t X C A) : outcome X C A :=
  match engine_step EX EC L sch st S dep e with
  | None => Done (Engine.current e)
  | Some e' => Pending e'
  end.

(** A fuel run returns an assignment exactly when a probe observes the empty queue. *)
Definition run_worklist {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S)
  (fuel : positive) : option (assignment X A) :=
  match loop (step_outcome EX EC L sch st S dep) fuel (initial_state EC sch S) with
  | Done m => Some m
  | Pending _ => None
  end.

(** * Pending constraints and recorded readers *)

Section QueueLaws.
Context {X C A : Type} (EC : encoding C) (sch : scheduler X) (S : System.t X C A).

Lemma enqueue_wf (cs : list C) (q : PQueue.t C) :
  PQueue.wf EC q -> PQueue.wf EC (enqueue EC sch S cs q).
Proof.
  revert q; induction cs as [|c cs IH]; intros q Hwf; cbn [enqueue].
  - exact Hwf.
  - apply IH, PQueue.wf_push; exact Hwf.
Qed.

Lemma enqueue_member (cs : list C) (q : PQueue.t C) (c : C) :
  PQueue.wf EC q ->
  (PQueue.priority EC c (enqueue EC sch S cs q) <> None <->
    In c cs \/ PQueue.priority EC c q <> None).
Proof.
  revert q; induction cs as [|d cs IH]; intros q Hwf; cbn [enqueue].
  - tauto.
  - change (PQueue.priority EC c
      (enqueue EC sch S cs (PQueue.push EC (priority sch (System.target S d)) d q)) <> None
      <-> In c (d :: cs) \/ PQueue.priority EC c q <> None).
    rewrite IH by (apply PQueue.wf_push; exact Hwf).
    destruct (Pos.eq_dec (encode EC c) (encode EC d)) as [Heq|Hne].
    + apply (encode_injective EC) in Heq; subst d.
      rewrite PQueue.priority_push_same by exact Hwf; cbn; intuition discriminate.
    + assert (Hcd : c <> d) by (intro Heq; subst; contradiction).
      rewrite PQueue.priority_push_other by assumption; cbn; intuition congruence.
Qed.

End QueueLaws.

Section RecordedLaws.
Context {X C : Type} (EX : encoding X) (EC : encoding C).

Definition recorded_wf (r : Map.t X (FinSet.t C)) : Prop :=
  forall x, FinSet.wf EC (recorded_at EX r x).

Lemma recorded_empty_wf : recorded_wf Map.empty.
Proof.
  intro x; unfold recorded_at; rewrite Map.get_empty; apply Map.wf_empty.
Qed.

Lemma recorded_at_set (r : Map.t X (FinSet.t C)) (x y : X) (cs : FinSet.t C) :
  recorded_at EX (Map.set EX x cs r) y =
  if Pos.eqb (encode EX y) (encode EX x) then cs else recorded_at EX r y.
Proof.
  destruct (Pos.eqb (encode EX y) (encode EX x)) eqn:Hxy.
  - apply Pos.eqb_eq in Hxy; apply (encode_injective EX) in Hxy; subst y.
    unfold recorded_at; rewrite Map.get_set_same; reflexivity.
  - assert (Hne : y <> x) by (intro Heq; subst; rewrite Pos.eqb_refl in Hxy; discriminate).
    unfold recorded_at; rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Lemma record_reads_wf (c : C) (rs : list X) (r : Map.t X (FinSet.t C)) :
  recorded_wf r -> recorded_wf (record_reads EX EC c rs r).
Proof.
  revert r; induction rs as [|x rs IH]; intros r Hwf; cbn [record_reads].
  - exact Hwf.
  - apply IH; intro y; rewrite recorded_at_set.
    destruct (Pos.eqb (encode EX y) (encode EX x)); [apply Map.wf_set|]; apply Hwf.
Qed.

Lemma record_reads_member (c d : C) (rs : list X) (r : Map.t X (FinSet.t C)) (y : X) :
  FinSet.mem EC d (recorded_at EX (record_reads EX EC c rs r) y) = true <->
  (d = c /\ In y rs) \/ FinSet.mem EC d (recorded_at EX r y) = true.
Proof.
  revert r; induction rs as [|x rs IH]; intro r; cbn [record_reads].
  - cbn; tauto.
  - change (FinSet.mem EC d (recorded_at EX
      (record_reads EX EC c rs (Map.set EX x (FinSet.add EC c (recorded_at EX r x)) r)) y)
      = true <-> (d = c /\ In y (x :: rs)) \/
      FinSet.mem EC d (recorded_at EX r y) = true).
    rewrite IH, recorded_at_set.
    destruct (Pos.eqb (encode EX y) (encode EX x)) eqn:Hxy.
    + apply Pos.eqb_eq in Hxy; apply (encode_injective EX) in Hxy; subst y.
      rewrite FinSet.mem_add; cbn; intuition congruence.
    + assert (Hne : x <> y) by (intro Heq; subst; rewrite Pos.eqb_refl in Hxy; discriminate).
      cbn; intuition congruence.
Qed.

End RecordedLaws.

(** * Raising outputs without losing pending work *)

Section UpdateLaws.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S).
Variable HL : lattice_laws L.

Lemma update_value_upper (x : X) (old a : A) :
  leb L old (update_value L sch st x old a) = true /\
  leb L a (update_value L sch st x old a) = true.
Proof.
  unfold update_value; destruct st; [|destruct (widening_point sch x)]; split;
    first [apply (join_upper_l HL) | apply (join_upper_r HL) |
      apply (widen_upper_l HL) | apply (widen_upper_r HL)].
Qed.

Lemma lookup_set_same (m : assignment X A) (x : X) (a : A) :
  lookup EX L (Map.set EX x a m) x = a.
Proof.
  unfold lookup; rewrite Map.get_set_same; reflexivity.
Qed.

Lemma lookup_set_other (m : assignment X A) (x y : X) (a : A) :
  y <> x -> lookup EX L (Map.set EX x a m) y = lookup EX L m y.
Proof.
  intro Hne; unfold lookup; rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Lemma engine_update_properties (r : Map.t X (FinSet.t C)) (x : X) (a : A)
  (m m' : assignment X A) (q q' : PQueue.t C) :
  PQueue.wf EC q -> engine_update EX EC L sch st S dep r (x, a) (m, q) = (m', q') ->
  PQueue.wf EC q' /\ fun_leb L (lookup EX L m) (lookup EX L m') /\
  leb L a (lookup EX L m' x) = true /\
  (forall c, PQueue.priority EC c q <> None -> PQueue.priority EC c q' <> None) /\
  (forall c y, In c (engine_readers EX dep r y) -> PQueue.priority EC c q' = None ->
    lookup EX L m' y = lookup EX L m y).
Proof.
  intros Hwf Hupdate; unfold engine_update in Hupdate; cbn in Hupdate.
  destruct (leb L a (lookup EX L m x)) eqn:Hbelow; inversion Hupdate; subst m' q'.
  - split; [exact Hwf|]; split; [intro y; apply (leb_refl HL)|].
    split; [exact Hbelow|]; split; [auto|reflexivity].
  - split; [apply enqueue_wf; exact Hwf|].
    split.
    + intro y; destruct (Pos.eq_dec (encode EX y) (encode EX x)) as [Heq|Hne].
      * apply (encode_injective EX) in Heq; subst y; rewrite lookup_set_same.
        apply update_value_upper.
      * rewrite lookup_set_other; [apply (leb_refl HL)|intro Heq; subst; contradiction].
    + split; [rewrite lookup_set_same; apply update_value_upper|].
      split.
      * intros c Hc; apply enqueue_member; [exact Hwf|now right].
      * intros c y Hreader Hnone.
        assert (Hyx : y <> x).
        { intro Heq; subst y.
          assert (Hpending : PQueue.priority EC c
            (enqueue EC sch S (engine_readers EX dep r x) q) <> None).
          { apply enqueue_member; [exact Hwf|now left]. }
          contradiction. }
        apply lookup_set_other; exact Hyx.
Qed.

Lemma engine_updates_properties (r : Map.t X (FinSet.t C)) (ups : list (X * A))
  (m m' : assignment X A) (q q' : PQueue.t C) :
  PQueue.wf EC q -> engine_updates EX EC L sch st S dep r ups (m, q) = (m', q') ->
  PQueue.wf EC q' /\ fun_leb L (lookup EX L m) (lookup EX L m') /\
  (forall x a, In (x, a) ups -> leb L a (lookup EX L m' x) = true) /\
  (forall c, PQueue.priority EC c q <> None -> PQueue.priority EC c q' <> None) /\
  (forall c y, In c (engine_readers EX dep r y) -> PQueue.priority EC c q' = None ->
    lookup EX L m' y = lookup EX L m y).
Proof.
  revert m q; induction ups as [|[x a] ups IH]; intros m q Hwf Hupdates.
  - cbn [engine_updates] in Hupdates; inversion Hupdates; subst m' q'.
    split; [exact Hwf|]; split; [intro y; apply (leb_refl HL)|].
    split; [intros y b Hin; contradiction|]; split; [auto|reflexivity].
  - change (engine_updates EX EC L sch st S dep r ups
      (engine_update EX EC L sch st S dep r (x, a) (m, q)) = (m', q')) in Hupdates.
    destruct (engine_update EX EC L sch st S dep r (x, a) (m, q)) as [m1 q1] eqn:Hone.
    destruct (engine_update_properties r x a m m1 q q1 Hwf Hone)
      as [Hwf1 [Hup1 [Hbound [Hpending1 Hsame1]]]].
    destruct (IH m1 q1 Hwf1 Hupdates) as [Hwf' [Hup [Hbounds [Hpending Hsame]]]].
    split; [exact Hwf'|]; split.
    + intro y; eapply (leb_trans HL); [apply Hup1|apply Hup].
    + split.
      * intros y b [Heq|Hin].
        -- inversion Heq; subst y b; eapply (leb_trans HL); [exact Hbound|apply Hup].
        -- apply Hbounds; exact Hin.
      * split.
        -- intros c Hc; apply Hpending, Hpending1; exact Hc.
        -- intros c y Hreader Hnone; rewrite (Hsame c y Hreader Hnone).
           apply (Hsame1 c y Hreader); destruct (PQueue.priority EC c q1) eqn:Hget;
             [exfalso; apply (Hpending c); congruence|reflexivity].
Qed.

End UpdateLaws.

(** * Stability of constraints outside the queue *)

Section EngineInvariant.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S).
Variable HL : lattice_laws L.
Variable Hdep : dependencies_ok EX dep.

Definition constraint_satisfied (c : C) (s : X -> A) : Prop :=
  leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true /\
  forall x a, In (x, a) (Query.sides (System.rhs S c) s) -> leb L a (s x) = true.

(* An unqueued constraint has been evaluated at the current read values, and all those reads
   are indexed. Future raises either preserve those values or put the constraint back in queue. *)
Definition engine_invariant (e : Engine.t X C A) : Prop :=
  PQueue.wf EC (Engine.queue e) /\ recorded_wf EX EC (Engine.recorded e) /\
  forall c, In c (System.constraints S) -> PQueue.priority EC c (Engine.queue e) = None ->
    constraint_satisfied c (lookup EX L (Engine.current e)) /\
    forall x, In x (Query.reads (System.rhs S c) (lookup EX L (Engine.current e))) ->
      In c (engine_readers EX dep (Engine.recorded e) x).

Lemma initial_state_invariant : engine_invariant (initial_state EC sch S).
Proof.
  split; [apply enqueue_wf, PQueue.wf_empty|].
  split; [apply recorded_empty_wf|].
  intros c Hc Hnone; cbn [initial_state Engine.queue] in Hnone.
  exfalso; apply (proj2 (enqueue_member EC sch S (System.constraints S)
    PQueue.empty c (PQueue.wf_empty EC))); [now left|exact Hnone].
Qed.

Definition learn_reads (c : C) (rs : list X) (r : Map.t X (FinSet.t C)) :
  Map.t X (FinSet.t C) :=
  match dep with
  | Declared _ _ => r
  | Recorded => record_reads EX EC c rs r
  end.

Lemma learn_reads_wf (c : C) (rs : list X) (r : Map.t X (FinSet.t C)) :
  recorded_wf EX EC r -> recorded_wf EX EC (learn_reads c rs r).
Proof.
  unfold learn_reads; destruct dep; [auto|apply record_reads_wf].
Qed.

Lemma learn_reads_preserved (c d : C) (rs : list X) (r : Map.t X (FinSet.t C)) (x : X) :
  recorded_wf EX EC r -> In d (engine_readers EX dep r x) ->
  In d (engine_readers EX dep (learn_reads c rs r) x).
Proof.
  intros Hwf Hin; unfold learn_reads, engine_readers in *; destruct dep; [exact Hin|].
  apply (FinSet.elements_spec EC); [apply record_reads_wf; exact Hwf|].
  apply record_reads_member; right; apply (FinSet.elements_spec EC); [apply Hwf|exact Hin].
Qed.

Lemma learn_reads_current (c : C) (s : X -> A) (r : Map.t X (FinSet.t C)) (x : X) :
  recorded_wf EX EC r -> In c (System.constraints S) ->
  In x (Query.reads (System.rhs S c) s) ->
  In c (engine_readers EX dep (learn_reads c (Query.reads (System.rhs S c) s) r) x).
Proof.
  intros Hwf Hc Hread; unfold learn_reads, engine_readers; destruct dep as [SS ix|].
  - apply (readers_agree Hdep); split; [exact Hc|].
    apply (System.reads_within SS c s); exact Hread.
  - apply (FinSet.elements_spec EC); [apply record_reads_wf; exact Hwf|].
    apply record_reads_member; left; auto.
Qed.

Lemma constraint_satisfied_transport (c : C) (s t : X -> A) :
  fun_leb L s t -> (forall x, In x (Query.reads (System.rhs S c) s) -> t x = s x) ->
  constraint_satisfied c s -> constraint_satisfied c t /\
  Query.reads (System.rhs S c) t = Query.reads (System.rhs S c) s.
Proof.
  intros Hup Hagree [Hv Hs].
  destruct (query_determined (System.rhs S c) s t) as [Hvalue [Hreads Hsides]].
  - intros x Hx; symmetry; apply Hagree; exact Hx.
  - split; [split|symmetry; exact Hreads].
    + rewrite <- Hvalue; eapply (leb_trans HL); [exact Hv|apply Hup].
    + intros x a Ha; rewrite <- Hsides in Ha.
      eapply (leb_trans HL); [apply Hs; exact Ha|apply Hup].
Qed.

Lemma engine_step_invariant (e e' : Engine.t X C A) :
  engine_invariant e -> engine_step EX EC L sch st S dep e = Some e' ->
  engine_invariant e'.
Proof.
  intros [Hwf [Hrwf Hstable]] Hstep; unfold engine_step in Hstep.
  destruct (PQueue.pop EC (Engine.queue e)) as [[[p c] q]|] eqn:Hpop;
    [|discriminate].
  rewrite run_spec in Hstep.
  change ((let '(m', q') := engine_updates EX EC L sch st S dep
    (learn_reads c (Query.reads (System.rhs S c) (lookup EX L (Engine.current e)))
      (Engine.recorded e))
    ((System.target S c, Query.eval (System.rhs S c) (lookup EX L (Engine.current e))) ::
      Query.sides (System.rhs S c) (lookup EX L (Engine.current e)))
    (Engine.current e, q) in Some (Engine.State m' q'
      (learn_reads c (Query.reads (System.rhs S c) (lookup EX L (Engine.current e)))
        (Engine.recorded e)))) = Some e') in Hstep.
  set (s := lookup EX L (Engine.current e)) in *.
  set (r := learn_reads c (Query.reads (System.rhs S c) s) (Engine.recorded e)) in *.
  destruct (engine_updates EX EC L sch st S dep r
    ((System.target S c, Query.eval (System.rhs S c) s) :: Query.sides (System.rhs S c) s)
    (Engine.current e, q)) as [m' q'] eqn:Hupdates.
  inversion Hstep; subst e'; clear Hstep.
  pose proof (PQueue.wf_pop EC _ _ _ _ Hwf Hpop) as Hqwf.
  destruct (engine_updates_properties EX EC L sch st S dep HL r _ _ _ _ _ Hqwf Hupdates)
    as [Hwf' [Hup [Hbounds [Hpending Hsame]]]].
  assert (Hrwf' : recorded_wf EX EC r) by (apply learn_reads_wf; exact Hrwf).
  split; [exact Hwf'|]; split; [exact Hrwf'|].
  intros d Hd Hnone; cbn in Hnone |- *.
  assert (Hqnone : PQueue.priority EC d q = None).
  { destruct (PQueue.priority EC d q) eqn:Hget; [|reflexivity].
    exfalso; apply (Hpending d); congruence. }
  destruct (Pos.eq_dec (encode EC d) (encode EC c)) as [Heq|Hne].
  - apply (encode_injective EC) in Heq; subst d.
    assert (Hreader : forall x, In x (Query.reads (System.rhs S c) s) ->
      In c (engine_readers EX dep r x)).
    { intros x Hx; apply learn_reads_current; assumption. }
    destruct (query_determined (System.rhs S c) s (lookup EX L m'))
      as [Hv [Hr Hs]].
    + intros x Hx; symmetry; apply (Hsame c x); [apply Hreader; exact Hx|exact Hnone].
    + split; [split|].
      * rewrite <- Hv; apply Hbounds; now left.
      * intros x a Ha; rewrite <- Hs in Ha; apply Hbounds; now right.
      * intros x Hx; rewrite <- Hr in Hx; apply Hreader; exact Hx.
  - assert (Hdc : d <> c) by (intro Heq; subst; contradiction).
    destruct (PQueue.pop_rest EC _ _ _ _ Hwf Hpop) as [_ [Hrest _]].
    rewrite Hrest in Hqnone by exact Hdc.
    destruct (Hstable d Hd Hqnone) as [Hsat Hreader].
    assert (Hreader' : forall x, In x (Query.reads (System.rhs S d) s) ->
      In d (engine_readers EX dep r x)).
    { intros x Hx; apply learn_reads_preserved; [exact Hrwf|apply Hreader; exact Hx]. }
    destruct (constraint_satisfied_transport d s (lookup EX L m') Hup)
      as [Hsat' Hr].
    + intros x Hx; apply (Hsame d x); [apply Hreader'; exact Hx|exact Hnone].
    + exact Hsat.
    + split; [exact Hsat'|]; intros x Hx; rewrite Hr in Hx; apply Hreader'; exact Hx.
Qed.

Lemma engine_reachable_invariant (e : Engine.t X C A) :
  engine_reachable EX EC L sch st S dep e -> engine_invariant e.
Proof.
  intro Hreach.
  assert (Hpreserve : forall a b,
    clos_refl_trans _ (fun from to => engine_rel EX EC L sch st S dep to from) a b ->
    engine_invariant a -> engine_invariant b).
  { intros a b Hpath; induction Hpath as [a b Hstep|a|a b c Hab IHab Hbc IHbc];
      intro Hinv.
    - eapply engine_step_invariant; [exact Hinv|exact Hstep].
    - exact Hinv.
    - apply IHbc, IHab; exact Hinv. }
  apply (Hpreserve _ _ Hreach), initial_state_invariant.
Qed.

End EngineInvariant.

Section EngineSoundness.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (S : System.t X C A).
Variables (sch : scheduler X) (st : strategy) (dep : dependencies S).

(** A finished reachable state satisfies all returns and side contributions. *)
Theorem engine_finished_sound (e : Engine.t X C A) :
  lattice_laws L -> dependencies_ok EX dep ->
  engine_reachable EX EC L sch st S dep e ->
  engine_step EX EC L sch st S dep e = None ->
  post_solution L S (lookup EX L (Engine.current e)).
Proof.
  intros HL Hdep Hreach Hfinished.
  destruct (engine_reachable_invariant EX EC L sch st S dep HL Hdep e Hreach)
    as [Hwf [_ Hstable]].
  assert (Hempty : PQueue.is_empty (Engine.queue e) = true).
  { apply (PQueue.pop_none EC); [exact Hwf|].
    unfold engine_step in Hfinished.
    destruct (PQueue.pop EC (Engine.queue e)) as [[[p c] q]|] eqn:Hpop;
      [|reflexivity].
    destruct (Query.run (System.rhs S c) (lookup EX L (Engine.current e))) as [[v rs] ss].
    destruct (engine_updates EX EC L sch st S dep
      (match dep with
       | Declared _ _ => Engine.recorded e
       | Recorded => record_reads EX EC c rs (Engine.recorded e)
       end) ((System.target S c, v) :: ss) (Engine.current e, q)); discriminate. }
  intros c Hc; apply (Hstable c Hc).
  apply (proj1 (PQueue.is_empty_spec EC _ Hwf) Hempty).
Qed.

End EngineSoundness.

(** * Binary loop semantics *)

Section LoopSemantics.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S).
Local Abbreviation step := (engine_step EX EC L sch st S dep).
Local Abbreviation next := (step_outcome EX EC L sch st S dep).
Local Abbreviation steps := (engine_steps EX EC L sch st S dep).

Lemma engine_steps_append (n k : nat) (e e' e'' : Engine.t X C A) :
  steps n e e' -> steps k e' e'' -> steps (n + k) e e''.
Proof.
  intros Hfirst Hsecond; induction Hsecond as [e'|k a b c Hab IH Hbc].
  - rewrite Nat.add_0_r; exact Hfirst.
  - rewrite Nat.add_succ_r; eapply steps_succ; [apply IH; exact Hfirst|exact Hbc].
Qed.

Lemma engine_steps_cons (n : nat) (e e' e'' : Engine.t X C A) :
  step e = Some e' -> steps n e' e'' -> steps (Datatypes.S n) e e''.
Proof.
  intros Hstep Hsteps.
  replace (Datatypes.S n) with (1 + n)%nat by lia.
  eapply engine_steps_append; [|exact Hsteps].
  econstructor; [constructor|exact Hstep].
Qed.

Lemma engine_steps_reachable (n : nat) (e : Engine.t X C A) :
  steps n (initial_state EC sch S) e -> engine_reachable EX EC L sch st S dep e.
Proof.
  intro Hsteps.
  assert (Hpath : forall n a b, steps n a b ->
    clos_refl_trans _ (fun from to => engine_rel EX EC L sch st S dep to from) a b).
  { intros k a b Hrun; induction Hrun as [a|k a b c Hrun IH Hstep].
    - apply rt_refl.
    - eapply rt_trans; [exact IH|apply rt_step; exact Hstep]. }
  exact (Hpath _ _ _ Hsteps).
Qed.

(* This proof-only relation counts probes, including the final empty-queue probe. It is not
   an executable unary loop: the exported computation recurses only over binary positives. *)
Inductive budget_run : nat -> Engine.t X C A -> outcome X C A -> Prop :=
  | budget_zero : forall e, budget_run 0 e (Pending e)
  | budget_finished : forall n e, step e = None ->
      budget_run (Datatypes.S n) e (Done (Engine.current e))
  | budget_next : forall n e e' o, step e = Some e' -> budget_run n e' o ->
      budget_run (Datatypes.S n) e o.

Lemma budget_run_unique (n : nat) (e : Engine.t X C A) (o o' : outcome X C A) :
  budget_run n e o -> budget_run n e o' -> o = o'.
Proof.
  intros Hrun; revert o'; induction Hrun as [e|n e Hnone|n e e' o Hstep Hrun IH];
    intros o' Hother; inversion Hother; subst; try reflexivity; try congruence.
  apply IH; match goal with
  | Hotherstep : step e = Some ?e2 |- _ =>
    assert (e' = e2) by congruence; subst e2; assumption
  end.
Qed.

Lemma budget_run_then (n k : nat) (e : Engine.t X C A) (o : outcome X C A)
  (f : Engine.t X C A -> outcome X C A) :
  budget_run n e o -> (forall e', budget_run k e' (f e')) ->
  budget_run (n + k) e (then_run f o).
Proof.
  intros Hrun Hf; induction Hrun as [e|n e Hnone|n e e' o Hstep Hrun IH]; cbn [then_run].
  - apply Hf.
  - constructor; exact Hnone.
  - econstructor; [exact Hstep|exact IH].
Qed.

Lemma budget_run_compose (n k : nat) (e : Engine.t X C A) (o o' : outcome X C A) :
  budget_run n e o ->
  (match o with Done m => o' = Done m | Pending e' => budget_run k e' o' end) ->
  budget_run (n + k) e o'.
Proof.
  intros Hrun; induction Hrun as [e|n e Hnone|n e e' o Hstep Hrun IH]; intro Hsecond.
  - exact Hsecond.
  - subst o'; constructor; exact Hnone.
  - econstructor; [exact Hstep|apply IH; exact Hsecond].
Qed.

Lemma budget_run_one (e : Engine.t X C A) : budget_run 1 e (next e).
Proof.
  unfold step_outcome; destruct (step e) as [e'|] eqn:Hstep.
  - econstructor; [exact Hstep|constructor].
  - constructor; exact Hstep.
Qed.

Lemma loop_budget (p : positive) (e : Engine.t X C A) :
  budget_run (Pos.to_nat p) e (loop next p e).
Proof.
  revert e; induction p as [p IH|p IH|]; intro e; cbn [loop].
  - rewrite Pos2Nat.inj_xI.
    replace (Datatypes.S (2 * Pos.to_nat p)) with
      ((Pos.to_nat p + Pos.to_nat p) + 1)%nat by lia.
    eapply budget_run_then; [|apply budget_run_one].
    apply budget_run_then; apply IH.
  - rewrite Pos2Nat.inj_xO.
    replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by lia.
    apply budget_run_then; apply IH.
  - apply budget_run_one.
Qed.

Lemma budget_run_steps (n : nat) (e : Engine.t X C A) (m : assignment X A) :
  budget_run n e (Done m) ->
  exists k e', (k < n)%nat /\ steps k e e' /\ step e' = None /\ Engine.current e' = m.
Proof.
  intro Hrun; remember (Done m) as o eqn:Ho; revert m Ho.
  induction Hrun as [e|n e Hnone|n e e' o Hstep Hrun IH]; intros m Ho.
  - discriminate.
  - inversion Ho; subst m; exists 0, e; split; [lia|].
    split; [constructor|auto].
  - destruct (IH m Ho) as [k [e'' [Hlt [Hsteps [Hnone Hcurrent]]]]].
    exists (Datatypes.S k), e''; split; [lia|].
    split; [apply (engine_steps_cons k e e' e'' Hstep Hsteps)|auto].
Qed.

Lemma engine_steps_budget (n : nat) (e e' : Engine.t X C A) :
  steps n e e' -> budget_run n e (Pending e').
Proof.
  intro Hsteps; induction Hsteps as [e|n e e' e'' Hsteps IH Hstep].
  - constructor.
  - replace (Datatypes.S n) with (n + 1)%nat by lia.
    pose proof (budget_run_then n 1 e (Pending e') next IH budget_run_one) as Hrun.
    cbn [then_run] in Hrun; unfold step_outcome in Hrun; rewrite Hstep in Hrun; exact Hrun.
Qed.

Lemma finished_steps_budget (n k : nat) (e e' : Engine.t X C A) :
  (k < n)%nat -> steps k e e' -> step e' = None ->
  budget_run n e (Done (Engine.current e')).
Proof.
  intros Hlt Hsteps Hnone.
  replace n with (k + Datatypes.S (n - k - 1))%nat by lia.
  eapply budget_run_compose.
  - apply engine_steps_budget; exact Hsteps.
  - cbn; constructor; exact Hnone.
Qed.

End LoopSemantics.

Section WorklistLaws.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (S : System.t X C A).
Variables (sch : scheduler X) (st : strategy) (dep : dependencies S).
Local Abbreviation step := (engine_step EX EC L sch st S dep).
Local Abbreviation start := (initial_state EC sch S).

(** Fuel counts successful transitions plus the final probe that discovers completion. *)
Theorem run_worklist_spec (m : assignment X A) (fuel : positive) :
  run_worklist EX EC L sch st S dep fuel = Some m <->
  exists n e', (n < Pos.to_nat fuel)%nat /\
    engine_steps EX EC L sch st S dep n start e' /\
    step e' = None /\ Engine.current e' = m.
Proof.
  unfold run_worklist.
  pose proof (loop_budget EX EC L sch st S dep fuel start) as Hbudget.
  split.
  - destruct (loop (step_outcome EX EC L sch st S dep) fuel start) as [m'|e'] eqn:Hloop;
      intro Hresult; [|discriminate].
    inversion Hresult; subst m'; apply (budget_run_steps EX EC L sch st S dep); exact Hbudget.
  - intros [n [e' [Hlt [Hsteps [Hnone Hcurrent]]]]].
    pose proof (finished_steps_budget EX EC L sch st S dep _ _ _ _ Hlt Hsteps Hnone)
      as Hdone.
    pose proof (budget_run_unique EX EC L sch st S dep _ _ _ _ Hbudget Hdone) as Heq.
    rewrite Heq, Hcurrent; reflexivity.
Qed.

(** Every completed fuel run returns a post-solution. *)
Theorem run_worklist_sound (m : assignment X A) (fuel : positive) :
  lattice_laws L -> dependencies_ok EX dep ->
  run_worklist EX EC L sch st S dep fuel = Some m -> post_solution L S (lookup EX L m).
Proof.
  intros HL Hdep Hrun; apply run_worklist_spec in Hrun.
  destruct Hrun as [n [e [Hlt [Hsteps [Hnone Hcurrent]]]]].
  rewrite <- Hcurrent; eapply engine_finished_sound; [exact HL|exact Hdep| |exact Hnone].
  apply (engine_steps_reachable EX EC L sch st S dep n e); exact Hsteps.
Qed.

Lemma accessible_engine_finishes (e : Engine.t X C A) :
  Acc (engine_rel EX EC L sch st S dep) e ->
  exists n e', engine_steps EX EC L sch st S dep n e e' /\ step e' = None.
Proof.
  intro Hacc; induction Hacc as [e Hacc IH].
  destruct (step e) as [e'|] eqn:Hstep.
  - destruct (IH e' Hstep) as [n [e'' [Hsteps Hnone]]].
    exists (Datatypes.S n), e''; split; [|exact Hnone].
    apply (engine_steps_cons EX EC L sch st S dep n e e' e''); assumption.
  - exists 0, e; split; [constructor|exact Hstep].
Qed.

(** Accessibility supplies a threshold above which every fuel run completes. *)
Theorem run_worklist_acc : Acc (engine_rel EX EC L sch st S dep) start ->
  exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S dep fuel = Some m'.
Proof.
  intro Hacc; destruct (accessible_engine_finishes start Hacc) as [n [e [Hsteps Hnone]]].
  exists (Pos.of_succ_nat n); intros fuel Hfuel; exists (Engine.current e).
  apply run_worklist_spec; exists n, e; split.
  - apply Pos2Nat.inj_le in Hfuel; rewrite SuccNat2Pos.id_succ in Hfuel; lia.
  - split; [exact Hsteps|auto].
Qed.

End WorklistLaws.

(** The fuel solver returns a completed assignment or everywhere top on exhaustion. *)
Definition solve_fuel {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (T : top L) (sch : scheduler X) (st : strategy)
  (S : System.t X C A) (fuel : positive) : {s : X -> A | post_solution L S s}.
Proof.
  destruct (run_worklist EX EC L sch st S Recorded fuel) as [m|] eqn:Hrun.
  - refine (exist _ (lookup EX L m) _).
    abstract (exact (run_worklist_sound EX EC L S sch st Recorded m fuel HL I Hrun)).
  - exact (exist _ (fun _ => top_value T) (top_post_solution L S T)).
Defined.
