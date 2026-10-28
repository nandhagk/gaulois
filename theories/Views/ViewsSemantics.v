(** * Traced semantics and matching behaviours

    Semantics describe finite runs, endings and divergence over observable event lists.
    For example, a silent administrative step can precede a matching stuck endpoint.
    Builds on: Stdlib lists and well-founded natural-number induction. *)

From Stdlib Require Import List Arith Lia Wellfounded.
Import List.ListNotations.

(** A semantics supplies initial states and event-labelled transitions. *)
Record semantics (S O : Type) : Type := Semantics {
  initial : S -> Prop;
  step : S -> list O -> S -> Prop
}.

Arguments Semantics {S O}.
Arguments initial {S O}.
Arguments step {S O}.

(** Endings distinguish normal termination, traps and resource stops. *)
Record endings (S : Type) : Type := Endings {
  final : S -> Prop;
  trapped : S -> Prop;
  stopped : S -> Prop
}.

Arguments Endings {S}.
Arguments final {S}.
Arguments trapped {S}.
Arguments stopped {S}.

(** A running state has at least one transition. *)
Definition running {S O} (m : semantics S O) (s : S) : Prop :=
  exists l s', step m s l s'.

(** Stuck states have neither a transition nor a declared ending. *)
Definition stuck {S O} (m : semantics S O) (en : endings S) (s : S) : Prop :=
  ~ running m s /\ ~ final en s /\ ~ trapped en s /\ ~ stopped en s.

(** Declared endings halt and have disjoint classifications. *)
Record endings_wf {S O} (m : semantics S O) (en : endings S) : Prop := {
  final_halts : forall s, final en s -> ~ running m s;
  trapped_halts : forall s, trapped en s -> ~ running m s;
  stopped_halts : forall s, stopped en s -> ~ running m s;
  final_not_trapped : forall s, final en s -> ~ trapped en s;
  final_not_stopped : forall s, final en s -> ~ stopped en s;
  trapped_not_stopped : forall s, trapped en s -> ~ stopped en s
}.

(** Finite runs concatenate the event lists of their transitions. *)
Inductive exec {S O} (m : semantics S O) : S -> list O -> S -> Prop :=
  | exec_refl : forall s, exec m s nil s
  | exec_step : forall s l s' tr s'',
      step m s l s' -> exec m s' tr s'' -> exec m s (l ++ tr) s''.

Arguments exec_refl {S O m}.
Arguments exec_step {S O m}.

(** Restricted runs require the predicate at every state, including the endpoint. *)
Inductive exec_in {S O} (m : semantics S O) (P : S -> Prop) : S -> list O -> S -> Prop :=
  | exec_in_refl : forall s, P s -> exec_in m P s nil s
  | exec_in_step : forall s l s' tr t,
      P s -> step m s l s' -> exec_in m P s' tr t -> exec_in m P s (l ++ tr) t.

Arguments exec_in_refl {S O m P}.
Arguments exec_in_step {S O m P}.

(** Divergence is an infinite sequence of transitions without an event restriction. *)
CoInductive diverges {S O} (m : semantics S O) : S -> Prop :=
  | diverges_step : forall s l s', step m s l s' -> diverges m s' -> diverges m s.

Arguments diverges_step {S O m}.

(** A reachable state is the endpoint of a finite run from an initial state. *)
Definition reachable_state {S O} (m : semantics S O) (s : S) : Prop :=
  exists s0 tr, initial m s0 /\ exec m s0 tr s.

(** Ending tags retain the distinction between halting and being stuck. *)
Inductive ending : Type :=
  | EndFinal
  | EndTrap
  | EndStop
  | EndStuck.

(** Each tag selects its corresponding semantic endpoint predicate. *)
Definition ends_as {S O} (m : semantics S O) (en : endings S) (k : ending) (s : S) : Prop :=
  match k with
  | EndFinal => final en s
  | EndTrap => trapped en s
  | EndStop => stopped en s
  | EndStuck => stuck m en s
  end.

(** A diverging prefix is a finite trace leading to a diverging state. *)
Definition diverges_after {S O} (m : semantics S O) (s : S) (tr : list O) : Prop :=
  exists t, exec m s tr t /\ diverges m t.

(** Behaviour equality preserves finishes, finite traces and diverging prefixes. *)
Record same_behaviour {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1) (s1 : S1)
    (m2 : semantics S2 O) (e2 : endings S2) (s2 : S2) : Prop := {
  same_finish : forall k tr,
    (exists t, exec m1 s1 tr t /\ ends_as m1 e1 k t) <->
    (exists t, exec m2 s2 tr t /\ ends_as m2 e2 k t);
  same_prefix : forall tr, (exists t, exec m1 s1 tr t) <-> (exists t, exec m2 s2 tr t);
  same_diverging_prefix : forall tr, diverges_after m1 s1 tr <-> diverges_after m2 s2 tr
}.

(** A bisimulation matches endings and individual transitions in both directions. *)
Record bisimulation {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop) : Prop := {
  bisim_ends : forall s t k, R s t -> (ends_as m1 e1 k s <-> ends_as m2 e2 k t);
  bisim_forth : forall s t l s', R s t -> step m1 s l s' ->
    exists t', step m2 t l t' /\ R s' t';
  bisim_back : forall s t l t', R s t -> step m2 t l t' ->
    exists s', step m1 s l s' /\ R s' t'
}.

(** Stuttering matches all endings silently and bounds unmatched silent steps by measures. *)
Record stuttering {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1) (m2 : semantics S2 O)
    (e2 : endings S2) (R : S1 -> S2 -> Prop) (mu1 mu2 : S1 -> S2 -> nat) : Prop := {
  st_ends_forth : forall s t k, R s t -> ends_as m1 e1 k s ->
    exists t1, exec m2 t nil t1 /\ ends_as m2 e2 k t1;
  st_ends_back : forall s t k, R s t -> ends_as m2 e2 k t ->
    exists s1, exec m1 s nil s1 /\ ends_as m1 e1 k s1;
  st_forth : forall s t l s', R s t -> step m1 s l s' ->
    (l = nil /\ R s' t /\ mu1 s' t < mu1 s t) \/
    (exists t1 t', exec m2 t nil t1 /\ step m2 t1 l t' /\ R s' t');
  st_back : forall s t l t', R s t -> step m2 t l t' ->
    (l = nil /\ R s t' /\ mu2 s t' < mu2 s t) \/
    (exists s1 s', exec m1 s nil s1 /\ step m1 s1 l s' /\ R s' t')
}.

Arguments st_ends_forth {S1 S2 O m1 e1 m2 e2 R mu1 mu2}.
Arguments st_ends_back {S1 S2 O m1 e1 m2 e2 R mu1 mu2}.
Arguments st_forth {S1 S2 O m1 e1 m2 e2 R mu1 mu2}.
Arguments st_back {S1 S2 O m1 e1 m2 e2 R mu1 mu2}.

(** * Finite runs *)

Lemma exec_app {S O} (m : semantics S O) s u t tr1 tr2 :
  exec m s tr1 u -> exec m u tr2 t -> exec m s (tr1 ++ tr2) t.
Proof.
  intros Hrun; induction Hrun as [s|s l s' tr u Hstep Hrun IH]; intro Htail.
  - exact Htail.
  - rewrite <- app_assoc; econstructor; [exact Hstep|apply IH; exact Htail].
Qed.

Lemma exec_one {S O} (m : semantics S O) s l t :
  step m s l t -> exec m s l t.
Proof.
  intro Hstep; rewrite <- (app_nil_r l); econstructor; [exact Hstep|constructor].
Qed.

Lemma reachable_state_exec {S O} (m : semantics S O) s tr t :
  reachable_state m s -> exec m s tr t -> reachable_state m t.
Proof.
  intros [s0 [tr0 [Hinitial Hprefix]]] Hrun.
  exists s0, (tr0 ++ tr); split; [exact Hinitial|eapply exec_app; eassumption].
Qed.

Lemma reachable_state_step {S O} (m : semantics S O) s l t :
  reachable_state m s -> step m s l t -> reachable_state m t.
Proof.
  intros Hreachable Hstep; eapply reachable_state_exec; [exact Hreachable|].
  apply exec_one; exact Hstep.
Qed.

(** Forgetting the state predicate of a restricted run gives a run. *)
Theorem exec_in_exec {S O} (m : semantics S O) (P : S -> Prop) (s t : S) (tr : list O) :
  exec_in m P s tr t -> exec m s tr t.
Proof.
  intro Hrun; induction Hrun as [s HP|s l s' tr t HP Hstep Hrun IH].
  - constructor.
  - econstructor; eassumption.
Qed.

(** Restricted runs concatenate while retaining their predicate at every state. *)
Theorem exec_in_app {S O} (m : semantics S O) (P : S -> Prop) (s u t : S) (tr1 tr2 : list O) :
  exec_in m P s tr1 u -> exec_in m P u tr2 t -> exec_in m P s (tr1 ++ tr2) t.
Proof.
  intros Hrun; induction Hrun as [s HP|s l s' tr u HP Hstep Hrun IH]; intro Htail.
  - exact Htail.
  - rewrite <- app_assoc; econstructor; [exact HP|exact Hstep|apply IH; exact Htail].
Qed.

Lemma stuttering_swap {S1 S2 O} (m1 : semantics S1 O) e1 (m2 : semantics S2 O) e2 R mu1 mu2 :
  stuttering m1 e1 m2 e2 R mu1 mu2 ->
  stuttering m2 e2 m1 e1 (fun t s => R s t) (fun t s => mu2 s t) (fun t s => mu1 s t).
Proof.
  intro Hst; constructor.
  - intros t s k Hrel Hend; exact (st_ends_back Hst s t k Hrel Hend).
  - intros t s k Hrel Hend; exact (st_ends_forth Hst s t k Hrel Hend).
  - intros t s l t' Hrel Hstep; exact (st_back Hst s t l t' Hrel Hstep).
  - intros t s l s' Hrel Hstep; exact (st_forth Hst s t l s' Hrel Hstep).
Qed.

Lemma stuttering_exec {S1 S2 O} (m1 : semantics S1 O) e1 (m2 : semantics S2 O) e2 R mu1 mu2 :
  stuttering m1 e1 m2 e2 R mu1 mu2 ->
  forall s tr s', exec m1 s tr s' -> forall t, R s t ->
    exists t', exec m2 t tr t' /\ R s' t'.
Proof.
  intros Hst s tr s' Hrun.
  induction Hrun as [s|s l s' tr s'' Hstep Hrun IH]; intros t Hrel.
  - exists t; split; [constructor|exact Hrel].
  - destruct (st_forth Hst s t l s' Hrel Hstep) as
      [[-> [Hrel' Hdecrease]]|[t1 [t' [Hsilent [Hmatch Hrel']]]]].
    + apply IH; exact Hrel'.
    + destruct (IH t' Hrel') as [t'' [Htail Hrel'']].
      exists t''; split; [|exact Hrel''].
      eapply (exec_app m2 t t1 t'' [] (l ++ tr)); [exact Hsilent|].
      econstructor; eassumption.
Qed.

(** * Productive divergence matching *)

Lemma stuttering_diverges_progress {S1 S2 O} (m1 : semantics S1 O) e1
    (m2 : semantics S2 O) e2 R mu1 mu2 :
  stuttering m1 e1 m2 e2 R mu1 mu2 ->
  forall s t, R s t -> diverges m1 s ->
  exists t1 l t' s', exec m2 t nil t1 /\ step m2 t1 l t' /\ R s' t' /\ diverges m1 s'.
Proof.
  intros Hst s t; remember (mu1 s t) as n eqn:Hmeasure.
  revert s Hmeasure.
  induction n as [n IH] using lt_wf_ind; intros s Hmeasure Hrel Hdiv.
  destruct Hdiv as [s l s' Hstep Hdiv].
  destruct (st_forth Hst s t l s' Hrel Hstep) as
    [[Hsilent [Hrel' Hdecrease]]|[t1 [t' [Hprefix [Hmatch Hrel']]]]].
  - eapply (IH (mu1 s' t)); [lia|reflexivity|exact Hrel'|exact Hdiv].
  - exists t1, l, t', s'; repeat split; assumption.
Qed.

Lemma diverges_from_progress {S O} (m : semantics S O) (P : S -> Prop) :
  (forall s, P s -> exists l t, step m s l t /\ P t) ->
  forall s, P s -> diverges m s.
Proof.
  intro Hprogress; cofix CIH; intros s HP.
  destruct (Hprogress s HP) as [l [t [Hstep HP']]].
  econstructor; [exact Hstep|apply CIH; exact HP'].
Qed.

Lemma stuttering_diverges {S1 S2 O} (m1 : semantics S1 O) e1
    (m2 : semantics S2 O) e2 R mu1 mu2 :
  stuttering m1 e1 m2 e2 R mu1 mu2 ->
  forall s t, R s t -> diverges m1 s -> diverges m2 t.
Proof.
  intros Hst s t Hrel Hdiv.
  apply (diverges_from_progress m2 (fun t =>
    exists s tr u, exec m2 t tr u /\ R s u /\ diverges m1 s)).
  - intros v [s1 [tr [u [Hrun [Hrel1 Hdiv1]]]]].
    destruct Hrun as [v|v l v' tr u Hstep Hrun].
    + destruct (stuttering_diverges_progress m1 e1 m2 e2 R mu1 mu2 Hst
        s1 v Hrel1 Hdiv1) as [v1 [l [v2 [s2 [Hprefix [Hstep [Hrel2 Hdiv2]]]]]]].
      destruct Hprefix as [v|v l0 v' tr v1 Hfirst Hprefix].
      * exists l, v2; split; [exact Hstep|].
        exists s2, [], v2; split; [constructor|split; assumption].
      * exists l0, v'; split; [exact Hfirst|].
        exists s2, (tr ++ l), v2; split; [|split; assumption].
        eapply exec_app; [exact Hprefix|apply exec_one; exact Hstep].
    + exists l, v'; split; [exact Hstep|].
      exists s1, tr, u; split; [exact Hrun|split; assumption].
  - exists s, [], t; split; [constructor|split; assumption].
Qed.

Lemma stuttering_finish {S1 S2 O} (m1 : semantics S1 O) e1
    (m2 : semantics S2 O) e2 R mu1 mu2 :
  stuttering m1 e1 m2 e2 R mu1 mu2 -> forall s t, R s t -> forall k tr,
  (exists s', exec m1 s tr s' /\ ends_as m1 e1 k s') ->
  exists t', exec m2 t tr t' /\ ends_as m2 e2 k t'.
Proof.
  intros Hst s t Hrel k tr [s' [Hrun Hend]].
  destruct (stuttering_exec m1 e1 m2 e2 R mu1 mu2 Hst s tr s' Hrun t Hrel)
    as [t' [Hmatch Hrel']].
  destruct (st_ends_forth Hst s' t' k Hrel' Hend) as [t'' [Hsilent Hend']].
  exists t''; split; [|exact Hend'].
  rewrite <- (app_nil_r tr); eapply exec_app; eassumption.
Qed.

Lemma stuttering_diverges_after {S1 S2 O} (m1 : semantics S1 O) e1
    (m2 : semantics S2 O) e2 R mu1 mu2 :
  stuttering m1 e1 m2 e2 R mu1 mu2 -> forall s t, R s t -> forall tr,
  diverges_after m1 s tr -> diverges_after m2 t tr.
Proof.
  intros Hst s t Hrel tr [s' [Hrun Hdiv]].
  destruct (stuttering_exec m1 e1 m2 e2 R mu1 mu2 Hst s tr s' Hrun t Hrel)
    as [t' [Hmatch Hrel']].
  exists t'; split; [exact Hmatch|].
  eapply stuttering_diverges; eassumption.
Qed.

(** Stuttering bisimilar states have equal finishes, prefixes and diverging prefixes. *)
Theorem stuttering_same_behaviour {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop) (mu1 mu2 : S1 -> S2 -> nat)
    (s : S1) (t : S2) :
  stuttering m1 e1 m2 e2 R mu1 mu2 -> R s t -> same_behaviour m1 e1 s m2 e2 t.
Proof.
  intros Hst Hrel.
  pose proof (stuttering_swap m1 e1 m2 e2 R mu1 mu2 Hst) as Hswap.
  constructor.
  - intros k tr; split; eapply stuttering_finish; eassumption.
  - intro tr; split; intros [u Hrun].
    + destruct (stuttering_exec m1 e1 m2 e2 R mu1 mu2 Hst s tr u Hrun t Hrel)
        as [v [Hmatch Hrel']]; exists v; exact Hmatch.
    + destruct (stuttering_exec _ _ _ _ _ _ _ Hswap t tr u Hrun s Hrel)
        as [v [Hmatch Hrel']]; exists v; exact Hmatch.
  - intro tr; split; eapply stuttering_diverges_after; eassumption.
Qed.

(** Lock-step bisimilar states have the same observable behaviour. *)
Theorem bisimilar_same_behaviour {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop) (s : S1) (t : S2) :
  bisimulation m1 e1 m2 e2 R -> R s t -> same_behaviour m1 e1 s m2 e2 t.
Proof.
  intros Hbis Hrel; eapply stuttering_same_behaviour with (mu1 := fun _ _ => 0)
    (mu2 := fun _ _ => 0); [|exact Hrel].
  destruct Hbis as [Hends Hforth Hback]; constructor.
  - intros u v k Huv Hend; exists v; split; [constructor|apply (Hends u v k Huv); exact Hend].
  - intros u v k Huv Hend; exists u; split; [constructor|apply (Hends u v k Huv); exact Hend].
  - intros u v l u' Huv Hstep; right.
    destruct (Hforth u v l u' Huv Hstep) as [v' [Hmatch Huv']].
    exists v, v'; split; [constructor|split; assumption].
  - intros u v l v' Huv Hstep; right.
    destruct (Hback u v l v' Huv Hstep) as [u' [Hmatch Huv']].
    exists u, u'; split; [constructor|split; assumption].
Qed.

(** Observable behaviour equality can be reversed. *)
Theorem same_behaviour_sym {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1) (s : S1)
    (m2 : semantics S2 O) (e2 : endings S2) (t : S2) :
  same_behaviour m1 e1 s m2 e2 t -> same_behaviour m2 e2 t m1 e1 s.
Proof.
  intros [Hfinish Hprefix Hdiv]; constructor.
  - intros k tr; symmetry; apply Hfinish.
  - intro tr; symmetry; apply Hprefix.
  - intro tr; symmetry; apply Hdiv.
Qed.

(** Behaviour equality composes through the same intermediate state and semantics. *)
Theorem same_behaviour_trans {S1 S2 S3 O} (m1 : semantics S1 O) (e1 : endings S1) (s : S1)
    (m2 : semantics S2 O) (e2 : endings S2) (t : S2) (m3 : semantics S3 O) (e3 : endings S3)
    (u : S3) :
  same_behaviour m1 e1 s m2 e2 t -> same_behaviour m2 e2 t m3 e3 u ->
  same_behaviour m1 e1 s m3 e3 u.
Proof.
  intros [Hfinish12 Hprefix12 Hdiv12] [Hfinish23 Hprefix23 Hdiv23]; constructor.
  - intros k tr; transitivity (exists v, exec m2 t tr v /\ ends_as m2 e2 k v).
    + apply Hfinish12.
    + apply Hfinish23.
  - intro tr; transitivity (exists v, exec m2 t tr v).
    + apply Hprefix12.
    + apply Hprefix23.
  - intro tr; transitivity (diverges_after m2 t tr).
    + apply Hdiv12.
    + apply Hdiv23.
Qed.
