(** * Reachable assignments and least solutions

    Joining each constraint's outputs defines runs from the bottom assignment.
    For example, a constant constraint can raise its target in one run.
    Builds on: FixpointSystem, FixpointQuery and OrderMonotone. *)

From Stdlib Require Import List Bool PArith Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.
Import List.ListNotations.

(** A single update joins only when its value is not already below the destination. *)
Definition join_update {X A} (EX : encoding X) (L : lattice A) (x : X) (a : A)
  (s : X -> A) : X -> A :=
  fun y => if Pos.eqb (encode EX x) (encode EX y)
    then (if leb L a (s y) then s y else join L (s y) a) else s y.

(** One query run supplies the target update followed by the side updates. *)
Definition run_updates {X C A} (S : System.t X C A) (c : C) (s : X -> A) : list (X * A) :=
  let '(v, _, ss) := Query.run (System.rhs S c) s in (System.target S c, v) :: ss.

(** Updates are applied in trace order, retaining the previous value when already sufficient. *)
Definition apply_updates {X A} (EX : encoding X) (L : lattice A) (ups : list (X * A))
  (s : X -> A) : X -> A :=
  fold_left (fun s' xa => join_update EX L (fst xa) (snd xa) s') ups s.

(** A raise performs one listed constraint run, up to pointwise equality. *)
Definition raise {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (s t : X -> A) : Prop :=
  exists c, In c (System.constraints S) /\
    forall y, t y = apply_updates EX L (run_updates S c s) s y.

(** Reached assignments arise from bottom by finitely many constraint runs. *)
Definition reached {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (s : X -> A) : Prop :=
  exists s0, (forall x, s0 x = bot L) /\ clos_refl_trans (X -> A) (raise EX L S) s0 s.

(** A least solution is a post-solution below every post-solution. *)
Definition least_solution {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) : Prop :=
  post_solution L S s /\ forall t, post_solution L S t -> fun_leb L s t.

Section LeastLaws.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).

Lemma join_update_below (HL : lattice_laws L) (HJ : lub_laws L)
  (s t : X -> A) (x : X) (a : A) :
  fun_leb L s t -> leb L a (t x) = true -> fun_leb L (join_update EX L x a s) t.
Proof.
  intros Hst Ha y; unfold join_update.
  destruct (Pos.eqb (encode EX x) (encode EX y)) eqn:Hxy.
  - apply Pos.eqb_eq in Hxy; apply (encode_injective EX) in Hxy; subst y.
    destruct (leb L a (s x)); [apply Hst|].
    apply (join_least HJ); [apply Hst|exact Ha].
  - apply Hst.
Qed.

Lemma apply_updates_below (HL : lattice_laws L) (HJ : lub_laws L)
  (ups : list (X * A)) (s t : X -> A) :
  fun_leb L s t -> (forall x a, In (x, a) ups -> leb L a (t x) = true) ->
  fun_leb L (apply_updates EX L ups s) t.
Proof.
  revert s; induction ups as [|[x a] ups IH]; intros s Hst Hups; cbn [apply_updates].
  - exact Hst.
  - apply IH.
    + apply (join_update_below HL HJ); [exact Hst|apply Hups; now left].
    + intros y b Hb; apply Hups; now right.
Qed.

Lemma run_updates_below (HL : lattice_laws L) (s t : X -> A) (c : C) :
  monotone_query L (System.rhs S c) -> post_solution L S t ->
  In c (System.constraints S) -> fun_leb L s t ->
  forall x a, In (x, a) (run_updates S c s) -> leb L a (t x) = true.
Proof.
  intros [Hvalue Hside] Hpost Hc Hst x a Ha.
  unfold run_updates in Ha; rewrite run_spec in Ha; cbn in Ha.
  destruct (Hpost c Hc) as [Hv Hs].
  destruct Ha as [Ha|Ha].
  - inversion Ha; subst x a.
    eapply (leb_trans HL); [apply Hvalue; exact Hst|exact Hv].
  - destruct (Hside s t Hst x a Ha) as [b [Hb Hab]].
    eapply (leb_trans HL); [exact Hab|exact (Hs x b Hb)].
Qed.

Lemma raise_below (HL : lattice_laws L) (HJ : lub_laws L) (HM : monotone_system L S)
  (t s u : X -> A) :
  post_solution L S t -> fun_leb L s t -> raise EX L S s u -> fun_leb L u t.
Proof.
  intros Hpost Hst [c [Hc Hu]] y; rewrite Hu.
  apply (apply_updates_below HL HJ); [exact Hst|].
  apply (run_updates_below HL s t c (HM c Hc) Hpost Hc Hst).
Qed.

(** Every assignment reached in a monotone system stays below every post-solution. *)
Theorem reached_below (s t : X -> A) :
  lattice_laws L -> lub_laws L -> monotone_system L S ->
  post_solution L S t -> reached EX L S s -> fun_leb L s t.
Proof.
  intros HL HJ HM Hpost [s0 [Hbot Hsteps]].
  assert (Hpreserve : forall u v, clos_refl_trans (X -> A) (raise EX L S) u v ->
    fun_leb L u t -> fun_leb L v t).
  { intros u v Hrun; induction Hrun as [u v Hraise|u|u v w Huv IHuv Hvw IHvw]; intro Hu.
    - exact (raise_below HL HJ HM t u v Hpost Hu Hraise).
    - exact Hu.
    - apply IHvw; apply IHuv; exact Hu. }
  apply (Hpreserve s0 s Hsteps); intro x; rewrite Hbot; apply (bot_least HL).
Qed.

(** A reached post-solution is least under the separate least-upper-bound laws. *)
Theorem reached_least (s : X -> A) :
  lattice_laws L -> lub_laws L -> monotone_system L S ->
  reached EX L S s -> post_solution L S s -> least_solution L S s.
Proof.
  intros HL HJ HM Hreached Hpost; split; [exact Hpost|].
  intros t Ht; exact (reached_below s t HL HJ HM Ht Hreached).
Qed.

(** Least solutions bound each other and hence agree up to preorder equivalence. *)
Theorem least_solution_unique (s1 s2 : X -> A) :
  least_solution L S s1 -> least_solution L S s2 -> fun_leb L s1 s2 /\ fun_leb L s2 s1.
Proof.
  intros [Hpost1 Hleast1] [Hpost2 Hleast2]; split.
  - exact (Hleast1 s2 Hpost2).
  - exact (Hleast2 s1 Hpost1).
Qed.

End LeastLaws.
