(** * Prepared contributor and reader indexes

    Index preparation visits each constraint once and stores its distinct destinations and reads.
    For example, repeating a declared side target adds its constraint only once to that target.
    Builds on: FixpointSystem and CollectionsFinSet. *)

From Stdlib Require Import List PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Fixpoint Require Import FixpointSystem.
Import List.ListNotations.

(** A system index stores contributor lists and reader lists by unknown. *)
Record sys_index (X C : Type) : Type := SysIndex {
  contributors : Map.t X (list C);
  readers : Map.t X (list C)
}.

Arguments SysIndex {X C}.
Arguments contributors {X C}.
Arguments readers {X C}.

(** Missing index entries denote empty constraint lists. *)
Definition index_get {X C} (EX : encoding X) (m : Map.t X (list C)) (x : X) : list C :=
  match Map.get EX x m with
  | Some cs => cs
  | None => []
  end.

Definition index_push {X C} (EX : encoding X) (c : C) (x : X)
  (m : Map.t X (list C)) : Map.t X (list C) :=
  Map.set EX x (c :: index_get EX m x) m.

Fixpoint index_push_many {X C} (EX : encoding X) (c : C) (xs : list X)
  (m : Map.t X (list C)) : Map.t X (list C) :=
  match xs with
  | [] => m
  | x :: xs' => index_push EX c x (index_push_many EX c xs' m)
  end.

Definition distinct_unknowns {X} (EX : encoding X) (xs : list X) : list X :=
  FinSet.elements (FinSet.of_list EX xs).

(** Build both indexes together, deduplicating each constraint's unknown lists once. *)
Definition index_system {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) : sys_index X C :=
  fold_right (fun c ix => SysIndex
    (index_push_many EX c (distinct_unknowns EX (System.target S c :: side_targets SS c))
      (contributors ix))
    (index_push_many EX c (distinct_unknowns EX (deps SS c)) (readers ix)))
    (SysIndex Map.empty Map.empty) (System.constraints S).

(** Contributor lookup uses the prepared map, defaulting to an empty list. *)
Definition contributors_of {X C} (EX : encoding X) (ix : sys_index X C) (x : X) : list C :=
  index_get EX (contributors ix) x.

(** Reader lookup uses the prepared map, defaulting to an empty list. *)
Definition readers_of {X C} (EX : encoding X) (ix : sys_index X C) (x : X) : list C :=
  index_get EX (readers ix) x.

(** Prepared lists agree with the declared system and preserve constraint uniqueness. *)
Record sys_index_laws {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) : Prop := {
  contributors_agree : forall x c, In c (contributors_of EX ix x) <->
    In c (System.constraints S) /\ (System.target S c = x \/ In x (side_targets SS c));
  readers_agree : forall x c, In c (readers_of EX ix x) <->
    In c (System.constraints S) /\ In x (deps SS c);
  index_nodup : NoDup (System.constraints S) ->
    forall x, NoDup (contributors_of EX ix x) /\ NoDup (readers_of EX ix x)
}.

Arguments contributors_agree {X C A EX S SS ix}.
Arguments Build_sys_index_laws {X C A EX S SS ix}.
Arguments readers_agree {X C A EX S SS ix}.
Arguments index_nodup {X C A EX S SS ix}.

Section IndexHelpers.
Context {X C : Type} (EX : encoding X).

Lemma index_get_empty (x : X) : index_get EX (@Map.empty X (list C)) x = [].
Proof.
  unfold index_get; rewrite Map.get_empty; reflexivity.
Qed.

Lemma index_get_push (c : C) (x y : X) (m : Map.t X (list C)) :
  index_get EX (index_push EX c x m) y =
    if Pos.eqb (encode EX y) (encode EX x) then c :: index_get EX m y
    else index_get EX m y.
Proof.
  unfold index_push; destruct (Pos.eqb (encode EX y) (encode EX x)) eqn:Hxy.
  - apply Pos.eqb_eq in Hxy; apply (encode_injective EX) in Hxy; subst y.
    unfold index_get at 1; rewrite Map.get_set_same; reflexivity.
  - assert (Hne : y <> x) by (intro Heq; subst; rewrite Pos.eqb_refl in Hxy; discriminate).
    unfold index_get at 1; rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Lemma index_push_many_agree (c d : C) (xs : list X) (m : Map.t X (list C)) (y : X) :
  In d (index_get EX (index_push_many EX c xs m) y) <->
    (d = c /\ In y xs) \/ In d (index_get EX m y).
Proof.
  induction xs as [|x xs IH]; cbn [index_push_many].
  - cbn; tauto.
  - rewrite index_get_push.
    destruct (Pos.eqb (encode EX y) (encode EX x)) eqn:Hxy; cbn.
    + apply Pos.eqb_eq in Hxy; apply (encode_injective EX) in Hxy; subst y.
      rewrite IH; intuition congruence.
    + assert (Hne : x <> y) by (intro Heq; subst; rewrite Pos.eqb_refl in Hxy; discriminate).
      rewrite IH; intuition congruence.
Qed.

Lemma index_push_many_nodup (c : C) (xs : list X) (m : Map.t X (list C)) :
  NoDup xs -> (forall y, NoDup (index_get EX m y)) ->
  (forall y, ~ In c (index_get EX m y)) ->
  forall y, NoDup (index_get EX (index_push_many EX c xs m) y).
Proof.
  intros Hxs Hnodup Hfresh; induction Hxs as [|x xs Hnotin Hxs IH]; intro y.
  - apply Hnodup.
  - cbn [index_push_many]; rewrite index_get_push.
    destruct (Pos.eqb (encode EX y) (encode EX x)) eqn:Hxy.
    + apply Pos.eqb_eq in Hxy; apply (encode_injective EX) in Hxy; subst y.
      constructor; [|apply IH].
      rewrite index_push_many_agree; intros [[_ Hin]|Hin].
      * exact (Hnotin Hin).
      * exact (Hfresh x Hin).
    + apply IH.
Qed.

Lemma distinct_unknowns_spec (xs : list X) (x : X) :
  In x (distinct_unknowns EX xs) <-> In x xs.
Proof.
  unfold distinct_unknowns; rewrite FinSet.elements_spec by apply FinSet.wf_fold_add,
    Map.wf_empty.
  apply FinSet.of_list_spec.
Qed.

Lemma distinct_unknowns_nodup (xs : list X) : NoDup (distinct_unknowns EX xs).
Proof.
  apply (FinSet.elements_nodup EX); apply FinSet.wf_fold_add, Map.wf_empty.
Qed.

End IndexHelpers.

Section IndexLaws.
Context {X C A : Type} (EX : encoding X) (S : System.t X C A) (SS : System.static S).

Definition index_constraints (cs : list C) : sys_index X C :=
  fold_right (fun c ix => SysIndex
    (index_push_many EX c (distinct_unknowns EX (System.target S c :: side_targets SS c))
      (contributors ix))
    (index_push_many EX c (distinct_unknowns EX (deps SS c)) (readers ix)))
    (SysIndex Map.empty Map.empty) cs.

Lemma index_constraints_agree (cs : list C) :
  (forall x c, In c (contributors_of EX (index_constraints cs) x) <->
    In c cs /\ (System.target S c = x \/ In x (side_targets SS c))) /\
  (forall x c, In c (readers_of EX (index_constraints cs) x) <->
    In c cs /\ In x (deps SS c)).
Proof.
  induction cs as [|d cs [IHc IHr]].
  - split; intros x c; unfold contributors_of, readers_of;
      cbn [index_constraints fold_right contributors readers].
    all: rewrite index_get_empty; cbn; tauto.
  - split; intros x c; unfold contributors_of, readers_of;
      cbn [index_constraints fold_right contributors readers].
    + rewrite index_push_many_agree, distinct_unknowns_spec.
      change ((c = d /\ In x (System.target S d :: side_targets SS d)) \/
        In c (contributors_of EX (index_constraints cs) x) <->
        In c (d :: cs) /\ (System.target S c = x \/ In x (side_targets SS c))).
      rewrite IHc; cbn; intuition congruence.
    + rewrite index_push_many_agree, distinct_unknowns_spec.
      change ((c = d /\ In x (deps SS d)) \/
        In c (readers_of EX (index_constraints cs) x) <-> In c (d :: cs) /\ In x (deps SS c)).
      rewrite IHr; cbn; intuition congruence.
Qed.

Lemma index_constraints_nodup (cs : list C) : NoDup cs ->
  forall x, NoDup (contributors_of EX (index_constraints cs) x) /\
    NoDup (readers_of EX (index_constraints cs) x).
Proof.
  intro Hcs; induction Hcs as [|c cs Hfresh Hcs IH]; intro x.
  - unfold contributors_of, readers_of; cbn [index_constraints fold_right contributors readers].
    rewrite index_get_empty; split; constructor.
  - destruct (index_constraints_agree cs) as [Hcontributors Hreaders].
    split; unfold contributors_of, readers_of;
      cbn [index_constraints fold_right contributors readers].
    + apply index_push_many_nodup; [apply distinct_unknowns_nodup| |].
      * intro y; apply (proj1 (IH y)).
      * intros y Hin; apply Hfresh; apply (proj1 (Hcontributors y c) Hin).
    + apply index_push_many_nodup; [apply distinct_unknowns_nodup| |].
      * intro y; apply (proj2 (IH y)).
      * intros y Hin; apply Hfresh; apply (proj1 (Hreaders y c) Hin).
Qed.

(** Index construction establishes membership agreement and duplicate-free lists. *)
Theorem index_system_laws : sys_index_laws EX S SS (index_system EX S SS).
Proof.
  destruct (index_constraints_agree (System.constraints S)) as [Hc Hr].
  constructor; [exact Hc|exact Hr|].
  apply index_constraints_nodup.
Qed.

End IndexLaws.
