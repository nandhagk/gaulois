(** * Monotone functions

    Closure laws build monotone transfers from constants, reads, joins and composition.
    For example, reading one unknown preserves pointwise order on assignments.
    Builds on: OrderLattice and Stdlib relations. *)

From Stdlib.Relations Require Import Relation_Definitions.
From Gaulois.Order Require Import OrderLattice.

(** Assignments are ordered pointwise. *)
Definition fun_leb {X A} (L : lattice A) (s1 s2 : X -> A) : Prop :=
  forall x, leb L (s1 x) (s2 x) = true.

(** A unary function preserves boolean order. *)
Definition monotone_fun {A B} (L1 : lattice A) (L2 : lattice B) (f : A -> B) : Prop :=
  forall a b, leb L1 a b = true -> leb L2 (f a) (f b) = true.

(** A binary function preserves order in both arguments together. *)
Definition monotone_fun2 {A B C} (L1 : lattice A) (L2 : lattice B) (L3 : lattice C)
  (f : A -> B -> C) : Prop :=
  forall a1 a2 b1 b2, leb L1 a1 a2 = true -> leb L2 b1 b2 = true ->
  leb L3 (f a1 b1) (f a2 b2) = true.

(** A transfer preserves pointwise order on its input assignment. *)
Definition monotone_on_assignments {X A B} (L1 : lattice A) (L2 : lattice B)
  (f : (X -> A) -> B) : Prop :=
  forall s1 s2, fun_leb L1 s1 s2 -> leb L2 (f s1) (f s2) = true.

Section MonotoneLaws.
Context {X A B C : Type} (L1 : lattice A) (L2 : lattice B) (L3 : lattice C).

(** Identity preserves order. *)
Theorem monotone_id : lattice_laws L1 -> monotone_fun L1 L1 (fun a => a).
Proof.
  intros _ a b Hab; exact Hab.
Qed.

(** A constant function preserves order by reflexivity. *)
Theorem monotone_const : forall b : B, lattice_laws L2 -> monotone_fun L1 L2 (fun _ => b).
Proof.
  intros b laws a a' _; apply (leb_refl laws).
Qed.

(** Composition preserves monotonicity. *)
Theorem monotone_compose : forall (f : A -> B) (g : B -> C),
  monotone_fun L1 L2 f -> monotone_fun L2 L3 g -> monotone_fun L1 L3 (fun a => g (f a)).
Proof.
  intros f g Hf Hg a b Hab; apply Hg; apply Hf; exact Hab.
Qed.

(** Least upper bounds give a monotone binary join. *)
Theorem monotone_join : lattice_laws L1 -> lub_laws L1 -> monotone_fun2 L1 L1 L1 (join L1).
Proof.
  intros laws lub a a' b b' Ha Hb; apply (join_monotone L1 _ _ _ _ laws lub Ha Hb).
Qed.

(** A constant transfer preserves assignment order. *)
Theorem monotone_on_const : forall b : B, lattice_laws L2 ->
  @monotone_on_assignments X A B L1 L2 (fun _ => b).
Proof.
  intros b laws s1 s2 _; apply (leb_refl laws).
Qed.

(** Reading one unknown preserves assignment order. *)
Theorem monotone_on_lookup : forall x : X,
  @monotone_on_assignments X A A L1 L1 (fun s => s x).
Proof.
  intros x s1 s2 Hs; apply Hs.
Qed.

(** Joining monotone transfers remains monotone when joins are least upper bounds. *)
Theorem monotone_on_join : forall f g : (X -> A) -> A, lattice_laws L1 -> lub_laws L1 ->
  monotone_on_assignments L1 L1 f -> monotone_on_assignments L1 L1 g ->
  monotone_on_assignments L1 L1 (fun s => join L1 (f s) (g s)).
Proof.
  intros f g laws lub Hf Hg s1 s2 Hs.
  apply (join_monotone L1 _ _ _ _ laws lub); [apply Hf | apply Hg]; exact Hs.
Qed.

(** Composing a monotone transfer with a monotone function remains monotone. *)
Theorem monotone_on_compose : forall (f : (X -> A) -> B) (g : B -> C),
  monotone_on_assignments L1 L2 f -> monotone_fun L2 L3 g ->
  monotone_on_assignments L1 L3 (fun s => g (f s)).
Proof.
  intros f g Hf Hg s1 s2 Hs; apply Hg; apply Hf; exact Hs.
Qed.

(** The pointwise assignment order is a preorder. *)
Theorem fun_leb_preorder : lattice_laws L1 ->
  preorder (X -> A) (fun s1 s2 => fun_leb L1 s1 s2).
Proof.
  intro laws; constructor.
  - intros s x; apply (leb_refl laws).
  - intros s1 s2 s3 H12 H23 x; eapply (leb_trans laws); [apply H12 | apply H23].
Qed.
End MonotoneLaws.
