(** * Boolean and unit lattices

    Booleans describe liveness, and unit supplies a trivial abstract domain.
    For example, joining false with true gives true.
    Builds on: OrderLattice and OrderConcrete. *)

From Stdlib Require Import Bool Arith Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete.

(** Boolean order is implication and join is disjunction. *)
Definition bool_lattice : lattice bool :=
  {| leb := implb;
     bot := false;
     join := orb;
     widen := orb;
     narrow := fun a _ => a |}.

(** True bounds both booleans. *)
Definition bool_top : top bool_lattice.
Proof.
  refine {| top_value := true |}; abstract (intros []; reflexivity).
Defined.

(** False and true have ranks zero and one. *)
Definition bool_height : monotone_height bool_lattice.
Proof.
  unshelve refine (@MonotoneHeight bool bool_lattice
    (@Height bool bool_lattice (fun b => if b then 1 else 0) 1 _ _) _).
  - abstract (intros []; cbn; lia).
  - abstract (intros [] []; cbn; intros Hstrict; try discriminate; lia).
  - abstract (intros [] []; cbn; intros Hle; try discriminate; lia).
Defined.

(** A live value needs equality; a dead value needs nothing. *)
Definition bool_agree {C} : agreement bool C :=
  {| agree := fun b x y => b = true -> x = y |}.

(** The unit lattice has only one possible operation result. *)
Definition unit_lattice : lattice unit :=
  {| leb := fun _ _ => true;
     bot := tt;
     join := fun _ _ => tt;
     widen := fun _ _ => tt;
     narrow := fun _ _ => tt |}.

(** Unit's unique value is greatest. *)
Definition unit_top : top unit_lattice.
Proof.
  refine {| top_value := tt |}; abstract (intros []; reflexivity).
Defined.

(** Unit has constant rank zero. *)
Definition unit_height : monotone_height unit_lattice.
Proof.
  unshelve refine (@MonotoneHeight unit unit_lattice
    (@Height unit unit_lattice (fun _ => 0) 0 _ _) _).
  - abstract (intros []; reflexivity).
  - abstract (intros [] []; discriminate).
  - abstract (intros [] [] _; reflexivity).
Defined.

(** Boolean operations satisfy the weak lattice laws. *)
Theorem bool_laws : lattice_laws bool_lattice.
Proof.
  constructor; intros; repeat match goal with
  | b : bool |- _ => destruct b
  end;
    cbn in *; congruence.
Qed.

(** Boolean disjunction is a least upper bound. *)
Theorem bool_lub : lub_laws bool_lattice.
Proof.
  constructor; intros [] [] []; cbn; congruence.
Qed.

(** Boolean liveness gives reflexive antitone agreement. *)
Theorem bool_agree_laws {C : Type} : agreement_laws bool_lattice (@bool_agree C).
Proof.
  constructor.
  - intros b c _; reflexivity.
  - intros [] [] x y Hle Hxy Hlive; cbn in *; try discriminate;
      apply Hxy; reflexivity.
Qed.

(** Dead values place no restriction on a pair. *)
Theorem bool_agree_bot {C : Type} : agreement_bot bool_lattice (@bool_agree C).
Proof.
  constructor; intros x y Hfalse; discriminate.
Qed.

(** Agreement for both boolean needs gives agreement for their disjunction. *)
Theorem bool_agree_join {C : Type} : agreement_join_law bool_lattice (@bool_agree C).
Proof.
  constructor; intros [] [] x y Hx Hy Hlive; cbn in *; try discriminate;
    first [solve [apply Hx; reflexivity] | solve [apply Hy; reflexivity]].
Qed.

(** Boolean agreement is symmetric and transitive. *)
Theorem bool_agree_equivalence {C : Type} : agreement_equivalence (@bool_agree C).
Proof.
  constructor; cbn.
  - intros a x y Hxy Ha; symmetry; apply Hxy; exact Ha.
  - intros a x y z Hxy Hyz Ha; transitivity y; [apply Hxy | apply Hyz]; exact Ha.
Qed.

(** The unique unit value satisfies all weak lattice laws. *)
Theorem unit_laws : lattice_laws unit_lattice.
Proof.
  constructor; intros; reflexivity.
Qed.

(** The unique unit value is a least upper bound. *)
Theorem unit_lub : lub_laws unit_lattice.
Proof.
  constructor; intros; reflexivity.
Qed.
