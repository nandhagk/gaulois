(** * Flat values

    A flat lattice distinguishes unreachable, one known value and an unknown value.
    For example, joining two unequal known values returns FTop.
    Builds on: OrderLattice and OrderConcrete. *)

From Stdlib Require Import Bool Arith Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete.

(** Flat values add an empty bottom and an unconstrained top. *)
Inductive flat (A : Type) : Type :=
  | FBot
  | FVal (a : A)
  | FTop.

Arguments FBot {A}.
Arguments FVal {A}.
Arguments FTop {A}.

(** Flat comparison tests equality only between two known values. *)
Definition flat_lattice {A} (eqb : A -> A -> bool) : lattice (flat A) :=
  let combine := fun x y =>
    match x, y with
    | FBot, _ => y
    | _, FBot => x
    | FVal a, FVal b => if eqb a b then FVal a else FTop
    | _, _ => FTop
    end in
  {| leb := fun x y =>
       match x, y with
       | FBot, _ => true
       | _, FTop => true
       | FVal a, FVal b => eqb a b
       | _, _ => false
       end;
     bot := FBot;
     join := combine;
     widen := combine;
     narrow := fun x _ => x |}.

(** FTop bounds every flat value. *)
Definition flat_top {A} (eqb : A -> A -> bool) : top (flat_lattice eqb).
Proof.
  refine {| top_value := FTop |}; abstract (intros [|a|]; reflexivity).
Defined.

(** Flat concretisation interprets bottom as empty and top as full. *)
Definition flat_gamma {A C} (G : A -> C -> Prop) : concretisation (flat A) C :=
  {| gamma := fun x c =>
       match x with
       | FBot => False
       | FVal a => G a c
       | FTop => True
       end |}.

(** Flat agreement needs nothing at bottom and equality at top. *)
Definition flat_agree {A C} (R : A -> C -> C -> Prop) : agreement (flat A) C :=
  {| agree := fun a x y =>
       match a with
       | FBot => True
       | FVal v => R v x y
       | FTop => x = y
       end |}.

Section FlatLaws.
Context {A C : Type} (eqb : A -> A -> bool) (G : A -> C -> Prop).

Lemma flat_eqb_refl : eqb_spec eqb -> forall a, eqb a a = true.
Proof.
  intros Hspec a; apply Hspec; reflexivity.
Qed.

(** Flat operations satisfy the weak lattice laws when equality is reflected. *)
Theorem flat_laws : eqb_spec eqb -> lattice_laws (flat_lattice eqb).
Proof.
  intro Hspec; constructor.
  - intros [|a|]; cbn; auto using flat_eqb_refl.
  - intros [|a|] [|b|] [|c|]; cbn; intros Hab Hbc; try discriminate; try reflexivity.
    apply Hspec in Hab; subst b; exact Hbc.
  - intros [|a|]; reflexivity.
  - intros [|a|] [|b|]; cbn; try reflexivity; try apply (flat_eqb_refl Hspec).
    destruct (eqb a b) eqn:Hab; cbn; [apply (flat_eqb_refl Hspec) | reflexivity].
  - intros [|a|] [|b|]; cbn; try reflexivity; try apply (flat_eqb_refl Hspec).
    destruct (eqb a b) eqn:Hab; cbn; [apply Hspec in Hab; subst b;
      apply (flat_eqb_refl Hspec) | reflexivity].
  - intros [|a|] [|b|]; cbn; try reflexivity; try apply (flat_eqb_refl Hspec).
    destruct (eqb a b) eqn:Hab; cbn; [apply (flat_eqb_refl Hspec) | reflexivity].
  - intros [|a|] [|b|]; cbn; try reflexivity; try apply (flat_eqb_refl Hspec).
    destruct (eqb a b) eqn:Hab; cbn; [apply Hspec in Hab; subst b;
      apply (flat_eqb_refl Hspec) | reflexivity].
  - intros [|a|] b _; cbn; auto using flat_eqb_refl.
  - intros a b Hab; exact Hab.
Qed.

(** Flat joins are least upper bounds. *)
Theorem flat_lub : eqb_spec eqb -> lub_laws (flat_lattice eqb).
Proof.
  intro Hspec; constructor; intros [|a|] [|b|] [|c|]; cbn;
    intros Ha Hb; try discriminate; try reflexivity; try assumption.
  apply Hspec in Ha; apply Hspec in Hb; subst.
  rewrite (flat_eqb_refl Hspec); apply (flat_eqb_refl Hspec).
  all: destruct (eqb a b); reflexivity.
Qed.

(** The flat order preserves every supplied concretisation. *)
Theorem flat_gamma_laws : eqb_spec eqb ->
  concretisation_laws (flat_lattice eqb) (flat_gamma G).
Proof.
  intro Hspec; constructor; intros [|a|] [|b|] c Hab Hc; cbn in *;
    try contradiction; try discriminate; try exact I.
  apply Hspec in Hab; subst b; exact Hc.
Qed.

(** Flat bottom has no concrete values. *)
Theorem flat_gamma_bot_empty : bottom_empty (flat_lattice eqb) (flat_gamma G).
Proof.
  constructor; intros c Hc; exact Hc.
Qed.

(** Flat top denotes every concrete value. *)
Theorem flat_gamma_top_full : top_full (flat_top eqb) (flat_gamma G).
Proof.
  constructor; intro c; exact I.
Qed.
End FlatLaws.

(** The three flat levels have monotone ranks zero, one and two. *)
Definition flat_height {A} (eqb : A -> A -> bool) (Hspec : eqb_spec eqb) :
  monotone_height (flat_lattice eqb).
Proof.
  unshelve refine (@MonotoneHeight _ _
    (@Height _ _ (fun x =>
      match x with
      | FBot => 0
      | FVal _ => 1
      | FTop => 2
      end) 2 _ _) _).
  - abstract (intros [|a|]; cbn; lia).
  - abstract (intros [|a|] [|b|]; cbn; try discriminate; try lia;
      [rewrite (flat_eqb_refl eqb Hspec); discriminate |
       destruct (eqb a b) eqn:Hab; cbn; [rewrite (flat_eqb_refl eqb Hspec) |];
         intros Hstrict; try discriminate; lia]).
  - abstract (intros [|a|] [|b|]; cbn; intros Hab; try discriminate; lia).
Defined.

Section AgreeLaws.
Context {A C : Type} (eqb : A -> A -> bool) (RV : A -> C -> C -> Prop).

(** Reflexive needs extend to antitone flat agreement. *)
Theorem flat_agree_laws : eqb_spec eqb -> (forall a c, RV a c c) ->
  agreement_laws (flat_lattice eqb) (flat_agree RV).
Proof.
  intros Hspec HR; constructor.
  - intros [|a|] c; cbn; auto.
  - intros [|a|] [|b|] x y Hab Hxy; cbn in *; try discriminate; try exact I;
      try exact Hxy.
    + apply Hspec in Hab; subst b; exact Hxy.
    + subst y; apply HR.
Qed.

(** Flat bottom requires no agreement. *)
Theorem flat_agree_bot : agreement_bot (flat_lattice eqb) (flat_agree RV).
Proof.
  constructor; intros x y; exact I.
Qed.
End AgreeLaws.
