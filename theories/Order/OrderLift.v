(** * Fresh bottoms and tops

    Lifting adds an unreachable bottom or a fully unknown top to an existing domain.
    For example, Some a joined with None keeps Some a.
    Builds on: OrderLattice and OrderConcrete. *)

From Stdlib Require Import Bool Arith Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete.

(** Option adds a fresh bottom and otherwise uses the underlying operations. *)
Definition option_lattice {A} (L : lattice A) : lattice (option A) :=
  {| leb := fun x y =>
       match x, y with
       | None, _ => true
       | Some a, Some b => leb L a b
       | Some _, None => false
       end;
     bot := None;
     join := fun x y =>
       match x, y with
       | None, _ => y
       | _, None => x
       | Some a, Some b => Some (join L a b)
       end;
     widen := fun x y =>
       match x, y with
       | None, _ => y
       | _, None => x
       | Some a, Some b => Some (widen L a b)
       end;
     narrow := fun x y =>
       match x, y with
       | None, _ => None
       | _, None => x
       | Some a, Some b => Some (narrow L a b)
       end |}.

(** The bottom lift is represented by option. *)
Definition lift_bot (A : Type) : Type := option A.

Abbreviation Unreached := None.
Abbreviation Reached := Some.
Abbreviation lift_bot_lattice := option_lattice.

(** An underlying top remains greatest after lifting it into Some. *)
Definition option_top {A} {L : lattice A} (T : top L) : top (option_lattice L).
Proof.
  refine {| top_value := Some (top_value T) |};
    abstract (intros [a|]; cbn; [apply (top_greatest T) | reflexivity]).
Defined.

(** Option bottom denotes no concrete value. *)
Definition option_gamma {A C} (G : concretisation A C) : concretisation (option A) C :=
  {| gamma := fun a c =>
       match a with
       | None => False
       | Some v => gamma G v c
       end |}.

(** Option bottom requires no agreement. *)
Definition option_agree {A C} (R : agreement A C) : agreement (option A) C :=
  {| agree := fun a x y =>
       match a with
       | None => True
       | Some v => agree R v x y
       end |}.

Abbreviation lift_bot_gamma := option_gamma.
Abbreviation lift_bot_agree := option_agree.

(** A top lift adds an explicit fully unknown value. *)
Inductive lift_top (A : Type) : Type :=
  | Elem (a : A)
  | Unknown.

Arguments Elem {A}.
Arguments Unknown {A}.

(** The fresh top absorbs joins and widening, while narrowing can descend from it. *)
Definition lift_top_lattice {A} (L : lattice A) : lattice (lift_top A) :=
  {| leb := fun x y =>
       match x, y with
       | _, Unknown => true
       | Elem a, Elem b => leb L a b
       | Unknown, Elem _ => false
       end;
     bot := Elem (bot L);
     join := fun x y =>
       match x, y with
       | Elem a, Elem b => Elem (join L a b)
       | _, _ => Unknown
       end;
     widen := fun x y =>
       match x, y with
       | Elem a, Elem b => Elem (widen L a b)
       | _, _ => Unknown
       end;
     narrow := fun x y =>
       match x, y with
       | Elem a, Elem b => Elem (narrow L a b)
       | Unknown, _ => y
       | _, Unknown => x
       end |}.

(** Unknown bounds every lifted value. *)
Definition lift_top_top {A} (L : lattice A) : top (lift_top_lattice L).
Proof.
  refine {| top_value := Unknown |}; abstract (intros [a|]; reflexivity).
Defined.

(** Unknown denotes every concrete value. *)
Definition lift_top_gamma {A C} (G : concretisation A C) : concretisation (lift_top A) C :=
  {| gamma := fun a c =>
       match a with
       | Elem v => gamma G v c
       | Unknown => True
       end |}.

(** Unknown agreement requires equality of the concrete values. *)
Definition lift_top_agree {A C} (R : agreement A C) : agreement (lift_top A) C :=
  {| agree := fun a x y =>
       match a with
       | Elem v => agree R v x y
       | Unknown => x = y
       end |}.

Section LiftLaws.
Context {A C : Type} (L : lattice A) (G : concretisation A C) (R : agreement A C).

(** A fresh bottom preserves the weak lattice laws. *)
Theorem option_laws : lattice_laws L -> lattice_laws (option_lattice L).
Proof.
  intro laws; constructor.
  - intros [a|]; cbn; [apply (leb_refl laws) | reflexivity].
  - intros [a|] [b|] [c|]; cbn; intros Hab Hbc; try discriminate; try reflexivity.
    eapply (leb_trans laws); eassumption.
  - intros [a|]; reflexivity.
  - intros [a|] [b|]; cbn; try reflexivity;
      [apply (join_upper_l laws) | apply (leb_refl laws)].
  - intros [a|] [b|]; cbn; try reflexivity;
      [apply (join_upper_r laws) | apply (leb_refl laws)].
  - intros [a|] [b|]; cbn; try reflexivity;
      [apply (widen_upper_l laws) | apply (leb_refl laws)].
  - intros [a|] [b|]; cbn; try reflexivity;
      [apply (widen_upper_r laws) | apply (leb_refl laws)].
  - intros [a|] [b|]; cbn; intros Hab; try discriminate; try reflexivity;
      [apply (narrow_lower laws _ _ Hab) | apply (leb_refl laws)].
  - intros [a|] [b|]; cbn; intros Hab; try discriminate; try reflexivity;
      apply (narrow_upper laws _ _ Hab).
Qed.

(** Fresh bottom joins retain the least-upper-bound law. *)
Theorem option_lub : lub_laws L -> lub_laws (option_lattice L).
Proof.
  intro lub; constructor; intros [a|] [b|] [c|]; cbn; intros Ha Hb;
    try discriminate; try reflexivity; try assumption; apply (join_least lub); assumption.
Qed.

(** The lifted meaning is monotone when the original meaning is. *)
Theorem option_gamma_laws : concretisation_laws L G ->
  concretisation_laws (option_lattice L) (option_gamma G).
Proof.
  intro HG; constructor; intros [a|] [b|] c Hab Hc; cbn in *;
    try contradiction; try discriminate; eapply (gamma_monotone HG); eassumption.
Qed.

(** Fresh bottom denotes no values independently of the original bottom. *)
Theorem option_gamma_bot_empty : bottom_empty (option_lattice L) (option_gamma G).
Proof.
  constructor; intros c Hc; exact Hc.
Qed.

(** Lifted agreement is reflexive and antitone. *)
Theorem option_agree_laws : agreement_laws L R ->
  agreement_laws (option_lattice L) (option_agree R).
Proof.
  intro HR; constructor.
  - intros [a|] c; cbn; [apply (agree_refl HR) | exact I].
  - intros [a|] [b|] x y Hab Hxy; cbn in *; try discriminate; try exact I.
    eapply (agree_antitone HR); eassumption.
Qed.

(** Fresh bottom imposes no need. *)
Theorem option_agree_bot : agreement_bot (option_lattice L) (option_agree R).
Proof.
  constructor; intros x y; exact I.
Qed.

(** Fresh bottom preserves agreement on joins. *)
Theorem option_agree_join : agreement_join_law L R ->
  agreement_join_law (option_lattice L) (option_agree R).
Proof.
  intro HR; constructor; intros [a|] [b|] x y Ha Hb; cbn in *;
    try exact I; try assumption; apply (agree_join HR); assumption.
Qed.

(** Adding top preserves the weak lattice laws. *)
Theorem lift_top_laws : lattice_laws L -> lattice_laws (lift_top_lattice L).
Proof.
  intro laws; constructor.
  - intros [a|]; cbn; [apply (leb_refl laws) | reflexivity].
  - intros [a|] [b|] [c|]; cbn; intros Hab Hbc; try discriminate; try reflexivity.
    eapply (leb_trans laws); eassumption.
  - intros [a|]; cbn; [apply (bot_least laws) | reflexivity].
  - intros [a|] [b|]; cbn; try reflexivity; apply (join_upper_l laws).
  - intros [a|] [b|]; cbn; try reflexivity; apply (join_upper_r laws).
  - intros [a|] [b|]; cbn; try reflexivity; apply (widen_upper_l laws).
  - intros [a|] [b|]; cbn; try reflexivity; apply (widen_upper_r laws).
  - intros [a|] [b|]; cbn; intros Hab; try discriminate; try reflexivity;
      apply (narrow_lower laws _ _ Hab).
  - intros [a|] [b|]; cbn; intros Hab; try discriminate; try reflexivity;
      [apply (narrow_upper laws _ _ Hab) | apply (leb_refl laws)].
Qed.

(** Adding top preserves least upper bounds. *)
Theorem lift_top_lub : lub_laws L -> lub_laws (lift_top_lattice L).
Proof.
  intro lub; constructor; intros [a|] [b|] [c|]; cbn; intros Ha Hb;
    try discriminate; try reflexivity; apply (join_least lub); assumption.
Qed.

(** The top-lifted meaning is monotone. *)
Theorem lift_top_gamma_laws : concretisation_laws L G ->
  concretisation_laws (lift_top_lattice L) (lift_top_gamma G).
Proof.
  intro HG; constructor; intros [a|] [b|] c Hab Hc; cbn in *;
    try discriminate; try exact I; eapply (gamma_monotone HG); eassumption.
Qed.

(** Fresh top denotes every concrete value. *)
Theorem lift_top_gamma_top_full : top_full (lift_top_top L) (lift_top_gamma G).
Proof.
  constructor; intro c; exact I.
Qed.

(** Top agreement is reflexive and antitone because equality implies every reflexive need. *)
Theorem lift_top_agree_laws : agreement_laws L R ->
  agreement_laws (lift_top_lattice L) (lift_top_agree R).
Proof.
  intro HR; constructor.
  - intros [a|] c; cbn; [apply (agree_refl HR) | reflexivity].
  - intros [a|] [b|] x y Hab Hxy; cbn in *; try discriminate; try exact Hxy.
    + eapply (agree_antitone HR); eassumption.
    + subst y; apply (agree_refl HR).
Qed.

(** Top lifting retains an agreement-free original bottom. *)
Theorem lift_top_agree_bot : agreement_bot L R ->
  agreement_bot (lift_top_lattice L) (lift_top_agree R).
Proof.
  intro HR; constructor; apply (agree_bot HR).
Qed.

(** Top lifting preserves join agreement, with equality in the absorbing cases. *)
Theorem lift_top_agree_join : agreement_join_law L R ->
  agreement_join_law (lift_top_lattice L) (lift_top_agree R).
Proof.
  intro HR; constructor; intros [a|] [b|] x y Ha Hb; cbn in *; try assumption.
  apply (agree_join HR); assumption.
Qed.
End LiftLaws.

(** The fresh bottom has rank zero and reached values have successor ranks. *)
Definition option_height {A} {L : lattice A} (laws : lattice_laws L) (H : monotone_height L) :
  monotone_height (option_lattice L).
Proof.
  unshelve refine (@MonotoneHeight _ (option_lattice L)
    (@Height _ (option_lattice L)
      (fun x =>
        match x with
        | None => 0
        | Some a => S (rank (base_height H) a)
        end)
      (S (bound (base_height H))) _ _) _).
  - abstract (intros [a|]; cbn;
      [pose proof (rank_bounded (base_height H) a) as Hbound |]; lia).
  - abstract (intros [a|] [b|]; cbn; intro Hstrict; try discriminate; try lia;
      [pose proof (join_rank_grows (base_height H) a b Hstrict) as Hgrow; lia |
       rewrite (leb_refl laws) in Hstrict; discriminate]).
  - abstract (intros [a|] [b|]; cbn; intro Hle; try discriminate; try lia;
      pose proof (rank_monotone H _ _ Hle) as Hgrow; lia).
Defined.

(** The fresh bottom's widening rank exceeds all reached ranks. *)
Definition option_wrank {A} {L : lattice A} (W : bounded_widening_rank L) :
  bounded_widening_rank (option_lattice L).
Proof.
  unshelve refine (@BoundedWideningRank _ (option_lattice L)
    (@WideningRank _ (option_lattice L)
      (fun x =>
        match x with
        | None => S (wbound W)
        | Some a => wrank (base_wrank W) a
        end)
      _ _) (S (wbound W)) _).
  - abstract (intros [a|] [b|]; cbn; intro Hle; try discriminate; try lia;
      apply (widen_rank_stable (base_wrank W) _ _ Hle)).
  - abstract (intros [a|] [b|]; cbn; intro Hstrict; try discriminate;
      [apply (widen_rank_progress (base_wrank W) _ _ Hstrict) |
       pose proof (wrank_bounded W b) as Hbound; lia]).
  - abstract (intros [a|]; cbn; [pose proof (wrank_bounded W a) as Hbound |]; lia).
Defined.

(** Unknown receives a rank strictly above the entire original domain. *)
Definition lift_top_height {A} {L : lattice A} (H : monotone_height L) :
  monotone_height (lift_top_lattice L).
Proof.
  unshelve refine (@MonotoneHeight _ (lift_top_lattice L)
    (@Height _ (lift_top_lattice L)
      (fun x =>
        match x with
        | Elem a => rank (base_height H) a
        | Unknown => S (bound (base_height H))
        end)
      (S (bound (base_height H))) _ _) _).
  - abstract (intros [a|]; cbn;
      [pose proof (rank_bounded (base_height H) a) as Hbound |]; lia).
  - abstract (intros [a|] [b|]; cbn; intro Hstrict; try discriminate;
      [apply (join_rank_grows (base_height H) _ _ Hstrict) |
       pose proof (rank_bounded (base_height H) a) as Hbound; lia]).
  - abstract (intros [a|] [b|]; cbn; intro Hle; try discriminate; try lia;
      [apply (rank_monotone H _ _ Hle) |
       pose proof (rank_bounded (base_height H) a) as Hbound; lia]).
Defined.
