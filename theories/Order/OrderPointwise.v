(** * Pointwise maps

    Sparse maps represent assignments with a bottom or top default at absent keys.
    For example, a bottom-default join shares every subtree bound on just one side.
    Builds on: CollectionsMap, OrderConcrete and OrderMonotone. *)

From Stdlib Require Import List Bool PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderMonotone.

(** An absent binding reads as the supplied default. *)
Definition pointwise_lookup {K A} (E : encoding K) (d : A) (m : Map.t K A) (k : K) : A :=
  match Map.get E k m with
  | Some a => a
  | None => d
  end.

Definition map_default {A} (d : A) (o : option A) : A :=
  match o with
  | Some a => a
  | None => d
  end.

Definition map_bot_widen {A} (L : lattice A) (a b : option A) : option A :=
  match a, b with
  | Some a, Some b => Some (widen L a b)
  | Some a, None => Some a
  | None, Some b => Some (widen L (bot L) b)
  | None, None => None
  end.

Definition map_bot_narrow {A} (L : lattice A) (a b : option A) : option A :=
  match a, b with
  | Some a, Some b => Some (narrow L a b)
  | Some a, None => Some a
  | None, _ => None
  end.

(** Bottom-default maps compare bound positions and share one-sided joins. *)
Definition pointwise_lattice {K A} (E : encoding K) (L : lattice A) : lattice (Map.t K A) :=
  {| leb := Map.forall2 (fun a b => leb L a (map_default (bot L) b));
     bot := Map.empty;
     join := Map.union_with (join L);
     widen := Map.combine E (map_bot_widen L);
     narrow := Map.combine E (map_bot_narrow L) |}.

(** Pointwise concretisation interprets each key using the bottom default. *)
Definition pointwise_gamma {K A V} (E : encoding K) (L : lattice A)
  (G : concretisation A V) : concretisation (Map.t K A) (K -> V) :=
  {| gamma := fun m s => forall k, gamma G (pointwise_lookup E (bot L) m k) (s k) |}.

(** Pointwise agreement interprets each key using the bottom default. *)
Definition pointwise_agree {K A V} (E : encoding K) (L : lattice A)
  (R : agreement A V) : agreement (Map.t K A) (K -> V) :=
  {| agree := fun m x y => forall k,
       agree R (pointwise_lookup E (bot L) m k) (x k) (y k) |}.

Definition map_top_combine {A} (f : A -> A -> A) (a b : option A) : option A :=
  match a, b with
  | Some a, Some b => Some (f a b)
  | _, _ => None
  end.

Definition map_top_narrow {A} (L : lattice A) (a b : option A) : option A :=
  match a, b with
  | Some a, Some b => Some (narrow L a b)
  | Some a, None => Some a
  | None, Some b => Some b
  | None, None => None
  end.

Definition map_top_leb {K A} (L : lattice A) (T : top L) (a b : Map.t K A) : bool :=
  Map.forall2 (fun b a => leb L (map_default (top_value T) a) b) b a.

(** Top-default maps have an explicit unreachable bottom and intersect supports on join. *)
Definition pointwise_top_lattice {K A} (E : encoding K) (L : lattice A) (T : top L) :
  lattice (option (Map.t K A)) :=
  {| leb := fun a b =>
       match a, b with
       | None, _ => true
       | Some _, None => false
       | Some a, Some b => map_top_leb L T a b
       end;
     bot := None;
     join := fun a b =>
       match a, b with
       | None, _ => b
       | _, None => a
       | Some a, Some b => Some (Map.combine E (map_top_combine (join L)) a b)
       end;
     widen := fun a b =>
       match a, b with
       | None, _ => b
       | _, None => a
       | Some a, Some b => Some (Map.combine E (map_top_combine (widen L)) a b)
       end;
     narrow := fun a b =>
       match a, b with
       | None, _ => None
       | _, None => a
       | Some a, Some b => Some (Map.combine E (map_top_narrow L) a b)
       end |}.

(** Top-default meanings interpret missing keys as top and explicit bottom as empty. *)
Definition pointwise_top_gamma {K A V} (E : encoding K) (L : lattice A) (T : top L)
  (G : concretisation A V) : concretisation (option (Map.t K A)) (K -> V) :=
  {| gamma := fun m s =>
       match m with
       | None => False
       | Some m => forall k, gamma G (pointwise_lookup E (top_value T) m k) (s k)
       end |}.

Section PositionLaws.
Context {K A : Type} (E : encoding K) (L : lattice A).

Lemma pointwise_leb_code (laws : lattice_laws L) (a b : Map.t K A) :
  leb (pointwise_lattice E L) a b = true <-> forall p,
  leb L (map_default (bot L) (Map.code_get p a))
    (map_default (bot L) (Map.code_get p b)) = true.
Proof.
  cbn [pointwise_lattice leb]; rewrite Map.forall2_spec; split.
  - intros Hab p; destruct (Map.code_get p a) as [x|] eqn:Ha; cbn.
    + apply (Hab p x Ha).
    + apply (bot_least laws).
  - intros Hab p x Ha; specialize (Hab p); rewrite Ha in Hab; exact Hab.
Qed.

Lemma pointwise_join_code (a b : Map.t K A) p :
  Map.code_get p (join (pointwise_lattice E L) a b) =
  Trie.union_opt (join L) (Map.code_get p a) (Map.code_get p b).
Proof.
  apply Map.code_get_union_with.
Qed.

Lemma pointwise_widen_code (a b : Map.t K A) p :
  Map.code_get p (widen (pointwise_lattice E L) a b) =
  map_bot_widen L (Map.code_get p a) (Map.code_get p b).
Proof.
  apply Map.code_get_combine; reflexivity.
Qed.

Lemma pointwise_narrow_code (a b : Map.t K A) p :
  Map.code_get p (narrow (pointwise_lattice E L) a b) =
  map_bot_narrow L (Map.code_get p a) (Map.code_get p b).
Proof.
  apply Map.code_get_combine; reflexivity.
Qed.

(** All raw maps satisfy the weak laws when the value lattice does. *)
Theorem pointwise_laws : lattice_laws L -> lattice_laws (pointwise_lattice E L).
Proof.
  intro laws; constructor.
  - intro a; apply (pointwise_leb_code laws); intro p; apply (leb_refl laws).
  - intros a b c Hab Hbc.
    rewrite (pointwise_leb_code laws a b) in Hab.
    rewrite (pointwise_leb_code laws b c) in Hbc.
    apply (pointwise_leb_code laws); intro p; eapply (leb_trans laws); [apply Hab | apply Hbc].
  - intro a; apply (pointwise_leb_code laws); intro p.
    change (leb L (map_default (bot L) (Map.code_get p (@Map.empty K A)))
      (map_default (bot L) (Map.code_get p a)) = true).
    rewrite Map.code_get_empty.
    apply (bot_least laws).
  - intros a b; apply (pointwise_leb_code laws); intro p; rewrite pointwise_join_code.
    destruct (Map.code_get p a), (Map.code_get p b); cbn [Trie.union_opt map_default];
      first [apply (join_upper_l laws) | apply (leb_refl laws) | apply (bot_least laws)].
  - intros a b; apply (pointwise_leb_code laws); intro p; rewrite pointwise_join_code.
    destruct (Map.code_get p a), (Map.code_get p b); cbn [Trie.union_opt map_default];
      first [apply (join_upper_r laws) | apply (leb_refl laws) | apply (bot_least laws)].
  - intros a b; apply (pointwise_leb_code laws); intro p; rewrite pointwise_widen_code.
    destruct (Map.code_get p a), (Map.code_get p b); cbn [map_bot_widen map_default];
      first [apply (widen_upper_l laws) | apply (leb_refl laws) | apply (bot_least laws)].
  - intros a b; apply (pointwise_leb_code laws); intro p; rewrite pointwise_widen_code.
    destruct (Map.code_get p a), (Map.code_get p b); cbn [map_bot_widen map_default];
      first [apply (widen_upper_r laws) | apply (leb_refl laws) | apply (bot_least laws)].
  - intros a b Hba; rewrite (pointwise_leb_code laws b a) in Hba.
    apply (pointwise_leb_code laws); intro p; rewrite pointwise_narrow_code.
    specialize (Hba p); destruct (Map.code_get p a), (Map.code_get p b);
      cbn [map_bot_narrow map_default] in *;
      first [apply (narrow_lower laws); exact Hba | apply (leb_refl laws)].
  - intros a b Hba; rewrite (pointwise_leb_code laws b a) in Hba.
    apply (pointwise_leb_code laws); intro p; rewrite pointwise_narrow_code.
    specialize (Hba p); destruct (Map.code_get p a), (Map.code_get p b);
      cbn [map_bot_narrow map_default] in *;
      first [apply (narrow_upper laws); exact Hba | exact Hba].
Qed.

(** Pointwise joins are least upper bounds when the value joins are. *)
Theorem pointwise_lub : lattice_laws L -> lub_laws L -> lub_laws (pointwise_lattice E L).
Proof.
  intros laws lub; constructor; intros a b c Ha Hb.
  rewrite (pointwise_leb_code laws a c) in Ha.
  rewrite (pointwise_leb_code laws b c) in Hb; apply (pointwise_leb_code laws).
  intro p; rewrite pointwise_join_code; specialize (Ha p); specialize (Hb p).
  destruct (Map.code_get p a), (Map.code_get p b); cbn [Trie.union_opt map_default] in *;
    first [apply (join_least lub); assumption | exact Ha | exact Hb].
Qed.

(** Reading a raw key preserves the pointwise order. *)
Theorem monotone_pointwise_lookup : lattice_laws L -> forall k : K,
  monotone_fun (pointwise_lattice E L) L (fun m => pointwise_lookup E (bot L) m k).
Proof.
  intros laws k a b Hab.
  rewrite (pointwise_leb_code laws a b) in Hab; apply (Hab (encode E k)).
Qed.
End PositionLaws.

Section MeaningLaws.
Context {K A V : Type} (E : encoding K) (L : lattice A) (T : top L)
  (G : concretisation A V) (R : agreement A V).

(** Pointwise interpretation preserves monotonicity of meanings. *)
Theorem pointwise_gamma_laws : lattice_laws L -> concretisation_laws L G ->
  concretisation_laws (pointwise_lattice E L) (pointwise_gamma E L G).
Proof.
  intros laws HG; constructor; intros a b s Hab Hs k.
  eapply (gamma_monotone HG); [eapply monotone_pointwise_lookup; eassumption | apply Hs].
Qed.

(** Pointwise agreement preserves reflexivity and antitonicity. *)
Theorem pointwise_agree_laws : lattice_laws L -> agreement_laws L R ->
  agreement_laws (pointwise_lattice E L) (pointwise_agree E L R).
Proof.
  intros laws HR; constructor.
  - intros a s k; apply (agree_refl HR).
  - intros a b x y Hab Hxy k; eapply (agree_antitone HR).
    + eapply monotone_pointwise_lookup; eassumption.
    + apply Hxy.
Qed.

(** An empty map needs nothing if value-bottom needs nothing. *)
Theorem pointwise_agree_bot : agreement_bot L R ->
  agreement_bot (pointwise_lattice E L) (pointwise_agree E L R).
Proof.
  intro HR; constructor; intros x y k.
  change (agree R (map_default (bot L) (Map.get E k (@Map.empty K A))) (x k) (y k)).
  rewrite Map.get_empty.
  apply (agree_bot HR).
Qed.

(** Agreement on both maps suffices for agreement on their shared join. *)
Theorem pointwise_agree_join : lattice_laws L -> agreement_laws L R -> agreement_bot L R ->
  agreement_join_law L R -> agreement_join_law (pointwise_lattice E L) (pointwise_agree E L R).
Proof.
  intros laws HR Hbot Hjoin; constructor; intros a b x y Ha Hb k.
  specialize (Ha k); specialize (Hb k).
  unfold pointwise_lookup, Map.get in *; rewrite pointwise_join_code.
  destruct (Map.code_get (encode E k) a), (Map.code_get (encode E k) b);
    cbn [Trie.union_opt] in *; try assumption; apply (agree_join Hjoin); assumption.
Qed.
End MeaningLaws.

Section TopPositionLaws.
Context {K A : Type} (E : encoding K) (L : lattice A) (T : top L).

Lemma map_top_leb_code (a b : Map.t K A) : map_top_leb L T a b = true <-> forall p,
  leb L (map_default (top_value T) (Map.code_get p a))
    (map_default (top_value T) (Map.code_get p b)) = true.
Proof.
  unfold map_top_leb; rewrite Map.forall2_spec; split.
  - intros Hab p; destruct (Map.code_get p b) as [y|] eqn:Hb; cbn.
    + apply (Hab p y Hb).
    + apply (top_greatest T).
  - intros Hab p y Hb; specialize (Hab p); rewrite Hb in Hab; exact Hab.
Qed.

Lemma map_top_refl (laws : lattice_laws L) (a : Map.t K A) : map_top_leb L T a a = true.
Proof.
  apply map_top_leb_code; intro p; apply (leb_refl laws).
Qed.

Lemma map_top_upper (laws : lattice_laws L) (f : A -> A -> A)
  (Hl : forall a b, leb L a (f a b) = true)
  (Hr : forall a b, leb L b (f a b) = true) (a b : Map.t K A) :
  map_top_leb L T a (Map.combine E (map_top_combine f) a b) = true /\
  map_top_leb L T b (Map.combine E (map_top_combine f) a b) = true.
Proof.
  split; apply map_top_leb_code; intro p;
    rewrite Map.code_get_combine by reflexivity;
    destruct (Map.code_get p a), (Map.code_get p b); cbn [map_top_combine map_default];
    first [apply Hl | apply Hr | apply (top_greatest T)].
Qed.

(** Top-default maps with explicit bottom satisfy the weak lattice laws. *)
Theorem pointwise_top_laws : lattice_laws L -> lattice_laws (pointwise_top_lattice E L T).
Proof.
  intro laws; constructor.
  - intros [a|]; cbn; [apply map_top_refl; exact laws | reflexivity].
  - intros [a|] [b|] [c|]; cbn; intros Hab Hbc;
      try discriminate; try reflexivity.
    rewrite map_top_leb_code in Hab, Hbc; apply map_top_leb_code; intro p.
    eapply (leb_trans laws); [apply Hab | apply Hbc].
  - intros [a|]; reflexivity.
  - intros [a|] [b|]; cbn; try reflexivity; try (apply map_top_refl; exact laws).
    exact (proj1 (map_top_upper laws _ (join_upper_l laws) (join_upper_r laws) a b)).
  - intros [a|] [b|]; cbn; try reflexivity; try (apply map_top_refl; exact laws).
    exact (proj2 (map_top_upper laws _ (join_upper_l laws) (join_upper_r laws) a b)).
  - intros [a|] [b|]; cbn; try reflexivity; try (apply map_top_refl; exact laws).
    exact (proj1 (map_top_upper laws _ (widen_upper_l laws) (widen_upper_r laws) a b)).
  - intros [a|] [b|]; cbn; try reflexivity; try (apply map_top_refl; exact laws).
    exact (proj2 (map_top_upper laws _ (widen_upper_l laws) (widen_upper_r laws) a b)).
  - intros [a|] [b|]; cbn; intro Hba; try reflexivity;
      try (apply map_top_refl; exact laws).
    rewrite map_top_leb_code in Hba; apply map_top_leb_code; intro p.
    rewrite Map.code_get_combine by reflexivity; specialize (Hba p).
    destruct (Map.code_get p a), (Map.code_get p b);
      cbn [map_top_narrow map_default] in *;
      first [apply (narrow_lower laws); exact Hba |
        apply (leb_refl laws) | apply (top_greatest T)].
  - intros [a|] [b|]; cbn; intro Hba; try discriminate; try reflexivity.
    rewrite map_top_leb_code in Hba; apply map_top_leb_code; intro p.
    rewrite Map.code_get_combine by reflexivity; specialize (Hba p).
    destruct (Map.code_get p a), (Map.code_get p b);
      cbn [map_top_narrow map_default] in *;
      first [apply (narrow_upper laws); exact Hba | exact Hba | apply (leb_refl laws)].
Qed.

(** Top-default joins are least upper bounds when value joins are. *)
Theorem pointwise_top_lub : lattice_laws L -> lub_laws L ->
  lub_laws (pointwise_top_lattice E L T).
Proof.
  intros laws lub; constructor; intros [a|] [b|] [c|]; cbn;
    intros Ha Hb; try discriminate; try reflexivity; try assumption.
  rewrite map_top_leb_code in Ha, Hb; apply map_top_leb_code; intro p.
  rewrite Map.code_get_combine by reflexivity; specialize (Ha p); specialize (Hb p).
  destruct (Map.code_get p a), (Map.code_get p b);
    cbn [map_top_combine map_default] in *;
    first [apply (join_least lub); assumption | exact Ha | exact Hb].
Qed.
End TopPositionLaws.

Section TopMeaningLaws.
Context {K A V : Type} (E : encoding K) (L : lattice A) (T : top L)
  (G : concretisation A V).

(** Top-default concretisation is monotone. *)
Theorem pointwise_top_gamma_laws : lattice_laws L -> concretisation_laws L G -> top_full T G ->
  concretisation_laws (pointwise_top_lattice E L T) (pointwise_top_gamma E L T G).
Proof.
  intros laws HG Htop; constructor; intros [a|] [b|] s Hab Hs; cbn in *;
    try contradiction; try discriminate.
  rewrite map_top_leb_code in Hab; intro k.
  eapply (gamma_monotone HG); [apply (Hab (encode E k)) | apply Hs].
Qed.

(** Explicit bottom has empty concrete meaning. *)
Theorem pointwise_top_gamma_bot_empty :
  bottom_empty (pointwise_top_lattice E L T) (pointwise_top_gamma E L T G).
Proof.
  constructor; intros s Hs; exact Hs.
Qed.
End TopMeaningLaws.

(** A finite map is well formed and has no bindings outside its universe. *)
Definition within_map {K A} (E : encoding K) (U : list K) (m : Map.t K A) : Prop :=
  Map.wf E m /\ forall k, Map.get E k m <> None -> In k U.

(** Finite maps carry erased support evidence. *)
Definition finite_map {K} (E : encoding K) (U : list K) (A : Type) : Type :=
  { m : Map.t K A | within_map E U m }.

Lemma within_map_empty {K A} (E : encoding K) (U : list K) :
  within_map E U (@Map.empty K A).
Proof.
  split; [apply Map.wf_empty | intros k Hk; rewrite Map.get_empty in Hk; contradiction].
Qed.

Lemma within_map_combine {K A} (E : encoding K) (U : list K)
  (f : option A -> option A -> option A) (Hnone : f None None = None) (a b : Map.t K A) :
  within_map E U a -> within_map E U b -> within_map E U (Map.combine E f a b).
Proof.
  intros [Hwa Ha] [Hwb Hb]; split.
  - apply Map.wf_combine; assumption.
  - intros k Hk; rewrite Map.get_combine in Hk by exact Hnone.
    destruct (Map.get E k a) eqn:HgetA.
    + apply Ha; congruence.
    + destruct (Map.get E k b) eqn:HgetB.
      * apply Hb; congruence.
      * rewrite Hnone in Hk; contradiction.
Qed.

Lemma within_map_union {K A} (E : encoding K) (U : list K) (f : A -> A -> A)
  (a b : Map.t K A) :
  within_map E U a -> within_map E U b -> within_map E U (Map.union_with f a b).
Proof.
  intros [Hwa Ha] [Hwb Hb]; split.
  - apply Map.wf_union_with; assumption.
  - intros k Hk; unfold Map.get in Hk; rewrite Map.code_get_union_with in Hk.
    destruct (Map.get E k a) eqn:HgetA.
    + apply Ha; congruence.
    + destruct (Map.get E k b) eqn:HgetB.
      * apply Hb; congruence.
      * change (Map.code_get (encode E k) a = None) in HgetA.
        change (Map.code_get (encode E k) b = None) in HgetB.
        rewrite HgetA, HgetB in Hk; contradiction.
Qed.

Definition finite_map_combine {K A} (E : encoding K) (U : list K)
  (f : option A -> option A -> option A) (Hnone : f None None = None)
  (a b : finite_map E U A) : finite_map E U A :=
  exist _ (Map.combine E f (proj1_sig a) (proj1_sig b))
    (within_map_combine E U f Hnone _ _ (proj2_sig a) (proj2_sig b)).

Definition finite_map_union {K A} (E : encoding K) (U : list K) (f : A -> A -> A)
  (a b : finite_map E U A) : finite_map E U A :=
  exist _ (Map.union_with f (proj1_sig a) (proj1_sig b))
    (within_map_union E U f _ _ (proj2_sig a) (proj2_sig b)).

(** Finite bottom-default maps use the raw operations with preserved support evidence. *)
Definition finite_pointwise_lattice {K A} (E : encoding K) (U : list K) (L : lattice A) :
  lattice (finite_map E U A) :=
  {| leb := fun a b => leb (pointwise_lattice E L) (proj1_sig a) (proj1_sig b);
     bot := exist _ Map.empty (within_map_empty E U);
     join := finite_map_union E U (join L);
     widen := finite_map_combine E U (map_bot_widen L) eq_refl;
     narrow := finite_map_combine E U (map_bot_narrow L) eq_refl |}.

(** Finite map meanings pull back from raw bottom-default maps. *)
Definition finite_pointwise_gamma {K A V} (E : encoding K) (U : list K) (L : lattice A)
  (G : concretisation A V) : concretisation (finite_map E U A) (K -> V) :=
  comap_gamma (@proj1_sig _ _) (pointwise_gamma E L G).

(** Finite map agreement pulls back from raw bottom-default maps. *)
Definition finite_pointwise_agree {K A V} (E : encoding K) (U : list K) (L : lattice A)
  (R : agreement A V) : agreement (finite_map E U A) (K -> V) :=
  comap_agree (@proj1_sig _ _) (pointwise_agree E L R).

(** Finite top-default operations preserve the explicit unreachable bottom. *)
Definition finite_pointwise_top_lattice {K A} (E : encoding K) (U : list K) (L : lattice A)
  (T : top L) : lattice (option (finite_map E U A)) :=
  {| leb := fun a b => leb (pointwise_top_lattice E L T)
       (option_map (@proj1_sig _ _) a) (option_map (@proj1_sig _ _) b);
     bot := None;
     join := fun a b =>
       match a, b with
       | None, _ => b
       | _, None => a
       | Some a, Some b => Some (finite_map_combine E U (map_top_combine (join L)) eq_refl a b)
       end;
     widen := fun a b =>
       match a, b with
       | None, _ => b
       | _, None => a
       | Some a, Some b => Some (finite_map_combine E U (map_top_combine (widen L)) eq_refl a b)
       end;
     narrow := fun a b =>
       match a, b with
       | None, _ => None
       | _, None => a
       | Some a, Some b => Some (finite_map_combine E U (map_top_narrow L) eq_refl a b)
       end |}.

Section FiniteLaws.
Context {K A : Type} (E : encoding K) (U : list K) (L : lattice A) (T : top L).

(** Forgetting finite support preserves raw bottom-default comparison exactly. *)
Theorem finite_pointwise_embedding :
  order_embedding (pointwise_lattice E L) (finite_pointwise_lattice E U L) (@proj1_sig _ _).
Proof.
  intros a b; reflexivity.
Qed.

(** Finite bottom-default maps inherit the raw weak lattice laws. *)
Theorem finite_pointwise_laws : lattice_laws L -> lattice_laws (finite_pointwise_lattice E U L).
Proof.
  intro laws; pose proof (pointwise_laws E L laws) as Hraw; constructor.
  - intros a; apply (leb_refl Hraw).
  - intros a b c; apply (leb_trans Hraw).
  - intros a; apply (bot_least Hraw).
  - intros a b; apply (join_upper_l Hraw).
  - intros a b; apply (join_upper_r Hraw).
  - intros a b; apply (widen_upper_l Hraw).
  - intros a b; apply (widen_upper_r Hraw).
  - intros a b; apply (narrow_lower Hraw).
  - intros a b; apply (narrow_upper Hraw).
Qed.

(** Finite bottom-default joins remain least upper bounds. *)
Theorem finite_pointwise_lub : lattice_laws L -> lub_laws L ->
  lub_laws (finite_pointwise_lattice E U L).
Proof.
  intros laws lub; constructor; intros a b c; apply (join_least (pointwise_lub E L laws lub)).
Qed.

(** Reading a finite map is monotone. *)
Theorem monotone_finite_pointwise_lookup : lattice_laws L -> forall k : K,
  monotone_fun (finite_pointwise_lattice E U L) L
    (fun m => pointwise_lookup E (bot L) (proj1_sig m) k).
Proof.
  intros laws k a b; apply (monotone_pointwise_lookup E L laws k).
Qed.

(** Forgetting finite support preserves raw top-default comparison exactly. *)
Theorem finite_pointwise_top_embedding : order_embedding (pointwise_top_lattice E L T)
  (finite_pointwise_top_lattice E U L T) (option_map (@proj1_sig _ _)).
Proof.
  intros a b; reflexivity.
Qed.

Lemma finite_top_join_image (a b : option (finite_map E U A)) :
  option_map (@proj1_sig _ _) (join (finite_pointwise_top_lattice E U L T) a b) =
  join (pointwise_top_lattice E L T)
    (option_map (@proj1_sig _ _) a) (option_map (@proj1_sig _ _) b).
Proof.
  destruct a, b; reflexivity.
Qed.

Lemma finite_top_widen_image (a b : option (finite_map E U A)) :
  option_map (@proj1_sig _ _) (widen (finite_pointwise_top_lattice E U L T) a b) =
  widen (pointwise_top_lattice E L T)
    (option_map (@proj1_sig _ _) a) (option_map (@proj1_sig _ _) b).
Proof.
  destruct a, b; reflexivity.
Qed.

Lemma finite_top_narrow_image (a b : option (finite_map E U A)) :
  option_map (@proj1_sig _ _) (narrow (finite_pointwise_top_lattice E U L T) a b) =
  narrow (pointwise_top_lattice E L T)
    (option_map (@proj1_sig _ _) a) (option_map (@proj1_sig _ _) b).
Proof.
  destruct a, b; reflexivity.
Qed.

(** Finite top-default maps inherit the raw weak lattice laws. *)
Theorem finite_pointwise_top_laws : lattice_laws L ->
  lattice_laws (finite_pointwise_top_lattice E U L T).
Proof.
  intro laws; pose proof (pointwise_top_laws E L T laws) as Hraw; constructor.
  - intro a; apply (leb_refl Hraw).
  - intros a b c; apply (leb_trans Hraw).
  - intro a; apply (bot_least Hraw).
  - intros a b; unfold leb at 1; cbn [finite_pointwise_top_lattice].
    rewrite finite_top_join_image; apply (join_upper_l Hraw).
  - intros a b; unfold leb at 1; cbn [finite_pointwise_top_lattice].
    rewrite finite_top_join_image; apply (join_upper_r Hraw).
  - intros a b; unfold leb at 1; cbn [finite_pointwise_top_lattice].
    rewrite finite_top_widen_image; apply (widen_upper_l Hraw).
  - intros a b; unfold leb at 1; cbn [finite_pointwise_top_lattice].
    rewrite finite_top_widen_image; apply (widen_upper_r Hraw).
  - intros a b Hba; unfold leb at 1; cbn [finite_pointwise_top_lattice].
    rewrite finite_top_narrow_image; apply (narrow_lower Hraw); exact Hba.
  - intros a b Hba; unfold leb at 1; cbn [finite_pointwise_top_lattice].
    rewrite finite_top_narrow_image; apply (narrow_upper Hraw); exact Hba.
Qed.

(** Finite top-default joins remain least upper bounds. *)
Theorem finite_pointwise_top_lub : lattice_laws L -> lub_laws L ->
  lub_laws (finite_pointwise_top_lattice E U L T).
Proof.
  intros laws lub; constructor; intros a b c Ha Hb.
  change (leb (pointwise_top_lattice E L T)
    (option_map (@proj1_sig _ _) (join (finite_pointwise_top_lattice E U L T) a b))
    (option_map (@proj1_sig _ _) c) = true).
  rewrite finite_top_join_image; apply (join_least (pointwise_top_lub E L T laws lub)); assumption.
Qed.
End FiniteLaws.

Section FiniteMeaningLaws.
Context {K A V : Type} (E : encoding K) (U : list K) (L : lattice A)
  (G : concretisation A V) (R : agreement A V).

(** Finite bottom-default meanings remain monotone. *)
Theorem finite_pointwise_gamma_laws : lattice_laws L -> concretisation_laws L G ->
  concretisation_laws (finite_pointwise_lattice E U L) (finite_pointwise_gamma E U L G).
Proof.
  intros laws HG; eapply comap_gamma_laws.
  - apply finite_pointwise_embedding.
  - apply pointwise_gamma_laws; assumption.
Qed.

(** Finite bottom-default agreement remains reflexive and antitone. *)
Theorem finite_pointwise_agree_laws : lattice_laws L -> agreement_laws L R ->
  agreement_laws (finite_pointwise_lattice E U L) (finite_pointwise_agree E U L R).
Proof.
  intros laws HR; eapply comap_agree_laws.
  - apply finite_pointwise_embedding.
  - apply pointwise_agree_laws; assumption.
Qed.
End FiniteMeaningLaws.

Definition map_rebuild {K A} (E : encoding K) (U : list K) (f : K -> option A) : Map.t K A :=
  fold_right (fun k m =>
    match f k with
    | Some a => Map.set E k a m
    | None => m
    end) Map.empty U.

Lemma map_rebuild_wf {K A} (E : encoding K) (U : list K) (f : K -> option A) :
  Map.wf E (map_rebuild E U f).
Proof.
  induction U as [|k U IH]; cbn [map_rebuild fold_right].
  - apply Map.wf_empty.
  - destruct (f k); [apply Map.wf_set |]; exact IH.
Qed.

Definition encoded_eq_dec {K} (E : encoding K) (x y : K) : {x = y} + {x <> y} :=
  match Pos.eq_dec (encode E x) (encode E y) with
  | left Heq => left (encode_injective E x y Heq)
  | right Hne => right (fun Heq => Hne (f_equal (encode E) Heq))
  end.

Lemma map_rebuild_get {K A} (E : encoding K) (U : list K) (f : K -> option A) k :
  Map.get E k (map_rebuild E U f) =
  if in_dec (encoded_eq_dec E) k U then f k else None.
Proof.
  induction U as [|a U IH].
  - change (Map.get E k (@Map.empty K A) = None); apply Map.get_empty.
  - change (Map.get E k
      (match f a with Some x => Map.set E a x (map_rebuild E U f)
       | None => map_rebuild E U f end) =
      if in_dec (encoded_eq_dec E) k (a :: U) then f k else None).
    destruct (encoded_eq_dec E k a) as [Heq | Hka].
    + subst a.
      destruct (f k) eqn:Hvalue.
      * rewrite Map.get_set_same; destruct (in_dec (encoded_eq_dec E) k (k :: U))
          as [Hin | Hout]; [reflexivity | exfalso; apply Hout; left; reflexivity].
      * rewrite IH; destruct (in_dec (encoded_eq_dec E) k U);
          destruct (in_dec (encoded_eq_dec E) k (k :: U)); try rewrite Hvalue; reflexivity.
    + destruct (f a); [rewrite Map.get_set_other by exact Hka |]; rewrite IH;
        destruct (in_dec (encoded_eq_dec E) k U) as [Hin | Hout];
        destruct (in_dec (encoded_eq_dec E) k (a :: U)) as [Hin' | Hout'];
        try reflexivity.
      * exfalso; apply Hout'; right; exact Hin.
      * exfalso; destruct Hin' as [Heq | Hin].
        -- apply Hka; symmetry; exact Heq.
        -- apply Hout; exact Hin.
      * exfalso; apply Hout'; right; exact Hin.
      * exfalso; destruct Hin' as [Heq | Hin].
        -- apply Hka; symmetry; exact Heq.
        -- apply Hout; exact Hin.
Qed.

Lemma map_rebuild_in {K A} (E : encoding K) (U : list K) (f : K -> option A) k :
  In k U -> Map.get E k (map_rebuild E U f) = f k.
Proof.
  intro Hin; rewrite map_rebuild_get; destruct (in_dec (encoded_eq_dec E) k U);
    [reflexivity | contradiction].
Qed.

Lemma map_rebuild_out {K A} (E : encoding K) (U : list K) (f : K -> option A) k :
  ~ In k U -> Map.get E k (map_rebuild E U f) = None.
Proof.
  intro Hout; rewrite map_rebuild_get; destruct (in_dec (encoded_eq_dec E) k U);
    [contradiction | reflexivity].
Qed.

Lemma map_rebuild_within {K A} (E : encoding K) (U : list K) (f : K -> option A) :
  within_map E U (map_rebuild E U f).
Proof.
  split; [apply map_rebuild_wf | intros k Hget].
  destruct (in_dec (encoded_eq_dec E) k U) as [Hin | Hout]; [exact Hin |].
  rewrite map_rebuild_out in Hget by exact Hout; contradiction.
Qed.

(** Clamping rebuilds bindings by key lookups over the universe. *)
Definition finite_map_clamp {K A} (E : encoding K) (U : list K) (m : Map.t K A) :
  finite_map E U A :=
  exist _ (map_rebuild E U (fun k => Map.get E k m)) (map_rebuild_within E U _).

(** Clamping preserves the lookup at every key in the universe. *)
Theorem finite_map_clamp_get {K A} (E : encoding K) (U : list K) :
  forall (m : Map.t K A) (k : K), In k U ->
  Map.get E k (proj1_sig (finite_map_clamp E U m)) = Map.get E k m.
Proof.
  intros m k Hin; exact (map_rebuild_in E U (fun x => Map.get E x m) k Hin).
Qed.

Lemma finite_map_out {K A} (E : encoding K) (U : list K) (m : finite_map E U A) k :
  ~ In k U -> Map.get E k (proj1_sig m) = None.
Proof.
  intros Hout; destruct (Map.get E k (proj1_sig m)) eqn:Hget; [|reflexivity].
  exfalso; apply Hout, (proj2 (proj2_sig m)); congruence.
Qed.

Lemma map_code_key {K A} (E : encoding K) (m : Map.t K A) p a :
  Map.wf E m -> Map.code_get p m = Some a -> exists k, encode E k = p.
Proof.
  intros Hwf; unfold Map.code_get.
  destruct (Trie.get p m) as [[k b]|] eqn:Hget; cbn; intro Ha; try discriminate.
  exists k; eapply Hwf; exact Hget.
Qed.

(** Binding each universe key to value-top gives the greatest finite bottom-default map. *)
Definition finite_pointwise_top {K A} {L : lattice A} (E : encoding K) (U : list K)
  (T : top L) : top (finite_pointwise_lattice E U L).
Proof.
  refine {| top_value := exist _ (map_rebuild E U (fun _ => Some (top_value T)))
    (map_rebuild_within E U _) |}.
  abstract (intros [m [Hwf Hin]]; cbn [finite_pointwise_lattice leb];
    apply Map.forall2_spec; intros p a Hget; cbn [proj1_sig] in Hget;
    destruct (map_code_key E m p a Hwf Hget) as [k Hcode]; subst p;
    assert (Hkin : In k U) by (apply Hin; change (Map.code_get (encode E k) m <> None);
      rewrite Hget; discriminate);
    change (leb L a (map_default (bot L)
      (Map.get E k (map_rebuild E U (fun _ => Some (top_value T))))) = true);
    rewrite map_rebuild_in by exact Hkin; apply (top_greatest T)).
Defined.

Definition key_sum {K} (f : K -> nat) (U : list K) : nat :=
  fold_right (fun k n => f k + n) 0 U.

Lemma key_sum_le {K} (U : list K) (f g : K -> nat) :
  (forall k, In k U -> f k <= g k) -> key_sum f U <= key_sum g U.
Proof.
  intro Hle; induction U as [|k U IH]; [reflexivity |].
  change (f k + key_sum f U <= g k + key_sum g U).
  assert (Hhead : f k <= g k) by (apply Hle; left; reflexivity).
  assert (Htail : key_sum f U <= key_sum g U) by
    (apply IH; intros a Ha; apply Hle; right; exact Ha).
  lia.
Qed.

Lemma key_sum_lt {K} (U : list K) (f g : K -> nat) :
  (forall k, In k U -> f k <= g k) ->
  (exists k, In k U /\ f k < g k) -> key_sum f U < key_sum g U.
Proof.
  intros Hle Hstrict; induction U as [|a U IH].
  - destruct Hstrict as [k [Hin Hk]]; contradiction.
  - change (f a + key_sum f U < g a + key_sum g U).
    assert (Hhead : f a <= g a) by (apply Hle; left; reflexivity).
    assert (Htail : key_sum f U <= key_sum g U) by
      (apply key_sum_le; intros k Hk; apply Hle; right; exact Hk).
    destruct Hstrict as [k [[Heq | Hin] Hk]].
    + subst k; lia.
    + assert (HtailStrict : key_sum f U < key_sum g U).
      { apply IH.
        - intros x Hx; apply Hle; right; exact Hx.
        - exists k; split; assumption. }
      lia.
Qed.

Lemma key_sum_bound {K} (U : list K) (f : K -> nat) n :
  (forall k, f k <= n) -> key_sum f U <= length U * n.
Proof.
  intro Hbound; induction U as [|k U IH]; [reflexivity |].
  change (f k + key_sum f U <= n + length U * n).
  specialize (Hbound k); lia.
Qed.

Lemma forallb_false_member {K} (f : K -> bool) (U : list K) :
  forallb f U = false -> exists k, In k U /\ f k = false.
Proof.
  induction U as [|k U IH]; cbn; intro Hfalse; [discriminate |].
  destruct (f k) eqn:Hk.
  - destruct (IH Hfalse) as [a [Hin Ha]]; exists a; split; [right |]; assumption.
  - exists k; split; [left; reflexivity | exact Hk].
Qed.

Lemma finite_map_forall2 {K A} (E : encoding K) (U : list K)
  (r : A -> option A -> bool) (a b : finite_map E U A) :
  Map.forall2 r (proj1_sig a) (proj1_sig b) =
  forallb (fun k =>
    match Map.get E k (proj1_sig a) with
    | Some x => r x (Map.get E k (proj1_sig b))
    | None => true
    end) U.
Proof.
  apply eq_true_iff_eq; rewrite Map.forall2_spec, forallb_forall; split.
  - intros Hrel k Hin; destruct (Map.get E k (proj1_sig a)) as [x|] eqn:Hget;
      [apply (Hrel (encode E k) x Hget) | reflexivity].
  - intros Hrel p x Hget.
    destruct (map_code_key E _ p x (proj1 (proj2_sig a)) Hget) as [k Hcode]; subst p.
    assert (Hin : In k U) by (apply (proj2 (proj2_sig a));
      change (Map.code_get (encode E k) (proj1_sig a) <> None); rewrite Hget; discriminate).
    specialize (Hrel k Hin); change (Map.get E k (proj1_sig a) = Some x) in Hget.
    rewrite Hget in Hrel; exact Hrel.
Qed.

Lemma finite_map_comparison_witness {K A} (E : encoding K) (U : list K) (L : lattice A)
  (a b : finite_map E U A) :
  leb (finite_pointwise_lattice E U L) b a = false ->
  exists k x, In k U /\ Map.get E k (proj1_sig b) = Some x /\
    leb L x (pointwise_lookup E (bot L) (proj1_sig a) k) = false.
Proof.
  intro Hfalse; change (Map.forall2 (fun x y => leb L x (map_default (bot L) y))
    (proj1_sig b) (proj1_sig a) = false) in Hfalse.
  rewrite finite_map_forall2 in Hfalse.
  destruct (forallb_false_member _ _ Hfalse) as [k [Hin Hk]].
  destruct (Map.get E k (proj1_sig b)) as [x|] eqn:Hget; [|discriminate].
  exists k, x; split; [exact Hin |]; split; assumption.
Qed.

Lemma pointwise_join_lookup_upper {K A} (E : encoding K) (L : lattice A)
  (laws : lattice_laws L) (a b : Map.t K A) k :
  leb L (pointwise_lookup E (bot L) a k)
    (pointwise_lookup E (bot L) (join (pointwise_lattice E L) a b) k) = true.
Proof.
  apply (monotone_pointwise_lookup E L laws k); apply (join_upper_l (pointwise_laws E L laws)).
Qed.

Lemma height_strict_order {A} (L : lattice A) (laws : lattice_laws L) (lub : lub_laws L)
  (H : monotone_height L) a b : leb L a b = true -> leb L b a = false ->
  rank (base_height H) a < rank (base_height H) b.
Proof.
  intros Hab Hba.
  assert (Hstrict : leb L (join L a b) a = false).
  { destruct (leb L (join L a b) a) eqn:Hjoin; [|reflexivity].
    pose proof (leb_trans laws _ _ _ (join_upper_r laws a b) Hjoin) as Hcontra; congruence. }
  pose proof (join_rank_grows (base_height H) a b Hstrict) as Hgrow.
  assert (Hjoin : leb L (join L a b) b = true) by
    (apply (join_least lub); [exact Hab | apply (leb_refl laws)]).
  pose proof (rank_monotone H _ _ Hjoin) as Hbound; lia.
Qed.

(** Summing value heights over the universe bounds finite bottom-default maps. *)
Definition finite_pointwise_height {K A} {L : lattice A} (E : encoding K) (U : list K)
  (Hnodup : NoDup U) (laws : lattice_laws L) (lub : lub_laws L) (H : monotone_height L) :
  monotone_height (finite_pointwise_lattice E U L).
Proof.
  set (measure := fun m : finite_map E U A => key_sum
    (fun k => rank (base_height H) (pointwise_lookup E (bot L) (proj1_sig m) k)) U).
  unshelve refine (@MonotoneHeight _ (finite_pointwise_lattice E U L)
    (@Height _ (finite_pointwise_lattice E U L) measure
      (length U * bound (base_height H)) _ _) _).
  - abstract (intro a; apply key_sum_bound; intro k; apply rank_bounded).
  - abstract (intros a b Hstrict; apply key_sum_lt;
      [intros k Hin; apply (rank_monotone H); apply pointwise_join_lookup_upper; exact laws |];
      destruct (finite_map_comparison_witness E U L a
        (join (finite_pointwise_lattice E U L) a b) Hstrict) as [k [x [Hin [Hget Hbad]]]];
      exists k; split; [exact Hin |]; apply (height_strict_order L laws lub H);
      [apply pointwise_join_lookup_upper; exact laws |];
      unfold pointwise_lookup; change (Map.get E k
        (proj1_sig (join (finite_pointwise_lattice E U L) a b)) = Some x) in Hget;
      rewrite Hget; exact Hbad).
  - abstract (intros a b Hab; apply key_sum_le; intros k Hin;
      apply (rank_monotone H); apply (monotone_finite_pointwise_lookup E U L laws k); exact Hab).
Defined.

Lemma map_wrank_nonincreasing {A} (L : lattice A) (W : widening_rank L) a b :
  wrank W (widen L a b) <= wrank W a.
Proof.
  destruct (leb L b a) eqn:Hba.
  - apply (widen_rank_stable W); exact Hba.
  - pose proof (widen_rank_progress W a b Hba) as Hlt; lia.
Qed.

Lemma pointwise_wrank_nonincreasing {K A} (E : encoding K) (L : lattice A)
  (W : widening_rank L) (a b : Map.t K A) k :
  wrank W (pointwise_lookup E (bot L) (widen (pointwise_lattice E L) a b) k) <=
  wrank W (pointwise_lookup E (bot L) a k).
Proof.
  unfold pointwise_lookup, Map.get; rewrite pointwise_widen_code.
  destruct (Map.code_get (encode E k) a), (Map.code_get (encode E k) b);
    cbn [map_bot_widen]; try lia; apply map_wrank_nonincreasing.
Qed.

Lemma pointwise_wrank_progress {K A} (E : encoding K) (L : lattice A)
  (W : widening_rank L) (a b : Map.t K A) k x :
  Map.get E k b = Some x -> leb L x (pointwise_lookup E (bot L) a k) = false ->
  wrank W (pointwise_lookup E (bot L) (widen (pointwise_lattice E L) a b) k) <
  wrank W (pointwise_lookup E (bot L) a k).
Proof.
  unfold pointwise_lookup, Map.get; intros Hget Hbad; rewrite pointwise_widen_code, Hget.
  destruct (Map.code_get (encode E k) a); cbn [map_bot_widen] in *;
    apply (widen_rank_progress W); exact Hbad.
Qed.

(** Summed value widening ranks measure finite bottom-default widening. *)
Definition finite_pointwise_wrank {K A} {L : lattice A} (E : encoding K) (U : list K)
  (Hnodup : NoDup U) (W : bounded_widening_rank L) :
  bounded_widening_rank (finite_pointwise_lattice E U L).
Proof.
  set (measure := fun m : finite_map E U A => key_sum
    (fun k => wrank (base_wrank W) (pointwise_lookup E (bot L) (proj1_sig m) k)) U).
  unshelve refine (@BoundedWideningRank _ (finite_pointwise_lattice E U L)
    (@WideningRank _ (finite_pointwise_lattice E U L) measure _ _)
    (length U * wbound W) _).
  - abstract (intros a b _; apply key_sum_le; intros k Hin; apply pointwise_wrank_nonincreasing).
  - abstract (intros a b Hstrict; apply key_sum_lt;
      [intros k Hin; apply pointwise_wrank_nonincreasing |];
      destruct (finite_map_comparison_witness E U L a b Hstrict)
        as [k [x [Hin [Hget Hbad]]]];
      exists k; split; [exact Hin |]; eapply pointwise_wrank_progress; eassumption).
  - abstract (intro a; apply key_sum_bound; intro k; apply wrank_bounded).
Defined.

(** A reachable empty map is greatest for finite top-default maps. *)
Definition finite_pointwise_top_top {K A} (E : encoding K) (U : list K) (L : lattice A)
  (T : top L) : top (finite_pointwise_top_lattice E U L T).
Proof.
  refine {| top_value := Some (exist _ Map.empty (within_map_empty E U)) |}.
  abstract (intros [m|]; reflexivity).
Defined.

Lemma finite_map_top_witness {K A} (E : encoding K) (U : list K) (L : lattice A) (T : top L)
  (a b : finite_map E U A) : map_top_leb L T (proj1_sig a) (proj1_sig b) = false ->
  exists k y, In k U /\ Map.get E k (proj1_sig b) = Some y /\
    leb L (pointwise_lookup E (top_value T) (proj1_sig a) k) y = false.
Proof.
  unfold map_top_leb; rewrite finite_map_forall2; intro Hfalse.
  destruct (forallb_false_member _ _ Hfalse) as [k [Hin Hk]].
  destruct (Map.get E k (proj1_sig b)) as [y|] eqn:Hget; [|discriminate].
  exists k, y; split; [exact Hin |]; split; assumption.
Qed.

Lemma height_strict_top {A} (L : lattice A) (laws : lattice_laws L) (T : top L)
  (H : monotone_height L) a : leb L (top_value T) a = false ->
  rank (base_height H) a < rank (base_height H) (top_value T).
Proof.
  intro Hbad.
  assert (Hstrict : leb L (join L a (top_value T)) a = false).
  { destruct (leb L (join L a (top_value T)) a) eqn:Hjoin; [|reflexivity].
    pose proof (leb_trans laws _ _ _ (join_upper_r laws a (top_value T)) Hjoin) as Hcontra.
    congruence. }
  pose proof (join_rank_grows (base_height H) a (top_value T) Hstrict) as Hgrow.
  pose proof (rank_monotone H _ _ (top_greatest T (join L a (top_value T)))) as Hbound.
  lia.
Qed.

Lemma map_top_join_lookup_upper {K A} (E : encoding K) (L : lattice A) (T : top L)
  (laws : lattice_laws L) (a b : Map.t K A) k :
  leb L (pointwise_lookup E (top_value T) a k)
    (pointwise_lookup E (top_value T) (Map.combine E (map_top_combine (join L)) a b) k) = true.
Proof.
  pose proof (proj1 (map_top_upper E L T laws _ (join_upper_l laws) (join_upper_r laws) a b))
    as Hupper.
  rewrite map_top_leb_code in Hupper; apply (Hupper (encode E k)).
Qed.

Lemma finite_top_sum_growth {K A} (E : encoding K) (U : list K) (L : lattice A)
  (laws : lattice_laws L) (T : top L) (H : monotone_height L) (a b : finite_map E U A) :
  let j := finite_map_combine E U (map_top_combine (join L)) eq_refl a b in
  map_top_leb L T (proj1_sig j) (proj1_sig a) = false ->
  key_sum (fun k => rank (base_height H) (pointwise_lookup E (top_value T) (proj1_sig a) k)) U <
  key_sum (fun k => rank (base_height H) (pointwise_lookup E (top_value T) (proj1_sig j) k)) U.
Proof.
  intros j Hbad; apply key_sum_lt.
  - intros k Hin; apply (rank_monotone H); apply map_top_join_lookup_upper; exact laws.
  - destruct (finite_map_top_witness E U L T j a Hbad) as [k [x [Hin [Ha Hstrict]]]].
    exists k; split; [exact Hin |].
    unfold pointwise_lookup in *; rewrite Ha in *.
    unfold j, finite_map_combine in Hstrict |- *; cbn [proj1_sig] in Hstrict |- *.
    rewrite Map.get_combine in Hstrict |- * by reflexivity; rewrite Ha in Hstrict |- *.
    destruct (Map.get E k (proj1_sig b)) as [y|] eqn:Hb.
    + apply (join_rank_grows (base_height H)); exact Hstrict.
    + apply (height_strict_top L laws T H); exact Hstrict.
Qed.

(** The explicit bottom and summed key heights bound finite top-default maps. *)
Definition finite_pointwise_top_height {K A} {L : lattice A} (E : encoding K) (U : list K)
  (Hnodup : NoDup U) (laws : lattice_laws L) (T : top L) (H : monotone_height L) :
  monotone_height (finite_pointwise_top_lattice E U L T).
Proof.
  set (sum := fun m : finite_map E U A => key_sum
    (fun k => rank (base_height H) (pointwise_lookup E (top_value T) (proj1_sig m) k)) U).
  set (measure := fun m : option (finite_map E U A) =>
    match m with
    | None => 0
    | Some m => 1 + sum m
    end).
  unshelve refine (@MonotoneHeight _ (finite_pointwise_top_lattice E U L T)
    (@Height _ (finite_pointwise_top_lattice E U L T) measure
      (1 + length U * bound (base_height H)) _ _) _).
  - abstract (intros [a|]; cbn [measure]; [|lia];
      assert (Hsum : sum a <= length U * bound (base_height H)) by
        (apply key_sum_bound; intro k; apply rank_bounded); lia).
  - abstract (intros [a|] [b|] Hbad; cbn [measure] in *;
      [assert (Hsum : sum a < sum (finite_map_combine E U
        (map_top_combine (join L)) eq_refl a b)) by
          (apply (finite_top_sum_growth E U L laws T H); exact Hbad);
       change (1 + sum a < 1 + sum (finite_map_combine E U
         (map_top_combine (join L)) eq_refl a b)); lia |
       pose proof (map_top_refl L T laws (proj1_sig a)) as Hrefl;
       change (map_top_leb L T (proj1_sig a) (proj1_sig a) = false) in Hbad; congruence |
       change (0 < 1 + sum b); lia | discriminate]).
  - abstract (intros a b Hab; change (measure a <= measure b);
      destruct a as [a|], b as [b|]; cbn [measure];
      [assert (Hsum : sum a <= sum b) by
        (apply key_sum_le; intros k Hin; apply (rank_monotone H);
         change (map_top_leb L T (proj1_sig a) (proj1_sig b) = true) in Hab;
         rewrite map_top_leb_code in Hab; apply (Hab (encode E k))); lia |
       discriminate | lia | lia]).
Defined.
