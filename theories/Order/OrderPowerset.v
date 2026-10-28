(** * Powersets and must-facts

    Sets provide may-facts under inclusion and must-facts under reverse inclusion.
    For example, joining must-facts keeps only the facts shared by both inputs.
    Builds on: CollectionsFinSet, OrderConcrete and OrderDual. *)

From Stdlib Require Import List Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderDual.

(** Inclusion, empty and union provide the raw powerset operations. *)
Definition powerset_lattice {K} (E : encoding K) : lattice (FinSet.t K) :=
  {| leb := FinSet.subset E;
     bot := FinSet.empty;
     join := FinSet.union E;
     widen := FinSet.union E;
     narrow := fun a _ => a |}.

(** A may-set denotes its members. *)
Definition powerset_gamma {K} (E : encoding K) : concretisation (FinSet.t K) K :=
  {| gamma := fun s k => FinSet.mem E k s = true |}.

(** A set of needs requires equality at each member. *)
Definition powerset_agree {K V} (E : encoding K) : agreement (FinSet.t K) (K -> V) :=
  {| agree := fun s x y => forall k, FinSet.mem E k s = true -> x k = y k |}.

(** Must-facts have an explicit unreachable bottom and finite conjunctions of facts. *)
Inductive must (K : Type) : Type :=
  | All
  | Only (s : FinSet.t K).

Arguments All {K}.
Arguments Only {K}.

(** Must order reverses inclusion and joins by intersection. *)
Definition must_lattice {K} (E : encoding K) : lattice (must K) :=
  let combine := fun a b =>
    match a, b with
    | All, _ => b
    | _, All => a
    | Only s, Only t => Only (FinSet.inter E s t)
    end in
  {| leb := fun a b =>
       match a, b with
       | All, _ => true
       | Only _, All => false
       | Only s, Only t => FinSet.subset E t s
       end;
     bot := All;
     join := combine;
     widen := combine;
     narrow := fun a _ => a |}.

(** Must meaning requires every represented fact, while bottom means unreachable. *)
Definition must_gamma {K C} (E : encoding K) (holds : K -> C -> Prop) :
  concretisation (must K) C :=
  {| gamma := fun a c =>
       match a with
       | All => False
       | Only s => forall k, FinSet.mem E k s = true -> holds k c
       end |}.

Section RawLaws.
Context {K : Type} (E : encoding K).

Lemma set_subset_refl (s : FinSet.t K) : FinSet.subset E s s = true.
Proof.
  apply FinSet.subset_code; intros p Hmem; exact Hmem.
Qed.

Lemma set_subset_trans (s t u : FinSet.t K) :
  FinSet.subset E s t = true -> FinSet.subset E t u = true ->
  FinSet.subset E s u = true.
Proof.
  repeat rewrite FinSet.subset_code; intros Hst Htu p Hp; apply Htu, Hst, Hp.
Qed.

Lemma set_empty_least (s : FinSet.t K) : FinSet.subset E FinSet.empty s = true.
Proof.
  apply FinSet.subset_code; intros p Hp; unfold FinSet.empty in Hp.
  rewrite Map.code_get_empty in Hp; contradiction.
Qed.

Lemma set_union_left (s t : FinSet.t K) : FinSet.subset E s (FinSet.union E s t) = true.
Proof.
  apply FinSet.subset_code; intros p Hp; apply FinSet.union_code; left; exact Hp.
Qed.

Lemma set_union_right (s t : FinSet.t K) : FinSet.subset E t (FinSet.union E s t) = true.
Proof.
  apply FinSet.subset_code; intros p Hp; apply FinSet.union_code; right; exact Hp.
Qed.

Lemma set_inter_left (s t : FinSet.t K) : FinSet.subset E (FinSet.inter E s t) s = true.
Proof.
  apply FinSet.subset_code; intros p Hp; apply FinSet.inter_code in Hp; exact (proj1 Hp).
Qed.

Lemma set_inter_right (s t : FinSet.t K) : FinSet.subset E (FinSet.inter E s t) t = true.
Proof.
  apply FinSet.subset_code; intros p Hp; apply FinSet.inter_code in Hp; exact (proj2 Hp).
Qed.

Lemma set_inter_greatest (s t u : FinSet.t K) :
  FinSet.subset E u s = true -> FinSet.subset E u t = true ->
  FinSet.subset E u (FinSet.inter E s t) = true.
Proof.
  repeat rewrite FinSet.subset_code; intros Hus Hut p Hp.
  apply FinSet.inter_code; split; [apply Hus | apply Hut]; exact Hp.
Qed.

Lemma set_member_subset (s t : FinSet.t K) : FinSet.subset E s t = true ->
  forall k, FinSet.mem E k s = true -> FinSet.mem E k t = true.
Proof.
  rewrite FinSet.subset_code; intros Hsub k; repeat rewrite FinSet.mem_code; apply Hsub.
Qed.

(** All raw sets satisfy the weak lattice laws, including malformed tries. *)
Theorem powerset_laws : lattice_laws (powerset_lattice E).
Proof.
  constructor; cbn.
  - apply set_subset_refl.
  - apply set_subset_trans.
  - apply set_empty_least.
  - apply set_union_left.
  - apply set_union_right.
  - apply set_union_left.
  - apply set_union_right.
  - intros a b _; apply set_subset_refl.
  - intros a b Hba; exact Hba.
Qed.

(** Union is a least upper bound at every trie position. *)
Theorem powerset_lub : lub_laws (powerset_lattice E).
Proof.
  constructor; intros a b c; cbn; repeat rewrite FinSet.subset_code.
  intros Ha Hb p Hp; apply FinSet.union_code in Hp; destruct Hp as [Hp | Hp].
  - apply Ha; exact Hp.
  - apply Hb; exact Hp.
Qed.

(** Inclusion preserves set membership. *)
Theorem powerset_gamma_laws : concretisation_laws (powerset_lattice E) (powerset_gamma E).
Proof.
  constructor; intros a b k Hab Hk; exact (set_member_subset a b Hab k Hk).
Qed.

(** The empty set denotes nothing. *)
Theorem powerset_gamma_bot_empty : bottom_empty (powerset_lattice E) (powerset_gamma E).
Proof.
  constructor; intro k; cbn; rewrite FinSet.mem_empty; discriminate.
Qed.

(** Reverse inclusion of represented facts satisfies the weak lattice laws. *)
Theorem must_laws : lattice_laws (must_lattice E).
Proof.
  constructor.
  - intros [|s]; cbn; [reflexivity | apply set_subset_refl].
  - intros [|s] [|t] [|u]; cbn; intros Hst Htu; try discriminate; try reflexivity.
    eapply set_subset_trans; eassumption.
  - intros [|s]; reflexivity.
  - intros [|s] [|t]; cbn; try reflexivity;
      [apply set_subset_refl | apply set_inter_left].
  - intros [|s] [|t]; cbn; try reflexivity;
      [apply set_subset_refl | apply set_inter_right].
  - intros [|s] [|t]; cbn; try reflexivity;
      [apply set_subset_refl | apply set_inter_left].
  - intros [|s] [|t]; cbn; try reflexivity;
      [apply set_subset_refl | apply set_inter_right].
  - intros [|s] b _; cbn; [reflexivity | apply set_subset_refl].
  - intros a b Hba; exact Hba.
Qed.

(** Intersection is the least upper bound in reverse inclusion. *)
Theorem must_lub : lub_laws (must_lattice E).
Proof.
  constructor; intros [|s] [|t] [|u]; cbn; intros Ha Hb;
    try discriminate; try reflexivity; try assumption.
  apply set_inter_greatest; assumption.
Qed.
End RawLaws.

(** The empty conjunction is the greatest must-value. *)
Definition must_top {K} (E : encoding K) : top (must_lattice E).
Proof.
  refine {| top_value := Only FinSet.empty |}.
  abstract (intros [|s]; reflexivity).
Defined.

Section MeaningLaws.
Context {K V C : Type} (E : encoding K) (holds : K -> C -> Prop).

(** Increasing needs preserves reflexivity and restricts agreement. *)
Theorem powerset_agree_laws :
  agreement_laws (powerset_lattice E) (@powerset_agree K V E).
Proof.
  constructor.
  - intros a x k _; reflexivity.
  - intros a b x y Hab Hxy k Hk; apply Hxy; exact (set_member_subset E a b Hab k Hk).
Qed.

(** Empty needs relate every pair of states. *)
Theorem powerset_agree_bot : agreement_bot (powerset_lattice E) (@powerset_agree K V E).
Proof.
  constructor; intros x y k Hk; change (FinSet.mem E k FinSet.empty = true) in Hk.
  rewrite FinSet.mem_empty in Hk; discriminate.
Qed.

(** Agreement on each input gives agreement on their union. *)
Theorem powerset_agree_join :
  agreement_join_law (powerset_lattice E) (@powerset_agree K V E).
Proof.
  constructor; intros a b x y Ha Hb k Hk; apply FinSet.mem_union in Hk.
  destruct Hk as [Hk | Hk]; [apply Ha | apply Hb]; exact Hk.
Qed.

(** Equality on represented keys is symmetric and transitive. *)
Theorem powerset_agree_equivalence : agreement_equivalence (@powerset_agree K V E).
Proof.
  constructor.
  - intros a x y Hxy k Hk; symmetry; apply Hxy; exact Hk.
  - intros a x y z Hxy Hyz k Hk; transitivity (y k); [apply Hxy | apply Hyz]; exact Hk.
Qed.

(** Dropping must-facts enlarges their concrete meaning. *)
Theorem must_gamma_laws : concretisation_laws (must_lattice E) (must_gamma E holds).
Proof.
  constructor; intros [|s] [|t] c Hst Hc; cbn in *; try contradiction; try discriminate.
  intros k Hk; apply Hc; exact (set_member_subset E t s Hst k Hk).
Qed.

(** The explicit must-bottom is unreachable. *)
Theorem must_gamma_bot_empty : bottom_empty (must_lattice E) (must_gamma E holds).
Proof.
  constructor; intros c Hc; exact Hc.
Qed.

(** The empty conjunction holds in every state. *)
Theorem must_gamma_top_full : top_full (must_top E) (must_gamma E holds).
Proof.
  constructor; intros c k Hk; change (FinSet.mem E k FinSet.empty = true) in Hk.
  rewrite FinSet.mem_empty in Hk; discriminate.
Qed.
End MeaningLaws.

(** A finite carrier contains only well-formed sets supported in its universe. *)
Definition within_set {K} (E : encoding K) (U : list K) (s : FinSet.t K) : Prop :=
  FinSet.wf E s /\ forall k, FinSet.mem E k s = true -> In k U.

(** Finite sets carry erased evidence of support and well-formedness. *)
Definition finite_set {K} (E : encoding K) (U : list K) : Type :=
  { s : FinSet.t K | within_set E U s }.

Lemma within_set_empty {K} (E : encoding K) (U : list K) :
  within_set E U FinSet.empty.
Proof.
  split; [apply Map.wf_empty | intros k Hk; rewrite FinSet.mem_empty in Hk; discriminate].
Qed.

Lemma within_set_union {K} (E : encoding K) (U : list K) (a b : FinSet.t K) :
  within_set E U a -> within_set E U b -> within_set E U (FinSet.union E a b).
Proof.
  intros [Hwa Ha] [Hwb Hb]; split.
  - apply FinSet.wf_union; assumption.
  - intros k Hk; apply FinSet.mem_union in Hk; destruct Hk; [apply Ha | apply Hb]; assumption.
Qed.

Lemma within_set_inter {K} (E : encoding K) (U : list K) (a b : FinSet.t K) :
  within_set E U a -> within_set E U b -> within_set E U (FinSet.inter E a b).
Proof.
  intros [Hwa Ha] [Hwb Hb]; split.
  - apply FinSet.wf_inter; assumption.
  - intros k Hk; apply FinSet.mem_inter in Hk; apply Ha; exact (proj1 Hk).
Qed.

(** Finite powersets use the raw operations with their preserved support proofs. *)
Definition finite_powerset_lattice {K} (E : encoding K) (U : list K) :
  lattice (finite_set E U) :=
  {| leb := fun a b => FinSet.subset E (proj1_sig a) (proj1_sig b);
     bot := exist _ FinSet.empty (within_set_empty E U);
     join := fun a b => exist _ (FinSet.union E (proj1_sig a) (proj1_sig b))
       (within_set_union E U _ _ (proj2_sig a) (proj2_sig b));
     widen := fun a b => exist _ (FinSet.union E (proj1_sig a) (proj1_sig b))
       (within_set_union E U _ _ (proj2_sig a) (proj2_sig b));
     narrow := fun a _ => a |}.

(** The universe itself is the greatest finite powerset. *)
Definition finite_powerset_top {K} (E : encoding K) (U : list K) :
  top (finite_powerset_lattice E U).
Proof.
  assert (Hwithin : within_set E U (FinSet.of_list E U)).
  { split.
    - apply FinSet.wf_fold_add; apply Map.wf_empty.
    - intros k Hk; apply FinSet.of_list_spec in Hk; exact Hk. }
  refine {| top_value := exist _ (FinSet.of_list E U) Hwithin |}.
  abstract (intros [s [Hwf Hin]]; cbn; apply FinSet.subset_spec; [exact Hwf |];
    intros k Hk; apply FinSet.of_list_spec; apply Hin; exact Hk).
Defined.

(** Finite intersection preserves the finite carrier. *)
Definition finite_set_inter {K} (E : encoding K) (U : list K)
  (a b : finite_set E U) : finite_set E U :=
  exist _ (FinSet.inter E (proj1_sig a) (proj1_sig b))
    (within_set_inter E U _ _ (proj2_sig a) (proj2_sig b)).

(** Finite must-facts are the dual of finite may-facts. *)
Definition finite_must_lattice {K} (E : encoding K) (U : list K) :
  lattice (finite_set E U) :=
  dual_lattice (finite_powerset_lattice E U) (finite_powerset_top E U) (finite_set_inter E U).

Section FiniteLaws.
Context {K : Type} (E : encoding K) (U : list K).

(** Restricting the carrier preserves every powerset law. *)
Theorem finite_powerset_laws : lattice_laws (finite_powerset_lattice E U).
Proof.
  constructor; cbn.
  - intros [a Ha]; apply set_subset_refl.
  - intros [a Ha] [b Hb] [c Hc]; apply set_subset_trans.
  - intros [a Ha]; reflexivity.
  - intros [a Ha] [b Hb]; apply set_union_left.
  - intros [a Ha] [b Hb]; apply set_union_right.
  - intros [a Ha] [b Hb]; apply set_union_left.
  - intros [a Ha] [b Hb]; apply set_union_right.
  - intros [a Ha] [b Hb] _; apply set_subset_refl.
  - intros a b Hba; exact Hba.
Qed.

(** Finite union remains a least upper bound. *)
Theorem finite_powerset_lub : lub_laws (finite_powerset_lattice E U).
Proof.
  constructor; intros [a Ha] [b Hb] [c Hc]; apply (join_least (powerset_lub E)).
Qed.

(** Finite intersection is a greatest lower bound. *)
Theorem finite_set_inter_meet :
  meet_laws (finite_powerset_lattice E U) (finite_set_inter E U).
Proof.
  constructor; intros [a Ha] [b Hb]; cbn.
  - apply set_inter_left.
  - apply set_inter_right.
  - intros [c Hc]; apply set_inter_greatest.
Qed.

(** Finite reverse inclusion satisfies the weak lattice laws. *)
Theorem finite_must_laws : lattice_laws (finite_must_lattice E U).
Proof.
  apply dual_laws; [apply finite_powerset_laws | apply finite_set_inter_meet].
Qed.

(** Finite must-facts have least upper bounds. *)
Theorem finite_must_lub : lub_laws (finite_must_lattice E U).
Proof.
  apply dual_lub; [apply finite_powerset_laws | apply finite_set_inter_meet].
Qed.

(** Forgetting the finite proof preserves boolean comparison exactly. *)
Theorem finite_powerset_embedding :
  order_embedding (powerset_lattice E) (finite_powerset_lattice E U) (@proj1_sig _ _).
Proof.
  intros a b; reflexivity.
Qed.
End FiniteLaws.

(** The empty set is greatest among finite must-facts. *)
Definition finite_must_top {K} (E : encoding K) (U : list K) :
  top (finite_must_lattice E U) :=
  dual_top (finite_powerset_top E U) (finite_set_inter E U) (finite_powerset_laws E U).

(** Cardinality is a monotone height for finite powersets. *)
Definition finite_powerset_height {K} (E : encoding K) (U : list K) (Hnodup : NoDup U) :
  monotone_height (finite_powerset_lattice E U).
Proof.
  unshelve refine (@MonotoneHeight _ (finite_powerset_lattice E U)
    (@Height _ (finite_powerset_lattice E U) (fun a => FinSet.size (proj1_sig a))
      (length U) _ _) _).
  - abstract (intros [a [Hwf Hin]]; cbn; apply (FinSet.size_le_length E); assumption).
  - abstract (intros [a Ha] [b Hb] Hstrict; cbn in *;
      apply (FinSet.size_lt E); try exact (proj1 Ha);
      try (apply FinSet.wf_union; [exact (proj1 Ha) | exact (proj1 Hb)]);
      [apply set_union_left | exact Hstrict]).
  - abstract (intros [a Ha] [b Hb] Hle; cbn in *;
      apply (FinSet.size_subset E); [exact (proj1 Ha) | exact (proj1 Hb) | exact Hle]).
Defined.

(** Missing cardinality is a monotone height for finite must-facts. *)
Definition finite_must_height {K} (E : encoding K) (U : list K) (Hnodup : NoDup U) :
  monotone_height (finite_must_lattice E U).
Proof.
  unshelve refine (@MonotoneHeight _ (finite_must_lattice E U)
    (@Height _ (finite_must_lattice E U)
      (fun a => length U - FinSet.size (proj1_sig a)) (length U) _ _) _).
  - abstract (intro a; cbn; lia).
  - abstract (intros [a Ha] [b Hb] Hstrict; cbn in *;
      assert (Hwi : FinSet.wf E (FinSet.inter E a b)) by
        (apply FinSet.wf_inter; [exact (proj1 Ha) | exact (proj1 Hb)]);
      pose proof (FinSet.size_lt E (FinSet.inter E a b) a Hwi (proj1 Ha)
        (set_inter_left E a b) Hstrict) as Hsize;
      pose proof (FinSet.size_le_length E a U (proj1 Ha) (proj2 Ha)) as Hbound; lia).
  - abstract (intros [a Ha] [b Hb] Hle; cbn in *;
      pose proof (FinSet.size_subset E b a (proj1 Hb) (proj1 Ha) Hle) as Hsize; lia).
Defined.

(** Clamping rebuilds precisely the source's members encountered in the universe. *)
Definition finite_clamp {K} (E : encoding K) (U : list K) (s : FinSet.t K) :
  finite_set E U.
Proof.
  refine (exist _ (FinSet.of_list E (filter (fun k => FinSet.mem E k s) U)) _).
  abstract (split; [apply FinSet.wf_fold_add; apply Map.wf_empty |];
    intros k Hk; apply FinSet.of_list_spec in Hk; apply filter_In in Hk; exact (proj1 Hk)).
Defined.

(** Finite may-meaning is the pullback of raw membership. *)
Definition finite_powerset_gamma {K} (E : encoding K) (U : list K) :
  concretisation (finite_set E U) K := comap_gamma (@proj1_sig _ _) (powerset_gamma E).

(** Finite needs use the underlying set's agreement. *)
Definition finite_powerset_agree {K V} (E : encoding K) (U : list K) :
  agreement (finite_set E U) (K -> V) := comap_agree (@proj1_sig _ _) (powerset_agree E).

(** Finite must-facts embed as finite conjunctions. *)
Definition finite_must_embed {K} (E : encoding K) (U : list K) (a : finite_set E U) : must K :=
  Only (proj1_sig a).

(** Finite must-meaning pulls back along the conjunction embedding. *)
Definition finite_must_gamma {K C} (E : encoding K) (U : list K) (holds : K -> C -> Prop) :
  concretisation (finite_set E U) C := comap_gamma (finite_must_embed E U) (must_gamma E holds).

Section FiniteMeaningLaws.
Context {K V C : Type} (E : encoding K) (holds : K -> C -> Prop) (U : list K).

(** Finite reverse inclusion agrees with the raw must order. *)
Theorem finite_must_embedding :
  order_embedding (must_lattice E) (finite_must_lattice E U) (finite_must_embed E U).
Proof.
  intros a b; reflexivity.
Qed.

(** Membership stays monotone on finite sets. *)
Theorem finite_powerset_gamma_laws :
  concretisation_laws (finite_powerset_lattice E U) (finite_powerset_gamma E U).
Proof.
  eapply comap_gamma_laws; [apply finite_powerset_embedding | apply powerset_gamma_laws].
Qed.

(** The finite empty set denotes nothing. *)
Theorem finite_powerset_gamma_bot_empty :
  bottom_empty (finite_powerset_lattice E U) (finite_powerset_gamma E U).
Proof.
  constructor; intro k; cbn; rewrite FinSet.mem_empty; discriminate.
Qed.

(** Finite needs preserve the raw agreement laws. *)
Theorem finite_powerset_agree_laws :
  agreement_laws (finite_powerset_lattice E U) (@finite_powerset_agree K V E U).
Proof.
  eapply comap_agree_laws; [apply finite_powerset_embedding | apply powerset_agree_laws].
Qed.

(** Dropping finite must-facts enlarges concrete meaning. *)
Theorem finite_must_gamma_laws :
  concretisation_laws (finite_must_lattice E U) (finite_must_gamma E U holds).
Proof.
  eapply comap_gamma_laws; [apply finite_must_embedding | apply must_gamma_laws].
Qed.

(** The finite empty conjunction denotes every state. *)
Theorem finite_must_gamma_top_full :
  top_full (finite_must_top E U) (finite_must_gamma E U holds).
Proof.
  constructor; intros c k Hk; cbn in Hk; rewrite FinSet.mem_empty in Hk; discriminate.
Qed.

(** Clamping preserves every membership whose key lies in the universe. *)
Theorem finite_clamp_mem : forall (s : FinSet.t K) (k : K), In k U ->
  FinSet.mem E k (proj1_sig (finite_clamp E U s)) = FinSet.mem E k s.
Proof.
  intros s k Hin; apply eq_true_iff_eq; cbn; rewrite FinSet.of_list_spec, filter_In; tauto.
Qed.

(** Every clamped member lies in the universe. *)
Theorem finite_clamp_in : forall (s : FinSet.t K) (k : K),
  FinSet.mem E k (proj1_sig (finite_clamp E U s)) = true -> In k U.
Proof.
  intros s k Hk; exact (proj2 (proj2_sig (finite_clamp E U s)) k Hk).
Qed.
End FiniteMeaningLaws.
