(** * Finite sets over encoded keys

    Sets use unit-valued maps, with position-wise union and short-circuit inclusion.
    For example, adding a member twice leaves the same singleton set.
    Builds on: CollectionsEncoding, CollectionsTrie, CollectionsMap. *)

From Stdlib Require Import List Bool PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap.

Module FinSet.

(** * Representation and operations *)

(** A finite set is a map with unit values. *)
Definition t (K : Type) : Type := Map.t K unit.

(** Well-formedness places every stored key at its encoded position. *)
Definition wf {K} (E : encoding K) (s : t K) : Prop := Map.wf E s.

(** The empty set is the empty map. *)
Definition empty {K} : t K := Map.empty.

(** Membership tests the encoded position of a key. *)
Definition mem {K} (E : encoding K) (k : K) (s : t K) : bool := Map.mem E k s.

(** Adding stores a unit binding at the key's code. *)
Definition add {K} (E : encoding K) (k : K) (s : t K) : t K := Map.set E k tt s.

(** Removing clears the key's encoded position. *)
Definition remove {K} (E : encoding K) (k : K) (s : t K) : t K := Map.remove E k s.

(** Union shares one-sided subtrees and keeps the left stored key at shared positions. *)
Definition union {K} (E : encoding K) (s1 s2 : t K) : t K :=
  Map.union_with (fun a _ => a) s1 s2.

(** Intersection retains only positions present in both sets. *)
Definition inter {K} (E : encoding K) (s1 s2 : t K) : t K :=
  Map.combine E (fun a b =>
    match a, b with
    | Some _, Some _ => Some tt
    | _, _ => None
    end) s1 s2.

(** Difference retains first-set positions absent from the second set. *)
Definition diff {K} (E : encoding K) (s1 s2 : t K) : t K :=
  Map.combine E (fun a b =>
    match a, b with
    | Some _, None => Some tt
    | _, _ => None
    end) s1 s2.

(** Inclusion checks first-set positions and stops at the first absent position. *)
Definition subset {K} (E : encoding K) (s1 s2 : t K) : bool :=
  Map.forall2 (fun _ o =>
    match o with
    | Some _ => true
    | None => false
    end) s1 s2.

(** Enumeration returns stored keys in trie position order. *)
Definition elements {K} (s : t K) : list K := List.map fst (Map.elements s).

(** Size counts the set's occupied positions. *)
Definition size {K} (s : t K) : nat := Map.size s.

(** Emptiness inspects the canonical map representation. *)
Definition is_empty {K} (s : t K) : bool := Map.is_empty s.

(** List construction adds each key from left to right. *)
Definition of_list {K} (E : encoding K) (l : list K) : t K :=
  List.fold_left (fun s k => add E k s) l empty.

(** * Position and membership laws *)

Section Laws.
Context {K : Type} (E : encoding K).
Variables (k : K) (s : t K).

(** Membership reads the key's position without inspecting its stored key. *)
Theorem mem_code : mem E k s = true <-> Map.code_get (encode E k) s <> None.
Proof.
  apply Map.mem_spec.
Qed.

End Laws.

Section PositionLaws.
Context {K : Type} (E : encoding K).
Variables (k k1 k2 : K) (s s1 s2 : t K) (p : positive).

(** The empty set contains no member. *)
Theorem mem_empty : mem E k (@empty K) = false.
Proof.
  unfold mem, Map.mem, empty; rewrite Map.get_empty; reflexivity.
Qed.

(** Adding a key makes it present and preserves every other membership. *)
Theorem mem_add : mem E k1 (add E k2 s) = true <-> k1 = k2 \/ mem E k1 s = true.
Proof.
  destruct (Pos.eq_dec (encode E k1) (encode E k2)) as [Heq|Hne].
  - apply (encode_injective E) in Heq; subst k2.
    unfold mem, Map.mem, add; rewrite Map.get_set_same; tauto.
  - assert (Hkeys : k1 <> k2) by (intro Heq; subst k2; contradiction).
    unfold mem, Map.mem, add; rewrite Map.get_set_other by exact Hkeys; tauto.
Qed.

(** Removing a key preserves precisely the other members. *)
Theorem mem_remove : mem E k1 (remove E k2 s) = true <->
  k1 <> k2 /\ mem E k1 s = true.
Proof.
  destruct (Pos.eq_dec (encode E k1) (encode E k2)) as [Heq|Hne].
  - apply (encode_injective E) in Heq; subst k2.
    unfold mem, Map.mem, remove; rewrite Map.get_remove_same; intuition congruence.
  - assert (Hkeys : k1 <> k2) by (intro Heq; subst k2; contradiction).
    unfold mem, Map.mem, remove; rewrite Map.get_remove_other by exact Hkeys; tauto.
Qed.

(** A union binds a position present in either operand. *)
Theorem union_code : Map.code_get p (union E s1 s2) <> None <->
  Map.code_get p s1 <> None \/ Map.code_get p s2 <> None.
Proof.
  unfold union; rewrite Map.code_get_union_with.
  destruct (Map.code_get p s1), (Map.code_get p s2); cbn [Trie.union_opt];
    intuition congruence.
Qed.

(** An intersection binds exactly positions shared by its operands. *)
Theorem inter_code : Map.code_get p (inter E s1 s2) <> None <->
  Map.code_get p s1 <> None /\ Map.code_get p s2 <> None.
Proof.
  unfold inter; rewrite Map.code_get_combine by reflexivity.
  destruct (Map.code_get p s1), (Map.code_get p s2); cbn; intuition congruence.
Qed.

(** Difference binds positions of its first operand absent from the second. *)
Theorem diff_code : Map.code_get p (diff E s1 s2) <> None <->
  Map.code_get p s1 <> None /\ Map.code_get p s2 = None.
Proof.
  unfold diff; rewrite Map.code_get_combine by reflexivity.
  destruct (Map.code_get p s1), (Map.code_get p s2); cbn; intuition congruence.
Qed.

End PositionLaws.

Section MembershipLaws.
Context {K : Type} (E : encoding K).
Variables (k : K) (s1 s2 : t K).

(** Union membership is disjunction, even for malformed inputs. *)
Theorem mem_union : mem E k (union E s1 s2) = true <->
  mem E k s1 = true \/ mem E k s2 = true.
Proof.
  repeat rewrite mem_code; apply union_code.
Qed.

(** Intersection membership is conjunction, even for malformed inputs. *)
Theorem mem_inter : mem E k (inter E s1 s2) = true <->
  mem E k s1 = true /\ mem E k s2 = true.
Proof.
  repeat rewrite mem_code; apply inter_code.
Qed.

(** Difference keeps a member exactly when the second operand lacks it. *)
Theorem mem_diff : mem E k (diff E s1 s2) = true <->
  mem E k s1 = true /\ mem E k s2 = false.
Proof.
  rewrite mem_code, diff_code, <- mem_code.
  unfold mem, Map.mem, Map.get.
  destruct (Map.code_get (encode E k) s2); intuition congruence.
Qed.

(** Subset checks inclusion at every position, without a well-formedness premise. *)
Theorem subset_code : subset E s1 s2 = true <->
  forall p, Map.code_get p s1 <> None -> Map.code_get p s2 <> None.
Proof.
  unfold subset; rewrite Map.forall2_spec; split.
  - intros Hrel q Hsome.
    destruct (Map.code_get q s1) as [x|] eqn:Hleft; try contradiction.
    specialize (Hrel q x Hleft).
    destruct (Map.code_get q s2); congruence.
  - intros Hincl q x Hget.
    assert (Hsome : Map.code_get q s2 <> None) by (apply Hincl; congruence).
    destruct (Map.code_get q s2); congruence.
Qed.

End MembershipLaws.

(** * Well-formedness and key agreement *)

Lemma wf_fold_add {K} (E : encoding K) (l : list K) (s : t K) :
  wf E s -> wf E (List.fold_left (fun s k => add E k s) l s).
Proof.
  revert s; induction l as [|k l IH]; intros s Hwf; cbn.
  - exact Hwf.
  - apply IH; apply Map.wf_set; exact Hwf.
Qed.

Lemma mem_fold_add {K} (E : encoding K) k (l : list K) (s : t K) :
  mem E k (List.fold_left (fun s k => add E k s) l s) = true <->
  In k l \/ mem E k s = true.
Proof.
  revert s; induction l as [|a l IH]; intro s; cbn.
  - tauto.
  - rewrite IH, mem_add; intuition congruence.
Qed.

(** List construction contains exactly the keys occurring in the list. *)
Theorem of_list_spec {K} (E : encoding K) k (l : list K) :
  mem E k (of_list E l) = true <-> In k l.
Proof.
  unfold of_list; rewrite mem_fold_add, mem_empty; intuition discriminate.
Qed.

Lemma wf_union {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> wf E s2 -> wf E (union E s1 s2).
Proof.
  apply Map.wf_union_with.
Qed.

Lemma wf_inter {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> wf E s2 -> wf E (inter E s1 s2).
Proof.
  apply Map.wf_combine.
Qed.

Lemma wf_diff {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> wf E s2 -> wf E (diff E s1 s2).
Proof.
  apply Map.wf_combine.
Qed.

(** All set constructors and operations preserve well-formedness. *)
Theorem wf_ops {K} (E : encoding K) k (s1 s2 : t K) l :
  wf E s1 -> wf E s2 ->
  wf E (@empty K) /\ wf E (add E k s1) /\ wf E (remove E k s1) /\
  wf E (union E s1 s2) /\ wf E (inter E s1 s2) /\ wf E (diff E s1 s2) /\
  wf E (of_list E l).
Proof.
  intros Hleft Hright; repeat split.
  - apply Map.wf_empty.
  - apply Map.wf_set; exact Hleft.
  - apply Map.wf_remove; exact Hleft.
  - apply wf_union; assumption.
  - apply wf_inter; assumption.
  - apply wf_diff; assumption.
  - apply wf_fold_add; apply Map.wf_empty.
Qed.

(** Well-formed sets are equal when their memberships agree. *)
Theorem extensionality {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> wf E s2 -> (forall k, mem E k s1 = mem E k s2) -> s1 = s2.
Proof.
  intros Hleft Hright Heq; apply (Map.extensionality E); try assumption.
  intro k; specialize (Heq k); unfold mem, Map.mem in Heq.
  destruct (Map.get E k s1) as [[]|], (Map.get E k s2) as [[]|]; congruence.
Qed.

Lemma code_member {K} (E : encoding K) (s : t K) p :
  wf E s -> Map.code_get p s <> None ->
  exists k, encode E k = p /\ mem E k s = true.
Proof.
  intros Hwf; unfold Map.code_get.
  destruct (Trie.get p s) as [[k []]|] eqn:Hget; cbn; intro Hsome; try contradiction.
  exists k; split.
  - eapply Hwf; exact Hget.
  - apply mem_code; unfold Map.code_get; rewrite (Hwf p k tt Hget), Hget; discriminate.
Qed.

(** On a well-formed first operand, subset is inclusion of key memberships. *)
Theorem subset_spec {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> (subset E s1 s2 = true <->
    forall k, mem E k s1 = true -> mem E k s2 = true).
Proof.
  intro Hwf; rewrite subset_code; split.
  - intros Hincl k; repeat rewrite mem_code; apply Hincl.
  - intros Hincl p Hsome; destruct (code_member E s1 p Hwf Hsome) as [k [Hcode Hmem]].
    specialize (Hincl k Hmem); apply mem_code in Hincl; rewrite Hcode in Hincl; exact Hincl.
Qed.

(** Enumerated keys are exactly the members of a well-formed set. *)
Theorem elements_spec {K} (E : encoding K) k (s : t K) :
  wf E s -> (In k (elements s) <-> mem E k s = true).
Proof.
  intro Hwf; unfold elements; rewrite in_map_iff; split.
  - intros [[a []] [Heq Hin]]; cbn in Heq; subst a.
    apply (Map.elements_sound E) in Hin; try exact Hwf.
    unfold mem, Map.mem; rewrite Hin; reflexivity.
  - intro Hmem; exists (k, tt); split; try reflexivity.
    apply (Map.elements_complete E); try exact Hwf.
    unfold mem, Map.mem in Hmem.
    destruct (Map.get E k s) as [[]|]; congruence.
Qed.

(** A well-formed set enumerates each member once. *)
Theorem elements_nodup {K} (E : encoding K) (s : t K) :
  wf E s -> NoDup (elements s).
Proof.
  apply Map.elements_nodup.
Qed.

(** Size is the number of enumerated keys for every set. *)
Theorem size_elements {K} (s : t K) : size s = List.length (elements s).
Proof.
  unfold size, elements; rewrite length_map; apply Map.size_elements.
Qed.

(** A well-formed set is empty exactly when it has no members. *)
Theorem is_empty_spec {K} (E : encoding K) (s : t K) :
  wf E s -> (is_empty s = true <-> forall k, mem E k s = false).
Proof.
  intro Hwf; unfold is_empty; rewrite Map.is_empty_spec by exact Hwf.
  split; intros Hnone k; specialize (Hnone k); unfold mem, Map.mem in *.
  - rewrite Hnone; reflexivity.
  - destruct (Map.get E k s); congruence.
Qed.

(** * Cardinality *)

(** Inclusion of well-formed sets bounds their sizes. *)
Theorem size_subset {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> wf E s2 -> subset E s1 s2 = true -> size s1 <= size s2.
Proof.
  intros Hleft Hright Hincl; repeat rewrite size_elements.
  apply NoDup_incl_length.
  - apply (elements_nodup E); exact Hleft.
  - intros k Hin; apply (elements_spec E); try exact Hright.
    apply (proj1 (subset_spec E s1 s2 Hleft) Hincl).
    apply (elements_spec E); assumption.
Qed.

(** A proper subset of well-formed sets has strictly smaller size. *)
Theorem size_lt {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> wf E s2 -> subset E s1 s2 = true ->
  subset E s2 s1 = false -> size s1 < size s2.
Proof.
  intros Hleft Hright Hincl Hproper.
  pose proof (size_subset E s1 s2 Hleft Hright Hincl) as Hle.
  assert (Hne : size s1 <> size s2).
  { intro Heq.
    assert (Hreverse : incl (elements s2) (elements s1)).
    { apply NoDup_length_incl.
      - apply (elements_nodup E); exact Hleft.
      - repeat rewrite <- size_elements; lia.
      - intros k Hin; apply (elements_spec E); try exact Hright.
        apply (proj1 (subset_spec E s1 s2 Hleft) Hincl).
        apply (elements_spec E); assumption. }
    assert (Hback : subset E s2 s1 = true).
    { apply (subset_spec E); try exact Hright; intros k Hmem.
      apply (elements_spec E); try exact Hleft; apply Hreverse.
      apply (elements_spec E); assumption. }
    congruence. }
  lia.
Qed.

(** A well-formed set contained in a list has size at most the list's length. *)
Theorem size_le_length {K} (E : encoding K) (s1 : t K) : forall U : list K,
  wf E s1 -> (forall k, mem E k s1 = true -> In k U) -> size s1 <= List.length U.
Proof.
  intros U Hwf Hincl; rewrite size_elements; apply NoDup_incl_length.
  - apply (elements_nodup E); exact Hwf.
  - intros k Hin; apply Hincl; apply (elements_spec E); assumption.
Qed.

(** * Set algebra *)

(* Equality of membership booleans follows from equivalence of their true cases. *)
Local Ltac membership_equality :=
  intro k; apply eq_true_iff_eq;
  repeat first [rewrite mem_union | rewrite mem_inter | rewrite mem_diff | rewrite mem_empty];
  intuition congruence.

(** Union commutes on well-formed sets. *)
Theorem union_comm {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> wf E s2 -> union E s1 s2 = union E s2 s1.
Proof.
  intros Hleft Hright; apply (extensionality E);
    try (apply wf_union; assumption); membership_equality.
Qed.

(** Union associates on well-formed sets. *)
Theorem union_assoc {K} (E : encoding K) (s1 s2 s3 : t K) :
  wf E s1 -> wf E s2 -> wf E s3 ->
  union E s1 (union E s2 s3) = union E (union E s1 s2) s3.
Proof.
  intros H1 H2 H3; apply (extensionality E).
  - apply wf_union; [exact H1|apply wf_union; assumption].
  - apply wf_union; [apply wf_union; assumption|exact H3].
  - membership_equality.
Qed.

(** Union with itself leaves a well-formed set unchanged. *)
Theorem union_idem {K} (E : encoding K) (s : t K) : wf E s -> union E s s = s.
Proof.
  intro Hwf; apply (extensionality E); try exact Hwf;
    try (apply wf_union; assumption); membership_equality.
Qed.

(** Empty is a right identity of union. *)
Theorem union_empty_r {K} (E : encoding K) (s : t K) :
  wf E s -> union E s empty = s.
Proof.
  intro Hwf; apply (extensionality E); try exact Hwf.
  - apply wf_union; [exact Hwf|apply Map.wf_empty].
  - membership_equality.
Qed.

(** Intersection commutes on well-formed sets. *)
Theorem inter_comm {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> wf E s2 -> inter E s1 s2 = inter E s2 s1.
Proof.
  intros Hleft Hright; apply (extensionality E);
    try (apply wf_inter; assumption); membership_equality.
Qed.

(** Intersection associates on well-formed sets. *)
Theorem inter_assoc {K} (E : encoding K) (s1 s2 s3 : t K) :
  wf E s1 -> wf E s2 -> wf E s3 ->
  inter E s1 (inter E s2 s3) = inter E (inter E s1 s2) s3.
Proof.
  intros H1 H2 H3; apply (extensionality E).
  - apply wf_inter; [exact H1|apply wf_inter; assumption].
  - apply wf_inter; [apply wf_inter; assumption|exact H3].
  - membership_equality.
Qed.

(** Intersection with itself leaves a well-formed set unchanged. *)
Theorem inter_idem {K} (E : encoding K) (s : t K) : wf E s -> inter E s s = s.
Proof.
  intro Hwf; apply (extensionality E); try exact Hwf;
    try (apply wf_inter; assumption); membership_equality.
Qed.

(** Intersecting with empty yields empty. *)
Theorem inter_empty_r {K} (E : encoding K) (s : t K) :
  wf E s -> inter E s empty = empty.
Proof.
  intro Hwf; apply (extensionality E).
  - apply wf_inter; [exact Hwf|apply Map.wf_empty].
  - apply Map.wf_empty.
  - membership_equality.
Qed.

(** Intersection distributes over union on well-formed sets. *)
Theorem inter_union_distr {K} (E : encoding K) (s1 s2 s3 : t K) :
  wf E s1 -> wf E s2 -> wf E s3 ->
  inter E s1 (union E s2 s3) = union E (inter E s1 s2) (inter E s1 s3).
Proof.
  intros H1 H2 H3; apply (extensionality E).
  - apply wf_inter; [exact H1|apply wf_union; assumption].
  - apply wf_union; apply wf_inter; assumption.
  - membership_equality.
Qed.

(** Union absorbs intersection with the same well-formed set. *)
Theorem union_inter_absorb {K} (E : encoding K) (s1 s2 : t K) :
  wf E s1 -> wf E s2 -> union E s1 (inter E s1 s2) = s1.
Proof.
  intros H1 H2; apply (extensionality E); try exact H1.
  - apply wf_union; [exact H1|apply wf_inter; assumption].
  - membership_equality.
Qed.

(** Subtracting a well-formed set from itself yields empty. *)
Theorem diff_self {K} (E : encoding K) (s : t K) : wf E s -> diff E s s = empty.
Proof.
  intro Hwf; apply (extensionality E).
  - apply wf_diff; assumption.
  - apply Map.wf_empty.
  - membership_equality.
Qed.

End FinSet.
Import FinSet.
