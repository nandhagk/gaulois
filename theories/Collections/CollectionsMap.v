(** * Maps over encoded keys

    Maps store each key beside its value at the key's encoded trie position.
    For example, setting a key twice retains its second value.
    Builds on: CollectionsEncoding, CollectionsTrie. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie.

Module Map.

(** * Representation and operations *)

(** A map stores key-value pairs in a canonical trie. *)
Definition t (K V : Type) : Type := Trie.t (K * V).

(** The empty map has no stored pair. *)
Definition empty {K V} : t K V := Trie.empty.

(** Every stored key agrees with the position at which it is stored. *)
Definition wf {K V} (E : encoding K) (m : t K V) : Prop :=
  forall p k v, Trie.get p m = Some (k, v) -> encode E k = p.

(** Position lookup discards the stored key without checking it. *)
Definition code_get {K V} (p : positive) (m : t K V) : option V :=
  option_map snd (Trie.get p m).

(** Key lookup encodes its key once and reads that position. *)
Definition get {K V} (E : encoding K) (k : K) (m : t K V) : option V :=
  code_get (encode E k) m.

(** Setting stores the supplied key and value at the encoded position. *)
Definition set {K V} (E : encoding K) (k : K) (v : V) (m : t K V) : t K V :=
  Trie.set (encode E k) (k, v) m.

(** Removing clears the supplied key's encoded position. *)
Definition remove {K V} (E : encoding K) (k : K) (m : t K V) : t K V :=
  Trie.remove (encode E k) m.

(** Mapping changes values while retaining stored keys. *)
Definition map {K V W} (f : V -> W) (m : t K V) : t K W :=
  Trie.map (fun kv => (fst kv, f (snd kv))) m.

(* A nonempty input supplies the key; the absent/absent case cannot invent one. *)
Definition combine_pair {K V W U} (f : option V -> option W -> option U)
    (a : option (K * V)) (b : option (K * W)) : option (K * U) :=
  match a, b with
  | Some (k, v), _ => option_map (fun u => (k, u)) (f (Some v) (option_map snd b))
  | None, Some (k, w) => option_map (fun u => (k, u)) (f None (Some w))
  | None, None => None
  end.

(** Combining selects the first available stored key at each retained position. *)
Definition combine {K V W U} (E : encoding K)
    (f : option V -> option W -> option U) (m1 : t K V) (m2 : t K W) : t K U :=
  Trie.combine (combine_pair f) m1 m2.

(** Union shares one-sided subtrees and retains the left key at shared positions. *)
Definition union_with {K V} (f : V -> V -> V) (m1 m2 : t K V) : t K V :=
  Trie.union_with (fun a b => (fst a, f (snd a) (snd b))) m1 m2.

(** Comparison visits only positions bound in the first map and stops on failure. *)
Definition forall2 {K V W} (r : V -> option W -> bool) (m1 : t K V) (m2 : t K W)
    : bool := Trie.forall2 (fun a b => r (snd a) (option_map snd b)) m1 m2.

(** Folding visits stored keys and values in trie position order. *)
Definition fold {K V B} (f : B -> K -> V -> B) (m : t K V) (b : B) : B :=
  Trie.fold (fun acc _ kv => f acc (fst kv) (snd kv)) m b.

(** Enumeration drops trie positions and retains stored pairs in traversal order. *)
Definition elements {K V} (m : t K V) : list (K * V) :=
  List.map snd (Trie.elements m).

(** Size counts bindings without reconstructing their keys. *)
Definition size {K V} (m : t K V) : nat := Trie.size m.

(** Emptiness inspects the canonical trie root. *)
Definition is_empty {K V} (m : t K V) : bool := Trie.is_empty m.

(** Membership tests for a value at the supplied key's encoded position. *)
Definition mem {K V} (E : encoding K) (k : K) (m : t K V) : bool :=
  match get E k m with
  | Some _ => true
  | None => false
  end.

(** List construction processes bindings from left to right, replacing duplicates. *)
Definition of_list {K V} (E : encoding K) (l : list (K * V)) : t K V :=
  List.fold_left (fun m kv => set E (fst kv) (snd kv) m) l empty.

(** Structural comparison compares values and ignores stored keys. *)
Definition beq {K V} (eqb : V -> V -> bool) (m1 m2 : t K V) : bool :=
  Trie.beq (fun a b => eqb (snd a) (snd b)) m1 m2.

(** * Position lookup and preservation *)

Section Laws.
Context {K V W U : Type} (E : encoding K).
Variables (k k1 k2 : K) (v : V) (m m' : t K V) (n : t K W).

(** Key lookup reads exactly the key's encoded position. *)
Theorem get_code : get E k m = code_get (encode E k) m.
Proof.
  reflexivity.
Qed.

(** The empty map has no value at any position. *)
Theorem code_get_empty : forall p, code_get p (@empty K V) = None.
Proof.
  intro p; unfold code_get, empty; rewrite Trie.get_empty; reflexivity.
Qed.

(** Combining maps computes each position independently. *)
Theorem code_get_combine : forall (f : option V -> option W -> option U) p,
  f None None = None ->
  code_get p (combine E f m n) = f (code_get p m) (code_get p n).
Proof.
  intros f p Hnone; unfold code_get, combine.
  rewrite Trie.get_combine by reflexivity.
  destruct (Trie.get p m) as [[a x]|], (Trie.get p n) as [[b y]|];
    cbn [combine_pair option_map snd]; try (rewrite Hnone; reflexivity);
    clear Hnone; destruct (f _ _); reflexivity.
Qed.

(** Union preserves one-sided values and combines shared values. *)
Theorem code_get_union_with : forall (f : V -> V -> V) p,
  code_get p (union_with f m m') = Trie.union_opt f (code_get p m) (code_get p m').
Proof.
  intros f p; unfold code_get, union_with; rewrite Trie.get_union_with.
  destruct (Trie.get p m) as [[a x]|], (Trie.get p m') as [[b y]|]; reflexivity.
Qed.

(** The short-circuit traversal checks each value bound in its first map. *)
Theorem forall2_spec : forall (r : V -> option W -> bool),
  forall2 r m n = true <-> forall p v, code_get p m = Some v ->
  r v (code_get p n) = true.
Proof.
  intro r; unfold forall2; rewrite Trie.forall2_spec; split.
  - intros Hrel p x; unfold code_get.
    destruct (Trie.get p m) as [[a y]|] eqn:Hget; cbn; intro Heq;
      try discriminate.
    inversion Heq; subst y; exact (Hrel p (a, x) Hget).
  - intros Hrel p [a x] Hget; cbn; apply (Hrel p x).
    unfold code_get; rewrite Hget; reflexivity.
Qed.

(** Well-formed unions keep their selected stored key at its code. *)
Theorem wf_union_with : forall (f : V -> V -> V), wf E m -> wf E m' ->
  wf E (union_with f m m').
Proof.
  intros f Hm Hm' p a x; unfold union_with; rewrite Trie.get_union_with.
  destruct (Trie.get p m) as [[b y]|] eqn:Hleft;
    destruct (Trie.get p m') as [[c z]|] eqn:Hright;
    cbn [Trie.union_opt]; intro Heq; inversion Heq; subst;
    eauto.
Qed.

(** Membership tests whether key lookup succeeds. *)
Theorem mem_spec : mem E k m = true <-> get E k m <> None.
Proof.
  unfold mem; destruct (get E k m); split; congruence.
Qed.

(** Empty maps satisfy the position invariant. *)
Theorem wf_empty : wf E (@empty K V).
Proof.
  intros p a x; unfold empty; rewrite Trie.get_empty; discriminate.
Qed.

(** Setting a binding preserves the position invariant. *)
Theorem wf_set : wf E m -> wf E (set E k v m).
Proof.
  intros Hwf p a x; unfold set.
  destruct (Pos.eq_dec (encode E k) p) as [Heq|Hne].
  - subst p; rewrite Trie.get_set_same; intro Hpair; inversion Hpair; reflexivity.
  - rewrite Trie.get_set_other by exact Hne; apply Hwf.
Qed.

(** Removing a binding preserves the position invariant. *)
Theorem wf_remove : wf E m -> wf E (remove E k m).
Proof.
  intros Hwf p a x; unfold remove.
  destruct (Pos.eq_dec (encode E k) p) as [Heq|Hne].
  - subst p; rewrite Trie.get_remove_same; discriminate.
  - rewrite Trie.get_remove_other by exact Hne; apply Hwf.
Qed.

(** Mapping values keeps every stored key unchanged. *)
Theorem wf_map : forall (f : V -> W), wf E m -> wf E (map f m).
Proof.
  intros f Hwf p a x; unfold map; rewrite Trie.get_map.
  destruct (Trie.get p m) as [[b y]|] eqn:Hget; cbn; intro Heq; try discriminate.
  inversion Heq; subst a; eapply Hwf; exact Hget.
Qed.

(** Combining well-formed maps selects a key already at that position. *)
Theorem wf_combine : forall (f : option V -> option W -> option U),
  wf E m -> wf E n -> wf E (combine E f m n).
Proof.
  intros f Hm Hn p a x; unfold combine; rewrite Trie.get_combine by reflexivity.
  destruct (Trie.get p m) as [[b y]|] eqn:Hleft;
    destruct (Trie.get p n) as [[c z]|] eqn:Hright; cbn [combine_pair];
    try discriminate;
    destruct (f _ _) eqn:Hvalue; cbn; intro Heq; try discriminate;
    inversion Heq; subst; eauto.
Qed.

(** Reading an empty map fails. *)
Theorem get_empty : get E k (@empty K V) = None.
Proof.
  apply code_get_empty.
Qed.

(** Reading the key just set returns its new value. *)
Theorem get_set_same : get E k (set E k v m) = Some v.
Proof.
  unfold get, code_get, set; rewrite Trie.get_set_same; reflexivity.
Qed.

(** Setting a distinct key leaves lookup unchanged. *)
Theorem get_set_other : k1 <> k2 -> get E k1 (set E k2 v m) = get E k1 m.
Proof.
  intro Hne; unfold get, code_get, set; rewrite Trie.get_set_other; try reflexivity.
  intro Heq; apply Hne; symmetry; eapply encode_injective; exact Heq.
Qed.

(** Reading the key just removed fails. *)
Theorem get_remove_same : get E k (remove E k m) = None.
Proof.
  unfold get, code_get, remove; rewrite Trie.get_remove_same; reflexivity.
Qed.

(** Removing a distinct key leaves lookup unchanged. *)
Theorem get_remove_other : k1 <> k2 -> get E k1 (remove E k2 m) = get E k1 m.
Proof.
  intro Hne; unfold get, code_get, remove; rewrite Trie.get_remove_other; try reflexivity.
  intro Heq; apply Hne; symmetry; eapply encode_injective; exact Heq.
Qed.

(** Mapping values commutes with key lookup. *)
Theorem get_map : forall (f : V -> W),
  get E k (map f m) = option_map f (get E k m).
Proof.
  intro f; unfold get, code_get, map; rewrite Trie.get_map.
  destruct (Trie.get (encode E k) m) as [[a x]|]; reflexivity.
Qed.

(** Combining maps commutes with key lookup. *)
Theorem get_combine : forall (f : option V -> option W -> option U),
  f None None = None -> get E k (combine E f m n) = f (get E k m) (get E k n).
Proof.
  intros f Hnone; unfold get; apply code_get_combine; exact Hnone.
Qed.

End Laws.

(** * Key agreement and traversal *)

Lemma wf_fold_set {K V} (E : encoding K) (l : list (K * V)) (m : t K V) :
  wf E m -> wf E (List.fold_left (fun m kv => set E (fst kv) (snd kv) m) l m).
Proof.
  revert m; induction l as [|[k v] l IH]; intros m Hwf; cbn.
  - exact Hwf.
  - apply IH; apply wf_set; exact Hwf.
Qed.

(** Building a map from bindings establishes well-formedness. *)
Theorem wf_of_list {K V} (E : encoding K) (l : list (K * V)) : wf E (of_list E l).
Proof.
  apply wf_fold_set; apply wf_empty.
Qed.

Lemma get_pair {K V} (E : encoding K) (m : t K V) k v :
  wf E m -> get E k m = Some v -> Trie.get (encode E k) m = Some (k, v).
Proof.
  intros Hwf; unfold get, code_get.
  destruct (Trie.get (encode E k) m) as [[a x]|] eqn:Hget; cbn;
    intro Heq; try discriminate.
  inversion Heq; subst x.
  assert (a = k) by (apply (encode_injective E); eapply Hwf; exact Hget).
  subst a; reflexivity.
Qed.

(** Well-formed maps are equal when all their key lookups agree. *)
Theorem extensionality {K V} (E : encoding K) (m m' : t K V) :
  wf E m -> wf E m' -> (forall k, get E k m = get E k m') -> m = m'.
Proof.
  intros Hm Hm' Heq; apply Trie.extensionality; intro p.
  destruct (Trie.get p m) as [[k v]|] eqn:Hleft;
    destruct (Trie.get p m') as [[k' v']|] eqn:Hright; try reflexivity.
  - pose proof (Hm p k v Hleft) as Hcode.
    pose proof (Hm' p k' v' Hright) as Hcode'.
    assert (k = k') by (apply (encode_injective E); congruence).
    subst k'; specialize (Heq k); unfold get, code_get in Heq.
    rewrite Hcode, Hleft, Hright in Heq; cbn in Heq; congruence.
  - specialize (Heq k); unfold get, code_get in Heq.
    rewrite (Hm p k v Hleft), Hleft, Hright in Heq; discriminate.
  - specialize (Heq k'); unfold get, code_get in Heq.
    rewrite (Hm' p k' v' Hright), Hleft, Hright in Heq; discriminate.
Qed.

(** A well-formed map is empty exactly when every key lookup fails. *)
Theorem is_empty_spec {K V} (E : encoding K) (m : t K V) :
  wf E m -> (is_empty m = true <-> forall k, get E k m = None).
Proof.
  intro Hwf; unfold is_empty; rewrite Trie.is_empty_spec; split.
  - intros Heq k; rewrite Heq; apply get_empty.
  - intro Hnone; apply (extensionality E); try assumption.
    + apply wf_empty.
    + intro k; rewrite Hnone; symmetry; apply get_empty.
Qed.

(** Enumerated bindings are successful lookups in a well-formed map. *)
Theorem elements_sound {K V} (E : encoding K) (k : K) (v : V) (m : t K V) :
  wf E m -> In (k, v) (elements m) -> get E k m = Some v.
Proof.
  intros Hwf Hin; apply in_map_iff in Hin.
  destruct Hin as [[p [a x]] [Heq Hin]]; cbn in Heq; inversion Heq; subst a x.
  apply Trie.elements_sound in Hin; unfold get, code_get.
  rewrite (Hwf p k v Hin), Hin; reflexivity.
Qed.

(** Every successful lookup of a well-formed map is enumerated. *)
Theorem elements_complete {K V} (E : encoding K) (k : K) (v : V) (m : t K V) :
  wf E m -> get E k m = Some v -> In (k, v) (elements m).
Proof.
  intros Hwf Hget; unfold elements; apply in_map_iff.
  exists (encode E k, (k, v)); split; try reflexivity.
  apply Trie.elements_complete; apply (get_pair E); assumption.
Qed.

(** Enumerating a well-formed map never repeats a key. *)
Theorem elements_nodup {K V} (E : encoding K) (m : t K V) :
  wf E m -> NoDup (List.map fst (elements m)).
Proof.
  intro Hwf; apply (NoDup_map_inv (encode E)).
  unfold elements; repeat rewrite map_map.
  replace (List.map (fun x => encode E (fst (snd x))) (Trie.elements m))
    with (List.map fst (Trie.elements m)).
  - apply Trie.elements_nodup.
  - apply map_ext_in; intros [p [k v]] Hin; cbn.
    symmetry; eapply Hwf; apply Trie.elements_sound; exact Hin.
Qed.

(** Folding follows exactly the enumeration order. *)
Theorem fold_elements {K V} (m : t K V) : forall B (f : B -> K -> V -> B) b,
  fold f m b = List.fold_left (fun acc kv => f acc (fst kv) (snd kv)) (elements m) b.
Proof.
  intros B f b; unfold fold, elements.
  rewrite Trie.fold_elements, Trie.fold_left_map_values.
  reflexivity.
Qed.

(** Map size counts enumerated bindings, including malformed maps. *)
Theorem size_elements {K V} (m : t K V) : size m = List.length (elements m).
Proof.
  unfold size, elements; rewrite length_map; apply Trie.size_elements.
Qed.

(** List construction keeps the last occurrence of each key. *)
Theorem get_of_list {K V} (E : encoding K) (k : K) : forall l : list (K * V),
  get E k (of_list E l) =
  option_map snd (List.find (fun kv => Pos.eqb (encode E (fst kv)) (encode E k))
    (List.rev l)).
Proof.
  intro l; induction l using rev_ind.
  - apply get_empty.
  - destruct x as [a v]; unfold of_list in *; rewrite fold_left_app; cbn.
    rewrite rev_app_distr; cbn.
    destruct (Pos.eqb (encode E a) (encode E k)) eqn:Hcode.
    + apply Pos.eqb_eq in Hcode; apply (encode_injective E) in Hcode; subst a.
      apply get_set_same.
    + rewrite get_set_other; try exact IHl.
      intro Heq; subst a; rewrite Pos.eqb_refl in Hcode; discriminate.
Qed.

(** Value comparison decides equality of all key lookups on well-formed maps. *)
Theorem beq_correct {K V} (E : encoding K) (m m' : t K V) :
  forall eqb : V -> V -> bool, (forall a b, eqb a b = true <-> a = b) ->
  wf E m -> wf E m' ->
  (beq eqb m m' = true <-> forall k, get E k m = get E k m').
Proof.
  intros eqb Heqb Hm Hm'; unfold beq; rewrite Trie.beq_pointwise; split.
  - intros Hpoint k; specialize (Hpoint (encode E k)); unfold get, code_get.
    destruct (Trie.get (encode E k) m) as [[a x]|];
      destruct (Trie.get (encode E k) m') as [[b y]|]; cbn in *;
      try contradiction; try reflexivity.
    apply Heqb in Hpoint; congruence.
  - intro Hget; pose proof (extensionality E m m' Hm Hm' Hget) as Heq; subst m'.
    intro p; destruct (Trie.get p m) as [[a x]|]; cbn; try exact I.
    apply Heqb; reflexivity.
Qed.

End Map.
Import Map.
