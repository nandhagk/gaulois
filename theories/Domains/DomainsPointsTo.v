(** * Points-to sets

    A finite set of concrete objects and an unknown-object flag describe pointer targets.
    For example, two distinct singleton targets cannot alias.
    Builds on: CollectionsFinSet, OrderPowerset, OrderProduct and OrderBasic. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderBasic OrderProduct OrderPowerset.
Import List.ListNotations.

(** Targets consist of known objects and the possibility of any other object. *)
Definition points_to : Type := (FinSet.t positive * bool)%type.

(** Both known targets and the unknown flag grow under the may order. *)
Definition points_to_lattice : lattice points_to :=
  product_lattice (powerset_lattice positive_encoding) bool_lattice.

(** A target is possible if it is known or the unknown flag is set. *)
Definition points_to_gamma : concretisation points_to positive :=
  {| gamma := fun a p => FinSet.mem positive_encoding p (fst a) = true \/ snd a = true |}.

(** A singleton points-to value identifies one concrete object. *)
Definition pts_of_site (s : positive) : points_to :=
  (FinSet.add positive_encoding s FinSet.empty, false).

(** An unknown target may denote any object. *)
Definition pts_unknown : points_to := (FinSet.empty, true).

(** Possible aliasing includes unknown objects or a shared known target. *)
Definition pts_may_alias (a b : points_to) : bool :=
  snd a || snd b || negb (FinSet.is_empty (FinSet.inter positive_encoding (fst a) (fst b))).

(** Read the unique occupied position, rather than a possibly malformed stored key. *)
Definition pts_singleton (s : FinSet.t positive) : option positive :=
  match Trie.elements s with
  | [(p, _)] => Some p
  | _ => None
  end.

(** Definite aliasing requires the same unique concrete target without unknown flags. *)
Definition pts_must_alias (a b : points_to) : bool :=
  negb (snd a) && negb (snd b) &&
    match pts_singleton (fst a), pts_singleton (fst b) with
    | Some p, Some q => Pos.eqb p q
    | _, _ => false
    end.

Lemma pts_singleton_member : forall s p q,
  pts_singleton s = Some p -> FinSet.mem positive_encoding q s = true -> q = p.
Proof.
  intros s p q Hsingle Hmem. apply FinSet.mem_code in Hmem.
  unfold Map.code_get in Hmem. cbn [encode positive_encoding] in Hmem.
  destruct (Trie.get q s) as [v|] eqn:Hget; [|contradiction].
  apply Trie.elements_complete in Hget.
  unfold pts_singleton in Hsingle.
  destruct (Trie.elements s) as [|[r x] rest]; [discriminate|].
  destruct rest as [|y rest]; [|discriminate]. injection Hsingle as Hsingle. subst r.
  cbn in Hget. destruct Hget as [Heq|Hfalse]; [injection Heq; congruence|contradiction].
Qed.

(** Points-to facts inherit the product's weak lattice laws. *)
Theorem points_to_laws : lattice_laws points_to_lattice.
Proof.
  apply product_laws; [apply powerset_laws|apply bool_laws].
Qed.

(** Points-to joins are least upper bounds. *)
Theorem points_to_lub : lub_laws points_to_lattice.
Proof.
  apply product_lub; [apply powerset_lub|apply bool_lub].
Qed.

(** Increasing known targets or the unknown flag preserves possible concrete targets. *)
Theorem points_to_gamma_laws : concretisation_laws points_to_lattice points_to_gamma.
Proof.
  constructor. intros [sa ua] [sb ub] p Hle [Hmem|Hunknown].
  - apply andb_true_iff in Hle as [Hsets _]. left.
    apply (gamma_monotone (powerset_gamma_laws positive_encoding) sa sb p Hsets Hmem).
  - apply andb_true_iff in Hle as [_ Hflags]. right.
    cbn in Hunknown, Hflags |- *. subst ua. exact Hflags.
Qed.

(** A concrete target shared by both values is reported as a possible alias. *)
Theorem pts_may_alias_sound : forall p pa pb,
  gamma points_to_gamma pa p -> gamma points_to_gamma pb p -> pts_may_alias pa pb = true.
Proof.
  intros p [sa ua] [sb ub] [Ha|Ha] [Hb|Hb]; unfold pts_may_alias; cbn in *.
  - apply orb_true_iff. right. apply negb_true_iff.
    destruct (FinSet.is_empty (FinSet.inter positive_encoding sa sb)) eqn:Hempty;
      [|reflexivity].
    unfold FinSet.is_empty, Map.is_empty in Hempty. apply Trie.is_empty_spec in Hempty.
    assert (Hmem : FinSet.mem positive_encoding p
      (FinSet.inter positive_encoding sa sb) = true).
    { apply FinSet.mem_inter. split; assumption. }
    unfold FinSet.mem, Map.mem, Map.get, Map.code_get in Hmem.
    rewrite Hempty, Trie.get_empty in Hmem. discriminate.
  - rewrite Hb, orb_true_r. reflexivity.
  - rewrite Ha. reflexivity.
  - rewrite Ha. reflexivity.
Qed.

(** A successful definite-alias query forces all described concrete objects to coincide. *)
Theorem pts_must_alias_sound : forall p q pa pb,
  pts_must_alias pa pb = true -> gamma points_to_gamma pa p ->
  gamma points_to_gamma pb q -> p = q.
Proof.
  intros p q [sa ua] [sb ub] Hmust Ha Hb.
  unfold pts_must_alias in Hmust. cbn in Hmust, Ha, Hb.
  repeat rewrite andb_true_iff in Hmust. destruct Hmust as [[Hua Hub] Hsingle].
  apply negb_true_iff in Hua, Hub. subst ua ub.
  destruct Ha as [Ha|Ha], Hb as [Hb|Hb]; try discriminate.
  destruct (pts_singleton sa) as [s|] eqn:Hsa,
    (pts_singleton sb) as [t|] eqn:Hsb; try discriminate.
  apply Pos.eqb_eq in Hsingle. subst t.
  rewrite (pts_singleton_member sa s p Hsa Ha), (pts_singleton_member sb s q Hsb Hb).
  reflexivity.
Qed.

(** A singleton points-to value denotes exactly its named object. *)
Theorem pts_of_site_gamma : forall s p,
  gamma points_to_gamma (pts_of_site s) p <-> p = s.
Proof.
  intros s p. cbn [points_to_gamma pts_of_site gamma fst snd].
  rewrite FinSet.mem_add, FinSet.mem_empty. intuition discriminate.
Qed.
