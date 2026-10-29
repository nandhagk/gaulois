(** * Addresses and overlap

    Addresses describe the allocation object, integer offset and width of a memory access.
    For example, four bytes at offset zero cover two bytes at offset one of the same object.
    Builds on: DomainsInterval and OrderConcrete. *)

From Stdlib Require Import ZArith Bool Lia.
From Gaulois.Order Require Import OrderConcrete.
From Gaulois.Domains Require Import DomainsInterval.

Local Open Scope Z_scope.

(** An absent site represents an unknown object, including summary objects. *)
Record address : Type := Address {
  site : option positive;
  offset : interval;
  size : nat
}.

(** Concrete accesses retain their object, starting offset and byte width. *)
Definition access : Type := (positive * Z * nat)%type.

(** An access touches the half-open integer range starting at its offset. *)
Definition bytes_of (c : access) (b : positive * Z) : Prop :=
  fst b = fst (fst c) /\ snd (fst c) <= snd b < snd (fst c) + Z.of_nat (snd c).

(** A concrete access has the described width and an allowed object and offset. *)
Definition address_gamma : concretisation address access :=
  {| gamma := fun a c => snd c = size a /\
       (site a = None \/ site a = Some (fst (fst c))) /\
       gamma interval_gamma (offset a) (snd (fst c)) |}.

(** Detect interval forms with no integer inhabitant, including inverted finite bounds. *)
Definition address_offset_empty (i : interval) : bool :=
  match i with
  | IBot => true
  | Itv PosInf _ => true
  | Itv _ NegInf => true
  | Itv (Fin lo) (Fin hi) => negb (lo <=? hi)
  | _ => false
  end.

Lemma address_offset_empty_sound : forall i z,
  address_offset_empty i = true -> gamma interval_gamma i z -> False.
Proof.
  intros [|[|lo|] [|hi|]] z; cbn; try discriminate; try tauto;
    try (intros _ [Hl Hh]; discriminate).
  rewrite negb_true_iff, Z.leb_gt.
  intros Hempty [Hlo Hhi]. apply Z.leb_le in Hlo, Hhi. lia.
Qed.

(** Coverage requires an exact first offset and a known common concrete object. *)
Definition covers (a1 a2 : address) : bool :=
  match site a1, site a2, offset a1, offset a2 with
  | Some s1, Some s2, Itv (Fin lo) (Fin hi), Itv lo2 hi2 =>
    Pos.eqb s1 s2 && (lo =? hi) &&
      (address_offset_empty (Itv lo2 hi2) ||
        (bound_leb (Fin lo) lo2 &&
          bound_leb hi2 (Fin (lo + Z.of_nat (size a1) - Z.of_nat (size a2)))))
  | Some s1, Some s2, Itv (Fin lo) (Fin hi), IBot => Pos.eqb s1 s2 && (lo =? hi)
  | _, _, _, _ => false
  end.

(** Disjointness follows from emptiness, distinct concrete objects or separated finite bounds. *)
Definition disjoint (a1 a2 : address) : bool :=
  address_offset_empty (offset a1) || address_offset_empty (offset a2) ||
    match site a1, site a2 with
    | Some s1, Some s2 =>
      negb (Pos.eqb s1 s2) ||
        match offset a1, offset a2 with
        | Itv (Fin lo1) (Fin hi1), Itv (Fin lo2) (Fin hi2) =>
          (hi1 + Z.of_nat (size a1) <=? lo2) ||
          (hi2 + Z.of_nat (size a2) <=? lo1)
        | _, _ => false
        end
    | _, _ => false
    end.

(** Potential overlap is the complement of proved disjointness. *)
Definition may_overlap (a1 a2 : address) : bool := negb (disjoint a1 a2).

Lemma address_finite_lower : forall lo z,
  bound_leb (Fin lo) (Fin z) = true -> lo <= z.
Proof.
  intros lo z Hle. apply Z.leb_le. exact Hle.
Qed.

Lemma address_between_bounds : forall lo hi x low high,
  bound_leb (Fin low) lo = true -> bound_leb hi (Fin high) = true ->
  gamma interval_gamma (Itv lo hi) x -> low <= x <= high.
Proof.
  intros lo hi x low high Hlo Hhi [Hxlo Hxhi]. split; apply address_finite_lower.
  - eapply bound_leb_trans; eassumption.
  - eapply bound_leb_trans; eassumption.
Qed.

(** Every byte described by the second access belongs to a covering first access. *)
Theorem covers_sound : forall a1 a2 c1 c2 b,
  covers a1 a2 = true -> gamma address_gamma a1 c1 ->
  gamma address_gamma a2 c2 -> bytes_of c2 b -> bytes_of c1 b.
Proof.
  intros [s1 i1 n1] [s2 i2 n2] [[t1 o1] w1] [[t2 o2] w2] [t k].
  intros Hcovers [Hw1 [Hs1 Hi1]] [Hw2 [Hs2 Hi2]] [Ht Hbyte].
  cbn in Hw1, Hw2, Hs1, Hs2, Hi1, Hi2, Ht, Hbyte. subst w1 w2 t.
  destruct s1 as [s1|], s2 as [s2|]; try discriminate Hcovers.
  destruct i1 as [|[|lo|] [|hi|]]; try discriminate Hcovers.
  destruct i2 as [|lo2 hi2]; [contradiction |].
  cbn [covers site offset size] in Hcovers.
  assert (Hnonempty : address_offset_empty (Itv lo2 hi2) = false).
  { destruct (address_offset_empty (Itv lo2 hi2)) eqn:He; [|reflexivity].
    exfalso. exact (address_offset_empty_sound _ _ He Hi2). }
  rewrite Hnonempty in Hcovers. cbn in Hcovers.
  repeat rewrite andb_true_iff in Hcovers.
  destruct Hcovers as [[Hsite Heq] [Hlo Hhi]].
  apply Pos.eqb_eq in Hsite. apply Z.eqb_eq in Heq. subst s2 hi.
  destruct Hs1 as [Hnone|Hsome]; [discriminate|injection Hsome as Hsome].
  destruct Hs2 as [Hnone|Hsome2]; [discriminate|injection Hsome2 as Hsome2].
  subst t1 t2. cbn in Hi1. destruct Hi1 as [Hlow Hhigh].
  apply Z.leb_le in Hlow, Hhigh.
  pose proof (address_between_bounds lo2 hi2 o2 lo
    (lo + Z.of_nat n1 - Z.of_nat n2) Hlo Hhi Hi2) as Hbounds.
  split; [reflexivity | cbn; lia].
Qed.

(** Proved disjoint addresses cannot describe accesses with a common byte. *)
Theorem disjoint_sound : forall a1 a2 c1 c2 b,
  disjoint a1 a2 = true -> gamma address_gamma a1 c1 ->
  gamma address_gamma a2 c2 -> bytes_of c1 b -> bytes_of c2 b -> False.
Proof.
  intros [s1 i1 n1] [s2 i2 n2] [[t1 o1] w1] [[t2 o2] w2] [t k].
  intros Hd [Hw1 [Hs1 Hi1]] [Hw2 [Hs2 Hi2]] [Ht1 Hb1] [Ht2 Hb2].
  cbn in Hw1, Hw2, Hs1, Hs2, Hi1, Hi2, Ht1, Ht2, Hb1, Hb2.
  subst w1 w2 t1 t2. unfold disjoint in Hd; cbn in Hd.
  repeat rewrite orb_true_iff in Hd. destruct Hd as [[He|He]|Hd].
  - exact (address_offset_empty_sound i1 o1 He Hi1).
  - exact (address_offset_empty_sound i2 o2 He Hi2).
  - destruct s1 as [s1|], s2 as [s2|]; try discriminate Hd.
    destruct Hs1 as [Hnone|Hsome]; [discriminate|injection Hsome as Hsome].
    destruct Hs2 as [Hnone|Hsome2]; [discriminate|injection Hsome2 as Hsome2].
    subst s1 s2. rewrite Pos.eqb_refl in Hd; cbn in Hd.
    destruct i1 as [|[|lo1|] [|hi1|]], i2 as [|[|lo2|] [|hi2|]];
      try discriminate Hd.
    cbn in Hi1, Hi2. destruct Hi1 as [Hl1 Hh1], Hi2 as [Hl2 Hh2].
    apply Z.leb_le in Hl1, Hh1, Hl2, Hh2.
    apply orb_true_iff in Hd. destruct Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.

(** Accesses sharing a byte always pass the potential-overlap test. *)
Theorem may_overlap_sound : forall a1 a2 c1 c2 b,
  gamma address_gamma a1 c1 -> gamma address_gamma a2 c2 ->
  bytes_of c1 b -> bytes_of c2 b -> may_overlap a1 a2 = true.
Proof.
  intros a1 a2 c1 c2 b H1 H2 Hb1 Hb2. unfold may_overlap.
  destruct (disjoint a1 a2) eqn:Hd; [|reflexivity].
  exfalso. exact (disjoint_sound a1 a2 c1 c2 b Hd H1 H2 Hb1 Hb2).
Qed.

(** An exact singleton-site address covers itself, including a zero-width access. *)
Theorem covers_exact : forall a1 s k,
  site a1 = Some s -> offset a1 = Itv (Fin k) (Fin k) -> covers a1 a1 = true.
Proof.
  intros a1 s k Hs Hi. unfold covers. rewrite Hs, Hi.
  rewrite Pos.eqb_refl, Z.eqb_refl. cbn [address_offset_empty bound_leb].
  replace (k + Z.of_nat (size a1) - Z.of_nat (size a1)) with k by lia.
  now rewrite Z.leb_refl.
Qed.

(** Known distinct objects are disjoint regardless of their offset intervals. *)
Theorem disjoint_sites : forall a1 a2 s1 s2,
  site a1 = Some s1 -> site a2 = Some s2 -> s1 <> s2 -> disjoint a1 a2 = true.
Proof.
  intros a1 a2 s1 s2 Hs1 Hs2 Hne. unfold disjoint. rewrite Hs1, Hs2.
  apply orb_true_iff. right. apply orb_true_iff. left.
  apply negb_true_iff, Pos.eqb_neq. exact Hne.
Qed.
