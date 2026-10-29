(** * Symbolic expression keys and persistent numbering

    Operator codes and canonical operand lists identify expressions in a flat table.
    For example, interning the operands [2; 1] of addition reuses the key for [1; 2].
    Builds on: CollectionsEncoding, CollectionsTable, BitsOp and Stdlib mergesort. *)

From Stdlib Require Import List PArith PeanoNat Bool Lia Sorting.Mergesort Sorting.Permutation.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTable.
From Gaulois.Bits Require Import BitsWord BitsOp.
Import List.ListNotations.

Module SymbolicOrder.
Definition t := positive.
Definition leb := Pos.leb.
Infix "<=?" := leb (at level 70, no associativity).

Lemma leb_total : forall a b, leb a b = true \/ leb b a = true.
Proof.
  intros a b; unfold leb; destruct (Pos.leb a b) eqn:Hab; [now left|].
  right; apply Pos.leb_le; apply Pos.leb_gt in Hab; lia.
Qed.
End SymbolicOrder.
Import SymbolicOrder.

Module SymbolicSort := Mergesort.Sort SymbolicOrder.
Import SymbolicSort.

(** A symbolic key is the complete operator-and-operands list. *)
Definition sym_key : Type := list positive.

(** Commutative operators sort operands before prefixing the injective operator code. *)
Definition expr_key (o : op) (args : list positive) : sym_key :=
  encode op_encoding o :: if commutative o then SymbolicSort.sort args else args.

(** Numberings store existing IDs and the next unused positive number. *)
Record numbering : Type := Numbering {
  ids : Table.t positive;
  next : positive
}.

(** The empty numbering starts allocating at one. *)
Definition numbering_empty : numbering := Numbering Table.empty 1%positive.

(** Interning performs one lookup and inserts only a previously absent key. *)
Definition intern (k : sym_key) (n : numbering) : positive * numbering :=
  match Table.get k (ids n) with
  | Some i => (i, n)
  | None => (next n, Numbering (Table.set k (next n) (ids n)) (Pos.succ (next n)))
  end.

(** IDs are unique, below the allocation frontier, and stored in a well-formed table. *)
Definition numbering_wf (n : numbering) : Prop :=
  Table.wf (ids n) /\
  (forall k i, Table.get k (ids n) = Some i -> (i < next n)%positive) /\
  (forall k1 k2 i, Table.get k1 (ids n) = Some i ->
    Table.get k2 (ids n) = Some i -> k1 = k2).

(** Empty numbering has no IDs that could violate its invariant. *)
Theorem numbering_wf_empty : numbering_wf numbering_empty.
Proof.
  unfold numbering_wf, numbering_empty; cbn; split; [apply Table.wf_empty|]; split.
  - intros k i Hget; rewrite Table.get_empty in Hget; discriminate.
  - intros k1 k2 i Hget; rewrite Table.get_empty in Hget; discriminate.
Qed.

(** A successful old lookup returns its ID without changing the numbering. *)
Theorem intern_found n k i : Table.get k (ids n) = Some i -> intern k n = (i, n).
Proof.
  intro Hget; unfold intern; rewrite Hget; reflexivity.
Qed.

(** An absent key receives exactly the frontier and advances it by one. *)
Theorem intern_fresh n k : Table.get k (ids n) = None ->
  fst (intern k n) = next n /\ next (snd (intern k n)) = Pos.succ (next n).
Proof.
  intro Hget; unfold intern; rewrite Hget; split; reflexivity.
Qed.

(** Interning makes its returned ID readable at the supplied key. *)
Theorem intern_get n k :
  Table.get k (ids (snd (intern k n))) = Some (fst (intern k n)).
Proof.
  unfold intern; destruct (Table.get k (ids n)) as [i|] eqn:Hget; cbn [fst snd ids].
  - exact Hget.
  - apply Table.get_set_same.
Qed.

(** Interning preserves every previously recorded ID, even for arbitrary raw numberings. *)
Theorem intern_stable n k k' i : Table.get k' (ids n) = Some i ->
  Table.get k' (ids (snd (intern k n))) = Some i.
Proof.
  intro Hget; unfold intern; destruct (Table.get k (ids n)) eqn:Hkey;
    cbn [fst snd ids].
  - exact Hget.
  - rewrite Table.get_set_other; [exact Hget|]; congruence.
Qed.

(** Interning maintains table well-formedness, frontier freshness and ID uniqueness. *)
Theorem numbering_wf_intern n k : numbering_wf n -> numbering_wf (snd (intern k n)).
Proof.
  intros [Htable [Hbound Hunique]]; unfold intern.
  destruct (Table.get k (ids n)) as [i|] eqn:Hkey; cbn [snd].
  - split; [exact Htable|]; split; assumption.
  - unfold numbering_wf; cbn [ids next]; split; [now apply Table.wf_set|]; split.
    + intros k' i Hget.
      destruct (list_eq_dec Pos.eq_dec k' k) as [Heq|Hne].
      * subst k'; rewrite Table.get_set_same in Hget; inversion Hget; lia.
      * rewrite Table.get_set_other in Hget by exact Hne.
        specialize (Hbound k' i Hget); lia.
    + intros k1 k2 i Hget1 Hget2.
      destruct (list_eq_dec Pos.eq_dec k1 k) as [Heq1|Hne1];
        destruct (list_eq_dec Pos.eq_dec k2 k) as [Heq2|Hne2].
      * congruence.
      * subst k1; rewrite Table.get_set_same in Hget1.
        rewrite Table.get_set_other in Hget2 by exact Hne2.
        specialize (Hbound k2 i Hget2); inversion Hget1; lia.
      * subst k2; rewrite Table.get_set_same in Hget2.
        rewrite Table.get_set_other in Hget1 by exact Hne1.
        specialize (Hbound k1 i Hget1); inversion Hget2; lia.
      * rewrite Table.get_set_other in Hget1 by exact Hne1.
        rewrite Table.get_set_other in Hget2 by exact Hne2.
        exact (Hunique k1 k2 i Hget1 Hget2).
Qed.

(** Equal IDs from two threaded interning operations identify the same key. *)
Theorem intern_injective n k1 k2 : numbering_wf n ->
  fst (intern k2 (snd (intern k1 n))) = fst (intern k1 n) -> k2 = k1.
Proof.
  intros Hwf Heq.
  pose proof (numbering_wf_intern n k1 Hwf) as Hwf1.
  pose proof (numbering_wf_intern (snd (intern k1 n)) k2 Hwf1) as [_ [_ Hunique]].
  apply (Hunique k2 k1 (fst (intern k1 n))).
  - rewrite <- Heq; apply intern_get.
  - apply intern_stable; apply intern_get.
Qed.

(** Sorting two positive operands gives the same pair in either input order. *)
Theorem expr_key_commutative o a b : commutative o = true ->
  expr_key o [a; b] = expr_key o [b; a].
Proof.
  intro Hcomm; unfold expr_key; rewrite Hcomm; f_equal.
  cbn [SymbolicSort.sort SymbolicSort.iter_merge SymbolicSort.merge_list_to_stack
    SymbolicSort.merge_stack SymbolicSort.merge].
  destruct (Pos.leb a b) eqn:Hab; destruct (Pos.leb b a) eqn:Hba;
    try reflexivity.
  - apply Pos.leb_le in Hab; apply Pos.leb_le in Hba; assert (a = b) by lia; now subst.
  - apply Pos.leb_gt in Hab; apply Pos.leb_gt in Hba; lia.
Qed.

Lemma commutative_arity o : commutative o = true -> arity o = 2.
Proof.
  destruct o; cbn; intros Hcomm; try discriminate; reflexivity.
Qed.

Lemma eval_op_wrong_arity o xs : length xs <> arity o -> eval_op o xs = None.
Proof.
  intro Hlength; destruct (eval_op o xs) as [r|] eqn:Heval; [|reflexivity].
  exfalso; apply Hlength; exact (eval_op_arity o xs r Heval).
Qed.

Lemma commutative_permutation o xs ys : commutative o = true ->
  Permutation xs ys -> eval_op o xs = eval_op o ys.
Proof.
  intros Hcomm Hperm; destruct (Nat.eq_dec (length xs) 2) as [Htwo|Hother].
  - destruct xs as [|a [|b rest]]; cbn in Htwo; try discriminate.
    destruct rest; [|discriminate].
    apply Permutation_length_2_inv in Hperm as [Heq|Heq]; subst ys.
    + reflexivity.
    + apply commutative_sound; exact Hcomm.
  - rewrite !eval_op_wrong_arity; [reflexivity| |].
    + rewrite <- (Permutation_length Hperm), (commutative_arity o Hcomm); exact Hother.
    + rewrite (commutative_arity o Hcomm); exact Hother.
Qed.

(** Equal canonical keys evaluate equally under every valuation, including malformed arities. *)
Theorem expr_key_eval o args1 args2 : expr_key o args1 = expr_key o args2 ->
  forall val : positive -> word,
    eval_op o (List.map val args1) = eval_op o (List.map val args2).
Proof.
  unfold expr_key; destruct (commutative o) eqn:Hcomm; intros Hkey val;
    injection Hkey as Hargs.
  - apply commutative_permutation; [exact Hcomm|]; apply Permutation_map.
    eapply Permutation_trans; [apply SymbolicSort.Permuted_sort|].
    rewrite Hargs; apply Permutation_sym; apply SymbolicSort.Permuted_sort.
  - now rewrite Hargs.
Qed.
