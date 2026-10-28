(** * Persistent union-find forests

    Parent links increase rank, bounding traversal by the cached maximum rank.
    For example, repeated unions preserve a class while finds compress its paths.
    Builds on: CollectionsEncoding, CollectionsMap, CollectionsFinSet. *)

From Stdlib Require Import List Bool PArith PeanoNat Lia Relation_Definitions Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
Import List.ListNotations.

Module UnionFind.

(** A forest stores parent and rank maps with a global rank bound. *)
Record t (K : Type) : Type := Forest {
  parents : Map.t K K;
  ranks : Map.t K nat;
  max_rank : nat
}.

Arguments Forest {K}.
Arguments parents {K}.
Arguments ranks {K}.
Arguments max_rank {K}.

(** Every key is initially its own root of rank zero. *)
Definition make {K} : t K := Forest Map.empty Map.empty 0.

Definition rank_of {K} (E : encoding K) (uf : t K) (x : K) : nat :=
  match Map.get E x (ranks uf) with
  | Some n => n
  | None => 0
  end.

Definition key_eqb {K} (E : encoding K) (x y : K) : bool :=
  Pos.eqb (encode E x) (encode E y).

Lemma key_eqb_spec {K} (E : encoding K) x y : key_eqb E x y = true <-> x = y.
Proof.
  unfold key_eqb; rewrite Pos.eqb_eq; split; [apply encode_injective|congruence].
Qed.

Lemma key_dec {K} (E : encoding K) (x y : K) : {x = y} + {x <> y}.
Proof.
  destruct (Pos.eq_dec (encode E x) (encode E y)) as [Heq|Hne].
  - left; apply (encode_injective E); exact Heq.
  - right; congruence.
Defined.

(** Maps are well formed and every parent has strictly larger bounded rank. *)
Definition wf {K} (E : encoding K) (uf : t K) : Prop :=
  Map.wf E (parents uf) /\ Map.wf E (ranks uf) /\
  (forall x, rank_of E uf x <= max_rank uf) /\
  (forall x y, Map.get E x (parents uf) = Some y -> rank_of E uf x < rank_of E uf y).

Definition redirect {K} (E : encoding K) (x root : K) (uf : t K) : t K :=
  Forest (Map.set E x root (parents uf)) (ranks uf) (max_rank uf).

(** A bounded find compresses each visited link on its return path. *)
Fixpoint find_fuel {K} (E : encoding K) (fuel : nat) (x : K) (uf : t K) : K * t K :=
  match fuel with
  | 0 => (x, uf)
  | S rest =>
    match Map.get E x (parents uf) with
    | None => (x, uf)
    | Some y =>
      let '(root, compressed) := find_fuel E rest y uf in
      (root, redirect E x root compressed)
    end
  end.

(** Rank bounds provide enough fuel to reach a root. *)
Definition find {K} (E : encoding K) (x : K) (uf : t K) : K * t K :=
  find_fuel E (S (max_rank uf)) x uf.

(** Equivalence compares the representatives returned by find. *)
Definition equiv {K} (E : encoding K) (uf : t K) (x y : K) : Prop :=
  fst (find E x uf) = fst (find E y uf).

Definition touch {K} (E : encoding K) (x : K) (uf : t K) : t K :=
  match Map.get E x (ranks uf) with
  | Some _ => uf
  | None => Forest (parents uf) (Map.set E x 0 (ranks uf)) (max_rank uf)
  end.

Definition link {K} (E : encoding K) (child root : K) (raise : bool) (uf : t K) : t K :=
  if raise then
    let n := S (rank_of E uf root) in
    Forest (Map.set E child root (parents uf)) (Map.set E root n (ranks uf))
      (Nat.max (max_rank uf) n)
  else redirect E child root uf.

(** Union first compresses both paths, then links their roots by rank. *)
Definition union {K} (E : encoding K) (x y : K) (uf : t K) : t K :=
  let '(rx, uf1) := find E x uf in
  let '(ry, uf2) := find E y uf1 in
  if key_eqb E rx ry then touch E rx uf2
  else
    match Nat.compare (rank_of E uf2 rx) (rank_of E uf2 ry) with
    | Lt => link E rx ry false uf2
    | Gt => link E ry rx false uf2
    | Eq => link E ry rx true uf2
    end.

(** Equivalence testing threads the two compressed forests. *)
Definition equivb {K} (E : encoding K) (x y : K) (uf : t K) : bool * t K :=
  let '(rx, uf1) := find E x uf in
  let '(ry, uf2) := find E y uf1 in
  (key_eqb E rx ry, uf2).

(** Support enumerates the union of parent and rank domains once. *)
Definition keys {K} (E : encoding K) (uf : t K) : list K :=
  FinSet.elements (FinSet.union E (Map.map (fun _ => tt) (parents uf))
    (Map.map (fun _ => tt) (ranks uf))).

(** Building from unions processes them in call order. *)
Definition of_unions {K} (E : encoding K) (l : list (K * K)) : t K :=
  List.fold_left (fun uf xy => union E (fst xy) (snd xy) uf) l make.

(** A path ends at a key without a parent. *)
Inductive reaches {K} (E : encoding K) (uf : t K) : K -> K -> Prop :=
  | Root x : Map.get E x (parents uf) = None -> reaches E uf x x
  | Step x y root : Map.get E x (parents uf) = Some y ->
      reaches E uf y root -> reaches E uf x root.

Lemma reaches_unique {K} (E : encoding K) uf x a b :
  reaches E uf x a -> reaches E uf x b -> a = b.
Proof.
  intro Hpath; revert b; induction Hpath as [x Hroot|x y a Hparent Hpath IH];
    intros b Hother; inversion Hother as [x' Hroot'|x' y' b' Hparent' Htail]; subst.
  - reflexivity.
  - congruence.
  - congruence.
  - assert (y = y') by congruence; subst y'; apply IH; exact Htail.
Qed.

Lemma reaches_root {K} (E : encoding K) uf x root :
  reaches E uf x root -> Map.get E root (parents uf) = None.
Proof.
  intro Hpath; induction Hpath; assumption.
Qed.

Lemma reaches_rank {K} (E : encoding K) uf x root :
  wf E uf -> reaches E uf x root -> rank_of E uf x <= rank_of E uf root.
Proof.
  intros [_ [_ [_ Hrank]]] Hpath; induction Hpath as [x Hroot|x y r Hparent Hpath IH].
  - lia.
  - specialize (Hrank x y Hparent); lia.
Qed.

Lemma redirect_wf {K} (E : encoding K) uf x root :
  wf E uf -> rank_of E uf x < rank_of E uf root -> wf E (redirect E x root uf).
Proof.
  intros [Hp [Hr [Hbound Hstep]]] Hlt; split.
  - apply Map.wf_set; exact Hp.
  - split; [exact Hr|]; split; [exact Hbound|]; intros a b Hget.
    change (Map.get E a (Map.set E x root (parents uf)) = Some b) in Hget.
    destruct (key_dec E a x) as [Heq|Hne].
    + subst a; rewrite Map.get_set_same in Hget; inversion Hget; subst b; exact Hlt.
    + rewrite Map.get_set_other in Hget by exact Hne; apply Hstep; exact Hget.
Qed.

Lemma redirect_root {K} (E : encoding K) uf x root :
  x <> root -> Map.get E root (parents uf) = None ->
  Map.get E root (parents (redirect E x root uf)) = None.
Proof.
  intros Hne Hroot; unfold redirect; cbn; rewrite Map.get_set_other by congruence; exact Hroot.
Qed.

Lemma redirect_reaches {K} (E : encoding K) uf x root :
  x <> root -> reaches E uf x root ->
  forall a b, reaches E (redirect E x root uf) a b <-> reaches E uf a b.
Proof.
  intros Hne Hpath a b; pose proof (reaches_root E uf x root Hpath) as Hroot; split.
  - intro Hnew; induction Hnew as [a Hnone|a y b Hparent Htail IH].
    + destruct (key_dec E a x) as [Heq|Hax].
      * subst a; change (Map.get E x (Map.set E x root (parents uf)) = None) in Hnone.
        rewrite Map.get_set_same in Hnone; discriminate.
      * apply Root; change (Map.get E a (Map.set E x root (parents uf)) = None) in Hnone.
        rewrite Map.get_set_other in Hnone by exact Hax; exact Hnone.
    + change (Map.get E a (Map.set E x root (parents uf)) = Some y) in Hparent.
      destruct (key_dec E a x) as [Heq|Hax].
      * subst a; rewrite Map.get_set_same in Hparent; inversion Hparent; subst y.
        assert (root = b) by (apply (reaches_unique E uf root root b); [apply Root|]; assumption).
        subst b; exact Hpath.
      * apply (Step E uf a y b); [rewrite Map.get_set_other in Hparent by exact Hax|];
          assumption.
  - intro Hold; induction Hold as [a Hnone|a y b Hparent Htail IH].
    + apply Root; cbn [redirect parents].
      destruct (key_dec E a x) as [Heq|Hax].
      * subst a; assert (x = root) by
          (apply (reaches_unique E uf x x root); [apply Root|]; assumption); contradiction.
      * rewrite Map.get_set_other by exact Hax; exact Hnone.
    + destruct (key_dec E a x) as [Heq|Hax].
      * subst a.
        assert (b = root) by (eapply reaches_unique; [eapply Step; eassumption|exact Hpath]).
        subst b; apply (Step E (redirect E x root uf) x root root).
        -- apply Map.get_set_same.
        -- apply Root; apply redirect_root; assumption.
      * apply (Step E (redirect E x root uf) a y b).
        -- cbn [redirect parents]; rewrite Map.get_set_other by exact Hax; exact Hparent.
        -- exact IH.
Qed.

Lemma find_fuel_ranks {K} (E : encoding K) fuel x uf :
  ranks (snd (find_fuel E fuel x uf)) = ranks uf /\
  max_rank (snd (find_fuel E fuel x uf)) = max_rank uf.
Proof.
  revert x uf; induction fuel as [|fuel IH]; intros x uf; cbn [find_fuel]; [auto|].
  destruct (Map.get E x (parents uf)) as [y|]; [|auto].
  specialize (IH y uf); destruct (find_fuel E fuel y uf) as [root uf']; exact IH.
Qed.

Lemma find_fuel_correct {K} (E : encoding K) fuel : forall x uf,
  wf E uf -> max_rank uf < fuel + rank_of E uf x ->
  let '(root, uf') := find_fuel E fuel x uf in
  wf E uf' /\ reaches E uf x root /\
  (forall a b, reaches E uf' a b <-> reaches E uf a b).
Proof.
  induction fuel as [|fuel IH]; intros x uf Hwf Hfuel.
  - pose proof (proj1 (proj2 (proj2 Hwf)) x) as Hbound; cbn in Hfuel; lia.
  - cbn [find_fuel]; destruct (Map.get E x (parents uf)) as [y|] eqn:Hparent.
    + pose proof (proj2 (proj2 (proj2 Hwf)) x y Hparent) as Hlt.
      specialize (IH y uf Hwf ltac:(lia)).
      pose proof (find_fuel_ranks E fuel y uf) as Hranks.
      destruct (find_fuel E fuel y uf) as [root uf'] eqn:Hfind.
      destruct IH as [Hwf' [Hpath Hagree]]; cbn in Hranks.
      destruct Hranks as [Hranks Hmax].
      assert (Hxr : rank_of E uf' x < rank_of E uf' root).
      { unfold rank_of; rewrite Hranks; fold (rank_of E uf x) (rank_of E uf root).
        pose proof (reaches_rank E uf y root Hwf Hpath); lia. }
      assert (Hne : x <> root) by (intro Heq; subst x; lia).
      assert (Hpathx : reaches E uf x root) by (eapply Step; eassumption).
      split; [apply redirect_wf; assumption|]; split; [exact Hpathx|].
      intros a b; rewrite (redirect_reaches E uf' x root Hne (proj2 (Hagree x root) Hpathx)).
      apply Hagree.
    + split; [exact Hwf|]; split; [apply Root; exact Hparent|].
      intros a b; reflexivity.
Qed.

Lemma find_correct {K} (E : encoding K) x uf : wf E uf ->
  wf E (snd (find E x uf)) /\ reaches E uf x (fst (find E x uf)) /\
  (forall a b, reaches E (snd (find E x uf)) a b <-> reaches E uf a b).
Proof.
  intro Hwf; pose proof (find_fuel_correct E (S (max_rank uf)) x uf Hwf ltac:(lia)) as H.
  unfold find; destruct (find_fuel E (S (max_rank uf)) x uf); exact H.
Qed.

(** Equality of representatives is an equivalence even for malformed forests. *)
Theorem equiv_equivalence {K} (E : encoding K) (uf : t K) : equivalence K (equiv E uf).
Proof.
  constructor; unfold reflexive, symmetric, transitive, equiv; congruence.
Qed.

(** The initial forest satisfies the rank invariant. *)
Theorem wf_make {K} (E : encoding K) : wf E (@make K).
Proof.
  split; [apply Map.wf_empty|]; split; [apply Map.wf_empty|]; split.
  - intro x; unfold rank_of; cbn; rewrite Map.get_empty; lia.
  - intros x y Hget; change (Map.get E x (@Map.empty K K) = Some y) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
Qed.

(** Path compression preserves well-formedness. *)
Theorem wf_find {K} (E : encoding K) uf x :
  wf E uf -> wf E (snd (find E x uf)).
Proof.
  intro Hwf; exact (proj1 (find_correct E x uf Hwf)).
Qed.

(** Finding one key preserves every representative. *)
Theorem find_rep_stable {K} (E : encoding K) uf x y : wf E uf ->
  fst (find E x (snd (find E y uf))) = fst (find E x uf).
Proof.
  intro Hwf; destruct (find_correct E y uf Hwf) as [Hwf' [_ Hagree]].
  apply (reaches_unique E uf x).
  - apply Hagree; exact (proj1 (proj2 (find_correct E x _ Hwf'))).
  - exact (proj1 (proj2 (find_correct E x uf Hwf))).
Qed.

(** A representative is a root and represents itself. *)
Theorem find_rep_canonical {K} (E : encoding K) uf x : wf E uf ->
  fst (find E (fst (find E x uf)) uf) = fst (find E x uf).
Proof.
  intro Hwf; apply (reaches_unique E uf (fst (find E x uf))).
  - exact (proj1 (proj2 (find_correct E _ uf Hwf))).
  - apply Root; eapply reaches_root; exact (proj1 (proj2 (find_correct E x uf Hwf))).
Qed.

(** Initially only equal keys are equivalent. *)
Theorem make_equiv {K} (E : encoding K) a b : equiv E make a b <-> a = b.
Proof.
  unfold equiv, find, make; cbn [max_rank find_fuel parents].
  rewrite !Map.get_empty; reflexivity.
Qed.

Definition support {K} (E : encoding K) (uf : t K) x : Prop :=
  Map.get E x (parents uf) <> None \/ Map.get E x (ranks uf) <> None.

Lemma keys_set_wf {K} (E : encoding K) (uf : t K) : wf E uf ->
  FinSet.wf E (FinSet.union E (Map.map (fun _ => tt) (parents uf))
    (Map.map (fun _ => tt) (ranks uf))).
Proof.
  intros [Hp [Hr _]]; apply Map.wf_union_with; apply Map.wf_map; assumption.
Qed.

Lemma keys_spec {K} (E : encoding K) uf x :
  wf E uf -> (In x (keys E uf) <-> support E uf x).
Proof.
  intro Hwf; unfold keys; rewrite FinSet.elements_spec by (apply keys_set_wf; exact Hwf).
  rewrite FinSet.mem_union; unfold FinSet.mem; rewrite !Map.mem_spec, !Map.get_map.
  unfold support; destruct (Map.get E x (parents uf)), (Map.get E x (ranks uf));
    cbn; intuition discriminate.
Qed.

(** Enumerating support never repeats a key. *)
Theorem keys_nodup {K} (E : encoding K) uf : wf E uf -> NoDup (keys E uf).
Proof.
  intro Hwf; apply (FinSet.elements_nodup E); apply keys_set_wf; exact Hwf.
Qed.

(** The initial support is empty. *)
Theorem keys_make {K} (E : encoding K) : keys E (@make K) = nil.
Proof.
  reflexivity.
Qed.

Lemma find_fuel_domain {K} (E : encoding K) fuel : forall x uf a,
  Map.get E a (parents (snd (find_fuel E fuel x uf))) = None <->
  Map.get E a (parents uf) = None.
Proof.
  induction fuel as [|fuel IH]; intros x uf a; cbn [find_fuel]; [reflexivity|].
  destruct (Map.get E x (parents uf)) as [y|] eqn:Hparent; [|reflexivity].
  specialize (IH y uf a); destruct (find_fuel E fuel y uf) as [root uf']; cbn in IH.
  cbn [snd redirect parents]; destruct (key_dec E a x) as [Heq|Hne].
  - subst a; rewrite Map.get_set_same, Hparent; split; discriminate.
  - rewrite Map.get_set_other by exact Hne; exact IH.
Qed.

Lemma find_support {K} (E : encoding K) x uf a :
  support E (snd (find E x uf)) a <-> support E uf a.
Proof.
  unfold support, find; destruct (find_fuel_ranks E (S (max_rank uf)) x uf) as [Hr Hmax].
  rewrite Hr; pose proof (find_fuel_domain E (S (max_rank uf)) x uf a); tauto.
Qed.

Lemma reaches_strict {K} (E : encoding K) uf x root :
  wf E uf -> reaches E uf x root -> x <> root -> rank_of E uf x < rank_of E uf root.
Proof.
  intros Hwf Hpath Hne; inversion Hpath as [a Hnone|a y r Hparent Htail]; subst.
  - contradiction.
  - pose proof (proj2 (proj2 (proj2 Hwf)) x y Hparent).
    pose proof (reaches_rank E uf y root Hwf Htail); lia.
Qed.

Lemma positive_rank_support {K} (E : encoding K) uf x :
  0 < rank_of E uf x -> support E uf x.
Proof.
  unfold rank_of, support; destruct (Map.get E x (ranks uf)) eqn:Hrank.
  - intro Hpositive; right; discriminate.
  - lia.
Qed.

Lemma path_support {K} (E : encoding K) uf x root :
  wf E uf -> reaches E uf x root -> x = root \/ (support E uf x /\ support E uf root).
Proof.
  intros Hwf Hpath; destruct (key_dec E x root) as [Heq|Hne]; [auto|right].
  split.
  - inversion Hpath as [a Hnone|a y r Hparent Htail]; subst; [contradiction|].
    left; rewrite Hparent; discriminate.
  - apply positive_rank_support; pose proof (reaches_strict E uf x root Hwf Hpath Hne); lia.
Qed.

(** A key outside support is alone in its class. *)
Theorem keys_support {K} (E : encoding K) uf x y : wf E uf -> ~ In x (keys E uf) ->
  equiv E uf x y -> y = x.
Proof.
  intros Hwf Houtside Hequiv; rewrite (keys_spec E uf x Hwf) in Houtside.
  destruct (Map.get E x (parents uf)) as [parent|] eqn:Hparent.
  - exfalso; apply Houtside; left; rewrite Hparent; discriminate.
  - assert (Hrep : fst (find E x uf) = x).
    { apply (reaches_unique E uf x); [exact (proj1 (proj2 (find_correct E x uf Hwf)))|].
      apply Root; exact Hparent. }
    unfold equiv in Hequiv; rewrite Hrep in Hequiv.
    pose proof (proj1 (proj2 (find_correct E y uf Hwf))) as Hpath.
    rewrite <- Hequiv in Hpath; destruct (path_support E uf y x Hwf Hpath) as [Heq|[_ Hsupport]].
    + exact Heq.
    + contradiction.
Qed.

Lemma touch_ranks {K} (E : encoding K) x uf a : rank_of E (touch E x uf) a = rank_of E uf a.
Proof.
  unfold touch; destruct (Map.get E x (ranks uf)) eqn:Hrank; [reflexivity|].
  unfold rank_of; cbn; destruct (key_dec E a x) as [Heq|Hne].
  - subst a; rewrite Map.get_set_same, Hrank; reflexivity.
  - rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Lemma touch_parents {K} (E : encoding K) x uf : parents (touch E x uf) = parents uf.
Proof.
  unfold touch; destruct (Map.get E x (ranks uf)); reflexivity.
Qed.

Lemma touch_wf {K} (E : encoding K) x uf : wf E uf -> wf E (touch E x uf).
Proof.
  intros [Hp [Hr [Hb Hs]]]; split; [rewrite touch_parents; exact Hp|].
  split.
  - unfold touch; destruct (Map.get E x (ranks uf)); [exact Hr|apply Map.wf_set; exact Hr].
  - split.
    + intro a; rewrite touch_ranks; unfold touch; destruct (Map.get E x (ranks uf)); apply Hb.
    + intros a b Hget; rewrite touch_parents in Hget; rewrite !touch_ranks; apply Hs; exact Hget.
Qed.

Lemma touch_reaches {K} (E : encoding K) x uf a b :
  reaches E (touch E x uf) a b <-> reaches E uf a b.
Proof.
  split; intro H; induction H; [apply Root|eapply Step|apply Root|eapply Step];
    try rewrite touch_parents in *; eassumption.
Qed.

Lemma touch_support {K} (E : encoding K) x uf a :
  support E (touch E x uf) a <-> a = x \/ support E uf a.
Proof.
  unfold support; rewrite touch_parents; unfold touch.
  destruct (Map.get E x (ranks uf)) eqn:Hrank.
  - destruct (key_dec E a x) as [Heq|Hne]; [subst a; rewrite Hrank|]; intuition discriminate.
  - cbn; destruct (key_dec E a x) as [Heq|Hne].
    + subst a; rewrite Map.get_set_same; intuition discriminate.
    + rewrite Map.get_set_other by exact Hne; tauto.
Qed.

Lemma touch_rep {K} (E : encoding K) x uf a : wf E uf ->
  fst (find E a (touch E x uf)) = fst (find E a uf).
Proof.
  intro Hwf; apply (reaches_unique E uf a).
  - apply (proj1 (touch_reaches E x uf a _)).
    exact (proj1 (proj2 (find_correct E a _ (touch_wf E x uf Hwf)))).
  - exact (proj1 (proj2 (find_correct E a uf Hwf))).
Qed.

Lemma link_parents {K} (E : encoding K) child root raise uf :
  parents (link E child root raise uf) = Map.set E child root (parents uf).
Proof.
  unfold link; destruct raise; reflexivity.
Qed.

Lemma link_rank_root {K} (E : encoding K) child root uf :
  rank_of E (link E child root true uf) root = S (rank_of E uf root).
Proof.
  unfold link, rank_of; cbn; rewrite Map.get_set_same; reflexivity.
Qed.

Lemma link_rank_other {K} (E : encoding K) child root uf a : a <> root ->
  rank_of E (link E child root true uf) a = rank_of E uf a.
Proof.
  intro Hne; unfold link, rank_of; cbn; rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Lemma link_raise_wf {K} (E : encoding K) child root uf :
  wf E uf -> child <> root -> Map.get E root (parents uf) = None ->
  rank_of E uf child <= rank_of E uf root -> wf E (link E child root true uf).
Proof.
  intros [Hp [Hr [Hbound Hstep]]] Hne Hroot Hrank; split.
  - apply Map.wf_set; exact Hp.
  - split; [apply Map.wf_set; exact Hr|]; split.
    + intro a; destruct (key_dec E a root) as [Heq|Har].
      * subst a; rewrite link_rank_root; apply Nat.le_max_r.
      * rewrite link_rank_other by exact Har.
        eapply Nat.le_trans; [apply Hbound|apply Nat.le_max_l].
    + intros a b Hget; rewrite link_parents in Hget.
      destruct (key_dec E a child) as [Heq|Hac].
      * subst a; rewrite Map.get_set_same in Hget; inversion Hget; subst b.
        rewrite link_rank_root, link_rank_other by exact Hne; lia.
      * rewrite Map.get_set_other in Hget by exact Hac.
        assert (Har : a <> root) by (intro Heq; subst a; congruence).
        rewrite link_rank_other by exact Har.
        specialize (Hstep a b Hget).
        destruct (key_dec E b root) as [Heq|Hbr].
        -- subst b; rewrite link_rank_root; lia.
        -- rewrite link_rank_other by exact Hbr; exact Hstep.
Qed.

Lemma link_path {K} (E : encoding K) child root raise uf :
  child <> root -> Map.get E child (parents uf) = None ->
  Map.get E root (parents uf) = None -> forall a b,
  reaches E uf a b -> reaches E (link E child root raise uf) a
    (if key_eqb E b child then root else b).
Proof.
  intros Hne Hchild Hroot a b Hpath; induction Hpath as [a Hnone|a y b Hparent Htail IH].
  - destruct (key_eqb E a child) eqn:Heq.
    + apply key_eqb_spec in Heq; subst a.
      apply (Step E _ child root root).
      * rewrite link_parents; apply Map.get_set_same.
      * apply Root; rewrite link_parents, Map.get_set_other by congruence; exact Hroot.
    + apply Root; rewrite link_parents, Map.get_set_other.
      * exact Hnone.
      * intro Hequal; subst a; rewrite (proj2 (key_eqb_spec E child child) eq_refl) in Heq.
        discriminate.
  - apply (Step E _ a y _); [|exact IH].
    rewrite link_parents, Map.get_set_other; [exact Hparent|].
    intro Heq; subst a; congruence.
Qed.

Lemma link_rep {K} (E : encoding K) child root raise uf a :
  wf E uf -> wf E (link E child root raise uf) -> child <> root ->
  Map.get E child (parents uf) = None -> Map.get E root (parents uf) = None ->
  fst (find E a (link E child root raise uf)) =
    if key_eqb E (fst (find E a uf)) child then root else fst (find E a uf).
Proof.
  intros Hwf Hnew Hne Hchild Hroot.
  apply (reaches_unique E (link E child root raise uf) a).
  - exact (proj1 (proj2 (find_correct E a _ Hnew))).
  - apply link_path; try assumption; exact (proj1 (proj2 (find_correct E a uf Hwf))).
Qed.

Lemma find_state {K} (E : encoding K) x uf root uf' :
  wf E uf -> find E x uf = (root, uf') ->
  wf E uf' /\ Map.get E root (parents uf') = None /\
  root = fst (find E x uf) /\
  (forall a, fst (find E a uf') = fst (find E a uf)) /\
  (forall a, support E uf' a <-> support E uf a).
Proof.
  intros Hwf Hfind; pose proof (find_correct E x uf Hwf) as Hcorrect.
  rewrite Hfind in Hcorrect; cbn in Hcorrect; destruct Hcorrect as [Hwf' [Hpath Hagree]].
  split; [exact Hwf'|]; split.
  - eapply reaches_root; apply Hagree; exact Hpath.
  - split; [rewrite Hfind; reflexivity|]; split.
    + intro a; pose proof (find_rep_stable E uf a x Hwf) as Hstable.
      rewrite Hfind in Hstable; exact Hstable.
    + intro a; pose proof (find_support E x uf a) as Hsupport.
      rewrite Hfind in Hsupport; exact Hsupport.
Qed.

Lemma two_finds {K} (E : encoding K) uf x y rx u1 ry u2 :
  wf E uf -> find E x uf = (rx, u1) -> find E y u1 = (ry, u2) ->
  wf E u2 /\ Map.get E rx (parents u2) = None /\ Map.get E ry (parents u2) = None /\
  rx = fst (find E x uf) /\ ry = fst (find E y uf) /\
  (forall a, fst (find E a u2) = fst (find E a uf)) /\
  (forall a, support E u2 a <-> support E uf a).
Proof.
  intros Hwf Hx Hy.
  destruct (find_state E x uf rx u1 Hwf Hx) as [Hwf_after_x [Hrx [Hrxrep [Hstable1 Hsupport1]]]].
  destruct (find_state E y u1 ry u2 Hwf_after_x Hy)
    as [Hwf_after_y [Hry [Hryrep [Hstable2 Hsupport2]]]].
  split; [exact Hwf_after_y|]; split.
  - pose proof (proj2 (proj2 (find_correct E y u1 Hwf_after_x)) rx rx) as Hagree.
    rewrite Hy in Hagree; cbn in Hagree.
    apply (reaches_root E u2 rx rx); apply Hagree; apply Root; exact Hrx.
  - split; [exact Hry|]; split; [exact Hrxrep|]; split.
    + rewrite Hryrep; apply Hstable1.
    + split.
      * intro a; rewrite Hstable2, Hstable1; reflexivity.
      * intro a; rewrite Hsupport2, Hsupport1; reflexivity.
Qed.

(** Union by rank preserves the forest invariant. *)
Theorem wf_union {K} (E : encoding K) uf x y : wf E uf -> wf E (union E x y uf).
Proof.
  intro Hwf; unfold union.
  destruct (find E x uf) as [rx u1] eqn:Hx.
  destruct (find E y u1) as [ry u2] eqn:Hy.
  destruct (two_finds E uf x y rx u1 ry u2 Hwf Hx Hy)
    as [Hwf_after_y [Hrx [Hry [Hrxrep [Hryrep [Hstable Hsupport]]]]]].
  destruct (key_eqb E rx ry) eqn:Heq.
  - apply touch_wf; exact Hwf_after_y.
  - assert (Hne : rx <> ry).
    { intro Hsame; assert (Htrue : key_eqb E rx ry = true) by
        (apply key_eqb_spec; exact Hsame); congruence. }
    destruct (Nat.compare (rank_of E u2 rx) (rank_of E u2 ry)) eqn:Hcmp.
    + apply Nat.compare_eq_iff in Hcmp.
      apply link_raise_wf; [exact Hwf_after_y|congruence|exact Hrx|lia].
    + apply Nat.compare_lt_iff in Hcmp; apply redirect_wf; assumption.
    + apply Nat.compare_gt_iff in Hcmp; apply redirect_wf; assumption.
Qed.

(** The boolean test agrees with equivalence and preserves every class. *)
Theorem equivb_correct {K} (E : encoding K) uf x y : wf E uf ->
  (fst (equivb E x y uf) = true <-> equiv E uf x y) /\
  wf E (snd (equivb E x y uf)) /\
  (forall a b, equiv E (snd (equivb E x y uf)) a b <-> equiv E uf a b).
Proof.
  intro Hwf; unfold equivb.
  destruct (find E x uf) as [rx u1] eqn:Hx.
  destruct (find E y u1) as [ry u2] eqn:Hy.
  destruct (two_finds E uf x y rx u1 ry u2 Hwf Hx Hy)
    as [Hwf_after_y [Hrx [Hry [Hrxrep [Hryrep [Hstable Hsupport]]]]]].
  cbn; split.
  - rewrite key_eqb_spec, Hrxrep, Hryrep; reflexivity.
  - split; [exact Hwf_after_y|]; intros a b; unfold equiv; rewrite !Hstable; reflexivity.
Qed.

Lemma key_eqb_false {K} (E : encoding K) x y : key_eqb E x y = false <-> x <> y.
Proof.
  destruct (key_eqb E x y) eqn:Heq; split; intro H; try discriminate; try reflexivity.
  - apply key_eqb_spec in Heq; contradiction.
  - intro Hsame; subst y; rewrite (proj2 (key_eqb_spec E x x) eq_refl) in Heq; discriminate.
Qed.

Definition collapse {K} (E : encoding K) (child root a : K) : K :=
  if key_eqb E a child then root else a.

Lemma collapse_equal {K} (E : encoding K) child root a b : child <> root ->
  (collapse E child root a = collapse E child root b <->
    a = b \/ (a = child /\ root = b) \/ (a = root /\ child = b)).
Proof.
  intro Hne; unfold collapse.
  destruct (key_eqb E a child) eqn:Ha, (key_eqb E b child) eqn:Hb;
    try apply key_eqb_spec in Ha; try apply key_eqb_spec in Hb;
    try apply key_eqb_false in Ha; try apply key_eqb_false in Hb; intuition congruence.
Qed.

Lemma link_equiv {K} (E : encoding K) child root raise uf a b :
  wf E uf -> wf E (link E child root raise uf) -> child <> root ->
  Map.get E child (parents uf) = None -> Map.get E root (parents uf) = None ->
  (equiv E (link E child root raise uf) a b <-> equiv E uf a b \/
    (fst (find E a uf) = child /\ root = fst (find E b uf)) \/
    (fst (find E a uf) = root /\ child = fst (find E b uf))).
Proof.
  intros Hwf Hnew Hne Hchild Hroot; unfold equiv.
  rewrite !link_rep by assumption; apply collapse_equal; exact Hne.
Qed.

(** Union merges exactly the two argument classes. *)
Theorem union_equiv {K} (E : encoding K) uf x y a b : wf E uf ->
  (equiv E (union E x y uf) a b <-> equiv E uf a b \/
    (equiv E uf a x /\ equiv E uf y b) \/ (equiv E uf a y /\ equiv E uf x b)).
Proof.
  intro Hwf; pose proof (wf_union E uf x y Hwf) as Hnew.
  unfold union in *.
  destruct (find E x uf) as [rx u1] eqn:Hx.
  destruct (find E y u1) as [ry u2] eqn:Hy.
  destruct (two_finds E uf x y rx u1 ry u2 Hwf Hx Hy)
    as [Hwf_after_y [Hrx [Hry [Hrxrep [Hryrep [Hstable Hsupport]]]]]].
  destruct (key_eqb E rx ry) eqn:Heq.
  - apply key_eqb_spec in Heq; unfold equiv.
    rewrite !touch_rep by exact Hwf_after_y; rewrite !Hstable.
    rewrite <- Hrxrep, <- Hryrep; subst ry; intuition congruence.
  - apply key_eqb_false in Heq.
    destruct (Nat.compare (rank_of E u2 rx) (rank_of E u2 ry)) eqn:Hcmp.
    + rewrite (link_equiv E ry rx true u2 a b) by (try assumption; congruence).
      unfold equiv; rewrite !Hstable, <- Hrxrep, <- Hryrep; tauto.
    + rewrite (link_equiv E rx ry false u2 a b) by assumption.
      unfold equiv; rewrite !Hstable, <- Hrxrep, <- Hryrep; tauto.
    + rewrite (link_equiv E ry rx false u2 a b) by (try assumption; congruence).
      unfold equiv; rewrite !Hstable, <- Hrxrep, <- Hryrep; tauto.
Qed.

Definition merged {K} (R : K -> K -> Prop) (x y a b : K) : Prop :=
  R a b \/ (R a x /\ R y b) \/ (R a y /\ R x b).

Lemma merged_equivalence {K} (R : K -> K -> Prop) x y :
  equivalence K R -> equivalence K (merged R x y).
Proof.
  intros [Hrefl Htrans Hsym]; constructor.
  - intro a; left; apply Hrefl.
  - intros a b c [Hab|[[Hax Hyb]|[Hay Hxb]]] [Hbc|[[Hbx Hyc]|[Hby Hxc]]];
      unfold merged; eauto 5.
  - intros a b [Hab|[[Hax Hyb]|[Hay Hxb]]].
    + left; apply Hsym; exact Hab.
    + right; right; split; apply Hsym; assumption.
    + right; left; split; apply Hsym; assumption.
Qed.

Lemma closure_equivalence {K} (R : K -> K -> Prop) :
  equivalence K (clos_refl_sym_trans K R).
Proof.
  constructor; [intro x; apply rst_refl|
    intros x y z Hxy Hyz; eapply rst_trans; eassumption|
    intros x y H; apply rst_sym; exact H].
Qed.

Lemma closure_mono {K} (R S : K -> K -> Prop) :
  (forall x y, R x y -> S x y) -> forall a b,
  clos_refl_sym_trans K R a b -> clos_refl_sym_trans K S a b.
Proof.
  intros Hincl a b Hpath; induction Hpath.
  - apply rst_step; apply Hincl; assumption.
  - apply rst_refl.
  - apply rst_sym; assumption.
  - eapply rst_trans; eassumption.
Qed.

Lemma closure_snoc {K} (l : list (K * K)) x y a b :
  clos_refl_sym_trans K (fun a b => In (a, b) (l ++ [(x, y)])) a b <->
  merged (clos_refl_sym_trans K (fun a b => In (a, b) l)) x y a b.
Proof.
  set (R := clos_refl_sym_trans K (fun a b => In (a, b) l)).
  assert (Hmerged : equivalence K (merged R x y)) by
    (apply merged_equivalence; apply closure_equivalence).
  destruct Hmerged as [Hrefl Htrans Hsym]; split.
  - intro Hpath; induction Hpath as [u v Hpair|u|u v Hpath IH|u v w Huv IHuv Hvw IHvw].
    + apply in_app_iff in Hpair; destruct Hpair as [Hold|Hnew].
      * left; apply rst_step; exact Hold.
      * cbn in Hnew; destruct Hnew as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
        right; left; split; apply rst_refl.
    + apply Hrefl.
    + apply Hsym; exact IH.
    + eapply Htrans; eassumption.
  - assert (Hembed : forall u v, R u v ->
        clos_refl_sym_trans K (fun a b => In (a, b) (l ++ [(x, y)])) u v).
    { apply closure_mono; intros u v Hin; apply in_or_app; left; exact Hin. }
    assert (Hxy : clos_refl_sym_trans K (fun a b => In (a, b) (l ++ [(x, y)])) x y).
    { apply rst_step; apply in_or_app; right; cbn; auto. }
    intros [Hab|[[Hax Hyb]|[Hay Hxb]]].
    + apply Hembed; exact Hab.
    + eapply rst_trans; [apply Hembed; exact Hax|].
      eapply rst_trans; [exact Hxy|apply Hembed; exact Hyb].
    + eapply rst_trans; [apply Hembed; exact Hay|].
      eapply rst_trans; [apply rst_sym; exact Hxy|apply Hembed; exact Hxb].
Qed.

Lemma of_unions_wf {K} (E : encoding K) l : wf E (of_unions E l).
Proof.
  unfold of_unions; generalize (@make K) (wf_make E).
  induction l as [|[x y] l IH]; intros uf Hwf; cbn; [exact Hwf|].
  apply IH; apply wf_union; exact Hwf.
Qed.

(** The generated partition is the equivalence closure of all union pairs. *)
Theorem of_unions_equiv {K} (E : encoding K) a b l :
  equiv E (of_unions E l) a b <->
  clos_refl_sym_trans K (fun x y => In (x, y) l) a b.
Proof.
  revert a b; induction l using rev_ind; intros a b.
  - rewrite make_equiv; split.
    + intro Heq; subst b; apply rst_refl.
    + intro Hpath; induction Hpath as [u v Hempty|u|u v Hpath IH|
        u v w Huv IHuv Hvw IHvw].
      * contradiction.
      * reflexivity.
      * symmetry; exact IH.
      * etransitivity; eassumption.
  - destruct x as [x y]; unfold of_unions at 1; rewrite fold_left_app; cbn.
    fold (of_unions E l); rewrite union_equiv by apply of_unions_wf.
    rewrite closure_snoc; unfold merged; rewrite !IHl; reflexivity.
Qed.

Lemma link_support {K} (E : encoding K) child root raise uf z :
  support E (link E child root raise uf) z <->
    z = child \/ (raise = true /\ z = root) \/ support E uf z.
Proof.
  unfold support, link, redirect; destruct raise; cbn.
  - destruct (key_dec E z child) as [Heq|Hne].
    + subst z; rewrite Map.get_set_same; intuition discriminate.
    + rewrite Map.get_set_other by exact Hne.
      destruct (key_dec E z root) as [Heq|Hnr].
      * subst z; rewrite Map.get_set_same; intuition discriminate.
      * rewrite Map.get_set_other by exact Hnr; intuition discriminate.
  - destruct (key_dec E z child) as [Heq|Hne].
    + subst z; rewrite Map.get_set_same; intuition discriminate.
    + rewrite Map.get_set_other by exact Hne; intuition discriminate.
Qed.

Lemma roots_support {K} (E : encoding K) uf x y rx ry z :
  wf E uf -> reaches E uf x rx -> reaches E uf y ry ->
  (z = rx \/ z = ry \/ support E uf z <-> z = x \/ z = y \/ support E uf z).
Proof.
  intros Hwf Hx Hy.
  destruct (path_support E uf x rx Hwf Hx) as [Hxroot|[Hsx Hsrx]];
    destruct (path_support E uf y ry Hwf Hy) as [Hyroot|[Hsy Hsry]];
    intuition congruence.
Qed.

Lemma union_support {K} (E : encoding K) uf x y z : wf E uf ->
  (support E (union E x y uf) z <-> z = x \/ z = y \/ support E uf z).
Proof.
  intro Hwf; unfold union.
  destruct (find E x uf) as [rx u1] eqn:Hx.
  destruct (find E y u1) as [ry u2] eqn:Hy.
  destruct (two_finds E uf x y rx u1 ry u2 Hwf Hx Hy)
    as [Hwf_after_y [Hrx [Hry [Hrxrep [Hryrep [Hstable Hsupport]]]]]].
  assert (Hpaths : reaches E uf x rx /\ reaches E uf y ry).
  { rewrite Hrxrep, Hryrep; split; apply (proj1 (proj2 (find_correct E _ uf Hwf))). }
  destruct Hpaths as [Hpathx Hpathy].
  rewrite <- (roots_support E uf x y rx ry z Hwf Hpathx Hpathy).
  rewrite <- (Hsupport z).
  destruct (key_eqb E rx ry) eqn:Heq.
  - apply key_eqb_spec in Heq; rewrite touch_support, <- Heq; tauto.
  - destruct (Nat.compare (rank_of E u2 rx) (rank_of E u2 ry)) eqn:Hcmp;
      rewrite link_support.
    + intuition.
    + apply Nat.compare_lt_iff in Hcmp.
      assert (Hsry : support E u2 ry) by (apply positive_rank_support; lia).
      intuition congruence.
    + apply Nat.compare_gt_iff in Hcmp.
      assert (Hsrx : support E u2 rx) by (apply positive_rank_support; lia).
      intuition congruence.
Qed.

(** Union records precisely its two arguments in addition to existing support. *)
Theorem keys_union {K} (E : encoding K) uf x y z : wf E uf ->
  (In z (keys E (union E x y uf)) <-> z = x \/ z = y \/ In z (keys E uf)).
Proof.
  intro Hwf; rewrite !keys_spec by (try exact Hwf; apply wf_union; exact Hwf).
  apply union_support; exact Hwf.
Qed.

End UnionFind.
Import UnionFind.
