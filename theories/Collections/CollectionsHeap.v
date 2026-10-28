(** * Persistent priority queues

    A rank-position binomial heap indexes a live map, retaining obsolete entries after decreases.
    For example, pushing a key at priorities 5 and 2 leaves only priority 2 live.
    Builds on: CollectionsEncoding, CollectionsMap. *)

From Stdlib Require Import List Bool PArith PeanoNat Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap.
Import List.ListNotations.

Module PQueue.

(** Priority order breaks ties by encoded key. *)
Definition before (p1 c1 p2 c2 : positive) : Prop :=
  (p1 < p2)%positive \/ (p1 = p2 /\ (c1 <= c2)%positive).

Definition entry (K : Type) := (positive * positive * K)%type.

Definition precedes {K} (a b : entry K) : Prop :=
  before (fst (fst a)) (snd (fst a)) (fst (fst b)) (snd (fst b)).

Definition precedesb {K} (a b : entry K) : bool :=
  (Pos.ltb (fst (fst a)) (fst (fst b)) ||
    (Pos.eqb (fst (fst a)) (fst (fst b)) &&
      Pos.leb (snd (fst a)) (snd (fst b))))%bool.

Lemma precedesb_spec {K} (a b : entry K) : precedesb a b = true <-> precedes a b.
Proof.
  unfold precedesb, precedes, before.
  rewrite Bool.orb_true_iff, Bool.andb_true_iff, Pos.ltb_lt, Pos.eqb_eq, Pos.leb_le.
  reflexivity.
Qed.

Lemma precedes_refl {K} (a : entry K) : precedes a a.
Proof.
  unfold precedes, before; right; split; [reflexivity|apply Pos.le_refl].
Qed.

Lemma precedes_trans {K} (a b c : entry K) :
  precedes a b -> precedes b c -> precedes a c.
Proof.
  unfold precedes, before; intros [Hab|[Hab Hcab]] [Hbc|[Hbc Hcbc]];
    try (left; lia); right; split; lia.
Qed.

Lemma precedesb_false {K} (a b : entry K) : precedesb a b = false -> precedes b a.
Proof.
  unfold precedesb, precedes, before.
  rewrite Bool.orb_false_iff, Bool.andb_false_iff, Pos.ltb_ge.
  intros [Hge [Hne|Hlt]].
  - apply Pos.eqb_neq in Hne; left; lia.
  - apply Pos.leb_gt in Hlt.
    destruct (Pos.eq_dec (fst (fst a)) (fst (fst b))) as [Heq|Hne].
    + right; split; lia.
    + left; lia.
Qed.

Scheme All for list.

(** A binomial tree stores its root and its children in decreasing rank order. *)
Inductive tree (K : Type) : Type :=
  | Tree (top : entry K) (children : list (tree K)).

Arguments Tree {K}.

Definition root {K} (t : tree K) : entry K :=
  match t with
  | Tree e _ => e
  end.

Fixpoint tree_entries {K} (t : tree K) : list (entry K) :=
  match t with
  | Tree e cs => e :: flat_map tree_entries cs
  end.

Definition tree_all {K} (P : entry K -> Prop) (t : tree K) : Prop :=
  forall e, In e (tree_entries t) -> P e.

(** Linking equal-rank trees uses one entry comparison and constant structural work. *)
Definition link {K} (a b : tree K) : tree K :=
  match a, b with
  | Tree e cs, Tree e' cs' =>
    if precedesb e e' then Tree e (b :: cs) else Tree e' (a :: cs')
  end.

(** Rank is a proof index, never an executable cache or comparison argument. *)
Inductive valid {K} (P : entry K -> Prop) : nat -> tree K -> Prop :=
  | Valid_zero e : P e -> valid P 0 (Tree e [])
  | Valid_link r e cs b :
      valid P r (Tree e cs) ->
      valid P r b ->
      tree_all (precedes e) b ->
      valid P (S r) (Tree e (b :: cs)).

Definition heap (K : Type) := list (option (tree K)).

Definition slot_entries {K} (s : option (tree K)) : list (entry K) :=
  match s with
  | None => []
  | Some t => tree_entries t
  end.

Fixpoint entries {K} (h : heap K) : list (entry K) :=
  match h with
  | [] => []
  | s :: hs => slot_entries s ++ entries hs
  end.

(** Counts are specification-only; the queue supplies the executable pop fuel. *)
Definition heap_count {K} (h : heap K) : nat := length (entries h).

Fixpoint forest_valid {K} (P : entry K -> Prop) r (h : heap K) : Prop :=
  match h with
  | [] => True
  | s :: hs =>
    (match s with None => True | Some t => valid P r t end) /\
    forest_valid P (S r) hs /\ (s <> None \/ hs <> [])
  end.

(** Smart cons removes only a trailing empty slot, in constant work. *)
Definition digit {K} (s : option (tree K)) (hs : heap K) : heap K :=
  match s, hs with
  | None, [] => []
  | _, _ => s :: hs
  end.

Fixpoint insert {K} (t : tree K) (h : heap K) : heap K :=
  match h with
  | [] => [Some t]
  | None :: hs => Some t :: hs
  | Some u :: hs => None :: insert (link t u) hs
  end.

(** Full-adder merging processes each position once, with at most one link per position. *)
Fixpoint meld {K} (a : heap K) : heap K -> option (tree K) -> heap K :=
  match a with
  | [] => fun b carry => match carry with None => b | Some t => insert t b end
  | x :: xs => fun b carry =>
    match b with
    | [] => match carry with None => a | Some t => insert t a end
    | y :: ys =>
      match x, y, carry with
      | None, None, c => digit c (meld xs ys None)
      | Some t, None, None | None, Some t, None => digit (Some t) (meld xs ys None)
      | Some t, Some u, None
      | Some t, None, Some u
      | None, Some t, Some u => digit None (meld xs ys (Some (link t u)))
      | Some t, Some u, Some c => digit (Some c) (meld xs ys (Some (link t u)))
      end
    end
  end.

Definition merge {K} (a b : heap K) : heap K := meld a b None.

(** Root selection returns the winning tree and a forest with just that root tree removed. *)
Fixpoint select {K} (h : heap K) : option (tree K * heap K) :=
  match h with
  | [] => None
  | x :: xs =>
    match select xs with
    | None => match x with None => None | Some t => Some (t, []) end
    | Some (t, rest) =>
      match x with
      | None => Some (t, digit None rest)
      | Some u =>
        if precedesb (root u) (root t) then Some (u, digit None xs)
        else Some (t, digit (Some u) rest)
      end
    end
  end.

(** Reversing the descending child list puts each child at its rank position. *)
Definition children_heap {K} (t : tree K) : heap K :=
  match t with
  | Tree _ cs => List.map (@Some (tree K)) (rev_append cs [])
  end.

Definition remove_min {K} (h : heap K) : option (entry K * heap K) :=
  match select h with
  | None => None
  | Some (t, rest) => Some (root t, merge (children_heap t) rest)
  end.

Lemma entries_digit {K} s (h : heap K) :
  entries (digit s h) = slot_entries s ++ entries h.
Proof.
  destruct s, h; reflexivity.
Qed.

Lemma valid_digit {K} P r s (h : heap K) :
  (match s with None => True | Some t => valid P r t end) ->
  forest_valid P (S r) h -> forest_valid P r (digit s h).
Proof.
  destruct s as [t|], h as [|x xs]; cbn; intros Hs Hh.
  - split; [exact Hs|]; split; [exact I|left; discriminate].
  - split; [exact Hs|]; split; [exact Hh|left; discriminate].
  - exact I.
  - split; [exact I|]; split; [exact Hh|right; discriminate].
Qed.

Lemma entries_link {K} (a b : tree K) e :
  In e (tree_entries (link a b)) <-> In e (tree_entries a) \/ In e (tree_entries b).
Proof.
  destruct a as [x xs], b as [y ys]; unfold link; destruct (precedesb x y);
    cbn; rewrite in_app_iff; intuition congruence.
Qed.

Lemma count_link {K} (a b : tree K) :
  length (tree_entries (link a b)) = length (tree_entries a) + length (tree_entries b).
Proof.
  destruct a as [x xs], b as [y ys]; unfold link; destruct (precedesb x y);
    cbn; rewrite length_app; cbn; lia.
Qed.

Lemma valid_root {K} P r (t : tree K) :
  valid P r t -> tree_all (precedes (root t)) t.
Proof.
  intro Hvalid; induction Hvalid as [e He|r e cs b Hbase IH Hchild IHchild Hbefore];
    intros a Hin; cbn in *.
  - destruct Hin as [Heq|Hfalse]; [subst; apply precedes_refl|contradiction].
  - destruct Hin as [Heq|Hin]; [subst; apply precedes_refl|].
    apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    + apply Hbefore; exact Hin.
    + apply IH; right; exact Hin.
Qed.

Lemma valid_all {K} P r (t : tree K) : valid P r t -> tree_all P t.
Proof.
  intro Hvalid; induction Hvalid as [e He|r e cs b Hbase IH Hchild IHchild Hbefore];
    intros a Hin; cbn in Hin.
  - destruct Hin as [Heq|Hfalse]; [subst; exact He|contradiction].
  - destruct Hin as [Heq|Hin].
    + apply IH; left; exact Heq.
    + apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
      * apply IHchild; exact Hin.
      * apply IH; right; exact Hin.
Qed.

Lemma valid_link {K} P r (a b : tree K) :
  valid P r a -> valid P r b -> valid P (S r) (link a b).
Proof.
  intros Ha Hb; destruct a as [e cs], b as [e' cs']; unfold link.
  destruct (precedesb e e') eqn:Hcmp; apply Valid_link; try assumption.
  - intros x Hin; eapply precedes_trans.
    + apply precedesb_spec; exact Hcmp.
    + apply (valid_root P r (Tree e' cs') Hb); exact Hin.
  - intros x Hin; eapply precedes_trans.
    + apply precedesb_false; exact Hcmp.
    + apply (valid_root P r (Tree e cs) Ha); exact Hin.
Qed.

Lemma entries_insert {K} (t : tree K) h e :
  In e (entries (insert t h)) <-> In e (tree_entries t) \/ In e (entries h).
Proof.
  revert t; induction h as [|[u|] hs IH]; intro t;
    cbn [insert entries slot_entries flat_map app length].
  - cbn [entries slot_entries flat_map app length]; rewrite app_nil_r; cbn; tauto.
  - rewrite IH, entries_link; cbn [entries slot_entries flat_map app length];
      rewrite in_app_iff; cbn; tauto.
  - cbn [entries slot_entries flat_map app length]; rewrite in_app_iff; cbn; tauto.
Qed.

Lemma count_insert {K} (t : tree K) h :
  heap_count (insert t h) = length (tree_entries t) + heap_count h.
Proof.
  revert t; induction h as [|[u|] hs IH]; intro t;
    unfold heap_count in *; cbn [insert entries slot_entries flat_map app length].
  - rewrite app_nil_r; cbn; lia.
  - rewrite IH, count_link; cbn [entries slot_entries flat_map app length]; rewrite length_app; lia.
  - cbn [entries slot_entries flat_map app length]; rewrite length_app; lia.
Qed.

Lemma valid_insert {K} P r (t : tree K) h :
  valid P r t -> forest_valid P r h -> forest_valid P r (insert t h).
Proof.
  revert r t; induction h as [|[u|] hs IH]; intros r t Ht Hh; cbn in *.
  - split; [exact Ht|]; split; [exact I|left; discriminate].
  - destruct Hh as [Hu [Hhs Hnonempty]].
    split; [exact I|]; split.
    + apply IH; [apply valid_link; assumption|exact Hhs].
    + right; destruct hs as [|[v|] rest]; cbn; discriminate.
  - destruct Hh as [_ [Hhs Hnonempty]].
    split; [exact Ht|]; split; [exact Hhs|left; discriminate].
Qed.

Lemma entries_meld {K} (a b : heap K) c e :
  In e (entries (meld a b c)) <->
    In e (entries a) \/ In e (entries b) \/ In e (slot_entries c).
Proof.
  revert b c; induction a as [|[x|] xs IH]; intros b c.
  - destruct c; cbn [meld slot_entries entries flat_map app length];
      [rewrite entries_insert|]; cbn; tauto.
  - destruct b as [|[y|] ys]; [destruct c; cbn [meld app length]; try rewrite entries_insert;
      cbn [slot_entries entries flat_map app length]; cbn; tauto| |];
      destruct c; cbn [meld app length]; rewrite entries_digit;
      cbn [entries slot_entries flat_map app length]; rewrite ?in_app_iff, IH;
      cbn [slot_entries app length]; rewrite ?entries_link; cbn; tauto.
  - destruct b as [|[y|] ys]; [destruct c; cbn [meld app length]; try rewrite entries_insert;
      cbn [slot_entries entries flat_map app length]; cbn; tauto| |];
      destruct c; cbn [meld app length]; rewrite entries_digit;
      cbn [entries slot_entries flat_map app length]; rewrite ?in_app_iff, IH;
      cbn [slot_entries app length]; rewrite ?entries_link; cbn; tauto.
Qed.

Lemma count_digit {K} s (h : heap K) :
  heap_count (digit s h) = length (slot_entries s) + heap_count h.
Proof.
  unfold heap_count; rewrite entries_digit, length_app; reflexivity.
Qed.

Lemma count_meld {K} (a b : heap K) c :
  heap_count (meld a b c) =
    heap_count a + heap_count b + length (slot_entries c).
Proof.
  revert b c; induction a as [|[x|] xs IH]; intros b c.
  - destruct c; cbn [meld slot_entries]; [rewrite count_insert|];
      unfold heap_count; cbn [entries length]; lia.
  - destruct b as [|[y|] ys].
    + destruct c; cbn [meld]; try rewrite count_insert;
        unfold heap_count; cbn [entries slot_entries length]; lia.
    + destruct c; cbn [meld]; rewrite count_digit, IH;
        cbn [slot_entries]; rewrite count_link;
        unfold heap_count; cbn [entries slot_entries]; rewrite !length_app; lia.
    + destruct c; cbn [meld]; rewrite count_digit, IH;
        cbn [slot_entries]; rewrite ?count_link;
        unfold heap_count; cbn [entries slot_entries app length]; rewrite !length_app; lia.
  - destruct b as [|[y|] ys].
    + destruct c; cbn [meld]; try rewrite count_insert;
        unfold heap_count; cbn [entries slot_entries app length]; lia.
    + destruct c; cbn [meld]; rewrite count_digit, IH;
        cbn [slot_entries]; rewrite ?count_link;
        unfold heap_count; cbn [entries slot_entries app length]; rewrite !length_app; lia.
    + destruct c; cbn [meld]; rewrite count_digit, IH;
        unfold heap_count; cbn [entries slot_entries app length]; lia.
Qed.

Lemma valid_meld {K} P (a b : heap K) c r :
  forest_valid P r a -> forest_valid P r b ->
  (match c with None => True | Some t => valid P r t end) ->
  forest_valid P r (meld a b c).
Proof.
  revert b c r; induction a as [|[x|] xs IH]; intros b c r Ha Hb Hc.
  - destruct c; cbn [meld app length]; [apply valid_insert|]; assumption.
  - destruct Ha as [Hx [Hxs Hnonempty]].
    destruct b as [|[y|] ys].
    + destruct c; cbn [meld app length]; [apply valid_insert|]; cbn; auto.
    + destruct Hb as [Hy [Hys Hnonempty']].
      destruct c; cbn [meld app length]; apply valid_digit; auto;
        apply IH; auto; apply valid_link; assumption.
    + destruct Hb as [_ [Hys Hnonempty']].
      destruct c; cbn [meld app length]; apply valid_digit; auto;
        apply IH; auto; apply valid_link; assumption.
  - destruct Ha as [_ [Hxs Hnonempty]].
    destruct b as [|[y|] ys].
    + destruct c; cbn [meld app length]; [apply valid_insert|]; cbn; auto.
    + destruct Hb as [Hy [Hys Hnonempty']].
      destruct c; cbn [meld app length]; apply valid_digit; auto;
        apply IH; auto; apply valid_link; assumption.
    + destruct Hb as [_ [Hys Hnonempty']].
      destruct c; cbn [meld app length]; apply valid_digit; auto; apply IH; auto.
Qed.

Lemma select_entries {K} (h : heap K) :
  match select h with
  | None => entries h = []
  | Some (t, rest) =>
    (forall e, In e (entries h) <-> In e (tree_entries t) \/ In e (entries rest)) /\
    heap_count h = length (tree_entries t) + heap_count rest
  end.
Proof.
  induction h as [|[u|] xs IH]; cbn [select].
  - reflexivity.
  - destruct (select xs) as [[t rest]|] eqn:Hselect.
    + destruct IH as [Hin Hcount].
      destruct (precedesb (root u) (root t)); split.
      * intro e; rewrite entries_digit; cbn [entries slot_entries app];
          rewrite in_app_iff; cbn; tauto.
      * unfold heap_count at 1; cbn [entries slot_entries]; rewrite length_app.
        unfold heap_count; rewrite entries_digit; cbn [slot_entries app]; reflexivity.
      * intro e; rewrite entries_digit; cbn [entries slot_entries].
        rewrite !in_app_iff, Hin; cbn; tauto.
      * rewrite count_digit; unfold heap_count in *.
        cbn [entries slot_entries]; rewrite !length_app; lia.
    + split.
      * intro e; cbn [entries slot_entries]; rewrite IH, app_nil_r; cbn; tauto.
      * unfold heap_count; cbn [entries slot_entries]; rewrite IH, app_nil_r; cbn; lia.
  - destruct (select xs) as [[t rest]|] eqn:Hselect.
    + destruct IH as [Hin Hcount]; split.
      * intro e; rewrite entries_digit; cbn [entries slot_entries app]; apply Hin.
      * change (heap_count xs = length (tree_entries t) + heap_count (digit None rest)).
        rewrite count_digit; cbn [slot_entries length]; lia.
    + cbn [entries slot_entries app]; exact IH.
Qed.

Lemma select_valid {K} P r (h : heap K) :
  forest_valid P r h ->
  match select h with
  | None => h = []
  | Some (t, rest) => (exists rank, valid P rank t) /\ forest_valid P r rest
  end.
Proof.
  revert r; induction h as [|[u|] xs IH]; intros r Hh; cbn [select].
  - reflexivity.
  - destruct Hh as [Hu [Hxs Hnonempty]].
    specialize (IH (S r) Hxs); destruct (select xs) as [[t rest]|] eqn:Hselect.
    + destruct IH as [Ht Hrest].
      destruct (precedesb (root u) (root t)); split.
      * exists r; exact Hu.
      * apply valid_digit; [exact I|exact Hxs].
      * exact Ht.
      * apply valid_digit; assumption.
    + split; [exists r; exact Hu|exact I].
  - destruct Hh as [_ [Hxs Hnonempty]].
    specialize (IH (S r) Hxs); destruct (select xs) as [[t rest]|] eqn:Hselect.
    + destruct IH as [Ht Hrest]; split; [exact Ht|].
      apply valid_digit; [exact I|exact Hrest].
    + subst xs; destruct Hnonempty; contradiction.
Qed.

Lemma select_min {K} P r (h : heap K) t rest :
  forest_valid P r h -> select h = Some (t, rest) ->
  forall e, In e (entries h) -> precedes (root t) e.
Proof.
  revert r t rest; induction h as [|[u|] xs IH]; intros r t rest Hh Hselect e Hin.
  - discriminate.
  - destruct Hh as [Hu [Hxs Hnonempty]]; cbn [select] in Hselect.
    destruct (select xs) as [[v tail]|] eqn:Htail.
    + destruct (precedesb (root u) (root v)) eqn:Hcmp; inversion Hselect; subst t rest.
      * cbn [entries slot_entries] in Hin; apply in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        -- apply (valid_root P r u Hu); exact Hin.
        -- eapply precedes_trans; [apply precedesb_spec; exact Hcmp|].
           apply (IH (S r) v tail Hxs eq_refl); exact Hin.
      * cbn [entries slot_entries] in Hin; apply in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        -- eapply precedes_trans; [apply precedesb_false; exact Hcmp|].
           apply (valid_root P r u Hu); exact Hin.
        -- apply (IH (S r) v tail Hxs eq_refl); exact Hin.
    + inversion Hselect; subst t rest.
      pose proof (select_entries xs) as Hempty; rewrite Htail in Hempty.
      cbn [entries slot_entries] in Hin; rewrite Hempty, app_nil_r in Hin.
      apply (valid_root P r u Hu); exact Hin.
  - destruct Hh as [_ [Hxs Hnonempty]]; cbn [select] in Hselect.
    destruct (select xs) as [[v tail]|] eqn:Htail; [|discriminate].
    inversion Hselect; subst t rest; cbn [entries slot_entries app] in Hin.
    apply (IH (S r) v tail Hxs eq_refl); exact Hin.
Qed.

Lemma forest_append {K} P r (a b : heap K) :
  forest_valid P r a -> forest_valid P (r + length a) b ->
  forest_valid P r (a ++ b).
Proof.
  revert r; induction a as [|s xs IH]; intros r Ha Hb; cbn in *.
  - replace (r + 0) with r in Hb by lia; exact Hb.
  - destruct Ha as [Hs [Hxs Hnonempty]]; split; [exact Hs|]; split.
    + apply IH; [exact Hxs|].
      replace (S r + length xs) with (r + S (length xs)) by lia; exact Hb.
    + destruct Hnonempty as [Hsome|Htail]; [left; exact Hsome|].
      right; intro Heq; apply app_eq_nil in Heq; cbn; tauto.
Qed.

Lemma valid_children {K} P r (t : tree K) :
  valid P r t -> forest_valid P 0 (children_heap t) /\ length (children_heap t) = r.
Proof.
  intro Hvalid; induction Hvalid as [e He|r e cs b Hbase IH Hchild IHchild Hbefore].
  - split; [exact I|reflexivity].
  - destruct IH as [Hcs Hlength].
    unfold children_heap in *; rewrite <- !rev_alt in *.
    cbn [rev]; rewrite map_app; cbn [map].
    split.
    + apply forest_append; [exact Hcs|]; cbn.
      rewrite Hlength; split; [exact Hchild|]; split; [exact I|left; discriminate].
    + rewrite length_app; cbn; lia.
Qed.

Lemma entries_some {K} (ts : list (tree K)) :
  entries (List.map (@Some (tree K)) ts) = flat_map tree_entries ts.
Proof.
  induction ts as [|u us IH]; cbn [entries map slot_entries flat_map]; auto.
  rewrite IH; reflexivity.
Qed.

Lemma entries_children {K} (t : tree K) e :
  In e (tree_entries t) <-> e = root t \/ In e (entries (children_heap t)).
Proof.
  destruct t as [top cs]; cbn [tree_entries root In]; unfold children_heap.
  rewrite <- rev_alt.
  rewrite entries_some, !in_flat_map.
  split.
  - intros [Heq|[u [Hu Hin]]]; [left; congruence|right].
    exists u; split; [apply (proj1 (in_rev cs u)); exact Hu|exact Hin].
  - intros [Heq|[u [Hu Hin]]]; [left; congruence|right].
    exists u; split; [apply (proj2 (in_rev cs u)); exact Hu|exact Hin].
Qed.

Lemma count_children {K} (t : tree K) :
  length (tree_entries t) = S (heap_count (children_heap t)).
Proof.
  destruct t as [e cs]; cbn [tree_entries length]; f_equal.
  unfold heap_count, children_heap; rewrite <- rev_alt, entries_some.
  induction cs as [|u us IH]; cbn [flat_map rev]; [reflexivity|].
  rewrite flat_map_app, !length_app; cbn [flat_map]; rewrite app_nil_r; lia.
Qed.

(** Removing a minimum preserves all other entries, ranks and entry codes. *)
Lemma remove_min_correct {K} P (h : heap K) :
  forest_valid P 0 h ->
  match remove_min h with
  | None => entries h = []
  | Some (e, rest) =>
    P e /\ forest_valid P 0 rest /\
    (forall a, In a (entries h) <-> a = e \/ In a (entries rest)) /\
    heap_count h = S (heap_count rest) /\
    (forall a, In a (entries h) -> precedes e a)
  end.
Proof.
  intro Hvalid; unfold remove_min.
  pose proof (select_entries h) as Hentries.
  pose proof (select_valid P 0 h Hvalid) as Hshape.
  destruct (select h) as [[t rest]|] eqn:Hselect; [|exact Hentries].
  destruct Hentries as [Hin Hcount], Hshape as [[rank Htree] Hrest].
  split.
  - apply (valid_all P rank t Htree); destruct t; cbn; auto.
  - split.
    + unfold merge; apply valid_meld.
      * apply (proj1 (valid_children P rank t Htree)).
      * exact Hrest.
      * exact I.
    + split.
      * intro a; rewrite Hin, entries_children.
        unfold merge; rewrite entries_meld; cbn [slot_entries In]; tauto.
      * split.
        -- unfold merge; rewrite count_meld; cbn [slot_entries length].
           rewrite count_children in Hcount; lia.
        -- apply (select_min P 0 h t rest Hvalid Hselect).
Qed.

(** Each rank-r binomial tree has exactly two to the power r entries. *)
Lemma valid_size {K} P r (t : tree K) :
  valid P r t -> length (tree_entries t) = 2 ^ r.
Proof.
  intro Hvalid; induction Hvalid as [e He|r e cs b Hbase IH Hchild IHchild Hbefore].
  - reflexivity.
  - cbn [tree_entries flat_map length] in *; rewrite length_app.
    rewrite Nat.pow_succ_r; lia.
Qed.

(** A nonempty canonical forest has a highest occupied position, so its width is logarithmic. *)
Lemma forest_height_bound {K} P r (h : heap K) :
  forest_valid P r h -> h <> [] -> 2 ^ (r + length h) <= 2 * heap_count h.
Proof.
  revert r; induction h as [|[t|] hs IH]; intros r Hforest Hnonempty.
  - contradiction.
  - destruct Hforest as [Ht [Hhs Hlast]].
    destruct hs as [|s ss].
    + cbn [length]; rewrite Nat.add_1_r, Nat.pow_succ_r by lia.
      unfold heap_count; cbn [entries slot_entries]; rewrite app_nil_r.
      rewrite (valid_size P r t Ht); lia.
    + specialize (IH (S r) Hhs ltac:(discriminate)).
      replace (S r + length (s :: ss)) with (r + length (Some t :: s :: ss)) in IH by
        (cbn; lia).
      unfold heap_count in *; cbn [entries slot_entries] in IH |- *;
        rewrite !length_app in *; lia.
  - destruct Hforest as [_ [Hhs Hlast]].
    destruct hs as [|s ss].
    + destruct Hlast; contradiction.
    + specialize (IH (S r) Hhs ltac:(discriminate)).
      replace (S r + length (s :: ss)) with (r + length (None :: s :: ss)) in IH by
        (cbn; lia).
      exact IH.
Qed.

(** A selected tree's child-list length is its occupied rank position inside the forest. *)
Lemma select_rank_bounds {K} P r (h : heap K) t rest :
  forest_valid P r h -> select h = Some (t, rest) ->
  r <= length (children_heap t) /\ length (children_heap t) < r + length h.
Proof.
  revert r t rest; induction h as [|[u|] xs IH]; intros r t rest Hh Hselect.
  - discriminate.
  - destruct Hh as [Hu [Hxs Hlast]]; cbn [select] in Hselect.
    pose proof (proj2 (valid_children P r u Hu)) as Hrank.
    destruct (select xs) as [[v tail]|] eqn:Htail.
    + destruct (precedesb (root u) (root v)); inversion Hselect; subst t rest.
      * rewrite Hrank; cbn [length]; lia.
      * specialize (IH (S r) v tail Hxs eq_refl); cbn [length]; lia.
    + inversion Hselect; subst t rest; rewrite Hrank; cbn [length]; lia.
  - destruct Hh as [_ [Hxs Hlast]]; cbn [select] in Hselect.
    destruct (select xs) as [[v tail]|] eqn:Htail; [|discriminate].
    inversion Hselect; subst t rest.
    specialize (IH (S r) v tail Hxs eq_refl); cbn [length]; lia.
Qed.

(** Each call visits at most one slot per carry or merge position.  Insertion visits at
    most [length h + 1] positions; melding visits at most [max (length a) (length b) + 1].
    Each position does constant constructor/branch work and at most one [precedesb].
    Selection visits [length h] positions and does at most that many comparisons.
    [children_heap] uses two linear passes over the selected tree's children; [rev_append]
    avoids the quadratic work of repeated append.  The rank and height lemmas above bound
    all these widths by O(log(2+n)) on every well-formed input, including persistent branches.
    Cached unary counters use only successor/predecessor, never subtree-sized arithmetic.
    Comparison bit work, encoding, and live-map operations are charged separately. *)

(** The queue caches the live-key count and total number of pending heap entries. *)
Record t (K : Type) : Type := Queue {
  pending : heap K;
  live : Map.t K positive;
  live_count : nat;
  pending_count : nat
}.

Arguments Queue {K}.
Arguments pending {K}.
Arguments live {K}.
Arguments live_count {K}.
Arguments pending_count {K}.

(** Empty queues have no pending or live entry. *)
Definition empty {K} : t K := Queue [] Map.empty 0 0.

(** Emptiness observes the live map. *)
Definition is_empty {K} (q : t K) : bool := Map.is_empty (live q).

(** Size reads the cached number of live keys. *)
Definition size {K} (q : t K) : nat := live_count q.

(** Priority reads the live map, ignoring obsolete heap entries. *)
Definition priority {K} (E : encoding K) (k : K) (q : t K) : option positive :=
  Map.get E k (live q).

(** Members enumerate the live bindings. *)
Definition members {K} (q : t K) : list (K * positive) := Map.elements (live q).

(** Ranked, ordered, correctly encoded trees cover the live map and agree with both caches. *)
Definition wf {K} (E : encoding K) (q : t K) : Prop :=
  forest_valid (fun e => snd (fst e) = encode E (snd e)) 0 (pending q) /\
  Map.wf E (live q) /\
  (forall k p, priority E k q = Some p -> In (p, encode E k, k) (entries (pending q))) /\
  live_count q = Map.size (live q) /\ pending_count q = heap_count (pending q).

(** Push inserts only a new or strictly lowered live priority. *)
Definition push {K} (E : encoding K) (p : positive) (k : K) (q : t K) : t K :=
  match priority E k q with
  | None => Queue (insert (Tree (p, encode E k, k) []) (pending q))
      (Map.set E k p (live q)) (S (live_count q)) (S (pending_count q))
  | Some old =>
    if Pos.ltb p old then
      Queue (insert (Tree (p, encode E k, k) []) (pending q))
        (Map.set E k p (live q)) (live_count q) (S (pending_count q))
    else q
  end.

(** Pop consumes one cached entry-count constructor for each selected heap entry. *)
Fixpoint pop_fuel {K} (E : encoding K) (fuel : nat) (h : heap K)
    (m : Map.t K positive) (n : nat) : option (positive * K * t K) :=
  match fuel with
  | 0 => None
  | S rest =>
    match remove_min h with
    | None => None
    | Some ((p, c, k), h') =>
      match Map.get E k m with
      | Some current =>
        if Pos.eqb p current then Some (p, k, Queue h' (Map.remove E k m) (Nat.pred n) rest)
        else pop_fuel E rest h' m n
      | None => pop_fuel E rest h' m n
      end
    end
  end.

(** Pop begins with enough fuel to examine every heap entry. *)
Definition pop {K} (E : encoding K) (q : t K) : option (positive * K * t K) :=
  pop_fuel E (pending_count q) (pending q) (live q) (live_count q).

Lemma trie_size_node {A} (l r : Trie.t A) o :
  Trie.size (Trie.node l o r) = Trie.size l + Trie.size r +
    match o with Some _ => 1 | None => 0 end.
Proof.
  rewrite !Trie.size_elements, Trie.elements_node, !length_app, !length_map.
  destruct o; cbn [Trie.root_entries length]; lia.
Qed.

Lemma trie_size_parts {A} (tr : Trie.t A) :
  Trie.size tr = Trie.size (Trie.left tr) + Trie.size (Trie.right tr) +
    match Trie.value tr with Some _ => 1 | None => 0 end.
Proof.
  rewrite <- (Trie.node_eta tr) at 1; apply trie_size_node.
Qed.

Lemma trie_size_set {A} p (v : A) : forall tr,
  Trie.size (Trie.set p v tr) =
  match Trie.get p tr with Some _ => Trie.size tr | None => S (Trie.size tr) end.
Proof.
  induction p; intro tr; cbn [Trie.set Trie.get]; rewrite trie_size_node;
    pose proof (trie_size_parts tr) as Hparts.
  - rewrite IHp; destruct (Trie.get p (Trie.right tr)), (Trie.value tr); lia.
  - rewrite IHp; destruct (Trie.get p (Trie.left tr)), (Trie.value tr); lia.
  - destruct (Trie.value tr); lia.
Qed.

Lemma trie_size_remove {A} p : forall tr : Trie.t A,
  Trie.size tr = match Trie.get p tr with
    | Some _ => S (Trie.size (Trie.remove p tr))
    | None => Trie.size (Trie.remove p tr)
    end.
Proof.
  induction p; intro tr; cbn [Trie.remove Trie.get];
    pose proof (trie_size_parts tr) as Hparts.
  - pose proof (IHp (Trie.right tr)) as IH.
    destruct (Trie.get p (Trie.right tr)); rewrite trie_size_node;
      destruct (Trie.value tr); lia.
  - pose proof (IHp (Trie.left tr)) as IH.
    destruct (Trie.get p (Trie.left tr)); rewrite trie_size_node;
      destruct (Trie.value tr); lia.
  - destruct (Trie.value tr); rewrite trie_size_node; lia.
Qed.

Lemma map_size_set {K V} (E : encoding K) k (v : V) m :
  Map.size (Map.set E k v m) =
    match Map.get E k m with Some _ => Map.size m | None => S (Map.size m) end.
Proof.
  unfold Map.size, Map.set, Map.get, Map.code_get; rewrite trie_size_set.
  destruct (Trie.get (encode E k) m) as [[a x]|]; reflexivity.
Qed.

Lemma map_size_remove {K V} (E : encoding K) k (m : Map.t K V) v :
  Map.get E k m = Some v -> Map.size m = S (Map.size (Map.remove E k m)).
Proof.
  unfold Map.size, Map.remove, Map.get, Map.code_get.
  pose proof (trie_size_remove (encode E k) m) as Hsize.
  destruct (Trie.get (encode E k) m) as [[a x]|]; cbn; intro Heq;
    [exact Hsize|discriminate].
Qed.

Section Laws.
Context {K : Type} (E : encoding K).
Variables (q q' : t K) (p p2 : positive) (k k1 k2 : K).

(** Empty queues satisfy all representation invariants. *)
Theorem wf_empty : wf E (@empty K).
Proof.
  split; [exact I|]; split; [apply Map.wf_empty|]; split.
  - intros a v Hget; change (Map.get E a (@Map.empty K positive) = Some v) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - split; reflexivity.
Qed.

(** No key has a live priority in the empty queue. *)
Theorem priority_empty : priority E k (@empty K) = None.
Proof.
  apply Map.get_empty.
Qed.

(** Pushing a key keeps the smaller of its old and supplied priorities. *)
Theorem priority_push_same : wf E q -> priority E k (push E p k q) =
  Some (match priority E k q with None => p | Some p0 => Pos.min p0 p end).
Proof.
  intro Hwf; unfold push; destruct (priority E k q) as [old|] eqn:Hget; cbn.
  - destruct (Pos.ltb p old) eqn:Hlt.
    + unfold priority; cbn; rewrite Map.get_set_same.
      apply Pos.ltb_lt in Hlt; rewrite Pos.min_r by lia; reflexivity.
    + rewrite Hget; apply Pos.ltb_ge in Hlt; rewrite Pos.min_l by lia; reflexivity.
  - apply Map.get_set_same.
Qed.

(** Pushing another key preserves its live priority. *)
Theorem priority_push_other : wf E q -> k1 <> k2 ->
  priority E k1 (push E p k2 q) = priority E k1 q.
Proof.
  intros Hwf Hne; unfold push; destruct (priority E k2 q) as [old|];
    [destruct (Pos.ltb p old)|]; unfold priority; cbn;
    try reflexivity; apply Map.get_set_other; exact Hne.
Qed.

(** A newly inserted key increases the cached live count. *)
Theorem size_push_new : wf E q -> priority E k q = None ->
  size (push E p k q) = S (size q).
Proof.
  intros Hwf Hget; unfold push; rewrite Hget; reflexivity.
Qed.

(** Updating a present key preserves the cached live count. *)
Theorem size_push_old : wf E q -> priority E k q <> None ->
  size (push E p k q) = size q.
Proof.
  intros Hwf Hget; unfold push; destruct (priority E k q) as [old|];
    [destruct (Pos.ltb p old); reflexivity|contradiction].
Qed.

(** The members list is exactly the live-priority map. *)
Theorem members_spec : wf E q -> (In (k, p) (members q) <-> priority E k q = Some p).
Proof.
  intros [_ [Hm _]]; split.
  - apply Map.elements_sound; exact Hm.
  - apply Map.elements_complete; exact Hm.
Qed.

(** Members never repeat a key. *)
Theorem members_nodup : wf E q -> NoDup (List.map fst (members q)).
Proof.
  intros [_ [Hm _]]; apply (Map.elements_nodup E); exact Hm.
Qed.

(** The cached live count agrees with enumeration. *)
Theorem size_members : wf E q -> size q = List.length (members q).
Proof.
  intros [_ [_ [_ [Hcount _]]]]; unfold size, members.
  rewrite Hcount; apply Map.size_elements.
Qed.

(** Emptiness is exactly absence of every live priority. *)
Theorem is_empty_spec : wf E q ->
  (is_empty q = true <-> forall k, priority E k q = None).
Proof.
  intros [_ [Hm _]]; apply Map.is_empty_spec; exact Hm.
Qed.

End Laws.

Lemma wf_insert {K} (E : encoding K) q p k n :
  wf E q -> n = Map.size (Map.set E k p (live q)) ->
  wf E (Queue (insert (Tree (p, encode E k, k) []) (pending q))
    (Map.set E k p (live q)) n (S (pending_count q))).
Proof.
  intros [Hforest [Hm [Hcover [Hsize Hentries]]]] Hn.
  split.
  - apply valid_insert; [apply Valid_zero; reflexivity|exact Hforest].
  - split; [apply Map.wf_set; exact Hm|]; split.
    + intros a v Hget; unfold priority in Hget; cbn in Hget.
      apply entries_insert; destruct (Pos.eq_dec (encode E a) (encode E k)) as [Heq|Hne].
      * apply (encode_injective E) in Heq; subst a.
        rewrite Map.get_set_same in Hget; inversion Hget; subst v; left; cbn; auto.
      * rewrite Map.get_set_other in Hget by (intro Heq; subst a; contradiction).
        right; apply Hcover; exact Hget.
    + split; [exact Hn|]; cbn [pending_count pending].
      rewrite count_insert; cbn [tree_entries length flat_map]; rewrite Hentries; lia.
Qed.

(** Pushing preserves heap coverage, ordering, rank positions and both counters. *)
Theorem wf_push {K} (E : encoding K) (q : t K) p k : wf E q -> wf E (push E p k q).
Proof.
  intro Hwf; unfold push; destruct (priority E k q) as [old|] eqn:Hget.
  - destruct (Pos.ltb p old); [|exact Hwf].
    apply wf_insert; [exact Hwf|].
    rewrite map_size_set; change (Map.get E k (live q) = Some old) in Hget.
    rewrite Hget; exact (proj1 (proj2 (proj2 (proj2 Hwf)))).
  - apply wf_insert; [exact Hwf|].
    rewrite map_size_set; change (Map.get E k (live q) = None) in Hget.
    rewrite Hget; f_equal; exact (proj1 (proj2 (proj2 (proj2 Hwf)))).
Qed.

Lemma wf_drop {K} (E : encoding K) h e rest m n total m' n' :
  wf E (Queue h m n total) -> remove_min h = Some (e, rest) -> Map.wf E m' ->
  (forall a v, Map.get E a m' = Some v ->
    Map.get E a m = Some v /\ (v, encode E a, a) <> e) ->
  n' = Map.size m' -> wf E (Queue rest m' n' (Nat.pred total)).
Proof.
  intros [Hforest [Hm [Hcover [Hn Htotal]]]] Hremove Hm' Hlookup Hn'.
  pose proof (remove_min_correct _ h Hforest) as Hheap; rewrite Hremove in Hheap.
  destruct Hheap as [Hcode [Hrest [Hin [Hcount Hmin]]]].
  split; [exact Hrest|]; split; [exact Hm'|]; split.
  - intros a v Hget; destruct (Hlookup a v Hget) as [Hold Hne].
    specialize (Hcover a v Hold); apply Hin in Hcover; tauto.
  - split; [exact Hn'|].
    change (total = heap_count h) in Htotal; cbn [pending_count pending].
    rewrite Htotal, Hcount; reflexivity.
Qed.

Lemma wf_skip {K} (E : encoding K) h p c k rest m n total :
  wf E (Queue h m n total) -> remove_min h = Some ((p, c, k), rest) ->
  Map.get E k m <> Some p -> wf E (Queue rest m n (Nat.pred total)).
Proof.
  intros Hwf Hremove Hstale; apply (wf_drop E h (p, c, k) rest m n total m n).
  - exact Hwf.
  - exact Hremove.
  - exact (proj1 (proj2 Hwf)).
  - intros a v Hget; split; [exact Hget|]; intro Heq; inversion Heq; subst; contradiction.
  - exact (proj1 (proj2 (proj2 (proj2 Hwf)))).
Qed.

Lemma wf_take {K} (E : encoding K) h p c k rest m n total :
  wf E (Queue h m n total) -> remove_min h = Some ((p, c, k), rest) ->
  Map.get E k m = Some p ->
  wf E (Queue rest (Map.remove E k m) (Nat.pred n) (Nat.pred total)) /\
  n = S (Nat.pred n).
Proof.
  intros Hwf Hremove Hget.
  pose proof (map_size_remove E k m p Hget) as Hsize.
  pose proof (proj1 (proj2 (proj2 (proj2 Hwf)))) as Hn; cbn in Hn.
  split; [|lia].
  apply (wf_drop E h (p, c, k) rest m n total).
  - exact Hwf.
  - exact Hremove.
  - apply Map.wf_remove; exact (proj1 (proj2 Hwf)).
  - intros a v Hlookup.
    destruct (Pos.eq_dec (encode E a) (encode E k)) as [Heq|Hne].
    + apply (encode_injective E) in Heq; subst a.
      rewrite Map.get_remove_same in Hlookup; discriminate.
    + rewrite Map.get_remove_other in Hlookup by (intro Heq; subst a; contradiction).
      split; [exact Hlookup|]; intro Heq; inversion Heq; congruence.
  - lia.
Qed.

Definition pop_result {K} (E : encoding K) (m : Map.t K positive) n
    (result : option (positive * K * t K)) : Prop :=
  match result with
  | None => forall k, Map.get E k m = None
  | Some (p, k, rest) =>
    Map.get E k m = Some p /\
    (forall a v, Map.get E a m = Some v -> before p (encode E k) v (encode E a)) /\
    Map.get E k (live rest) = None /\
    (forall a, a <> k -> Map.get E a (live rest) = Map.get E a m) /\
    n = S (size rest) /\ wf E rest
  end.

Lemma empty_entries_live {K} (E : encoding K) h m n total :
  wf E (Queue h m n total) -> entries h = [] -> forall k, Map.get E k m = None.
Proof.
  intros [_ [_ [Hcover _]]] Hempty k.
  destruct (Map.get E k m) as [p|] eqn:Hget; [|reflexivity].
  specialize (Hcover k p Hget); cbn in Hcover; rewrite Hempty in Hcover; contradiction.
Qed.

Lemma pop_fuel_correct {K} (E : encoding K) fuel : forall h m n,
  wf E (Queue h m n fuel) ->
  pop_result E m n (pop_fuel E fuel h m n).
Proof.
  induction fuel as [|fuel IH]; intros h m n Hwf.
  - cbn [pop_fuel pop_result].
    apply (empty_entries_live E h m n 0 Hwf).
    pose proof (proj2 (proj2 (proj2 (proj2 Hwf)))) as Hentries.
    cbn in Hentries; unfold heap_count in Hentries; symmetry in Hentries.
    apply length_zero_iff_nil; exact Hentries.
  - pose proof (remove_min_correct _ h (proj1 Hwf)) as Hheap.
    cbn [pop_fuel]; destruct (remove_min h) as [[[[p c] k] rest]|] eqn:Hremove.
    + destruct Hheap as [Hcode [Hrest [Hin [Hcount Hmin]]]].
      destruct (Map.get E k m) as [current|] eqn:Hget.
      * destruct (Pos.eqb p current) eqn:Heq.
        -- apply Pos.eqb_eq in Heq; subst current; cbn [pop_result].
           destruct (wf_take E h p c k rest m n (S fuel) Hwf Hremove Hget) as [Hwfrest Hn].
           split; [exact Hget|]; split.
           ++ intros a v Hvalue.
              pose proof (proj1 (proj2 (proj2 Hwf)) a v Hvalue) as Hcover.
              pose proof (Hmin (v, encode E a, a) Hcover) as Hbefore.
              unfold precedes in Hbefore; cbn in Hcode, Hbefore; rewrite Hcode in Hbefore.
              exact Hbefore.
           ++ split; [apply Map.get_remove_same|].
              split; [intros a Hne; apply Map.get_remove_other; exact Hne|].
              split; assumption.
        -- apply IH.
           apply (wf_skip E h p c k rest m n (S fuel)); [exact Hwf|exact Hremove|].
           intro Hbad; rewrite Hget in Hbad; inversion Hbad; subst current.
           rewrite Pos.eqb_refl in Heq; discriminate.
      * apply IH.
        apply (wf_skip E h p c k rest m n (S fuel)); [exact Hwf|exact Hremove|].
        rewrite Hget; discriminate.
    + exact (empty_entries_live E h m n (S fuel) Hwf Hheap).
Qed.

Lemma pop_correct {K} (E : encoding K) (q : t K) :
  wf E q -> pop_result E (live q) (size q) (pop E q).
Proof.
  destruct q as [h m n total]; intro Hwf; apply pop_fuel_correct; exact Hwf.
Qed.

Section PopLaws.
Context {K : Type} (E : encoding K).
Variables (q q' : t K) (p : positive) (k : K).

(** Pop fails exactly when the live map is empty. *)
Theorem pop_none : wf E q -> (pop E q = None <-> is_empty q = true).
Proof.
  intro Hwf; pose proof (pop_correct E q Hwf) as Hcorrect.
  rewrite (is_empty_spec E q Hwf).
  destruct (pop E q) as [[[v a] rest]|] eqn:Hpop; cbn [pop_result] in Hcorrect.
  - split; [discriminate|].
    intro Hempty; destruct Hcorrect as [Hget _]; specialize (Hempty a).
    unfold priority in Hempty; congruence.
  - split; [intro Hnone; exact Hcorrect|intro Hempty; reflexivity].
Qed.

(** The returned key has minimal live priority and encoded tie breaker. *)
Theorem pop_min : wf E q -> pop E q = Some (p, k, q') ->
  priority E k q = Some p /\
  forall (k2 : K) (p2 : positive), priority E k2 q = Some p2 ->
    before p (encode E k) p2 (encode E k2).
Proof.
  intros Hwf Hpop; pose proof (pop_correct E q Hwf) as Hcorrect.
  rewrite Hpop in Hcorrect; exact (conj (proj1 Hcorrect) (proj1 (proj2 Hcorrect))).
Qed.

(** Pop removes exactly the returned key and decreases the live count. *)
Theorem pop_rest : wf E q -> pop E q = Some (p, k, q') ->
  priority E k q' = None /\
  (forall k2 : K, k2 <> k -> priority E k2 q' = priority E k2 q) /\
  size q = S (size q').
Proof.
  intros Hwf Hpop; pose proof (pop_correct E q Hwf) as Hcorrect.
  rewrite Hpop in Hcorrect.
  destruct Hcorrect as [_ [_ [Hnone [Hother [Hsize Hrest]]]]].
  repeat split; assumption.
Qed.

(** Pop preserves the queue invariant. *)
Theorem wf_pop : wf E q -> pop E q = Some (p, k, q') -> wf E q'.
Proof.
  intros Hwf Hpop; pose proof (pop_correct E q Hwf) as Hcorrect.
  rewrite Hpop in Hcorrect; exact (proj2 (proj2 (proj2 (proj2 (proj2 Hcorrect))))).
Qed.

End PopLaws.

End PQueue.
Import PQueue.
