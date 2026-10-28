(** * Integer interval bounds

    Infinite bounds and interval lattice operations support word analysis.
    For example, joining two finite intervals takes their enclosing hull.
    Builds on: Order lattice dictionaries and Stdlib integer arithmetic. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith BitsSigned BitsOp.
From Gaulois.Domains Require Import DomainsNumeric.
Import List.ListNotations.

(** Bounds include both infinities and finite integers. *)
Inductive bound : Type :=
  | NegInf
  | Fin (z : Z)
  | PosInf.

(** An interval is bottom or a pair of bounds. *)
Inductive interval : Type :=
  | IBot
  | Itv (lo hi : bound).

(** Compare extended integer bounds. *)
Definition bound_leb (a b : bound) : bool :=
  match a, b with
  | NegInf, _ => true
  | _, PosInf => true
  | Fin x, Fin y => Z.leb x y
  | _, _ => false
  end.

(** Select the lesser of two extended bounds. *)
Definition bound_min (a b : bound) : bound :=
  if bound_leb a b then a else b.

(** Select the greater of two extended bounds. *)
Definition bound_max (a b : bound) : bound :=
  if bound_leb a b then b else a.

Lemma bound_leb_refl : forall a, bound_leb a a = true.
Proof.
  intros [|z|]; cbn; try reflexivity.
  apply Z.leb_refl.
Qed.

Lemma bound_leb_trans : forall a b c,
  bound_leb a b = true -> bound_leb b c = true -> bound_leb a c = true.
Proof.
  intros [|x|] [|y|] [|z|]; cbn; try discriminate; try reflexivity.
  intros Hxy Hyz. apply Z.leb_le in Hxy. apply Z.leb_le in Hyz.
  apply Z.leb_le. lia.
Qed.

Lemma bound_leb_total : forall a b, bound_leb a b = true \/ bound_leb b a = true.
Proof.
  intros [|x|] [|y|]; cbn; try (now left); try (now right).
  destruct (Z.leb x y) eqn:Hxy; [now left | right].
  apply Z.leb_gt in Hxy. apply Z.leb_le. lia.
Qed.

Lemma bound_min_lower_l : forall a b, bound_leb (bound_min a b) a = true.
Proof.
  intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
  - apply bound_leb_refl.
  - destruct (bound_leb_total a b) as [H | H]; congruence.
Qed.

Lemma bound_min_lower_r : forall a b, bound_leb (bound_min a b) b = true.
Proof.
  intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
  - exact Hab.
  - apply bound_leb_refl.
Qed.

Lemma bound_min_greatest : forall a b c,
  bound_leb c a = true -> bound_leb c b = true -> bound_leb c (bound_min a b) = true.
Proof.
  intros a b c Ha Hb. unfold bound_min. destruct (bound_leb a b); assumption.
Qed.

Lemma bound_max_upper_l : forall a b, bound_leb a (bound_max a b) = true.
Proof.
  intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
  - exact Hab.
  - apply bound_leb_refl.
Qed.

Lemma bound_max_upper_r : forall a b, bound_leb b (bound_max a b) = true.
Proof.
  intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
  - apply bound_leb_refl.
  - destruct (bound_leb_total a b) as [H | H]; congruence.
Qed.

Lemma bound_max_least : forall a b c,
  bound_leb a c = true -> bound_leb b c = true -> bound_leb (bound_max a b) c = true.
Proof.
  intros a b c Ha Hb. unfold bound_max. destruct (bound_leb a b); assumption.
Qed.

(** A search tree is built once when the lattice dictionary is constructed. *)
Inductive threshold_tree : Type :=
  | ThresholdEmpty
  | ThresholdNode (left : threshold_tree) (value : Z) (right : threshold_tree).

Fixpoint threshold_insert (z : Z) (tree : threshold_tree) : threshold_tree :=
  match tree with
  | ThresholdEmpty => ThresholdNode ThresholdEmpty z ThresholdEmpty
  | ThresholdNode lhs value rhs =>
    if Z.eqb z value then tree
    else if Z.leb z value then ThresholdNode (threshold_insert z lhs) value rhs
    else ThresholdNode lhs value (threshold_insert z rhs)
  end.

Definition threshold_index (ts : list Z) : threshold_tree :=
  fold_left (fun tree z => threshold_insert z tree) ts ThresholdEmpty.

(** The tree's values are used to justify its search results. *)
Fixpoint threshold_values (tree : threshold_tree) : list Z :=
  match tree with
  | ThresholdEmpty => []
  | ThresholdNode lhs value rhs => value :: threshold_values lhs ++ threshold_values rhs
  end.

Lemma threshold_insert_values : forall tree z x,
  In x (threshold_values (threshold_insert z tree)) ->
  x = z \/ In x (threshold_values tree).
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intros z x Hin; cbn in *.
  - destruct Hin as [Heq | Hnone]; [now left | contradiction].
  - destruct (Z.eqb z value); [now right |].
    destruct (Z.leb z value); cbn in Hin;
      destruct Hin as [Heq | Hin]; [now right; left | |now right; left |].
    + apply in_app_iff in Hin as [Hin | Hin].
      * destruct (IHleft z x Hin) as [Heq | Hmember]; [now left |].
        right. right. apply in_app_iff. now left.
      * right. right. apply in_app_iff. now right.
    + apply in_app_iff in Hin as [Hin | Hin].
      * right. right. apply in_app_iff. now left.
      * destruct (IHright z x Hin) as [Heq | Hmember]; [now left |].
        right. right. apply in_app_iff. now right.
Qed.

Lemma threshold_index_values : forall ts x,
  In x (threshold_values (threshold_index ts)) -> In x ts.
Proof.
  intros ts x. unfold threshold_index.
  assert (H : forall xs tree, In x (threshold_values (fold_left
    (fun acc z => threshold_insert z acc) xs tree)) ->
    In x xs \/ In x (threshold_values tree)).
  { induction xs as [|z rest IH]; intros tree Hin; cbn in *; [now right |].
    destruct (IH (threshold_insert z tree) Hin) as [Hin' | Hin'].
    - left. now right.
    - destruct (threshold_insert_values tree z x Hin') as [Heq | Hin''].
      + left. now left.
      + now right. }
  intro Hin. destruct (H ts ThresholdEmpty Hin) as [Hin' | Hin']; [exact Hin' | contradiction].
Qed.

Lemma threshold_node_values : forall lhs value rhs x,
  In x (threshold_values (ThresholdNode lhs value rhs)) <->
  x = value \/ In x (threshold_values lhs) \/ In x (threshold_values rhs).
Proof.
  intros lhs value rhs x. cbn. rewrite in_app_iff. intuition congruence.
Qed.

(** The index is a strict binary search tree; equal thresholds share a node. *)
Fixpoint threshold_ordered (tree : threshold_tree) : Prop :=
  match tree with
  | ThresholdEmpty => True
  | ThresholdNode lhs value rhs =>
    threshold_ordered lhs /\ threshold_ordered rhs /\
    (forall x, In x (threshold_values lhs) -> (x < value)%Z) /\
    (forall x, In x (threshold_values rhs) -> (value < x)%Z)
  end.

Lemma threshold_insert_complete : forall tree z x,
  x = z \/ In x (threshold_values tree) -> In x (threshold_values (threshold_insert z tree)).
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intros z x Hin; cbn in *.
  - destruct Hin as [-> | Hin]; [now left | contradiction].
  - destruct (Z.eqb z value) eqn:Hequal.
    + apply Z.eqb_eq in Hequal. destruct Hin as [-> | Hin]; [now left | exact Hin].
    + rewrite in_app_iff in Hin.
      destruct (Z.leb z value) eqn:Horder; rewrite threshold_node_values.
      * destruct Hin as [-> | [Heq | [Hleft | Hright]]].
        -- right. left. apply IHleft. now left.
        -- now left.
        -- right. left. apply IHleft. now right.
        -- now right; right.
      * destruct Hin as [-> | [Heq | [Hleft | Hright]]].
        -- right. right. apply IHright. now left.
        -- now left.
        -- now right; left.
        -- right. right. apply IHright. now right.
Qed.

Lemma threshold_insert_ordered : forall tree z,
  threshold_ordered tree -> threshold_ordered (threshold_insert z tree).
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intros z Hordered; cbn in *.
  - repeat split; intros x Hin; contradiction.
  - destruct Hordered as [Hleft [Hright [Hbelow Habove]]].
    destruct (Z.eqb z value) eqn:Hequal; [repeat split; assumption |].
    apply Z.eqb_neq in Hequal.
    destruct (Z.leb z value) eqn:Horder; cbn.
    + apply Z.leb_le in Horder. repeat split; try assumption.
      * now apply IHleft.
      * intros x Hin. apply threshold_insert_values in Hin. destruct Hin as [-> | Hin];
          [lia | now apply Hbelow].
    + apply Z.leb_gt in Horder. repeat split; try assumption.
      * now apply IHright.
      * intros x Hin. apply threshold_insert_values in Hin. destruct Hin as [-> | Hin];
          [lia | now apply Habove].
Qed.

Lemma threshold_index_ordered : forall ts, threshold_ordered (threshold_index ts).
Proof.
  intro ts. unfold threshold_index.
  assert (H : forall xs tree, threshold_ordered tree ->
    threshold_ordered (fold_left (fun acc z => threshold_insert z acc) xs tree)).
  { induction xs as [|z rest IH]; intros tree Htree; cbn; [exact Htree |].
    apply IH. now apply threshold_insert_ordered. }
  apply H. exact I.
Qed.

Lemma threshold_index_complete : forall ts x,
  In x ts -> In x (threshold_values (threshold_index ts)).
Proof.
  intros ts x. unfold threshold_index.
  assert (H : forall xs tree, In x xs \/ In x (threshold_values tree) ->
    In x (threshold_values (fold_left (fun acc z => threshold_insert z acc) xs tree))).
  { induction xs as [|z rest IH]; intros tree Hin; cbn in *.
    - destruct Hin as [Hin | Hin]; [contradiction | exact Hin].
    - apply IH. destruct Hin as [[Heq | Hin] | Hin]; [|now left |].
      + right. apply threshold_insert_complete. left. congruence.
      + right. apply threshold_insert_complete. now right. }
  intro Hin. apply H. now left.
Qed.

Lemma threshold_index_membership : forall ts x,
  In x (threshold_values (threshold_index ts)) <-> In x ts.
Proof.
  intros ts x. split; [apply threshold_index_values | apply threshold_index_complete].
Qed.

(** Find the greatest indexed threshold at most the given bound. *)
Fixpoint lower_threshold (tree : threshold_tree) (z : Z) : bound :=
  match tree with
  | ThresholdEmpty => NegInf
  | ThresholdNode lhs value rhs =>
    if Z.leb value z then bound_max (Fin value) (lower_threshold rhs z)
    else lower_threshold lhs z
  end.

(** Find the least indexed threshold at least the given bound. *)
Fixpoint upper_threshold (tree : threshold_tree) (z : Z) : bound :=
  match tree with
  | ThresholdEmpty => PosInf
  | ThresholdNode lhs value rhs =>
    if Z.leb z value then bound_min (Fin value) (upper_threshold lhs z)
    else upper_threshold rhs z
  end.

Lemma lower_threshold_member : forall tree z,
  match lower_threshold tree z with
  | NegInf => True
  | Fin x => In x (threshold_values tree)
  | PosInf => False
  end.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intro z; cbn; [exact I |].
  destruct (Z.leb value z).
  - specialize (IHright z). destruct (lower_threshold rhs z) as [|x|] eqn:Hresult;
      cbn [bound_max bound_leb] in *; try contradiction.
    + now left.
    + unfold bound_max, bound_leb. destruct (Z.leb value x); cbn;
        [right; apply in_app_iff; now right | now left].
  - specialize (IHleft z). destruct (lower_threshold lhs z); cbn in *; try contradiction;
      [exact I | right; apply in_app_iff; now left].
Qed.

Lemma upper_threshold_member : forall tree z,
  match upper_threshold tree z with
  | NegInf => False
  | Fin x => In x (threshold_values tree)
  | PosInf => True
  end.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intro z; cbn; [exact I |].
  destruct (Z.leb z value).
  - specialize (IHleft z). destruct (upper_threshold lhs z) as [|x|] eqn:Hresult;
      cbn [bound_min bound_leb] in *; try contradiction.
    + unfold bound_min, bound_leb. destruct (Z.leb value x); cbn;
        [now left | right; apply in_app_iff; now left].
    + now left.
  - specialize (IHright z). destruct (upper_threshold rhs z); cbn in *; try contradiction;
      [right; apply in_app_iff; now right | exact I].
Qed.

Lemma lower_threshold_lower : forall tree z,
  bound_leb (lower_threshold tree z) (Fin z) = true.
Proof.
  induction tree as [|left IHleft value right IHright]; intro z; cbn; [reflexivity |].
  destruct (Z.leb value z) eqn:Hle; [|apply IHleft].
  apply bound_max_least; [exact Hle | apply IHright].
Qed.

Lemma upper_threshold_upper : forall tree z,
  bound_leb (Fin z) (upper_threshold tree z) = true.
Proof.
  induction tree as [|left IHleft value right IHright]; intro z; cbn; [reflexivity |].
  destruct (Z.leb z value) eqn:Hle; [|apply IHright].
  change (bound_leb (Fin z) (bound_min (Fin value) (upper_threshold left z)) = true).
  apply bound_min_greatest; [exact Hle | apply IHleft].
Qed.

(** Every indexed lower candidate lies below the result of the ordered search. *)
Lemma lower_threshold_greatest : forall tree z x,
  threshold_ordered tree -> In x (threshold_values tree) -> (x <= z)%Z ->
  bound_leb (Fin x) (lower_threshold tree z) = true.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intros z x Hordered Hin Hxz.
  - contradiction.
  - cbn in Hordered. destruct Hordered as [Hleft [Hright [Hbelow Habove]]].
    apply threshold_node_values in Hin. cbn [lower_threshold].
    destruct (Z.leb value z) eqn:Htest.
    + destruct Hin as [-> | [Hin | Hin]].
      * apply bound_max_upper_l.
      * eapply bound_leb_trans; [|apply bound_max_upper_l].
        cbn. apply Z.leb_le. specialize (Hbelow x Hin). lia.
      * eapply bound_leb_trans; [apply IHright; eassumption | apply bound_max_upper_r].
    + apply Z.leb_gt in Htest. destruct Hin as [Heq | [Hin | Hin]].
      * lia.
      * now apply IHleft.
      * specialize (Habove x Hin). lia.
Qed.

(** Every indexed upper candidate lies above the result of the ordered search. *)
Lemma upper_threshold_least : forall tree z x,
  threshold_ordered tree -> In x (threshold_values tree) -> (z <= x)%Z ->
  bound_leb (upper_threshold tree z) (Fin x) = true.
Proof.
  induction tree as [|lhs IHleft value rhs IHright]; intros z x Hordered Hin Hzx.
  - contradiction.
  - cbn in Hordered. destruct Hordered as [Hleft [Hright [Hbelow Habove]]].
    apply threshold_node_values in Hin. cbn [upper_threshold].
    destruct (Z.leb z value) eqn:Htest.
    + destruct Hin as [-> | [Hin | Hin]].
      * apply bound_min_lower_l.
      * eapply bound_leb_trans; [apply bound_min_lower_r | apply IHleft; eassumption].
      * eapply bound_leb_trans; [apply bound_min_lower_l |].
        cbn. apply Z.leb_le. specialize (Habove x Hin). lia.
    + apply Z.leb_gt in Htest. destruct Hin as [Heq | [Hin | Hin]].
      * lia.
      * specialize (Hbelow x Hin). lia.
      * now apply IHright.
Qed.

(** The prepared predecessor is exactly the greatest eligible input threshold, or minus infinity. *)
Lemma lower_threshold_index_agrees : forall ts z,
  match lower_threshold (threshold_index ts) z with
  | NegInf => forall x, In x ts -> (z < x)%Z
  | Fin value => In value ts /\ (value <= z)%Z /\
      forall x, In x ts -> (x <= z)%Z -> (x <= value)%Z
  | PosInf => False
  end.
Proof.
  intros ts z.
  pose proof (lower_threshold_member (threshold_index ts) z) as Hmember.
  pose proof (lower_threshold_lower (threshold_index ts) z) as Hbound.
  assert (Hgreatest : forall x, In x ts -> (x <= z)%Z ->
    bound_leb (Fin x) (lower_threshold (threshold_index ts) z) = true).
  { intros x Hin Hxz. apply lower_threshold_greatest; [apply threshold_index_ordered | |exact Hxz].
    now apply threshold_index_complete. }
  destruct (lower_threshold (threshold_index ts) z) as [|value|] eqn:Hresult; cbn in *.
  - intros x Hin. destruct (Z_le_gt_dec x z) as [Hxz | Hzx]; [|lia].
    specialize (Hgreatest x Hin Hxz). discriminate.
  - split; [now apply threshold_index_values |].
    apply Z.leb_le in Hbound. split; [exact Hbound |].
    intros x Hin Hxz. apply Z.leb_le. now apply Hgreatest.
  - exact Hmember.
Qed.

(** The prepared successor is exactly the least eligible input threshold, or plus infinity. *)
Lemma upper_threshold_index_agrees : forall ts z,
  match upper_threshold (threshold_index ts) z with
  | NegInf => False
  | Fin value => In value ts /\ (z <= value)%Z /\
      forall x, In x ts -> (z <= x)%Z -> (value <= x)%Z
  | PosInf => forall x, In x ts -> (x < z)%Z
  end.
Proof.
  intros ts z.
  pose proof (upper_threshold_member (threshold_index ts) z) as Hmember.
  pose proof (upper_threshold_upper (threshold_index ts) z) as Hbound.
  assert (Hleast : forall x, In x ts -> (z <= x)%Z ->
    bound_leb (upper_threshold (threshold_index ts) z) (Fin x) = true).
  { intros x Hin Hzx. apply upper_threshold_least; [apply threshold_index_ordered | |exact Hzx].
    now apply threshold_index_complete. }
  destruct (upper_threshold (threshold_index ts) z) as [|value|] eqn:Hresult; cbn in *.
  - exact Hmember.
  - split; [now apply threshold_index_values |].
    apply Z.leb_le in Hbound. split; [exact Hbound |].
    intros x Hin Hzx. apply Z.leb_le. now apply Hleast.
  - intros x Hin. destruct (Z_le_gt_dec z x) as [Hzx | Hxz]; [|lia].
    specialize (Hleast x Hin Hzx). discriminate.
Qed.

Lemma lower_threshold_index_none : forall ts z,
  lower_threshold (threshold_index ts) z = NegInf <->
  forall x, In x ts -> (z < x)%Z.
Proof.
  intros ts z. pose proof (lower_threshold_index_agrees ts z) as Hagree.
  destruct (lower_threshold (threshold_index ts) z) as [|value|] eqn:Hresult; cbn in *.
  - split; [intros _; exact Hagree | reflexivity].
  - destruct Hagree as [Hin [Hbound _]]. split; [discriminate |].
    intro Hnone. specialize (Hnone value Hin). lia.
  - contradiction.
Qed.

Lemma upper_threshold_index_none : forall ts z,
  upper_threshold (threshold_index ts) z = PosInf <->
  forall x, In x ts -> (x < z)%Z.
Proof.
  intros ts z. pose proof (upper_threshold_index_agrees ts z) as Hagree.
  destruct (upper_threshold (threshold_index ts) z) as [|value|] eqn:Hresult; cbn in *.
  - contradiction.
  - destruct Hagree as [Hin [Hbound _]]. split; [discriminate |].
    intro Hnone. specialize (Hnone value Hin). lia.
  - split; [intros _; exact Hagree | reflexivity].
Qed.

(** Widen an outward-moving lower bound to its threshold. *)
Definition widen_lower (ts : threshold_tree) (old next : bound) : bound :=
  if bound_leb old next then old else
    match next with
    | NegInf => NegInf
    | Fin z => lower_threshold ts z
    | PosInf => PosInf
    end.

(** Widen an outward-moving upper bound to its threshold. *)
Definition widen_upper (ts : threshold_tree) (old next : bound) : bound :=
  if bound_leb next old then old else
    match next with
    | NegInf => NegInf
    | Fin z => upper_threshold ts z
    | PosInf => PosInf
    end.

(** Refine an infinite bound with the newer bound. *)
Definition narrow_bound (old next : bound) : bound :=
  match old with
  | Fin _ => old
  | _ => next
  end.

Lemma widen_lower_next : forall ts old next,
  bound_leb (widen_lower ts old next) next = true.
Proof.
  intros ts old next. unfold widen_lower. destruct (bound_leb old next) eqn:Hle.
  - exact Hle.
  - destruct next; cbn; try reflexivity. apply lower_threshold_lower.
Qed.

Lemma widen_lower_old : forall ts old next,
  bound_leb (widen_lower ts old next) old = true.
Proof.
  intros ts old next. unfold widen_lower. destruct (bound_leb old next) eqn:Hle.
  - apply bound_leb_refl.
  - eapply (bound_leb_trans _ next old); [|].
    + destruct next as [|z|].
      * reflexivity.
      * apply lower_threshold_lower.
      * destruct old; discriminate.
    + destruct (bound_leb_total old next) as [H | H]; congruence.
Qed.

Lemma widen_upper_next : forall ts old next,
  bound_leb next (widen_upper ts old next) = true.
Proof.
  intros ts old next. unfold widen_upper. destruct (bound_leb next old) eqn:Hle.
  - exact Hle.
  - destruct next; cbn; try reflexivity. apply upper_threshold_upper.
Qed.

Lemma widen_upper_old : forall ts old next,
  bound_leb old (widen_upper ts old next) = true.
Proof.
  intros ts old next. unfold widen_upper. destruct (bound_leb next old) eqn:Hle.
  - apply bound_leb_refl.
  - eapply (bound_leb_trans old next _); [|].
    + destruct (bound_leb_total old next) as [H | H]; congruence.
    + destruct next as [|z|].
      * destruct old; discriminate.
      * apply upper_threshold_upper.
      * reflexivity.
Qed.

(** The lattice uses hulls, threshold widening and infinite-bound narrowing. *)
Definition interval_lattice (thresholds : list Z) : lattice interval :=
  let index := threshold_index thresholds in
  {| leb a b :=
       match a, b with
       | IBot, _ => true
       | Itv _ _, IBot => false
       | Itv l h, Itv l' h' => bound_leb l' l && bound_leb h h'
       end;
     bot := IBot;
     join a b :=
       match a, b with
       | IBot, _ => b
       | _, IBot => a
       | Itv l h, Itv l' h' => Itv (bound_min l l') (bound_max h h')
       end;
     widen a b :=
       match a, b with
       | IBot, _ => b
       | _, IBot => a
       | Itv l h, Itv l' h' =>
         Itv (widen_lower index l l') (widen_upper index h h')
       end;
     narrow a b :=
       match a, b with
       | IBot, _ => IBot
       | _, IBot => a
       | Itv l h, Itv l' h' => Itv (narrow_bound l l') (narrow_bound h h')
       end |}.

(** An interval denotes the integers between its bounds. *)
Definition interval_gamma : concretisation interval Z :=
  {| gamma i z :=
       match i with
       | IBot => False
       | Itv l h => bound_leb l (Fin z) = true /\ bound_leb (Fin z) h = true
       end |}.

(** The word interpretation additionally requires a normalized unsigned word. *)
Definition interval_pgamma (w : width) (i : interval) (z : Z) : Prop :=
  is_word w z /\ gamma interval_gamma i z.

(** The unsigned word range is the width-specific top. *)
Definition interval_top (w : width) : interval :=
  Itv (Fin 0) (Fin (modulus w - 1)).

(** A concrete word is represented by its wrapped singleton. *)
Definition interval_const (w : width) (z : Z) : interval :=
  Itv (Fin (wrap w z)) (Fin (wrap w z)).

Lemma interval_top_sound : forall w z, is_word w z -> interval_pgamma w (interval_top w) z.
Proof.
  intros w z Hword. split; [exact Hword |].
  unfold interval_top, interval_gamma. cbn [gamma bound_leb].
  destruct Hword as [Hlower Hupper]. split; apply Z.leb_le; lia.
Qed.

Lemma interval_const_sound : forall w z, interval_pgamma w (interval_const w z) (wrap w z).
Proof.
  intros w z. split; [apply wrap_is_word |].
  unfold interval_const, interval_gamma. cbn [gamma bound_leb].
  now rewrite Z.leb_refl.
Qed.

(** A nonempty integer interval has a finite-or-negative-infinite lower endpoint and a
    finite-or-positive-infinite upper endpoint in the correct order. *)
Definition bounds_nonempty (lo hi : bound) : bool :=
  match lo, hi with
  | PosInf, _ => false
  | _, NegInf => false
  | _, _ => bound_leb lo hi
  end.

(** Intersect two intervals, normalizing an empty intersection to bottom. *)
Definition interval_meet (a b : interval) : interval :=
  match a, b with
  | Itv l h, Itv l' h' =>
    let lo := bound_max l l' in
    let hi := bound_min h h' in
    if bounds_nonempty lo hi then Itv lo hi else IBot
  | _, _ => IBot
  end.

(** A finite pair of endpoints is available after clipping to a word range. *)
Definition interval_finite (i : interval) : option (Z * Z) :=
  match i with
  | Itv (Fin lo) (Fin hi) => Some (lo, hi)
  | _ => None
  end.

(** Construct a finite range when it fits, otherwise use the word range. *)
Definition interval_checked (w : width) (lo hi : Z) : interval :=
  if (Z.leb 0 lo && Z.ltb hi (modulus w))%bool
  then Itv (Fin lo) (Fin hi) else interval_top w.

Lemma interval_checked_sound : forall w lo hi z,
  is_word w z -> (lo <= z <= hi)%Z -> interval_pgamma w (interval_checked w lo hi) z.
Proof.
  intros w lo hi z Hword Hz. unfold interval_checked.
  destruct (Z.leb 0 lo && Z.ltb hi (modulus w))%bool; [|now apply interval_top_sound].
  split; [exact Hword |]. cbn [interval_gamma gamma bound_leb].
  split; apply Z.leb_le; lia.
Qed.

Lemma interval_finite_sound : forall w i lo hi z,
  interval_pgamma w i z -> interval_finite i = Some (lo, hi) -> (lo <= z <= hi)%Z.
Proof.
  intros w [|[|l|] [|h|]] lo hi z Hgamma Hfinite;
    cbn [interval_finite] in Hfinite; try discriminate.
  inversion Hfinite; subst lo hi. destruct Hgamma as [_ [Hlo Hhi]].
  cbn [interval_gamma gamma bound_leb] in Hlo, Hhi.
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. lia.
Qed.

(** Addition uses endpoint arithmetic when its result cannot wrap. *)
Definition interval_add (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) => interval_checked w (la + lb) (ha + hb)
  | _, _ => interval_top w
  end.

Lemma interval_add_sound : forall w wa wb a b x y,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_add w a b) (wrap w (x + y)).
Proof.
  intros w wa wb a b x y Ha Hb. unfold interval_add.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wrap_is_word).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  unfold interval_checked. destruct (Z.leb 0 (la + lb) && Z.ltb (ha + hb) (modulus w))%bool
    eqn:Hrange; [|apply interval_top_sound; apply wrap_is_word].
  apply andb_true_iff in Hrange as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  assert (Hword : is_word w (x + y)) by (unfold is_word; lia).
  rewrite (wrap_id w (x + y) Hword). split; [exact Hword |].
  cbn [interval_gamma gamma bound_leb]. split; apply Z.leb_le; lia.
Qed.

(** Internal signed-modulus arithmetic also handles a uniformly wrapped sum. *)
Definition interval_add_modular (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb (modulus w) (la + lb) && Z.ltb (ha + hb) (2 * modulus w))%bool
    then interval_checked w (la + lb - modulus w) (ha + hb - modulus w)
    else interval_add w a b
  | _, _ => interval_top w
  end.

Lemma interval_add_modular_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_add_modular w a b) (wrap w (x + y)).
Proof.
  intros w a b x y Ha Hb. unfold interval_add_modular.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wrap_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct (Z.leb (modulus w) (la + lb) && Z.ltb (ha + hb) (2 * modulus w))%bool
    eqn:Hwrap; [|apply (interval_add_sound w w w); assumption].
  apply andb_true_iff in Hwrap as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  assert (Hword : is_word w (x + y - modulus w)) by (unfold is_word; lia).
  replace (x + y)%Z with ((x + y - modulus w) + 1 * modulus w)%Z by ring.
  rewrite wrap_add_modulus, (wrap_id w _ Hword). apply interval_checked_sound; [exact Hword | lia].
Qed.

(** Subtraction uses the opposite endpoints of the second operand. *)
Definition interval_sub (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) => interval_checked w (la - hb) (ha - lb)
  | _, _ => interval_top w
  end.

Lemma interval_sub_sound : forall w wa wb a b x y,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_sub w a b) (wrap w (x - y)).
Proof.
  intros w wa wb a b x y Ha Hb. unfold interval_sub.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wrap_is_word).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  unfold interval_checked. destruct (Z.leb 0 (la - hb) && Z.ltb (ha - lb) (modulus w))%bool
    eqn:Hrange; [|apply interval_top_sound; apply wrap_is_word].
  apply andb_true_iff in Hrange as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  assert (Hword : is_word w (x - y)) by (unfold is_word; lia).
  rewrite (wrap_id w (x - y) Hword). split; [exact Hword |].
  cbn [interval_gamma gamma bound_leb]. split; apply Z.leb_le; lia.
Qed.

(** Nonnegative endpoint multiplication covers clipped unsigned operands. *)
Definition interval_mul (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb)%bool
    then interval_checked w (la * lb) (ha * hb) else interval_top w
  | _, _ => interval_top w
  end.

Lemma interval_mul_sound : forall w wa wb a b x y,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_mul w a b) (wrap w (x * y)).
Proof.
  intros w wa wb a b x y Ha Hb. unfold interval_mul.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wrap_is_word).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  destruct (Z.leb 0 la && Z.leb 0 lb)%bool eqn:Hnonneg;
    [|apply interval_top_sound; apply wrap_is_word].
  apply andb_true_iff in Hnonneg as [Hla Hlb].
  apply Z.leb_le in Hla. apply Z.leb_le in Hlb.
  unfold interval_checked. destruct (Z.leb 0 (la * lb) && Z.ltb (ha * hb) (modulus w))%bool
    eqn:Hrange; [|apply interval_top_sound; apply wrap_is_word].
  apply andb_true_iff in Hrange as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  assert (Hproduct : (la * lb <= x * y <= ha * hb)%Z) by nia.
  assert (Hword : is_word w (x * y)) by (unfold is_word; lia).
  rewrite (wrap_id w (x * y) Hword). split; [exact Hword |].
  cbn [interval_gamma gamma bound_leb]. split; apply Z.leb_le; lia.
Qed.

(** Negation is exact for zero and for a strictly positive unsigned interval. *)
Definition interval_neg (w : width) (a : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.eqb hi 0 then Itv (Fin 0) (Fin 0)
    else if Z.ltb 0 lo then interval_checked w (modulus w - hi) (modulus w - lo)
    else interval_top w
  | None => interval_top w
  end.

Lemma interval_neg_sound : forall w a x,
  interval_pgamma w a x -> interval_pgamma w (interval_neg w a) (wrap w (- x)).
Proof.
  intros w a x Ha. unfold interval_neg.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite;
    [|apply interval_top_sound; apply wrap_is_word].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hx.
  destruct Ha as [Hword _].
  destruct (Z.eqb hi 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. unfold is_word in Hword. assert (x = 0)%Z by lia.
    subst x. rewrite Z.opp_0, wrap_0. split; [apply zero_is_word |].
    cbn [interval_gamma gamma bound_leb]. split; reflexivity.
  - destruct (Z.ltb 0 lo) eqn:Hpositive;
      [|apply interval_top_sound; apply wrap_is_word].
    apply Z.ltb_lt in Hpositive. unfold is_word in Hword.
    assert (Hshift : is_word w (modulus w - x)) by (unfold is_word; lia).
    assert (Hwrap : wrap w (- x) = (modulus w - x)%Z).
    { rewrite <- (wrap_add_modulus w (- x) 1).
      replace (- x + 1 * modulus w)%Z with (modulus w - x)%Z by ring.
      apply wrap_id. exact Hshift. }
    rewrite Hwrap. apply interval_checked_sound; [exact Hshift | lia].
Qed.

(** Bitwise complement reverses the unsigned interval's endpoints. *)
Definition interval_not (w : width) (a : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) => interval_checked w (modulus w - 1 - hi) (modulus w - 1 - lo)
  | None => interval_top w
  end.

Lemma interval_not_sound : forall w a x,
  interval_pgamma w a x -> interval_pgamma w (interval_not w a) (wnot w x).
Proof.
  intros w a x Ha. unfold interval_not.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite;
    [|apply interval_top_sound; apply wnot_is_word].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hbounds.
  destruct Ha as [Hword _]. apply interval_checked_sound; [apply wnot_is_word |].
  unfold wnot. rewrite (wrap_id w x Hword). lia.
Qed.

(** Bitwise and is nonnegative and no greater than either unsigned operand. *)
Definition interval_and (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (_, ha), Some (_, hb) => interval_checked w 0 (Z.min ha hb)
  | _, _ => interval_top w
  end.

Lemma interval_and_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_and w a b) (wand w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_and.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wand_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
  apply interval_checked_sound; [apply wand_is_word |].
  unfold wand. rewrite (wrap_id w x Hwordx), (wrap_id w y Hwordy).
  pose proof (Z.sub_land_same_l x y) as Hx.
  pose proof (Z.sub_land_same_l y x) as Hy. rewrite Z.land_comm in Hy.
  assert (Hnonnegx : (0 <= Z.land x (Z.lnot y))%Z).
  { apply Z.land_nonneg. left. exact (proj1 Hwordx). }
  assert (Hnonnegy : (0 <= Z.land y (Z.lnot x))%Z).
  { apply Z.land_nonneg. left. exact (proj1 Hwordy). }
  assert (Hnonneg : (0 <= Z.land x y)%Z).
  { apply Z.land_nonneg. left. exact (proj1 Hwordx). }
  split; [exact Hnonneg |]. apply Z.min_glb; lia.
Qed.

(** The next all-ones mask covers both disjunction and exclusive disjunction. *)
Definition interval_mask (hi : Z) : Z :=
  if Z.eqb hi 0 then 0 else Z.ones (Z.log2 hi + 1).

Lemma interval_mask_covers : forall x y hi,
  (0 <= x <= hi)%Z -> (0 <= y <= hi)%Z ->
  (0 <= Z.lor x y <= interval_mask hi)%Z /\
  (0 <= Z.lxor x y <= interval_mask hi)%Z.
Proof.
  intros x y hi Hx Hy. unfold interval_mask. destruct (Z.eqb hi 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. assert (x = 0 /\ y = 0)%Z by lia.
    destruct H as [-> ->]. cbn. lia.
  - set (n := (Z.log2 hi + 1)%Z).
    assert (Hn : (0 <= n)%Z) by (unfold n; pose proof (Z.log2_nonneg hi); lia).
    assert (Hmask : (0 <= Z.ones n)%Z).
    { rewrite Z.ones_equiv. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn). lia. }
    assert (Hlogx : (Z.log2 x < n)%Z) by
      (unfold n; pose proof (Z.log2_le_mono x hi ltac:(lia)); lia).
    assert (Hlogy : (Z.log2 y < n)%Z) by
      (unfold n; pose proof (Z.log2_le_mono y hi ltac:(lia)); lia).
    assert (Hor : Z.lor (Z.lor x y) (Z.ones n) = Z.ones n).
    { rewrite <- Z.lor_assoc, Z.lor_ones_low by lia. apply Z.lor_ones_low; lia. }
    assert (Hlor : (0 <= Z.lor x y)%Z) by (apply Z.lor_nonneg; lia).
    assert (Hmaskdiff : (0 <= Z.land (Z.ones n) (Z.lnot (Z.lor x y)))%Z).
    { apply Z.land_nonneg. now left. }
    pose proof (Z.sub_lor_l_same_l (Z.ones n) (Z.lor x y)) as Hdiff.
    rewrite Hor in Hdiff.
    assert (Hand : (0 <= Z.land x y)%Z) by (apply Z.land_nonneg; lia).
    pose proof (Z.sub_lor_land x y) as Hxor.
    assert (Hxor_nonneg : (0 <= Z.lxor x y)%Z) by (apply Z.lxor_nonneg; lia).
    lia.
Qed.

Definition interval_or_xor (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (_, ha), Some (_, hb) => interval_checked w 0 (interval_mask (Z.max ha hb))
  | _, _ => interval_top w
  end.

Lemma interval_or_xor_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_or_xor w a b) (wor w x y) /\
  interval_pgamma w (interval_or_xor w a b) (wxor w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_or_xor.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (split; apply interval_top_sound; first [apply wor_is_word | apply wxor_is_word]).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
  pose proof (proj1 Hwordx) as Hxnonneg. pose proof (proj1 Hwordy) as Hynonneg.
  pose proof (interval_mask_covers x y (Z.max ha hb) ltac:(pose proof (Z.le_max_l ha hb); lia)
    ltac:(pose proof (Z.le_max_r ha hb); lia)) as [Hor Hxor].
  split; apply interval_checked_sound; try apply wor_is_word; try apply wxor_is_word.
  - unfold wor. now rewrite (wrap_id w x Hwordx), (wrap_id w y Hwordy).
  - unfold wxor. now rewrite (wrap_id w x Hwordx), (wrap_id w y Hwordy).
Qed.

(** Bit counts lie between zero and the word width. *)
Definition interval_counts (w : width) : interval := Itv (Fin 0) (Fin (Zpos w)).

Lemma interval_clz_sound : forall w x, interval_pgamma w (interval_counts w) (wclz w x).
Proof.
  intros w x. split; [apply wclz_is_word |].
  cbn [interval_counts interval_gamma gamma bound_leb].
  unfold wclz. destruct (wrap w x =? 0).
  - split; apply Z.leb_le; lia.
  - pose proof (log2_word w _ (wrap_is_word w x)).
    pose proof (Z.log2_nonneg (wrap w x)). split; apply Z.leb_le; lia.
Qed.

Lemma interval_ctz_sound : forall w x, interval_pgamma w (interval_counts w) (wctz w x).
Proof.
  intros w x. split; [apply wctz_is_word |].
  cbn [interval_counts interval_gamma gamma bound_leb].
  unfold wctz. destruct (wrap w x =? 0).
  - split; apply Z.leb_le; lia.
  - assert (Hland : is_word w (Z.land (wrap w x) (- wrap w x))).
    { apply word_of_bits. intros i Hi. rewrite Z.land_spec.
      rewrite (word_bits_high w _ i (wrap_is_word w x) Hi). reflexivity. }
    pose proof (log2_word w _ Hland).
    pose proof (Z.log2_nonneg (Z.land (wrap w x) (- wrap w x))).
    split; apply Z.leb_le; lia.
Qed.

Lemma interval_popcnt_sound : forall w x, interval_pgamma w (interval_counts w) (wpopcnt w x).
Proof.
  intros w x. split; [apply wpopcnt_is_word |].
  cbn [interval_counts interval_gamma gamma bound_leb].
  unfold wpopcnt. split; apply Z.leb_le; [lia |].
  rewrite <- (positive_nat_Z w). apply Nat2Z.inj_le.
  eapply Nat.le_trans; [apply List.filter_length_le |]. rewrite List.length_seq. lia.
Qed.

(** A nonzero divisor admits the usual monotone quotient bounds. *)
Definition interval_udiv (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.ltb 0 lb)%bool
    then interval_checked w (la / hb) (ha / lb)
    else if (Z.leb 0 la && Z.eqb lb 0 && Z.ltb 0 hb)%bool
         then interval_checked w (la / hb) (modulus w - 1)
         else if (Z.eqb lb 0 && Z.eqb hb 0)%bool
              then Itv (Fin (modulus w - 1)) (Fin (modulus w - 1))
              else interval_top w
  | _, _ => interval_top w
  end.

Lemma interval_udiv_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_udiv w a b) (wudiv w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_udiv.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wudiv_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
  destruct (Z.leb 0 la && Z.ltb 0 lb)%bool eqn:Hvalid.
  - apply andb_true_iff in Hvalid as [Hla Hlb]. apply Z.leb_le in Hla.
    apply Z.ltb_lt in Hlb. rewrite (wudiv_spec w x y Hwordx Hwordy ltac:(lia)).
    apply interval_checked_sound.
    + rewrite <- (wudiv_spec w x y Hwordx Hwordy ltac:(lia)). apply wudiv_is_word.
    + split.
      * eapply (Z.le_trans _ (x / hb));
          [apply Z.div_le_mono; lia | apply Z.div_le_compat_l; lia].
      * eapply (Z.le_trans _ (x / lb));
          [apply Z.div_le_compat_l; lia | apply Z.div_le_mono; lia].
  - destruct (Z.leb 0 la && Z.eqb lb 0 && Z.ltb 0 hb)%bool eqn:Hcontains.
    + repeat rewrite andb_true_iff in Hcontains. destruct Hcontains as [[Hla Hlb] Hhb].
      apply Z.leb_le in Hla. apply Z.eqb_eq in Hlb. apply Z.ltb_lt in Hhb.
      apply interval_checked_sound; [apply wudiv_is_word |].
      destruct (Z.eqb y 0) eqn:Hzero.
      * apply Z.eqb_eq in Hzero. subst y. rewrite wudiv_zero.
        pose proof (Z.div_le_upper_bound la hb (modulus w - 1) Hhb
          ltac:(pose proof (modulus_pos w); destruct Hwordx; nia)). lia.
      * apply Z.eqb_neq in Hzero. rewrite (wudiv_spec w x y Hwordx Hwordy Hzero).
        assert (Hlower : (la / hb <= x / y)%Z).
        { eapply (Z.le_trans _ (x / hb));
            [apply Z.div_le_mono; lia | apply Z.div_le_compat_l; destruct Hwordy; lia]. }
        pose proof (wudiv_is_word w x y) as Hword.
        rewrite (wudiv_spec w x y Hwordx Hwordy Hzero) in Hword. destruct Hword. lia.
    + destruct (Z.eqb lb 0 && Z.eqb hb 0)%bool eqn:Hzero;
        [|apply interval_top_sound; apply wudiv_is_word].
      apply andb_true_iff in Hzero as [Hlb Hhb]. apply Z.eqb_eq in Hlb. apply Z.eqb_eq in Hhb.
      assert (y = 0)%Z by lia. subst y. rewrite wudiv_zero.
      split; [apply ones_is_word |]. cbn [interval_gamma gamma bound_leb].
      now rewrite Z.leb_refl.
Qed.

(** Remainders are at most the dividend and, for nonzero divisors, below the divisor. *)
Definition interval_urem (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.ltb 0 lb && Z.eqb (la / hb) (ha / lb))%bool then
      let quotient := la / hb in
      interval_checked w (la - quotient * hb) (ha - quotient * lb)
    else interval_checked w 0 (if Z.ltb 0 lb then Z.min ha (hb - 1) else ha)
  | _, _ => interval_top w
  end.

Lemma interval_urem_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_urem w a b) (wurem w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_urem.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wurem_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
  destruct (Z.leb 0 la && Z.ltb 0 lb && Z.eqb (la / hb) (ha / lb))%bool eqn:Hexact.
  - repeat rewrite andb_true_iff in Hexact. destruct Hexact as [[Hla Hlb] Hquot].
    apply Z.leb_le in Hla. apply Z.ltb_lt in Hlb. apply Z.eqb_eq in Hquot.
    assert (Hlower : (la / hb <= x / y)%Z).
    { eapply (Z.le_trans _ (x / hb));
        [apply Z.div_le_mono; lia | apply Z.div_le_compat_l; lia]. }
    assert (Hupper : (x / y <= ha / lb)%Z).
    { eapply (Z.le_trans _ (x / lb));
        [apply Z.div_le_compat_l; lia | apply Z.div_le_mono; lia]. }
    assert (Hq : (x / y = la / hb)%Z) by lia.
    assert (Hqnonnegative : (0 <= la / hb)%Z) by (apply Z.div_pos; lia).
    apply interval_checked_sound; [apply wurem_is_word |].
    rewrite (wurem_spec w x y Hwordx Hwordy ltac:(lia)).
    pose proof (Z.div_mod x y ltac:(lia)) as Hdivision. rewrite Hq in Hdivision. nia.
  - apply interval_checked_sound; [apply wurem_is_word |].
    destruct (Z.ltb 0 lb) eqn:Hpositive.
    + apply Z.ltb_lt in Hpositive.
    rewrite (wurem_spec w x y Hwordx Hwordy ltac:(lia)).
    pose proof (Z.mod_pos_bound x y ltac:(lia)).
    pose proof (Z.mod_le x y (proj1 Hwordx) ltac:(lia)).
      split; [lia | apply Z.min_glb; lia].
    + unfold wurem. rewrite (wrap_id w x Hwordx), (wrap_id w y Hwordy).
      destruct (Z.eqb y 0) eqn:Hzero; [destruct Hwordx; lia |].
      apply Z.eqb_neq in Hzero.
      pose proof (Z.mod_pos_bound x y ltac:(destruct Hwordy; lia)).
      pose proof (Z.mod_le x y (proj1 Hwordx) ltac:(destruct Hwordy; lia)). lia.
Qed.

(** A bounded left shift uses monotone multiplication by powers of two. *)
Definition interval_shl (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (la * 2 ^ lb) (ha * 2 ^ hb) else interval_top w
  | _, _ => interval_top w
  end.

Lemma interval_shl_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_shl w a b) (wshl w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_shl.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wshl_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
  destruct (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool eqn:Hrange;
    [|apply interval_top_sound; apply wshl_is_word].
  repeat rewrite andb_true_iff in Hrange. destruct Hrange as [[Hla Hlb] Hhb].
  apply Z.leb_le in Hla. apply Z.leb_le in Hlb. apply Z.ltb_lt in Hhb.
  assert (Hpowlo : (2 ^ lb <= 2 ^ y)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowhi : (2 ^ y <= 2 ^ hb)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowpos : (0 < 2 ^ lb)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Hbounds : (la * 2 ^ lb <= x * 2 ^ y <= ha * 2 ^ hb)%Z) by nia.
  unfold wshl. rewrite (wrap_id w x Hwordx), (wrap_id w y Hwordy).
  assert (Hshift : (Zpos w <=? y)%Z = false) by (apply Z.leb_gt; lia).
  rewrite Hshift. unfold interval_checked.
  destruct (Z.leb 0 (la * 2 ^ lb) && Z.ltb (ha * 2 ^ hb) (modulus w))%bool
    eqn:Hfit; [|apply interval_top_sound; apply wrap_is_word].
  apply andb_true_iff in Hfit as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  assert (Hword : is_word w (x * 2 ^ y)) by (unfold is_word; lia).
  rewrite (wrap_id w _ Hword). split; [exact Hword |].
  cbn [interval_gamma gamma bound_leb]. split; apply Z.leb_le; lia.
Qed.

(** A bounded logical right shift divides by the corresponding powers of two. *)
Definition interval_lshr (w : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    if (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool
    then interval_checked w (la / 2 ^ hb) (ha / 2 ^ lb) else interval_top w
  | _, _ => interval_top w
  end.

Lemma interval_lshr_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_lshr w a b) (wlshr w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_lshr.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wlshr_is_word).
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  destruct Ha as [Hwordx _]. destruct Hb as [Hwordy _].
  destruct (Z.leb 0 la && Z.leb 0 lb && Z.ltb hb (Zpos w))%bool eqn:Hrange;
    [|apply interval_top_sound; apply wlshr_is_word].
  repeat rewrite andb_true_iff in Hrange. destruct Hrange as [[Hla Hlb] Hhb].
  apply Z.leb_le in Hla. apply Z.leb_le in Hlb. apply Z.ltb_lt in Hhb.
  assert (Hpowlo : (2 ^ lb <= 2 ^ y)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowhi : (2 ^ y <= 2 ^ hb)%Z) by (apply Z.pow_le_mono_r; lia).
  assert (Hpowpos : (0 < 2 ^ lb)%Z) by (apply Z.pow_pos_nonneg; lia).
  unfold wlshr. rewrite (wrap_id w x Hwordx), (wrap_id w y Hwordy).
  assert (Hshift : (Zpos w <=? y)%Z = false) by (apply Z.leb_gt; lia).
  rewrite Hshift. apply interval_checked_sound.
  - pose proof (wlshr_is_word w x y) as Hresult.
    unfold wlshr in Hresult. rewrite (wrap_id w x Hwordx), (wrap_id w y Hwordy), Hshift in Hresult.
    exact Hresult.
  - split.
    + eapply (Z.le_trans _ (x / 2 ^ hb));
        [apply Z.div_le_mono; lia | apply Z.div_le_compat_l; lia].
    + eapply (Z.le_trans _ (x / 2 ^ lb));
        [apply Z.div_le_compat_l; lia | apply Z.div_le_mono; lia].
Qed.

(** Concatenation combines the endpoint values in the lower operand's radix. *)
Definition interval_concat (rw lower_width : width) (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    interval_checked rw (la * modulus lower_width + lb) (ha * modulus lower_width + hb)
  | _, _ => interval_top rw
  end.

Lemma interval_concat_sound : forall rw wa wb a b x y,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma rw (interval_concat rw wb a b) (wrap rw (x * modulus wb + y)).
Proof.
  intros rw wa wb a b x y Ha Hb. unfold interval_concat.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_top_sound; apply wrap_is_word).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  pose proof (modulus_pos wb) as Hmod.
  unfold interval_checked.
  destruct (Z.leb 0 (la * modulus wb + lb) &&
    Z.ltb (ha * modulus wb + hb) (modulus rw))%bool eqn:Hfit;
    [|apply interval_top_sound; apply wrap_is_word].
  apply andb_true_iff in Hfit as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  assert (Hbounds : (la * modulus wb + lb <= x * modulus wb + y <=
    ha * modulus wb + hb)%Z) by nia.
  assert (Hword : is_word rw (x * modulus wb + y)) by (unfold is_word; lia).
  rewrite (wrap_id rw _ Hword). split; [exact Hword |].
  cbn [interval_gamma gamma bound_leb]. split; apply Z.leb_le; lia.
Qed.

(** Extension or truncation preserves a range that fits the result width. *)
Definition interval_rewrap (rw : width) (a : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) => interval_checked rw lo hi
  | None => interval_top rw
  end.

Lemma interval_rewrap_sound : forall rw w a x,
  interval_pgamma w a x -> interval_pgamma rw (interval_rewrap rw a) (wrap rw x).
Proof.
  intros rw w a x Ha. unfold interval_rewrap.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite;
    [|apply interval_top_sound; apply wrap_is_word].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hbounds.
  unfold interval_checked. destruct (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool eqn:Hfit;
    [|apply interval_top_sound; apply wrap_is_word].
  apply andb_true_iff in Hfit as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  assert (Hword : is_word rw x) by (unfold is_word; lia).
  rewrite (wrap_id rw x Hword). split; [exact Hword |].
  cbn [interval_gamma gamma bound_leb]. split; apply Z.leb_le; lia.
Qed.

(** A decided comparison is a singleton; otherwise both Boolean values are possible. *)
Definition interval_truth (decision : option bool) : interval :=
  match decision with
  | Some true => Itv (Fin 1) (Fin 1)
  | Some false => Itv (Fin 0) (Fin 0)
  | None => Itv (Fin 0) (Fin 1)
  end.

Lemma interval_truth_sound : forall w decision value,
  (decision = Some true -> value = true) -> (decision = Some false -> value = false) ->
  interval_pgamma w (interval_truth decision) (if value then 1 else 0).
Proof.
  intros w [[|]|] value Htrue Hfalse; destruct value; cbn in *;
    try (exfalso; specialize (Htrue eq_refl); discriminate);
    try (exfalso; specialize (Hfalse eq_refl); discriminate);
    split; try apply one_is_word; try apply zero_is_word; split; reflexivity.
Qed.

(** Complement a Boolean interval, preserving an undecided pair. *)
Definition interval_bool_not (a : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.eqb lo 0 && Z.eqb hi 0 then interval_truth (Some true)
    else if Z.eqb lo 1 && Z.eqb hi 1 then interval_truth (Some false)
    else interval_truth None
  | None => interval_truth None
  end.

Lemma interval_bool_not_sound : forall w a (b : bool),
  interval_pgamma w a (if b then 1 else 0) ->
  interval_pgamma w (interval_bool_not a) (if negb b then 1 else 0).
Proof.
  intros w a b Ha. unfold interval_bool_not.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite;
    [|apply interval_truth_sound; discriminate].
  pose proof (interval_finite_sound w a lo hi (if b then 1 else 0) Ha Hfinite) as Hbounds.
  destruct (Z.eqb lo 0 && Z.eqb hi 0)%bool eqn:Hzero.
  - apply andb_true_iff in Hzero as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
    destruct b; cbn in Hbounds; [lia |].
    apply interval_truth_sound; [reflexivity | discriminate].
  - destruct (Z.eqb lo 1 && Z.eqb hi 1)%bool eqn:Hone.
    + apply andb_true_iff in Hone as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
      destruct b; cbn in Hbounds; [|lia].
      apply interval_truth_sound; [discriminate | reflexivity].
    + apply interval_truth_sound; discriminate.
Qed.

(** Unsigned less-than is decided when the endpoint ranges are separated. *)
Definition interval_ult (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    interval_truth (if Z.ltb ha lb then Some true
                    else if Z.leb hb la then Some false else None)
  | _, _ => interval_truth None
  end.

Lemma interval_ult_sound : forall wa wb a b x y w,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_ult a b) (if Z.ltb x y then 1 else 0).
Proof.
  intros wa wb a b x y w Ha Hb. unfold interval_ult.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_truth_sound; discriminate).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  destruct (Z.ltb ha lb) eqn:Htrue.
  - apply Z.ltb_lt in Htrue. apply interval_truth_sound; [|discriminate].
    intros _. apply Z.ltb_lt. lia.
  - destruct (Z.leb hb la) eqn:Hfalse.
    + apply Z.leb_le in Hfalse. apply interval_truth_sound; [discriminate|].
      intros _. apply Z.ltb_ge. lia.
    + apply interval_truth_sound; discriminate.
Qed.

(** Unsigned less-or-equal is decided when the endpoint ranges establish its result. *)
Definition interval_ule (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    interval_truth (if Z.leb ha lb then Some true
                    else if Z.ltb hb la then Some false else None)
  | _, _ => interval_truth None
  end.

Lemma interval_ule_sound : forall wa wb a b x y w,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_ule a b) (if Z.leb x y then 1 else 0).
Proof.
  intros wa wb a b x y w Ha Hb. unfold interval_ule.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_truth_sound; discriminate).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  destruct (Z.leb ha lb) eqn:Htrue.
  - apply Z.leb_le in Htrue. apply interval_truth_sound; [|discriminate].
    intros _. apply Z.leb_le. lia.
  - destruct (Z.ltb hb la) eqn:Hfalse.
    + apply Z.ltb_lt in Hfalse. apply interval_truth_sound; [discriminate|].
      intros _. apply Z.leb_gt. lia.
    + apply interval_truth_sound; discriminate.
Qed.

(** Equality is decided for disjoint ranges and equal singleton ranges. *)
Definition interval_eq (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    interval_truth (if (Z.ltb ha lb || Z.ltb hb la)%bool then Some false
      else if (Z.eqb la ha && Z.eqb lb hb && Z.eqb la lb)%bool then Some true else None)
  | _, _ => interval_truth None
  end.

Lemma interval_eq_sound : forall wa wb a b x y w,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_eq a b) (if Z.eqb x y then 1 else 0).
Proof.
  intros wa wb a b x y w Ha Hb. unfold interval_eq.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_truth_sound; discriminate).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  destruct (Z.ltb ha lb || Z.ltb hb la)%bool eqn:Hdisjoint.
  - assert (Hneq : x <> y).
    { apply orb_true_iff in Hdisjoint as [Hdisjoint | Hdisjoint];
        apply Z.ltb_lt in Hdisjoint; lia. }
    apply interval_truth_sound; [discriminate |]. intros _. now apply Z.eqb_neq.
  - destruct (Z.eqb la ha && Z.eqb lb hb && Z.eqb la lb)%bool eqn:Hpoint.
    + repeat rewrite andb_true_iff in Hpoint. destruct Hpoint as [[Ha' Hb'] Hab].
      apply Z.eqb_eq in Ha'. apply Z.eqb_eq in Hb'. apply Z.eqb_eq in Hab.
      apply interval_truth_sound; [intros _; apply Z.eqb_eq; lia | discriminate].
    + apply interval_truth_sound; discriminate.
Qed.

(** Signed endpoints are available when an interval lies wholly in one sign half. *)
Definition interval_signed (w : width) (a : interval) : option (Z * Z) :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.ltb hi (half w) then Some (lo, hi)
    else if Z.leb (half w) lo then Some (lo - modulus w, hi - modulus w)
    else None
  | None => None
  end.

Lemma interval_signed_sound : forall w a z lo hi,
  interval_pgamma w a z -> interval_signed w a = Some (lo, hi) ->
  (lo <= signed w z <= hi)%Z.
Proof.
  intros w a z lo hi Ha Hsigned. unfold interval_signed in Hsigned.
  destruct (interval_finite a) as [[l h]|] eqn:Hfinite; [|discriminate].
  pose proof (interval_finite_sound w a l h z Ha Hfinite) as Hbounds.
  destruct Ha as [Hword _]. unfold signed. rewrite (wrap_id w z Hword).
  destruct (Z.ltb h (half w)) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. inversion Hsigned; subst lo hi.
    assert (Htest : Z.ltb z (half w) = true) by (apply Z.ltb_lt; lia).
    now rewrite Htest.
  - destruct (Z.leb (half w) l) eqn:Hhigh; [|discriminate].
    apply Z.leb_le in Hhigh. inversion Hsigned; subst lo hi.
    assert (Htest : Z.ltb z (half w) = false) by (apply Z.ltb_ge; lia).
    rewrite Htest. lia.
Qed.

(** Sign extension shifts a wholly negative signed interval into the result word range. *)
Definition interval_sext (rw w : width) (a : interval) : interval :=
  match interval_signed w a with
  | Some (lo, hi) =>
    if Z.ltb hi 0 then interval_checked rw (modulus rw + lo) (modulus rw + hi)
    else if Z.leb 0 lo then interval_checked rw lo hi else interval_top rw
  | None => interval_top rw
  end.

Lemma interval_sext_sound : forall rw w a x,
  interval_pgamma w a x ->
  interval_pgamma rw (interval_sext rw w a) (wrap rw (signed w x)).
Proof.
  intros rw w a x Ha. unfold interval_sext.
  destruct (interval_signed w a) as [[lo hi]|] eqn:Hsigned;
    [|apply interval_top_sound; apply wrap_is_word].
  pose proof (interval_signed_sound w a x lo hi Ha Hsigned) as Hbounds.
  destruct (Z.ltb hi 0) eqn:Hnegative.
  - apply Z.ltb_lt in Hnegative. unfold interval_checked.
    destruct (Z.leb 0 (modulus rw + lo) && Z.ltb (modulus rw + hi) (modulus rw))%bool
      eqn:Hfit; [|apply interval_top_sound; apply wrap_is_word].
    apply andb_true_iff in Hfit as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    assert (Hword : is_word rw (modulus rw + signed w x)) by (unfold is_word; lia).
    rewrite <- (wrap_add_modulus rw (signed w x) 1).
    replace (signed w x + 1 * modulus rw)%Z with (modulus rw + signed w x)%Z by ring.
    rewrite (wrap_id rw _ Hword). split; [exact Hword |].
    cbn [interval_gamma gamma bound_leb]. split; apply Z.leb_le; lia.
  - destruct (Z.leb 0 lo) eqn:Hpositive; [|apply interval_top_sound; apply wrap_is_word].
    apply Z.leb_le in Hpositive. unfold interval_checked.
    destruct (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool eqn:Hfit;
      [|apply interval_top_sound; apply wrap_is_word].
    apply andb_true_iff in Hfit as [Hlo Hhi]. apply Z.ltb_lt in Hhi.
    assert (Hword : is_word rw (signed w x)) by (unfold is_word; lia).
    rewrite (wrap_id rw _ Hword). split; [exact Hword |].
    cbn [interval_gamma gamma bound_leb]. split; apply Z.leb_le; lia.
Qed.

(** Signed comparisons use the endpoints only when both sign halves are known. *)
Definition interval_signed_compare (w : width) (strict : bool) (a b : interval) : interval :=
  match interval_signed w a, interval_signed w b with
  | Some (la, ha), Some (lb, hb) =>
    if strict then
      interval_truth (if Z.ltb ha lb then Some true
                      else if Z.leb hb la then Some false else None)
    else
      interval_truth (if Z.leb ha lb then Some true
                      else if Z.ltb hb la then Some false else None)
  | _, _ => interval_truth None
  end.

Lemma interval_signed_compare_sound : forall w a b x y rw strict,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma rw (interval_signed_compare w strict a b)
    (if (if strict then Z.ltb (signed w x) (signed w y)
         else Z.leb (signed w x) (signed w y)) then 1 else 0).
Proof.
  intros w a b x y rw strict Ha Hb. unfold interval_signed_compare.
  destruct (interval_signed w a) as [[la ha]|] eqn:Hfa;
    destruct (interval_signed w b) as [[lb hb]|] eqn:Hfb;
    try (destruct strict; apply interval_truth_sound; discriminate).
  pose proof (interval_signed_sound w a x la ha Ha Hfa) as Hax.
  pose proof (interval_signed_sound w b y lb hb Hb Hfb) as Hby.
  destruct strict.
  - destruct (Z.ltb ha lb) eqn:Htrue.
    + apply Z.ltb_lt in Htrue. apply interval_truth_sound; [|discriminate].
      intros _. apply Z.ltb_lt. lia.
    + destruct (Z.leb hb la) eqn:Hfalse.
      * apply Z.leb_le in Hfalse. apply interval_truth_sound; [discriminate|].
        intros _. apply Z.ltb_ge. lia.
      * apply interval_truth_sound; discriminate.
  - destruct (Z.leb ha lb) eqn:Htrue.
    + apply Z.leb_le in Htrue. apply interval_truth_sound; [|discriminate].
      intros _. apply Z.leb_le. lia.
    + destruct (Z.ltb hb la) eqn:Hfalse.
      * apply Z.ltb_lt in Hfalse. apply interval_truth_sound; [discriminate|].
        intros _. apply Z.leb_gt. lia.
      * apply interval_truth_sound; discriminate.
Qed.

(** Threshold counts measure remaining outward steps at each endpoint. *)
Definition lower_count (ts : list Z) (z : Z) : nat :=
  length (filter (fun t => Z.ltb t z) ts).

Definition upper_count (ts : list Z) (z : Z) : nat :=
  length (filter (fun t => Z.ltb z t) ts).

Definition lower_rank (ts : list Z) (b : bound) : nat :=
  match b with
  | NegInf => 0
  | Fin z => S (lower_count ts z)
  | PosInf => S (length ts)
  end.

Definition upper_rank (ts : list Z) (b : bound) : nat :=
  match b with
  | NegInf => S (length ts)
  | Fin z => S (upper_count ts z)
  | PosInf => 0
  end.

Lemma lower_count_bounded : forall ts z, (lower_count ts z <= length ts)%nat.
Proof.
  intros ts z. unfold lower_count. induction ts as [|t rest IH]; cbn; [lia |].
  destruct (Z.ltb t z); cbn; lia.
Qed.

Lemma upper_count_bounded : forall ts z, (upper_count ts z <= length ts)%nat.
Proof.
  intros ts z. unfold upper_count. induction ts as [|t rest IH]; cbn; [lia |].
  destruct (Z.ltb z t); cbn; lia.
Qed.

Lemma lower_count_monotone : forall ts x y, (x <= y)%Z ->
  (lower_count ts x <= lower_count ts y)%nat.
Proof.
  intros ts x y Hxy. unfold lower_count. induction ts as [|t rest IH]; cbn; [lia |].
  destruct (Z.ltb t x) eqn:Htx, (Z.ltb t y) eqn:Hty; cbn; lia.
Qed.

Lemma upper_count_monotone : forall ts x y, (x <= y)%Z ->
  (upper_count ts y <= upper_count ts x)%nat.
Proof.
  intros ts x y Hxy. unfold upper_count. induction ts as [|t rest IH]; cbn; [lia |].
  destruct (Z.ltb y t) eqn:Hyt, (Z.ltb x t) eqn:Hxt; cbn; lia.
Qed.

Lemma lower_count_strict : forall ts x y, In x ts -> (x < y)%Z ->
  (lower_count ts x < lower_count ts y)%nat.
Proof.
  intros ts x y Hin Hxy. unfold lower_count. induction ts as [|t rest IH]; cbn in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst t. rewrite Z.ltb_irrefl. assert (Hlt : Z.ltb x y = true) by (apply Z.ltb_lt; exact Hxy).
      rewrite Hlt. cbn. pose proof (lower_count_monotone rest x y ltac:(lia)).
      unfold lower_count in H. lia.
    + specialize (IH Hin). destruct (Z.ltb t x) eqn:Htx, (Z.ltb t y) eqn:Hty;
        cbn in *; lia.
Qed.

Lemma upper_count_strict : forall ts x y, In y ts -> (x < y)%Z ->
  (upper_count ts y < upper_count ts x)%nat.
Proof.
  intros ts x y Hin Hxy. unfold upper_count. induction ts as [|t rest IH]; cbn in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst t. rewrite Z.ltb_irrefl. assert (Hlt : Z.ltb x y = true) by (apply Z.ltb_lt; exact Hxy).
      rewrite Hlt. cbn. pose proof (upper_count_monotone rest x y ltac:(lia)).
      unfold upper_count in H. lia.
    + specialize (IH Hin). destruct (Z.ltb y t) eqn:Hyt, (Z.ltb x t) eqn:Hxt;
        cbn in *; lia.
Qed.

Lemma lower_rank_monotone : forall ts a b, bound_leb a b = true ->
  (lower_rank ts a <= lower_rank ts b)%nat.
Proof.
  intros ts [|x|] [|y|] Hle; cbn in *; try discriminate; try lia.
  - apply Z.leb_le in Hle. pose proof (lower_count_monotone ts x y Hle). lia.
  - pose proof (lower_count_bounded ts x). lia.
Qed.

Lemma upper_rank_monotone : forall ts a b, bound_leb a b = true ->
  (upper_rank ts b <= upper_rank ts a)%nat.
Proof.
  intros ts [|x|] [|y|] Hle; cbn in *; try discriminate; try lia.
  - pose proof (upper_count_bounded ts y). lia.
  - apply Z.leb_le in Hle. pose proof (upper_count_monotone ts x y Hle). lia.
Qed.

Lemma lower_count_member_bound : forall ts x, In x ts ->
  (lower_count ts x < length ts)%nat.
Proof.
  intros ts x Hin. induction ts as [|t rest IH]; cbn in Hin; [contradiction |].
  unfold lower_count in *. cbn. destruct Hin as [Heq | Hin].
  - subst t. rewrite Z.ltb_irrefl. pose proof (lower_count_bounded rest x).
    unfold lower_count in H. cbn. lia.
  - specialize (IH Hin). unfold lower_count in IH.
    destruct (Z.ltb t x); cbn; lia.
Qed.

Lemma upper_count_member_bound : forall ts x, In x ts ->
  (upper_count ts x < length ts)%nat.
Proof.
  intros ts x Hin. induction ts as [|t rest IH]; cbn in Hin; [contradiction |].
  unfold upper_count in *. cbn. destruct Hin as [Heq | Hin].
  - subst t. rewrite Z.ltb_irrefl. pose proof (upper_count_bounded rest x).
    unfold upper_count in H. cbn. lia.
  - specialize (IH Hin). unfold upper_count in IH.
    destruct (Z.ltb x t); cbn; lia.
Qed.

Lemma widen_lower_progress : forall ts old next,
  bound_leb old next = false ->
  (lower_rank ts (widen_lower (threshold_index ts) old next) < lower_rank ts old)%nat.
Proof.
  intros ts [|x|] [|y|] Hmove; cbn in Hmove; try discriminate;
    unfold widen_lower; cbn [bound_leb]; try rewrite Hmove; cbn [lower_rank]; try lia.
  - pose proof (lower_threshold_lower (threshold_index ts) y) as Hlower.
    pose proof (lower_threshold_member (threshold_index ts) y) as Hmember.
    destruct (lower_threshold (threshold_index ts) y) as [|r|] eqn:Hresult;
      cbn in *; try contradiction; try lia.
    apply Z.leb_le in Hlower. apply Z.leb_gt in Hmove.
    apply threshold_index_values in Hmember.
    pose proof (lower_count_strict ts r x Hmember ltac:(lia)). lia.
  - pose proof (lower_threshold_member (threshold_index ts) y) as Hmember.
    destruct (lower_threshold (threshold_index ts) y) as [|r|] eqn:Hresult;
      cbn in *; try contradiction; try lia.
    apply threshold_index_values in Hmember.
    pose proof (lower_count_member_bound ts r Hmember). lia.
Qed.

Lemma widen_upper_progress : forall ts old next,
  bound_leb next old = false ->
  (upper_rank ts (widen_upper (threshold_index ts) old next) < upper_rank ts old)%nat.
Proof.
  intros ts [|x|] [|y|] Hmove; cbn in Hmove; try discriminate;
    unfold widen_upper; cbn [bound_leb]; try rewrite Hmove; cbn [upper_rank]; try lia.
  - pose proof (upper_threshold_member (threshold_index ts) y) as Hmember.
    destruct (upper_threshold (threshold_index ts) y) as [|r|] eqn:Hresult;
      cbn in *; try contradiction; try lia.
    apply threshold_index_values in Hmember.
    pose proof (upper_count_member_bound ts r Hmember). lia.
  - pose proof (upper_threshold_upper (threshold_index ts) y) as Hupper.
    pose proof (upper_threshold_member (threshold_index ts) y) as Hmember.
    destruct (upper_threshold (threshold_index ts) y) as [|r|] eqn:Hresult;
      cbn in *; try contradiction; try lia.
    apply Z.leb_le in Hupper. apply Z.leb_gt in Hmove.
    apply threshold_index_values in Hmember.
    pose proof (upper_count_strict ts x r Hmember ltac:(lia)). lia.
Qed.

Definition interval_rank (ts : list Z) (i : interval) : nat :=
  match i with
  | IBot => S (2 * S (length ts))
  | Itv l h => lower_rank ts l + upper_rank ts h
  end.

Lemma interval_rank_bound : forall ts i,
  (interval_rank ts i <= S (2 * S (length ts)))%nat.
Proof.
  intros ts [|l h]; cbn [interval_rank]; [lia |].
  destruct l as [|x|], h as [|y|]; cbn [lower_rank upper_rank];
    try pose proof (lower_count_bounded ts x);
    try pose proof (upper_count_bounded ts y); lia.
Qed.

(** Each strict widening step decreases a rank bounded by the threshold count. *)
Definition interval_wrank (thresholds : list Z) :
  bounded_widening_rank (interval_lattice thresholds).
Proof.
  unshelve refine (@BoundedWideningRank _ _
    (@WideningRank _ _ (interval_rank thresholds) _ _)
    (S (2 * S (length thresholds))) _).
  - intros [|la ha] [|lb hb] Hle; cbn [interval_lattice leb widen interval_rank] in *;
      try discriminate; try lia.
    pose proof (lower_rank_monotone thresholds _ _
      (widen_lower_old (threshold_index thresholds) la lb)) as Hlower.
    pose proof (upper_rank_monotone thresholds _ _
      (widen_upper_old (threshold_index thresholds) ha hb)) as Hupper. lia.
  - intros [|la ha] [|lb hb] Hle; cbn [interval_lattice leb widen interval_rank] in *;
      try discriminate; try lia.
    + pose proof (interval_rank_bound thresholds (Itv lb hb)) as Hbound.
      cbn [interval_rank] in Hbound.
      destruct lb as [|x|], hb as [|y|]; cbn [lower_rank upper_rank] in *;
        try pose proof (lower_count_bounded thresholds x);
        try pose proof (upper_count_bounded thresholds y); lia.
    + apply andb_false_iff in Hle as [Hlower | Hupper].
      * pose proof (widen_lower_progress thresholds la lb Hlower) as Hstrict.
        pose proof (upper_rank_monotone thresholds _ _
          (widen_upper_old (threshold_index thresholds) ha hb)) as Hstable. lia.
      * pose proof (lower_rank_monotone thresholds _ _
          (widen_lower_old (threshold_index thresholds) la lb)) as Hstable.
        pose proof (widen_upper_progress thresholds ha hb Hupper) as Hstrict. lia.
  - apply interval_rank_bound.
Defined.

Lemma interval_meet_lower_left : forall ts a b,
  leb (interval_lattice ts) (interval_meet a b) a = true.
Proof.
  intros ts [|la ha] [|lb hb]; cbn; try reflexivity.
  destruct (bounds_nonempty (bound_max la lb) (bound_min ha hb)); cbn; [|reflexivity].
  apply andb_true_iff. split; [apply bound_max_upper_l | apply bound_min_lower_l].
Qed.

Lemma interval_meet_sound : forall w a b z,
  interval_pgamma w a z -> interval_pgamma w b z ->
  interval_pgamma w (interval_meet a b) z.
Proof.
  intros w [|la ha] [|lb hb] z Ha Hb; cbn in Ha, Hb; try tauto.
  destruct Ha as [Hw [Hla Hha]]. destruct Hb as [_ [Hlb Hhb]].
  assert (Hlo : bound_leb (bound_max la lb) (Fin z) = true).
  { apply bound_max_least; assumption. }
  assert (Hhi : bound_leb (Fin z) (bound_min ha hb) = true).
  { apply bound_min_greatest; assumption. }
  assert (Hordered : bound_leb (bound_max la lb) (bound_min ha hb) = true).
  { eapply bound_leb_trans; eassumption. }
  assert (Hnonempty : bounds_nonempty (bound_max la lb) (bound_min ha hb) = true).
  { destruct (bound_max la lb), (bound_min ha hb); cbn in *; try discriminate; assumption. }
  cbn [interval_meet]. rewrite Hnonempty. split; [exact Hw |].
  split; assumption.
Qed.

(** Every operand is intersected with its unsigned word range before transfer. *)
Definition interval_clip (w : width) (a : interval) : interval :=
  interval_meet a (interval_top w).

Lemma interval_clip_sound : forall w a z,
  interval_pgamma w a z -> interval_pgamma w (interval_clip w a) z.
Proof.
  intros w a z Ha. apply interval_meet_sound; [exact Ha |].
  apply interval_top_sound. exact (proj1 Ha).
Qed.

(** A known equality intersects both operand intervals. *)
Definition interval_assume_equal (a b : interval) : interval * interval :=
  (interval_meet a b, interval_meet b a).

Lemma interval_assume_equal_sound : forall w a b z,
  interval_pgamma w a z -> interval_pgamma w b z ->
  interval_pgamma w (fst (interval_assume_equal a b)) z /\
  interval_pgamma w (snd (interval_assume_equal a b)) z.
Proof.
  intros w a b z Ha Hb. split; apply interval_meet_sound; assumption.
Qed.

(** A strict unsigned comparison tightens both operands using their opposite endpoints. *)
Definition interval_assume_ult (a b : interval) : interval * interval :=
  match interval_finite a, interval_finite b with
  | Some (la, _), Some (_, hb) =>
    (interval_meet a (Itv NegInf (Fin (hb - 1))),
     interval_meet b (Itv (Fin (la + 1)) PosInf))
  | _, _ => (a, b)
  end.

Lemma interval_assume_ult_sound : forall wa wb a b x y,
  interval_pgamma wa a x -> interval_pgamma wb b y -> (x < y)%Z ->
  interval_pgamma wa (fst (interval_assume_ult a b)) x /\
  interval_pgamma wb (snd (interval_assume_ult a b)) y.
Proof.
  intros wa wb a b x y Ha Hb Hlt. unfold interval_assume_ult.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb; cbn; try tauto.
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  split; apply interval_meet_sound; try assumption.
  - split; [exact (proj1 Ha) |]. cbn [interval_gamma gamma bound_leb].
    split; [reflexivity | apply Z.leb_le; lia].
  - split; [exact (proj1 Hb) |]. cbn [interval_gamma gamma bound_leb].
    split; [apply Z.leb_le; lia | reflexivity].
Qed.

(** A non-strict comparison tightens both operands without an endpoint offset. *)
Definition interval_assume_ule (a b : interval) : interval * interval :=
  match interval_finite a, interval_finite b with
  | Some (la, _), Some (_, hb) =>
    (interval_meet a (Itv NegInf (Fin hb)), interval_meet b (Itv (Fin la) PosInf))
  | _, _ => (a, b)
  end.

Lemma interval_assume_ule_sound : forall wa wb a b x y,
  interval_pgamma wa a x -> interval_pgamma wb b y -> (x <= y)%Z ->
  interval_pgamma wa (fst (interval_assume_ule a b)) x /\
  interval_pgamma wb (snd (interval_assume_ule a b)) y.
Proof.
  intros wa wb a b x y Ha Hb Hle. unfold interval_assume_ule.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb; cbn; try tauto.
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  split; apply interval_meet_sound; try assumption.
  - split; [exact (proj1 Ha) |]. cbn [interval_gamma gamma bound_leb].
    split; [reflexivity | apply Z.leb_le; lia].
  - split; [exact (proj1 Hb) |]. cbn [interval_gamma gamma bound_leb].
    split; [apply Z.leb_le; lia | reflexivity].
Qed.

Lemma interval_assume_ule_lower : forall ts a b,
  leb (interval_lattice ts) (fst (interval_assume_ule a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_ule a b)) b = true.
Proof.
  intros ts a b. assert (Hrefl : forall i, leb (interval_lattice ts) i i = true).
  { intros [|l h]; cbn; [reflexivity |]. now rewrite !bound_leb_refl. }
  unfold interval_assume_ule.
  destruct (interval_finite a) as [[la ha]|]; destruct (interval_finite b) as [[lb hb]|].
  - split; apply interval_meet_lower_left.
  - split; apply Hrefl.
  - split; apply Hrefl.
  - split; apply Hrefl.
Qed.

(** A nonwrapping sum can be inverted through the result and the other operand. *)
Definition interval_assume_add (w : width) (a b q : interval) : interval * interval :=
  match interval_finite a, interval_finite b, interval_finite q with
  | Some (la, ha), Some (lb, hb), Some (lq, hq) =>
    if Z.ltb (ha + hb) (modulus w) then
      (interval_meet a (Itv (Fin (lq - hb)) (Fin (hq - lb))),
       interval_meet b (Itv (Fin (lq - ha)) (Fin (hq - la))))
    else (a, b)
  | _, _, _ => (a, b)
  end.

Lemma interval_assume_add_sound : forall w a b q x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w q (wrap w (x + y)) ->
  interval_pgamma w (fst (interval_assume_add w a b q)) x /\
  interval_pgamma w (snd (interval_assume_add w a b q)) y.
Proof.
  intros w a b q x y Ha Hb Hq. unfold interval_assume_add.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    destruct (interval_finite q) as [[lq hq]|] eqn:Hfq; cbn; try tauto.
  destruct (Z.ltb (ha + hb) (Z.pow_pos 2 w)) eqn:Hfit; cbn; [|tauto].
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  pose proof (interval_finite_sound w q lq hq (wrap w (x + y)) Hq Hfq) as Hqsum.
  apply Z.ltb_lt in Hfit.
  change (ha + hb < modulus w)%Z in Hfit.
  assert (Hword : is_word w (x + y)) by
    (unfold is_word; pose proof (proj1 (proj1 Ha)); pose proof (proj1 (proj1 Hb)); lia).
  rewrite (wrap_id w _ Hword) in Hqsum.
  split; apply interval_meet_sound; try assumption.
  - split; [exact (proj1 Ha) |]. cbn [interval_gamma gamma bound_leb].
    split; apply Z.leb_le; lia.
  - split; [exact (proj1 Hb) |]. cbn [interval_gamma gamma bound_leb].
    split; apply Z.leb_le; lia.
Qed.

(** A nonwrapping difference can also be inverted on both operands. *)
Definition interval_assume_sub (a b q : interval) : interval * interval :=
  match interval_finite a, interval_finite b, interval_finite q with
  | Some (la, ha), Some (lb, hb), Some (lq, hq) =>
    if Z.leb hb la then
      (interval_meet a (Itv (Fin (lq + lb)) (Fin (hq + hb))),
       interval_meet b (Itv (Fin (la - hq)) (Fin (ha - lq))))
    else (a, b)
  | _, _, _ => (a, b)
  end.

Lemma interval_assume_sub_sound : forall w a b q x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w q (wrap w (x - y)) ->
  interval_pgamma w (fst (interval_assume_sub a b q)) x /\
  interval_pgamma w (snd (interval_assume_sub a b q)) y.
Proof.
  intros w a b q x y Ha Hb Hq. unfold interval_assume_sub.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    destruct (interval_finite q) as [[lq hq]|] eqn:Hfq; cbn; try tauto.
  destruct (Z.leb hb la) eqn:Hfit; cbn; [|tauto].
  pose proof (interval_finite_sound w a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound w b lb hb y Hb Hfb) as Hby.
  pose proof (interval_finite_sound w q lq hq (wrap w (x - y)) Hq Hfq) as Hqdiff.
  apply Z.leb_le in Hfit.
  assert (Hword : is_word w (x - y)) by
    (unfold is_word; pose proof (proj1 Ha); pose proof (proj1 Hb); unfold is_word in *; lia).
  rewrite (wrap_id w _ Hword) in Hqdiff.
  split; apply interval_meet_sound; try assumption.
  - split; [exact (proj1 Ha) |]. cbn [interval_gamma gamma bound_leb].
    split; apply Z.leb_le; lia.
  - split; [exact (proj1 Hb) |]. cbn [interval_gamma gamma bound_leb].
    split; apply Z.leb_le; lia.
Qed.

Lemma interval_assume_add_lower : forall ts w a b q,
  leb (interval_lattice ts) (fst (interval_assume_add w a b q)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_add w a b q)) b = true.
Proof.
  intros ts w a b q. assert (Hrefl : forall i, leb (interval_lattice ts) i i = true).
  { intros [|l h]; cbn; [reflexivity |]. now rewrite !bound_leb_refl. }
  unfold interval_assume_add.
  destruct (interval_finite a) as [[la ha]|]; destruct (interval_finite b) as [[lb hb]|];
    destruct (interval_finite q) as [[lq hq]|]; try (split; apply Hrefl).
  destruct (Z.ltb (ha + hb) (modulus w)); split;
    first [apply interval_meet_lower_left | apply Hrefl].
Qed.

Lemma interval_assume_sub_lower : forall ts a b q,
  leb (interval_lattice ts) (fst (interval_assume_sub a b q)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_sub a b q)) b = true.
Proof.
  intros ts a b q. assert (Hrefl : forall i, leb (interval_lattice ts) i i = true).
  { intros [|l h]; cbn; [reflexivity |]. now rewrite !bound_leb_refl. }
  unfold interval_assume_sub.
  destruct (interval_finite a) as [[la ha]|]; destruct (interval_finite b) as [[lb hb]|];
    destruct (interval_finite q) as [[lq hq]|]; try (split; apply Hrefl).
  destruct (Z.leb hb la); split; first [apply interval_meet_lower_left | apply Hrefl].
Qed.

Lemma interval_assume_equal_lower : forall ts a b,
  leb (interval_lattice ts) (fst (interval_assume_equal a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_equal a b)) b = true.
Proof.
  intros ts a b. split; apply interval_meet_lower_left.
Qed.

Lemma interval_assume_ult_lower : forall ts a b,
  leb (interval_lattice ts) (fst (interval_assume_ult a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_ult a b)) b = true.
Proof.
  intros ts a b. assert (Hrefl : forall i, leb (interval_lattice ts) i i = true).
  { intros [|l h]; cbn; [reflexivity |]. now rewrite !bound_leb_refl. }
  unfold interval_assume_ult.
  destruct (interval_finite a) as [[la ha]|]; destruct (interval_finite b) as [[lb hb]|].
  - split; apply interval_meet_lower_left.
  - split; apply Hrefl.
  - split; apply Hrefl.
  - split; apply Hrefl.
Qed.

(** Interval ordering, hull, widening and narrowing satisfy the weak lattice laws. *)
Theorem interval_laws : forall thresholds, lattice_laws (interval_lattice thresholds).
Proof.
  intro thresholds. constructor.
  - intros [|l h]; cbn; [reflexivity |].
    now rewrite !bound_leb_refl.
  - intros [|la ha] [|lb hb] [|lc hc]; cbn; try discriminate; try reflexivity.
    intros Hab Hbc. apply andb_true_iff in Hab as [Hlb Hhb].
    apply andb_true_iff in Hbc as [Hlc Hhc]. apply andb_true_iff. split;
      eapply bound_leb_trans; eassumption.
  - intros [|l h]; reflexivity.
  - intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_l | apply bound_max_upper_l].
  - intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_r | apply bound_max_upper_r].
  - intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply widen_lower_old | apply widen_upper_old].
  - intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply widen_lower_next | apply widen_upper_next].
  - intros [|la ha] [|lb hb]; cbn; try discriminate; try reflexivity;
      try (intros _; now rewrite !bound_leb_refl).
    intros Hle. apply andb_true_iff in Hle as [Hl Hh]. apply andb_true_iff. split.
    + unfold narrow_bound. destruct la; try assumption; apply bound_leb_refl.
    + unfold narrow_bound. destruct ha; try assumption; apply bound_leb_refl.
  - intros [|la ha] [|lb hb]; cbn; try discriminate; try reflexivity;
      try (intros _; now rewrite !bound_leb_refl).
    intros Hle. apply andb_true_iff in Hle as [Hl Hh]. apply andb_true_iff. split.
    + unfold narrow_bound. destruct la; try assumption; apply bound_leb_refl.
    + unfold narrow_bound. destruct ha; try assumption; apply bound_leb_refl.
Qed.

(** The interval hull is the least upper bound for the boundwise order. *)
Theorem interval_lub : forall thresholds, lub_laws (interval_lattice thresholds).
Proof.
  intro thresholds. constructor.
  intros [|la ha] [|lb hb] [|lc hc]; cbn; try discriminate; try tauto.
  intros Ha Hb. apply andb_true_iff in Ha as [Hla Hha].
  apply andb_true_iff in Hb as [Hlb Hhb]. apply andb_true_iff. split.
  - now apply bound_min_greatest.
  - now apply bound_max_least.
Qed.

(** Ordered intervals preserve their concrete integer meaning. *)
Theorem interval_gamma_laws : forall thresholds,
  concretisation_laws (interval_lattice thresholds) interval_gamma.
Proof.
  intro thresholds. constructor.
  intros [|la ha] [|lb hb] z Hle Hgamma; cbn in *; try contradiction; try discriminate.
  apply andb_true_iff in Hle as [Hlower Hupper]. destruct Hgamma as [Hlo Hhi].
  split.
  - eapply bound_leb_trans; eassumption.
  - change (bound_leb (Fin z) hb = true).
    eapply bound_leb_trans; eassumption.
Qed.

(** Bottom denotes no integer. *)
Theorem interval_gamma_bot_empty : forall thresholds,
  bottom_empty (interval_lattice thresholds) interval_gamma.
Proof.
  intro thresholds. constructor. intros z H. exact H.
Qed.

Definition interval_swap (p : interval * interval) : interval * interval := (snd p, fst p).

(** A singleton interval supplies its unique endpoint. *)
Definition interval_singleton (a : interval) : option Z :=
  match interval_finite a with
  | Some (lo, hi) => if Z.eqb lo hi then Some lo else None
  | None => None
  end.

Lemma interval_singleton_sound : forall w a x c,
  interval_pgamma w a x -> interval_singleton a = Some c -> x = c.
Proof.
  intros w a x c Ha Hsingle. unfold interval_singleton in Hsingle.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite; [|discriminate].
  destruct (Z.eqb lo hi) eqn:Heq; [|discriminate].
  apply Z.eqb_eq in Heq. inversion Hsingle; subst c.
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite). lia.
Qed.

(** Excluding an endpoint removes it when the remaining set is representable by an interval. *)
Definition interval_exclude (a : interval) (c : Z) : interval :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.eqb lo c then interval_meet a (Itv (Fin (c + 1)) PosInf)
    else if Z.eqb hi c then interval_meet a (Itv NegInf (Fin (c - 1)))
    else a
  | None => a
  end.

Lemma interval_exclude_sound : forall w a x c,
  interval_pgamma w a x -> x <> c -> interval_pgamma w (interval_exclude a c) x.
Proof.
  intros w a x c Ha Hneq. unfold interval_exclude.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite; [|exact Ha].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hbounds.
  destruct (Z.eqb lo c) eqn:Hlo.
  - apply Z.eqb_eq in Hlo. apply interval_meet_sound; [exact Ha |].
    split; [exact (proj1 Ha) |]. cbn [interval_gamma gamma bound_leb].
    split; [apply Z.leb_le; lia | reflexivity].
  - destruct (Z.eqb hi c) eqn:Hhi; [|exact Ha].
    apply Z.eqb_eq in Hhi. apply interval_meet_sound; [exact Ha |].
    split; [exact (proj1 Ha) |]. cbn [interval_gamma gamma bound_leb].
    split; [reflexivity | apply Z.leb_le; lia].
Qed.

Lemma interval_exclude_lower : forall ts a c,
  leb (interval_lattice ts) (interval_exclude a c) a = true.
Proof.
  intros ts a c. unfold interval_exclude. destruct (interval_finite a) as [[lo hi]|];
    [|apply (leb_refl (interval_laws ts))].
  destruct (Z.eqb lo c); [apply interval_meet_lower_left |].
  destruct (Z.eqb hi c); [apply interval_meet_lower_left | apply (leb_refl (interval_laws ts))].
Qed.

(** Inequality excludes a known singleton from the other interval's endpoints. *)
Definition interval_assume_neq (a b : interval) : interval * interval :=
  (match interval_singleton b with Some c => interval_exclude a c | None => a end,
   match interval_singleton a with Some c => interval_exclude b c | None => b end).

Lemma interval_assume_neq_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y -> x <> y ->
  interval_pgamma w (fst (interval_assume_neq a b)) x /\
  interval_pgamma w (snd (interval_assume_neq a b)) y.
Proof.
  intros w a b x y Ha Hb Hneq. unfold interval_assume_neq. split; cbn.
  - destruct (interval_singleton b) as [c|] eqn:Hsingle; [|exact Ha].
    apply interval_exclude_sound; [exact Ha |].
    pose proof (interval_singleton_sound w b y c Hb Hsingle). congruence.
  - destruct (interval_singleton a) as [c|] eqn:Hsingle; [|exact Hb].
    apply interval_exclude_sound; [exact Hb |].
    pose proof (interval_singleton_sound w a x c Ha Hsingle). congruence.
Qed.

Lemma interval_assume_neq_lower : forall ts a b,
  leb (interval_lattice ts) (fst (interval_assume_neq a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_neq a b)) b = true.
Proof.
  intros ts a b. unfold interval_assume_neq. split.
  - destruct (interval_singleton b);
      [apply interval_exclude_lower | apply (leb_refl (interval_laws ts))].
  - destruct (interval_singleton a);
      [apply interval_exclude_lower | apply (leb_refl (interval_laws ts))].
Qed.

(** A finite clipped interval can decide the sign bit when it occupies one half. *)
Definition interval_sign (w : width) (a : interval) : option bool :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.ltb hi (half w) then Some false
    else if Z.leb (half w) lo then Some true else None
  | None => None
  end.

Lemma interval_sign_sound : forall w a x sign,
  interval_pgamma w a x -> interval_sign w a = Some sign -> msb w x = sign.
Proof.
  intros w a x sign Ha Hsign. unfold interval_sign in Hsign.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite; [|discriminate].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hbounds.
  rewrite msb_half, (wrap_id w x (proj1 Ha)).
  destruct (Z.ltb hi (half w)) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. inversion Hsign; subst sign.
    assert (Htest : Z.ltb x (half w) = true) by (apply Z.ltb_lt; lia).
    now rewrite Htest.
  - destruct (Z.leb (half w) lo) eqn:Hhigh; [|discriminate].
    apply Z.leb_le in Hhigh. inversion Hsign; subst sign.
    assert (Htest : Z.ltb x (half w) = false) by (apply Z.ltb_ge; lia).
    now rewrite Htest.
Qed.

Lemma interval_same_sign_order : forall w x y,
  is_word w x -> is_word w y -> msb w x = msb w y ->
  ((signed w x < signed w y)%Z <-> (x < y)%Z) /\
  ((signed w x <= signed w y)%Z <-> (x <= y)%Z).
Proof.
  intros w x y Hx Hy Hsame. rewrite !msb_half, (wrap_id w x Hx), (wrap_id w y Hy) in Hsame.
  unfold signed. rewrite (wrap_id w x Hx), (wrap_id w y Hy).
  destruct (Z.ltb x (half w)), (Z.ltb y (half w)); cbn in *; try discriminate; lia.
Qed.

(** Signed comparisons within one common sign half use the same endpoint order. *)
Definition interval_assume_signed (w : width) (strict result : bool)
  (a b : interval) : interval * interval :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    if Bool.eqb sa sb then
      match strict, result with
      | true, true => interval_assume_ult a b
      | true, false => interval_swap (interval_assume_ule b a)
      | false, true => interval_assume_ule a b
      | false, false => interval_swap (interval_assume_ult b a)
      end
    else (a, b)
  | _, _ => (a, b)
  end.

Lemma interval_assume_signed_sound : forall w (strict result : bool) a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  (if strict then Z.ltb (signed w x) (signed w y)
   else Z.leb (signed w x) (signed w y)) = result ->
  interval_pgamma w (fst (interval_assume_signed w strict result a b)) x /\
  interval_pgamma w (snd (interval_assume_signed w strict result a b)) y.
Proof.
  intros w strict result a b x y Ha Hb Hcmp. unfold interval_assume_signed.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb; try (split; assumption).
  destruct (Bool.eqb sa sb) eqn:Hsame; [|split; assumption].
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  assert (Hbits : msb w x = msb w y) by
    (rewrite Hx, Hy; destruct sa, sb; cbn in Hsame; congruence).
  pose proof (interval_same_sign_order w x y (proj1 Ha) (proj1 Hb) ltac:(congruence))
    as [Hlt Hle]. destruct strict, result; cbn in *.
  - apply Z.ltb_lt in Hcmp. apply Hlt in Hcmp. now apply interval_assume_ult_sound.
  - apply Z.ltb_ge in Hcmp. assert (Horder : (y <= x)%Z) by lia.
    destruct (interval_assume_ule_sound w w b a y x Hb Ha Horder); split; assumption.
  - apply Z.leb_le in Hcmp. apply Hle in Hcmp. now apply interval_assume_ule_sound.
  - apply Z.leb_gt in Hcmp. assert (Horder : (y < x)%Z) by lia.
    destruct (interval_assume_ult_sound w w b a y x Hb Ha Horder); split; assumption.
Qed.

Lemma interval_assume_signed_lower : forall ts w strict result a b,
  leb (interval_lattice ts) (fst (interval_assume_signed w strict result a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_signed w strict result a b)) b = true.
Proof.
  intros ts w strict result a b. unfold interval_assume_signed.
  destruct (interval_sign w a) as [sa|]; destruct (interval_sign w b) as [sb|];
    try (split; apply (leb_refl (interval_laws ts))).
  destruct (Bool.eqb sa sb); [|split; apply (leb_refl (interval_laws ts))].
  destruct strict, result.
  - apply interval_assume_ult_lower.
  - destruct (interval_assume_ule_lower ts b a). split; assumption.
  - apply interval_assume_ule_lower.
  - destruct (interval_assume_ult_lower ts b a). split; assumption.
Qed.

(** Signed division is reduced to unsigned division over magnitudes. *)
Definition interval_sdiv (w : width) (a b : interval) : interval :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let q := interval_udiv w aa bb in
    if xorb sa sb then interval_neg w q else q
  | _, _ => interval_top w
  end.

Lemma interval_sdiv_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_sdiv w a b) (wsdiv w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_sdiv.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb;
    try (apply interval_top_sound; apply wsdiv_is_word).
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  destruct sa, sb; unfold wsdiv; rewrite Hx, Hy; cbn;
    try (apply interval_neg_sound; apply interval_udiv_sound;
      try apply interval_neg_sound; assumption);
    apply interval_udiv_sound; try apply interval_neg_sound; assumption.
Qed.

(** Signed remainder follows the sign of its dividend. *)
Definition interval_srem (w : width) (a b : interval) : interval :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let r := interval_urem w aa bb in
    if sa then interval_neg w r else r
  | _, _ => interval_top w
  end.

Lemma interval_srem_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_srem w a b) (wsrem w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_srem.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb;
    try (apply interval_top_sound; apply wsrem_is_word).
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  destruct sa, sb; unfold wsrem; rewrite Hx, Hy; cbn;
    try (apply interval_neg_sound; apply interval_urem_sound;
      try apply interval_neg_sound; assumption);
    apply interval_urem_sound; try apply interval_neg_sound; assumption.
Qed.

Lemma interval_join_sound : forall ts w a b z,
  interval_pgamma w a z \/ interval_pgamma w b z ->
  interval_pgamma w (join (interval_lattice ts) a b) z.
Proof.
  intros ts w a b z [Ha | Hb]; split; [exact (proj1 Ha) | |exact (proj1 Hb) |].
  - eapply (gamma_monotone (interval_gamma_laws ts)); [apply (join_upper_l (interval_laws ts)) |].
    exact (proj2 Ha).
  - eapply (gamma_monotone (interval_gamma_laws ts)); [apply (join_upper_r (interval_laws ts)) |].
    exact (proj2 Hb).
Qed.

(** A zero remainder selects zero; otherwise the signed-modulus case selects its candidate. *)
Definition interval_mod_choice (u candidate : interval) : interval :=
  match interval_finite u with
  | Some (lo, hi) =>
    if Z.ltb 0 lo then candidate
    else if Z.eqb hi 0 then Itv (Fin 0) (Fin 0)
    else join (interval_lattice []) (Itv (Fin 0) (Fin 0)) candidate
  | None => join (interval_lattice []) (Itv (Fin 0) (Fin 0)) candidate
  end.

Lemma interval_mod_choice_sound : forall w u candidate r z,
  interval_pgamma w u r -> interval_pgamma w candidate z ->
  interval_pgamma w (interval_mod_choice u candidate) (if Z.eqb r 0 then r else z).
Proof.
  intros w u candidate r z Hu Hz. unfold interval_mod_choice.
  destruct (interval_finite u) as [[lo hi]|] eqn:Hfinite.
  - pose proof (interval_finite_sound w u lo hi r Hu Hfinite) as Hbounds.
    destruct (Z.ltb 0 lo) eqn:Hpositive.
    + apply Z.ltb_lt in Hpositive. assert (Hnonzero : Z.eqb r 0 = false)
        by (apply Z.eqb_neq; lia). now rewrite Hnonzero.
    + destruct (Z.eqb hi 0) eqn:Hzero.
      * apply Z.eqb_eq in Hzero. assert (r = 0)%Z by (pose proof (proj1 (proj1 Hu)); lia).
        subst r. cbn. split; [apply zero_is_word |]. cbn [interval_gamma gamma bound_leb].
        split; reflexivity.
      * apply interval_join_sound. destruct (Z.eqb r 0) eqn:Hzeroeq; [left | now right].
        apply Z.eqb_eq in Hzeroeq. subst r.
        split; [apply zero_is_word |]. cbn [interval_gamma gamma bound_leb]. split; reflexivity.
  - apply interval_join_sound. destruct (Z.eqb r 0) eqn:Hzeroeq; [left | now right].
    apply Z.eqb_eq in Hzeroeq. subst r.
    split; [apply zero_is_word |]. cbn [interval_gamma gamma bound_leb]. split; reflexivity.
Qed.

(** Signed modulus combines unsigned magnitudes with the divisor's sign. *)
Definition interval_smod_base (w : width) (a b : interval) : interval :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let u := interval_urem w aa bb in
    let candidate :=
      match sa, sb with
      | false, false => u
      | true, false => interval_add_modular w (interval_neg w u) b
      | false, true => interval_add_modular w u b
      | true, true => interval_neg w u
      end in
    interval_mod_choice u candidate
  | _, _ => interval_top w
  end.

Lemma interval_smod_base_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_smod_base w a b) (wsmod w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_smod_base.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb;
    try (apply interval_top_sound; apply wsmod_is_word).
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  destruct sa, sb; unfold wsmod; rewrite Hx, Hy; cbn [xorb];
    rewrite ?(wrap_id w x (proj1 Ha)), ?(wrap_id w y (proj1 Hb)).
  - apply interval_mod_choice_sound.
    + apply interval_urem_sound; apply interval_neg_sound; assumption.
    + apply interval_neg_sound. apply interval_urem_sound; apply interval_neg_sound; assumption.
  - apply interval_mod_choice_sound.
    + apply interval_urem_sound; [apply interval_neg_sound |]; assumption.
    + apply interval_add_modular_sound; [apply interval_neg_sound; apply interval_urem_sound;
        [apply interval_neg_sound |] |]; assumption.
  - apply interval_mod_choice_sound.
    + apply interval_urem_sound; [|apply interval_neg_sound]; assumption.
    + apply interval_add_modular_sound; [apply interval_urem_sound; [|apply interval_neg_sound] |];
        assumption.
  - apply interval_mod_choice_sound; apply interval_urem_sound; assumption.
Qed.

(** A strictly positive divisor bounds signed modulus in its nonnegative half. *)
Definition interval_smod (w : width) (a b : interval) : interval :=
  match interval_sign w b, interval_finite b with
  | Some false, Some (lo, hi) =>
    if Z.ltb 0 lo then
      interval_meet (interval_smod_base w a b) (Itv (Fin 0) (Fin (hi - 1)))
    else interval_smod_base w a b
  | _, _ => interval_smod_base w a b
  end.

Lemma interval_smod_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_smod w a b) (wsmod w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_smod.
  destruct (interval_sign w b) as [sign|] eqn:Hsign;
    [destruct sign |]; try now apply interval_smod_base_sound.
  destruct (interval_finite b) as [[lo hi]|] eqn:Hfinite;
    [|now apply interval_smod_base_sound].
  destruct (Z.ltb 0 lo) eqn:Hpositive; [|now apply interval_smod_base_sound].
  apply Z.ltb_lt in Hpositive.
  pose proof (interval_finite_sound w b lo hi y Hb Hfinite) as Hy.
  pose proof (interval_sign_sound w b y false Hb Hsign) as Hmsb.
  assert (Hsignedy : signed w y = y).
  { rewrite (signed_nonnegative w y Hmsb). apply wrap_id. exact (proj1 Hb). }
  pose proof (proj1 (wsmod_sign w x y) ltac:(rewrite Hsignedy; lia)) as Hmod.
  assert (Hword : is_word w (wsmod w x y)) by apply wsmod_is_word.
  assert (Hsigned : signed w (wsmod w x y) = wsmod w x y).
  { unfold signed. rewrite (wrap_id w _ Hword).
    destruct (Z.ltb (wsmod w x y) (half w)) eqn:Hhalf; [reflexivity |].
    unfold signed in Hmod. rewrite (wrap_id w _ Hword), Hhalf in Hmod.
    unfold is_word in Hword. lia. }
  apply interval_meet_sound; [now apply interval_smod_base_sound |].
  split; [exact Hword |]. cbn [interval_gamma gamma bound_leb].
  rewrite Hsignedy, Hsigned in Hmod. split; apply Z.leb_le; lia.
Qed.

Lemma interval_div_complement : forall x d,
  (0 <= x)%Z -> (0 < d)%Z -> ((-1 - x) / d = -1 - x / d)%Z.
Proof.
  intros x d Hx Hd. apply Z.diveq. right. left.
  pose proof (Z.div_mod x d ltac:(lia)) as Hdivision.
  pose proof (Z.mod_pos_bound x d Hd) as Hremainder. nia.
Qed.

Lemma interval_ashr_negative : forall w x y,
  is_word w x -> is_word w y -> msb w x = true ->
  washr w x y = wnot w (wlshr w (wnot w x) y).
Proof.
  intros w x y Hx Hy Hnegative. unfold washr, wlshr, wnot.
  rewrite (wrap_id w x Hx), (wrap_id w y Hy).
  rewrite (wrap_id w (modulus w - 1 - x)) by
    (pose proof (modulus_pos w); unfold is_word in *; lia).
  destruct (Z.leb (Zpos w) y) eqn:Hlarge.
  - rewrite Hnegative, wrap_0. lia.
  - rewrite msb_half, (wrap_id w x Hx) in Hnegative.
    apply Bool.negb_true_iff in Hnegative. apply Z.ltb_ge in Hnegative.
    unfold signed. rewrite (wrap_id w x Hx).
    assert (Hhalf : Z.ltb x (half w) = false) by (apply Z.ltb_ge; exact Hnegative).
    rewrite Hhalf. set (d := (2 ^ y)%Z).
    assert (Hd : (0 < d)%Z) by (unfold d; apply Z.pow_pos_nonneg; destruct Hy; lia).
    assert (Ht : (0 <= modulus w - 1 - x)%Z) by (destruct Hx; lia).
    replace (x - modulus w)%Z with (-1 - (modulus w - 1 - x))%Z by ring.
    rewrite interval_div_complement by assumption.
    pose proof (Z.div_pos (modulus w - 1 - x) d Ht Hd) as Hqlo.
    pose proof (Z.div_le_upper_bound (modulus w - 1 - x) d (modulus w - 1)
      ltac:(lia) ltac:(pose proof (modulus_pos w); pose proof (proj1 Hx); nia)) as Hqhi.
    assert (Hout : is_word w (modulus w - 1 - (modulus w - 1 - x) / d))
      by (unfold is_word; pose proof (modulus_pos w); lia).
    rewrite (wrap_id w ((modulus w - 1 - x) / d)) by
      (unfold is_word; pose proof (modulus_pos w); lia).
    rewrite <- (wrap_add_modulus w (-1 - (modulus w - 1 - x) / d) 1).
    replace (-1 - (modulus w - 1 - x) / d + 1 * modulus w)%Z with
      (modulus w - 1 - (modulus w - 1 - x) / d)%Z by ring.
    now rewrite (wrap_id w _ Hout).
Qed.

Lemma interval_ashr_nonnegative : forall w x y,
  is_word w x -> is_word w y -> msb w x = false -> washr w x y = wlshr w x y.
Proof.
  intros w x y Hx Hy Hsign. unfold washr.
  rewrite (wrap_id w y Hy). destruct (Z.leb (Zpos w) y) eqn:Hlarge.
  - rewrite Hsign. symmetry. apply (proj2 (wshl_big w x y Hy ltac:(now apply Z.leb_le))).
  - rewrite msb_half, (wrap_id w x Hx) in Hsign.
    apply Bool.negb_false_iff in Hsign. unfold signed. rewrite (wrap_id w x Hx), Hsign.
    assert (Hlogical : wlshr w x y = (x / 2 ^ y)%Z).
    { unfold wlshr. now rewrite (wrap_id w x Hx), (wrap_id w y Hy), Hlarge. }
    rewrite Hlogical. apply wrap_id. rewrite <- Hlogical. apply wlshr_is_word.
Qed.

(** Arithmetic right shift uses logical shift on positive or complemented negative inputs. *)
Definition interval_ashr_small (w : width) (a b : interval) : interval :=
  match interval_sign w a with
  | Some false => interval_lshr w a b
  | Some true => interval_not w (interval_lshr w (interval_not w a) b)
  | None => interval_top w
  end.

Lemma interval_ashr_small_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_ashr_small w a b) (washr w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_ashr_small.
  destruct (interval_sign w a) as [sign|] eqn:Hsign;
    [|apply interval_top_sound; apply washr_is_word].
  pose proof (interval_sign_sound w a x sign Ha Hsign) as Hmsb.
  destruct sign.
  - rewrite (interval_ashr_negative w x y (proj1 Ha) (proj1 Hb) Hmsb).
    apply interval_not_sound. apply interval_lshr_sound; [apply interval_not_sound |]; assumption.
  - rewrite (interval_ashr_nonnegative w x y (proj1 Ha) (proj1 Hb) Hmsb).
    now apply interval_lshr_sound.
Qed.

(** Include the saturated result when the shift interval reaches the word width. *)
Definition interval_ashr (w : width) (a b : interval) : interval :=
  match interval_sign w a, interval_finite b with
  | Some sign, Some (lo, hi) =>
    let saturated := if sign then modulus w - 1 else 0 in
    if Z.ltb hi (Zpos w) then interval_ashr_small w a b
    else if Z.leb (Zpos w) lo then Itv (Fin saturated) (Fin saturated)
    else join (interval_lattice [])
      (interval_ashr_small w a (Itv (Fin lo) (Fin (Zpos w - 1))))
      (Itv (Fin saturated) (Fin saturated))
  | _, _ => interval_ashr_small w a b
  end.

Lemma interval_ashr_sound : forall w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w (interval_ashr w a b) (washr w x y).
Proof.
  intros w a b x y Ha Hb. unfold interval_ashr.
  destruct (interval_sign w a) as [sign|] eqn:Hsign;
    [|now apply interval_ashr_small_sound].
  destruct (interval_finite b) as [[lo hi]|] eqn:Hfinite;
    [|now apply interval_ashr_small_sound].
  pose proof (interval_finite_sound w b lo hi y Hb Hfinite) as Hbounds.
  pose proof (interval_sign_sound w a x sign Ha Hsign) as Hmsb.
  destruct (Z.ltb hi (Zpos w)) eqn:Hhi; [now apply interval_ashr_small_sound |].
  assert (Hsaturated : (Zpos w <= y)%Z ->
    interval_pgamma w (Itv (Fin (if sign then modulus w - 1 else 0))
      (Fin (if sign then modulus w - 1 else 0))) (washr w x y)).
  { intro Hlarge. unfold washr. rewrite (wrap_id w y (proj1 Hb)).
    rewrite (proj2 (Z.leb_le _ _) Hlarge), Hmsb. destruct sign.
    - split; [unfold is_word; pose proof (modulus_pos w); lia |].
      cbn [interval_gamma gamma bound_leb]. split; apply Z.leb_refl.
    - split; [apply zero_is_word |].
      cbn [interval_gamma gamma bound_leb]. split; reflexivity. }
  destruct (Z.leb (Zpos w) lo) eqn:Hlo.
  - apply Hsaturated. apply Z.leb_le in Hlo. lia.
  - apply interval_join_sound. destruct (Z.leb (Zpos w) y) eqn:Hy.
    + right. apply Hsaturated. now apply Z.leb_le.
    + left. apply interval_ashr_small_sound; [exact Ha |].
      split; [exact (proj1 Hb) |]. cbn [interval_gamma gamma bound_leb].
      apply Z.leb_gt in Hy. split; apply Z.leb_le; lia.
Qed.

(** Forward transfer on already clipped operands. *)
Definition interval_forward_clipped (o : op) (wps : list (width * interval)) (rw : width) :
  interval :=
  match o, wps with
  | bvnot, [(_, a)] => interval_not rw a
  | bvneg, [(_, a)] => interval_neg rw a
  | (bvclz | bvctz | bvpopcnt), [_] => interval_counts rw
  | bvadd, [(_, a); (_, b)] => interval_add rw a b
  | bvsub, [(_, a); (_, b)] => interval_sub rw a b
  | bvmul, [(_, a); (_, b)] => interval_mul rw a b
  | bvudiv, [(_, a); (_, b)] => interval_udiv rw a b
  | bvurem, [(_, a); (_, b)] => interval_urem rw a b
  | bvsdiv, [(_, a); (_, b)] => interval_sdiv rw a b
  | bvsrem, [(_, a); (_, b)] => interval_srem rw a b
  | bvsmod, [(_, a); (_, b)] => interval_smod rw a b
  | bvand, [(_, a); (_, b)] => interval_and rw a b
  | (bvor | bvxor), [(_, a); (_, b)] => interval_or_xor rw a b
  | bvshl, [(_, a); (_, b)] => interval_shl rw a b
  | bvlshr, [(_, a); (_, b)] => interval_lshr rw a b
  | bvashr, [(_, a); (_, b)] => interval_ashr rw a b
  | bveq, [(_, a); (_, b)] => interval_eq a b
  | bvne, [(_, a); (_, b)] => interval_bool_not (interval_eq a b)
  | bvult, [(_, a); (_, b)] => interval_ult a b
  | bvule, [(_, a); (_, b)] => interval_ule a b
  | bvslt, [(w, a); (_, b)] => interval_signed_compare w true a b
  | bvsle, [(w, a); (_, b)] => interval_signed_compare w false a b
  | bvite, [_; (_, a); (_, b)] => join (interval_lattice []) a b
  | (bvzext _ | bvtrunc _), [(_, a)] => interval_rewrap rw a
  | bvsext _, [(w, a)] => interval_sext rw w a
  | bvconcat, [(_, a); (w, b)] => interval_concat rw w a b
  | _, _ => interval_top rw
  end.

Definition interval_clip_input (wp : width * interval) : width * interval :=
  (fst wp, interval_clip (fst wp) (snd wp)).

Definition interval_empty_input (wp : width * interval) : bool :=
  match snd wp with
  | IBot => true
  | Itv _ _ => false
  end.

Fixpoint interval_values (wps : list (width * interval)) : option (list word) :=
  match wps with
  | [] => Some []
  | (w, a) :: rest =>
    match interval_singleton a, interval_values rest with
    | Some x, Some xs => Some ((w, x) :: xs)
    | _, _ => None
    end
  end.

(** Population count uses the constant-size count bound instead of enumerating word bits. *)
Definition interval_point_fast (o : op) : bool :=
  match o with
  | bvpopcnt => false
  | _ => true
  end.

Lemma interval_values_sound : forall wps ys xs,
  Forall2 (payload_sound interval_pgamma) wps ys -> interval_values wps = Some xs -> xs = ys.
Proof.
  intros wps ys xs Hpayload. revert xs.
  induction Hpayload as [|[w a] [v z] rest tail Hhead Htail IH]; intros xs Hvalues; cbn in Hvalues.
  - now inversion Hvalues.
  - destruct (interval_singleton a) as [c|] eqn:Hsingle; [|discriminate].
    destruct (interval_values rest) as [zs|] eqn:Hrest; [|discriminate].
    inversion Hvalues; subst xs. destruct Hhead as [Hwidth [Hword Ha]]. cbn in Hwidth, Ha.
    subst v. pose proof (interval_singleton_sound w a z c Ha Hsingle). subst z.
    rewrite (IH zs eq_refl). reflexivity.
Qed.

(** Transfer clips operands and propagates empty intervals. *)
Definition interval_forward (o : op) (wps : list (width * interval)) (rw : width) : interval :=
  let clipped := map interval_clip_input wps in
  if existsb interval_empty_input clipped then IBot else
  if interval_point_fast o then
    match interval_values clipped with
    | Some xs =>
      match eval_op o xs with
      | Some (_, z) => Itv (Fin z) (Fin z)
      | None => IBot
      end
    | None => interval_forward_clipped o clipped rw
    end
  else interval_forward_clipped o clipped rw.

Lemma interval_forward_one_sound : forall o w a x rw z,
  interval_pgamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  interval_pgamma rw (interval_forward_clipped o [(w, a)] rw) z.
Proof.
  intros o w a x rw z Ha Heval.
  assert (Hresult : is_word rw z) by (exact (eval_op_is_word o [(w, x)] (rw, z) Heval)).
  destruct o; try (apply interval_top_sound; exact Hresult).
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvnot w x wnot eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply interval_not_sound. exact Ha.
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvneg w x wneg eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply interval_neg_sound. exact Ha.
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvclz w x wclz eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply interval_clz_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvctz w x wctz eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply interval_ctz_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvpopcnt w x wpopcnt eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply interval_popcnt_sound.
  - change (Some ((w + extra)%positive, wrap (w + extra)%positive (wrap w x)) =
      Some (rw, z)) in Heval.
    rewrite (wrap_id w x (proj1 Ha)) in Heval. inversion Heval; subst rw z.
    apply (interval_rewrap_sound _ w). exact Ha.
  - change (Some ((w + extra)%positive, wrap (w + extra)%positive (signed w (wrap w x))) =
      Some (rw, z)) in Heval.
    rewrite (wrap_id w x (proj1 Ha)) in Heval. inversion Heval; subst rw z.
    apply interval_sext_sound. exact Ha.
  - unfold eval_op in Heval. cbn [result_width map fst snd] in Heval.
    destruct (Pos.leb target w) eqn:Hwidth; [|discriminate].
    cbn [op_value normalize_word map fst snd] in Heval.
    rewrite (wrap_id w x (proj1 Ha)) in Heval. inversion Heval; subst rw z.
    apply (interval_rewrap_sound _ w). exact Ha.
Qed.

Lemma interval_forward_two_sound : forall o w v a b x y rw z,
  interval_pgamma w a x -> interval_pgamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  interval_pgamma rw (interval_forward_clipped o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v a b x y rw z Ha Hb Heval.
  assert (Hresult : is_word rw z) by (exact (eval_op_is_word o [(w, x); (v, y)] (rw, z) Heval)).
  destruct o; try (apply interval_top_sound; exact Hresult).
  all: try (assert (Hwv : w = v) by
    (pose proof (eval_op_width _ _ _ Heval) as Hwidth;
     cbn [result_width map fst] in Hwidth;
     destruct (Pos.eqb w v) eqn:Hsame; [now apply Pos.eqb_eq | discriminate]); subst v).
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvadd w x y wadd eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply (interval_add_sound w w w); assumption.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsub w x y wsub eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply (interval_sub_sound w w w); assumption.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvmul w x y wmul eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply (interval_mul_sound w w w); assumption.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvudiv w x y wudiv eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_udiv_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvurem w x y wurem eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_urem_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsdiv w x y wsdiv eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_sdiv_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsrem w x y wsrem eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_srem_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsmod w x y wsmod eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_smod_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvand w x y wand eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_and_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvor w x y wor eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. exact (proj1 (interval_or_xor_sound w a b x y Ha Hb)).
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvxor w x y wxor eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. exact (proj2 (interval_or_xor_sound w a b x y Ha Hb)).
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvshl w x y wshl eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_shl_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvlshr w x y wlshr eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_lshr_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvashr w x y washr eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_ashr_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bveq w x y
      (fun w' x' y' => Z.eqb (wrap w' x') (wrap w' y')) eq_refl)) Heval) as Hr.
    cbn beta in Hr.
    rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Hr.
    inversion Hr; subst rw z. exact (interval_eq_sound w w a b x y 1%positive Ha Hb).
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvne w x y
      (fun w' x' y' => negb (Z.eqb (wrap w' x') (wrap w' y'))) eq_refl)) Heval) as Hr.
    cbn beta in Hr.
    rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Hr.
    inversion Hr; subst rw z. apply interval_bool_not_sound.
    exact (interval_eq_sound w w a b x y 1%positive Ha Hb).
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvult w x y wult eq_refl)) Heval) as Hr.
    unfold wult in Hr. rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Hr.
    inversion Hr; subst rw z. exact (interval_ult_sound w w a b x y 1%positive Ha Hb).
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvule w x y wule eq_refl)) Heval) as Hr.
    unfold wule in Hr. rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Hr.
    inversion Hr; subst rw z. exact (interval_ule_sound w w a b x y 1%positive Ha Hb).
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvslt w x y wslt eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. exact (interval_signed_compare_sound w a b x y 1%positive true Ha Hb).
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvsle w x y wsle eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z.
    exact (interval_signed_compare_sound w a b x y 1%positive false Ha Hb).
  - unfold eval_op in Heval. cbn [result_width op_value normalize_word map fst snd] in Heval.
    rewrite (wrap_id w x (proj1 Ha)), (wrap_id v y (proj1 Hb)) in Heval.
    inversion Heval; subst rw z. apply (interval_concat_sound _ w v); assumption.
Qed.

Lemma interval_forward_three_sound : forall o w v u a b c x y t rw z,
  interval_pgamma w a x -> interval_pgamma v b y -> interval_pgamma u c t ->
  eval_op o [(w, x); (v, y); (u, t)] = Some (rw, z) ->
  interval_pgamma rw (interval_forward_clipped o [(w, a); (v, b); (u, c)] rw) z.
Proof.
  intros o w v u a b c x y t rw z Ha Hb Hc Heval.
  assert (Hresult : is_word rw z) by
    (exact (eval_op_is_word o [(w, x); (v, y); (u, t)] (rw, z) Heval)).
  destruct o; try (apply interval_top_sound; exact Hresult).
  pose proof (eval_op_width _ _ _ Heval) as Hwidth.
  cbn [result_width map fst] in Hwidth.
  destruct (Pos.eqb w 1 && Pos.eqb v u)%bool eqn:Hshape; [|discriminate].
  apply andb_true_iff in Hshape as [Hw Hvu]. apply Pos.eqb_eq in Hw, Hvu. subst w u.
  pose proof (eq_trans (eq_sym (eval_op_ite v y t x)) Heval) as Hr.
  inversion Hr; subst rw z. apply interval_join_sound.
  destruct (wrap 1%positive x =? 1)%Z;
    rewrite wrap_id by first [exact (proj1 Hb) | exact (proj1 Hc)]; auto.
Qed.

Lemma interval_clipped_payloads : forall wps ys,
  Forall2 (payload_sound interval_pgamma) wps ys ->
  Forall2 (payload_sound interval_pgamma) (map interval_clip_input wps) ys.
Proof.
  intros wps ys Hpayload. induction Hpayload as [|[w a] [v z] rest tail Hhead Htail IH].
  - constructor.
  - constructor; [|exact IH]. destruct Hhead as [Hwidth [Hword Ha]]. cbn in *.
    split; [exact Hwidth |]. split; [exact Hword |]. now apply interval_clip_sound.
Qed.

Lemma interval_clipped_nonempty : forall wps ys,
  Forall2 (payload_sound interval_pgamma) wps ys ->
  existsb interval_empty_input wps = false.
Proof.
  intros wps ys Hpayload. induction Hpayload as [|[w [|lo hi]] [v z] rest tail Hhead Htail IH];
    cbn; try reflexivity; try assumption.
  destruct Hhead as [_ [_ [_ Hempty]]]. exact (False_ind _ Hempty).
Qed.

Lemma interval_forward_clipped_sound : forall o wps ys rw z,
  Forall2 (payload_sound interval_pgamma) wps ys -> eval_op o ys = Some (rw, z) ->
  interval_pgamma rw (interval_forward_clipped o wps rw) z.
Proof.
  intros o wps ys rw z Hpayload Heval.
  destruct wps as [|[w a] [|[v b] [|[u c] [|wp rest]]]].
  - destruct o; apply interval_top_sound; exact (eval_op_is_word _ _ _ Heval).
  - inversion Hpayload as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
    destruct y as [wy x]. destruct Hhead as [Hwx [Hword Ha]]. cbn in Hwx, Ha. subst wy.
    exact (interval_forward_one_sound o w a x rw z Ha Heval).
  - inversion Hpayload as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
    destruct y as [wy x], y' as [vy y].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Ha, Hb. subst wy vy.
    exact (interval_forward_two_sound o w v a b x y rw z Ha Hb Heval).
  - inversion Hpayload as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst.
    inversion Htail' as [|wp y'' wps' tail'' Hhead'' Htail'']; subst.
    inversion Htail''; subst. destruct y as [wy x], y' as [vy y], y'' as [uy t].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]], Hhead'' as [Hut [Ht Hc]].
    cbn in Hwx, Hvy, Hut, Ha, Hb, Hc. subst wy vy uy.
    exact (interval_forward_three_sound o w v u a b c x y t rw z Ha Hb Hc Heval).
  - destruct o; apply interval_top_sound; exact (eval_op_is_word _ _ _ Heval).
Qed.

Lemma interval_forward_sound : forall o wps ys rw z,
  Forall2 (payload_sound interval_pgamma) wps ys -> eval_op o ys = Some (rw, z) ->
  interval_pgamma rw (interval_forward o wps rw) z.
Proof.
  intros o wps ys rw z Hpayload Heval. unfold interval_forward.
  pose proof (interval_clipped_payloads wps ys Hpayload) as Hclipped.
  rewrite (interval_clipped_nonempty _ _ Hclipped).
  destruct (interval_point_fast o); [|eapply interval_forward_clipped_sound; eassumption].
  destruct (interval_values (map interval_clip_input wps)) as [xs|] eqn:Hvalues.
  - pose proof (interval_values_sound _ _ _ Hclipped Hvalues) as Hsame. subst xs.
    rewrite Heval. split; [exact (eval_op_is_word _ _ _ Heval) |].
    cbn [interval_gamma gamma bound_leb]. now rewrite Z.leb_refl.
  - eapply interval_forward_clipped_sound; eassumption.
Qed.

(** A singleton result decides its concrete value. *)
Definition interval_is_point (i : interval) (z : Z) : bool :=
  match interval_finite i with
  | Some (lo, hi) => Z.eqb lo z && Z.eqb hi z
  | None => false
  end.

Lemma interval_is_point_sound : forall w i z value,
  interval_pgamma w i value -> interval_is_point i z = true -> value = z.
Proof.
  intros w i z value Hi Hpoint. unfold interval_is_point in Hpoint.
  destruct (interval_finite i) as [[lo hi]|] eqn:Hfinite; [|discriminate].
  apply andb_true_iff in Hpoint as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
  pose proof (interval_finite_sound w i lo hi value Hi Hfinite). lia.
Qed.

(** Backward transfer refines binary operands using the result interval. *)
Definition interval_assume_pair (o : op) (w : width) (a b q : interval) : interval * interval :=
  match o with
  | bveq => if interval_is_point q 1 then interval_assume_equal a b
            else if interval_is_point q 0 then interval_assume_neq a b else (a, b)
  | bvne => if interval_is_point q 0 then interval_assume_equal a b
            else if interval_is_point q 1 then interval_assume_neq a b else (a, b)
  | bvult => if interval_is_point q 1 then interval_assume_ult a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ule b a)
             else (a, b)
  | bvule => if interval_is_point q 1 then interval_assume_ule a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ult b a)
             else (a, b)
  | bvslt => if interval_is_point q 1 then interval_assume_signed w true true a b
             else if interval_is_point q 0 then interval_assume_signed w true false a b
             else (a, b)
  | bvsle => if interval_is_point q 1 then interval_assume_signed w false true a b
             else if interval_is_point q 0 then interval_assume_signed w false false a b
             else (a, b)
  | bvadd => interval_assume_add w a b q
  | bvsub => interval_assume_sub a b q
  | _ => (a, b)
  end.

Definition interval_assume_clipped (o : op) (clipped : list (width * interval))
  (rw : width) (q : interval) : list interval :=
  match clipped with
  | [(_, a)] =>
    match o with
    | bvzext _ | bvtrunc _ =>
      [match interval_finite a with
       | Some (lo, hi) =>
         if (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool then interval_meet a q else a
       | None => a
       end]
    | _ => [a]
    end
  | [(w, a); (_, b)] =>
    let '(a', b') := interval_assume_pair o w a b q in [a'; b']
  | _ => map snd clipped
  end.

Definition interval_assume (o : op) (wps : list (width * interval)) (rw : width)
  (q : interval) : list interval :=
  interval_assume_clipped o (map interval_clip_input wps) rw q.

Lemma interval_assume_pair_sound : forall o w v a b q x y rw z,
  interval_pgamma w a x -> interval_pgamma v b y -> interval_pgamma rw q z ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  interval_pgamma w (fst (interval_assume_pair o w a b q)) x /\
  interval_pgamma v (snd (interval_assume_pair o w a b q)) y.
Proof.
  intros o w v a b q x y rw z Ha Hb Hq Heval.
  destruct o; try (split; assumption).
  all: assert (Hwv : w = v) by
    (pose proof (eval_op_width _ _ _ Heval) as Hwidth;
     cbn [result_width map fst] in Hwidth;
     destruct (Pos.eqb w v) eqn:Hsame; [now apply Pos.eqb_eq | discriminate]); subst v.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvadd w x y wadd eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_assume_add_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsub w x y wsub eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply interval_assume_sub_sound.
  - unfold interval_assume_pair.
    pose proof (eq_trans (eq_sym (eval_op_cmp bveq w x y
      (fun w' x' y' => Z.eqb (wrap w' x') (wrap w' y')) eq_refl)) Heval) as Hr.
    cbn beta in Hr. rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Hr.
    destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Hr; subst rw z. destruct (Z.eqb x y) eqn:Heq; [|discriminate].
      apply Z.eqb_eq in Heq. subst y. now apply interval_assume_equal_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Hr; subst rw z. destruct (Z.eqb x y) eqn:Heq; [discriminate |].
      apply Z.eqb_neq in Heq. now apply interval_assume_neq_sound.
  - unfold interval_assume_pair.
    pose proof (eq_trans (eq_sym (eval_op_cmp bvne w x y
      (fun w' x' y' => negb (Z.eqb (wrap w' x') (wrap w' y'))) eq_refl)) Heval) as Hr.
    cbn beta in Hr. rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Hr.
    destruct (interval_is_point q 0) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 0 z Hq Hpoint) as Hz.
      inversion Hr; subst rw z. destruct (Z.eqb x y) eqn:Heq; [|discriminate].
      apply Z.eqb_eq in Heq. subst y. now apply interval_assume_equal_sound.
    + destruct (interval_is_point q 1) eqn:Hpoint1; [|split; assumption].
      pose proof (interval_is_point_sound rw q 1 z Hq Hpoint1) as Hz.
      inversion Hr; subst rw z. destruct (Z.eqb x y) eqn:Heq; [discriminate |].
      apply Z.eqb_neq in Heq. now apply interval_assume_neq_sound.
  - unfold interval_assume_pair.
    pose proof (eq_trans (eq_sym (eval_op_cmp bvult w x y wult eq_refl)) Heval) as Hr.
    unfold wult in Hr. rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Hr.
    destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Hr; subst rw z. destruct (Z.ltb x y) eqn:Hlt; [|discriminate].
      apply Z.ltb_lt in Hlt. now apply interval_assume_ult_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Hr; subst rw z. destruct (Z.ltb x y) eqn:Hlt; [discriminate |].
      apply Z.ltb_ge in Hlt.
      pose proof (interval_assume_ule_sound w w b a y x Hb Ha Hlt) as Hpair.
      destruct Hpair as [Hfirst Hsecond]. split; assumption.
  - unfold interval_assume_pair.
    pose proof (eq_trans (eq_sym (eval_op_cmp bvule w x y wule eq_refl)) Heval) as Hr.
    unfold wule in Hr. rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Hr.
    destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Hr; subst rw z. destruct (Z.leb x y) eqn:Hle; [|discriminate].
      apply Z.leb_le in Hle. now apply interval_assume_ule_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Hr; subst rw z. destruct (Z.leb x y) eqn:Hle; [discriminate |].
      apply Z.leb_gt in Hle.
      pose proof (interval_assume_ult_sound w w b a y x Hb Ha Hle) as Hpair.
      destruct Hpair as [Hfirst Hsecond]. split; assumption.
  - unfold interval_assume_pair.
    pose proof (eq_trans (eq_sym (eval_op_cmp bvslt w x y wslt eq_refl)) Heval) as Hr.
    unfold wslt in Hr. destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Hr; subst rw z. destruct (Z.ltb (signed w x) (signed w y)) eqn:Hlt;
        [|discriminate]. now apply interval_assume_signed_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Hr; subst rw z. destruct (Z.ltb (signed w x) (signed w y)) eqn:Hlt;
        [discriminate |]. now apply interval_assume_signed_sound.
  - unfold interval_assume_pair.
    pose proof (eq_trans (eq_sym (eval_op_cmp bvsle w x y wsle eq_refl)) Heval) as Hr.
    unfold wsle in Hr. destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Hr; subst rw z. destruct (Z.leb (signed w x) (signed w y)) eqn:Hle;
        [|discriminate]. now apply interval_assume_signed_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Hr; subst rw z. destruct (Z.leb (signed w x) (signed w y)) eqn:Hle;
        [discriminate |]. now apply interval_assume_signed_sound.
Qed.

Lemma interval_assume_pair_lower : forall ts o w a b q,
  leb (interval_lattice ts) (fst (interval_assume_pair o w a b q)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_pair o w a b q)) b = true.
Proof.
  intros ts o w a b q. destruct o; try (split; apply (leb_refl (interval_laws ts))).
  - apply interval_assume_add_lower.
  - apply interval_assume_sub_lower.
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_equal_lower |].
    destruct (interval_is_point q 0); [apply interval_assume_neq_lower |].
    split; apply (leb_refl (interval_laws ts)).
  - unfold interval_assume_pair. destruct (interval_is_point q 0);
      [apply interval_assume_equal_lower |].
    destruct (interval_is_point q 1); [apply interval_assume_neq_lower |].
    split; apply (leb_refl (interval_laws ts)).
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_ult_lower |].
    destruct (interval_is_point q 0); [|split; apply (leb_refl (interval_laws ts))].
    pose proof (interval_assume_ule_lower ts b a) as [Hfirst Hsecond]. split; assumption.
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_ule_lower |].
    destruct (interval_is_point q 0); [|split; apply (leb_refl (interval_laws ts))].
    pose proof (interval_assume_ult_lower ts b a) as [Hfirst Hsecond]. split; assumption.
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_signed_lower |].
    destruct (interval_is_point q 0); [apply interval_assume_signed_lower |].
    split; apply (leb_refl (interval_laws ts)).
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_signed_lower |].
    destruct (interval_is_point q 0); [apply interval_assume_signed_lower |].
    split; apply (leb_refl (interval_laws ts)).
Qed.

(** Rewrapping can be inverted when the operand already fits the result width. *)
Definition interval_assume_rewrap (rw : width) (a q : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) =>
    if (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool then interval_meet a q else a
  | None => a
  end.

Lemma interval_assume_rewrap_sound : forall rw w a q x,
  interval_pgamma w a x -> interval_pgamma rw q (wrap rw x) ->
  interval_pgamma w (interval_assume_rewrap rw a q) x.
Proof.
  intros rw w a q x Ha Hq. unfold interval_assume_rewrap.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite; [|exact Ha].
  destruct (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool eqn:Hfit; [|exact Ha].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hbounds.
  apply andb_true_iff in Hfit as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  assert (Hword : is_word rw x) by (unfold is_word; lia).
  rewrite (wrap_id rw x Hword) in Hq. apply interval_meet_sound; [exact Ha |].
  split; [exact (proj1 Ha) | exact (proj2 Hq)].
Qed.

Lemma interval_assume_rewrap_lower : forall ts rw a q,
  leb (interval_lattice ts) (interval_assume_rewrap rw a q) a = true.
Proof.
  intros ts rw a q. unfold interval_assume_rewrap.
  destruct (interval_finite a) as [[lo hi]|]; [|apply (leb_refl (interval_laws ts))].
  destruct (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool;
    [apply interval_meet_lower_left | apply (leb_refl (interval_laws ts))].
Qed.

Lemma interval_assume_one_sound : forall o w a x rw z q,
  interval_pgamma w a x -> interval_pgamma rw q z ->
  eval_op o [(w, x)] = Some (rw, z) ->
  Forall2 (fun p y => interval_pgamma (fst p) (snd p) (snd y))
    (combine [w] (interval_assume_clipped o [(w, a)] rw q)) [(w, x)].
Proof.
  intros o w a x rw z q Ha Hq Heval. destruct o;
    try (constructor; [exact Ha | constructor]).
  - change (Some ((w + extra)%positive, wrap (w + extra)%positive (wrap w x)) =
      Some (rw, z)) in Heval.
    rewrite (wrap_id w x (proj1 Ha)) in Heval. inversion Heval; subst rw z.
    constructor; [apply interval_assume_rewrap_sound with (rw := (w + extra)%positive);
      assumption | constructor].
  - unfold eval_op in Heval. cbn [result_width map fst snd] in Heval.
    destruct (Pos.leb target w) eqn:Hwidth; [|discriminate].
    cbn [op_value normalize_word map fst snd] in Heval.
    rewrite (wrap_id w x (proj1 Ha)) in Heval. inversion Heval; subst rw z.
    constructor; [apply interval_assume_rewrap_sound with (rw := target); assumption | constructor].
Qed.

Lemma interval_payload_identity : forall wps ys,
  Forall2 (payload_sound interval_pgamma) wps ys ->
  Forall2 (fun p y => interval_pgamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (map snd wps)) ys.
Proof.
  intros wps ys Hpayload. induction Hpayload as [|[w a] [v z] rest tail Hhead Htail IH];
    cbn; constructor; auto.
  destruct Hhead as [_ [_ Ha]]. exact Ha.
Qed.

Lemma interval_assume_clipped_sound : forall o wps ys rw z q,
  Forall2 (payload_sound interval_pgamma) wps ys -> eval_op o ys = Some (rw, z) ->
  interval_pgamma rw q z ->
  Forall2 (fun p y => interval_pgamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (interval_assume_clipped o wps rw q)) ys.
Proof.
  intros o wps ys rw z q Hpayload Heval Hq.
  destruct wps as [|[w a] [|[v b] [|wp rest]]].
  - inversion Hpayload. constructor.
  - inversion Hpayload as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
    destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Ha. subst wy.
    exact (interval_assume_one_sound o w a x rw z q Ha Hq Heval).
  - inversion Hpayload as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
    destruct y as [wy x], y' as [vy y].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Ha, Hb. subst wy vy.
    pose proof (interval_assume_pair_sound o w v a b q x y rw z Ha Hb Hq Heval) as Hpair.
    destruct (interval_assume_pair o w a b q) as [a' b'] eqn:Hpairdef.
    cbn in Hpair. cbn [interval_assume_clipped map combine fst snd].
    rewrite Hpairdef. cbn. destruct Hpair as [Ha' Hb']. constructor; [exact Ha' |].
    constructor; [exact Hb' | constructor].
  - apply interval_payload_identity. exact Hpayload.
Qed.

Lemma interval_assume_sound : forall o wps ys rw z q,
  Forall2 (payload_sound interval_pgamma) wps ys -> eval_op o ys = Some (rw, z) ->
  interval_pgamma rw q z ->
  Forall2 (fun p y => interval_pgamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (interval_assume o wps rw q)) ys.
Proof.
  intros o wps ys rw z q Hpayload Heval Hq. unfold interval_assume.
  assert (Hwidths : map fst (map interval_clip_input wps) = map fst wps).
  { rewrite map_map. apply map_ext. intros [w a]. reflexivity. }
  rewrite <- Hwidths. apply (interval_assume_clipped_sound o _ ys rw z q); try assumption.
  now apply interval_clipped_payloads.
Qed.

Lemma interval_snd_refl : forall ts (wps : list (width * interval)),
  Forall2 (fun wp p => leb (interval_lattice ts) p (snd wp) = true) wps (map snd wps).
Proof.
  intros ts wps. induction wps as [|[w a] rest IH]; cbn; constructor; auto.
  apply (leb_refl (interval_laws ts)).
Qed.

Lemma interval_assume_clipped_lower : forall ts o wps rw q,
  Forall2 (fun wp p => leb (interval_lattice ts) p (snd wp) = true)
    wps (interval_assume_clipped o wps rw q).
Proof.
  intros ts o wps rw q. destruct wps as [|[w a] [|[v b] [|wp rest]]].
  - constructor.
  - destruct o; apply Forall2_cons.
    all: try apply Forall2_nil.
    all: first [apply interval_assume_rewrap_lower | apply (leb_refl (interval_laws ts))].
  - pose proof (interval_assume_pair_lower ts o w a b q) as Hpair.
    destruct (interval_assume_pair o w a b q) as [a' b'] eqn:Hpairdef.
    cbn in Hpair. cbn [interval_assume_clipped]. rewrite Hpairdef. cbn.
    destruct Hpair as [Ha Hb]. constructor; [exact Ha |]. constructor; [exact Hb | constructor].
  - apply interval_snd_refl.
Qed.

Lemma interval_assume_lower : forall ts o wps rw q,
  Forall2 (fun wp p => leb (interval_lattice ts) p (snd wp) = true)
    wps (interval_assume o wps rw q).
Proof.
  intros ts o wps rw q. unfold interval_assume.
  pose proof (interval_assume_clipped_lower ts o (map interval_clip_input wps) rw q) as Hlower.
  remember (interval_assume_clipped o (map interval_clip_input wps) rw q) as qs.
  clear Heqqs. revert qs Hlower. induction wps as [|[w a] rest IH]; intros qs Hlower;
    inversion Hlower as [|wp p tail ps Hhead Htail]; subst; cbn; constructor.
  - eapply (leb_trans (interval_laws ts)); [exact Hhead |]. apply interval_meet_lower_left.
  - now apply IH.
Qed.

(** The width-indexed interval payload supplies forward and backward transfer. *)
Definition interval_domain (thresholds : list Z) : word_domain interval :=
  let lattice := interval_lattice thresholds in
  {| plat _ := lattice;
     ptop := interval_top;
     pconst := interval_const;
     pforward := interval_forward;
     passume := interval_assume;
     pmeet _ := interval_meet |}.

(** Interval transfer and refinement preserve all concrete word outcomes. *)
Theorem interval_word_laws : forall thresholds,
  word_laws (interval_domain thresholds) interval_pgamma.
Proof.
  intro thresholds. constructor.
  - intro w. apply interval_laws.
  - intros w a b z Hle [Hword Ha]. split; [exact Hword |].
    eapply (gamma_monotone (interval_gamma_laws thresholds)); eassumption.
  - intros w z [_ Hempty]. exact Hempty.
  - apply interval_top_sound.
  - apply interval_const_sound.
  - apply interval_forward_sound.
  - apply interval_assume_sound.
  - intros o wps rw q. apply interval_assume_lower.
  - intros w a b z. apply interval_meet_sound.
  - intros w a b. apply interval_meet_lower_left.
Qed.
