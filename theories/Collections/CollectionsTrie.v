(** * Canonical binary tries

    Finite maps on positive keys have seven nonempty node shapes, so an empty branch
    has only one representation. Keys follow their least significant bits first.

    For example, keys 2, 1 and 3 are visited in that order.
    Builds on: Stdlib binary integers, lists, booleans and sorted lists. *)

From Stdlib Require Import ZArith List Bool Sorting.Sorted.

Import List.ListNotations.

Module Trie.

Inductive ne (A : Type) : Type :=
  | N001 (r : ne A)
  | N010 (v : A)
  | N011 (v : A) (r : ne A)
  | N100 (l : ne A)
  | N101 (l r : ne A)
  | N110 (l : ne A) (v : A)
  | N111 (l : ne A) (v : A) (r : ne A).

Arguments N001 {A}.
Arguments N010 {A}.
Arguments N011 {A}.
Arguments N100 {A}.
Arguments N101 {A}.
Arguments N110 {A}.
Arguments N111 {A}.

Inductive t (A : Type) : Type :=
  | Empty
  | Nodes (n : ne A).

Arguments Empty {A}.
Arguments Nodes {A}.

(** The empty trie contains no bindings. *)
Definition empty {A} : t A := Empty.

(** Emptiness is decided by the outer constructor. *)
Definition is_empty {A} (tr : t A) : bool :=
  match tr with
  | Empty => true
  | Nodes _ => false
  end.

Definition left {A} (tr : t A) : t A :=
  match tr with
  | Nodes (N100 l) | Nodes (N101 l _) | Nodes (N110 l _) | Nodes (N111 l _ _) =>
    Nodes l
  | _ => Empty
  end.

Definition value {A} (tr : t A) : option A :=
  match tr with
  | Nodes (N010 v) | Nodes (N011 v _) | Nodes (N110 _ v) | Nodes (N111 _ v _) =>
    Some v
  | _ => None
  end.

Definition right {A} (tr : t A) : t A :=
  match tr with
  | Nodes (N001 r) | Nodes (N011 _ r) | Nodes (N101 _ r) | Nodes (N111 _ _ r) =>
    Nodes r
  | _ => Empty
  end.

(* The smart constructor never represents a node with three absent components. *)
Definition node {A} (l : t A) (o : option A) (r : t A) : t A :=
  match l, o, r with
  | Empty, None, Empty => Empty
  | Empty, None, Nodes r => Nodes (N001 r)
  | Empty, Some v, Empty => Nodes (N010 v)
  | Empty, Some v, Nodes r => Nodes (N011 v r)
  | Nodes l, None, Empty => Nodes (N100 l)
  | Nodes l, None, Nodes r => Nodes (N101 l r)
  | Nodes l, Some v, Empty => Nodes (N110 l v)
  | Nodes l, Some v, Nodes r => Nodes (N111 l v r)
  end.

Lemma left_node {A} (l r : t A) o : left (node l o r) = l.
Proof.
  destruct l, o, r; reflexivity.
Qed.

Lemma value_node {A} (l r : t A) o : value (node l o r) = o.
Proof.
  destruct l, o, r; reflexivity.
Qed.

Lemma right_node {A} (l r : t A) o : right (node l o r) = r.
Proof.
  destruct l, o, r; reflexivity.
Qed.

Lemma node_eta {A} (tr : t A) : node (left tr) (value tr) (right tr) = tr.
Proof.
  destruct tr as [|n]; [reflexivity|destruct n; reflexivity].
Qed.

Lemma node_ind {A} (P : t A -> Prop) :
  P Empty -> (forall l o r, P l -> P r -> P (node l o r)) -> forall tr, P tr.
Proof.
  intros Hempty Hnode [|n]; [exact Hempty|].
  induction n as [r IHr|v|v r IHr|l IHl|l IHl r IHr|l IHl v|l IHl v r IHr].
  - exact (Hnode Empty None (Nodes r) Hempty IHr).
  - exact (Hnode Empty (Some v) Empty Hempty Hempty).
  - exact (Hnode Empty (Some v) (Nodes r) Hempty IHr).
  - exact (Hnode (Nodes l) None Empty IHl Hempty).
  - exact (Hnode (Nodes l) None (Nodes r) IHl IHr).
  - exact (Hnode (Nodes l) (Some v) Empty IHl Hempty).
  - exact (Hnode (Nodes l) (Some v) (Nodes r) IHl IHr).
Qed.

(** Lookup consumes the key from its least significant bit. *)
Fixpoint get {A} (p : positive) (tr : t A) : option A :=
  match p with
  | xH => value tr
  | xO q => get q (left tr)
  | xI q => get q (right tr)
  end.

(** Empty tries bind no key. *)
Theorem get_empty {A} (p : positive) : get p (@empty A) = None.
Proof.
  induction p; cbn [get left right value empty]; assumption || reflexivity.
Qed.

Lemma get_node {A} (p : positive) (l r : t A) o :
  get p (node l o r) =
  match p with
  | xH => o
  | xO q => get q l
  | xI q => get q r
  end.
Proof.
  destruct p; cbn [get]; rewrite ?left_node, ?right_node, ?value_node; reflexivity.
Qed.

(** A trie is empty precisely when its emptiness test succeeds. *)
Theorem is_empty_spec {A} (tr : t A) : is_empty tr = true <-> tr = empty.
Proof.
  destruct tr; split; intro H; try reflexivity; discriminate H.
Qed.

(** Two tries with the same bindings have the same canonical representation. *)
Theorem extensionality {A} (t1 t2 : t A) :
  (forall p, get p t1 = get p t2) -> t1 = t2.
Proof.
  revert t2.
  induction t1 as [|l o r IHl IHr] using node_ind; intros t2 Hagree.
  - assert (Hempty : forall tr : t A, (forall p, get p tr = None) -> tr = Empty).
    { intros tr.
      induction tr as [|l o r IHl IHr] using node_ind; intro Hnone.
      - reflexivity.
      - assert (Hl : l = Empty).
        { apply IHl. intro p. specialize (Hnone (xO p)). rewrite get_node in Hnone.
          exact Hnone. }
        assert (Hr : r = Empty).
        { apply IHr. intro p. specialize (Hnone (xI p)). rewrite get_node in Hnone.
          exact Hnone. }
        specialize (Hnone xH). rewrite get_node in Hnone.
        rewrite Hl, Hr, Hnone. reflexivity. }
    symmetry. apply Hempty. intro p. rewrite <- Hagree. apply get_empty.
  - assert (Hl : l = left t2).
    { apply IHl. intro p. specialize (Hagree (xO p)). rewrite get_node in Hagree.
      exact Hagree. }
    assert (Hr : r = right t2).
    { apply IHr. intro p. specialize (Hagree (xI p)). rewrite get_node in Hagree.
      exact Hagree. }
    specialize (Hagree xH). rewrite get_node in Hagree.
    rewrite Hl, Hr, Hagree. apply node_eta.
Qed.

(** Setting follows only the path of the updated key. *)
Fixpoint set {A} (p : positive) (v : A) (tr : t A) : t A :=
  match p with
  | xH => node (left tr) (Some v) (right tr)
  | xO q => node (set q v (left tr)) (value tr) (right tr)
  | xI q => node (left tr) (value tr) (set q v (right tr))
  end.

(** Removal collapses each newly empty node along the key path. *)
Fixpoint remove {A} (p : positive) (tr : t A) : t A :=
  match p with
  | xH => node (left tr) None (right tr)
  | xO q => node (remove q (left tr)) (value tr) (right tr)
  | xI q => node (left tr) (value tr) (remove q (right tr))
  end.

(** Lookup at the updated key returns its new value. *)
Theorem get_set_same {A} (tr : t A) p v : get p (set p v tr) = Some v.
Proof.
  revert tr. induction p; intro tr; cbn [set]; rewrite get_node; auto.
Qed.

(** Updating a distinct key preserves lookup. *)
Theorem get_set_other {A} (tr : t A) p q v :
  p <> q -> get q (set p v tr) = get q tr.
Proof.
  revert tr q. induction p; intros tr q Hneq; destruct q; cbn [set];
    rewrite get_node; cbn [get]; try reflexivity; try congruence;
    apply IHp; congruence.
Qed.

(** Lookup at a removed key returns no value. *)
Theorem get_remove_same {A} (tr : t A) p : get p (remove p tr) = None.
Proof.
  revert tr. induction p; intro tr; cbn [remove]; rewrite get_node; auto.
Qed.

(** Removing a distinct key preserves lookup. *)
Theorem get_remove_other {A} (tr : t A) p q :
  p <> q -> get q (remove p tr) = get q tr.
Proof.
  revert tr q. induction p; intros tr q Hneq; destruct q; cbn [remove];
    rewrite get_node; cbn [get]; try reflexivity; try congruence;
    apply IHp; congruence.
Qed.

Fixpoint filter_ne {A B} (g : A -> option B) (n : ne A) : t B :=
  match n with
  | N001 r => node Empty None (filter_ne g r)
  | N010 v => node Empty (g v) Empty
  | N011 v r => node Empty (g v) (filter_ne g r)
  | N100 l => node (filter_ne g l) None Empty
  | N101 l r => node (filter_ne g l) None (filter_ne g r)
  | N110 l v => node (filter_ne g l) (g v) Empty
  | N111 l v r => node (filter_ne g l) (g v) (filter_ne g r)
  end.

Definition filter_map {A B} (g : A -> option B) (tr : t A) : t B :=
  match tr with
  | Empty => Empty
  | Nodes n => filter_ne g n
  end.

Lemma filter_node {A B} (g : A -> option B) (l r : t A) o :
  filter_map g (node l o r) =
  node (filter_map g l)
    (match o with
    | Some a => g a
    | None => None
    end) (filter_map g r).
Proof.
  destruct l, o, r; reflexivity.
Qed.

Lemma get_filter {A B} (g : A -> option B) (tr : t A) p :
  get p (filter_map g tr) =
  match get p tr with
  | Some a => g a
  | None => None
  end.
Proof.
  revert p. induction tr as [|l o r IHl IHr] using node_ind; intro p.
  - rewrite get_empty. apply get_empty.
  - rewrite filter_node, !get_node. destruct p; cbn; auto.
Qed.

(** Mapping changes values without changing the bound keys. *)
Definition map {A B} (f : A -> B) (tr : t A) : t B :=
  filter_map (fun a => Some (f a)) tr.

(** Mapping acts independently at every position. *)
Theorem get_map {A B} (tr : t A) p (g : A -> B) :
  get p (map g tr) = option_map g (get p tr).
Proof.
  unfold map. rewrite get_filter. destruct (get p tr); reflexivity.
Qed.

(* One-sided branches are delegated without inspecting their descendants. *)
Fixpoint merge_ne {A B C} (f : option A -> option B -> option C)
    (only_l : t A -> t C) (only_r : t B -> t C) (n : ne A) (tr : t B) : t C :=
  match tr with
  | Empty => only_l (Nodes n)
  | Nodes _ =>
    match n with
    | N001 r =>
      node (only_r (left tr)) (f None (value tr)) (merge_ne f only_l only_r r (right tr))
    | N010 v =>
      node (only_r (left tr)) (f (Some v) (value tr)) (only_r (right tr))
    | N011 v r =>
      node (only_r (left tr)) (f (Some v) (value tr)) (merge_ne f only_l only_r r (right tr))
    | N100 l =>
      node (merge_ne f only_l only_r l (left tr)) (f None (value tr)) (only_r (right tr))
    | N101 l r =>
      node (merge_ne f only_l only_r l (left tr)) (f None (value tr))
        (merge_ne f only_l only_r r (right tr))
    | N110 l v =>
      node (merge_ne f only_l only_r l (left tr)) (f (Some v) (value tr)) (only_r (right tr))
    | N111 l v r =>
      node (merge_ne f only_l only_r l (left tr)) (f (Some v) (value tr))
        (merge_ne f only_l only_r r (right tr))
    end
  end.

Definition merge {A B C} (f : option A -> option B -> option C)
    (only_l : t A -> t C) (only_r : t B -> t C) (t1 : t A) (t2 : t B) : t C :=
  match t1 with
  | Empty => only_r t2
  | Nodes n => merge_ne f only_l only_r n t2
  end.

Lemma get_merge {A B C} (f : option A -> option B -> option C) only_l only_r :
  (forall p tr, get p (only_l tr) = f (get p tr) None) ->
  (forall p tr, get p (only_r tr) = f None (get p tr)) ->
  forall p t1 t2, get p (merge f only_l only_r t1 t2) = f (get p t1) (get p t2).
Proof.
  intros Hl Hr p [|n] t2.
  - cbn [merge]. rewrite get_empty. apply Hr.
  - revert p t2.
    induction n as [r IHr|v|v r IHr|l IHl|l IHl r IHr|l IHl v|l IHl v r IHr];
      intros p [|other_tree].
    all: try (cbn [merge merge_ne]; rewrite get_empty; apply Hl).
    all: try (cbn [merge] in IHl); try (cbn [merge] in IHr).
    all: destruct p; cbn [merge merge_ne]; rewrite get_node;
      cbn [get left right value]; rewrite ?IHl, ?IHr, ?Hr, ?get_empty;
      reflexivity.
Qed.

(** Combining rebuilds the paths present in either operand. *)
Definition combine {A B C} (f : option A -> option B -> option C)
    (t1 : t A) (t2 : t B) : t C :=
  merge f (filter_map (fun a => f (Some a) None))
    (filter_map (fun b => f None (Some b))) t1 t2.

(** A combine whose absent/absent result is absent acts pointwise. *)
Theorem get_combine {A B C} (tr : t A) (u : t B) p
    (f : option A -> option B -> option C) :
  f None None = None -> get p (combine f tr u) = f (get p tr) (get p u).
Proof.
  intro Hnone. unfold combine. apply get_merge; intros q t'; rewrite get_filter;
    destruct (get q t'); congruence.
Qed.

(** Union retains a one-sided binding and combines overlapping values. *)
Definition union_opt {A} (f : A -> A -> A) (a b : option A) : option A :=
  match a, b with
  | Some x, Some y => Some (f x y)
  | Some x, None => Some x
  | None, Some y => Some y
  | None, None => None
  end.

(** Union shares each subtree present in only one operand. *)
Definition union_with {A} (f : A -> A -> A) (t1 t2 : t A) : t A :=
  merge (union_opt f) (fun tr => tr) (fun tr => tr) t1 t2.

(** Union acts pointwise by the optional union operation. *)
Theorem get_union_with {A} (tr t1 : t A) p (f : A -> A -> A) :
  get p (union_with f tr t1) = union_opt f (get p tr) (get p t1).
Proof.
  unfold union_with. apply get_merge; intros q t'; destruct (get q t'); reflexivity.
Qed.

(** The sharing union has the same result as general combine. *)
Theorem union_with_combine {A} (tr t1 : t A) (f : A -> A -> A) :
  union_with f tr t1 = combine (union_opt f) tr t1.
Proof.
  apply extensionality. intro p. rewrite get_union_with, get_combine; reflexivity.
Qed.

Definition test_value {A B} (r : A -> option B -> bool) (a : option A) (b : option B) : bool :=
  match a with
  | Some v => r v b
  | None => true
  end.

Fixpoint forall2_ne {A B} (rel : A -> option B -> bool) (n : ne A) (tr : t B) : bool :=
  match n with
  | N001 r => forall2_ne rel r (right tr)
  | N010 v => rel v (value tr)
  | N011 v r => if rel v (value tr) then forall2_ne rel r (right tr) else false
  | N100 l => forall2_ne rel l (left tr)
  | N101 l r =>
    if forall2_ne rel l (left tr) then forall2_ne rel r (right tr) else false
  | N110 l v => if forall2_ne rel l (left tr) then rel v (value tr) else false
  | N111 l v r =>
    if forall2_ne rel l (left tr) then
      if rel v (value tr) then forall2_ne rel r (right tr) else false
    else false
  end.

(** The relational test follows only the first trie's paths and stops on failure. *)
Definition forall2 {A B} (r : A -> option B -> bool) (t1 : t A) (t2 : t B) : bool :=
  match t1 with
  | Empty => true
  | Nodes n => forall2_ne r n t2
  end.

Lemma forall2_node {A B} (rel : A -> option B -> bool) (l r : t A) o (u : t B) :
  forall2 rel (node l o r) u =
  forall2 rel l (left u) && (test_value rel o (value u) && forall2 rel r (right u)).
Proof.
  destruct l, o, r; cbn [node forall2 forall2_ne test_value];
    rewrite ?andb_true_r; reflexivity.
Qed.

(** The relational checker accepts exactly when all bindings of its first trie pass. *)
Theorem forall2_spec {A B} (tr : t A) (u : t B) :
  forall r : A -> option B -> bool,
  forall2 r tr u = true <-> forall p a, get p tr = Some a -> r a (get p u) = true.
Proof.
  revert u. induction tr as [|l o r IHl IHr] using node_ind; intros u rel.
  - cbn [forall2]. split; intros Htest.
    + intros p a Hget. rewrite get_empty in Hget. discriminate Hget.
    + reflexivity.
  - rewrite forall2_node, !andb_true_iff, IHl, IHr.
    split.
    + intros [Hl [Ho Hr]] p a Hget. rewrite get_node in Hget.
      destruct p; cbn [get]; [exact (Hr p a Hget)|exact (Hl p a Hget)|].
      subst o. exact Ho.
    + intro Htest. split.
      * intros p a Hget. apply (Htest (xO p) a). rewrite get_node. exact Hget.
      * split.
        -- destruct o as [a|]; [apply (Htest xH a); apply get_node|reflexivity].
        -- intros p a Hget. apply (Htest (xI p) a). rewrite get_node. exact Hget.
Qed.

(** Equality testing compares values at matching positions and rejects different supports. *)
Definition beq {A} (eqb : A -> A -> bool) (t1 t2 : t A) : bool :=
  if forall2 (fun a ob =>
    match ob with
    | Some b => eqb a b
    | None => false
    end) t1 t2 then
    forall2 (fun _ oa =>
      match oa with
      | Some _ => true
      | None => false
      end) t2 t1
  else false.

(** The comparison is pointwise even when the supplied value test is not equality. *)
Theorem beq_pointwise {A} (t1 t2 : t A) : forall eqb : A -> A -> bool,
  beq eqb t1 t2 = true <-> forall p, match get p t1, get p t2 with
    | None, None => True
    | Some a, Some b => eqb a b = true
    | _, _ => False
    end.
Proof.
  intro eqb. unfold beq.
  change ((forall2 (fun a ob =>
    match ob with
    | Some b => eqb a b
    | None => false
    end) t1 t2 &&
    forall2 (fun _ oa =>
      match oa with
      | Some _ => true
      | None => false
      end) t2 t1) = true <->
    forall p, match get p t1, get p t2 with
    | None, None => True
    | Some a, Some b => eqb a b = true
    | _, _ => False
    end).
  rewrite andb_true_iff, !forall2_spec. split.
  - intros [Hforward Hback] p.
    destruct (get p t1) as [a|] eqn:Hfirst; destruct (get p t2) as [b|] eqn:Hsecond.
    + specialize (Hforward p a Hfirst). rewrite Hsecond in Hforward. exact Hforward.
    + specialize (Hforward p a Hfirst). rewrite Hsecond in Hforward. discriminate Hforward.
    + specialize (Hback p b Hsecond). rewrite Hfirst in Hback. discriminate Hback.
    + exact I.
  - intro Hpoint. split; intros p a Hget; specialize (Hpoint p); rewrite Hget in Hpoint.
    + destruct (get p t2); [exact Hpoint|contradiction].
    + destruct (get p t1); [reflexivity|contradiction].
Qed.

(** A value test deciding equality makes the trie test decide canonical equality. *)
Theorem beq_correct {A} (t1 t2 : t A) : forall eqb : A -> A -> bool,
  (forall a b, eqb a b = true <-> a = b) -> (beq eqb t1 t2 = true <-> t1 = t2).
Proof.
  intros eqb Heqb. rewrite beq_pointwise. split.
  - intro Hpoint. apply extensionality. intro p. specialize (Hpoint p).
    destruct (get p t1) as [a|], (get p t2) as [b|]; try contradiction; [|reflexivity].
    apply Heqb in Hpoint. subst b. reflexivity.
  - intro Hequal. subst t2. intro p. destruct (get p t1) as [a|]; [apply Heqb|]; reflexivity.
Qed.

Definition lift {A} (k : positive -> positive) (pv : positive * A) : positive * A :=
  (k (fst pv), snd pv).

Definition root_entries {A} (o : option A) : list (positive * A) :=
  match o with
  | Some v => [(xH, v)]
  | None => []
  end.

(* This append-based list is a proof specification, never an executable traversal. *)
Fixpoint entries_ne {A} (n : ne A) : list (positive * A) :=
  match n with
  | N001 r => List.map (lift xI) (entries_ne r)
  | N010 v => [(xH, v)]
  | N011 v r => (xH, v) :: List.map (lift xI) (entries_ne r)
  | N100 l => List.map (lift xO) (entries_ne l)
  | N101 l r => List.map (lift xO) (entries_ne l) ++ List.map (lift xI) (entries_ne r)
  | N110 l v => List.map (lift xO) (entries_ne l) ++ [(xH, v)]
  | N111 l v r => List.map (lift xO) (entries_ne l) ++
    (xH, v) :: List.map (lift xI) (entries_ne r)
  end.

Definition entries {A} (tr : t A) : list (positive * A) :=
  match tr with
  | Empty => []
  | Nodes n => entries_ne n
  end.

Lemma entries_node {A} (l r : t A) o :
  entries (node l o r) = List.map (lift xO) (entries l) ++
    root_entries o ++ List.map (lift xI) (entries r).
Proof.
  destruct l, o, r; cbn [node entries entries_ne root_entries];
    rewrite ?app_nil_r; reflexivity.
Qed.

(* Each edge extends the path in constant work; emitting a key applies its accumulated
   path once. Starting with the identity path, traversal costs O(N + L), plus callback
   work, for N visited nodes and L emitted key bits. *)
Fixpoint fold_ne {A B} (f : B -> positive -> A -> B) (path : positive -> positive)
    (n : ne A) (b : B) : B :=
  match n with
  | N001 r => fold_ne f (fun p => path (xI p)) r b
  | N010 v => f b (path xH) v
  | N011 v r => fold_ne f (fun p => path (xI p)) r (f b (path xH) v)
  | N100 l => fold_ne f (fun p => path (xO p)) l b
  | N101 l r =>
    fold_ne f (fun p => path (xI p)) r (fold_ne f (fun p => path (xO p)) l b)
  | N110 l v => f (fold_ne f (fun p => path (xO p)) l b) (path xH) v
  | N111 l v r =>
    fold_ne f (fun p => path (xI p)) r
      (f (fold_ne f (fun p => path (xO p)) l b) (path xH) v)
  end.

Definition fold_path {A B} (f : B -> positive -> A -> B) (path : positive -> positive)
    (tr : t A) (b : B) : B :=
  match tr with
  | Empty => b
  | Nodes n => fold_ne f path n b
  end.

(** Folding visits the left subtree, root binding and right subtree in order. *)
Definition fold {A B} (f : B -> positive -> A -> B) (tr : t A) (b : B) : B :=
  fold_path f (fun p => p) tr b.

Lemma fold_left_map_values {X Y B} (f : B -> Y -> B) (g : X -> Y) xs b :
  List.fold_left f (List.map g xs) b = List.fold_left (fun acc x => f acc (g x)) xs b.
Proof.
  revert b. induction xs as [|x xs IH]; intro b; cbn [List.map fold_left]; auto.
Qed.

Lemma fold_path_entries {A B} (f : B -> positive -> A -> B) (tr : t A) :
  forall path b, fold_path f path tr b =
    List.fold_left (fun acc pv => f acc (path (fst pv)) (snd pv)) (entries tr) b.
Proof.
  destruct tr as [|n]; [reflexivity|].
  induction n as [r IHr|v|v r IHr|l IHl|l IHl r IHr|l IHl v|l IHl v r IHr];
    intros path b.
  all: try (cbn [fold_path entries] in IHl); try (cbn [fold_path entries] in IHr).
  all: cbn [fold_path fold_ne entries entries_ne];
    rewrite ?fold_left_app; cbn [fold_left];
    rewrite ?fold_left_map_values; cbn [lift fst snd];
    rewrite ?IHl, ?IHr; reflexivity.
Qed.

(** Elements are collected with an accumulator and reversed once. *)
Definition elements {A} (tr : t A) : list (positive * A) :=
  List.rev_append (fold (fun acc p v => (p, v) :: acc) tr []) [].

Lemma fold_left_pairs {A} (xs acc : list (positive * A)) :
  List.fold_left (fun acc pv => (fst pv, snd pv) :: acc) xs acc = List.rev xs ++ acc.
Proof.
  revert acc. induction xs as [|[p a] xs IH]; intro acc.
  - reflexivity.
  - cbn [fold_left rev fst snd]. rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma elements_entries {A} (tr : t A) : elements tr = entries tr.
Proof.
  unfold elements, fold. rewrite rev_append_rev, app_nil_r, fold_path_entries.
  rewrite fold_left_pairs, app_nil_r, rev_involutive. reflexivity.
Qed.

Lemma elements_node {A} (l r : t A) o :
  elements (node l o r) = List.map (lift xO) (elements l) ++
    root_entries o ++ List.map (lift xI) (elements r).
Proof.
  rewrite !elements_entries. apply entries_node.
Qed.

(** Every listed binding is returned by lookup. *)
Theorem elements_sound {A} (tr : t A) p v : In (p, v) (elements tr) -> get p tr = Some v.
Proof.
  revert p v. induction tr as [|l o r IHl IHr] using node_ind; intros p v Hin.
  - cbn [elements fold fold_path rev] in Hin. contradiction.
  - rewrite elements_node, !in_app_iff in Hin. destruct Hin as [Hl|[Ho|Hr]].
    + apply in_map_iff in Hl. destruct Hl as [[q a] [Heq Hin]].
      cbn [lift fst snd] in Heq. inversion Heq; subst p a.
      rewrite get_node. apply IHl. exact Hin.
    + destruct o as [a|]; cbn [root_entries] in Ho; [|contradiction].
      destruct Ho as [Heq|Hfalse]; [|contradiction]. inversion Heq; subst p a.
      apply get_node.
    + apply in_map_iff in Hr. destruct Hr as [[q a] [Heq Hin]].
      cbn [lift fst snd] in Heq. inversion Heq; subst p a.
      rewrite get_node. apply IHr. exact Hin.
Qed.

(** Every binding returned by lookup occurs in the elements. *)
Theorem elements_complete {A} (tr : t A) p v : get p tr = Some v -> In (p, v) (elements tr).
Proof.
  revert p v. induction tr as [|l o r IHl IHr] using node_ind; intros p v Hget.
  - rewrite get_empty in Hget. discriminate Hget.
  - rewrite elements_node, !in_app_iff. rewrite get_node in Hget. destruct p.
    + right. right. apply in_map_iff. exists (p, v). split; [reflexivity|].
      apply IHr. exact Hget.
    + left. apply in_map_iff. exists (p, v). split; [reflexivity|].
      apply IHl. exact Hget.
    + right. left. subst o. cbn [root_entries]. left. reflexivity.
Qed.

(** The trie traversal agrees with a left fold over its element list. *)
Theorem fold_elements {A B} (tr : t A) : forall (g : B -> positive -> A -> B) b,
  fold g tr b = List.fold_left (fun acc pv => g acc (fst pv) (snd pv)) (elements tr) b.
Proof.
  intros g b. unfold fold. rewrite elements_entries.
  exact (fold_path_entries g tr (fun p => p) b).
Qed.

Fixpoint count_ne {A} (n : ne A) (acc : nat) : nat :=
  match n with
  | N001 r => count_ne r acc
  | N010 _ => S acc
  | N011 _ r => count_ne r (S acc)
  | N100 l => count_ne l acc
  | N101 l r => count_ne r (count_ne l acc)
  | N110 l _ => S (count_ne l acc)
  | N111 l _ r => count_ne r (S (count_ne l acc))
  end.

(** Size counts bindings with an accumulator, without constructing keys. *)
Definition size {A} (tr : t A) : nat :=
  match tr with
  | Empty => 0
  | Nodes n => count_ne n 0
  end.

Lemma count_ne_entries {A} (n : ne A) :
  forall acc, count_ne n acc = List.length (entries_ne n) + acc.
Proof.
  induction n as [r IHr|v|v r IHr|l IHl|l IHl r IHr|l IHl v|l IHl v r IHr];
    intro acc; cbn [count_ne entries_ne]; rewrite ?IHl, ?IHr, ?length_app, ?length_map;
    cbn [length]; rewrite ?length_map, ?Nat.add_succ_r, ?Nat.add_0_r, ?Nat.add_assoc;
    try reflexivity.
  - rewrite (Nat.add_comm (length (entries_ne r)) (length (entries_ne l))). reflexivity.
  - rewrite (Nat.add_comm (length (entries_ne r)) (length (entries_ne l))). reflexivity.
Qed.

(** Size equals the number of listed bindings. *)
Theorem size_elements {A} (tr : t A) : size tr = List.length (elements tr).
Proof.
  rewrite elements_entries. destruct tr as [|n]; [reflexivity|].
  unfold size, entries. rewrite count_ne_entries, Nat.add_0_r. reflexivity.
Qed.

(** The traversal order places every left key before the root and every right key after it. *)
Fixpoint key_lt (p q : positive) {struct p} : Prop :=
  match p, q with
  | xO p', xO q' => key_lt p' q'
  | xI p', xI q' => key_lt p' q'
  | xO _, xH | xO _, xI _ | xH, xI _ => True
  | _, _ => False
  end.

Lemma key_lt_irrefl p : ~ key_lt p p.
Proof.
  induction p; cbn [key_lt]; assumption || tauto.
Qed.

Lemma strongly_sorted_app {X} (R : X -> X -> Prop) xs ys :
  StronglySorted R xs -> StronglySorted R ys ->
  (forall x y, In x xs -> In y ys -> R x y) -> StronglySorted R (xs ++ ys).
Proof.
  intros Hxs Hys. induction Hxs as [|x xs Hsort IH Hforall]; intro Hcross.
  - exact Hys.
  - cbn [app]. constructor.
    + apply IH. intros a b Ha Hb. apply Hcross; [right; exact Ha|exact Hb].
    + apply Forall_app. split; [exact Hforall|]. apply Forall_forall.
      intros y Hy. apply Hcross; [left; reflexivity|exact Hy].
Qed.

Lemma strongly_sorted_map {X Y} (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (f : X -> Y) xs :
  (forall x y, R x y -> S (f x) (f y)) ->
  StronglySorted R xs -> StronglySorted S (List.map f xs).
Proof.
  intros Hmap Hsort. induction Hsort as [|x xs Hsort IH Hforall]; cbn [List.map].
  - constructor.
  - constructor; [exact IH|]. apply Forall_forall. intros y Hy.
    apply in_map_iff in Hy. destruct Hy as [z [Heq Hin]]. subst y.
    apply Hmap. rewrite Forall_forall in Hforall. apply Hforall. exact Hin.
Qed.

(** The elements are strongly sorted in the public trie order. *)
Theorem elements_sorted {A} (tr : t A) :
  StronglySorted (fun a b => key_lt (fst a) (fst b)) (elements tr).
Proof.
  induction tr as [|l o r IHl IHr] using node_ind.
  - cbn [elements fold fold_path rev]. constructor.
  - rewrite elements_node.
    assert (Hl : StronglySorted (fun a b => key_lt (fst a) (fst b))
      (List.map (lift xO) (elements l))).
    { eapply strongly_sorted_map; [|exact IHl]. intros [p a] [q b] Hlt. exact Hlt. }
    assert (Hr : StronglySorted (fun a b => key_lt (fst a) (fst b))
      (List.map (lift xI) (elements r))).
    { eapply strongly_sorted_map; [|exact IHr]. intros [p a] [q b] Hlt. exact Hlt. }
    apply strongly_sorted_app; [exact Hl| |].
    + destruct o as [v|]; cbn [root_entries app]; [|exact Hr].
      constructor; [exact Hr|]. apply Forall_forall. intros [q b] Hin.
      apply in_map_iff in Hin. destruct Hin as [[p a] [Heq Hin]].
      inversion Heq. exact I.
    + intros [p a] [q b] Hinl Hinr. apply in_map_iff in Hinl.
      destruct Hinl as [[k c] [Heq Hin]]. inversion Heq; subst p a.
      apply in_app_iff in Hinr. destruct Hinr as [Hroot|Hright].
      * destruct o as [v|]; cbn [root_entries] in Hroot; [|contradiction].
        destruct Hroot as [Heqroot|Hfalse]; [|contradiction]. inversion Heqroot. exact I.
      * apply in_map_iff in Hright. destruct Hright as [[j d] [Heqright Hinright]].
        inversion Heqright. exact I.
Qed.

Lemma sorted_keys_nodup {A} (xs : list (positive * A)) :
  StronglySorted (fun a b => key_lt (fst a) (fst b)) xs -> NoDup (List.map fst xs).
Proof.
  intro Hsort. induction Hsort as [|[p a] xs Hsort IH Hforall]; cbn [List.map fst].
  - constructor.
  - constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin.
    destruct Hin as [[q b] [Heq Hin]]. cbn [fst] in Heq. subst q.
    rewrite Forall_forall in Hforall. specialize (Hforall (p, b) Hin).
    exact (key_lt_irrefl p Hforall).
Qed.

(** Every key is listed at most once. *)
Theorem elements_nodup {A} (tr : t A) : NoDup (List.map fst (elements tr)).
Proof.
  apply sorted_keys_nodup. apply elements_sorted.
Qed.

End Trie.

Import Trie.
