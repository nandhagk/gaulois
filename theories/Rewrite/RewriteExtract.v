(** * Exact extraction of finite represented trees

    Synchronous dynamic programming retains a cheapest finite tree at every canonical class.
    For example, a zero-cost self-cycle loses to its finite leaf by the size tie breaker.
    Builds on: CollectionsMap, RewriteSyntax, RewriteEquality and RewriteEgraph. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph.
Import List.ListNotations.

(** * Tree measures and deterministic candidates *)

(** Cost counts each occurrence, including repeated copies of a represented subtree. *)
Fixpoint rw_tree_cost {K Sort V} (var_cost : V -> nat) (op_cost : K -> nat)
    (t : rw_term K Sort V) : nat :=
  match t with
  | RWVar _ v => var_cost v
  | RWApp _ op ts => op_cost op + fold_right (fun t n => rw_tree_cost var_cost op_cost t + n) 0 ts
  end.

(** Size counts constructors, so deleting even a zero-cost cycle strictly reduces size. *)
Fixpoint rw_tree_size {K Sort V} (t : rw_term K Sort V) : nat :=
  match t with
  | RWVar _ _ => 1
  | RWApp _ _ ts => S (fold_right (fun t n => rw_tree_size t + n) 0 ts)
  end.

(** Height counts constructors on the longest path and gives a finite witness index. *)
Fixpoint rw_tree_height {K Sort V} (t : rw_term K Sort V) : nat :=
  match t with
  | RWVar _ _ => 1
  | RWApp _ _ ts => S (fold_right (fun t n => Nat.max (rw_tree_height t) n) 0 ts)
  end.

(** Four tokens per constructor encode its tag, sort, payload and arity in preorder. *)
Fixpoint rw_tree_code {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (t : rw_term K Sort V) : list positive :=
  match t with
  | RWVar s v => [1%positive; encode ES s; encode EV v; 1%positive]
  | RWApp s op ts => 2%positive :: encode ES s :: encode EK op ::
      encode nat_encoding (length ts) :: flat_map (rw_tree_code EK ES EV) ts
  end.

(** Structural ties use the lexicographic order of encoded preorder tokens. *)
Fixpoint rw_codes_leb (xs ys : list positive) : bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    match Pos.compare x y with
    | Eq => rw_codes_leb xs ys
    | Lt => true
    | Gt => false
    end
  end.

Lemma rw_codes_leb_refl xs : rw_codes_leb xs xs = true.
Proof.
  induction xs as [|x xs IH]; cbn; [reflexivity|now rewrite Pos.compare_refl].
Qed.

Lemma rw_codes_leb_total xs ys : rw_codes_leb xs ys = false -> rw_codes_leb ys xs = true.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; cbn; try discriminate;
    [reflexivity|].
  destruct (Pos.compare x y) eqn:Hxy.
  - apply Pos.compare_eq_iff in Hxy; subst y; rewrite Pos.compare_refl; apply IH.
  - discriminate.
  - apply Pos.compare_gt_iff in Hxy.
    assert (Hyx : Pos.compare y x = Lt) by (apply Pos.compare_lt_iff; exact Hxy).
    rewrite Hyx; reflexivity.
Qed.

Lemma rw_tree_code_size {K Sort V} EK ES EV (t : rw_term K Sort V) :
  length (rw_tree_code EK ES EV t) = 4 * rw_tree_size t.
Proof.
  revert t; fix IH 1; intros [s v|s op ts]; cbn; [reflexivity|].
  assert (Hargs : length (flat_map (rw_tree_code EK ES EV) ts) =
      4 * fold_right (fun t n => rw_tree_size t + n) 0 ts).
  { induction ts as [|t ts IHts]; cbn; [reflexivity|].
    rewrite length_app, IH, IHts; lia. }
  lia.
Qed.

Lemma rw_tree_codes_prefix {K Sort V} EK ES EV (ts : list (rw_term K Sort V)) :
  Forall (fun t => forall u xs ys,
    rw_tree_code EK ES EV t ++ xs = rw_tree_code EK ES EV u ++ ys -> t = u /\ xs = ys) ts ->
  forall us xs ys, length ts = length us ->
    flat_map (rw_tree_code EK ES EV) ts ++ xs = flat_map (rw_tree_code EK ES EV) us ++ ys ->
    ts = us /\ xs = ys.
Proof.
  intro Hprefix; induction Hprefix as [|t ts Ht Hrest IH]; intros [|u us] xs ys Hlength Hcode;
    cbn in Hlength; try discriminate.
  - cbn in Hcode; auto.
  - cbn in Hcode; rewrite <- !app_assoc in Hcode.
    destruct (Ht u _ _ Hcode) as [-> Htails].
    destruct (IH us xs ys ltac:(lia) Htails) as [-> ->]; auto.
Qed.

(** The preorder encoding is prefix-free and distinguishes every sort, payload and child. *)
Lemma rw_tree_code_prefix {K Sort V} EK ES EV (t : rw_term K Sort V) :
  forall u xs ys, rw_tree_code EK ES EV t ++ xs = rw_tree_code EK ES EV u ++ ys ->
    t = u /\ xs = ys.
Proof.
  revert t; fix IH 1; intros [s v|s op ts] [s' v'|s' op' us] xs ys Hcode;
    cbn in Hcode; try discriminate.
  - injection Hcode as Hsort Hvar Htail.
    apply (encode_injective ES) in Hsort; apply (encode_injective EV) in Hvar;
      subst; split; reflexivity.
  - injection Hcode as Hsort Hop Hlength Htail.
    apply (encode_injective ES) in Hsort; apply (encode_injective EK) in Hop.
    apply (encode_injective nat_encoding) in Hlength; subst s' op'.
    assert (Hprefix : Forall (fun t => forall u xs ys,
        rw_tree_code EK ES EV t ++ xs = rw_tree_code EK ES EV u ++ ys -> t = u /\ xs = ys) ts).
    { clear Hlength Htail; induction ts as [|t ts IHts].
      - constructor.
      - constructor; [apply IH|exact IHts]. }
    destruct (rw_tree_codes_prefix EK ES EV ts Hprefix us xs ys Hlength Htail) as [-> ->];
      split; reflexivity.
Qed.

Lemma rw_tree_code_injective {K Sort V} EK ES EV (t u : rw_term K Sort V) :
  rw_tree_code EK ES EV t = rw_tree_code EK ES EV u -> t = u.
Proof.
  intro Hcode.
  assert (Happend : rw_tree_code EK ES EV t ++ [] = rw_tree_code EK ES EV u ++ [])
    by now rewrite !app_nil_r.
  exact (proj1 (rw_tree_code_prefix EK ES EV t u [] [] Happend)).
Qed.

(** Cached measures avoid traversing the materialized tree to compare candidates. *)
Record rw_tree_candidate (K Sort V : Type) : Type := RwTreeCandidate {
  rw_candidate_tree : rw_term K Sort V;
  rw_candidate_cost : nat;
  rw_candidate_size : nat;
  rw_candidate_code : list positive
}.

Arguments RwTreeCandidate {K Sort V}.
Arguments rw_candidate_tree {K Sort V}.
Arguments rw_candidate_cost {K Sort V}.
Arguments rw_candidate_size {K Sort V}.
Arguments rw_candidate_code {K Sort V}.

Definition rw_candidate_ok {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (vc : V -> nat) (oc : K -> nat) (a : rw_tree_candidate K Sort V) : Prop :=
  rw_candidate_cost a = rw_tree_cost vc oc (rw_candidate_tree a) /\
  rw_candidate_size a = rw_tree_size (rw_candidate_tree a) /\
  rw_candidate_code a = rw_tree_code EK ES EV (rw_candidate_tree a).

(** The primary and secondary order is lexicographic in cost and materialized size. *)
Definition rw_tree_better {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (t u : rw_term K Sort V) : Prop :=
  rw_tree_cost vc oc t <= rw_tree_cost vc oc u /\
  (rw_tree_cost vc oc u <= rw_tree_cost vc oc t -> rw_tree_size t <= rw_tree_size u).

Lemma rw_tree_better_refl {K Sort V} vc oc (t : rw_term K Sort V) :
  rw_tree_better vc oc t t.
Proof.
  split; lia.
Qed.

Lemma rw_tree_better_trans {K Sort V} vc oc (t u v : rw_term K Sort V) :
  rw_tree_better vc oc t u -> rw_tree_better vc oc u v -> rw_tree_better vc oc t v.
Proof.
  unfold rw_tree_better; intros [Htu Hsu] [Huv Hsv]; split; [lia|intro Hvt].
  specialize (Hsu ltac:(lia)); specialize (Hsv ltac:(lia)); lia.
Qed.

(** Equal costs prefer smaller trees, and equal sizes prefer smaller structural codes. *)
Definition rw_choose_tree {K Sort V} (a b : rw_tree_candidate K Sort V) :
    rw_tree_candidate K Sort V :=
  match Nat.compare (rw_candidate_cost a) (rw_candidate_cost b) with
  | Lt => a
  | Gt => b
  | Eq =>
    match Nat.compare (rw_candidate_size a) (rw_candidate_size b) with
    | Lt => a
    | Gt => b
    | Eq => if rw_codes_leb (rw_candidate_code a) (rw_candidate_code b) then a else b
    end
  end.

Lemma rw_choose_tree_member {K Sort V} (a b : rw_tree_candidate K Sort V) :
  rw_choose_tree a b = a \/ rw_choose_tree a b = b.
Proof.
  unfold rw_choose_tree; destruct (Nat.compare _ _); try auto.
  destruct (Nat.compare _ _); try auto; destruct (rw_codes_leb _ _); auto.
Qed.

Lemma rw_choose_tree_rank {K Sort V} (a b : rw_tree_candidate K Sort V) :
  (rw_candidate_cost (rw_choose_tree a b) <= rw_candidate_cost a /\
    (rw_candidate_cost a <= rw_candidate_cost (rw_choose_tree a b) ->
      rw_candidate_size (rw_choose_tree a b) <= rw_candidate_size a)) /\
  (rw_candidate_cost (rw_choose_tree a b) <= rw_candidate_cost b /\
    (rw_candidate_cost b <= rw_candidate_cost (rw_choose_tree a b) ->
      rw_candidate_size (rw_choose_tree a b) <= rw_candidate_size b)).
Proof.
  unfold rw_choose_tree; destruct (Nat.compare (rw_candidate_cost a) (rw_candidate_cost b))
    eqn:Hcost.
  - apply Nat.compare_eq_iff in Hcost.
    destruct (Nat.compare (rw_candidate_size a) (rw_candidate_size b)) eqn:Hsize.
    + apply Nat.compare_eq_iff in Hsize; destruct (rw_codes_leb _ _); cbn; lia.
    + apply Nat.compare_lt_iff in Hsize; cbn; lia.
    + apply Nat.compare_gt_iff in Hsize; cbn; lia.
  - apply Nat.compare_lt_iff in Hcost; cbn; lia.
  - apply Nat.compare_gt_iff in Hcost; cbn; lia.
Qed.

(** Final structural ties are decided by encoded trees rather than production identifiers. *)
Lemma rw_choose_tree_code {K Sort V} (a b : rw_tree_candidate K Sort V) :
  rw_candidate_cost a = rw_candidate_cost b -> rw_candidate_size a = rw_candidate_size b ->
  rw_codes_leb (rw_candidate_code (rw_choose_tree a b)) (rw_candidate_code a) = true /\
  rw_codes_leb (rw_candidate_code (rw_choose_tree a b)) (rw_candidate_code b) = true.
Proof.
  intros Hcost Hsize; unfold rw_choose_tree; rewrite Hcost, Nat.compare_refl, Hsize,
    Nat.compare_refl; destruct (rw_codes_leb (rw_candidate_code a) (rw_candidate_code b))
      eqn:Hcode; cbn.
  - split; [apply rw_codes_leb_refl|exact Hcode].
  - split; [apply rw_codes_leb_total; exact Hcode|apply rw_codes_leb_refl].
Qed.

Lemma rw_choose_tree_better {K Sort V} EK ES EV vc oc (a b : rw_tree_candidate K Sort V) :
  rw_candidate_ok EK ES EV vc oc a -> rw_candidate_ok EK ES EV vc oc b ->
  rw_tree_better vc oc (rw_candidate_tree (rw_choose_tree a b)) (rw_candidate_tree a) /\
  rw_tree_better vc oc (rw_candidate_tree (rw_choose_tree a b)) (rw_candidate_tree b).
Proof.
  intros Ha Hb; pose proof (rw_choose_tree_rank a b) as Hrank.
  assert (Hchosen : rw_candidate_ok EK ES EV vc oc (rw_choose_tree a b)).
  { destruct (rw_choose_tree_member a b) as [Ha'|Hb']; rewrite ?Ha', ?Hb'; assumption. }
  destruct Ha as [Hca [Hsa Hka]], Hb as [Hcb [Hsb Hkb]],
    Hchosen as [Hcc [Hsc Hkc]].
  unfold rw_tree_better; now rewrite Hca, Hcb, Hcc, Hsa, Hsb, Hsc in Hrank.
Qed.

Lemma rw_height_positive {K Sort V} (t : rw_term K Sort V) : 0 < rw_tree_height t.
Proof.
  destruct t; cbn; lia.
Qed.

Lemma rw_height_args {K Sort V} (ts : list (rw_term K Sort V)) h :
  fold_right (fun t n => Nat.max (rw_tree_height t) n) 0 ts <= h <->
  Forall (fun t => rw_tree_height t <= h) ts.
Proof.
  induction ts as [|t ts IH]; cbn; [split; [constructor|lia]|].
  rewrite Nat.max_lub_iff, IH; split; intros H; [now constructor|].
  inversion H; auto.
Qed.

Lemma rw_measure_child {K Sort V} vc oc (ts : list (rw_term K Sort V)) t :
  In t ts -> rw_tree_cost vc oc t <=
    fold_right (fun u n => rw_tree_cost vc oc u + n) 0 ts /\
    rw_tree_size t <= fold_right (fun u n => rw_tree_size u + n) 0 ts.
Proof.
  induction ts as [|u ts IH]; cbn; [contradiction|].
  intros [<-|Hin]; [lia|destruct (IH Hin); lia].
Qed.

(** * Indexed synchronous rounds *)

Definition rw_tree_table (K Sort V : Type) := Map.t rw_id (rw_tree_candidate K Sort V).

(** Alias resolution and candidate lookup are both trie queries, never list searches. *)
Definition rw_tree_get {K Sort V} (g : rw_graph K Sort V) (m : rw_tree_table K Sort V)
    (c : rw_id) : option (rw_tree_candidate K Sort V) :=
  match rw_find g c with
  | Some root => Map.get positive_encoding root m
  | None => None
  end.

Fixpoint rw_tree_children {K Sort V} (g : rw_graph K Sort V) (m : rw_tree_table K Sort V)
    (ids : list rw_id) : option (list (rw_tree_candidate K Sort V)) :=
  match ids with
  | [] => Some []
  | id :: ids =>
    match rw_tree_get g m id, rw_tree_children g m ids with
    | Some a, Some args => Some (a :: args)
    | _, _ => None
    end
  end.

Definition rw_tree_leaf {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (vc : V -> nat) (s : Sort) (v : V) : rw_tree_candidate K Sort V :=
  RwTreeCandidate (RWVar s v) (vc v) 1 (rw_tree_code EK ES EV (RWVar s v)).

Definition rw_tree_app {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (oc : K -> nat) (s : Sort) (op : K) (args : list (rw_tree_candidate K Sort V)) :
    rw_tree_candidate K Sort V :=
  RwTreeCandidate (RWApp s op (map rw_candidate_tree args))
    (oc op + fold_right (fun a n => rw_candidate_cost a + n) 0 args)
    (S (fold_right (fun a n => rw_candidate_size a + n) 0 args))
    (2%positive :: encode ES s :: encode EK op :: encode nat_encoding (length args) ::
      flat_map rw_candidate_code args).

Definition rw_tree_node {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (vc : V -> nat) (oc : K -> nat) (g : rw_graph K Sort V) (m : rw_tree_table K Sort V)
    (node : rw_node K Sort V) : option (rw_tree_candidate K Sort V) :=
  match node with
  | RWNVar s v => Some (rw_tree_leaf EK ES EV vc s v)
  | RWNApp s op ids => option_map (rw_tree_app EK ES EV oc s op) (rw_tree_children g m ids)
  end.

Definition rw_tree_insert {K Sort V} (m : rw_tree_table K Sort V) root
    (a : rw_tree_candidate K Sort V) : rw_tree_table K Sort V :=
  Map.set positive_encoding root
    (match Map.get positive_encoding root m with
    | Some old => rw_choose_tree old a
    | None => a
    end) m.

Definition rw_tree_visit {K Sort V} EK ES EV vc oc (g : rw_graph K Sort V)
    (old acc : rw_tree_table K Sort V) (_ : rw_id) (owned : rw_id * rw_node K Sort V) :
    rw_tree_table K Sort V :=
  match rw_find g (fst owned), rw_tree_node EK ES EV vc oc g old (snd owned) with
  | Some root, Some a => rw_tree_insert acc root a
  | _, _ => acc
  end.

(** Each round folds the production trie once, always reading children from the previous round. *)
Definition rw_tree_step {K Sort V} EK ES EV vc oc (g : rw_graph K Sort V)
    (m : rw_tree_table K Sort V) : rw_tree_table K Sort V :=
  Map.fold (rw_tree_visit EK ES EV vc oc g m) (rw_nodes g) m.

(** Binary iteration counts height rounds; old candidates survive every round. *)
Definition rw_tree_rounds {K Sort V} EK ES EV vc oc (g : rw_graph K Sort V) (height : N) :
    rw_tree_table K Sort V :=
  N.iter height (rw_tree_step EK ES EV vc oc g) Map.empty.

(** Canonical-class count bounds the required rounds even for nonproductive cyclic graphs. *)
Definition rw_extract_tree {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (var_cost : V -> nat) (op_cost : K -> nat) (g : rw_graph K Sort V) (c : rw_id) :
    option (rw_term K Sort V) :=
  option_map rw_candidate_tree
    (rw_tree_get g (rw_tree_rounds EK ES EV var_cost op_cost g (N.of_nat (length (rw_roots g)))) c).

(** Each round charges production traversal and child trie lookups separately from cached natural
    arithmetic and structural-code bit work. Materialization counts every output occurrence and
    can take exponential space in the compact graph's size. *)

(** * Cache and round invariants *)

Definition rw_candidate_better {K Sort V} (a b : rw_tree_candidate K Sort V) : Prop :=
  rw_candidate_cost a <= rw_candidate_cost b /\
  (rw_candidate_cost b <= rw_candidate_cost a -> rw_candidate_size a <= rw_candidate_size b).

Lemma rw_candidate_better_refl {K Sort V} (a : rw_tree_candidate K Sort V) :
  rw_candidate_better a a.
Proof.
  split; lia.
Qed.

Lemma rw_candidate_better_trans {K Sort V} (a b c : rw_tree_candidate K Sort V) :
  rw_candidate_better a b -> rw_candidate_better b c -> rw_candidate_better a c.
Proof.
  unfold rw_candidate_better; intros [Hab Hsab] [Hbc Hsbc]; split; [lia|intro Hca].
  specialize (Hsab ltac:(lia)); specialize (Hsbc ltac:(lia)); lia.
Qed.

Definition rw_table_improves {K Sort V} (m m' : rw_tree_table K Sort V) : Prop :=
  forall root a, Map.get positive_encoding root m = Some a ->
    exists b, Map.get positive_encoding root m' = Some b /\ rw_candidate_better b a.

Lemma rw_table_improves_refl {K Sort V} (m : rw_tree_table K Sort V) :
  rw_table_improves m m.
Proof.
  intros root a Hget; exists a; split; [exact Hget|apply rw_candidate_better_refl].
Qed.

Lemma rw_table_improves_trans {K Sort V} (m m' m'' : rw_tree_table K Sort V) :
  rw_table_improves m m' -> rw_table_improves m' m'' -> rw_table_improves m m''.
Proof.
  intros Hleft Hright root a Hget.
  destruct (Hleft root a Hget) as [b [Hb Hba]].
  destruct (Hright root b Hb) as [c [Hc Hcb]].
  exists c; split; [exact Hc|eapply rw_candidate_better_trans; eassumption].
Qed.

Lemma rw_tree_insert_hit {K Sort V} (m : rw_tree_table K Sort V) root a :
  exists b, Map.get positive_encoding root (rw_tree_insert m root a) = Some b /\
    rw_candidate_better b a.
Proof.
  unfold rw_tree_insert; rewrite Map.get_set_same.
  destruct (Map.get positive_encoding root m) as [old|].
  - exists (rw_choose_tree old a); split; [reflexivity|exact (proj2 (rw_choose_tree_rank old a))].
  - exists a; split; [reflexivity|apply rw_candidate_better_refl].
Qed.

Lemma rw_tree_insert_improves {K Sort V} (m : rw_tree_table K Sort V) root a :
  rw_table_improves m (rw_tree_insert m root a).
Proof.
  intros r old Hget; unfold rw_tree_insert; destruct (Pos.eq_dec r root) as [->|Hne].
  - rewrite Map.get_set_same, Hget.
    exists (rw_choose_tree old a); split; [reflexivity|exact (proj1 (rw_choose_tree_rank old a))].
  - rewrite Map.get_set_other by exact Hne.
    exists old; split; [exact Hget|apply rw_candidate_better_refl].
Qed.

Lemma rw_tree_visit_improves {K Sort V} EK ES EV vc oc (g : rw_graph K Sort V)
    old acc n owned :
  rw_table_improves acc (rw_tree_visit EK ES EV vc oc g old acc n owned).
Proof.
  unfold rw_tree_visit; destruct (rw_find g (fst owned)),
    (rw_tree_node EK ES EV vc oc g old (snd owned));
    try apply rw_table_improves_refl; apply rw_tree_insert_improves.
Qed.

Lemma rw_tree_fold_improves {K Sort V} EK ES EV vc oc (g : rw_graph K Sort V) old xs acc :
  rw_table_improves acc (fold_left (fun m kv =>
    rw_tree_visit EK ES EV vc oc g old m (fst kv) (snd kv)) xs acc).
Proof.
  revert acc; induction xs as [|[n owned] xs IH]; intro acc; cbn.
  - apply rw_table_improves_refl.
  - eapply rw_table_improves_trans; [apply rw_tree_visit_improves|apply IH].
Qed.

Lemma rw_tree_fold_hit {K Sort V} EK ES EV vc oc (g : rw_graph K Sort V)
    old xs acc n owner node root a :
  In (n, (owner, node)) xs -> rw_find g owner = Some root ->
  rw_tree_node EK ES EV vc oc g old node = Some a ->
  exists b, Map.get positive_encoding root
    (fold_left (fun m kv => rw_tree_visit EK ES EV vc oc g old m (fst kv) (snd kv)) xs acc)
      = Some b /\ rw_candidate_better b a.
Proof.
  revert acc; induction xs as [|[n' [owner' node']] xs IH]; intros acc Hin Ho Ha;
    cbn in Hin; [contradiction|].
  destruct Hin as [Heq|Hin].
  - injection Heq as Heqn Heqo Heqnode; subst n' owner' node'.
    assert (Hvisit : rw_tree_visit EK ES EV vc oc g old acc n (owner, node) =
        rw_tree_insert acc root a).
    { unfold rw_tree_visit; change (match rw_find g owner,
        rw_tree_node EK ES EV vc oc g old node with
        | Some r, Some b => rw_tree_insert acc r b
        | _, _ => acc
        end = rw_tree_insert acc root a).
      now rewrite Ho, Ha. }
    change (exists b, Map.get positive_encoding root
      (fold_left (fun m kv => rw_tree_visit EK ES EV vc oc g old m (fst kv) (snd kv)) xs
        (rw_tree_visit EK ES EV vc oc g old acc n (owner, node))) = Some b /\
      rw_candidate_better b a).
    rewrite Hvisit.
    destruct (rw_tree_insert_hit acc root a) as [b [Hb Hba]].
    destruct (rw_tree_fold_improves EK ES EV vc oc g old xs _ root b Hb)
      as [d [Hd Hdb]].
    exists d; split; [exact Hd|eapply rw_candidate_better_trans; eassumption].
  - cbn [fold_left fst snd]; apply IH; assumption.
Qed.

Lemma rw_tree_children_spec {K Sort V} (g : rw_graph K Sort V) m ids args :
  rw_tree_children g m ids = Some args <->
  Forall2 (fun id a => rw_tree_get g m id = Some a) ids args.
Proof.
  revert args; induction ids as [|id ids IH]; intros args; cbn.
  - split; [intro Heq; injection Heq as <-; constructor|intro H; inversion H; reflexivity].
  - split; intro H.
    + destruct (rw_tree_get g m id) as [a|] eqn:Hget;
        destruct (rw_tree_children g m ids) as [rest|] eqn:Hrest; try discriminate.
      injection H as <-; constructor; [exact Hget|apply IH; reflexivity].
    + inversion H as [|id' a' ids' rest' Hhead Htail]; subst.
      apply IH in Htail; rewrite Hhead, Htail; reflexivity.
Qed.

Lemma rw_tree_app_ok {K Sort V} EK ES EV vc oc s op (args : list (rw_tree_candidate K Sort V)) :
  Forall (rw_candidate_ok EK ES EV vc oc) args ->
  rw_candidate_ok EK ES EV vc oc (rw_tree_app EK ES EV oc s op args).
Proof.
  intro Hargs; unfold rw_candidate_ok, rw_tree_app; cbn [rw_candidate_tree rw_candidate_cost
    rw_candidate_size rw_candidate_code rw_tree_cost rw_tree_size rw_tree_code].
  assert (Hcost : fold_right (fun a n => rw_candidate_cost a + n) 0 args =
      fold_right (fun t n => rw_tree_cost vc oc t + n) 0 (map rw_candidate_tree args)).
  { induction Hargs as [|a args [Hca [Hsa Hka]] Hrest IH]; cbn; congruence. }
  assert (Hsize : fold_right (fun a n => rw_candidate_size a + n) 0 args =
      fold_right (fun t n => rw_tree_size t + n) 0 (map rw_candidate_tree args)).
  { clear Hcost; induction Hargs as [|a args [Hca [Hsa Hka]] Hrest IH]; cbn; congruence. }
  assert (Hcode : flat_map rw_candidate_code args =
      flat_map (rw_tree_code EK ES EV) (map rw_candidate_tree args)).
  { clear Hcost Hsize; induction Hargs as [|a args [Hca [Hsa Hka]] Hrest IH]; cbn; congruence. }
  rewrite Hcost, Hsize, Hcode, length_map; auto.
Qed.

(** Valid tables contain accurate caches and finite represented witnesses within their height. *)
Definition rw_tree_valid {K Sort V} EK ES EV vc oc (g : rw_graph K Sort V) h
    (m : rw_tree_table K Sort V) : Prop :=
  forall root a, Map.get positive_encoding root m = Some a ->
    rw_candidate_ok EK ES EV vc oc a /\ rw_represents g root (rw_candidate_tree a) /\
    rw_tree_height (rw_candidate_tree a) <= h.

Section RoundProofs.
Context {K Sort V : Type} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
  (vc : V -> nat) (oc : K -> nat) (sig : rw_signature K Sort V) (g : rw_graph K Sort V).
Hypothesis Hlayout : rw_layout sig g.

Lemma rw_tree_get_valid h m c a :
  rw_tree_valid EK ES EV vc oc g h m -> rw_tree_get g m c = Some a ->
  rw_candidate_ok EK ES EV vc oc a /\ rw_represents g c (rw_candidate_tree a) /\
    rw_tree_height (rw_candidate_tree a) <= h.
Proof.
  intros Hvalid; unfold rw_tree_get; destruct (rw_find g c) as [root|] eqn:Hc;
    intro Hget; [|discriminate].
  destruct (Hvalid root a Hget) as [Ha [Hrepr Hheight]]; split; [exact Ha|].
  split; [|exact Hheight]; eapply rw_represents_alias; [|exact Hrepr].
  rewrite Hc; exact (proj1 (proj2 (rw_layout_find sig g Hlayout c root Hc))).
Qed.

Lemma rw_tree_node_valid h m n owner node root a :
  rw_tree_valid EK ES EV vc oc g h m -> rw_node_at g n = Some (owner, node) ->
  rw_find g owner = Some root -> rw_tree_node EK ES EV vc oc g m node = Some a ->
  rw_candidate_ok EK ES EV vc oc a /\ rw_represents g root (rw_candidate_tree a) /\
    rw_tree_height (rw_candidate_tree a) <= S h.
Proof.
  intros Hvalid Hnode Ho Ha.
  pose proof (proj1 (proj2 (rw_layout_find sig g Hlayout owner root Ho))) as Hr.
  destruct node as [s v|s op ids]; cbn [rw_tree_node] in Ha.
  - injection Ha as <-; split; [unfold rw_candidate_ok, rw_tree_leaf; cbn; auto|].
    split; [eapply rw_repr_var; eassumption|cbn; lia].
  - destruct (rw_tree_children g m ids) as [args|] eqn:Hargs; cbn in Ha;
      [injection Ha as <-|discriminate].
    apply rw_tree_children_spec in Hargs.
    assert (Hchildren : Forall (rw_candidate_ok EK ES EV vc oc) args /\
        Forall2 (rw_represents g) ids (map rw_candidate_tree args) /\
        Forall (fun t => rw_tree_height t <= h) (map rw_candidate_tree args)).
    { clear Hnode Ho Hr; induction Hargs as [|id a ids args Hget Hrest IH]; cbn.
      - split; [constructor|split; constructor].
      - destruct (rw_tree_get_valid h m id a Hvalid Hget) as [Ha [Hrepr Hheight]].
        destruct IH as [Hoks [Hreprs Hheights]]; split; [now constructor|].
        split; now constructor. }
    destruct Hchildren as [Hoks [Hreprs Hheights]]; split; [apply rw_tree_app_ok; exact Hoks|].
    split; [eapply rw_repr_app; eassumption|].
    change (S (fold_right (fun t n => Nat.max (rw_tree_height t) n) 0
      (map rw_candidate_tree args)) <= S h).
    assert (Hmax : fold_right (fun t n => Nat.max (rw_tree_height t) n) 0
      (map rw_candidate_tree args) <= h) by (apply rw_height_args; exact Hheights).
    lia.
Qed.

Lemma rw_tree_insert_valid h m root a :
  rw_tree_valid EK ES EV vc oc g h m ->
  rw_candidate_ok EK ES EV vc oc a -> rw_represents g root (rw_candidate_tree a) ->
  rw_tree_height (rw_candidate_tree a) <= h ->
  rw_tree_valid EK ES EV vc oc g h (rw_tree_insert m root a).
Proof.
  intros Hvalid Ha Hrepr Hheight r b Hget; unfold rw_tree_insert in Hget.
  destruct (Pos.eq_dec r root) as [->|Hne].
  - rewrite Map.get_set_same in Hget.
    destruct (Map.get positive_encoding root m) as [old|] eqn:Hold.
    + injection Hget as <-; destruct (rw_choose_tree_member old a) as [Hleft|Hright].
      * rewrite Hleft; apply Hvalid; exact Hold.
      * rewrite Hright; auto.
    + injection Hget as <-; auto.
  - rewrite Map.get_set_other in Hget by exact Hne; apply Hvalid; exact Hget.
Qed.

Lemma rw_tree_step_valid h m :
  rw_tree_valid EK ES EV vc oc g h m ->
  rw_tree_valid EK ES EV vc oc g (S h) (rw_tree_step EK ES EV vc oc g m).
Proof.
  intro Hvalid; unfold rw_tree_step; rewrite Map.fold_elements.
  assert (Hstart : rw_tree_valid EK ES EV vc oc g (S h) m).
  { intros root a Hget; destruct (Hvalid root a Hget) as [Ha [Hr Hh]]; auto. }
  assert (Hnodes : forall n owner node, In (n, (owner, node)) (Map.elements (rw_nodes g)) ->
      rw_node_at g n = Some (owner, node)).
  { intros n owner node Hin; apply Map.elements_sound; [exact (rw_layout_productions sig g Hlayout)|
      exact Hin]. }
  assert (Hfold : forall xs acc,
      rw_tree_valid EK ES EV vc oc g (S h) acc ->
      (forall n owner node, In (n, (owner, node)) xs -> rw_node_at g n = Some (owner, node)) ->
      rw_tree_valid EK ES EV vc oc g (S h) (fold_left (fun acc kv =>
        rw_tree_visit EK ES EV vc oc g m acc (fst kv) (snd kv)) xs acc)).
  { intro xs; induction xs as [|[n [owner node]] xs IH]; intros acc Hacc Hactual;
      cbn [fold_left fst snd]; [exact Hacc|].
    apply IH; [|intros; apply Hactual; cbn; auto].
    unfold rw_tree_visit; change (rw_tree_valid EK ES EV vc oc g (S h)
      (match rw_find g owner, rw_tree_node EK ES EV vc oc g m node with
      | Some root, Some a => rw_tree_insert acc root a
      | _, _ => acc
      end)).
    destruct (rw_find g owner) as [root|] eqn:Ho;
      destruct (rw_tree_node EK ES EV vc oc g m node) as [a|] eqn:Ha; try exact Hacc.
    destruct (rw_tree_node_valid h m n owner node root a Hvalid
      (Hactual n owner node (or_introl eq_refl)) Ho Ha) as [Hok [Hrepr Hheight]].
    apply rw_tree_insert_valid; assumption. }
  apply Hfold; assumption.
Qed.

End RoundProofs.

(** * Optimality within a finite height *)

Definition rw_trees_better {K Sort V} vc oc (ts us : list (rw_term K Sort V)) : Prop :=
  fold_right (fun t n => rw_tree_cost vc oc t + n) 0 ts <=
    fold_right (fun u n => rw_tree_cost vc oc u + n) 0 us /\
  (fold_right (fun u n => rw_tree_cost vc oc u + n) 0 us <=
      fold_right (fun t n => rw_tree_cost vc oc t + n) 0 ts ->
    fold_right (fun t n => rw_tree_size t + n) 0 ts <=
      fold_right (fun u n => rw_tree_size u + n) 0 us).

Lemma rw_trees_better_pointwise {K Sort V} vc oc (ts us : list (rw_term K Sort V)) :
  Forall2 (rw_tree_better vc oc) ts us -> rw_trees_better vc oc ts us.
Proof.
  intro Hargs; induction Hargs as [|t u ts us [Hcost Hsize] Hrest [Hcosts Hsizes]];
    unfold rw_trees_better in *; cbn; split; lia.
Qed.

Lemma rw_tree_better_app {K Sort V} vc oc s op (ts us : list (rw_term K Sort V)) :
  rw_trees_better vc oc ts us -> rw_tree_better vc oc (RWApp s op ts) (RWApp s op us).
Proof.
  unfold rw_trees_better, rw_tree_better; cbn; intros [Hcost Hsize]; split; [lia|].
  intro Hreverse; specialize (Hsize ltac:(lia)); lia.
Qed.

Lemma rw_candidate_rank_sound {K Sort V} EK ES EV vc oc (a b : rw_tree_candidate K Sort V) :
  rw_candidate_ok EK ES EV vc oc a -> rw_candidate_ok EK ES EV vc oc b ->
  rw_candidate_better a b -> rw_tree_better vc oc (rw_candidate_tree a) (rw_candidate_tree b).
Proof.
  intros [Hca [Hsa Hka]] [Hcb [Hsb Hkb]] Hrank.
  unfold rw_candidate_better in Hrank; unfold rw_tree_better.
  now rewrite Hca, Hcb, Hsa, Hsb in Hrank.
Qed.

(** Every represented term up to the stated height is bounded by its class's stored candidate. *)
Definition rw_tree_complete {K Sort V} vc oc (g : rw_graph K Sort V) h
    (m : rw_tree_table K Sort V) : Prop :=
  forall c t, rw_represents g c t -> rw_tree_height t <= h ->
    exists a, rw_tree_get g m c = Some a /\ rw_tree_better vc oc (rw_candidate_tree a) t.

Lemma rw_tree_children_complete {K Sort V} vc oc (g : rw_graph K Sort V) h m ids ts :
  rw_tree_complete vc oc g h m -> Forall2 (rw_represents g) ids ts ->
  Forall (fun t => rw_tree_height t <= h) ts ->
  exists args, rw_tree_children g m ids = Some args /\
    Forall2 (rw_tree_better vc oc) (map rw_candidate_tree args) ts.
Proof.
  intros Hcomplete Hrepr; induction Hrepr as [|id t ids ts Hrepr Hrest IH]; intro Hheights.
  - exists []; split; [reflexivity|constructor].
  - inversion Hheights as [|t' ts' Hheight Htail]; subst.
    destruct (Hcomplete id t Hrepr Hheight) as [a [Ha Hbetter]].
    destruct (IH Htail) as [args [Hargs Hbetters]].
    exists (a :: args); split.
    + cbn [rw_tree_children]; rewrite Ha, Hargs; reflexivity.
    + cbn; now constructor.
Qed.

Section CompleteProofs.
Context {K Sort V : Type} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
  (vc : V -> nat) (oc : K -> nat) (sig : rw_signature K Sort V) (g : rw_graph K Sort V).
Hypothesis Hlayout : rw_layout sig g.

Lemma rw_tree_step_hit h m c n owner node root a :
  rw_tree_valid EK ES EV vc oc g h m -> rw_node_at g n = Some (owner, node) ->
  rw_find g owner = Some root -> rw_find g c = Some root ->
  rw_tree_node EK ES EV vc oc g m node = Some a ->
  exists b, rw_tree_get g (rw_tree_step EK ES EV vc oc g m) c = Some b /\
    rw_tree_better vc oc (rw_candidate_tree b) (rw_candidate_tree a).
Proof.
  intros Hvalid Hnode Ho Hc Ha.
  destruct (rw_tree_fold_hit EK ES EV vc oc g m (Map.elements (rw_nodes g)) m
    n owner node root a) as [b [Hb Hba]].
  - apply (Map.elements_complete positive_encoding);
      [exact (rw_layout_productions sig g Hlayout)|exact Hnode].
  - exact Ho.
  - exact Ha.
  - assert (Hget : rw_tree_get g (rw_tree_step EK ES EV vc oc g m) c = Some b).
    { unfold rw_tree_get, rw_tree_step; rewrite Hc, Map.fold_elements; exact Hb. }
    exists b; split; [exact Hget|].
    destruct (rw_tree_get_valid EK ES EV vc oc sig g Hlayout (S h) _ c b
      (rw_tree_step_valid EK ES EV vc oc sig g Hlayout h m Hvalid) Hget) as [Hbvalid _].
    destruct (rw_tree_node_valid EK ES EV vc oc sig g Hlayout h m n owner node root a
      Hvalid Hnode Ho Ha) as [Havalid _].
    exact (rw_candidate_rank_sound EK ES EV vc oc b a Hbvalid Havalid Hba).
Qed.

Lemma rw_tree_step_complete h m :
  rw_tree_valid EK ES EV vc oc g h m -> rw_tree_complete vc oc g h m ->
  rw_tree_complete vc oc g (S h) (rw_tree_step EK ES EV vc oc g m).
Proof.
  intros Hvalid Hcomplete c t Hrepr Hheight.
  destruct Hrepr as [c n owner root s v Hnode Ho Hc|
    c n owner root s op ids ts Hnode Ho Hc Hargs].
  - set (a := rw_tree_leaf EK ES EV vc s v).
    assert (Ha : rw_tree_node EK ES EV vc oc g m (RWNVar s v) = Some a) by reflexivity.
    exact (rw_tree_step_hit h m c n owner (RWNVar s v) root a Hvalid Hnode Ho Hc Ha).
  - assert (Hheights : Forall (fun t => rw_tree_height t <= h) ts).
    { apply rw_height_args; cbn in Hheight; lia. }
    destruct (rw_tree_children_complete vc oc g h m ids ts Hcomplete Hargs Hheights)
      as [args [Hchildren Hbetters]].
    set (a := rw_tree_app EK ES EV oc s op args).
    assert (Ha : rw_tree_node EK ES EV vc oc g m (RWNApp s op ids) = Some a).
    { cbn [rw_tree_node]; now rewrite Hchildren. }
    destruct (rw_tree_step_hit h m c n owner (RWNApp s op ids) root a Hvalid Hnode Ho Hc Ha)
      as [b [Hb Hba]].
    exists b; split; [exact Hb|]; eapply rw_tree_better_trans; [exact Hba|].
    apply rw_tree_better_app, rw_trees_better_pointwise; exact Hbetters.
Qed.

(** Round h contains finite witnesses and the cost/size optimum among height-at-most-h terms. *)
Theorem rw_tree_rounds_correct h :
  rw_tree_valid EK ES EV vc oc g h (rw_tree_rounds EK ES EV vc oc g (N.of_nat h)) /\
  rw_tree_complete vc oc g h (rw_tree_rounds EK ES EV vc oc g (N.of_nat h)).
Proof.
  induction h as [|h [Hvalid Hcomplete]].
  - split.
    + intros root a Hget; change (Map.get positive_encoding root Map.empty = Some a) in Hget.
      rewrite Map.get_empty in Hget; discriminate.
    + intros c t Hrepr Hheight; pose proof (rw_height_positive t); lia.
  - unfold rw_tree_rounds in *; rewrite Nat2N.inj_succ, N.iter_succ.
    split.
    + apply (rw_tree_step_valid EK ES EV vc oc sig g Hlayout h); exact Hvalid.
    + apply rw_tree_step_complete; assumption.
Qed.

End CompleteProofs.

(** * Repeated-class elimination *)

(** Minimality is bounded by height, making its witness available constructively from a round. *)
Definition rw_minimal_at {K Sort V} vc oc (g : rw_graph K Sort V) h c
    (t : rw_term K Sort V) : Prop :=
  forall u, rw_represents g c u -> rw_tree_height u <= h -> rw_tree_better vc oc t u.

Lemma rw_minimal_args {K Sort V} vc oc (g : rw_graph K Sort V) h ids ts :
  Forall2 (rw_represents g) ids ts -> Forall (fun t => rw_tree_height t <= h) ts ->
  (forall us, Forall2 (rw_represents g) ids us ->
    Forall (fun u => rw_tree_height u <= h) us -> rw_trees_better vc oc ts us) ->
  Forall2 (rw_minimal_at vc oc g h) ids ts.
Proof.
  intro Hrepr; induction Hrepr as [|id t ids ts Hrepr Hrest IH]; intros Hheights Hminimal.
  - constructor.
  - inversion Hheights as [|t' ts' Hheight Htail]; subst; constructor.
    + intros u Hu Hhu.
      assert (Hus : Forall2 (rw_represents g) (id :: ids) (u :: ts)) by now constructor.
      assert (Hhus : Forall (fun t => rw_tree_height t <= h) (u :: ts)) by now constructor.
      specialize (Hminimal (u :: ts) Hus Hhus).
      unfold rw_trees_better in Hminimal; unfold rw_tree_better; cbn in Hminimal; lia.
    + apply IH; [exact Htail|].
      intros us Hus Hhus.
      assert (Hts : Forall2 (rw_represents g) (id :: ids) (t :: us)) by now constructor.
      assert (Hhts : Forall (fun t => rw_tree_height t <= h) (t :: us)) by now constructor.
      specialize (Hminimal (t :: us) Hts Hhts).
      unfold rw_trees_better in *; cbn in Hminimal; lia.
Qed.

Lemma rw_minimal_children {K Sort V} vc oc (g : rw_graph K Sort V) h
    c n owner root s op ids ts :
  rw_node_at g n = Some (owner, RWNApp s op ids) -> rw_find g owner = Some root ->
  rw_find g c = Some root -> Forall2 (rw_represents g) ids ts ->
  rw_tree_height (RWApp s op ts) <= S h ->
  rw_minimal_at vc oc g (S h) c (RWApp s op ts) ->
  Forall2 (rw_minimal_at vc oc g h) ids ts.
Proof.
  intros Hnode Ho Hc Hargs Hheight Hminimal.
  assert (Hheights : Forall (fun t => rw_tree_height t <= h) ts).
  { apply rw_height_args; cbn in Hheight; lia. }
  apply (rw_minimal_args vc oc g h ids ts Hargs Hheights).
  intros us Hreprs Hheights'.
  assert (Hheight' : rw_tree_height (RWApp s op us) <= S h).
  { cbn; apply rw_height_args in Hheights'; lia. }
  specialize (Hminimal (RWApp s op us)
    (rw_repr_app g c n owner root s op ids us Hnode Ho Hc Hreprs) Hheight').
  unfold rw_tree_better in Hminimal; unfold rw_trees_better; cbn in Hminimal; lia.
Qed.

(** Excluded classes have no sufficiently small and cheap competitor at the remaining height.
    Descending from a minimum witness excludes its root: any repeated root could replace the
    ancestor, preserving cost and strictly decreasing size, including when every cycle costs
    zero. *)
Definition rw_tree_excludes {K Sort V} vc oc (g : rw_graph K Sort V) h
    (allowed : list rw_id) (t : rw_term K Sort V) : Prop :=
  forall root, In root (rw_roots g) -> ~ In root allowed ->
    forall u, rw_represents g root u -> rw_tree_cost vc oc u <= rw_tree_cost vc oc t ->
      rw_tree_height u <= h -> rw_tree_size t < rw_tree_size u.

Lemma rw_remove_member root r xs :
  In r (remove Pos.eq_dec root xs) <-> In r xs /\ r <> root.
Proof.
  induction xs as [|x xs IH]; cbn; [tauto|].
  destruct (Pos.eq_dec root x) as [->|Hne]; cbn; rewrite IH; intuition congruence.
Qed.

Lemma rw_remove_shorter root xs : In root xs -> length (remove Pos.eq_dec root xs) < length xs.
Proof.
  induction xs as [|x xs IH]; cbn; [contradiction|].
  destruct (Pos.eq_dec root x) as [->|Hne]; cbn.
  - assert (Hle : length (remove Pos.eq_dec x xs) <= length xs).
    { clear IH; induction xs as [|y xs IHxs]; cbn; [lia|].
      destruct (Pos.eq_dec x y); cbn; lia. }
    lia.
  - intros [Heq|Hin]; [congruence|specialize (IH Hin); lia].
Qed.

Lemma rw_combine_forall2 {A B} (R : A -> B -> Prop) xs ys :
  Forall2 R xs ys -> forall x y, In (x, y) (combine xs ys) -> R x y.
Proof.
  intro Hrel; induction Hrel as [|x y xs ys Hhead Htail IH]; intros a b Hin;
    cbn in Hin; [contradiction|].
  destruct Hin as [Heq|Hin]; [injection Heq as <- <-; exact Hhead|exact (IH a b Hin)].
Qed.

Lemma rw_combine_witness {A B} (R : A -> B -> Prop) xs ys y :
  Forall2 R xs ys -> In y ys -> exists x, In (x, y) (combine xs ys).
Proof.
  intro Hrel; induction Hrel as [|x b xs ys Hhead Htail IH]; cbn; [contradiction|].
  intros [<-|Hin]; [exists x; auto|].
  destruct (IH Hin) as [a Ha]; exists a; auto.
Qed.

Section HeightBound.
Context {K Sort V : Type} (vc : V -> nat) (oc : K -> nat)
  (sig : rw_signature K Sort V) (g : rw_graph K Sort V).
Hypothesis Hlayout : rw_layout sig g.

Lemma rw_minimal_root_allowed h allowed c t :
  rw_represents g c t -> rw_tree_height t <= h ->
  rw_tree_excludes vc oc g h allowed t ->
  exists root, rw_find g c = Some root /\ In root allowed.
Proof.
  intros Hrepr Hheight Hexcludes.
  destruct (rw_represents_find g c t Hrepr) as [root Hc].
  destruct (rw_layout_find sig g Hlayout c root Hc) as [Hin [Hr Hsort]].
  exists root; split; [exact Hc|].
  destruct (in_dec Pos.eq_dec root allowed) as [Hallowed|Habsent]; [exact Hallowed|].
  assert (Hrepr' : rw_represents g root t) by
    (eapply rw_represents_alias; [rewrite Hc, Hr; reflexivity|exact Hrepr]).
  specialize (Hexcludes root Hin Habsent t Hrepr' (Nat.le_refl _) Hheight); lia.
Qed.

Lemma rw_minimal_child_excludes h allowed c n owner root s op ids ts id t :
  rw_node_at g n = Some (owner, RWNApp s op ids) -> rw_find g owner = Some root ->
  rw_find g c = Some root -> Forall2 (rw_represents g) ids ts ->
  rw_minimal_at vc oc g (S h) c (RWApp s op ts) ->
  rw_tree_excludes vc oc g (S h) allowed (RWApp s op ts) ->
  In (id, t) (combine ids ts) ->
  rw_tree_excludes vc oc g h (remove Pos.eq_dec root allowed) t.
Proof.
  intros Hnode Ho Hc Hargs Hminimal Hexcludes Hin q Hq Habsent u Hu Hcost Hheight.
  assert (Hint : In t ts).
  { apply in_combine_r in Hin; exact Hin. }
  destruct (rw_measure_child vc oc ts t Hint) as [Hcostt Hsizet].
  destruct (Pos.eq_dec q root) as [->|Hne].
  - pose proof (proj1 (proj2 (rw_layout_find sig g Hlayout c root Hc))) as Hr.
    assert (Hu' : rw_represents g c u) by
      (apply (rw_represents_alias g root c u); [rewrite Hc, Hr; reflexivity|exact Hu]).
    destruct (Hminimal u Hu' ltac:(lia)) as [Hmincost Hminsize].
    cbn in Hcost, Hminsize; specialize (Hminsize ltac:(cbn; lia)); lia.
  - assert (Habsent' : ~ In q allowed).
    { intro Hinallowed; apply Habsent, rw_remove_member; auto. }
    specialize (Hexcludes q Hq Habsent' u Hu ltac:(cbn; lia) ltac:(lia)).
    cbn in Hexcludes; lia.
Qed.

(** An optimal height-bounded witness cannot repeat a canonical class along a path. *)
Theorem rw_minimal_height h :
  forall allowed c t, rw_represents g c t -> rw_tree_height t <= h ->
    rw_minimal_at vc oc g h c t -> rw_tree_excludes vc oc g h allowed t ->
    rw_tree_height t <= length allowed.
Proof.
  induction h as [|h IH]; intros allowed c t Hrepr Hheight Hminimal Hexcludes.
  - pose proof (rw_height_positive t); lia.
  - destruct (rw_minimal_root_allowed (S h) allowed c t Hrepr Hheight Hexcludes)
      as [root [Hc Hallowed]].
    pose proof (rw_remove_shorter root allowed Hallowed) as Hshorter.
    destruct Hrepr as [c n owner r s v Hnode Ho Hc'|
      c n owner r s op ids ts Hnode Ho Hc' Hargs].
    + cbn; eapply Nat.le_trans; [|exact Hshorter]; apply le_n_S, Nat.le_0_l.
    + assert (Hr : r = root) by congruence; subst r.
      pose proof (rw_minimal_children vc oc g h c n owner root s op ids ts
        Hnode Ho Hc Hargs Hheight Hminimal) as Hminimals.
      assert (Hheights : Forall (fun t => rw_tree_height t <= h) ts).
      { apply rw_height_args; cbn in Hheight; lia. }
      assert (Hbounds : Forall (fun t => rw_tree_height t <=
          length (remove Pos.eq_dec root allowed)) ts).
      { apply Forall_forall; intros t Hint.
        destruct (rw_combine_witness _ ids ts t Hargs Hint) as [id Hin].
        pose proof (rw_combine_forall2 _ ids ts Hargs id t Hin) as Ht.
        pose proof (rw_combine_forall2 _ ids ts Hminimals id t Hin) as Hmin.
        pose proof (proj1 (Forall_forall _ _) Hheights t Hint) as Hh.
        apply (IH _ id t Ht Hh Hmin).
        exact (rw_minimal_child_excludes h allowed c n owner root s op ids ts id t
          Hnode Ho Hc Hargs Hminimal Hexcludes Hin). }
      apply rw_height_args in Hbounds; cbn.
      eapply Nat.le_trans; [apply le_n_S; exact Hbounds|exact Hshorter].
Qed.

End HeightBound.

(** * Completeness at the canonical-class bound *)

(** Every finite witness has a cost/size-better witness whose height is at most the class count. *)
Theorem rw_class_bounded_witness {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) vc oc
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V) c t :
  rw_graph_wf sig g -> rw_represents g c t ->
  exists u, rw_represents g c u /\ rw_tree_better vc oc u t /\
    rw_tree_height u <= length (rw_roots g).
Proof.
  intros Hwf Hrepr; pose proof (rw_wf_layout sig g Hwf) as Hlayout.
  set (h := rw_tree_height t).
  destruct (rw_tree_rounds_correct EK ES EV vc oc sig g Hlayout h) as [Hvalid Hcomplete].
  destruct (Hcomplete c t Hrepr (Nat.le_refl _)) as [a [Hget Hbetter]].
  destruct (rw_tree_get_valid EK ES EV vc oc sig g Hlayout h _ c a Hvalid Hget)
    as [Hok [Hrepresented Hheight]].
  exists (rw_candidate_tree a); split; [exact Hrepresented|]; split; [exact Hbetter|].
  apply (rw_minimal_height vc oc sig g Hlayout h (rw_roots g) c (rw_candidate_tree a)
    Hrepresented Hheight).
  - intros u Hu Hhu; destruct (Hcomplete c u Hu Hhu) as [b [Hb Hbu]].
    rewrite Hget in Hb; injection Hb as <-; exact Hbu.
  - intros root Hin Hnot; contradiction.
Qed.

Lemma rw_extract_candidate_correct {K Sort V} EK ES EV vc oc
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V) c a :
  rw_graph_wf sig g ->
  rw_tree_get g (rw_tree_rounds EK ES EV vc oc g (N.of_nat (length (rw_roots g)))) c = Some a ->
  rw_represents g c (rw_candidate_tree a) /\
    forall u, rw_represents g c u -> rw_tree_better vc oc (rw_candidate_tree a) u.
Proof.
  intros Hwf Hget; pose proof (rw_wf_layout sig g Hwf) as Hlayout.
  destruct (rw_tree_rounds_correct EK ES EV vc oc sig g Hlayout (length (rw_roots g)))
    as [Hvalid Hcomplete].
  destruct (rw_tree_get_valid EK ES EV vc oc sig g Hlayout _ _ c a Hvalid Hget)
    as [Hok [Hrepr Hheight]]; split; [exact Hrepr|].
  intros u Hu; destruct (rw_class_bounded_witness EK ES EV vc oc sig g c u Hwf Hu)
    as [v [Hv [Hvu Hhv]]].
  destruct (Hcomplete c v Hv Hhv) as [b [Hb Hbv]].
  rewrite Hget in Hb; injection Hb as <-.
  eapply rw_tree_better_trans; eassumption.
Qed.

(** The materialized result respects the class-height bound and the secondary size optimum. *)
Lemma rw_extract_tree_rank {K Sort V} EK ES EV vc oc (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) c t :
  rw_graph_wf sig g -> rw_extract_tree EK ES EV vc oc g c = Some t ->
  rw_tree_height t <= length (rw_roots g) /\
    forall u, rw_represents g c u -> rw_tree_better vc oc t u.
Proof.
  intros Hwf Hextract; unfold rw_extract_tree in Hextract.
  destruct (rw_tree_get g (rw_tree_rounds EK ES EV vc oc g
    (N.of_nat (length (rw_roots g)))) c) as [a|] eqn:Hget; cbn in Hextract;
    [injection Hextract as <-|discriminate].
  destruct (rw_tree_rounds_correct EK ES EV vc oc sig g (rw_wf_layout sig g Hwf)
    (length (rw_roots g))) as [Hvalid Hcomplete].
  destruct (rw_tree_get_valid EK ES EV vc oc sig g (rw_wf_layout sig g Hwf) _ _ c a Hvalid Hget)
    as [Hok [Hrepr Hheight]].
  split; [exact Hheight|].
  exact (proj2 (rw_extract_candidate_correct EK ES EV vc oc sig g c a Hwf Hget)).
Qed.

(** Successful extraction returns a represented finite tree of minimum additive natural cost. *)
Theorem rw_extract_tree_some {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (var_cost : V -> nat) (op_cost : K -> nat)
    (g : rw_graph K Sort V) (c : rw_id) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> rw_extract_tree EK ES EV var_cost op_cost g c = Some t ->
  rw_represents g c t /\
  forall u, rw_represents g c u ->
    rw_tree_cost var_cost op_cost t <= rw_tree_cost var_cost op_cost u.
Proof.
  intros Hwf Hextract; unfold rw_extract_tree in Hextract.
  destruct (rw_tree_get g (rw_tree_rounds EK ES EV var_cost op_cost g
    (N.of_nat (length (rw_roots g)))) c) as [a|] eqn:Hget; cbn in Hextract;
    [injection Hextract as <-|discriminate].
  destruct (rw_extract_candidate_correct EK ES EV var_cost op_cost sig g c a Hwf Hget)
    as [Hrepr Hminimal]; split; [exact Hrepr|].
  intros u Hu; exact (proj1 (Hminimal u Hu)).
Qed.

(** Failure means exactly that the class has no finite represented tree, without productivity. *)
Theorem rw_extract_tree_none {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (var_cost : V -> nat) (op_cost : K -> nat)
    (g : rw_graph K Sort V) (c : rw_id) :
  rw_graph_wf sig g -> (rw_extract_tree EK ES EV var_cost op_cost g c = None <->
    (forall t, ~ rw_represents g c t)).
Proof.
  intro Hwf; split.
  - intros Hnone t Hrepr.
    destruct (rw_class_bounded_witness EK ES EV var_cost op_cost sig g c t Hwf Hrepr)
      as [u [Hu [Hbetter Hheight]]].
    destruct (rw_tree_rounds_correct EK ES EV var_cost op_cost sig g (rw_wf_layout sig g Hwf)
      (length (rw_roots g))) as [Hvalid Hcomplete].
    destruct (Hcomplete c u Hu Hheight) as [a [Hget Hminimal]].
    unfold rw_extract_tree in Hnone; rewrite Hget in Hnone; discriminate.
  - intro Habsent; destruct (rw_extract_tree EK ES EV var_cost op_cost g c) as [t|] eqn:Hget;
      [|reflexivity].
    exfalso; apply (Habsent t).
    exact (proj1 (rw_extract_tree_some EK ES EV sig var_cost op_cost g c t Hwf Hget)).
Qed.

(** Sound class equality connects the minimum-cost witness to any represented input's semantics. *)
Theorem rw_extract_tree_equiv {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (var_cost : V -> nat) (op_cost : K -> nat) (g : rw_graph K Sort V)
    (c : rw_id) (input output : rw_term K Sort V) :
  Forall (rw_rule_sound sig admissible) rules -> rw_graph_wf sig g ->
  rw_graph_sound sig admissible rules g -> rw_represents g c input ->
  rw_extract_tree EK ES EV var_cost op_cost g c = Some output ->
  rw_equiv admissible input output /\
  rw_tree_cost var_cost op_cost output <= rw_tree_cost var_cost op_cost input.
Proof.
  intros Hrules Hwf Hsound Hinput Hextract.
  destruct (rw_extract_tree_some EK ES EV sig var_cost op_cost g c output Hwf Hextract)
    as [Houtput Hminimal]; split.
  - apply (rw_equal_sound sig admissible rules Hrules input output).
    exact (Hsound c input output Hinput Houtput).
  - exact (Hminimal input Hinput).
Qed.
