(** * Relational pointers, unification, escape and untouched bytes

    Relational observations connect pointer origins to inclusion constraints and byte facts.
    For example, a dangling input may denote every static site until its block is allocated.
    Builds on: AnalysesPointsToBase, AnalysesPointsToDelta, ViewsForward and DomainsFootprint. *)

From Stdlib Require Import List Bool ZArith Lia Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsUnionFind.
From Gaulois.Order Require Import OrderLattice OrderPowerset OrderConcrete.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointLeast.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemory ViewsForward.
From Gaulois.Analyses Require Import AnalysesLiveness.
From Gaulois.Analyses Require Export AnalysesPointsToBase AnalysesPointsToDelta.
Import List.ListNotations.

(** Relational observations allow several active bindings and speculative sites per key. *)
Record relational_ptr_view (S V T : Type) : Type := RelationalPtrView {
  rel_value : S -> V -> T -> Prop;
  rel_heap : S -> T -> T -> Prop
}.

Arguments RelationalPtrView {S V T}.
Arguments rel_value {S V T}.
Arguments rel_heap {S V T}.

(** Local origins mention semantic observations and static effects, independently of a solution. *)
Record relational_ptr_laws {S O V T} (m : semantics S O)
    (rv : relational_ptr_view S V T) (ops : list (ptr_op V T)) : Prop := {
  rel_value_initial : forall s x t, initial m s -> rel_value rv s x t ->
    In (PAlloc x t) ops;
  rel_heap_initial : forall s t0 t, initial m s -> rel_heap rv s t0 t -> False;
  rel_value_origin : forall s l s' x t, reachable_state m s -> step m s l s' ->
    rel_value rv s' x t ->
    rel_value rv s x t \/ In (PAlloc x t) ops \/
    (exists y, In (PCopy x y) ops /\ rel_value rv s y t) \/
    (exists p t0, In (PLoad x p) ops /\ rel_value rv s p t0 /\ rel_heap rv s t0 t);
  rel_heap_origin : forall s l s' t0 t, reachable_state m s -> step m s l s' ->
    rel_heap rv s' t0 t -> rel_heap rv s t0 t \/
    (exists p y, In (PStore p y) ops /\ rel_value rv s p t0 /\ rel_value rv s y t)
}.

Arguments Build_relational_ptr_laws {S O V T m rv ops}.
Arguments rel_value_initial {S O V T m rv ops}.
Arguments rel_heap_initial {S O V T m rv ops}.
Arguments rel_value_origin {S O V T m rv ops}.
Arguments rel_heap_origin {S O V T m rv ops}.

Lemma relational_pts_step {S O V T} (m : semantics S O)
    (rv : relational_ptr_view S V T) (ET : encoding T) ops sigma
    (Hlaws : relational_ptr_laws m rv ops) (Hclosed : pts_closed ET ops sigma) s l s' :
  reachable_state m s -> step m s l s' ->
  (forall x t, rel_value rv s x t -> fmem ET t (sigma (PVal x)) = true) ->
  (forall u t, rel_heap rv s u t -> fmem ET t (sigma (PHeap u)) = true) ->
  (forall x t, rel_value rv s' x t -> fmem ET t (sigma (PVal x)) = true) /\
  (forall u t, rel_heap rv s' u t -> fmem ET t (sigma (PHeap u)) = true).
Proof.
  intros Hreach Hstep Hval Hheap; split.
  - intros x t Hpts; destruct (rel_value_origin Hlaws s l s' x t Hreach Hstep Hpts)
      as [Hold|[Halloc|[[y [Hcopy Hy]]|[p [u [Hload [Hp Ht]]]]]]].
    + apply Hval; exact Hold.
    + eapply pts_alloc_closed; eassumption.
    + eapply pts_copy_closed; [exact Hclosed|exact Hcopy|apply Hval; exact Hy].
    + eapply pts_load_closed; [exact Hclosed|exact Hload|apply Hval; exact Hp|
        apply Hheap; exact Ht].
  - intros u t Hpts; destruct (rel_heap_origin Hlaws s l s' u t Hreach Hstep Hpts)
      as [Hold|[p [y [Hstore [Hp Hy]]]]].
    + apply Hheap; exact Hold.
    + eapply pts_store_closed; [exact Hclosed|exact Hstore|apply Hval; exact Hp|
        apply Hval; exact Hy].
Qed.

(** * Indexed unification of pointer shapes *)

Module SteensUnify.

Section Closure.
Context (nodes : list positive) (equations references : list (positive * positive)).
Hypothesis equations_supported : forall a b, In (a, b) equations -> In a nodes /\ In b nodes.
Hypothesis references_supported : forall a b, In (a, b) references -> In a nodes /\ In b nodes.

Local Abbreviation E := positive_encoding.
Local Abbreviation db := (@PtsDelta.database positive positive).
Local Abbreviation st := (@PtsDelta.state positive positive).

(** Dereference subscribers are indexed once, independently of the equality worklist. *)
Definition reference_index : db :=
  fold_right (PtsDelta.put_row E E) Map.empty references.

Lemma reference_rows_wf : PtsDelta.rows_wf E E reference_index.
Proof.
  clear references_supported; unfold reference_index;
    induction references as [|e es IH]; cbn [fold_right].
  - apply PtsDelta.rows_empty.
  - apply PtsDelta.rows_put; exact IH.
Qed.

Lemma reference_member a b : PtsDelta.holds E E reference_index (a, b) <->
  In (a, b) references.
Proof.
  clear references_supported; unfold reference_index;
    induction references as [|e es IH]; cbn [fold_right].
  - split; [intro H; exfalso; exact (PtsDelta.holds_empty E E _ H)|contradiction].
  - rewrite PtsDelta.holds_put, IH; cbn [In]; intuition congruence.
Qed.

Definition children (index : db) (a : positive) : list positive :=
  FinSet.elements (PtsDelta.row E index a).

Lemma children_member index a b : PtsDelta.rows_wf E E index ->
  (In b (children index a) <-> PtsDelta.holds E E index (a, b)).
Proof.
  intros [_ Hrows]; apply FinSet.elements_spec, Hrows.
Qed.

Definition universe : list (positive * positive) := list_prod nodes nodes.
Definition seeds : list (positive * positive) := equations ++ map (fun a => (a, a)) nodes.

(** Equal source shapes unify dereferences; indexed equality rows close paths in both orders. *)
Definition consequences (index : db) (current : db) (e : positive * positive) :
    list (positive * positive) :=
  let a := fst e in
  let b := snd e in
  (b, a) ::
    map (fun c => (a, c)) (children current b) ++
    map (fun c => (c, b)) (children current a) ++
    list_prod (children index a) (children index b).

Lemma seeds_supported : incl seeds universe.
Proof.
  intros [a b] Hin; apply in_prod_iff; unfold seeds in Hin; apply in_app_or in Hin.
  destruct Hin as [Hin|Hin]; [apply equations_supported; exact Hin|].
  apply in_map_iff in Hin; destruct Hin as [c [Heq Hc]]; injection Heq as <- <-; auto.
Qed.

Lemma consequences_supported current e : PtsDelta.valid E E universe current ->
  PtsDelta.holds E E (PtsDelta.current current) e ->
  incl (consequences reference_index (PtsDelta.current current) e) universe.
Proof.
  intros Hvalid He [x y] Hout.
  pose proof (PtsDelta.current_supported E E universe current Hvalid e He) as Hsupport.
  destruct e as [a b]; apply in_prod_iff in Hsupport; destruct Hsupport as [Ha Hb].
  cbn [consequences fst snd In] in Hout; apply in_prod_iff.
  destruct Hout as [Heq|Hout]; [injection Heq as <- <-; auto|].
  apply in_app_or in Hout; destruct Hout as [Hout|Hout].
  - apply in_map_iff in Hout; destruct Hout as [c [Heq Hc]]; injection Heq as <- <-.
    apply (children_member _ _ _ (PtsDelta.current_wf E E universe current Hvalid)) in Hc.
    apply (PtsDelta.current_supported E E universe current Hvalid) in Hc.
    apply in_prod_iff in Hc; tauto.
  - apply in_app_or in Hout; destruct Hout as [Hout|Hout].
    + apply in_map_iff in Hout; destruct Hout as [c [Heq Hc]]; injection Heq as <- <-.
      apply (children_member _ _ _ (PtsDelta.current_wf E E universe current Hvalid)) in Hc.
      apply (PtsDelta.current_supported E E universe current Hvalid) in Hc.
      apply in_prod_iff in Hc; tauto.
    + apply in_prod_iff in Hout; destruct Hout as [Hx Hy].
      apply (children_member _ _ _ reference_rows_wf), reference_member in Hx, Hy.
      destruct (references_supported _ _ Hx), (references_supported _ _ Hy); auto.
Qed.

Definition present (current : st) a b : Prop :=
  PtsDelta.holds E E (PtsDelta.current current) (a, b).

Definition done_pair (current : st) a b : Prop :=
  FinSet.mem (pair_encoding E E) (a, b) (PtsDelta.processed current) = true.

(** Processing records obligations only for processed pairs; later events discharge late joins. *)
Record invariant (current : st) : Prop := Invariant {
  engine_valid : PtsDelta.valid E E universe current;
  initial_present : forall a b, In (a, b) seeds -> present current a b;
  symmetric_covered : forall a b, done_pair current a b -> present current b a;
  transitive_covered : forall a b c,
    done_pair current a b -> done_pair current b c -> present current a c;
  reference_covered : forall a b x y, done_pair current a b ->
    In (a, x) references -> In (b, y) references -> present current x y
}.

Definition initial : st := PtsDelta.insert_all E E seeds PtsDelta.empty.

Lemma initial_invariant : invariant initial.
Proof.
  constructor.
  - apply PtsDelta.valid_insert_all; [apply PtsDelta.valid_empty|apply seeds_supported].
  - intros a b Hin; apply PtsDelta.insert_all_holds; now left.
  - intros a b Hdone; unfold done_pair, initial in Hdone.
    rewrite PtsDelta.insert_all_processed in Hdone.
    cbn [PtsDelta.empty PtsDelta.processed] in Hdone; rewrite FinSet.mem_empty in Hdone;
      discriminate.
  - intros a b c Hdone; unfold done_pair, initial in Hdone.
    rewrite PtsDelta.insert_all_processed in Hdone.
    cbn [PtsDelta.empty PtsDelta.processed] in Hdone; rewrite FinSet.mem_empty in Hdone;
      discriminate.
  - intros a b x y Hdone; unfold done_pair, initial in Hdone.
    rewrite PtsDelta.insert_all_processed in Hdone.
    cbn [PtsDelta.empty PtsDelta.processed] in Hdone; rewrite FinSet.mem_empty in Hdone;
      discriminate.
Qed.

Definition advance : st -> st := PtsDelta.advance E E (consequences reference_index).

Lemma advance_invariant current : invariant current -> invariant (advance current).
Proof.
  intros Hinv; destruct (PtsDelta.pending current) as [|[a b] rest] eqn:Hqueue.
  { unfold advance; rewrite PtsDelta.advance_empty by exact Hqueue; exact Hinv. }
  pose proof (engine_valid current Hinv) as Hvalid.
  assert (He : present current a b).
  { apply (PtsDelta.pending_spec E E universe current Hvalid); rewrite Hqueue; now left. }
  assert (Hgrow : forall x y, present current x y -> present (advance current) x y).
  { intros x y Hin; apply (PtsDelta.advance_holds E E (consequences reference_index)
      current (a, b) rest (x, y) Hqueue); now right. }
  assert (Hproduce : forall x y,
    In (x, y) (consequences reference_index (PtsDelta.current current) (a, b)) ->
    present (advance current) x y).
  { intros x y Hin; apply (PtsDelta.advance_holds E E (consequences reference_index)
      current (a, b) rest (x, y) Hqueue); now left. }
  assert (Hdone : forall x y, done_pair (advance current) x y ->
    (x = a /\ y = b) \/ done_pair current x y).
  { intros x y Hin; unfold done_pair, advance in Hin.
    rewrite (PtsDelta.advance_processed E E _ _ _ _ Hqueue) in Hin.
    apply FinSet.mem_add in Hin; destruct Hin as [Heq|Hin].
    - injection Heq as -> ->; now left.
    - now right. }
  assert (Hrow : forall x y, present current x y ->
    In y (children (PtsDelta.current current) x)).
  { intros x y Hin; apply (children_member _ _ _ (PtsDelta.current_wf E E _ _ Hvalid));
      exact Hin. }
  constructor.
  - apply PtsDelta.advance_valid with (universe := universe);
      [exact consequences_supported|exact Hvalid].
  - intros x y Hin; apply Hgrow, (initial_present current Hinv); exact Hin.
  - intros x y Hin; destruct (Hdone x y Hin) as [[-> ->]|Hold].
    + apply Hproduce; now left.
    + apply Hgrow; exact (symmetric_covered current Hinv x y Hold).
  - intros x y z Hxy Hyz.
    destruct (Hdone x y Hxy) as [[-> ->]|Holdxy];
      destruct (Hdone _ z Hyz) as [[Heqy ->]|Holdyz].
    + subst b; apply Hgrow; exact He.
    + apply Hproduce; right; apply in_or_app; left; apply in_map_iff.
      exists z; split; [reflexivity|apply Hrow].
      apply (PtsDelta.processed_present E E _ _ Hvalid); exact Holdyz.
    + subst y; apply Hproduce; right; apply in_or_app; right; apply in_or_app; left.
      apply in_map_iff; exists x; split; [reflexivity|apply Hrow].
      exact (symmetric_covered current Hinv x a Holdxy).
    + apply Hgrow; exact (transitive_covered current Hinv x y z Holdxy Holdyz).
  - intros x y p q Hin Hxp Hyq; destruct (Hdone x y Hin) as [[-> ->]|Hold].
    + apply Hproduce; right; apply in_or_app; right; apply in_or_app; right.
      apply in_prod_iff; split; apply (children_member _ _ _ reference_rows_wf),
        reference_member; assumption.
    + apply Hgrow; exact (reference_covered current Hinv x y p q Hold Hxp Hyq).
Qed.

Definition solved : st :=
  let index := reference_index in
  PtsDelta.run E E (consequences index) (Pos.of_succ_nat (length nodes * length nodes)) initial.

Lemma solved_invariant : invariant solved.
Proof.
  unfold solved; apply PtsDelta.run_invariant; [apply advance_invariant|apply initial_invariant].
Qed.

Lemma solved_quiescent : PtsDelta.pending solved = [].
Proof.
  unfold solved; rewrite <- length_prod.
  apply PtsDelta.run_quiescent with (universe := universe);
    [exact consequences_supported|exact (engine_valid initial initial_invariant)].
Qed.

Lemma solved_done a b : present solved a b -> done_pair solved a b.
Proof.
  intro Hin; destruct (FinSet.mem (pair_encoding E E) (a, b) (PtsDelta.processed solved))
    eqn:Hdone; [exact Hdone|].
  exfalso; pose proof (PtsDelta.pending_spec E E universe solved
    (engine_valid solved solved_invariant) (a, b)) as Hpending.
  assert (Hqueued : In (a, b) (PtsDelta.pending solved)).
  { apply Hpending; split; [exact Hin|].
    change (~ FinSet.mem (pair_encoding E E) (a, b) (PtsDelta.processed solved) = true).
    rewrite Hdone; discriminate. }
  rewrite solved_quiescent in Hqueued; exact Hqueued.
Qed.

Lemma solved_refl a : In a nodes -> present solved a a.
Proof.
  intro Hin; apply (initial_present solved solved_invariant).
  apply in_or_app; right; apply in_map_iff; exists a; auto.
Qed.

Lemma solved_sym a b : present solved a b -> present solved b a.
Proof.
  intro Hin; apply (symmetric_covered solved solved_invariant), solved_done; exact Hin.
Qed.

Lemma solved_trans a b c : present solved a b -> present solved b c -> present solved a c.
Proof.
  intros Hab Hbc; eapply (transitive_covered solved solved_invariant);
    apply solved_done; eassumption.
Qed.

Lemma solved_reference a b x y : present solved a b ->
  In (a, x) references -> In (b, y) references -> present solved x y.
Proof.
  intros Hab Hax Hby; eapply (reference_covered solved solved_invariant);
    [apply solved_done; exact Hab|exact Hax|exact Hby].
Qed.

Definition pairs : list (positive * positive) :=
  let current := PtsDelta.current solved in
  flat_map (fun a => map (fun b => (a, b)) (children current a)) nodes.

Lemma pairs_member a b : In (a, b) pairs <-> present solved a b.
Proof.
  unfold pairs; rewrite in_flat_map; split.
  - intros [x [Hx Hin]]; apply in_map_iff in Hin; destruct Hin as [y [Heq Hy]].
    injection Heq as <- <-; apply (children_member _ _ _
      (PtsDelta.current_wf E E universe solved (engine_valid solved solved_invariant))); exact Hy.
  - intro Hin; exists a; split.
    + apply (PtsDelta.current_supported E E universe solved
        (engine_valid solved solved_invariant)) in Hin; apply in_prod_iff in Hin; tauto.
    + apply in_map_iff; exists b; split; [reflexivity|].
      apply (children_member _ _ _
        (PtsDelta.current_wf E E universe solved (engine_valid solved solved_invariant)));
        exact Hin.
Qed.

Definition forest : UnionFind.t positive := UnionFind.of_unions E pairs.

Lemma forest_present a b : present solved a b -> UnionFind.equiv E forest a b.
Proof.
  intro Hin; apply UnionFind.of_unions_equiv, rst_step, pairs_member; exact Hin.
Qed.

Lemma forest_characterization a b : UnionFind.equiv E forest a b -> a = b \/ present solved a b.
Proof.
  intro Hequiv; apply UnionFind.of_unions_equiv in Hequiv.
  induction Hequiv as [x y Hedge|x|x y Hxy IH|x y z Hxy IHxy Hyz IHyz].
  - right; apply pairs_member; exact Hedge.
  - now left.
  - destruct IH as [->|IH]; [now left|right; apply solved_sym; exact IH].
  - destruct IHxy as [->|IHxy]; [exact IHyz|].
    destruct IHyz as [->|IHyz]; [now right|right; eapply solved_trans; eassumption].
Qed.

Lemma forest_equation a b : In (a, b) equations -> UnionFind.equiv E forest a b.
Proof.
  intro Hin; apply forest_present, (initial_present solved solved_invariant).
  apply in_or_app; now left.
Qed.

(** Equal source classes unify the targets of their actual load/store subscriptions. *)
Lemma forest_reference a b x y : UnionFind.equiv E forest a b ->
  In (a, x) references -> In (b, y) references -> UnionFind.equiv E forest x y.
Proof.
  intros Hab Hax Hby; apply forest_present.
  destruct (forest_characterization _ _ Hab) as [->|Hpresent].
  - eapply solved_reference; [apply solved_refl; exact (proj1 (references_supported _ _ Hby))|
      exact Hax|exact Hby].
  - eapply solved_reference; eassumption.
Qed.

(** The independent shape congruence contains only required equations and their closure. *)
Inductive generated : positive -> positive -> Prop :=
  | generated_refl : forall a, In a nodes -> generated a a
  | generated_equation : forall a b, In (a, b) equations -> generated a b
  | generated_sym : forall a b, generated a b -> generated b a
  | generated_trans : forall a b c, generated a b -> generated b c -> generated a c
  | generated_reference : forall a b x y, generated a b ->
      In (a, x) references -> In (b, y) references -> generated x y.

Lemma seeds_generated a b : In (a, b) seeds -> generated a b.
Proof.
  unfold seeds; rewrite in_app_iff; intros [Heq|Hdiag].
  - apply generated_equation; exact Heq.
  - apply in_map_iff in Hdiag; destruct Hdiag as [x [Heq Hx]]; injection Heq as <- <-.
    apply generated_refl; exact Hx.
Qed.

Definition all_generated (current : st) : Prop := forall a b, present current a b -> generated a b.

Lemma consequences_generated current a b x y : PtsDelta.rows_wf E E current ->
  (forall p q, PtsDelta.holds E E current (p, q) -> generated p q) -> generated a b ->
  In (x, y) (consequences reference_index current (a, b)) -> generated x y.
Proof.
  intros Hrows Hgenerated Hab Hout; cbn [consequences fst snd In] in Hout.
  destruct Hout as [Heq|Hout]; [injection Heq as <- <-; now apply generated_sym|].
  apply in_app_or in Hout; destruct Hout as [Hout|Hout].
  - apply in_map_iff in Hout; destruct Hout as [c [Heq Hc]]; injection Heq as <- <-.
    eapply generated_trans; [exact Hab|apply Hgenerated].
    apply (children_member _ _ _ Hrows); exact Hc.
  - apply in_app_or in Hout; destruct Hout as [Hout|Hout].
    + apply in_map_iff in Hout; destruct Hout as [c [Heq Hc]]; injection Heq as <- <-.
      eapply generated_trans; [apply generated_sym, Hgenerated|exact Hab].
      apply (children_member _ _ _ Hrows); exact Hc.
    + apply in_prod_iff in Hout; destruct Hout as [Hx Hy].
      eapply generated_reference; [exact Hab| |];
        apply reference_member, (children_member _ _ _ reference_rows_wf); assumption.
Qed.

Lemma solved_generated : all_generated solved.
Proof.
  assert (Hinitial : all_generated initial).
  { intros a b Hin; apply PtsDelta.insert_all_holds in Hin; destruct Hin as [Hin|Hin].
    - apply seeds_generated; exact Hin.
    - exfalso; exact (PtsDelta.holds_empty E E _ Hin). }
  assert (Hadvance : forall current,
    invariant current /\ all_generated current -> invariant (advance current) /\
    all_generated (advance current)).
  { intros current [Hinv Hgenerated]; split; [apply advance_invariant; exact Hinv|].
    intros x y Hin; destruct (PtsDelta.pending current) as [|[a b] rest] eqn:Hqueue.
    - unfold advance in Hin; rewrite PtsDelta.advance_empty in Hin by exact Hqueue.
      apply Hgenerated; exact Hin.
    - apply (PtsDelta.advance_holds E E _ _ _ _ _ Hqueue) in Hin.
      destruct Hin as [Hnew|Hold]; [|apply Hgenerated; exact Hold].
      eapply consequences_generated;
        [exact (PtsDelta.current_wf E E _ _ (engine_valid current Hinv))|
          exact Hgenerated| |exact Hnew].
      apply Hgenerated, (PtsDelta.pending_spec E E _ _ (engine_valid current Hinv)).
      rewrite Hqueue; now left. }
  exact (proj2 (PtsDelta.run_invariant E E (consequences reference_index)
    (fun current => invariant current /\ all_generated current) Hadvance
    (Pos.of_succ_nat (length nodes * length nodes)) initial
    (conj initial_invariant Hinitial))).
Qed.

(** For supported nodes the forest is exactly the least required shape congruence. *)
Lemma forest_exact a b : In a nodes ->
  (UnionFind.equiv E forest a b <-> generated a b).
Proof.
  intro Ha; split.
  - intro Hab; destruct (forest_characterization _ _ Hab) as [->|Hpresent].
    + apply generated_refl; exact Ha.
    + apply solved_generated; exact Hpresent.
  - clear Ha; intro Hgenerated; induction Hgenerated as
      [x Hx|x y Heq|x y Hxy IH|x y z Hxy IHxy Hyz IHyz|
        x y p q Hxy IH Hxp Hyq].
    + reflexivity.
    + apply forest_equation; exact Heq.
    + unfold UnionFind.equiv in *; symmetry; exact IH.
    + unfold UnionFind.equiv in *; transitivity (fst (UnionFind.find E y forest));
        [exact IHxy|exact IHyz].
    + apply (forest_reference x y p q); [exact IH|exact Hxp|exact Hyq].
Qed.

End Closure.

End SteensUnify.

(** A unification result exposes the class forest and each value's pointee node. *)
Record steens_result (V : Type) : Type := SteensResult {
  classes : UnionFind.t positive;
  pointee : V -> positive
}.

Arguments SteensResult {V}.
Arguments classes {V}.
Arguments pointee {V}.

(** Values may alias when unification places their pointees in the same class. *)
Definition may_alias {V} (r : steens_result V) (x y : V) : Prop :=
  UnionFind.equiv positive_encoding (classes r) (pointee r x) (pointee r y).

Definition steens_value {V} (EV : encoding V) (x : V) : positive := xO (encode EV x).
Definition steens_site {T} (ET : encoding T) (t : T) : positive := xI (encode ET t).

Definition steens_operands {V T} (op : ptr_op V T) : list V :=
  match op with
  | PAlloc x _ | PEscape x => [x]
  | PCopy x y | PLoad x y | PStore x y => [x; y]
  end.

Definition steens_nodes {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) : list positive :=
  FinSet.elements (FinSet.of_list positive_encoding
    (map (steens_value EV) (flat_map steens_operands ops) ++
      map (steens_site ET) (site_universe ET ops))).

Definition steens_equations {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) : list (positive * positive) :=
  flat_map (fun op => match op with
    | PAlloc x t => [(steens_value EV x, steens_site ET t)]
    | PCopy x y => [(steens_value EV x, steens_value EV y)]
    | _ => []
    end) ops.

Definition steens_references {V T} (EV : encoding V) (ops : list (ptr_op V T)) :
    list (positive * positive) :=
  flat_map (fun op => match op with
    | PLoad x p => [(steens_value EV p, steens_value EV x)]
    | PStore p y => [(steens_value EV p, steens_value EV y)]
    | _ => []
    end) ops.

(** Unify direct equations and dereference shapes with an indexed binary-fuel worklist. *)
Definition steensgaard {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) : steens_result V :=
  SteensResult
    (SteensUnify.forest (steens_nodes EV ET ops) (steens_equations EV ET ops)
      (steens_references EV ops)) (steens_value EV).

Lemma steens_node_member {V T} (EV : encoding V) (ET : encoding T) ops p :
  In p (steens_nodes EV ET ops) <->
  In p (map (steens_value EV) (flat_map (@steens_operands V T) ops) ++
    map (steens_site ET) (site_universe ET ops)).
Proof.
  unfold steens_nodes; rewrite (FinSet.elements_spec positive_encoding);
    [apply FinSet.of_list_spec|apply FinSet.wf_fold_add, Map.wf_empty].
Qed.

Lemma steens_operand_node {V T} (EV : encoding V) (ET : encoding T) ops op x :
  In op ops -> In x (steens_operands op) -> In (steens_value EV x) (steens_nodes EV ET ops).
Proof.
  intros Hop Hx; apply steens_node_member, in_or_app; left; apply in_map, in_flat_map.
  exists op; auto.
Qed.

Lemma steens_equations_supported {V T} (EV : encoding V) (ET : encoding T) ops a b :
  In (a, b) (steens_equations EV ET ops) ->
  In a (steens_nodes EV ET ops) /\ In b (steens_nodes EV ET ops).
Proof.
  unfold steens_equations; rewrite in_flat_map.
  intros [op [Hop Hpair]]; destruct op; try contradiction;
    destruct Hpair as [Heq|[]]; injection Heq as <- <-; split.
  - eapply steens_operand_node; [exact Hop|now left].
  - apply steens_node_member, in_or_app; right; apply in_map; eapply allocation_site_in;
      exact Hop.
  - eapply steens_operand_node; [exact Hop|now left].
  - eapply steens_operand_node; [exact Hop|right; now left].
Qed.

Lemma steens_references_supported {V T} (EV : encoding V) (ET : encoding T) ops a b :
  In (a, b) (steens_references EV ops) ->
  In a (steens_nodes EV ET ops) /\ In b (steens_nodes EV ET ops).
Proof.
  unfold steens_references; rewrite in_flat_map.
  intros [op [Hop Hpair]]; destruct op; try contradiction;
    destruct Hpair as [Heq|[]]; injection Heq as <- <-; split;
    eapply steens_operand_node; [exact Hop|right; now left|exact Hop|now left|
      exact Hop|now left|exact Hop|right; now left].
Qed.

Lemma steens_alloc_equation {V T} (EV : encoding V) (ET : encoding T) ops x t :
  In (PAlloc x t) ops ->
  UnionFind.equiv positive_encoding (classes (steensgaard EV ET ops))
    (steens_value EV x) (steens_site ET t).
Proof.
  intro Hop; apply SteensUnify.forest_equation;
    [apply steens_equations_supported|apply steens_references_supported|].
  apply in_flat_map; exists (PAlloc x t); split; [exact Hop|now left].
Qed.

Lemma steens_copy_equation {V T} (EV : encoding V) (ET : encoding T) ops x y :
  In (PCopy x y) ops ->
  UnionFind.equiv positive_encoding (classes (steensgaard EV ET ops))
    (steens_value EV x) (steens_value EV y).
Proof.
  intro Hop; apply SteensUnify.forest_equation;
    [apply steens_equations_supported|apply steens_references_supported|].
  apply in_flat_map; exists (PCopy x y); split; [exact Hop|now left].
Qed.

Lemma steens_load_reference {V T} (EV : encoding V) (ops : list (ptr_op V T)) x p :
  In (PLoad x p) ops -> In (steens_value EV p, steens_value EV x) (steens_references EV ops).
Proof.
  intro Hop; apply in_flat_map; exists (PLoad x p); split; [exact Hop|now left].
Qed.

Lemma steens_store_reference {V T} (EV : encoding V) (ops : list (ptr_op V T)) p y :
  In (PStore p y) ops -> In (steens_value EV p, steens_value EV y) (steens_references EV ops).
Proof.
  intro Hop; apply in_flat_map; exists (PStore p y); split; [exact Hop|now left].
Qed.

(** A heap inclusion means every dereference of that source class reaches the included class. *)
Definition steens_fact {V T} (EV : encoding V) (ET : encoding T) ops
    (key : pts_key V T) (t : T) : Prop :=
  let forest := classes (steensgaard EV ET ops) in
  match key with
  | PVal x => UnionFind.equiv positive_encoding forest (steens_value EV x) (steens_site ET t)
  | PHeap u => forall a b, In (a, b) (steens_references EV ops) ->
      UnionFind.equiv positive_encoding forest a (steens_site ET u) ->
      UnionFind.equiv positive_encoding forest b (steens_site ET t)
  end.

Lemma steens_derivation {V T} (EV : encoding V) (ET : encoding T) ops e :
  AndersenDelta.derivable ops e ->
  match e with
  | (k, inl t) => steens_fact EV ET ops k t
  | (s, inr d) => forall t, steens_fact EV ET ops s t -> steens_fact EV ET ops d t
  end.
Proof.
  intro Hderivation; induction Hderivation as
    [x t Hop|x y Hop|x p u Hop Hpointer IHpointer|p y u Hop Hpointer IHpointer|
      s d t Hfact IHfact Hedge IHedge]; cbn [AndersenDelta.fact AndersenDelta.edge].
  - apply steens_alloc_equation; exact Hop.
  - intros t Hvalue; unfold steens_fact in *; unfold UnionFind.equiv in *.
    rewrite <- Hvalue; apply steens_copy_equation; exact Hop.
  - intros t Hheap; apply (Hheap (steens_value EV p) (steens_value EV x));
      [apply steens_load_reference; exact Hop|exact IHpointer].
  - intros t Hvalue a b Href Hab.
    assert (Hsame : UnionFind.equiv positive_encoding (classes (steensgaard EV ET ops))
      a (steens_value EV p)).
    { unfold steens_fact, UnionFind.equiv in *; congruence. }
    pose proof (SteensUnify.forest_reference (steens_nodes EV ET ops)
      (steens_equations EV ET ops) (steens_references EV ops)
      (steens_equations_supported EV ET ops) (steens_references_supported EV ET ops)
      a (steens_value EV p) b (steens_value EV y) Hsame Href
      (steens_store_reference EV ops p y Hop)) as Htarget.
    unfold UnionFind.equiv.
    transitivity (fst (UnionFind.find positive_encoding (steens_value EV y)
      (classes (steensgaard EV ET ops)))); [exact Htarget|exact Hvalue].
  - apply IHedge; exact IHfact.
Qed.

Lemma steens_delta_fact {V T} (EV : encoding V) (ET : encoding T) ops key t :
  fmem ET t (andersen_delta EV ET ops key) = true -> steens_fact EV ET ops key t.
Proof.
  intro Hmem; apply (steens_derivation EV ET ops (AndersenDelta.fact key t)).
  apply (AndersenDelta.events_derivable EV ET ops _ (AndersenDelta.solved_invariant EV ET ops)).
  apply AndersenDelta.answer_mem; exact Hmem.
Qed.

(** Any two values sharing a site in the least inclusion solution have unified pointees. *)
Theorem steensgaard_coarser {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) (sigma : pts_key V T -> pts_set ET ops) (x y : V) (t : T) :
  least_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma ->
  fmem ET t (sigma (PVal x)) = true -> fmem ET t (sigma (PVal y)) = true ->
  may_alias (steensgaard EV ET ops) x y.
Proof.
  intros [_ Hleast] Hx Hy.
  pose proof (proj1 (andersen_delta_least EV ET ops)) as Hpost.
  pose proof (steens_delta_fact EV ET ops (PVal x) t
    (proj1 (pts_le ET ops _ _) (Hleast _ Hpost (PVal x)) t Hx)) as Hxeq.
  pose proof (steens_delta_fact EV ET ops (PVal y) t
    (proj1 (pts_le ET ops _ _) (Hleast _ Hpost (PVal y)) t Hy)) as Hyeq.
  unfold steens_fact, may_alias, UnionFind.equiv in *; cbn [steensgaard pointee] in *.
  congruence.
Qed.

(** Concrete values pointing into the same site belong to one unification class. *)
Theorem steensgaard_sound {S O V C L T} (m : semantics S O) (pv : ptr_view S V C L T)
    (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T)) :
  ptr_view_laws m pv ops ->
  forall s x y t, reachable_state m s -> pts_of pv s x = Some t -> pts_of pv s y = Some t ->
    may_alias (steensgaard EV ET ops) x y.
Proof.
  intros Hlaws s x y t Hreach Hx Hy.
  destruct (andersen_delta_sound m pv EV ET ops Hlaws s Hreach) as [Hvalues Hheap].
  eapply steensgaard_coarser; [apply andersen_delta_least|apply Hvalues; exact Hx|
    apply Hvalues; exact Hy].
Qed.

(** * Least escape closure *)

Definition escape_roots {V T} (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) : list T :=
  flat_map (fun op => match op with
    | PEscape x => FinSet.elements (proj1_sig (sigma (PVal x)))
    | _ => []
    end) ops.

(** Heap facts are direct adjacency buckets; graph preparation indexes them once. *)
Definition escape_graph {V T} (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) : Graph.t T (T * T) :=
  Graph.Make (escape_roots ET ops sigma) (site_universe ET ops)
    (fun t => map (fun u => (t, u)) (FinSet.elements (proj1_sig (sigma (PHeap t))))) fst snd.

Lemma escape_root_member {V T} (ET : encoding T) ops sigma t :
  In t (escape_roots ET ops sigma) <->
  exists x, In (PEscape x) ops /\ fmem ET t (sigma (@PVal V T x)) = true.
Proof.
  unfold escape_roots; rewrite in_flat_map; split.
  - intros [op [Hop Hin]]; destruct op; try contradiction.
    exists x; split; [exact Hop|apply pts_members; exact Hin].
  - intros [x [Hop Hmem]]; exists (PEscape x); split; [exact Hop|].
    apply pts_members; exact Hmem.
Qed.

Lemma escape_graph_wf {V T} (ET : encoding T) ops sigma :
  graph_wf (@escape_graph V T ET ops sigma).
Proof.
  constructor.
  - apply site_universe_nodup.
  - intros t Hin; apply escape_root_member in Hin; destruct Hin as [x [Hop Hmem]].
    exact (proj2 (proj2_sig (sigma (PVal x))) t Hmem).
  - intros t [a b] Hin; apply in_map_iff in Hin; destruct Hin as [u [Heq Hin]].
    injection Heq as <- <-; reflexivity.
  - intros t [a b] Ht Hin; apply in_map_iff in Hin; destruct Hin as [u [Heq Hin]].
    injection Heq as <- <-; apply (proj2 (proj2_sig (sigma (PHeap t)))), pts_members; exact Hin.
Qed.

(** Search computes precisely the sites reachable from escape roots through heap inclusions. *)
Definition escaped_sites {V T} (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) : FinSet.t T :=
  let graph := escape_graph ET ops sigma in
  visited (dfs (prepare ET graph) FinSet.empty (Graph.entries graph)).

Lemma escaped_sites_member {V T} (ET : encoding T) ops sigma t :
  FinSet.mem ET t (@escaped_sites V T ET ops sigma) = true <->
  reachable (escape_graph ET ops sigma) t.
Proof.
  apply reachable_dfs, prepare_ready; [apply escape_graph_wf|].
  intro x; cbn [escape_graph Graph.out].
  pose proof (FinSet.elements_nodup ET (proj1_sig (sigma (PHeap x)))
    (proj1 (proj2_sig (sigma (PHeap x))))) as Hnodup.
  induction Hnodup as [|a xs Hfresh Hnodup IH]; cbn [map]; [constructor|].
  constructor; [|exact IH].
  intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Heq Hy]].
  injection Heq as ->; exact (Hfresh Hy).
Qed.

(** Every explicit escape contributes all sites of its value fact. *)
Lemma escaped_sites_root {V T} (ET : encoding T) ops sigma x t :
  In (@PEscape V T x) ops -> fmem ET t (sigma (PVal x)) = true ->
  FinSet.mem ET t (escaped_sites ET ops sigma) = true.
Proof.
  intros Hop Hmem; apply escaped_sites_member, reachable_entry, escape_root_member.
  exists x; auto.
Qed.

(** Escaped sites are closed under every heap inclusion of the supplied assignment. *)
Lemma escaped_sites_step {V T} (ET : encoding T) ops sigma t u :
  FinSet.mem ET t (@escaped_sites V T ET ops sigma) = true ->
  fmem ET u (sigma (PHeap t)) = true ->
  FinSet.mem ET u (escaped_sites ET ops sigma) = true.
Proof.
  intros Hescape Hheap; apply escaped_sites_member in Hescape; apply escaped_sites_member.
  eapply (@reachable_step T (T * T) (escape_graph ET ops sigma) (t, u));
    [exact Hescape|].
  apply in_map_iff; exists u; split; [reflexivity|apply pts_members; exact Hheap].
Qed.

(** Every closed predicate containing the roots contains the computed escaped set. *)
Lemma escaped_sites_least {V T} (ET : encoding T) ops sigma (contains : T -> Prop) :
  (forall x t, In (@PEscape V T x) ops -> fmem ET t (sigma (PVal x)) = true -> contains t) ->
  (forall t u, contains t -> fmem ET u (sigma (PHeap t)) = true -> contains u) ->
  forall t, FinSet.mem ET t (escaped_sites ET ops sigma) = true -> contains t.
Proof.
  intros Hroot Hclosed t Hmem; apply escaped_sites_member in Hmem.
  induction Hmem as [t Hin|[a b] Hreach IH Hedge].
  - apply escape_root_member in Hin; destruct Hin as [x [Hop Hfact]]; eapply Hroot; eassumption.
  - apply in_map_iff in Hedge; destruct Hedge as [u [Heq Hu]].
    cbn [escape_graph Graph.source Graph.target fst snd] in *.
    injection Heq as <-; eapply Hclosed; [exact IH|apply pts_members; exact Hu].
Qed.

(** Actual escapes and their reachable stored pointers belong to the least escape closure. *)
Theorem escaped_closed {S O V C L T} (m : semantics S O) (pv : ptr_view S V C L T)
    (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) :
  ptr_view_laws m pv ops ->
  post_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma ->
  forall s x t t', reachable_state m s -> In (PEscape x) (pop pv s) -> pts_of pv s x = Some t ->
    FinSet.mem ET t (escaped_sites ET ops sigma) = true /\
    (heap_pts pv s t t' -> FinSet.mem ET t' (escaped_sites ET ops sigma) = true).
Proof.
  intros Hlaws Hpost s x t t' Hreach Hescape Hpts.
  destruct (andersen_sound m pv EV ET ops sigma Hlaws Hpost s Hreach) as [Hval Hheap].
  assert (Hroot : FinSet.mem ET t (escaped_sites ET ops sigma) = true).
  { eapply escaped_sites_root; [eapply pop_listed; eassumption|apply Hval; exact Hpts]. }
  split; [exact Hroot|].
  intro Hstored; eapply escaped_sites_step; [exact Hroot|apply Hheap; exact Hstored].
Qed.


(** Every relational value and heap observation belongs to any post-solution. *)
Theorem relational_andersen_sound {S O V T} (m : semantics S O)
    (rv : relational_ptr_view S V T) (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) (sigma : pts_key V T -> pts_set ET ops) :
  relational_ptr_laws m rv ops ->
  post_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma ->
  forall s, reachable_state m s ->
    (forall x t, rel_value rv s x t -> fmem ET t (sigma (PVal x)) = true) /\
    (forall t0 t, rel_heap rv s t0 t -> fmem ET t (sigma (PHeap t0)) = true).
Proof.
  intros Hlaws Hpost s [s0 [tr [Hinitial Hrun]]].
  pose proof (pts_post_closed EV ET ops sigma Hpost) as Hclosed.
  assert (Hstart : reachable_state m s0).
  { exists s0, []; split; [exact Hinitial|constructor]. }
  assert (Hfacts :
    (forall x t, rel_value rv s0 x t -> fmem ET t (sigma (PVal x)) = true) /\
    (forall u t, rel_heap rv s0 u t -> fmem ET t (sigma (PHeap u)) = true)).
  { split.
    - intros x t Hvalue; apply (pts_alloc_closed Hclosed).
      eapply rel_value_initial; eassumption.
    - intros u t Hheap; exfalso; eapply rel_heap_initial; eassumption. }
  clear Hinitial; revert Hstart Hfacts.
  induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intros Hreach [Hval Hheap].
  - auto.
  - apply IH; [eapply reachable_state_step; eassumption|].
    eapply relational_pts_step; eassumption.
Qed.

(** * Zero-initialized bytes *)

(** The finite universe retains the actual footprints of all graph edges. *)
Definition write_universe {S O N E T} (EF : encoding (footprint T))
    (gv : graph_view S O N E) (fp : E -> list (footprint T)) : list (footprint T) :=
  FinSet.elements (FinSet.of_list EF (flat_map fp (edges_of (cfg gv)))).

(** Written facts are finite sets of the graph's footprints. *)
Definition written_set {S O N E T} (EF : encoding (footprint T))
    (gv : graph_view S O N E) (fp : E -> list (footprint T)) : Type :=
  finite_set EF (write_universe EF gv fp).

(** Each step accumulates its may-write footprints, including frees and callee writes. *)
Definition zero_written_system {S O N E T} (EF : encoding (footprint T))
    (gv : graph_view S O N E) (fp : E -> list (footprint T)) :
    System.t N (dense_constraint N E) (written_set EF gv fp) :=
  forward_system (cfg gv)
    (fun _ => finite_clamp EF (write_universe EF gv fp) FinSet.empty)
    (fun e a => finite_clamp EF (write_universe EF gv fp)
      (FinSet.union EF (proj1_sig a) (FinSet.of_list EF (fp e)))).

(** Zero laws transport the same pointer's retained address and preserve unwritten zero bytes. *)
Record zero_laws {S O N E V C L T} (m : semantics S O) (gv : graph_view S O N E)
    (pv : ptr_view S V C L T) (fp : E -> list (footprint T)) : Prop := {
  z_view : graph_view_laws m gv;
  z_no_stays : forall s l s', ~ stays gv s l s';
  z_init : forall s c l0 t n, initial m s -> loc_of (pmem pv) s c = Some l0 ->
    loc_site (pmem pv) s l0 = Some t -> pbyte pv s c = Some n -> n = 0;
  z_fresh : forall s l s' e c l0 t n, reachable_state m s -> step m s l s' ->
    taken gv s l s' e -> loc_of (pmem pv) s c = None ->
    loc_of (pmem pv) s' c = Some l0 -> loc_site (pmem pv) s' l0 = Some t ->
    pbyte pv s' c = Some n -> n = 0;
  z_address : forall s l s' e c l0 l1 t,
    reachable_state m s -> step m s l s' -> taken gv s l s' e ->
    loc_of (pmem pv) s c = Some l0 -> loc_of (pmem pv) s' c = Some l1 ->
    loc_site (pmem pv) s' l1 = Some t ->
    loc_site (pmem pv) s l0 = Some t /\
    loc_offset (pmem pv) s c = loc_offset (pmem pv) s' c;
  z_kept : forall s l s' e c l0 t, reachable_state m s -> step m s l s' ->
    taken gv s l s' e -> loc_of (pmem pv) s c = Some l0 ->
    loc_site (pmem pv) s l0 = Some t ->
    ~ covered (fp e) t (loc_offset (pmem pv) s c) 1 ->
    (forall n, pbyte pv s c = Some n -> n = 0) ->
    forall n, pbyte pv s' c = Some n -> n = 0
}.

Arguments z_view {S O N E V C L T m gv pv fp}.
Arguments z_no_stays {S O N E V C L T m gv pv fp}.
Arguments z_init {S O N E V C L T m gv pv fp}.
Arguments z_fresh {S O N E V C L T m gv pv fp}.
Arguments z_address {S O N E V C L T m gv pv fp}.
Arguments z_kept {S O N E V C L T m gv pv fp}.

Lemma written_edge_in {S O N E T} (EF : encoding (footprint T))
    (gv : graph_view S O N E) fp e f :
  In e (edges_of (cfg gv)) -> In f (fp e) -> In f (write_universe EF gv fp).
Proof.
  intros He Hf; apply (FinSet.elements_spec EF); [apply FinSet.wf_fold_add, Map.wf_empty|].
  apply FinSet.of_list_spec, in_flat_map; exists e; auto.
Qed.

Lemma written_transfer_member {S O N E T} (EF : encoding (footprint T))
    (gv : graph_view S O N E) fp (a : written_set EF gv fp) e f :
  In e (edges_of (cfg gv)) ->
  In f (FinSet.elements (proj1_sig a)) \/ In f (fp e) ->
  In f (FinSet.elements (proj1_sig (finite_clamp EF (write_universe EF gv fp)
    (FinSet.union EF (proj1_sig a) (FinSet.of_list EF (fp e)))))).
Proof.
  intros He Hf; apply (FinSet.elements_spec EF); [apply FinSet.wf_fold_add, Map.wf_empty|].
  assert (Hin : In f (write_universe EF gv fp)).
  { destruct Hf as [Hf|Hf].
    - apply (proj2 (proj2_sig a)); apply (FinSet.elements_spec EF);
        [exact (proj1 (proj2_sig a))|exact Hf].
    - eapply written_edge_in; eassumption. }
  change (FinSet.mem EF f (FinSet.of_list EF
    (filter (fun k => FinSet.mem EF k
      (FinSet.union EF (proj1_sig a) (FinSet.of_list EF (fp e))))
      (write_universe EF gv fp))) = true).
  apply FinSet.of_list_spec, filter_In; split; [exact Hin|].
  apply FinSet.mem_union; destruct Hf as [Hf|Hf].
    + left; apply (FinSet.elements_spec EF); [exact (proj1 (proj2_sig a))|exact Hf].
    + right; apply FinSet.of_list_spec; exact Hf.
Qed.

Lemma covered_inclusion {T} (F G : list (footprint T)) t o w :
  incl F G -> covered F t o w -> covered G t o w.
Proof.
  intros Hin Hcovered k Hk; destruct (Hcovered k Hk) as [f [Hf [Ht Hbounds]]].
  exists f; split; [apply Hin; exact Hf|auto].
Qed.

(** A byte outside the accumulated footprints reads zero whenever it is readable. *)
Theorem zero_written_sound {S O N E V C L T} (m : semantics S O)
    (EF : encoding (footprint T)) (gv : graph_view S O N E)
    (pv : ptr_view S V C L T) (fp : E -> list (footprint T))
    (sigma : N -> written_set EF gv fp) :
  zero_laws m gv pv fp ->
  post_solution (finite_powerset_lattice EF (write_universe EF gv fp))
    (zero_written_system EF gv fp) sigma ->
  forall s c l0 t n, reachable_state m s -> loc_of (pmem pv) s c = Some l0 ->
    loc_site (pmem pv) s l0 = Some t ->
    ~ covered (FinSet.elements (proj1_sig (sigma (point gv s))))
      t (loc_offset (pmem pv) s c) 1 ->
    pbyte pv s c = Some n -> n = 0.
Proof.
  intros Hlaws Hpost.
  pose (G := {| gamma := fun (a : written_set EF gv fp) s =>
    forall c l0 t n, loc_of (pmem pv) s c = Some l0 ->
      loc_site (pmem pv) s l0 = Some t ->
      ~ covered (FinSet.elements (proj1_sig a)) t (loc_offset (pmem pv) s c) 1 ->
      pbyte pv s c = Some n -> n = 0 |}).
  assert (HG : concretisation_laws
    (finite_powerset_lattice EF (write_universe EF gv fp)) G).
  { constructor; intros a b s Hab Ha c l0 t n Hloc Hsite Houtside Hbyte.
    apply (Ha c l0 t n Hloc Hsite); [|exact Hbyte].
    intro Hcovered; apply Houtside; eapply covered_inclusion; [|exact Hcovered].
    intros f Hf; apply (FinSet.elements_spec EF); [exact (proj1 (proj2_sig b))|].
    apply (set_member_subset EF _ _ Hab).
    apply (FinSet.elements_spec EF); [exact (proj1 (proj2_sig a))|exact Hf]. }
  assert (Hfacts : forall s, reachable_state m s -> gamma G (sigma (point gv s)) s).
  { eapply (forward_invariant_sound m gv
    (finite_powerset_lattice EF (write_universe EF gv fp)) (fun _ => G)
    (fun _ => finite_clamp EF (write_universe EF gv fp) FinSet.empty)
    (fun e a => finite_clamp EF (write_universe EF gv fp)
      (FinSet.union EF (proj1_sig a) (FinSet.of_list EF (fp e)))) sigma).
  - exact (z_view Hlaws).
  - exact HG.
  - intros s Hinitial c l0 t n Hloc Hsite Houtside Hbyte.
    eapply z_init; eassumption.
  - intros e s l s' Hreach Hstep Htaken Hfact c l1 t n Hloc Hsite Houtside Hbyte.
    destruct (view_taken_edge m gv s l s' e (z_view Hlaws) Hreach Hstep Htaken)
      as [He Hends].
    destruct (loc_of (pmem pv) s c) as [l0|] eqn:Hbefore.
    + destruct (z_address Hlaws s l s' e c l0 l1 t Hreach Hstep Htaken
        Hbefore Hloc Hsite) as [Hsite0 Hoffset].
      eapply (z_kept Hlaws s l s' e c l0 t Hreach Hstep Htaken Hbefore Hsite0).
      * intro Hcovered; apply Houtside; rewrite <- Hoffset.
        eapply covered_inclusion; [|exact Hcovered].
        intros f Hf; apply written_transfer_member; [exact He|now right].
      * intros k Hread; apply (Hfact c l0 t k Hbefore Hsite0); [|exact Hread].
        intro Hcovered; apply Houtside; rewrite <- Hoffset.
        eapply covered_inclusion; [|exact Hcovered].
        intros f Hf; apply written_transfer_member; [exact He|now left].
      * exact Hbyte.
    + eapply z_fresh; eassumption.
  - intros s l s' Hreach Hstep Hstay Hfact; exfalso.
    exact (z_no_stays Hlaws s l s' Hstay).
  - exact Hpost. }
  intros s c l0 t n Hreach Hloc Hsite Houtside Hbyte.
  exact (Hfacts s Hreach c l0 t n Hloc Hsite Houtside Hbyte).
Qed.
