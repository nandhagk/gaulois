(** * Strongly connected components

    An explicit Tarjan frame stack computes components and indexes their members.
    For example, the cycle 1 to 2 to 1 is emitted as one component.
    Builds on: GraphCore, GraphPrepare, GraphDfs and Collections tries, maps and finite sets. *)

From Stdlib Require Import List Bool PArith Arith Lia Permutation.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs.
Import List.ListNotations.

(** A topological order lists every graph node once and places each source before its target. *)
Definition topological_order {V E} (g : Graph.t V E) (l : list V) : Prop :=
  NoDup l /\ (forall v, In v l <-> In v (Graph.nodes g)) /\
  forall e, In (Graph.source g e) (Graph.nodes g) ->
    In e (Graph.out g (Graph.source g e)) ->
    before l (Graph.source g e) (Graph.target g e).

(** Components and their positive identifiers are listed in emission order. *)
Record scc_result (V : Type) : Type := SccResult {
  components : list (list V);
  component_ids : list positive;
  component_at : Trie.t (list V);
  comp_of : Map.t V positive
}.
Arguments SccResult {V}.
Arguments components {V}.
Arguments component_ids {V}.
Arguments component_at {V}.
Arguments comp_of {V}.

(** A frame retains the open vertex and its unprocessed successor edges. *)
Record tarjan_frame (V E : Type) : Type := TarjanFrame {
  frame_node : V;
  frame_edges : list E
}.
Arguments TarjanFrame {V E}.
Arguments frame_node {V E}.
Arguments frame_edges {V E}.

(** The machine keeps open frames, discovery numbers, lowlinks and the pending stack. *)
Record tarjan_state (V E : Type) : Type := TarjanState {
  frames : list (tarjan_frame V E);
  disc : Map.t V positive;
  low : Map.t V positive;
  pending : list V;
  clock : positive;
  emitted : scc_result V
}.
Arguments TarjanState {V E}.
Arguments frames {V E}.
Arguments disc {V E}.
Arguments low {V E}.
Arguments pending {V E}.
Arguments clock {V E}.
Arguments emitted {V E}.

(** Every open frame belongs to the graph and retains only edges of its own adjacency. *)
Definition tarjan_control {V E} (g : Graph.t V E) (st : tarjan_state V E) : Prop :=
  forall f, In f (frames st) ->
    In (frame_node f) (Graph.nodes g) /\ incl (frame_edges f) (Graph.out g (frame_node f)).

(** * Machine transitions *)

(** Before the first discovery, both stacks and all indexes are empty. *)
Definition tarjan_initial {V E} : tarjan_state V E :=
  TarjanState [] Map.empty Map.empty [] 1%positive
    (SccResult [] [] Trie.empty Map.empty).

(** The most recently allocated identifier determines the next identifier in constant time. *)
Definition tarjan_next_id {V} (r : scc_result V) : positive :=
  match component_ids r with
  | [] => 1%positive
  | i :: _ => Pos.succ i
  end.

(** Discovering a fresh vertex pushes its frame and gives it its initial lowlink. *)
Definition tarjan_discover {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (v : V) (st : tarjan_state V E) : tarjan_state V E :=
  TarjanState (TarjanFrame v (succ_edges p v) :: frames st)
    (Map.set EV v (clock st) (disc st)) (Map.set EV v (clock st) (low st))
    (v :: pending st) (Pos.succ (clock st)) (emitted st).

(** Lower a pending vertex's lowlink without changing the other state fields. *)
Definition tarjan_lower {V E} (EV : encoding V) (v : V) (n : positive)
    (st : tarjan_state V E) : tarjan_state V E :=
  match Map.get EV v (low st) with
  | None => st
  | Some old =>
    TarjanState (frames st) (disc st) (Map.set EV v (Pos.min old n) (low st))
      (pending st) (clock st) (emitted st)
  end.

(** Pop through the component root, removing its lowlinks and indexing its members once. *)
Fixpoint tarjan_pop {V} (EV : encoding V) (root : V) (i : positive) (xs : list V)
    (links : Map.t V positive) (owners : Map.t V positive)
    : list V * list V * Map.t V positive * Map.t V positive :=
  match xs with
  | [] => ([], [], links, owners)
  | v :: rest =>
    let links' := Map.remove EV v links in
    let owners' := Map.set EV v i owners in
    if Pos.eqb (encode EV v) (encode EV root)
    then ([v], rest, links', owners')
    else
      let '(members, tail, links'', owners'') :=
        tarjan_pop EV root i rest links' owners' in
      (v :: members, tail, links'', owners'')
  end.

(** Emit one component; the machine accumulates lists backwards and reverses them only at exit. *)
Definition tarjan_emit {V E} (EV : encoding V) (root : V) (st : tarjan_state V E)
    : tarjan_state V E :=
  let r := emitted st in
  let i := tarjan_next_id r in
  let '(members, tail, links, owners) :=
    tarjan_pop EV root i (pending st) (low st) (comp_of r) in
  TarjanState (frames st) (disc st) links tail (clock st)
    (SccResult (members :: components r) (i :: component_ids r)
      (Trie.set i members (component_at r)) owners).

(** Closing a frame emits a root or propagates the child's lowlink to its open parent. *)
Definition tarjan_close {V E} (EV : encoding V) (v : V) (rest : list (tarjan_frame V E))
    (st : tarjan_state V E) : tarjan_state V E :=
  let closed := TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st) in
  match Map.get EV v (low st), Map.get EV v (disc st) with
  | Some l, Some d =>
    if Pos.eqb l d then tarjan_emit EV v closed
    else
      match rest with
      | [] => closed
      | parent :: _ => tarjan_lower EV (frame_node parent) l closed
      end
  | _, _ => closed
  end.

(** One step closes a frame or consumes an edge, possibly discovering a fresh target. *)
Definition tarjan_step {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (st : tarjan_state V E)
    : tarjan_state V E :=
  match frames st with
  | [] => st
  | TarjanFrame v [] :: rest => tarjan_close EV v rest st
  | TarjanFrame v (e :: es) :: rest =>
    let advanced := TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
      (pending st) (clock st) (emitted st) in
    let w := Graph.target g e in
    if FinSet.mem EV w region then
      match Map.get EV w (disc st) with
      | None => tarjan_discover p w advanced
      | Some d =>
        match Map.get EV w (low st) with
        | None => advanced
        | Some _ => tarjan_lower EV v d advanced
        end
      end
    else advanced
  end.

(** Binary fuel counts transitions and an empty frame stack stops without spending fuel. *)
Fixpoint tarjan_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (n : positive) (st : tarjan_state V E)
    : tarjan_state V E :=
  match frames st with
  | [] => st
  | _ :: _ =>
    match n with
    | xH => tarjan_step p region st
    | xO k => tarjan_run p region k (tarjan_run p region k st)
    | xI k => tarjan_step p region (tarjan_run p region k (tarjan_run p region k st))
    end
  end.

(** Already discovered roots are skipped, including repeated entries in the region list. *)
Definition tarjan_root {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (st : tarjan_state V E) (v : V)
    : tarjan_state V E :=
  match Map.get EV v (disc st) with
  | Some _ => st
  | None => tarjan_run p region (fuel p) (tarjan_discover p v st)
  end.

(** Return the internal result in increasing component identifier and emission order. *)
Definition tarjan_result {V E} (st : tarjan_state V E) : scc_result V :=
  let r := emitted st in
  SccResult (rev (components r)) (rev (component_ids r)) (component_at r) (comp_of r).

(** Iterative Tarjan visits region roots in order and ignores edges leaving the indexed region. *)
Definition scc_within {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (region : list V) : scc_result V :=
  let keep := FinSet.of_list EV region in
  tarjan_result (fold_left (tarjan_root p keep) region tarjan_initial).

(** Whole-graph SCCs include unreachable nodes as well as reachable nodes. *)
Definition scc {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    : scc_result V := scc_within p (Graph.nodes g).

(** * Condensation indexes *)

(** Missing component bindings have the harmless default identifier one. *)
Definition scc_owner {V} (EV : encoding V) (r : scc_result V) (v : V) : positive :=
  match Map.get EV v (comp_of r) with
  | Some i => i
  | None => 1%positive
  end.

(** Add an original edge to its component's adjacency list only when it crosses components. *)
Definition condensation_edge {V E} (EV : encoding V) (g : Graph.t V E)
    (r : scc_result V) (v : V) (e : E) (m : Trie.t (list E)) : Trie.t (list E) :=
  match Map.get EV v (comp_of r), Map.get EV (Graph.target g e) (comp_of r) with
  | Some i, Some j =>
    if Pos.eqb i j then m
    else Trie.set i (e :: match Trie.get i m with Some es => es | None => [] end) m
  | _, _ => m
  end.

(** The condensation adjacency trie is built in one pass over indexed original edges. *)
Definition condensation_index {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : scc_result V) : Trie.t (list E) :=
  fold_right (fun v m => fold_right (condensation_edge EV g r v) m (succ_edges p v))
    Trie.empty (Graph.nodes g).

(** Map entries to components and retain each identifier's first occurrence. *)
Fixpoint condensation_entries {V} (EV : encoding V) (r : scc_result V)
    (roots : list V) (seen : FinSet.t positive) : list positive :=
  match roots with
  | [] => []
  | v :: rest =>
    match Map.get EV v (comp_of r) with
    | None => condensation_entries EV r rest seen
    | Some i =>
      if FinSet.mem positive_encoding i seen
      then condensation_entries EV r rest seen
      else i :: condensation_entries EV r rest (FinSet.add positive_encoding i seen)
    end
  end.

(** The condensation retains original cross-component edges, with component endpoints. *)
Definition condensation {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (r : scc_result V) : Graph.t positive E :=
  let m := condensation_index p r in
  {| Graph.entries := condensation_entries EV r (Graph.entries g) FinSet.empty;
     Graph.nodes := rev (component_ids r);
     Graph.out := fun i => match Trie.get i m with Some es => es | None => [] end;
     Graph.source := fun e => scc_owner EV r (Graph.source g e);
     Graph.target := fun e => scc_owner EV r (Graph.target g e) |}.

(** * Stack splitting and index agreement *)

Lemma tarjan_pop_split {V} (EV : encoding V) root i xs links owners :
  let '(members, tail, _, _) := tarjan_pop EV root i xs links owners in
  xs = members ++ tail /\ (In root xs -> In root members).
Proof.
  revert links owners; induction xs as [|v xs IH]; intros links owners.
  - cbn; split; [reflexivity|contradiction].
  - cbn [tarjan_pop].
    destruct (Pos.eqb (encode EV v) (encode EV root)) eqn:Heq.
    + apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst v.
      cbn; split; [reflexivity|intros _; left; reflexivity].
    + specialize (IH (Map.remove EV v links) (Map.set EV v i owners)).
      destruct (tarjan_pop EV root i xs (Map.remove EV v links)
        (Map.set EV v i owners)) as [[[members tail] links'] owners'].
      cbn in *; destruct IH as [Hsplit Hroot].
      split; [now rewrite Hsplit|].
      intros [Hroot'|Hin].
      * subst v; rewrite Pos.eqb_refl in Heq; discriminate.
      * right; apply Hroot; exact Hin.
Qed.

Lemma tarjan_pop_nonempty {V} (EV : encoding V) root i xs links owners :
  In root xs ->
  let '(members, _, _, _) := tarjan_pop EV root i xs links owners in members <> [].
Proof.
  intro Hroot; pose proof (tarjan_pop_split EV root i xs links owners) as Hsplit.
  destruct (tarjan_pop EV root i xs links owners) as [[[members tail] links'] owners'].
  cbn in *; destruct Hsplit as [_ Hmembers].
  specialize (Hmembers Hroot); intro Heq; subst members; contradiction.
Qed.

Lemma tarjan_pop_links {V} (EV : encoding V) root i xs links owners x :
  let '(members, _, links', _) := tarjan_pop EV root i xs links owners in
  Map.get EV x links' =
    if existsb (fun v => Pos.eqb (encode EV x) (encode EV v)) members
    then None else Map.get EV x links.
Proof.
  revert links owners; induction xs as [|v xs IH]; intros links owners.
  - reflexivity.
  - cbn [tarjan_pop].
    destruct (Pos.eqb (encode EV v) (encode EV root)) eqn:Hroot.
    + cbn; destruct (Pos.eqb (encode EV x) (encode EV v)) eqn:Heq.
      * apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst x.
        apply Map.get_remove_same.
      * apply Pos.eqb_neq in Heq; apply Map.get_remove_other.
        intro H; subst x; contradiction.
    + specialize (IH (Map.remove EV v links) (Map.set EV v i owners)).
      destruct (tarjan_pop EV root i xs (Map.remove EV v links)
        (Map.set EV v i owners)) as [[[members tail] links'] owners'].
      cbn in *; rewrite IH.
      destruct (Pos.eqb (encode EV x) (encode EV v)) eqn:Heq.
      * apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst x.
        rewrite Map.get_remove_same; destruct (existsb _ members); reflexivity.
      * cbn; destruct (existsb _ members); [reflexivity|].
        apply Map.get_remove_other; intro H; subst x; rewrite Pos.eqb_refl in Heq;
          discriminate.
Qed.

Lemma tarjan_pop_owners {V} (EV : encoding V) root i xs links owners x :
  let '(members, _, _, owners') := tarjan_pop EV root i xs links owners in
  Map.get EV x owners' =
    if existsb (fun v => Pos.eqb (encode EV x) (encode EV v)) members
    then Some i else Map.get EV x owners.
Proof.
  revert links owners; induction xs as [|v xs IH]; intros links owners.
  - reflexivity.
  - cbn [tarjan_pop].
    destruct (Pos.eqb (encode EV v) (encode EV root)) eqn:Hroot.
    + cbn; destruct (Pos.eqb (encode EV x) (encode EV v)) eqn:Heq.
      * apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst x.
        apply Map.get_set_same.
      * apply Pos.eqb_neq in Heq; apply Map.get_set_other.
        intro H; subst x; contradiction.
    + specialize (IH (Map.remove EV v links) (Map.set EV v i owners)).
      destruct (tarjan_pop EV root i xs (Map.remove EV v links)
        (Map.set EV v i owners)) as [[[members tail] links'] owners'].
      cbn in *; rewrite IH.
      destruct (Pos.eqb (encode EV x) (encode EV v)) eqn:Heq.
      * apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst x.
        rewrite Map.get_set_same; destruct (existsb _ members); reflexivity.
      * cbn; destruct (existsb _ members); [reflexivity|].
        apply Map.get_set_other; intro H; subst x; rewrite Pos.eqb_refl in Heq;
          discriminate.
Qed.

Lemma tarjan_run_empty {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region n (st : tarjan_state V E) :
  frames st = [] -> tarjan_run p region n st = st.
Proof.
  intro Hempty; destruct n; cbn [tarjan_run]; rewrite Hempty; reflexivity.
Qed.

Lemma tarjan_iter_empty {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region n (st : tarjan_state V E) :
  frames st = [] -> Pos.iter (tarjan_step p region) st n = st.
Proof.
  intro Hempty; induction n using Pos.peano_ind.
  - change (tarjan_step p region st = st); unfold tarjan_step; now rewrite Hempty.
  - rewrite Pos.iter_succ, IHn; unfold tarjan_step; now rewrite Hempty.
Qed.

Lemma tarjan_run_agrees {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region n (st : tarjan_state V E) :
  tarjan_run p region n st = Pos.iter (tarjan_step p region) st n.
Proof.
  revert st; induction n as [n IH|n IH|]; intro st;
    destruct (frames st) as [|f rest] eqn:Hframes.
  - rewrite tarjan_run_empty by exact Hframes; symmetry; apply tarjan_iter_empty;
      exact Hframes.
  - cbn [tarjan_run]; rewrite Hframes, !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO n)).
  - rewrite tarjan_run_empty by exact Hframes; symmetry; apply tarjan_iter_empty;
      exact Hframes.
  - cbn [tarjan_run]; rewrite Hframes, !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - rewrite tarjan_run_empty by exact Hframes; symmetry; apply tarjan_iter_empty;
      exact Hframes.
  - cbn [tarjan_run]; now rewrite Hframes.
Qed.

(** * Component index invariant *)

(** The internal reversed component list agrees with both maintained indexes. *)
Record tarjan_indexed {V} (EV : encoding V) (r : scc_result V) : Prop := {
  tarjan_index_length : length (component_ids r) = length (components r);
  tarjan_index_distinct : NoDup (component_ids r);
  tarjan_index_bound : forall i, In i (component_ids r) -> (i < tarjan_next_id r)%positive;
  tarjan_index_order : forall i j, In i (component_ids r) -> In j (component_ids r) ->
    (j < i)%positive -> before (component_ids r) i j;
  tarjan_index_at : forall i c, Trie.get i (component_at r) = Some c <->
    In (i, c) (combine (component_ids r) (components r));
  tarjan_index_owner : forall x i, Map.get EV x (comp_of r) = Some i <->
    exists c, In (i, c) (combine (component_ids r) (components r)) /\ In x c;
  tarjan_index_nonempty : forall c, In c (components r) -> c <> []
}.

Lemma tarjan_member_spec {V} (EV : encoding V) x xs :
  existsb (fun v => Pos.eqb (encode EV x) (encode EV v)) xs = true <-> In x xs.
Proof.
  rewrite existsb_exists; split.
  - intros [v [Hin Heq]]; apply Pos.eqb_eq in Heq.
    apply (encode_injective EV) in Heq; now subst v.
  - intro Hin; exists x; split; [exact Hin|apply Pos.eqb_refl].
Qed.

Lemma tarjan_initial_indexed {V} (EV : encoding V) :
  tarjan_indexed EV (@emitted V unit tarjan_initial).
Proof.
  constructor; cbn [tarjan_initial emitted components component_ids component_at comp_of].
  - reflexivity.
  - constructor.
  - intros i Hfalse; contradiction.
  - intros i j Hfalse; contradiction.
  - intros i c; rewrite Trie.get_empty; split; [discriminate|contradiction].
  - intros x i; rewrite Map.get_empty; split; [discriminate|].
    intros [c [Hfalse _]]; contradiction.
  - intros c Hfalse; contradiction.
Qed.

Lemma tarjan_emit_at {V} (EV : encoding V) (r : scc_result V) members i c :
  tarjan_indexed EV r ->
  (Trie.get i (Trie.set (tarjan_next_id r) members (component_at r)) = Some c <->
    In (i, c) ((tarjan_next_id r, members) ::
      combine (component_ids r) (components r))).
Proof.
  intro Hindex; destruct (Pos.eq_dec i (tarjan_next_id r)) as [Heq|Hne].
  - subst i; rewrite Trie.get_set_same; cbn [In]; split.
    + intro Heq; inversion Heq; left; reflexivity.
    + intros [Heq|Hin]; [inversion Heq; reflexivity|].
      apply in_combine_l in Hin.
      pose proof (tarjan_index_bound _ _ Hindex _ Hin) as Hbound.
      exfalso; exact (Pos.lt_irrefl _ Hbound).
  - rewrite Trie.get_set_other by congruence.
    rewrite (tarjan_index_at _ _ Hindex); cbn [In]; split; [auto|].
    intros [Heq|Hin]; [inversion Heq; congruence|exact Hin].
Qed.

Lemma tarjan_emit_owner {V} (EV : encoding V) (r : scc_result V) members owners :
  tarjan_indexed EV r ->
  (forall x, In x members -> ~ In x (concat (components r))) ->
  (forall x, Map.get EV x owners =
    if existsb (fun v => Pos.eqb (encode EV x) (encode EV v)) members
    then Some (tarjan_next_id r) else Map.get EV x (comp_of r)) ->
  forall x i, Map.get EV x owners = Some i <->
    exists c, In (i, c) ((tarjan_next_id r, members) ::
      combine (component_ids r) (components r)) /\ In x c.
Proof.
  intros Hindex Hdisjoint Howners x i; rewrite Howners.
  destruct (existsb (fun v => Pos.eqb (encode EV x) (encode EV v)) members) eqn:Hmem.
  - apply tarjan_member_spec in Hmem; split.
    + intro Heq; inversion Heq; exists members; cbn; auto.
    + intros [c [[Heq|Hin] Hx]].
      * inversion Heq; reflexivity.
      * exfalso; apply (Hdisjoint x Hmem).
        apply in_concat; exists c; split; [eapply in_combine_r; eauto|exact Hx].
  - split.
    + intro Hget; apply (tarjan_index_owner _ _ Hindex) in Hget.
      destruct Hget as [c [Hin Hx]]; exists c; cbn; auto.
    + intros [c [[Heq|Hin] Hx]].
      * inversion Heq; subst c.
        pose proof (proj2 (tarjan_member_spec EV x members) Hx); congruence.
      * apply (tarjan_index_owner _ _ Hindex); exists c; auto.
Qed.

Lemma tarjan_emit_indexed {V E} (EV : encoding V) root (st : tarjan_state V E) :
  tarjan_indexed EV (emitted st) -> In root (pending st) ->
  (forall x, In x (pending st) -> ~ In x (concat (components (emitted st)))) ->
  tarjan_indexed EV (emitted (tarjan_emit EV root st)).
Proof.
  intros Hindex Hroot Hdisjoint.
  pose proof (tarjan_pop_split EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  pose proof (tarjan_pop_nonempty EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st)) Hroot) as Hnonempty.
  pose proof (tarjan_pop_owners EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Howners.
  unfold tarjan_emit.
  destruct (tarjan_pop EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st)))
    as [[[members tail] links] owners] eqn:Hpop.
  cbn in Hsplit, Hnonempty, Howners; destruct Hsplit as [Hsplit _].
  constructor; cbn [emitted component_ids components component_at comp_of].
  - cbn [length]; f_equal; apply (tarjan_index_length _ _ Hindex).
  - constructor; [|apply (tarjan_index_distinct _ _ Hindex)].
    intro Hin; pose proof (tarjan_index_bound _ _ Hindex _ Hin) as Hbound.
    exact (Pos.lt_irrefl _ Hbound).
  - intros i [Heq|Hin]; cbn [tarjan_next_id component_ids].
    + subst i; apply Pos.lt_succ_diag_r.
    + eapply Pos.lt_trans; [apply (tarjan_index_bound _ _ Hindex _ Hin)|].
      apply Pos.lt_succ_diag_r.
  - intros i j [Hi|Hi] [Hj|Hj] Hlt.
    + subst i j; exfalso; exact (Pos.lt_irrefl _ Hlt).
    + subst i; apply dfs_before_cons; left; auto.
    + subst j; pose proof (tarjan_index_bound _ _ Hindex _ Hi) as Hbound.
      exfalso; exact (Pos.lt_irrefl _ (Pos.lt_trans _ _ _ Hlt Hbound)).
    + apply dfs_before_cons; right; apply (tarjan_index_order _ _ Hindex); assumption.
  - intros j c; exact (tarjan_emit_at EV (emitted st) members j c Hindex).
  - apply tarjan_emit_owner; [exact Hindex| |exact Howners].
    intros x Hin; apply Hdisjoint; rewrite Hsplit; apply in_or_app; left; exact Hin.
  - intros c [Heq|Hin]; [now subst c|].
    apply (tarjan_index_nonempty _ _ Hindex); exact Hin.
Qed.

(** The frame vertices occur in pending-stack order, with closed vertices between them. *)
Inductive tarjan_stack_order {V} : list V -> list V -> Prop :=
  | TarjanStackEmpty : forall xs, tarjan_stack_order [] xs
  | TarjanStackCons : forall v rest prefix tail,
      tarjan_stack_order rest tail ->
      tarjan_stack_order (v :: rest) (prefix ++ v :: tail).

Lemma tarjan_stack_prefix {V} (stack xs prefix : list V) :
  tarjan_stack_order stack xs -> tarjan_stack_order stack (prefix ++ xs).
Proof.
  intro Hstack; destruct Hstack as [xs|v rest front tail Hrest].
  - constructor.
  - rewrite app_assoc; apply (TarjanStackCons v rest (prefix ++ front) tail); exact Hrest.
Qed.

Lemma tarjan_stack_member {V} (stack xs : list V) :
  tarjan_stack_order stack xs -> incl stack xs.
Proof.
  intro Hstack; induction Hstack as [xs|v rest prefix tail Hrest IH]; intros x Hin.
  - contradiction.
  - apply in_or_app; right; destruct Hin as [Heq|Hin].
    + left; exact Heq.
    + right; apply IH; exact Hin.
Qed.

Lemma tarjan_stack_head {V} (v : V) rest xs :
  tarjan_stack_order (v :: rest) xs ->
  exists prefix tail, xs = prefix ++ v :: tail /\ tarjan_stack_order rest tail.
Proof.
  intro Hstack; inversion Hstack as [|w stack prefix tail Htail]; subst.
  exists prefix, tail; auto.
Qed.

Lemma tarjan_stack_drop {V} (v : V) rest xs :
  tarjan_stack_order (v :: rest) xs -> tarjan_stack_order rest xs.
Proof.
  intro Hstack; destruct (tarjan_stack_head v rest xs Hstack)
    as [prefix [tail [Heq Htail]]]; subst xs.
  replace (prefix ++ v :: tail) with ((prefix ++ [v]) ++ tail)
    by (rewrite <- app_assoc; reflexivity).
  apply tarjan_stack_prefix; exact Htail.
Qed.

Lemma tarjan_stack_suffix {V} (prefix tail xs : list V) :
  tarjan_stack_order (prefix ++ tail) xs -> tarjan_stack_order tail xs.
Proof.
  induction prefix as [|v prefix IH]; intro Hstack; [exact Hstack|].
  apply IH; apply (tarjan_stack_drop v); exact Hstack.
Qed.

Lemma tarjan_pop_prefix {V} (EV : encoding V) root i prefix tail links owners :
  ~ In root prefix ->
  let '(members, remaining, _, _) :=
    tarjan_pop EV root i (prefix ++ root :: tail) links owners in
  members = prefix ++ [root] /\ remaining = tail.
Proof.
  revert links owners; induction prefix as [|v prefix IH]; intros links owners Hnot.
  - cbn [app tarjan_pop]; rewrite Pos.eqb_refl; auto.
  - cbn [tarjan_pop app].
    assert (Hne : Pos.eqb (encode EV v) (encode EV root) = false).
    { apply Pos.eqb_neq; intro Heq; apply (encode_injective EV) in Heq.
      subst v; apply Hnot; left; reflexivity. }
    rewrite Hne.
    specialize (IH (Map.remove EV v links) (Map.set EV v i owners)
      ltac:(intro Hin; apply Hnot; right; exact Hin)).
    destruct (tarjan_pop EV root i (prefix ++ root :: tail)
      (Map.remove EV v links) (Map.set EV v i owners))
      as [[[members remaining] links'] owners'].
    cbn in *; destruct IH as [Heq Htail]; split; [now rewrite Heq|exact Htail].
Qed.

(** Pending and emitted nodes partition the discovery domain, and lowlinks index pending nodes. *)
Record tarjan_bookkeeping {V E} (EV : encoding V) (st : tarjan_state V E) : Prop := {
  tarjan_book_distinct : NoDup (pending st ++ concat (components (emitted st)));
  tarjan_book_disc : forall x, (exists n, Map.get EV x (disc st) = Some n) <->
    In x (pending st ++ concat (components (emitted st)));
  tarjan_book_low : forall x, (exists n, Map.get EV x (low st) = Some n) <->
    In x (pending st);
  tarjan_book_frames : tarjan_stack_order (map frame_node (frames st)) (pending st);
  tarjan_book_index : tarjan_indexed EV (emitted st)
}.

Lemma tarjan_nodup_disjoint {A} (xs ys : list A) :
  NoDup (xs ++ ys) -> forall x, In x xs -> ~ In x ys.
Proof.
  intro Hnodup; induction xs as [|v xs IH]; intros x Hin; [contradiction|].
  inversion Hnodup as [|head rest Hnot Htail]; subst.
  destruct Hin as [Heq|Hin].
  - subst v; intro Hx; apply Hnot; apply in_or_app; right; exact Hx.
  - apply IH; assumption.
Qed.

Lemma tarjan_initial_bookkeeping {V E} (EV : encoding V) :
  tarjan_bookkeeping EV (@tarjan_initial V E).
Proof.
  constructor; cbn [tarjan_initial pending components emitted disc low frames].
  - constructor.
  - intro x; rewrite Map.get_empty; split; [intros [n Hfalse]; discriminate|contradiction].
  - intro x; rewrite Map.get_empty; split; [intros [n Hfalse]; discriminate|contradiction].
  - constructor.
  - exact (tarjan_initial_indexed EV).
Qed.

Lemma tarjan_discover_bookkeeping {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) st v :
  tarjan_bookkeeping EV st -> Map.get EV v (disc st) = None ->
  tarjan_bookkeeping EV (tarjan_discover p v st).
Proof.
  intros Hbook Hfresh.
  assert (Hnot : ~ In v (pending st ++ concat (components (emitted st)))).
  { intro Hin; apply (tarjan_book_disc _ _ Hbook) in Hin.
    destruct Hin as [n Hn]; congruence. }
  constructor; cbn [tarjan_discover pending emitted disc low frames].
  - constructor; [exact Hnot|apply (tarjan_book_distinct _ _ Hbook)].
  - intro x; destruct (Pos.eq_dec (encode EV x) (encode EV v)) as [Heq|Hne].
    + apply (encode_injective EV) in Heq; subst x; rewrite Map.get_set_same.
      split; [intros _; left; reflexivity|intros _; eauto].
    + rewrite Map.get_set_other by (intro Heq; subst x; contradiction).
      rewrite (tarjan_book_disc _ _ Hbook); cbn [app In]; intuition congruence.
  - intro x; destruct (Pos.eq_dec (encode EV x) (encode EV v)) as [Heq|Hne].
    + apply (encode_injective EV) in Heq; subst x; rewrite Map.get_set_same.
      split; [intros _; left; reflexivity|intros _; eauto].
    + rewrite Map.get_set_other by (intro Heq; subst x; contradiction).
      rewrite (tarjan_book_low _ _ Hbook); cbn [In]; intuition congruence.
  - change (tarjan_stack_order (v :: map frame_node (frames st)) ([] ++ v :: pending st)).
    constructor; apply (tarjan_book_frames _ _ Hbook).
  - apply (tarjan_book_index _ _ Hbook).
Qed.

Lemma tarjan_lower_bookkeeping {V E} (EV : encoding V) v n (st : tarjan_state V E) :
  tarjan_bookkeeping EV st -> tarjan_bookkeeping EV (tarjan_lower EV v n st).
Proof.
  intro Hbook; unfold tarjan_lower; destruct (Map.get EV v (low st)) as [old|] eqn:Hold;
    [|exact Hbook].
  constructor; cbn [pending emitted disc low frames].
  - apply (tarjan_book_distinct _ _ Hbook).
  - apply (tarjan_book_disc _ _ Hbook).
  - intro x; destruct (Pos.eq_dec (encode EV x) (encode EV v)) as [Heq|Hne].
    + apply (encode_injective EV) in Heq; subst x; rewrite Map.get_set_same.
      assert (Hin : In v (pending st)).
      { apply (tarjan_book_low _ _ Hbook); exists old; exact Hold. }
      split; [intros _; exact Hin|intros _; eauto].
    + rewrite Map.get_set_other by (intro Heq; subst x; contradiction).
      apply (tarjan_book_low _ _ Hbook).
  - apply (tarjan_book_frames _ _ Hbook).
  - apply (tarjan_book_index _ _ Hbook).
Qed.

Lemma tarjan_rotate_nodup {A} (xs ys zs : list A) :
  NoDup (xs ++ ys ++ zs) -> NoDup (ys ++ xs ++ zs).
Proof.
  intro Hnodup; rewrite !app_assoc in *.
  eapply Permutation_NoDup; [apply Permutation_app_tail; apply Permutation_app_comm|].
  exact Hnodup.
Qed.

Lemma tarjan_emit_bookkeeping {V E} (EV : encoding V) root
    (st : tarjan_state V E) prefix tail :
  tarjan_bookkeeping EV st -> pending st = prefix ++ root :: tail ->
  ~ In root prefix -> tarjan_stack_order (map frame_node (frames st)) tail ->
  tarjan_bookkeeping EV (tarjan_emit EV root st).
Proof.
  intros Hbook Hpending Hnot Hframes.
  pose proof (tarjan_pop_prefix EV root (tarjan_next_id (emitted st)) prefix tail
    (low st) (comp_of (emitted st)) Hnot) as Hprefix.
  pose proof (tarjan_pop_links EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hlinks.
  pose proof (tarjan_pop_split EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  assert (Hroot : In root (pending st)).
  { rewrite Hpending; apply in_or_app; right; left; reflexivity. }
  pose proof (tarjan_emit_indexed EV root st (tarjan_book_index _ _ Hbook) Hroot
    (tarjan_nodup_disjoint _ _ (tarjan_book_distinct _ _ Hbook))) as Hindex.
  unfold tarjan_emit in Hindex |- *.
  rewrite <- Hpending in Hprefix.
  destruct (tarjan_pop EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st)))
    as [[[members remaining] links] owners] eqn:Hpop.
  cbn in Hprefix, Hlinks, Hsplit; destruct Hprefix as [Hmembers Htail].
  destruct Hsplit as [Hsplit _]; subst remaining.
  constructor; cbn [pending emitted components disc low frames concat].
  - apply tarjan_rotate_nodup; rewrite app_assoc, <- Hsplit.
    apply (tarjan_book_distinct _ _ Hbook).
  - intro x; rewrite (tarjan_book_disc _ _ Hbook), Hsplit, !in_app_iff; tauto.
  - intro x; rewrite Hlinks.
    destruct (existsb (fun v => Pos.eqb (encode EV x) (encode EV v)) members) eqn:Hmem.
    + apply tarjan_member_spec in Hmem; split; [intros [n Hfalse]; discriminate|].
      intro Hin; exfalso.
      pose proof (tarjan_book_distinct _ _ Hbook) as Hnodup.
      rewrite Hsplit, <- app_assoc in Hnodup.
      apply (tarjan_nodup_disjoint members
        (tail ++ concat (components (emitted st))) Hnodup x Hmem).
      apply in_or_app; left; exact Hin.
    + rewrite (tarjan_book_low _ _ Hbook), Hsplit, in_app_iff.
      split; [intros [Hin|Hin]; [|exact Hin]|auto].
      pose proof (proj2 (tarjan_member_spec EV x members) Hin); congruence.
  - exact Hframes.
  - exact Hindex.
Qed.

Lemma tarjan_reframe_bookkeeping {V E} (EV : encoding V)
    (st : tarjan_state V E) (stack : list (tarjan_frame V E)) :
  tarjan_bookkeeping EV st ->
  tarjan_stack_order (map frame_node stack) (pending st) ->
  tarjan_bookkeeping EV
    (TarjanState stack (disc st) (low st) (pending st) (clock st) (emitted st)).
Proof.
  intros Hbook Hstack; constructor; cbn.
  - apply (tarjan_book_distinct _ _ Hbook).
  - apply (tarjan_book_disc _ _ Hbook).
  - apply (tarjan_book_low _ _ Hbook).
  - exact Hstack.
  - apply (tarjan_book_index _ _ Hbook).
Qed.

Lemma tarjan_drop_bookkeeping {V E} (EV : encoding V) (st : tarjan_state V E) head rest :
  tarjan_bookkeeping EV st -> frames st = head :: rest ->
  tarjan_bookkeeping EV
    (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)).
Proof.
  intros Hbook Hframes; apply tarjan_reframe_bookkeeping; [exact Hbook|].
  apply (tarjan_stack_drop (frame_node head)).
  pose proof (tarjan_book_frames _ _ Hbook) as Hstack; rewrite Hframes in Hstack; exact Hstack.
Qed.

Lemma tarjan_close_bookkeeping {V E} (EV : encoding V) (st : tarjan_state V E)
    v es rest :
  tarjan_bookkeeping EV st -> frames st = TarjanFrame v es :: rest ->
  tarjan_bookkeeping EV (tarjan_close EV v rest st).
Proof.
  intros Hbook Hframes.
  pose proof (tarjan_book_frames _ _ Hbook) as Hstack.
  rewrite Hframes in Hstack; cbn [map frame_node] in Hstack.
  destruct (tarjan_stack_head v _ _ Hstack) as [prefix [tail [Hpending Htail]]].
  assert (Hclosed : tarjan_bookkeeping EV
    (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))).
  { apply tarjan_reframe_bookkeeping; [exact Hbook|].
    apply (tarjan_stack_drop v); exact Hstack. }
  unfold tarjan_close.
  destruct (Map.get EV v (low st)) as [l|], (Map.get EV v (disc st)) as [d|];
    try exact Hclosed.
  destruct (Pos.eqb l d).
  - apply (tarjan_emit_bookkeeping EV v _ prefix tail Hclosed Hpending); [|exact Htail].
    intro Hin.
    pose proof (tarjan_book_distinct _ _ Hbook) as Hnodup.
    rewrite Hpending, <- app_assoc in Hnodup.
    apply (tarjan_nodup_disjoint prefix
      ((v :: tail) ++ concat (components (emitted st))) Hnodup v Hin).
    left; reflexivity.
  - destruct rest as [|parent rest]; [exact Hclosed|].
    apply tarjan_lower_bookkeeping; exact Hclosed.
Qed.

Lemma tarjan_step_bookkeeping {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region st :
  tarjan_bookkeeping EV st -> tarjan_bookkeeping EV (tarjan_step p region st).
Proof.
  intro Hbook; unfold tarjan_step.
  destruct (frames st) as [|[v [|e es]] rest] eqn:Hframes; [exact Hbook| |].
  - apply (tarjan_close_bookkeeping EV st v [] rest Hbook Hframes).
  - assert (Hadvanced : tarjan_bookkeeping EV
      (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))).
    { apply tarjan_reframe_bookkeeping; [exact Hbook|].
      pose proof (tarjan_book_frames _ _ Hbook) as Hstack.
      rewrite Hframes in Hstack; exact Hstack. }
    destruct (FinSet.mem EV (Graph.target g e) region); [|exact Hadvanced].
    destruct (Map.get EV (Graph.target g e) (disc st)) as [d|] eqn:Hfresh.
    + destruct (Map.get EV (Graph.target g e) (low st)); [|exact Hadvanced].
      apply tarjan_lower_bookkeeping; exact Hadvanced.
    + apply tarjan_discover_bookkeeping; [exact Hadvanced|exact Hfresh].
Qed.

Lemma tarjan_run_bookkeeping {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region n st :
  tarjan_bookkeeping EV st -> tarjan_bookkeeping EV (tarjan_run p region n st).
Proof.
  rewrite tarjan_run_agrees; intro Hbook; induction n using Pos.peano_ind.
  - apply tarjan_step_bookkeeping; exact Hbook.
  - rewrite Pos.iter_succ; apply tarjan_step_bookkeeping; exact IHn.
Qed.

Lemma tarjan_root_bookkeeping {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region st v :
  tarjan_bookkeeping EV st -> tarjan_bookkeeping EV (tarjan_root p region st v).
Proof.
  intro Hbook; unfold tarjan_root.
  destruct (Map.get EV v (disc st)) as [d|] eqn:Hfresh; [exact Hbook|].
  apply tarjan_run_bookkeeping; apply tarjan_discover_bookkeeping; assumption.
Qed.

Lemma tarjan_fold_bookkeeping {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region roots st :
  tarjan_bookkeeping EV st ->
  tarjan_bookkeeping EV (fold_left (tarjan_root p region) roots st).
Proof.
  revert st; induction roots as [|v roots IH]; intros st Hbook; [exact Hbook|].
  cbn [fold_left]; apply IH; apply tarjan_root_bookkeeping; exact Hbook.
Qed.

Lemma tarjan_combine_app {A B} (xs : list A) (ys : list B) tailx taily :
  length xs = length ys ->
  combine (xs ++ tailx) (ys ++ taily) = combine xs ys ++ combine tailx taily.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] Hlength;
    cbn [length] in Hlength; try discriminate; [reflexivity|].
  cbn [combine app]; f_equal; apply IH; lia.
Qed.

Lemma tarjan_combine_rev {A B} (xs : list A) (ys : list B) :
  length xs = length ys -> combine (rev xs) (rev ys) = rev (combine xs ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] Hlength;
    cbn [length] in Hlength; try discriminate; [reflexivity|].
  cbn [rev combine]; rewrite tarjan_combine_app by (rewrite !length_rev; lia).
  rewrite IH by lia; reflexivity.
Qed.

Lemma tarjan_concat_rev {A} (xs : list (list A)) :
  Permutation (concat (rev xs)) (concat xs).
Proof.
  induction xs as [|x xs IH]; [constructor|].
  cbn [rev concat]; rewrite concat_app; cbn [concat]; rewrite app_nil_r.
  eapply Permutation_trans; [apply Permutation_app_tail; exact IH|].
  apply Permutation_app_comm.
Qed.

Lemma tarjan_nodup_suffix {A} (xs ys : list A) :
  NoDup (xs ++ ys) -> NoDup ys.
Proof.
  induction xs as [|x xs IH]; intro Hnodup; [exact Hnodup|].
  inversion Hnodup as [|head tail Hnot Htail]; apply IH; exact Htail.
Qed.

(** The returned component list retains exact indexes, distinct members and emission order. *)
Lemma scc_within_indexes {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region :
  let r := scc_within p region in
  NoDup (concat (components r)) /\
  (forall c, In c (components r) -> c <> []) /\
  length (component_ids r) = length (components r) /\
  (forall i c, Trie.get i (component_at r) = Some c <->
    In (i, c) (combine (component_ids r) (components r))) /\
  NoDup (component_ids r) /\
  (forall x i, Map.get EV x (comp_of r) = Some i <->
    exists c, Trie.get i (component_at r) = Some c /\ In x c) /\
  (forall i j, In i (component_ids r) -> In j (component_ids r) ->
    (j < i)%positive -> before (rev (component_ids r)) i j).
Proof.
  pose proof (tarjan_fold_bookkeeping EV g p (FinSet.of_list EV region) region
    tarjan_initial (tarjan_initial_bookkeeping EV)) as Hbook.
  remember (fold_left (tarjan_root p (FinSet.of_list EV region)) region tarjan_initial)
    as result eqn:Hresult.
  pose proof (tarjan_book_index _ _ Hbook) as Hindex.
  cbn zeta; unfold scc_within; rewrite <- Hresult; unfold tarjan_result.
  cbn [components component_ids component_at comp_of].
  split.
  - eapply Permutation_NoDup; [apply Permutation_sym; apply tarjan_concat_rev|].
    apply (tarjan_nodup_suffix (pending result)).
    apply (tarjan_book_distinct _ _ Hbook).
  - split.
    + intros c Hin; rewrite <- in_rev in Hin.
      apply (tarjan_index_nonempty _ _ Hindex); exact Hin.
    + split; [rewrite !length_rev; apply (tarjan_index_length _ _ Hindex)|].
      split.
      * intros i c; rewrite tarjan_combine_rev by apply (tarjan_index_length _ _ Hindex).
        rewrite <- in_rev; apply (tarjan_index_at _ _ Hindex).
      * split; [apply NoDup_rev; apply (tarjan_index_distinct _ _ Hindex)|].
        split.
        -- intros x i; rewrite (tarjan_index_owner _ _ Hindex).
           split; intros [c [Hc Hx]]; exists c; split; [|exact Hx| |exact Hx].
           ++ apply (tarjan_index_at _ _ Hindex); exact Hc.
           ++ apply (tarjan_index_at _ _ Hindex); exact Hc.
        -- rewrite rev_involutive; intros i j Hi Hj Hlt.
           rewrite <- in_rev in Hi, Hj; apply (tarjan_index_order _ _ Hindex); assumption.
Qed.

(** The discovery map is a fresh numbering, and pending retains its discovery order. *)
Definition tarjan_numbered {V E} (EV : encoding V) (st : tarjan_state V E) : Prop :=
  exists history, dfs_numbering EV history (disc st) (clock st) /\
    tarjan_stack_order (pending st) history.

Lemma tarjan_initial_numbered {V E} (EV : encoding V) :
  tarjan_numbered EV (@tarjan_initial V E).
Proof.
  exists []; split; constructor.
Qed.

Lemma tarjan_discover_numbered {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v st :
  tarjan_numbered EV st -> Map.get EV v (disc st) = None ->
  tarjan_numbered EV (tarjan_discover p v st).
Proof.
  intros [history [Hnumbers Hpending]] Hfresh; exists (v :: history).
  split; cbn [tarjan_discover disc clock pending].
  - constructor; [exact Hnumbers|].
    intro Hin; apply (dfs_numbering_domain EV _ _ _ Hnumbers) in Hin.
    destruct Hin as [d Hd]; congruence.
  - change (tarjan_stack_order (v :: pending st) ([] ++ v :: history)).
    constructor; exact Hpending.
Qed.

Lemma tarjan_lower_numbered {V E} (EV : encoding V) v n (st : tarjan_state V E) :
  tarjan_numbered EV st -> tarjan_numbered EV (tarjan_lower EV v n st).
Proof.
  intro Hnumbers; unfold tarjan_lower; destruct (Map.get EV v (low st)); exact Hnumbers.
Qed.

Lemma tarjan_emit_numbered {V E} (EV : encoding V) v (st : tarjan_state V E) :
  tarjan_numbered EV st -> tarjan_numbered EV (tarjan_emit EV v st).
Proof.
  intros [history [Hnumbers Hpending]].
  pose proof (tarjan_pop_split EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  unfold tarjan_emit; destruct (tarjan_pop EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as [[[members tail] links] owners].
  cbn in Hsplit; destruct Hsplit as [Hsplit _].
  exists history; split; [exact Hnumbers|].
  cbn [pending]; rewrite Hsplit in Hpending.
  apply (tarjan_stack_suffix members tail history); exact Hpending.
Qed.

Lemma tarjan_reframe_numbered {V E} (EV : encoding V)
    (st : tarjan_state V E) (stack : list (tarjan_frame V E)) :
  tarjan_numbered EV st -> tarjan_numbered EV
    (TarjanState stack (disc st) (low st) (pending st) (clock st) (emitted st)).
Proof.
  intros [history [Hnumbers Hpending]]; exists history; auto.
Qed.

Lemma tarjan_close_numbered {V E} (EV : encoding V) v rest (st : tarjan_state V E) :
  tarjan_numbered EV st -> tarjan_numbered EV (tarjan_close EV v rest st).
Proof.
  intro Hnumbers; unfold tarjan_close.
  destruct (Map.get EV v (low st)) as [l|], (Map.get EV v (disc st)) as [d|];
    try (apply tarjan_reframe_numbered; exact Hnumbers).
  destruct (Pos.eqb l d).
  - apply tarjan_emit_numbered; apply tarjan_reframe_numbered; exact Hnumbers.
  - destruct rest as [|parent rest]; [apply tarjan_reframe_numbered; exact Hnumbers|].
    apply tarjan_lower_numbered; apply tarjan_reframe_numbered; exact Hnumbers.
Qed.

Lemma tarjan_step_numbered {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region st :
  tarjan_numbered EV st -> tarjan_numbered EV (tarjan_step p region st).
Proof.
  intro Hnumbers; unfold tarjan_step.
  destruct (frames st) as [|[v [|e es]] rest]; [exact Hnumbers| |].
  - apply tarjan_close_numbered; exact Hnumbers.
  - destruct (FinSet.mem EV (Graph.target g e) region);
      [|apply tarjan_reframe_numbered; exact Hnumbers].
    destruct (Map.get EV (Graph.target g e) (disc st)) as [d|] eqn:Hfresh.
    + destruct (Map.get EV (Graph.target g e) (low st));
        [apply tarjan_lower_numbered|]; apply tarjan_reframe_numbered; exact Hnumbers.
    + apply tarjan_discover_numbered; [apply tarjan_reframe_numbered; exact Hnumbers|].
      exact Hfresh.
Qed.

Lemma tarjan_root_numbered {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region st v :
  tarjan_numbered EV st -> tarjan_numbered EV (tarjan_root p region st v).
Proof.
  intro Hnumbers; unfold tarjan_root.
  destruct (Map.get EV v (disc st)) as [d|] eqn:Hfresh; [exact Hnumbers|].
  rewrite tarjan_run_agrees.
  assert (Hstart : tarjan_numbered EV (tarjan_discover p v st)).
  { apply tarjan_discover_numbered; assumption. }
  generalize (fuel p); intro n; induction n using Pos.peano_ind.
  - apply tarjan_step_numbered; exact Hstart.
  - rewrite Pos.iter_succ; apply tarjan_step_numbered; exact IHn.
Qed.

Lemma tarjan_before_prefix {A} (prefix xs : list A) u v :
  before xs u v -> before (prefix ++ xs) u v.
Proof.
  intros [first [middle [last Heq]]]; exists (prefix ++ first), middle, last.
  rewrite Heq, <- app_assoc; reflexivity.
Qed.

Lemma tarjan_before_cross {A} (xs ys : list A) u v :
  In u xs -> In v ys -> before (xs ++ ys) u v.
Proof.
  intros Hu Hv; apply in_split in Hu, Hv.
  destruct Hu as [first [middle Heq]], Hv as [front [last Heq']]; subst xs ys.
  exists first, (middle ++ front), last; rewrite <- !app_assoc; reflexivity.
Qed.

Lemma tarjan_stack_before {V} (stack xs : list V) u v :
  tarjan_stack_order stack xs -> before stack u v -> before xs u v.
Proof.
  intro Hstack; induction Hstack as [xs|w rest prefix tail Htail IH]; intro Hbefore.
  - destruct Hbefore as [[|a first] [middle [last Hfalse]]]; discriminate.
  - apply tarjan_before_prefix; apply dfs_before_cons in Hbefore; apply dfs_before_cons.
    destruct Hbefore as [[Heq Hin]|Hbefore].
    + left; split; [exact Heq|apply (tarjan_stack_member _ _ Htail); exact Hin].
    + right; apply IH; exact Hbefore.
Qed.

Lemma tarjan_pending_numbers {V E} (EV : encoding V) (st : tarjan_state V E) u v a b :
  tarjan_numbered EV st -> before (pending st) u v ->
  Map.get EV u (disc st) = Some a -> Map.get EV v (disc st) = Some b ->
  (b < a)%positive.
Proof.
  intros [history [Hnumbers Hpending]] Hbefore Hu Hv.
  apply (proj1 (dfs_numbering_order EV history _ _ Hnumbers v u b a Hv Hu)).
  apply (proj1 (dfs_before_reverse history u v)).
  apply (tarjan_stack_before _ _ _ _ Hpending); exact Hbefore.
Qed.

Lemma tarjan_path_append {V E} (g : Graph.t V E) u first v last w :
  path g u first v -> path g v last w -> path g u (first ++ last) w.
Proof.
  intros Hfirst Hlast; induction Hfirst as [v|e es v Hedge Hpath IH].
  - exact Hlast.
  - cbn [app]; constructor; [exact Hedge|apply IH; exact Hlast].
Qed.

Lemma tarjan_reaches_trans {V E} (g : Graph.t V E) u v w :
  reaches g u v -> reaches g v w -> reaches g u w.
Proof.
  intros [first Hfirst] [last Hlast]; exists (first ++ last).
  eapply tarjan_path_append; eauto.
Qed.

(** Each lowlink denotes a pending vertex reachable from its owner, never a newer vertex. *)
Definition tarjan_low_witness {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) : Prop :=
  forall w l, Map.get EV w (low st) = Some l ->
    exists d x, Map.get EV w (disc st) = Some d /\ (l <= d)%positive /\
      In x (pending st) /\ Map.get EV x (disc st) = Some l /\ reaches g w x.

(** A pending vertex whose frame has closed has a strictly older lowlink witness. *)
Definition tarjan_closed_low {V E} (EV : encoding V) (st : tarjan_state V E) : Prop :=
  forall w l d, In w (pending st) -> ~ In w (map frame_node (frames st)) ->
    Map.get EV w (low st) = Some l -> Map.get EV w (disc st) = Some d ->
    (l < d)%positive.

(** An older pending vertex reaches every newer pending vertex. *)
Definition tarjan_pending_paths {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) : Prop :=
  forall u v a b, In u (pending st) -> In v (pending st) ->
    Map.get EV u (disc st) = Some a -> Map.get EV v (disc st) = Some b ->
    (a <= b)%positive -> reaches g u v.

Lemma tarjan_pending_support {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) :
  tarjan_bookkeeping EV st -> tarjan_low_witness EV g st -> tarjan_closed_low EV st ->
  forall w d, In w (pending st) -> Map.get EV w (disc st) = Some d ->
    exists a da, In a (map frame_node (frames st)) /\ reaches g w a /\
      Map.get EV a (disc st) = Some da /\ (da <= d)%positive.
Proof.
  intros Hbook Hlow Hclosed.
  assert (Hsupport : forall n w d, Pos.to_nat d = n ->
    In w (pending st) -> Map.get EV w (disc st) = Some d ->
    exists a da, In a (map frame_node (frames st)) /\ reaches g w a /\
      Map.get EV a (disc st) = Some da /\ (da <= d)%positive).
  { intro n; induction n as [n IH] using lt_wf_ind; intros w d Hn Hin Hdisc.
    destruct (in_dec (dfs_eq_dec EV) w (map frame_node (frames st))) as [Hopen|Hnot].
    - exists w, d; split; [exact Hopen|].
      split; [exists []; constructor|]; split; [exact Hdisc|apply Pos.le_refl].
    - destruct (proj2 (tarjan_book_low _ _ Hbook w) Hin) as [l Hlink].
      destruct (Hlow w l Hlink) as [d' [x [Hdisc' [_ [Hx [Hnumber Hreach]]]]]].
      assert (Hstrict : (l < d)%positive) by (apply (Hclosed w l d); assumption).
      destruct (IH (Pos.to_nat l) ltac:(rewrite <- Hn; apply Pos2Nat.inj_lt; exact Hstrict)
        x l eq_refl Hx Hnumber) as [a [da [Ha [Hpath [Hnum Hbound]]]]].
      exists a, da; split; [exact Ha|]; split.
      + eapply tarjan_reaches_trans; eauto.
      + split; [exact Hnum|]; eapply Pos.le_trans; [exact Hbound|].
        apply Pos.lt_le_incl; exact Hstrict. }
  intros w d Hin Hdisc; apply (Hsupport (Pos.to_nat d) w d eq_refl Hin Hdisc).
Qed.

Lemma tarjan_pending_empty {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) :
  tarjan_bookkeeping EV st -> tarjan_low_witness EV g st -> tarjan_closed_low EV st ->
  frames st = [] -> pending st = [].
Proof.
  intros Hbook Hlow Hclosed Hframes; destruct (pending st) as [|w rest] eqn:Hpending;
    [reflexivity|].
  assert (Hin : In w (pending st)) by (rewrite Hpending; left; reflexivity).
  assert (Hvisited : exists d, Map.get EV w (disc st) = Some d).
  { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hin. }
  destruct Hvisited as [d Hnumber].
  destruct (tarjan_pending_support EV g st Hbook Hlow Hclosed w d Hin Hnumber)
    as [a [da [Ha _]]].
  rewrite Hframes in Ha; contradiction.
Qed.

Lemma tarjan_pending_current {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v es rest :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st ->
  tarjan_low_witness EV g st -> tarjan_closed_low EV st -> tarjan_pending_paths EV g st ->
  frames st = TarjanFrame v es :: rest ->
  forall w, In w (pending st) -> reaches g w v.
Proof.
  intros Hbook Hnumbers Hlow Hclosed Hpaths Hframes w Hw.
  assert (Hvpending : In v (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)).
    rewrite Hframes; left; reflexivity. }
  assert (Hwd : exists d, Map.get EV w (disc st) = Some d).
  { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hw. }
  assert (Hvd : exists d, Map.get EV v (disc st) = Some d).
  { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hvpending. }
  destruct Hwd as [dw Hwd], Hvd as [dv Hvd].
  destruct (tarjan_pending_support EV g st Hbook Hlow Hclosed w dw Hw Hwd)
    as [a [da [Ha [Hreach [Had Hbound]]]]].
  eapply tarjan_reaches_trans; [exact Hreach|].
  apply (Hpaths a v da dv); [|exact Hvpending|exact Had|exact Hvd|].
  - apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); exact Ha.
  - rewrite Hframes in Ha; cbn [map frame_node In] in Ha.
    destruct Ha as [Heq|Ha].
    + subst a; rewrite Hvd in Had; inversion Had; apply Pos.le_refl.
    + apply Pos.lt_le_incl; apply (tarjan_pending_numbers EV st v a dv da Hnumbers);
        [|exact Hvd|exact Had].
      apply (tarjan_stack_before _ _ _ _ (tarjan_book_frames _ _ Hbook)).
      rewrite Hframes; apply dfs_before_cons; left; split; [reflexivity|exact Ha].
Qed.

Lemma tarjan_fresh_pending {V E} (EV : encoding V) (st : tarjan_state V E) v :
  tarjan_bookkeeping EV st -> Map.get EV v (disc st) = None -> ~ In v (pending st).
Proof.
  intros Hbook Hfresh Hin.
  assert (Hdisc : exists d, Map.get EV v (disc st) = Some d).
  { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hin. }
  destruct Hdisc as [d Hd]; congruence.
Qed.

Lemma tarjan_discover_low_witness {V E} (EV : encoding V) (g h : Graph.t V E)
    (p : prepared EV g) v st :
  tarjan_bookkeeping EV st -> tarjan_low_witness EV h st ->
  Map.get EV v (disc st) = None -> tarjan_low_witness EV h (tarjan_discover p v st).
Proof.
  intros Hbook Hlow Hfresh w l Hlink.
  cbn [tarjan_discover low] in Hlink.
  destruct (dfs_eq_dec EV w v) as [Heq|Hne].
  - subst w; rewrite Map.get_set_same in Hlink; inversion Hlink; subst l.
    exists (clock st), v; cbn [tarjan_discover disc clock pending].
    rewrite Map.get_set_same; split; [reflexivity|].
    split; [apply Pos.le_refl|]; split; [left; reflexivity|].
    split; [reflexivity|exists []; constructor].
  - rewrite Map.get_set_other in Hlink by exact Hne.
    destruct (Hlow w l Hlink) as [d [x [Hdisc [Hbound [Hx [Hnumber Hpath]]]]]].
    assert (Hxne : x <> v).
    { intro Heq; subst x; exact (tarjan_fresh_pending EV st v Hbook Hfresh Hx). }
    exists d, x; cbn [tarjan_discover disc pending].
    rewrite !Map.get_set_other by assumption; split; [exact Hdisc|].
    split; [exact Hbound|]; split; [right; exact Hx|]; auto.
Qed.

Lemma tarjan_discover_closed_low {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v st :
  tarjan_closed_low EV st -> tarjan_closed_low EV (tarjan_discover p v st).
Proof.
  intros Hclosed w l d Hin Hnot Hlink Hdisc.
  cbn [tarjan_discover pending frames map frame_node In] in Hin, Hnot.
  destruct Hin as [Heq|Hin]; [subst w; exfalso; apply Hnot; left; reflexivity|].
  assert (Hne : w <> v) by (intro Heq; subst w; apply Hnot; left; reflexivity).
  cbn [tarjan_discover disc low] in Hlink, Hdisc.
  rewrite Map.get_set_other in Hlink, Hdisc by exact Hne.
  apply (Hclosed w l d); [exact Hin| |exact Hlink|exact Hdisc].
  intro Hopen; apply Hnot; right; exact Hopen.
Qed.

Lemma tarjan_discover_pending_paths {V E} (EV : encoding V) (g h : Graph.t V E)
    (p : prepared EV g) v st :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_pending_paths EV h st ->
  Map.get EV v (disc st) = None ->
  (forall w, In w (pending st) -> reaches h w v) ->
  tarjan_pending_paths EV h (tarjan_discover p v st).
Proof.
  intros Hbook [history [Hnumbers Hpending]] Hpaths Hfresh Hreach u w a b Hu Hw Hua Hwb Hab.
  cbn [tarjan_discover pending In disc] in Hu, Hw, Hua, Hwb.
  destruct Hu as [Heq|Hu], Hw as [Heq'|Hw].
  - subst u w; exists []; constructor.
  - subst u; rewrite Map.get_set_same in Hua; inversion Hua; subst a.
    assert (Hne : w <> v).
    { intro Heq; subst w; exact (tarjan_fresh_pending EV st v Hbook Hfresh Hw). }
    rewrite Map.get_set_other in Hwb by exact Hne.
    pose proof (dfs_numbering_bound EV _ _ _ Hnumbers w b Hwb) as Hbound.
    exfalso; exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hab Hbound)).
  - subst w; apply Hreach; exact Hu.
  - assert (Hune : u <> v).
    { intro Heq; subst u; exact (tarjan_fresh_pending EV st v Hbook Hfresh Hu). }
    assert (Hwne : w <> v).
    { intro Heq; subst w; exact (tarjan_fresh_pending EV st v Hbook Hfresh Hw). }
    rewrite Map.get_set_other in Hua by exact Hune.
    rewrite Map.get_set_other in Hwb by exact Hwne.
    apply (Hpaths u w a b); assumption.
Qed.

Lemma tarjan_lower_low_witness {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v n :
  tarjan_low_witness EV g st ->
  (exists x, In x (pending st) /\ Map.get EV x (disc st) = Some n /\ reaches g v x) ->
  tarjan_low_witness EV g (tarjan_lower EV v n st).
Proof.
  intros Hlow [x [Hx [Hnumber Hreach]]]; unfold tarjan_lower.
  destruct (Map.get EV v (low st)) as [old|] eqn:Hold; [|exact Hlow].
  intros w l Hlink; cbn [low] in Hlink.
  destruct (dfs_eq_dec EV w v) as [Heq|Hne].
  - subst w; rewrite Map.get_set_same in Hlink; inversion Hlink; subst l.
    destruct (Hlow v old Hold) as [d [y [Hdisc [Hbound [Hy [Hyd Hypath]]]]]].
    destruct (Pos.leb old n) eqn:Htest.
    + apply Pos.leb_le in Htest; rewrite Pos.min_l by exact Htest; exists d, y; cbn; auto.
    + apply Pos.leb_gt in Htest.
      assert (Hle : (n <= old)%positive) by (apply Pos.lt_le_incl; exact Htest).
      rewrite Pos.min_r by exact Hle; exists d, x; cbn; split; [exact Hdisc|].
      split; [eapply Pos.le_trans; eauto|]; auto.
  - rewrite Map.get_set_other in Hlink by exact Hne.
    exact (Hlow w l Hlink).
Qed.

Lemma tarjan_lower_closed_low {V E} (EV : encoding V) v n (st : tarjan_state V E) :
  tarjan_closed_low EV st -> In v (map frame_node (frames st)) ->
  tarjan_closed_low EV (tarjan_lower EV v n st).
Proof.
  intros Hclosed Hv; unfold tarjan_lower.
  destruct (Map.get EV v (low st)); [|exact Hclosed].
  intros w l d Hin Hnot Hlink Hdisc; cbn in Hin, Hnot, Hlink, Hdisc.
  assert (Hne : w <> v) by (intro Heq; subst w; contradiction).
  rewrite Map.get_set_other in Hlink by exact Hne.
  apply (Hclosed w l d); assumption.
Qed.

Lemma tarjan_lower_pending_paths {V E} (EV : encoding V) (g : Graph.t V E)
    v n (st : tarjan_state V E) :
  tarjan_pending_paths EV g st -> tarjan_pending_paths EV g (tarjan_lower EV v n st).
Proof.
  intro Hpaths; unfold tarjan_lower; destruct (Map.get EV v (low st)); exact Hpaths.
Qed.

Lemma tarjan_pop_survivor {V} (EV : encoding V) root i xs links owners w l :
  In w xs ->
  let '(_, tail, links', _) := tarjan_pop EV root i xs links owners in
  Map.get EV w links' = Some l -> In w tail /\ Map.get EV w links = Some l.
Proof.
  intro Hin; pose proof (tarjan_pop_split EV root i xs links owners) as Hsplit.
  pose proof (tarjan_pop_links EV root i xs links owners w) as Hlinks.
  destruct (tarjan_pop EV root i xs links owners) as [[[members tail] links'] owners'].
  cbn in Hsplit, Hlinks; destruct Hsplit as [Hsplit _]; rewrite Hlinks.
  destruct (existsb (fun v => Pos.eqb (encode EV w) (encode EV v)) members) eqn:Hmem;
    [discriminate|].
  intro Hget; split; [|exact Hget].
  rewrite Hsplit, in_app_iff in Hin; destruct Hin as [Hin|Hin]; [|exact Hin].
  pose proof (proj2 (tarjan_member_spec EV w members) Hin); congruence.
Qed.

Lemma tarjan_emit_low_witness {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) root :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_low_witness EV g st ->
  tarjan_low_witness EV g (tarjan_emit EV root st).
Proof.
  intros Hbook Hnumbers Hlow.
  pose proof (tarjan_pop_split EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  pose proof (tarjan_pop_links EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hlinks.
  unfold tarjan_emit; destruct (tarjan_pop EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st)))
    as [[[members tail] links] owners] eqn:Hpop.
  cbn in Hsplit, Hlinks; destruct Hsplit as [Hsplit _].
  intros w l Hlink; cbn [low] in Hlink; rewrite Hlinks in Hlink.
  destruct (existsb (fun v => Pos.eqb (encode EV w) (encode EV v)) members) eqn:Hmem;
    [discriminate|].
  destruct (Hlow w l Hlink) as [d [x [Hdisc [Hbound [Hx [Hnumber Hreach]]]]]].
  assert (Hw : In w tail).
  { assert (Hin : In w (pending st)).
    { apply (tarjan_book_low _ _ Hbook); exists l; exact Hlink. }
    rewrite Hsplit, in_app_iff in Hin; destruct Hin as [Hin|Hin]; [|exact Hin].
    pose proof (proj2 (tarjan_member_spec EV w members) Hin); congruence. }
  exists d, x; cbn [disc pending]; split; [exact Hdisc|]; split; [exact Hbound|].
  split; [|auto].
  rewrite Hsplit, in_app_iff in Hx; destruct Hx as [Hx|Hx]; [|exact Hx].
  exfalso.
  assert (Hlt : (d < l)%positive).
  { apply (tarjan_pending_numbers EV st x w l d Hnumbers); [|exact Hnumber|exact Hdisc].
    rewrite Hsplit; apply tarjan_before_cross; assumption. }
  exact (Pos.lt_irrefl _ (Pos.lt_le_trans _ _ _ Hlt Hbound)).
Qed.

Lemma tarjan_emit_pending_paths {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) root :
  tarjan_pending_paths EV g st -> tarjan_pending_paths EV g (tarjan_emit EV root st).
Proof.
  intro Hpaths; pose proof (tarjan_pop_split EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  unfold tarjan_emit; destruct (tarjan_pop EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as [[[members tail] links] owners].
  cbn in Hsplit; destruct Hsplit as [Hsplit _].
  intros u v a b Hu Hv Hua Hvb Hbound; cbn in Hu, Hv, Hua, Hvb.
  apply (Hpaths u v a b); try assumption;
    rewrite Hsplit; apply in_or_app; right; assumption.
Qed.

Lemma tarjan_closed_reframe {V E} (EV : encoding V) (st : tarjan_state V E) v es rest :
  tarjan_closed_low EV st -> frames st = TarjanFrame v es :: rest ->
  (forall l d, Map.get EV v (low st) = Some l -> Map.get EV v (disc st) = Some d ->
    (l < d)%positive) ->
  tarjan_closed_low EV
    (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)).
Proof.
  intros Hclosed Hframes Hv w l d Hin Hnot Hlink Hdisc.
  cbn in Hin, Hnot, Hlink, Hdisc.
  destruct (dfs_eq_dec EV w v) as [Heq|Hne]; [subst w; apply Hv; assumption|].
  apply (Hclosed w l d); try assumption.
  rewrite Hframes; cbn [map frame_node In]; intros [Heq|Hopen]; congruence.
Qed.

Lemma tarjan_close_emit_closed_low {V E} (EV : encoding V) (st : tarjan_state V E)
    v es rest :
  tarjan_bookkeeping EV st -> tarjan_closed_low EV st ->
  frames st = TarjanFrame v es :: rest ->
  tarjan_closed_low EV (tarjan_emit EV v
    (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))).
Proof.
  intros Hbook Hclosed Hframes.
  assert (Hv : In v (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); rewrite Hframes.
    left; reflexivity. }
  pose proof (tarjan_pop_split EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  pose proof (tarjan_pop_links EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hlinks.
  unfold tarjan_emit; cbn [pending low emitted comp_of].
  destruct (tarjan_pop EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st)))
    as [[[members tail] links] owners] eqn:Hpop.
  cbn in Hsplit, Hlinks; destruct Hsplit as [Hsplit Hroot].
  intros w l d Hin Hnot Hlink Hdisc; cbn in Hin, Hnot, Hlink, Hdisc.
  rewrite Hlinks in Hlink.
  destruct (existsb (fun x => Pos.eqb (encode EV w) (encode EV x)) members);
    [discriminate|].
  assert (Hne : v <> w).
  { intro Heq; subst w; pose proof (tarjan_book_distinct _ _ Hbook) as Hnodup.
    rewrite Hsplit, <- app_assoc in Hnodup.
    apply (tarjan_nodup_disjoint members
      (tail ++ concat (components (emitted st))) Hnodup v (Hroot Hv)).
    apply in_or_app; left; exact Hin. }
  apply (Hclosed w l d); try assumption.
  - rewrite Hsplit; apply in_or_app; right; exact Hin.
  - rewrite Hframes; cbn [map frame_node In]; intros [Heq|Hopen]; congruence.
Qed.

(** Discovery order, lowlink witnesses and closed-frame obligations form the lowlink invariant. *)
Record tarjan_low_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) : Prop := {
  tarjan_low_book : tarjan_bookkeeping EV st;
  tarjan_low_numbers : tarjan_numbered EV st;
  tarjan_low_links : tarjan_low_witness EV g st;
  tarjan_low_closed : tarjan_closed_low EV st;
  tarjan_low_paths : tarjan_pending_paths EV g st
}.

Lemma tarjan_initial_low_invariant {V E} (EV : encoding V) (g : Graph.t V E) :
  tarjan_low_invariant EV g (@tarjan_initial V E).
Proof.
  constructor.
  - apply tarjan_initial_bookkeeping.
  - apply tarjan_initial_numbered.
  - intros w l Hfalse; cbn [tarjan_initial low] in Hfalse.
    rewrite Map.get_empty in Hfalse; discriminate.
  - intros w l d Hfalse; cbn [tarjan_initial pending] in Hfalse; contradiction.
  - intros u v a b Hfalse; cbn [tarjan_initial pending] in Hfalse; contradiction.
Qed.

Lemma tarjan_discover_low_invariant {V E} (EV : encoding V) (g h : Graph.t V E)
    (p : prepared EV g) v st :
  tarjan_low_invariant EV h st -> Map.get EV v (disc st) = None ->
  (forall w, In w (pending st) -> reaches h w v) ->
  tarjan_low_invariant EV h (tarjan_discover p v st).
Proof.
  intros Hinv Hfresh Hreach; constructor.
  - apply tarjan_discover_bookkeeping; [apply (tarjan_low_book _ _ _ Hinv)|exact Hfresh].
  - apply tarjan_discover_numbered; [apply (tarjan_low_numbers _ _ _ Hinv)|exact Hfresh].
  - apply tarjan_discover_low_witness; [apply (tarjan_low_book _ _ _ Hinv)| |exact Hfresh].
    apply (tarjan_low_links _ _ _ Hinv).
  - apply tarjan_discover_closed_low; apply (tarjan_low_closed _ _ _ Hinv).
  - apply tarjan_discover_pending_paths; try assumption.
    + apply (tarjan_low_book _ _ _ Hinv).
    + apply (tarjan_low_numbers _ _ _ Hinv).
    + apply (tarjan_low_paths _ _ _ Hinv).
Qed.

Lemma tarjan_frame_parent_path {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v es parent rest :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_pending_paths EV g st ->
  frames st = TarjanFrame v es :: parent :: rest -> reaches g (frame_node parent) v.
Proof.
  intros Hbook Hnumbers Hpaths Hframes.
  assert (Hv : In v (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)).
    rewrite Hframes; left; reflexivity. }
  assert (Hp : In (frame_node parent) (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)).
    rewrite Hframes; right; left; reflexivity. }
  assert (Hvd : exists d, Map.get EV v (disc st) = Some d).
  { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hv. }
  assert (Hpd : exists d, Map.get EV (frame_node parent) (disc st) = Some d).
  { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hp. }
  destruct Hvd as [dv Hvd], Hpd as [dp Hpd].
  apply (Hpaths (frame_node parent) v dp dv); try assumption; apply Pos.lt_le_incl.
  apply (tarjan_pending_numbers EV st v (frame_node parent) dv dp Hnumbers);
    [|exact Hvd|exact Hpd].
  apply (tarjan_stack_before _ _ _ _ (tarjan_book_frames _ _ Hbook)).
  rewrite Hframes; apply dfs_before_cons; left; split; [reflexivity|left; reflexivity].
Qed.

Lemma tarjan_close_low_witness {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v es rest :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_low_witness EV g st ->
  tarjan_pending_paths EV g st -> frames st = TarjanFrame v es :: rest ->
  tarjan_low_witness EV g (tarjan_close EV v rest st).
Proof.
  intros Hbook Hnumbers Hlow Hpaths Hframes.
  assert (Hclosedbook : tarjan_bookkeeping EV
    (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))).
  { apply tarjan_reframe_bookkeeping; [exact Hbook|].
    apply (tarjan_stack_drop v).
    pose proof (tarjan_book_frames _ _ Hbook) as Hstack; rewrite Hframes in Hstack;
      exact Hstack. }
  unfold tarjan_close.
  destruct (Map.get EV v (low st)) as [l|] eqn:Hlink;
    destruct (Map.get EV v (disc st)) as [d|] eqn:Hdisc; try exact Hlow.
  destruct (Pos.eqb l d).
  - apply tarjan_emit_low_witness; [exact Hclosedbook| |exact Hlow].
    apply tarjan_reframe_numbered; exact Hnumbers.
  - destruct rest as [|parent rest]; [exact Hlow|].
    apply tarjan_lower_low_witness; [exact Hlow|].
    destruct (Hlow v l Hlink) as [dv [x [_ [_ [Hx [Hnumber Hreach]]]]]].
    exists x; split; [exact Hx|]; split; [exact Hnumber|].
    eapply tarjan_reaches_trans; [|exact Hreach].
    apply (tarjan_frame_parent_path EV g st v es parent rest); assumption.
Qed.

Lemma tarjan_close_closed_low {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v es rest :
  tarjan_bookkeeping EV st -> tarjan_low_witness EV g st -> tarjan_closed_low EV st ->
  frames st = TarjanFrame v es :: rest ->
  tarjan_closed_low EV (tarjan_close EV v rest st).
Proof.
  intros Hbook Hlow Hclosed Hframes.
  assert (Hv : In v (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); rewrite Hframes.
    left; reflexivity. }
  destruct (proj2 (tarjan_book_low _ _ Hbook v) Hv) as [l Hlink].
  destruct (Hlow v l Hlink) as [d [x [Hdisc [Hbound _]]]].
  unfold tarjan_close; rewrite Hlink, Hdisc.
  destruct (Pos.eqb l d) eqn:Heq.
  - apply (tarjan_close_emit_closed_low EV st v es rest); assumption.
  - assert (Hstrict : (l < d)%positive).
    { apply Pos.eqb_neq in Heq; apply Pos.le_lteq in Hbound.
      destruct Hbound as [Hlt|Hequal]; [exact Hlt|contradiction]. }
    assert (Hreframed : tarjan_closed_low EV
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))).
    { apply (tarjan_closed_reframe EV st v es rest Hclosed Hframes).
      intros l' d' Hl Hd; rewrite Hlink in Hl; rewrite Hdisc in Hd.
      inversion Hl; inversion Hd; subst; exact Hstrict. }
    destruct rest as [|parent rest]; [exact Hreframed|].
    apply tarjan_lower_closed_low; [exact Hreframed|left; reflexivity].
Qed.

Lemma tarjan_close_pending_paths {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v rest :
  tarjan_pending_paths EV g st -> tarjan_pending_paths EV g (tarjan_close EV v rest st).
Proof.
  intro Hpaths; unfold tarjan_close.
  destruct (Map.get EV v (low st)) as [l|], (Map.get EV v (disc st)) as [d|];
    try exact Hpaths.
  destruct (Pos.eqb l d); [apply tarjan_emit_pending_paths; exact Hpaths|].
  destruct rest as [|parent rest]; [exact Hpaths|].
  apply tarjan_lower_pending_paths; exact Hpaths.
Qed.

Lemma tarjan_close_low_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v es rest :
  tarjan_low_invariant EV g st -> frames st = TarjanFrame v es :: rest ->
  tarjan_low_invariant EV g (tarjan_close EV v rest st).
Proof.
  intros Hinv Hframes; destruct Hinv as [Hbook Hnumbers Hlow Hclosed Hpaths]; constructor.
  - apply (tarjan_close_bookkeeping EV st v es rest); assumption.
  - apply tarjan_close_numbered; exact Hnumbers.
  - apply (tarjan_close_low_witness EV g st v es rest); assumption.
  - apply (tarjan_close_closed_low EV g st v es rest); assumption.
  - apply tarjan_close_pending_paths; exact Hpaths.
Qed.

Lemma tarjan_reframe_low_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) (stack : list (tarjan_frame V E)) :
  tarjan_low_invariant EV g st -> map frame_node stack = map frame_node (frames st) ->
  tarjan_low_invariant EV g
    (TarjanState stack (disc st) (low st) (pending st) (clock st) (emitted st)).
Proof.
  intros [Hbook Hnumbers Hlow Hclosed Hpaths] Hsame; constructor.
  - apply tarjan_reframe_bookkeeping; [exact Hbook|].
    rewrite Hsame; apply (tarjan_book_frames _ _ Hbook).
  - apply tarjan_reframe_numbered; exact Hnumbers.
  - exact Hlow.
  - unfold tarjan_closed_low in *; cbn [pending frames low disc]; rewrite Hsame;
      exact Hclosed.
  - exact Hpaths.
Qed.

Lemma tarjan_lower_low_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v n :
  tarjan_low_invariant EV g st -> In v (map frame_node (frames st)) ->
  (exists x, In x (pending st) /\ Map.get EV x (disc st) = Some n /\ reaches g v x) ->
  tarjan_low_invariant EV g (tarjan_lower EV v n st).
Proof.
  intros [Hbook Hnumbers Hlow Hclosed Hpaths] Hopen Hcandidate; constructor.
  - apply tarjan_lower_bookkeeping; exact Hbook.
  - apply tarjan_lower_numbered; exact Hnumbers.
  - apply tarjan_lower_low_witness; assumption.
  - apply tarjan_lower_closed_low; assumption.
  - apply tarjan_lower_pending_paths; exact Hpaths.
Qed.

Lemma tarjan_induced_edge {V E} (EV : encoding V) (g : Graph.t V E) keep v e :
  graph_wf g -> In e (Graph.out g v) -> FinSet.mem EV (Graph.target g e) keep = true ->
  reaches (induced EV keep g) v (Graph.target g e).
Proof.
  intros Hwf Hedge Hkeep.
  pose proof (out_source Hwf v e Hedge) as Hsource; rewrite <- Hsource in Hedge |- *.
  exists [e]; apply (@path_cons V E (induced EV keep g) e [] (Graph.target g e));
    [|constructor].
  change (In e (filter (fun a => FinSet.mem EV (Graph.target g a) keep)
    (Graph.out g (Graph.source g e)))).
  apply filter_In; auto.
Qed.

Lemma tarjan_step_low_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st :
  ready EV g p -> tarjan_control g st ->
  tarjan_low_invariant EV (induced EV keep g) st ->
  tarjan_low_invariant EV (induced EV keep g) (tarjan_step p keep st).
Proof.
  intros Hready Hcontrol Hinv.
  unfold tarjan_step; destruct (frames st) as [|[v [|e es]] rest] eqn:Hframes;
    [exact Hinv| |].
  - apply (tarjan_close_low_invariant EV _ st v [] rest); assumption.
  - assert (Hadvanced : tarjan_low_invariant EV (induced EV keep g)
      (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))).
    { apply tarjan_reframe_low_invariant; [exact Hinv|rewrite Hframes; reflexivity]. }
    destruct (FinSet.mem EV (Graph.target g e) keep) eqn:Hkeep; [|exact Hadvanced].
    assert (Hedge : In e (Graph.out g v)).
    { destruct (Hcontrol (TarjanFrame v (e :: es))
        ltac:(rewrite Hframes; left; reflexivity)) as [_ Hedges].
      apply Hedges; left; reflexivity. }
    assert (Hpath : reaches (induced EV keep g) v (Graph.target g e)).
    { apply tarjan_induced_edge; [exact (proj1 Hready)|exact Hedge|exact Hkeep]. }
    destruct (Map.get EV (Graph.target g e) (disc st)) as [d|] eqn:Hfresh.
    + destruct (Map.get EV (Graph.target g e) (low st)) as [l|] eqn:Hlink;
        [|exact Hadvanced].
      apply tarjan_lower_low_invariant; [exact Hadvanced|left; reflexivity|].
      exists (Graph.target g e); split; [|split; assumption].
      apply (tarjan_book_low _ _ (tarjan_low_book _ _ _ Hinv)); exists l; exact Hlink.
    + apply tarjan_discover_low_invariant; [exact Hadvanced|exact Hfresh|].
      intros w Hw; eapply tarjan_reaches_trans; [|exact Hpath].
      apply (tarjan_pending_current EV _ st v (e :: es) rest);
        try exact Hframes; try exact Hw.
      * apply (tarjan_low_book _ _ _ Hinv).
      * apply (tarjan_low_numbers _ _ _ Hinv).
      * apply (tarjan_low_links _ _ _ Hinv).
      * apply (tarjan_low_closed _ _ _ Hinv).
      * apply (tarjan_low_paths _ _ _ Hinv).
Qed.

(** * Condensation boundary properties *)

Lemma condensation_entries_spec {V} (EV : encoding V) (r : scc_result V) roots seen c :
  In c (condensation_entries EV r roots seen) <->
  FinSet.mem positive_encoding c seen = false /\
  exists v, In v roots /\ Map.get EV v (comp_of r) = Some c.
Proof.
  revert seen; induction roots as [|v roots IH]; intro seen.
  - cbn; split; [contradiction|intros [_ [w [Hfalse _]]]; contradiction].
  - cbn [condensation_entries]; destruct (Map.get EV v (comp_of r)) as [i|] eqn:Howner.
    + destruct (FinSet.mem positive_encoding i seen) eqn:Hseen.
      * rewrite IH; split.
        -- intros [Hfresh [w [Hin Hget]]]; split; [exact Hfresh|].
           exists w; split; [right; exact Hin|exact Hget].
        -- intros [Hfresh [w [[Heq|Hin] Hget]]].
           ++ subst w; rewrite Howner in Hget; inversion Hget; subst i; congruence.
           ++ split; [exact Hfresh|]; exists w; auto.
      * cbn [In]; rewrite IH; split.
        -- intros [Heq|[Hfresh [w [Hin Hget]]]].
           ++ subst c; split; [exact Hseen|]; exists v; auto.
           ++ split.
              ** destruct (FinSet.mem positive_encoding c seen) eqn:Hmem;
                   [|reflexivity].
                 assert (Hadded : FinSet.mem positive_encoding c
                   (FinSet.add positive_encoding i seen) = true).
                 { apply FinSet.mem_add; right; exact Hmem. }
                 congruence.
              ** exists w; auto.
        -- intros [Hfresh [w [[Heq|Hin] Hget]]].
           ++ subst w; rewrite Howner in Hget; inversion Hget; left; reflexivity.
           ++ destruct (Pos.eq_dec i c) as [Heq|Hne].
              ** left; exact Heq.
              ** right; split; [|exists w; auto].
                 destruct (FinSet.mem positive_encoding c
                   (FinSet.add positive_encoding i seen)) eqn:Hadded; [|reflexivity].
                 apply FinSet.mem_add in Hadded; destruct Hadded as [Heq|Hmem];
                   congruence.
    + rewrite IH; split.
      * intros [Hfresh [w [Hin Hget]]]; split; [exact Hfresh|].
        exists w; split; [right; exact Hin|exact Hget].
      * intros [Hfresh [w [[Heq|Hin] Hget]]].
        -- subst w; congruence.
        -- split; [exact Hfresh|]; exists w; auto.
Qed.

Lemma condensation_entries_nodup {V} (EV : encoding V) (r : scc_result V) roots seen :
  NoDup (condensation_entries EV r roots seen).
Proof.
  revert seen; induction roots as [|v roots IH]; intro seen; cbn [condensation_entries].
  - constructor.
  - destruct (Map.get EV v (comp_of r)) as [i|]; [|apply IH].
    destruct (FinSet.mem positive_encoding i seen); [apply IH|].
    constructor; [|apply IH].
    rewrite condensation_entries_spec; intros [Hfresh _].
    assert (Hadded : FinSet.mem positive_encoding i
      (FinSet.add positive_encoding i seen) = true).
    { apply FinSet.mem_add; left; reflexivity. }
    congruence.
Qed.

Lemma condensation_entry_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) c :
  In c (Graph.entries (condensation p r)) <->
  exists s, In s (Graph.entries g) /\ Map.get EV s (comp_of r) = Some c.
Proof.
  cbn [condensation Graph.entries]; rewrite condensation_entries_spec, FinSet.mem_empty;
    tauto.
Qed.

Lemma condensation_entry_nodup {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) :
  NoDup (Graph.entries (condensation p r)).
Proof.
  apply condensation_entries_nodup.
Qed.

(** * Traversal termination *)

(** Discovery and closing pay once for a node, and its adjacency pays once for every edge. *)
Fixpoint tarjan_white_work {V E} (EV : encoding V) (g : Graph.t V E)
    (numbers : Map.t V positive) (nodes : list V) : nat :=
  match nodes with
  | [] => 0
  | v :: rest =>
    (match Map.get EV v numbers with Some _ => 0 | None => length (Graph.out g v) + 2 end) +
      tarjan_white_work EV g numbers rest
  end.

(** A frame pays for its remaining edge inspections and its closing transition. *)
Definition tarjan_frame_work {V E} (stack : list (tarjan_frame V E)) : nat :=
  fold_right (fun f n => length (frame_edges f) + 1 + n) 0 stack.

(** The work measure is used only in proofs, never recomputed by the executable machine. *)
Definition tarjan_work {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) : nat :=
  tarjan_white_work EV g (disc st) (Graph.nodes g) + tarjan_frame_work (frames st).

Lemma tarjan_white_other {V E} (EV : encoding V) (g : Graph.t V E) numbers nodes v n :
  ~ In v nodes ->
  tarjan_white_work EV g (Map.set EV v n numbers) nodes =
    tarjan_white_work EV g numbers nodes.
Proof.
  induction nodes as [|w nodes IH]; intro Hnot; cbn [tarjan_white_work]; [reflexivity|].
  rewrite Map.get_set_other.
  - rewrite IH; [reflexivity|intro Hin; apply Hnot; right; exact Hin].
  - intro Heq; subst w; apply Hnot; left; reflexivity.
Qed.

Lemma tarjan_white_set {V E} (EV : encoding V) (g : Graph.t V E) numbers nodes v n :
  NoDup nodes -> In v nodes -> Map.get EV v numbers = None ->
  tarjan_white_work EV g (Map.set EV v n numbers) nodes + length (Graph.out g v) + 2 =
    tarjan_white_work EV g numbers nodes.
Proof.
  intro Hnodes; induction Hnodes as [|w nodes Hnot Hnodes IH]; intros Hin Hfresh.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst w; cbn [tarjan_white_work]; rewrite Map.get_set_same, Hfresh.
      rewrite tarjan_white_other by exact Hnot; lia.
    + assert (Hne : w <> v) by (intro Heq; subst w; contradiction).
      cbn [tarjan_white_work]; rewrite Map.get_set_other by exact Hne.
      specialize (IH Hin Hfresh); destruct (Map.get EV w numbers); lia.
Qed.

Lemma tarjan_white_bound {V E} (EV : encoding V) (g : Graph.t V E) numbers nodes :
  tarjan_white_work EV g numbers nodes <=
    2 * length nodes + fold_right (fun v n => length (Graph.out g v) + n) 0 nodes.
Proof.
  induction nodes as [|v nodes IH]; cbn [tarjan_white_work length fold_right]; [lia|].
  destruct (Map.get EV v numbers); lia.
Qed.

Lemma tarjan_lower_control_fields {V E} (EV : encoding V) v n (st : tarjan_state V E) :
  frames (tarjan_lower EV v n st) = frames st /\
  disc (tarjan_lower EV v n st) = disc st.
Proof.
  unfold tarjan_lower; destruct (Map.get EV v (low st)); split; reflexivity.
Qed.

Lemma tarjan_emit_control_fields {V E} (EV : encoding V) v (st : tarjan_state V E) :
  frames (tarjan_emit EV v st) = frames st /\ disc (tarjan_emit EV v st) = disc st.
Proof.
  unfold tarjan_emit; destruct (tarjan_pop EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as [[[members tail] links] owners].
  split; reflexivity.
Qed.

Lemma tarjan_close_control_fields {V E} (EV : encoding V) v rest
    (st : tarjan_state V E) :
  frames (tarjan_close EV v rest st) = rest /\ disc (tarjan_close EV v rest st) = disc st.
Proof.
  unfold tarjan_close; destruct (Map.get EV v (low st)) as [l|],
    (Map.get EV v (disc st)) as [d|];
    try (split; reflexivity).
  destruct (Pos.eqb l d).
  - exact (tarjan_emit_control_fields EV v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))).
  - destruct rest as [|parent rest]; [split; reflexivity|].
    exact (tarjan_lower_control_fields EV (frame_node parent) l
      (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st)
        (emitted st))).
Qed.

Lemma tarjan_step_control {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region st :
  ready EV g p -> tarjan_control g st -> tarjan_control g (tarjan_step p region st).
Proof.
  intros [Hwf [_ Hlaws]] Hcontrol.
  unfold tarjan_step; destruct (frames st) as [|[v [|e es]] rest] eqn:Hframes.
  - exact Hcontrol.
  - destruct (tarjan_close_control_fields EV v rest st) as [Hstack _].
    intros f Hin; rewrite Hstack in Hin; apply Hcontrol; rewrite Hframes; right; exact Hin.
  - assert (Hv : In v (Graph.nodes g) /\ incl (e :: es) (Graph.out g v)).
    { apply (Hcontrol (TarjanFrame v (e :: es))); rewrite Hframes; left; reflexivity. }
    destruct Hv as [Hv Hedges].
    assert (Hadvanced : tarjan_control g
      (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))).
    { intros f [Heq|Hin].
      - subst f; cbn; split; [exact Hv|intros a Ha; apply Hedges; right; exact Ha].
      - apply Hcontrol; rewrite Hframes; right; exact Hin. }
    destruct (FinSet.mem EV (Graph.target g e) region); [|exact Hadvanced].
    destruct (Map.get EV (Graph.target g e) (disc st)) as [d|].
    + destruct (Map.get EV (Graph.target g e) (low st)); [|exact Hadvanced].
      intros f Hin; rewrite (proj1 (tarjan_lower_control_fields _ _ _ _)) in Hin.
      apply Hadvanced; exact Hin.
    + intros f [Heq|Hin].
      * subst f; cbn; assert (Ht : In (Graph.target g e) (Graph.nodes g)).
        { eapply out_target_in; [exact Hwf|exact Hv|apply Hedges; left; reflexivity]. }
        split; [exact Ht|rewrite (succ_agrees Hlaws _ Ht); intros a Ha; exact Ha].
      * apply Hadvanced; exact Hin.
Qed.

Lemma tarjan_step_decreases {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region st :
  ready EV g p -> tarjan_control g st -> frames st <> [] ->
  tarjan_work EV g (tarjan_step p region st) < tarjan_work EV g st.
Proof.
  intros [Hwf [_ Hlaws]] Hcontrol Hnonempty.
  unfold tarjan_step; destruct (frames st) as [|[v [|e es]] rest] eqn:Hframes;
    [contradiction| |].
  - destruct (tarjan_close_control_fields EV v rest st) as [Hstack Hdisc].
    unfold tarjan_work; rewrite Hstack, Hdisc, Hframes;
      unfold tarjan_frame_work; cbn [frame_edges fold_right length]; lia.
  - assert (Hv : In v (Graph.nodes g) /\ incl (e :: es) (Graph.out g v)).
    { apply (Hcontrol (TarjanFrame v (e :: es))); rewrite Hframes; left; reflexivity. }
    destruct Hv as [Hv Hedges].
    destruct (FinSet.mem EV (Graph.target g e) region).
    + destruct (Map.get EV (Graph.target g e) (disc st)) as [d|] eqn:Hfresh.
      * destruct (Map.get EV (Graph.target g e) (low st)).
        -- destruct (tarjan_lower_control_fields EV v d
             (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
               (pending st) (clock st) (emitted st))) as [Hstack Hdisc].
           unfold tarjan_work; rewrite Hstack, Hdisc, Hframes; unfold tarjan_frame_work;
             cbn [disc frames frame_edges fold_right length]; lia.
        -- unfold tarjan_work; rewrite Hframes; unfold tarjan_frame_work;
             cbn [disc frames frame_edges fold_right length]; lia.
      * assert (Ht : In (Graph.target g e) (Graph.nodes g)).
        { eapply out_target_in; [exact Hwf|exact Hv|apply Hedges; left; reflexivity]. }
        pose proof (tarjan_white_set EV g (disc st) (Graph.nodes g)
          (Graph.target g e) (clock st) (nodes_nodup Hwf) Ht Hfresh) as Hcredit.
        unfold tarjan_work; rewrite Hframes; unfold tarjan_frame_work;
          cbn [tarjan_discover disc frames clock frame_edges fold_right length].
        rewrite (succ_agrees Hlaws _ Ht); lia.
    + unfold tarjan_work; rewrite Hframes; unfold tarjan_frame_work;
        cbn [disc frames frame_edges fold_right length]; lia.
Qed.

Lemma tarjan_iter_terminates {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region st n :
  ready EV g p -> tarjan_control g st ->
  let result := Pos.iter (tarjan_step p region) st n in
  tarjan_control g result /\
    (frames result = [] \/ tarjan_work EV g result + Pos.to_nat n <= tarjan_work EV g st).
Proof.
  intros Hready Hcontrol; induction n using Pos.peano_ind.
  - change (tarjan_control g (tarjan_step p region st) /\
      (frames (tarjan_step p region st) = [] \/
        tarjan_work EV g (tarjan_step p region st) + 1 <= tarjan_work EV g st)).
    split; [apply tarjan_step_control; assumption|].
    destruct (frames st) as [|f rest] eqn:Hframes.
    + left; unfold tarjan_step; now rewrite Hframes.
    + right; pose proof (tarjan_step_decreases EV g p region st Hready Hcontrol
        ltac:(rewrite Hframes; discriminate)); lia.
  - rewrite Pos.iter_succ.
    remember (Pos.iter (tarjan_step p region) st n) as result eqn:Hresult.
    destruct IHn as [Hstate Hbound].
    split; [apply tarjan_step_control; assumption|].
    destruct Hbound as [Hempty|Hbound].
    + left; unfold tarjan_step; now rewrite Hempty.
    + destruct (frames result) as [|f rest] eqn:Hframes.
      * left; unfold tarjan_step; now rewrite Hframes.
      * right; pose proof (tarjan_step_decreases EV g p region
          result Hready Hstate
          ltac:(rewrite Hframes; discriminate)) as Hdecrease.
        rewrite Pos2Nat.inj_succ; lia.
Qed.

Lemma tarjan_root_terminates {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region st v :
  ready EV g p -> frames st = [] -> In v (Graph.nodes g) ->
  tarjan_control g (tarjan_root p region st v) /\ frames (tarjan_root p region st v) = [].
Proof.
  intros Hready Hempty Hv; unfold tarjan_root.
  destruct (Map.get EV v (disc st)) eqn:Hfresh.
  - split; [intros f Hin; rewrite Hempty in Hin; contradiction|exact Hempty].
  - pose proof Hready as [Hwf [_ Hlaws]].
    assert (Hcontrol : tarjan_control g (tarjan_discover p v st)).
    { intros f [Heq|Hin].
      - subst f; cbn; split; [exact Hv|].
        rewrite (succ_agrees Hlaws _ Hv); intros e He; exact He.
      - rewrite Hempty in Hin; contradiction. }
    pose proof (tarjan_white_set EV g (disc st) (Graph.nodes g) v (clock st)
      (nodes_nodup Hwf) Hv Hfresh) as Hcredit.
    pose proof (tarjan_white_bound EV g (disc st) (Graph.nodes g)) as Htotal.
    assert (Hfuel : tarjan_work EV g (tarjan_discover p v st) < Pos.to_nat (fuel p)).
    { unfold tarjan_work; cbn [tarjan_discover disc frames]; rewrite Hempty.
      unfold tarjan_frame_work; cbn [fold_right frame_edges length].
      rewrite (succ_agrees Hlaws _ Hv), (fuel_value Hlaws); unfold edge_count; lia. }
    rewrite tarjan_run_agrees.
    destruct (tarjan_iter_terminates EV g p region (tarjan_discover p v st)
      (fuel p) Hready Hcontrol) as [Hstate [Hdone|Hbound]].
    + split; assumption.
    + lia.
Qed.

(** * Exact condensation adjacency *)

(** Reading a missing adjacency binding returns the empty list. *)
Definition condensation_edges {E} (m : Trie.t (list E)) (c : positive) : list E :=
  match Trie.get c m with Some es => es | None => [] end.

(** A component keeps precisely the edges whose endpoints have different assigned identifiers. *)
Definition condensation_cross {V E} (EV : encoding V) (g : Graph.t V E)
    (r : scc_result V) (c : positive) (v : V) (e : E) : bool :=
  match Map.get EV v (comp_of r), Map.get EV (Graph.target g e) (comp_of r) with
  | Some i, Some j => Pos.eqb i c && negb (Pos.eqb j c)
  | _, _ => false
  end.

Lemma condensation_cross_spec {V E} (EV : encoding V) (g : Graph.t V E)
    (r : scc_result V) c v e :
  condensation_cross EV g r c v e = true <->
    exists j, Map.get EV v (comp_of r) = Some c /\
      Map.get EV (Graph.target g e) (comp_of r) = Some j /\ j <> c.
Proof.
  unfold condensation_cross; destruct (Map.get EV v (comp_of r)) as [i|] eqn:Hi;
    destruct (Map.get EV (Graph.target g e) (comp_of r)) as [j|] eqn:Hj.
  - rewrite andb_true_iff, negb_true_iff, Pos.eqb_eq, Pos.eqb_neq;
      split; [intros [Heq Hne]; subst i; exists j; auto|].
    intros [k [Heq [Htarget Hne]]]; inversion Heq; inversion Htarget; subst; auto.
  - split; [discriminate|intros [k [_ [Hfalse _]]]; discriminate].
  - split; [discriminate|intros [k [Hfalse _]]; discriminate].
  - split; [discriminate|intros [k [Hfalse _]]; discriminate].
Qed.

Lemma condensation_edge_read {V E} (EV : encoding V) (g : Graph.t V E)
    (r : scc_result V) v e m c :
  condensation_edges (condensation_edge EV g r v e m) c =
    if condensation_cross EV g r c v e then e :: condensation_edges m c
    else condensation_edges m c.
Proof.
  unfold condensation_edge, condensation_cross.
  destruct (Map.get EV v (comp_of r)) as [i|]; [|reflexivity].
  destruct (Map.get EV (Graph.target g e) (comp_of r)) as [j|]; [|reflexivity].
  destruct (Pos.eq_dec i c) as [Heq|Hne].
  - subst i; rewrite Pos.eqb_refl; cbn [andb].
    destruct (Pos.eqb c j) eqn:Hsame.
    + apply Pos.eqb_eq in Hsame; subst j; rewrite Pos.eqb_refl; reflexivity.
    + assert (Hdifferent : Pos.eqb j c = false).
      { apply Pos.eqb_neq; intro Heq; subst j; rewrite Pos.eqb_refl in Hsame;
          discriminate. }
      rewrite Hdifferent; unfold condensation_edges; rewrite Trie.get_set_same;
        reflexivity.
  - assert (Hdifferent : Pos.eqb i c = false) by (apply Pos.eqb_neq; exact Hne).
    rewrite Hdifferent; cbn [andb].
    destruct (Pos.eqb i j); [reflexivity|].
    unfold condensation_edges; rewrite Trie.get_set_other; [reflexivity|congruence].
Qed.

Lemma condensation_edges_fold {V E} (EV : encoding V) (g : Graph.t V E)
    (r : scc_result V) v es m c :
  condensation_edges (fold_right (condensation_edge EV g r v) m es) c =
    filter (condensation_cross EV g r c v) es ++ condensation_edges m c.
Proof.
  induction es as [|e es IH]; [reflexivity|].
  cbn [fold_right]; rewrite condensation_edge_read, IH; cbn [filter].
  destruct (condensation_cross EV g r c v e); reflexivity.
Qed.

Lemma condensation_nodes_fold {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) nodes m c :
  condensation_edges
    (fold_right (fun v acc => fold_right (condensation_edge EV g r v) acc
      (succ_edges p v)) m nodes) c =
    flat_map (fun v => filter (condensation_cross EV g r c v) (succ_edges p v)) nodes ++
      condensation_edges m c.
Proof.
  induction nodes as [|v nodes IH]; [reflexivity|].
  cbn [fold_right flat_map]; rewrite condensation_edges_fold, IH, app_assoc; reflexivity.
Qed.

Lemma condensation_out_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) c e :
  ready EV g p ->
  (In e (Graph.out (condensation p r) c) <->
    exists x j, In x (Graph.nodes g) /\ In e (Graph.out g x) /\
      Map.get EV x (comp_of r) = Some c /\
      Map.get EV (Graph.target g e) (comp_of r) = Some j /\ j <> c).
Proof.
  intros [_ [_ Hlaws]].
  change (In e (condensation_edges (condensation_index p r) c) <->
    exists x j, In x (Graph.nodes g) /\ In e (Graph.out g x) /\
      Map.get EV x (comp_of r) = Some c /\
      Map.get EV (Graph.target g e) (comp_of r) = Some j /\ j <> c).
  unfold condensation_index; rewrite condensation_nodes_fold.
  unfold condensation_edges; rewrite Trie.get_empty, app_nil_r, in_flat_map; split.
  - intros [v [Hv He]]; apply filter_In in He; destruct He as [He Hcross].
    apply condensation_cross_spec in Hcross; destruct Hcross as [j [Hsource [Htarget Hne]]].
    exists v, j; rewrite (succ_agrees Hlaws _ Hv) in He; auto.
  - intros [v [j [Hv [He [Hsource [Htarget Hne]]]]]].
    exists v; split; [exact Hv|]; apply filter_In; split.
    + rewrite (succ_agrees Hlaws _ Hv); exact He.
    + apply condensation_cross_spec; exists j; auto.
Qed.

Lemma condensation_out_nodup {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) c :
  ready EV g p -> NoDup (Graph.out (condensation p r) c).
Proof.
  intros [Hwf [Hunique Hlaws]].
  change (NoDup (condensation_edges (condensation_index p r) c)).
  unfold condensation_index; rewrite condensation_nodes_fold.
  unfold condensation_edges; rewrite Trie.get_empty, app_nil_r.
  assert (Hlist : forall nodes, incl nodes (Graph.nodes g) ->
    flat_map (fun v => filter (condensation_cross EV g r c v) (succ_edges p v)) nodes =
      filter (fun e => condensation_cross EV g r c (Graph.source g e) e)
        (flat_map (Graph.out g) nodes)).
  { intros nodes Hnodes; induction nodes as [|v nodes IH]; [reflexivity|].
    cbn [flat_map]; rewrite (succ_agrees Hlaws v (Hnodes v (or_introl eq_refl))),
      filter_app, IH by (intros x Hx; apply Hnodes; right; exact Hx).
    f_equal; apply filter_ext_in; intros e He.
    rewrite (out_source Hwf v e He); reflexivity. }
  rewrite Hlist by (intros x Hx; exact Hx); apply NoDup_filter.
  apply graph_edges_nodup; [apply (nodes_nodup Hwf)|exact Hunique|].
  intros; eapply out_source; eauto.
Qed.

(** A component index covers precisely graph vertices and gives them listed identifiers. *)
Definition scc_covers {V E} (EV : encoding V) (g : Graph.t V E)
    (r : scc_result V) : Prop :=
  (forall v, In v (Graph.nodes g) -> exists i, Map.get EV v (comp_of r) = Some i) /\
  (forall v i, Map.get EV v (comp_of r) = Some i -> In i (component_ids r)).

Lemma condensation_endpoints {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) e :
  scc_covers EV g r ->
  In (Graph.source g e) (Graph.nodes g) -> In (Graph.target g e) (Graph.nodes g) ->
  exists i j, Map.get EV (Graph.source g e) (comp_of r) = Some i /\
    Map.get EV (Graph.target g e) (comp_of r) = Some j /\
    Graph.source (condensation p r) e = i /\ Graph.target (condensation p r) e = j.
Proof.
  intros [Htotal _] Hsource Htarget.
  destruct (Htotal _ Hsource) as [i Hi]; destruct (Htotal _ Htarget) as [j Hj].
  exists i, j; split; [exact Hi|]; split; [exact Hj|].
  change (scc_owner EV r (Graph.source g e) = i /\
    scc_owner EV r (Graph.target g e) = j).
  unfold scc_owner; rewrite Hi, Hj; auto.
Qed.

Lemma condensation_wf {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) :
  ready EV g p -> scc_covers EV g r -> NoDup (component_ids r) ->
  graph_wf (condensation p r).
Proof.
  intros Hready [Htotal Hids] Hnodup; pose proof Hready as [Hwf _].
  constructor.
  - apply NoDup_rev; exact Hnodup.
  - intros c Hin; apply condensation_entry_exact in Hin; destruct Hin as [v [_ Hget]].
    change (In c (rev (component_ids r))); rewrite <- in_rev.
    eapply Hids; exact Hget.
  - intros c e Hin; apply (condensation_out_exact EV g p r c e Hready) in Hin.
    destruct Hin as [v [j [_ [Hedge [Howner _]]]]].
    change (scc_owner EV r (Graph.source g e) = c).
    unfold scc_owner; rewrite (out_source Hwf _ _ Hedge), Howner.
    reflexivity.
  - intros c e _ Hin; apply (condensation_out_exact EV g p r c e Hready) in Hin.
    destruct Hin as [v [j [_ [_ [_ [Htarget _]]]]]].
    change (In (scc_owner EV r (Graph.target g e)) (rev (component_ids r))).
    unfold scc_owner; rewrite Htarget.
    rewrite <- in_rev; eapply Hids; exact Htarget.
Qed.

Lemma condensation_edge_decreases {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) :
  ready EV g p ->
  (forall e i j, In (Graph.source g e) (Graph.nodes g) ->
    In e (Graph.out g (Graph.source g e)) ->
    Map.get EV (Graph.source g e) (comp_of r) = Some i ->
    Map.get EV (Graph.target g e) (comp_of r) = Some j -> (j <= i)%positive) ->
  forall c e, In e (Graph.out (condensation p r) c) ->
    (Graph.target (condensation p r) e < c)%positive.
Proof.
  intros Hready Hrank c e Hin; pose proof Hready as [Hwf _].
  apply (condensation_out_exact EV g p r c e Hready) in Hin.
  destruct Hin as [v [j [Hv [Hedge [Howner [Htarget Hne]]]]]].
  assert (Hsource : Graph.source g e = v) by (eapply out_source; eauto).
  assert (Hbound : (j <= c)%positive).
  { apply (Hrank e c j); rewrite ?Hsource; assumption. }
  change (scc_owner EV r (Graph.target g e) < c)%positive.
  unfold scc_owner; rewrite Htarget.
  apply Pos.le_lteq in Hbound; destruct Hbound as [Hlt|Heq]; [exact Hlt|contradiction].
Qed.

Lemma positive_path_decreases {E} (g : Graph.t positive E) v es w :
  (forall e, In e (Graph.out g (Graph.source g e)) ->
    (Graph.target g e < Graph.source g e)%positive) ->
  path g v es w -> es <> [] -> (w < v)%positive.
Proof.
  intros Hedges Hpath; induction Hpath as [v|e es w Hedge Hpath IH]; intro Hnonempty.
  - contradiction.
  - destruct es as [|a es].
    + inversion Hpath; subst w; apply Hedges; exact Hedge.
    + eapply Pos.lt_trans; [apply IH; discriminate|apply Hedges; exact Hedge].
Qed.

Lemma condensation_acyclic {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) :
  ready EV g p ->
  (forall e i j, In (Graph.source g e) (Graph.nodes g) ->
    In e (Graph.out g (Graph.source g e)) ->
    Map.get EV (Graph.source g e) (comp_of r) = Some i ->
    Map.get EV (Graph.target g e) (comp_of r) = Some j -> (j <= i)%positive) ->
  acyclic (condensation p r).
Proof.
  intros Hready Hrank v es _ Hpath; destruct es as [|e es]; [reflexivity|].
  exfalso; apply (Pos.lt_irrefl v).
  eapply positive_path_decreases; [|exact Hpath|discriminate].
  intros a Ha; eapply condensation_edge_decreases; eauto.
Qed.

Lemma condensation_topological {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : scc_result V) :
  ready EV g p -> scc_covers EV g r -> NoDup (component_ids r) ->
  (forall e i j, In (Graph.source g e) (Graph.nodes g) ->
    In e (Graph.out g (Graph.source g e)) ->
    Map.get EV (Graph.source g e) (comp_of r) = Some i ->
    Map.get EV (Graph.target g e) (comp_of r) = Some j -> (j <= i)%positive) ->
  (forall i j, In i (component_ids r) -> In j (component_ids r) ->
    (j < i)%positive -> before (rev (component_ids r)) i j) ->
  topological_order (condensation p r) (rev (component_ids r)).
Proof.
  intros Hready Hcovers Hnodup Hrank Horder.
  pose proof (condensation_wf EV g p r Hready Hcovers Hnodup) as Hwf.
  split; [apply NoDup_rev; exact Hnodup|].
  split; [intro v; reflexivity|].
  intros e Hsource Hedge; apply Horder.
  - change (In (Graph.source (condensation p r) e) (rev (component_ids r))) in Hsource.
    rewrite <- in_rev in Hsource; exact Hsource.
  - pose proof (out_target_in Hwf _ _ Hsource Hedge) as Htarget.
    change (In (Graph.target (condensation p r) e) (rev (component_ids r))) in Htarget.
    rewrite <- in_rev in Htarget; exact Htarget.
  - apply (condensation_edge_decreases EV g p r Hready Hrank); exact Hedge.
Qed.

(** * Completed traversals and region coverage *)

Lemma tarjan_run_low_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st n :
  ready EV g p -> tarjan_control g st -> tarjan_low_invariant EV (induced EV keep g) st ->
  tarjan_low_invariant EV (induced EV keep g) (tarjan_run p keep n st) /\
    tarjan_control g (tarjan_run p keep n st).
Proof.
  intros Hready Hcontrol Hinv; rewrite tarjan_run_agrees.
  induction n using Pos.peano_ind.
  - split; [apply tarjan_step_low_invariant|apply tarjan_step_control]; assumption.
  - rewrite Pos.iter_succ; destruct IHn as [Hstate Hstack].
    split; [apply tarjan_step_low_invariant|apply tarjan_step_control]; assumption.
Qed.

Lemma tarjan_root_low_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st v :
  ready EV g p -> tarjan_low_invariant EV (induced EV keep g) st ->
  frames st = [] -> In v (Graph.nodes g) ->
  tarjan_low_invariant EV (induced EV keep g) (tarjan_root p keep st v) /\
    frames (tarjan_root p keep st v) = [].
Proof.
  intros Hready Hinv Hempty Hv; split.
  - assert (Hpending : pending st = []).
    { apply (tarjan_pending_empty EV (induced EV keep g) st);
        [apply (tarjan_low_book _ _ _ Hinv)|apply (tarjan_low_links _ _ _ Hinv)|
         apply (tarjan_low_closed _ _ _ Hinv)|exact Hempty]. }
    unfold tarjan_root; destruct (Map.get EV v (disc st)) as [d|] eqn:Hfresh;
      [exact Hinv|].
    assert (Hstartcontrol : tarjan_control g (tarjan_discover p v st)).
    { intros f [Heq|Hin]; [subst f|rewrite Hempty in Hin; contradiction].
      split; [exact Hv|].
      destruct Hready as [_ [_ Hlaws]]; cbn [tarjan_discover frame_node frame_edges].
      rewrite (succ_agrees Hlaws _ Hv); intros e He; exact He. }
    assert (Hstartlow : tarjan_low_invariant EV (induced EV keep g)
      (tarjan_discover p v st)).
    { apply tarjan_discover_low_invariant; [exact Hinv|exact Hfresh|].
      intros w Hin; rewrite Hpending in Hin; contradiction. }
    exact (proj1 (tarjan_run_low_invariant EV g p keep (tarjan_discover p v st)
      (fuel p) Hready Hstartcontrol Hstartlow)).
  - apply (proj2 (tarjan_root_terminates EV g p keep st v Hready Hempty Hv)).
Qed.

Lemma tarjan_fold_low_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep roots st :
  ready EV g p -> incl roots (Graph.nodes g) ->
  tarjan_low_invariant EV (induced EV keep g) st -> frames st = [] ->
  tarjan_low_invariant EV (induced EV keep g) (fold_left (tarjan_root p keep) roots st) /\
    frames (fold_left (tarjan_root p keep) roots st) = [].
Proof.
  intros Hready; revert st; induction roots as [|v roots IH]; intros st Hin Hinv Hempty.
  - split; assumption.
  - cbn [fold_left]; destruct (tarjan_root_low_invariant EV g p keep st v Hready Hinv
      Hempty (Hin v (or_introl eq_refl))) as [Hstate Hframes].
    apply IH; [intros x Hx; apply Hin; right; exact Hx|exact Hstate|exact Hframes].
Qed.

Lemma tarjan_step_disc_extends {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st x d :
  Map.get EV x (disc st) = Some d ->
  Map.get EV x (disc (tarjan_step p keep st)) = Some d.
Proof.
  intro Hget; unfold tarjan_step; destruct (frames st) as [|[v [|e es]] rest];
    [exact Hget| |].
  - rewrite (proj2 (tarjan_close_control_fields EV v rest st)); exact Hget.
  - destruct (FinSet.mem EV (Graph.target g e) keep); [|exact Hget].
    destruct (Map.get EV (Graph.target g e) (disc st)) as [n|] eqn:Hfresh.
    + destruct (Map.get EV (Graph.target g e) (low st)); [|exact Hget].
      rewrite (proj2 (tarjan_lower_control_fields EV v n _)); exact Hget.
    + cbn [tarjan_discover disc]; rewrite Map.get_set_other; [exact Hget|].
      intro Heq; subst x; congruence.
Qed.

Lemma tarjan_run_disc_extends {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st n x d :
  Map.get EV x (disc st) = Some d ->
  Map.get EV x (disc (tarjan_run p keep n st)) = Some d.
Proof.
  intro Hget; rewrite tarjan_run_agrees; induction n using Pos.peano_ind.
  - apply tarjan_step_disc_extends; exact Hget.
  - rewrite Pos.iter_succ; apply tarjan_step_disc_extends; exact IHn.
Qed.

Lemma tarjan_root_disc_extends {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st v x d :
  Map.get EV x (disc st) = Some d ->
  Map.get EV x (disc (tarjan_root p keep st v)) = Some d.
Proof.
  intro Hget; unfold tarjan_root.
  destruct (Map.get EV v (disc st)) as [n|] eqn:Hfresh; [exact Hget|].
  apply tarjan_run_disc_extends; cbn [tarjan_discover disc].
  rewrite Map.get_set_other; [exact Hget|intro Heq; subst x; congruence].
Qed.

Lemma tarjan_root_discovers {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st v :
  exists d, Map.get EV v (disc (tarjan_root p keep st v)) = Some d.
Proof.
  unfold tarjan_root; destruct (Map.get EV v (disc st)) as [d|] eqn:Hfresh.
  - exists d; exact Hfresh.
  - exists (clock st); apply tarjan_run_disc_extends.
    cbn [tarjan_discover disc]; apply Map.get_set_same.
Qed.

Lemma tarjan_fold_disc_extends {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep roots st x d :
  Map.get EV x (disc st) = Some d ->
  Map.get EV x (disc (fold_left (tarjan_root p keep) roots st)) = Some d.
Proof.
  revert st; induction roots as [|v roots IH]; intros st Hget; [exact Hget|].
  cbn [fold_left]; apply IH; apply tarjan_root_disc_extends; exact Hget.
Qed.

Lemma tarjan_fold_discovers {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep roots st x :
  In x roots -> exists d, Map.get EV x (disc (fold_left (tarjan_root p keep) roots st)) = Some d.
Proof.
  revert st; induction roots as [|v roots IH]; intros st Hin; [contradiction|].
  cbn [fold_left]; destruct Hin as [Heq|Hin].
  - subst x; destruct (tarjan_root_discovers EV g p keep st v) as [d Hd].
    exists d; apply tarjan_fold_disc_extends; exact Hd.
  - apply IH; exact Hin.
Qed.

(** Every discovery belongs to the indexed region. *)
Definition tarjan_in_region {V E} (EV : encoding V) keep (st : tarjan_state V E) : Prop :=
  forall x d, Map.get EV x (disc st) = Some d -> FinSet.mem EV x keep = true.

Lemma tarjan_step_in_region {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st :
  tarjan_in_region EV keep st -> tarjan_in_region EV keep (tarjan_step p keep st).
Proof.
  intros Hinregion x d Hget; unfold tarjan_step in Hget.
  destruct (frames st) as [|[v [|e es]] rest]; [apply (Hinregion x d Hget)| |].
  - rewrite (proj2 (tarjan_close_control_fields EV v rest st)) in Hget.
    apply (Hinregion x d Hget).
  - destruct (FinSet.mem EV (Graph.target g e) keep) eqn:Hkeep;
      [|apply (Hinregion x d Hget)].
    destruct (Map.get EV (Graph.target g e) (disc st)) as [n|].
    + destruct (Map.get EV (Graph.target g e) (low st));
        [rewrite (proj2 (tarjan_lower_control_fields EV v n _)) in Hget|];
        apply (Hinregion x d Hget).
    + cbn [tarjan_discover disc] in Hget.
      destruct (dfs_eq_dec EV x (Graph.target g e)) as [Heq|Hne].
      * subst x; exact Hkeep.
      * rewrite Map.get_set_other in Hget by exact Hne; apply (Hinregion x d Hget).
Qed.

Lemma tarjan_run_in_region {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep n st :
  tarjan_in_region EV keep st -> tarjan_in_region EV keep (tarjan_run p keep n st).
Proof.
  intro Hregion; rewrite tarjan_run_agrees; induction n using Pos.peano_ind.
  - apply tarjan_step_in_region; exact Hregion.
  - rewrite Pos.iter_succ; apply tarjan_step_in_region; exact IHn.
Qed.

Lemma tarjan_root_in_region {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st v :
  tarjan_in_region EV keep st -> FinSet.mem EV v keep = true ->
  tarjan_in_region EV keep (tarjan_root p keep st v).
Proof.
  intros Hregion Hv; unfold tarjan_root.
  destruct (Map.get EV v (disc st)); [exact Hregion|].
  apply tarjan_run_in_region; intros x d Hget; cbn [tarjan_discover disc] in Hget.
  destruct (dfs_eq_dec EV x v) as [Heq|Hne]; [subst x; exact Hv|].
  rewrite Map.get_set_other in Hget by exact Hne; apply (Hregion x d Hget).
Qed.

Lemma tarjan_fold_in_region {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep roots st :
  tarjan_in_region EV keep st -> (forall v, In v roots -> FinSet.mem EV v keep = true) ->
  tarjan_in_region EV keep (fold_left (tarjan_root p keep) roots st).
Proof.
  revert st; induction roots as [|v roots IH]; intros st Hregion Hroots; [exact Hregion|].
  cbn [fold_left]; apply IH.
  - apply tarjan_root_in_region; [exact Hregion|apply Hroots; left; reflexivity].
  - intros w Hw; apply Hroots; right; exact Hw.
Qed.

Lemma tarjan_concat_rev_in {A} (xs : list (list A)) x :
  In x (concat (rev xs)) <-> In x (concat xs).
Proof.
  rewrite !in_concat; split; intros [c [Hc Hx]]; exists c; split; try exact Hx.
  - rewrite <- in_rev in Hc; exact Hc.
  - rewrite <- in_rev; exact Hc.
Qed.

Lemma scc_within_members {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region :
  ready EV g p -> incl region (Graph.nodes g) ->
  forall x, In x (concat (components (scc_within p region))) <-> In x region.
Proof.
  intros Hready Hregion x.
  destruct (tarjan_fold_low_invariant EV g p (FinSet.of_list EV region) region
    tarjan_initial Hready Hregion (tarjan_initial_low_invariant EV _) eq_refl)
    as [Hinv Hframes].
  assert (Hdomain : tarjan_in_region EV (FinSet.of_list EV region)
    (fold_left (tarjan_root p (FinSet.of_list EV region)) region tarjan_initial)).
  { apply tarjan_fold_in_region.
    - intros v d Hfalse; cbn [tarjan_initial disc] in Hfalse.
      rewrite Map.get_empty in Hfalse; discriminate.
    - intros v Hv; apply FinSet.of_list_spec; exact Hv. }
  remember (fold_left (tarjan_root p (FinSet.of_list EV region)) region tarjan_initial)
    as result eqn:Hresult.
  assert (Hpending : pending result = []).
  { apply (tarjan_pending_empty EV (induced EV (FinSet.of_list EV region) g) result);
      [apply (tarjan_low_book _ _ _ Hinv)|apply (tarjan_low_links _ _ _ Hinv)|
       apply (tarjan_low_closed _ _ _ Hinv)|exact Hframes]. }
  unfold scc_within; rewrite <- Hresult.
  cbn [tarjan_result components]; rewrite tarjan_concat_rev_in.
  split.
  - intro Hin; apply (proj1 (FinSet.of_list_spec EV x region)).
    assert (Hdisc : exists d, Map.get EV x (disc result) = Some d).
    { apply (tarjan_book_disc _ _ (tarjan_low_book _ _ _ Hinv)).
      rewrite Hpending; exact Hin. }
    destruct Hdisc as [d Hd]; exact (Hdomain x d Hd).
  - intro Hin.
    destruct (tarjan_fold_discovers EV g p (FinSet.of_list EV region) region
      tarjan_initial x Hin) as [d Hd].
    rewrite <- Hresult in Hd.
    pose proof (proj1 (tarjan_book_disc _ _ (tarjan_low_book _ _ _ Hinv) x)
      (ex_intro _ d Hd)) as Hnodes.
    rewrite Hpending in Hnodes; exact Hnodes.
Qed.

Lemma tarjan_combine_total_right {A B} (xs : list A) (ys : list B) y :
  length xs = length ys -> In y ys -> exists x, In (x, y) (combine xs ys).
Proof.
  revert xs; induction ys as [|b ys IH]; intros [|a xs] Hlength Hin;
    cbn [length] in Hlength; try discriminate; try contradiction.
  destruct Hin as [Heq|Hin].
  - subst b; exists a; left; reflexivity.
  - destruct (IH xs ltac:(lia) Hin) as [x Hx]; exists x; right; exact Hx.
Qed.

Lemma scc_covers_nodes {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  ready EV g p -> scc_covers EV g (scc p).
Proof.
  intro Hready.
  destruct (scc_within_indexes EV g p (Graph.nodes g))
    as [_ [_ [Hlength [Hat [_ [Howner _]]]]]].
  split.
  - intros x Hx; apply (scc_within_members EV g p (Graph.nodes g) Hready
      (fun _ H => H)) in Hx.
    apply in_concat in Hx; destruct Hx as [c [Hc Hmember]].
    destruct (tarjan_combine_total_right _ _ c Hlength Hc) as [i Hi].
    exists i; apply Howner; exists c; split; [apply Hat; exact Hi|exact Hmember].
  - intros x i Hget; apply Howner in Hget; destruct Hget as [c [Hc _]].
    apply Hat in Hc; eapply in_combine_l; exact Hc.
Qed.

Lemma scc_condensation_structure {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  ready EV g p ->
  graph_wf (condensation p (scc p)) /\
  (forall c, NoDup (Graph.out (condensation p (scc p)) c)) /\
  (forall c e, In e (Graph.out (condensation p (scc p)) c) <->
    exists x j, In x (Graph.nodes g) /\ In e (Graph.out g x) /\
      Map.get EV x (comp_of (scc p)) = Some c /\
      Map.get EV (Graph.target g e) (comp_of (scc p)) = Some j /\ j <> c) /\
  (forall c, In c (Graph.entries (condensation p (scc p))) <->
    exists s, In s (Graph.entries g) /\ Map.get EV s (comp_of (scc p)) = Some c) /\
  NoDup (Graph.entries (condensation p (scc p))) /\
  (forall e, In (Graph.source g e) (Graph.nodes g) -> In (Graph.target g e) (Graph.nodes g) ->
    exists i j, Map.get EV (Graph.source g e) (comp_of (scc p)) = Some i /\
      Map.get EV (Graph.target g e) (comp_of (scc p)) = Some j /\
      Graph.source (condensation p (scc p)) e = i /\
      Graph.target (condensation p (scc p)) e = j).
Proof.
  intro Hready; pose proof (scc_covers_nodes EV g p Hready) as Hcovers.
  destruct (scc_within_indexes EV g p (Graph.nodes g)) as [_ [_ [_ [_ [Hids _]]]]].
  split; [apply condensation_wf; assumption|].
  split; [intro c; apply condensation_out_nodup; exact Hready|].
  split; [intros c e; apply condensation_out_exact; exact Hready|].
  split; [intro c; apply condensation_entry_exact|].
  split; [apply condensation_entry_nodup|].
  intros e Hs Ht; apply condensation_endpoints; assumption.
Qed.

(** * The open-frame frontier *)

(** A newer pending lowlink is bounded either by this frame or by a still newer open frame. *)
Definition tarjan_frontier {V E} (EV : encoding V) (st : tarjan_state V E) : Prop :=
  forall a w da dw la lw, In a (map frame_node (frames st)) -> In w (pending st) ->
    Map.get EV a (disc st) = Some da -> Map.get EV w (disc st) = Some dw ->
    Map.get EV a (low st) = Some la -> Map.get EV w (low st) = Some lw ->
    (da <= dw)%positive ->
    (la <= lw)%positive \/
    exists b db lb, In b (map frame_node (frames st)) /\ (da < db)%positive /\
      (db <= dw)%positive /\ Map.get EV b (disc st) = Some db /\
      Map.get EV b (low st) = Some lb /\ (lb <= lw)%positive.

Lemma tarjan_frame_head_number {V E} (EV : encoding V) (st : tarjan_state V E)
    v es rest a da dv :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st ->
  frames st = TarjanFrame v es :: rest -> In a (map frame_node rest) ->
  Map.get EV a (disc st) = Some da -> Map.get EV v (disc st) = Some dv ->
  (da < dv)%positive.
Proof.
  intros Hbook Hnumbers Hframes Ha Had Hvd.
  apply (tarjan_pending_numbers EV st v a dv da Hnumbers); [|exact Hvd|exact Had].
  apply (tarjan_stack_before _ _ _ _ (tarjan_book_frames _ _ Hbook)).
  rewrite Hframes; apply dfs_before_cons; left; auto.
Qed.

Lemma tarjan_frontier_top {V E} (EV : encoding V) (st : tarjan_state V E)
    v es rest w dv dw lv lw :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_frontier EV st ->
  frames st = TarjanFrame v es :: rest -> In w (pending st) ->
  Map.get EV v (disc st) = Some dv -> Map.get EV w (disc st) = Some dw ->
  Map.get EV v (low st) = Some lv -> Map.get EV w (low st) = Some lw ->
  (dv <= dw)%positive -> (lv <= lw)%positive.
Proof.
  intros Hbook Hnumbers Hfrontier Hframes Hw Hvd Hwd Hvl Hwl Hbound.
  assert (Hv : In v (map frame_node (frames st))) by (rewrite Hframes; left; reflexivity).
  destruct (Hfrontier v w dv dw lv lw Hv Hw Hvd Hwd Hvl Hwl Hbound) as [Hle|Hnext];
    [exact Hle|].
  destruct Hnext as [b [db [lb [Hb [Hvb [_ [Hbd _]]]]]]].
  rewrite Hframes in Hb; cbn [map frame_node In] in Hb.
  destruct Hb as [Heq|Hb].
  - subst b; rewrite Hvd in Hbd; inversion Hbd; subst db.
    exfalso; exact (Pos.lt_irrefl _ Hvb).
  - pose proof (tarjan_frame_head_number EV st v es rest b db dv
      Hbook Hnumbers Hframes Hb Hbd Hvd) as Hbv.
    exfalso; exact (Pos.lt_irrefl _ (Pos.lt_trans _ _ _ Hvb Hbv)).
Qed.

(** An edge is unprocessed precisely when some open frame still contains it. *)
Definition tarjan_remaining {V E} (st : tarjan_state V E) (v : V) (e : E) : Prop :=
  exists f, In f (frames st) /\ frame_node f = v /\ In e (frame_edges f).

(** Every consumed edge has a visited target; a pending target bounds its source's lowlink. *)
Definition tarjan_examined {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) : Prop :=
  forall v e, In v (pending st) -> In e (Graph.out g v) ->
    tarjan_remaining st v e \/
    exists d, Map.get EV (Graph.target g e) (disc st) = Some d /\
      (In (Graph.target g e) (pending st) ->
        forall l, Map.get EV v (low st) = Some l -> (l <= d)%positive).

Lemma tarjan_close_remaining {V E} (EV : encoding V) (st : tarjan_state V E)
    v rest members tail links owners w e :
  tarjan_bookkeeping EV st -> frames st = TarjanFrame v [] :: rest ->
  tarjan_pop EV v (tarjan_next_id (emitted st)) (pending st) (low st)
    (comp_of (emitted st)) = (members, tail, links, owners) ->
  In w members -> ~ tarjan_remaining st w e.
Proof.
  intros Hbook Hframes Hpop Hw [f [Hf [Hnode Hedge]]].
  rewrite Hframes in Hf; destruct Hf as [Heq|Hf].
  - subst f; exact Hedge.
  - pose proof (tarjan_book_frames _ _ Hbook) as Hstack.
    rewrite Hframes in Hstack; cbn [map frame_node] in Hstack.
    destruct (tarjan_stack_head v _ _ Hstack) as [prefix [suffix [Hpending Hsuffix]]].
    assert (Hnot : ~ In v prefix).
    { intro Hin; pose proof (tarjan_book_distinct _ _ Hbook) as Hnodup.
      rewrite Hpending, <- app_assoc in Hnodup.
      apply (tarjan_nodup_disjoint prefix
        ((v :: suffix) ++ concat (components (emitted st))) Hnodup v Hin).
      left; reflexivity. }
    pose proof (tarjan_pop_prefix EV v (tarjan_next_id (emitted st)) prefix suffix
      (low st) (comp_of (emitted st)) Hnot) as Hsplit.
    rewrite <- Hpending, Hpop in Hsplit; cbn in Hsplit.
    destruct Hsplit as [Hmembers Htail]; subst suffix.
    assert (Hwtail : In w tail).
    { apply (tarjan_stack_member _ _ Hsuffix).
      rewrite <- Hnode; apply in_map; exact Hf. }
    pose proof (tarjan_pop_split EV v (tarjan_next_id (emitted st))
      (pending st) (low st) (comp_of (emitted st))) as Hsplit.
    rewrite Hpop in Hsplit; cbn in Hsplit; destruct Hsplit as [Hsplit _].
    pose proof (tarjan_book_distinct _ _ Hbook) as Hnodup.
    rewrite Hsplit, <- app_assoc in Hnodup.
    apply (tarjan_nodup_disjoint members
      (tail ++ concat (components (emitted st))) Hnodup w Hw).
    apply in_or_app; left; exact Hwtail.
Qed.

Lemma tarjan_pop_stack {V E} (EV : encoding V) (st : tarjan_state V E)
    v es rest members tail links owners :
  tarjan_bookkeeping EV st -> frames st = TarjanFrame v es :: rest ->
  tarjan_pop EV v (tarjan_next_id (emitted st)) (pending st) (low st)
    (comp_of (emitted st)) = (members, tail, links, owners) ->
  exists prefix, pending st = prefix ++ v :: tail /\ members = prefix ++ [v] /\
    tarjan_stack_order (map frame_node rest) tail.
Proof.
  intros Hbook Hframes Hpop.
  pose proof (tarjan_book_frames _ _ Hbook) as Hstack.
  rewrite Hframes in Hstack; cbn [map frame_node] in Hstack.
  destruct (tarjan_stack_head v _ _ Hstack) as [prefix [suffix [Hpending Hsuffix]]].
  assert (Hnot : ~ In v prefix).
  { intro Hin; pose proof (tarjan_book_distinct _ _ Hbook) as Hnodup.
    rewrite Hpending, <- app_assoc in Hnodup.
    apply (tarjan_nodup_disjoint prefix
      ((v :: suffix) ++ concat (components (emitted st))) Hnodup v Hin).
    left; reflexivity. }
  pose proof (tarjan_pop_prefix EV v (tarjan_next_id (emitted st)) prefix suffix
    (low st) (comp_of (emitted st)) Hnot) as Hsplit.
  rewrite <- Hpending, Hpop in Hsplit; cbn in Hsplit.
  destruct Hsplit as [Hmembers Htail]; subst suffix; exists prefix; auto.
Qed.

Lemma tarjan_popped_number {V E} (EV : encoding V) (st : tarjan_state V E)
    v es rest members tail links owners w dv dw :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st ->
  frames st = TarjanFrame v es :: rest ->
  tarjan_pop EV v (tarjan_next_id (emitted st)) (pending st) (low st)
    (comp_of (emitted st)) = (members, tail, links, owners) ->
  In w members -> Map.get EV v (disc st) = Some dv -> Map.get EV w (disc st) = Some dw ->
  (dv <= dw)%positive.
Proof.
  intros Hbook Hnumbers Hframes Hpop Hw Hvd Hwd.
  destruct (tarjan_pop_stack EV st v es rest members tail links owners Hbook Hframes Hpop)
    as [prefix [Hpending [Hmembers _]]].
  rewrite Hmembers, in_app_iff in Hw; destruct Hw as [Hw|[Heq|Hfalse]];
    [|subst w; rewrite Hvd in Hwd; inversion Hwd; apply Pos.le_refl|contradiction].
  apply Pos.lt_le_incl; apply (tarjan_pending_numbers EV st w v dw dv Hnumbers);
    [|exact Hwd|exact Hvd].
  rewrite Hpending; apply tarjan_before_cross; [exact Hw|left; reflexivity].
Qed.

Lemma tarjan_emission_strong {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v rest members tail links owners :
  tarjan_low_invariant EV g st -> frames st = TarjanFrame v [] :: rest ->
  tarjan_pop EV v (tarjan_next_id (emitted st)) (pending st) (low st)
    (comp_of (emitted st)) = (members, tail, links, owners) ->
  forall u w, In u members -> In w members -> mutual g u w.
Proof.
  intros Hinv Hframes Hpop.
  pose proof (tarjan_low_book _ _ _ Hinv) as Hbook.
  pose proof (tarjan_low_numbers _ _ _ Hinv) as Hnumbers.
  pose proof (tarjan_pop_split EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  rewrite Hpop in Hsplit; cbn in Hsplit; destruct Hsplit as [Hsplit Hroot].
  assert (Hv : In v (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); rewrite Hframes.
    left; reflexivity. }
  assert (Hvd : exists d, Map.get EV v (disc st) = Some d).
  { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hv. }
  destruct Hvd as [dv Hvd].
  assert (Hreach : forall w, In w members -> reaches g v w /\ reaches g w v).
  { intros w Hw; assert (Hwpending : In w (pending st)).
    { rewrite Hsplit; apply in_or_app; left; exact Hw. }
    assert (Hwd : exists d, Map.get EV w (disc st) = Some d).
    { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hwpending. }
    destruct Hwd as [dw Hwd]; split.
    - apply (tarjan_low_paths _ _ _ Hinv v w dv dw Hv Hwpending Hvd Hwd).
      apply (tarjan_popped_number EV st v [] rest members tail links owners w dv dw);
        assumption.
    - apply (tarjan_pending_current EV g st v [] rest);
        try assumption; [apply (tarjan_low_links _ _ _ Hinv)|
          apply (tarjan_low_closed _ _ _ Hinv)|apply (tarjan_low_paths _ _ _ Hinv)]. }
  intros u w Hu Hw; destruct (Hreach u Hu) as [Hvu Huv], (Hreach w Hw) as [Hvw Hwv].
  split; eapply tarjan_reaches_trans; eauto.
Qed.

Lemma tarjan_emission_closed {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v rest members tail links owners d :
  tarjan_low_invariant EV g st -> tarjan_frontier EV st -> tarjan_examined EV g st ->
  frames st = TarjanFrame v [] :: rest ->
  Map.get EV v (disc st) = Some d -> Map.get EV v (low st) = Some d ->
  tarjan_pop EV v (tarjan_next_id (emitted st)) (pending st) (low st)
    (comp_of (emitted st)) = (members, tail, links, owners) ->
  forall w e, In w members -> In e (Graph.out g w) ->
    In (Graph.target g e) members \/ In (Graph.target g e) (concat (components (emitted st))).
Proof.
  intros Hinv Hfrontier Hexamined Hframes Hvd Hvl Hpop w e Hw Hedge.
  pose proof (tarjan_low_book _ _ _ Hinv) as Hbook.
  pose proof (tarjan_low_numbers _ _ _ Hinv) as Hnumbers.
  pose proof (tarjan_pop_split EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  rewrite Hpop in Hsplit; cbn in Hsplit; destruct Hsplit as [Hsplit Hroot].
  assert (Hwpending : In w (pending st)) by (rewrite Hsplit; apply in_or_app; left; exact Hw).
  destruct (Hexamined w e Hwpending Hedge) as [Hremaining|[dt [Htarget Hbound]]].
  - exfalso; apply (tarjan_close_remaining EV st v rest members tail links owners w e);
      assumption.
  - pose proof (proj1 (tarjan_book_disc _ _ Hbook (Graph.target g e))
      (ex_intro _ dt Htarget)) as Hvisited.
    apply in_app_iff in Hvisited; destruct Hvisited as [Hpending|Hblack]; [|right; exact Hblack].
    rewrite Hsplit, in_app_iff in Hpending; destruct Hpending as [Hmember|Htail];
      [left; exact Hmember|].
    exfalso.
    destruct (proj2 (tarjan_book_low _ _ Hbook w) Hwpending) as [lw Hwl].
    destruct (tarjan_low_links _ _ _ Hinv w lw Hwl) as [dw [x [Hwd _]]].
    assert (Hvw : (d <= dw)%positive).
    { apply (tarjan_popped_number EV st v [] rest members tail links owners w d dw);
        assumption. }
    assert (Hlowbound : (d <= lw)%positive).
    { apply (tarjan_frontier_top EV st v [] rest w d dw d lw); assumption. }
    assert (Htargetpending : In (Graph.target g e) (pending st)).
    { rewrite Hsplit; apply in_or_app; right; exact Htail. }
    specialize (Hbound Htargetpending lw Hwl).
    assert (Hstrict : (dt < d)%positive).
    { apply (tarjan_pending_numbers EV st v (Graph.target g e) d dt Hnumbers);
        [|exact Hvd|exact Htarget].
      rewrite Hsplit; apply tarjan_before_cross; [|exact Htail].
      apply Hroot; apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)).
      rewrite Hframes; left; reflexivity. }
    exact (Pos.lt_irrefl _ (Pos.lt_le_trans _ _ _ Hstrict
      (Pos.le_trans _ _ _ Hlowbound Hbound))).
Qed.

Lemma tarjan_low_set_bound {V} (EV : encoding V) links v old n b lb :
  Map.get EV v links = Some old -> Map.get EV b links = Some lb ->
  exists lb', Map.get EV b (Map.set EV v (Pos.min old n) links) = Some lb' /\
    (lb' <= lb)%positive.
Proof.
  intros Hold Hb; destruct (dfs_eq_dec EV b v) as [Heq|Hne].
  - subst b; rewrite Hold in Hb; inversion Hb; subst lb.
    exists (Pos.min old n); rewrite Map.get_set_same; split; [reflexivity|apply Pos.le_min_l].
  - exists lb; rewrite Map.get_set_other by exact Hne; split; [exact Hb|apply Pos.le_refl].
Qed.

Lemma tarjan_lower_frontier {V E} (EV : encoding V) (st : tarjan_state V E)
    v es rest n :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_frontier EV st ->
  frames st = TarjanFrame v es :: rest -> tarjan_frontier EV (tarjan_lower EV v n st).
Proof.
  intros Hbook Hnumbers Hfrontier Hframes; unfold tarjan_lower.
  destruct (Map.get EV v (low st)) as [old|] eqn:Hold; [|exact Hfrontier].
  intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [frames pending disc low] in Ha, Hw, Had, Hwd, Hal, Hwl.
  cbn [frames disc low].
  destruct (dfs_eq_dec EV w v) as [Hwv|Hwne].
  - subst w; rewrite Map.get_set_same in Hwl; inversion Hwl; subst lw.
    destruct (dfs_eq_dec EV a v) as [Hav|Hane].
    + subst a; rewrite Map.get_set_same in Hal; inversion Hal; subst la.
      left; apply Pos.le_refl.
    + right; exists v, dw, (Pos.min old n); split.
      * rewrite Hframes; left; reflexivity.
      * split.
        -- apply (tarjan_frame_head_number EV st v es rest a da dw Hbook Hnumbers
             Hframes); [|exact Had|exact Hwd].
           rewrite Hframes in Ha; cbn [map frame_node In] in Ha.
           destruct Ha as [Heq|Ha]; [congruence|exact Ha].
        -- split; [apply Pos.le_refl|]; split; [exact Hwd|].
           rewrite Map.get_set_same; split; [reflexivity|apply Pos.le_refl].
  - rewrite Map.get_set_other in Hwl by exact Hwne.
    destruct (dfs_eq_dec EV a v) as [Hav|Hane].
    + subst a; rewrite Map.get_set_same in Hal; inversion Hal; subst la; left.
      eapply Pos.le_trans; [apply Pos.le_min_l|].
      apply (tarjan_frontier_top EV st v es rest w da dw old lw); assumption.
    + rewrite Map.get_set_other in Hal by exact Hane.
      destruct (Hfrontier a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound) as [Hle|Hnext];
        [left; exact Hle|].
      destruct Hnext as [b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]].
      destruct (tarjan_low_set_bound EV (low st) v old n b lb Hold Hbl)
        as [lb' [Hbl' Hle']].
      right; exists b, db, lb'; split; [exact Hb|]; split; [exact Hab|].
      split; [exact Hbw|]; split; [exact Hbd|]; split; [exact Hbl'|].
      eapply Pos.le_trans; eauto.
Qed.

Lemma tarjan_fresh_frame {V E} (EV : encoding V) (st : tarjan_state V E) v :
  tarjan_bookkeeping EV st -> Map.get EV v (disc st) = None ->
  ~ In v (map frame_node (frames st)).
Proof.
  intros Hbook Hfresh Hin; apply (tarjan_fresh_pending EV st v Hbook Hfresh).
  apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); exact Hin.
Qed.

Lemma tarjan_discover_frontier {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v st :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_frontier EV st ->
  Map.get EV v (disc st) = None -> tarjan_frontier EV (tarjan_discover p v st).
Proof.
  intros Hbook [history [Hnumbers Hpending]] Hfrontier Hfresh.
  intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [tarjan_discover frames pending disc low map frame_node In] in
    Ha, Hw, Had, Hwd, Hal, Hwl.
  cbn [tarjan_discover frames disc low map frame_node].
  destruct Hw as [Hwv|Hw], Ha as [Hav|Ha].
  - subst a w; rewrite Map.get_set_same in Hal, Hwl; inversion Hal; inversion Hwl; subst.
    left; apply Pos.le_refl.
  - subst w; rewrite Map.get_set_same in Hwd, Hwl; inversion Hwd; inversion Hwl;
      subst dw lw.
    assert (Hane : a <> v).
    { intro Heq; subst a; exact (tarjan_fresh_frame EV st v Hbook Hfresh Ha). }
    rewrite Map.get_set_other in Had by exact Hane.
    right; exists v, (clock st), (clock st); split; [left; reflexivity|].
    split; [eapply dfs_numbering_bound; eauto|]; split; [apply Pos.le_refl|].
    rewrite !Map.get_set_same; split; [reflexivity|].
    split; [reflexivity|apply Pos.le_refl].
  - subst a; rewrite Map.get_set_same in Had; inversion Had; subst da.
    assert (Hwne : w <> v).
    { intro Heq; subst w; exact (tarjan_fresh_pending EV st v Hbook Hfresh Hw). }
    rewrite Map.get_set_other in Hwd by exact Hwne.
    pose proof (dfs_numbering_bound EV _ _ _ Hnumbers w dw Hwd) as Hstrict.
    exfalso; exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hbound Hstrict)).
  - assert (Hwne : w <> v).
    { intro Heq; subst w; exact (tarjan_fresh_pending EV st v Hbook Hfresh Hw). }
    assert (Hane : a <> v).
    { intro Heq; subst a; exact (tarjan_fresh_frame EV st v Hbook Hfresh Ha). }
    rewrite Map.get_set_other in Had, Hal by exact Hane.
    rewrite Map.get_set_other in Hwd, Hwl by exact Hwne.
    destruct (Hfrontier a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound) as [Hle|Hnext];
      [left; exact Hle|].
    destruct Hnext as [b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]].
    assert (Hbne : b <> v).
    { intro Heq; subst b; exact (tarjan_fresh_frame EV st v Hbook Hfresh Hb). }
    right; exists b, db, lb; split; [right; exact Hb|].
    rewrite !Map.get_set_other by exact Hbne; auto.
Qed.

Lemma tarjan_nodup_prefix {A} (xs ys : list A) :
  NoDup (xs ++ ys) -> NoDup xs.
Proof.
  induction xs as [|x xs IH]; intro Hnodup; [constructor|].
  inversion Hnodup as [|head tail Hnot Htail]; subst; constructor.
  - intro Hin; apply Hnot; apply in_or_app; left; exact Hin.
  - apply IH; exact Htail.
Qed.

Lemma tarjan_pop_tail_links {V} (EV : encoding V) root i xs links owners
    members tail links' owners' x :
  NoDup xs -> tarjan_pop EV root i xs links owners = (members, tail, links', owners') ->
  In x tail -> Map.get EV x links' = Map.get EV x links.
Proof.
  intros Hnodup Hpop Hx.
  pose proof (tarjan_pop_split EV root i xs links owners) as Hsplit.
  pose proof (tarjan_pop_links EV root i xs links owners x) as Hlinks.
  rewrite Hpop in Hsplit, Hlinks; cbn in Hsplit, Hlinks; destruct Hsplit as [Hsplit _].
  rewrite Hlinks.
  destruct (existsb (fun v => Pos.eqb (encode EV x) (encode EV v)) members) eqn:Hmem;
    [|reflexivity].
  apply tarjan_member_spec in Hmem; rewrite Hsplit in Hnodup.
  exfalso; exact (tarjan_nodup_disjoint members tail Hnodup x Hmem Hx).
Qed.

Lemma tarjan_pop_tail_owners {V} (EV : encoding V) root i xs links owners
    members tail links' owners' x :
  NoDup xs -> tarjan_pop EV root i xs links owners = (members, tail, links', owners') ->
  In x tail -> Map.get EV x owners' = Map.get EV x owners.
Proof.
  intros Hnodup Hpop Hx.
  pose proof (tarjan_pop_split EV root i xs links owners) as Hsplit.
  pose proof (tarjan_pop_owners EV root i xs links owners x) as Howners.
  rewrite Hpop in Hsplit, Howners; cbn in Hsplit, Howners; destruct Hsplit as [Hsplit _].
  rewrite Howners.
  destruct (existsb (fun v => Pos.eqb (encode EV x) (encode EV v)) members) eqn:Hmem;
    [|reflexivity].
  apply tarjan_member_spec in Hmem; rewrite Hsplit in Hnodup.
  exfalso; exact (tarjan_nodup_disjoint members tail Hnodup x Hmem Hx).
Qed.

Lemma tarjan_close_emit_frontier {V E} (EV : encoding V) (st : tarjan_state V E)
    v es rest :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_frontier EV st ->
  frames st = TarjanFrame v es :: rest ->
  tarjan_frontier EV (tarjan_emit EV v
    (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))).
Proof.
  intros Hbook Hnumbers Hfrontier Hframes.
  unfold tarjan_emit; cbn [pending low emitted comp_of].
  destruct (tarjan_pop EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st)))
    as [[[members tail] links] owners] eqn:Hpop.
  destruct (tarjan_pop_stack EV st v es rest members tail links owners Hbook Hframes Hpop)
    as [prefix [Hpending [Hmembers Hrest]]].
  assert (Hnodup : NoDup (pending st)).
  { apply (tarjan_nodup_prefix _ (concat (components (emitted st)))).
    apply (tarjan_book_distinct _ _ Hbook). }
  assert (Htail : forall x, In x tail -> Map.get EV x links = Map.get EV x (low st)).
  { intros x Hx; eapply tarjan_pop_tail_links; eauto. }
  intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [frames pending disc low] in Ha, Hw, Had, Hwd, Hal, Hwl |- *.
  assert (Hatail : In a tail) by (apply (tarjan_stack_member _ _ Hrest); exact Ha).
  rewrite Htail in Hal, Hwl by assumption.
  assert (Haold : In a (map frame_node (frames st))).
  { rewrite Hframes; right; exact Ha. }
  assert (Hwold : In w (pending st)).
  { rewrite Hpending; apply in_or_app; right; right; exact Hw. }
  destruct (Hfrontier a w da dw la lw Haold Hwold Had Hwd Hal Hwl Hbound) as [Hle|Hnext];
    [left; exact Hle|].
  destruct Hnext as [b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]].
  rewrite Hframes in Hb; cbn [map frame_node In] in Hb; destruct Hb as [Heq|Hb].
  - subst b; assert (Hstrict : (dw < db)%positive).
    { apply (tarjan_pending_numbers EV st v w db dw Hnumbers); [|exact Hbd|exact Hwd].
      rewrite Hpending; apply tarjan_before_prefix; apply dfs_before_cons; left; auto. }
    exfalso; exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hbw Hstrict)).
  - right; exists b, db, lb; split; [exact Hb|]; split; [exact Hab|].
    split; [exact Hbw|]; split; [exact Hbd|]; split; [|exact Hle].
    rewrite Htail; [exact Hbl|apply (tarjan_stack_member _ _ Hrest); exact Hb].
Qed.

Lemma tarjan_low_set_inverse_bound {V} (EV : encoding V) links v old n a la :
  Map.get EV v links = Some old ->
  Map.get EV a (Map.set EV v (Pos.min old n) links) = Some la ->
  exists la0, Map.get EV a links = Some la0 /\ (la <= la0)%positive.
Proof.
  intros Hold Ha; destruct (dfs_eq_dec EV a v) as [Heq|Hne].
  - subst a; rewrite Map.get_set_same in Ha; inversion Ha; subst la.
    exists old; split; [exact Hold|apply Pos.le_min_l].
  - rewrite Map.get_set_other in Ha by exact Hne; exists la; auto using Pos.le_refl.
Qed.

Lemma tarjan_frontier_self {V E} (EV : encoding V) (st : tarjan_state V E)
    head rest links a da dh la lh :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> frames st = head :: rest ->
  In a (map frame_node (frames st)) ->
  Map.get EV a (disc st) = Some da -> Map.get EV (frame_node head) (disc st) = Some dh ->
  Map.get EV a links = Some la -> Map.get EV (frame_node head) links = Some lh ->
  (la <= lh)%positive \/ exists b db lb, In b (map frame_node (frames st)) /\
    (da < db)%positive /\ (db <= dh)%positive /\ Map.get EV b (disc st) = Some db /\
    Map.get EV b links = Some lb /\ (lb <= lh)%positive.
Proof.
  intros Hbook Hnumbers Hframes Ha Had Hhd Hal Hhl.
  destruct head as [v es]; cbn [frame_node] in Hhd, Hhl.
  destruct (dfs_eq_dec EV a v) as [Heq|Hne].
  - subst a; rewrite Hhl in Hal; inversion Hal; left; apply Pos.le_refl.
  - right; exists v, dh, lh; split; [rewrite Hframes; left; reflexivity|].
    split.
    + apply (tarjan_frame_head_number EV st v es rest a da dh Hbook Hnumbers Hframes);
        [|exact Had|exact Hhd].
      rewrite Hframes in Ha; cbn [map frame_node In] in Ha.
      destruct Ha as [Heq|Ha]; [congruence|exact Ha].
    + split; [apply Pos.le_refl|]; split; [exact Hhd|]; split; [exact Hhl|apply Pos.le_refl].
Qed.

Lemma tarjan_parent_frontier_witness {V E} (EV : encoding V) (st : tarjan_state V E)
    v es parent rest a da dp db dw lp l lw :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st ->
  frames st = TarjanFrame v es :: parent :: rest ->
  In a (map frame_node (parent :: rest)) -> a <> frame_node parent ->
  Map.get EV a (disc st) = Some da -> Map.get EV (frame_node parent) (disc st) = Some dp ->
  Map.get EV v (disc st) = Some db -> (db <= dw)%positive -> (l <= lw)%positive ->
  exists b db' lb', In b (map frame_node (parent :: rest)) /\ (da < db')%positive /\
    (db' <= dw)%positive /\ Map.get EV b (disc st) = Some db' /\
    Map.get EV b (Map.set EV (frame_node parent) (Pos.min lp l) (low st)) = Some lb' /\
    (lb' <= lw)%positive.
Proof.
  intros Hbook Hnumbers Hframes Ha Hane Had Hpd Hvd Hbw Hle.
  exists (frame_node parent), dp, (Pos.min lp l); split; [left; reflexivity|]; split.
  - apply (tarjan_pending_numbers EV st (frame_node parent) a dp da Hnumbers);
      [|exact Hpd|exact Had].
    apply (tarjan_stack_before _ _ _ _ (tarjan_book_frames _ _ Hbook)).
    rewrite Hframes; apply dfs_before_cons; right; apply dfs_before_cons; left.
    split; [reflexivity|]; cbn [map In] in Ha; destruct Ha as [Heq|Ha]; [congruence|exact Ha].
  - split.
    + eapply Pos.le_trans; [|exact Hbw]; apply Pos.lt_le_incl.
      apply (tarjan_frame_head_number EV st v es (parent :: rest)
        (frame_node parent) dp db Hbook Hnumbers Hframes);
        [left; reflexivity|exact Hpd|exact Hvd].
    + split; [exact Hpd|]; rewrite Map.get_set_same; split; [reflexivity|].
      eapply Pos.le_trans; [apply Pos.le_min_r|exact Hle].
Qed.

Lemma tarjan_close_lower_frontier {V E} (EV : encoding V) (st : tarjan_state V E)
    v es parent rest l :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_frontier EV st ->
  frames st = TarjanFrame v es :: parent :: rest -> Map.get EV v (low st) = Some l ->
  tarjan_frontier EV (tarjan_lower EV (frame_node parent) l
    (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st) (emitted st))).
Proof.
  intros Hbook Hnumbers Hfrontier Hframes Hvl.
  assert (Hp : In (frame_node parent) (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); rewrite Hframes.
    right; left; reflexivity. }
  destruct (proj2 (tarjan_book_low _ _ Hbook _) Hp) as [lp Hpl].
  assert (Hpd : exists dp, Map.get EV (frame_node parent) (disc st) = Some dp).
  { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hp. }
  destruct Hpd as [dp Hpd].
  pose proof (tarjan_drop_bookkeeping EV st (TarjanFrame v es) (parent :: rest)
    Hbook Hframes) as Hclosedbook.
  pose proof (tarjan_reframe_numbered EV st (parent :: rest) Hnumbers) as Hclosednumbers.
  unfold tarjan_lower; cbn [low]; rewrite Hpl.
  intros a w da dw la lw Ha Hw Had Hwd Hal Hwl Hbound.
  cbn [frames pending disc low] in Ha, Hw, Had, Hwd, Hal, Hwl |- *.
  destruct (dfs_eq_dec EV w (frame_node parent)) as [Heq|Hwne].
  - subst w; exact (tarjan_frontier_self EV _ parent rest _ a da dw la lw
      Hclosedbook Hclosednumbers eq_refl Ha Had Hwd Hal Hwl).
  - rewrite Map.get_set_other in Hwl by exact Hwne.
    destruct (tarjan_low_set_inverse_bound EV (low st) (frame_node parent) lp l a la
      Hpl Hal) as [la0 [Hal0 Hla]].
    assert (Haold : In a (map frame_node (frames st))) by (rewrite Hframes; right; exact Ha).
    destruct (Hfrontier a w da dw la0 lw Haold Hw Had Hwd Hal0 Hwl Hbound)
      as [Hle|Hnext].
    + left; eapply Pos.le_trans; eauto.
    + destruct Hnext as [b [db [lb [Hb [Hab [Hbw [Hbd [Hbl Hle]]]]]]]].
      rewrite Hframes in Hb; cbn [map frame_node In] in Hb; destruct Hb as [Heq|Hb].
      * subst b; rewrite Hvl in Hbl; inversion Hbl; subst lb.
        destruct (dfs_eq_dec EV a (frame_node parent)) as [Heq|Hane].
        -- subst a; rewrite Map.get_set_same in Hal; inversion Hal; subst la.
           left; eapply Pos.le_trans; [apply Pos.le_min_r|exact Hle].
        -- right; apply (tarjan_parent_frontier_witness EV st v es parent rest a
             da dp db dw lp l lw); assumption.
      * destruct (tarjan_low_set_bound EV (low st) (frame_node parent) lp l b lb Hpl Hbl)
          as [lb' [Hbl' Hlb']].
        right; exists b, db, lb'; split; [exact Hb|]; split; [exact Hab|].
        split; [exact Hbw|]; split; [exact Hbd|]; split; [exact Hbl'|].
        eapply Pos.le_trans; eauto.
Qed.

Lemma tarjan_reframe_frontier {V E} (EV : encoding V) (st : tarjan_state V E)
    (stack : list (tarjan_frame V E)) :
  tarjan_frontier EV st -> map frame_node stack = map frame_node (frames st) ->
  tarjan_frontier EV
    (TarjanState stack (disc st) (low st) (pending st) (clock st) (emitted st)).
Proof.
  intros Hfrontier Hsame; unfold tarjan_frontier in *; cbn; rewrite Hsame; exact Hfrontier.
Qed.

Lemma tarjan_close_frontier {V E} (EV : encoding V) (st : tarjan_state V E) v es rest :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_frontier EV st ->
  frames st = TarjanFrame v es :: rest -> tarjan_frontier EV (tarjan_close EV v rest st).
Proof.
  intros Hbook Hnumbers Hfrontier Hframes.
  assert (Hv : In v (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); rewrite Hframes.
    left; reflexivity. }
  destruct (proj2 (tarjan_book_low _ _ Hbook v) Hv) as [l Hlink].
  assert (Hdisc : exists d, Map.get EV v (disc st) = Some d).
  { apply (tarjan_book_disc _ _ Hbook); apply in_or_app; left; exact Hv. }
  destruct Hdisc as [d Hdisc]; unfold tarjan_close; rewrite Hlink, Hdisc.
  destruct (Pos.eqb l d).
  - apply (tarjan_close_emit_frontier EV st v es rest); assumption.
  - destruct rest as [|parent rest].
    + intros a w da dw la lw Hfalse; contradiction.
    + apply (tarjan_close_lower_frontier EV st v es parent rest l); assumption.
Qed.

Lemma tarjan_step_frontier {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st :
  tarjan_bookkeeping EV st -> tarjan_numbered EV st -> tarjan_frontier EV st ->
  tarjan_frontier EV (tarjan_step p keep st).
Proof.
  intros Hbook Hnumbers Hfrontier; unfold tarjan_step.
  destruct (frames st) as [|[v [|e es]] rest] eqn:Hframes; [exact Hfrontier| |].
  - apply (tarjan_close_frontier EV st v [] rest); assumption.
  - assert (Hstack : map frame_node (TarjanFrame v es :: rest) =
      map frame_node (frames st)) by (rewrite Hframes; reflexivity).
    assert (Hadvanced : tarjan_frontier EV
      (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))).
    { apply tarjan_reframe_frontier; assumption. }
    assert (Hbook' : tarjan_bookkeeping EV
      (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))).
    { apply tarjan_reframe_bookkeeping; [exact Hbook|].
      rewrite Hstack; apply (tarjan_book_frames _ _ Hbook). }
    assert (Hnumbers' : tarjan_numbered EV
      (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))).
    { apply tarjan_reframe_numbered; exact Hnumbers. }
    destruct (FinSet.mem EV (Graph.target g e) keep); [|exact Hadvanced].
    destruct (Map.get EV (Graph.target g e) (disc st)) as [d|] eqn:Hfresh.
    + destruct (Map.get EV (Graph.target g e) (low st)); [|exact Hadvanced].
      apply (tarjan_lower_frontier EV _ v es rest d); try assumption; reflexivity.
    + apply tarjan_discover_frontier; assumption.
Qed.

(** * Processed-edge preservation *)

Lemma tarjan_lower_examined {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v n :
  tarjan_examined EV g st -> tarjan_examined EV g (tarjan_lower EV v n st).
Proof.
  intro Hexamined; unfold tarjan_lower.
  destruct (Map.get EV v (low st)) as [old|] eqn:Hold; [|exact Hexamined].
  intros w e Hw Hedge; destruct (Hexamined w e Hw Hedge) as [Hremaining|[d [Hd Hbound]]].
  - left; exact Hremaining.
  - right; exists d; split; [exact Hd|].
    intros Htarget l Hlink; cbn [low] in Hlink.
    destruct (tarjan_low_set_inverse_bound EV (low st) v old n w l Hold Hlink)
      as [l0 [Hlink0 Hle]].
    eapply Pos.le_trans; [exact Hle|apply (Hbound Htarget l0 Hlink0)].
Qed.

Lemma tarjan_discover_examined {V E} (EV : encoding V) (g h : Graph.t V E)
    (p : prepared EV g) v st :
  tarjan_bookkeeping EV st -> tarjan_examined EV h st ->
  Map.get EV v (disc st) = None -> incl (Graph.out h v) (succ_edges p v) ->
  tarjan_examined EV h (tarjan_discover p v st).
Proof.
  intros Hbook Hexamined Hfresh Hedges w e Hw Hedge.
  cbn [tarjan_discover pending In] in Hw; destruct Hw as [Heq|Hw].
  - subst w; left; exists (TarjanFrame v (succ_edges p v)); split; [left; reflexivity|].
    split; [reflexivity|apply Hedges; exact Hedge].
  - destruct (Hexamined w e Hw Hedge) as [[f [Hf [Hnode Hremaining]]]|[d [Hd Hbound]]].
    + left; exists f; split; [right; exact Hf|]; auto.
    + right; exists d.
      assert (Htargetne : Graph.target h e <> v).
      { intro Heq; rewrite Heq, Hfresh in Hd; discriminate. }
      assert (Hwne : w <> v).
      { intro Heq; subst w; exact (tarjan_fresh_pending EV st v Hbook Hfresh Hw). }
      cbn [tarjan_discover disc]; rewrite Map.get_set_other by exact Htargetne.
      split; [exact Hd|]; intros Htarget l Hlink.
      cbn [tarjan_discover low] in Hlink; rewrite Map.get_set_other in Hlink by exact Hwne.
      cbn [tarjan_discover pending In] in Htarget.
      destruct Htarget as [Heq|Htarget]; [congruence|exact (Hbound Htarget l Hlink)].
Qed.

Lemma tarjan_consume_examined {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) prefix v e es rest :
  tarjan_examined EV g st -> frames st = prefix ++ TarjanFrame v (e :: es) :: rest ->
  (In e (Graph.out g v) -> exists d, Map.get EV (Graph.target g e) (disc st) = Some d /\
    (In (Graph.target g e) (pending st) ->
      forall l, Map.get EV v (low st) = Some l -> (l <= d)%positive)) ->
  tarjan_examined EV g
    (TarjanState (prefix ++ TarjanFrame v es :: rest) (disc st) (low st)
      (pending st) (clock st) (emitted st)).
Proof.
  intros Hexamined Hframes Hconsumed w a Hw Hedge.
  destruct (Hexamined w a Hw Hedge) as [[f [Hf [Hnode Ha]]]|Hdone]; [|right; exact Hdone].
  rewrite Hframes, in_app_iff in Hf; destruct Hf as [Hf|[Heq|Hf]].
  - left; exists f; split; [apply in_or_app; left; exact Hf|]; auto.
  - subst f; cbn [frame_node frame_edges] in Hnode, Ha; subst w.
    destruct Ha as [Heq|Ha].
    + subst a; right; apply Hconsumed; exact Hedge.
    + left; exists (TarjanFrame v es); split; [apply in_or_app; right; left; reflexivity|].
      split; [reflexivity|exact Ha].
  - left; exists f; split; [apply in_or_app; right; right; exact Hf|]; auto.
Qed.

Lemma tarjan_empty_frame_examined {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v rest :
  tarjan_examined EV g st -> frames st = TarjanFrame v [] :: rest ->
  tarjan_examined EV g
    (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)).
Proof.
  intros Hexamined Hframes w e Hw Hedge.
  destruct (Hexamined w e Hw Hedge) as [[f [Hf [Hnode He]]]|Hdone]; [|right; exact Hdone].
  rewrite Hframes in Hf; destruct Hf as [Heq|Hf].
  - subst f; cbn [frame_edges In] in He; contradiction.
  - left; exists f; auto.
Qed.

Lemma tarjan_emit_examined {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) root :
  tarjan_examined EV g st -> tarjan_examined EV g (tarjan_emit EV root st).
Proof.
  intro Hexamined.
  pose proof (tarjan_pop_split EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  pose proof (tarjan_pop_links EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hlinks.
  unfold tarjan_emit; destruct (tarjan_pop EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as [[[members tail] links] owners].
  cbn in Hsplit, Hlinks; destruct Hsplit as [Hsplit _].
  intros w e Hw Hedge; cbn [pending] in Hw.
  assert (Hwold : In w (pending st)) by (rewrite Hsplit; apply in_or_app; right; exact Hw).
  destruct (Hexamined w e Hwold Hedge) as [Hremaining|[d [Hd Hbound]]];
    [left; exact Hremaining|].
  right; exists d; split; [exact Hd|].
  intros Htarget l Hlink; cbn [low] in Hlink; rewrite Hlinks in Hlink.
  destruct (existsb (fun v => Pos.eqb (encode EV w) (encode EV v)) members);
    [discriminate|].
  apply Hbound with (l := l); [|exact Hlink].
  rewrite Hsplit; apply in_or_app; right; exact Htarget.
Qed.

Lemma tarjan_close_examined {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v rest :
  tarjan_examined EV g st -> frames st = TarjanFrame v [] :: rest ->
  tarjan_examined EV g (tarjan_close EV v rest st).
Proof.
  intros Hexamined Hframes.
  pose proof (tarjan_empty_frame_examined EV g st v rest Hexamined Hframes) as Hclosed.
  unfold tarjan_close; destruct (Map.get EV v (low st)) as [l|],
    (Map.get EV v (disc st)) as [d|]; try exact Hclosed.
  destruct (Pos.eqb l d); [apply tarjan_emit_examined; exact Hclosed|].
  destruct rest as [|parent rest]; [exact Hclosed|].
  apply tarjan_lower_examined; exact Hclosed.
Qed.

Lemma tarjan_skip_examined {V E} (EV : encoding V) (g : Graph.t V E) keep
    (st : tarjan_state V E) v e es rest :
  tarjan_examined EV (induced EV keep g) st ->
  frames st = TarjanFrame v (e :: es) :: rest ->
  FinSet.mem EV (Graph.target g e) keep = false ->
  tarjan_examined EV (induced EV keep g)
    (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
      (pending st) (clock st) (emitted st)).
Proof.
  intros Hexamined Hframes Hkeep.
  apply (tarjan_consume_examined EV _ st [] v e es rest Hexamined Hframes).
  intro Hedge; apply filter_In in Hedge; destruct Hedge as [_ Htrue]; congruence.
Qed.

Lemma tarjan_seen_examined {V E} (EV : encoding V) (g : Graph.t V E) keep
    (st : tarjan_state V E) v e es rest d :
  tarjan_bookkeeping EV st -> tarjan_examined EV (induced EV keep g) st ->
  frames st = TarjanFrame v (e :: es) :: rest ->
  Map.get EV (Graph.target g e) (disc st) = Some d ->
  Map.get EV (Graph.target g e) (low st) = None ->
  tarjan_examined EV (induced EV keep g)
    (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
      (pending st) (clock st) (emitted st)).
Proof.
  intros Hbook Hexamined Hframes Hdisc Hlow.
  apply (tarjan_consume_examined EV _ st [] v e es rest Hexamined Hframes).
  intros _; exists d; split; [exact Hdisc|].
  intro Hpending; change (In (Graph.target g e) (pending st)) in Hpending.
  destruct (proj2 (tarjan_book_low _ _ Hbook _) Hpending) as [l Hl].
  congruence.
Qed.

Lemma tarjan_back_examined {V E} (EV : encoding V) (g : Graph.t V E) keep
    (st : tarjan_state V E) v e es rest d :
  tarjan_bookkeeping EV st -> tarjan_examined EV (induced EV keep g) st ->
  frames st = TarjanFrame v (e :: es) :: rest ->
  Map.get EV (Graph.target g e) (disc st) = Some d ->
  tarjan_examined EV (induced EV keep g) (tarjan_lower EV v d
    (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
      (pending st) (clock st) (emitted st))).
Proof.
  intros Hbook Hexamined Hframes Hdisc.
  assert (Hv : In v (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); rewrite Hframes.
    left; reflexivity. }
  destruct (proj2 (tarjan_book_low _ _ Hbook v) Hv) as [old Hold].
  pose proof (tarjan_lower_examined EV (induced EV keep g) st v d Hexamined) as Hlower.
  unfold tarjan_lower in Hlower |- *; cbn [low]; rewrite Hold in Hlower |- *.
  apply (tarjan_consume_examined EV _
    (TarjanState (frames st) (disc st) (Map.set EV v (Pos.min old d) (low st))
      (pending st) (clock st) (emitted st)) [] v e es rest Hlower Hframes).
  intros _; exists d; split; [exact Hdisc|].
  intros _ l Hlink; cbn [low] in Hlink; rewrite Map.get_set_same in Hlink.
  inversion Hlink; subst l; apply Pos.le_min_r.
Qed.

Lemma tarjan_discover_edge_examined {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep (st : tarjan_state V E) v e es rest :
  ready EV g p -> tarjan_control g st ->
  tarjan_low_invariant EV (induced EV keep g) st ->
  tarjan_examined EV (induced EV keep g) st ->
  frames st = TarjanFrame v (e :: es) :: rest ->
  Map.get EV (Graph.target g e) (disc st) = None ->
  tarjan_examined EV (induced EV keep g) (tarjan_discover p (Graph.target g e)
    (TarjanState (TarjanFrame v es :: rest) (disc st) (low st)
      (pending st) (clock st) (emitted st))).
Proof.
  intros Hready Hcontrol Hinv Hexamined Hframes Hfresh.
  pose proof (tarjan_low_book _ _ _ Hinv) as Hbook.
  destruct (Hcontrol (TarjanFrame v (e :: es))
    ltac:(rewrite Hframes; left; reflexivity)) as [Hv Hedges].
  assert (Htarget : In (Graph.target g e) (Graph.nodes g)).
  { eapply out_target_in; [exact (proj1 Hready)|exact Hv|apply Hedges; left; reflexivity]. }
  assert (Hvpending : In v (pending st)).
  { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); rewrite Hframes.
    left; reflexivity. }
  destruct (proj2 (tarjan_book_low _ _ Hbook v) Hvpending) as [old Hold].
  destruct (tarjan_low_links _ _ _ Hinv v old Hold) as [dv [x [Hvd [Hbound _]]]].
  assert (Hne : v <> Graph.target g e) by (intro Heq; rewrite Heq, Hfresh in Hvd; discriminate).
  assert (Hbefore : tarjan_examined EV (induced EV keep g)
    (tarjan_discover p (Graph.target g e) st)).
  { apply tarjan_discover_examined; try assumption.
    intros a Ha; apply filter_In in Ha; destruct Ha as [Ha _].
    destruct Hready as [_ [_ Hlaws]]; rewrite (succ_agrees Hlaws _ Htarget); exact Ha. }
  apply (tarjan_consume_examined EV _ (tarjan_discover p (Graph.target g e) st)
    [TarjanFrame (Graph.target g e) (succ_edges p (Graph.target g e))]
    v e es rest Hbefore).
  - cbn [tarjan_discover frames]; rewrite Hframes; reflexivity.
  - intros _; exists (clock st); cbn [tarjan_discover disc]; rewrite Map.get_set_same.
    split; [reflexivity|]; intros _ l Hlink; cbn [tarjan_discover low] in Hlink.
    rewrite Map.get_set_other in Hlink by exact Hne; rewrite Hold in Hlink;
      inversion Hlink; subst l.
    eapply Pos.le_trans; [exact Hbound|apply Pos.lt_le_incl].
    destruct (tarjan_low_numbers _ _ _ Hinv) as [history [Hnumbers _]].
    apply (dfs_numbering_bound EV _ _ _ Hnumbers v dv Hvd).
Qed.

Lemma tarjan_step_examined {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st :
  ready EV g p -> tarjan_control g st ->
  tarjan_low_invariant EV (induced EV keep g) st -> tarjan_examined EV (induced EV keep g) st ->
  tarjan_examined EV (induced EV keep g) (tarjan_step p keep st).
Proof.
  intros Hready Hcontrol Hinv Hexamined; unfold tarjan_step.
  destruct (frames st) as [|[v [|e es]] rest] eqn:Hframes; [exact Hexamined| |].
  - apply (tarjan_close_examined EV _ st v rest); assumption.
  - destruct (FinSet.mem EV (Graph.target g e) keep) eqn:Hkeep.
    + destruct (Map.get EV (Graph.target g e) (disc st)) as [d|] eqn:Hdisc.
      * destruct (Map.get EV (Graph.target g e) (low st)) as [l|] eqn:Hlink.
        -- apply (tarjan_back_examined EV g keep st v e es rest d);
             try assumption; apply (tarjan_low_book _ _ _ Hinv).
        -- apply (tarjan_seen_examined EV g keep st v e es rest d);
             try assumption; apply (tarjan_low_book _ _ _ Hinv).
      * apply (tarjan_discover_edge_examined EV g p keep st v e es rest); assumption.
    + apply (tarjan_skip_examined EV g keep st v e es rest); assumption.
Qed.

(** * Emitted-component semantics *)

(** Emitted components are strongly connected and all their edges enter the same or older output. *)
Definition tarjan_output_valid {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) : Prop :=
  (forall c, In c (components (emitted st)) ->
    forall u v, In u c -> In v c -> mutual g u v) /\
  (forall u e i, Map.get EV u (comp_of (emitted st)) = Some i ->
    In e (Graph.out g u) ->
    exists j, Map.get EV (Graph.target g e) (comp_of (emitted st)) = Some j /\
      (j <= i)%positive).

Definition tarjan_output_strong {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) (Houtput : tarjan_output_valid EV g st) := proj1 Houtput.

Definition tarjan_output_rank {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) (Houtput : tarjan_output_valid EV g st) := proj2 Houtput.

Lemma tarjan_index_member_owner {V} (EV : encoding V) (r : scc_result V) x :
  tarjan_indexed EV r -> In x (concat (components r)) ->
  exists i, Map.get EV x (comp_of r) = Some i.
Proof.
  intros Hindex Hin; apply in_concat in Hin; destruct Hin as [c [Hc Hx]].
  destruct (tarjan_combine_total_right _ _ c (tarjan_index_length _ _ Hindex) Hc)
    as [i Hi].
  exists i; apply (tarjan_index_owner _ _ Hindex); exists c; auto.
Qed.

Lemma tarjan_index_owner_member {V} (EV : encoding V) (r : scc_result V) x i :
  tarjan_indexed EV r -> Map.get EV x (comp_of r) = Some i ->
  In x (concat (components r)) /\ In i (component_ids r).
Proof.
  intros Hindex Hget; apply (tarjan_index_owner _ _ Hindex) in Hget.
  destruct Hget as [c [Hc Hx]]; split.
  - apply in_concat; exists c; split; [eapply in_combine_r; eauto|exact Hx].
  - eapply in_combine_l; exact Hc.
Qed.

Lemma tarjan_emit_old_owner {V E} (EV : encoding V) (st : tarjan_state V E) root x i :
  tarjan_bookkeeping EV st -> Map.get EV x (comp_of (emitted st)) = Some i ->
  Map.get EV x (comp_of (emitted (tarjan_emit EV root st))) = Some i.
Proof.
  intros Hbook Hget.
  pose proof (proj1 (tarjan_index_owner_member EV _ x i (tarjan_book_index _ _ Hbook) Hget))
    as Hblack.
  pose proof (tarjan_pop_split EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hsplit.
  pose proof (tarjan_pop_owners EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st)) x) as Howners.
  unfold tarjan_emit; destruct (tarjan_pop EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as [[[members tail] links] owners].
  cbn in Hsplit, Howners; destruct Hsplit as [Hsplit _]; cbn [emitted comp_of].
  rewrite Howners.
  destruct (existsb (fun v => Pos.eqb (encode EV x) (encode EV v)) members) eqn:Hmem;
    [|exact Hget].
  apply tarjan_member_spec in Hmem; exfalso.
  apply (tarjan_nodup_disjoint _ _ (tarjan_book_distinct _ _ Hbook) x); [|exact Hblack].
  rewrite Hsplit; apply in_or_app; left; exact Hmem.
Qed.

Lemma tarjan_emit_output_rank {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) root members tail links owners :
  tarjan_bookkeeping EV st -> tarjan_output_valid EV g st ->
  tarjan_pop EV root (tarjan_next_id (emitted st)) (pending st) (low st)
    (comp_of (emitted st)) = (members, tail, links, owners) ->
  (forall u e, In u members -> In e (Graph.out g u) ->
    In (Graph.target g e) members \/ In (Graph.target g e) (concat (components (emitted st)))) ->
  forall u e i, Map.get EV u owners = Some i -> In e (Graph.out g u) ->
    exists j, Map.get EV (Graph.target g e) owners = Some j /\ (j <= i)%positive.
Proof.
  intros Hbook Houtput Hpop Hclosed u e i Howner Hedge.
  pose proof (tarjan_pop_owners EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Howners.
  rewrite Hpop in Howners; cbn in Howners.
  assert (Hold : forall x j, Map.get EV x (comp_of (emitted st)) = Some j ->
    Map.get EV x owners = Some j).
  { intros x j Hj; pose proof (tarjan_emit_old_owner EV st root x j Hbook Hj) as Hnew.
    unfold tarjan_emit in Hnew; rewrite Hpop in Hnew; exact Hnew. }
  rewrite Howners in Howner.
  destruct (existsb (fun v => Pos.eqb (encode EV u) (encode EV v)) members) eqn:Hmem.
  - inversion Howner; subst i; apply tarjan_member_spec in Hmem.
    destruct (Hclosed u e Hmem Hedge) as [Htarget|Htarget].
    + exists (tarjan_next_id (emitted st)); split; [|apply Pos.le_refl].
      rewrite Howners, (proj2 (tarjan_member_spec EV _ members) Htarget); reflexivity.
    + destruct (tarjan_index_member_owner EV _ _ (tarjan_book_index _ _ Hbook) Htarget)
        as [j Hj].
      exists j; split; [apply Hold; exact Hj|apply Pos.lt_le_incl].
      apply (tarjan_index_bound _ _ (tarjan_book_index _ _ Hbook)).
      exact (proj2 (tarjan_index_owner_member EV _ _ _ (tarjan_book_index _ _ Hbook) Hj)).
  - destruct (tarjan_output_rank _ _ _ Houtput u e i Howner Hedge) as [j [Hj Hbound]].
    exists j; split; [apply Hold; exact Hj|exact Hbound].
Qed.

Lemma tarjan_emit_output_valid {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v rest d :
  tarjan_low_invariant EV g st -> tarjan_frontier EV st -> tarjan_examined EV g st ->
  tarjan_output_valid EV g st -> frames st = TarjanFrame v [] :: rest ->
  Map.get EV v (disc st) = Some d -> Map.get EV v (low st) = Some d ->
  tarjan_output_valid EV g (tarjan_emit EV v st).
Proof.
  intros Hinv Hfrontier Hexamined Houtput Hframes Hdisc Hlink.
  unfold tarjan_emit.
  destruct (tarjan_pop EV v (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as [[[members tail] links] owners] eqn:Hpop.
  constructor; cbn [emitted components comp_of].
  - intros c [Heq|Hin] u w Hu Hw.
    + subst c; apply (tarjan_emission_strong EV g st v rest members tail links owners);
        assumption.
    + apply (tarjan_output_strong _ _ _ Houtput c Hin u w Hu Hw).
  - apply (tarjan_emit_output_rank EV g st v members tail links owners);
      [apply (tarjan_low_book _ _ _ Hinv)|exact Houtput|exact Hpop|].
    apply (tarjan_emission_closed EV g st v rest members tail links owners d); assumption.
Qed.

(** Adjacent open frames are joined by the discovery edge from parent to child. *)
Fixpoint tarjan_tree_path {V E} (g : Graph.t V E) (xs : list V) : Prop :=
  match xs with
  | [] => True
  | v :: rest =>
    (match rest with
    | [] => True
    | parent :: _ => exists e, In e (Graph.out g parent) /\ Graph.target g e = v
    end) /\ tarjan_tree_path g rest
  end.

Definition tarjan_tree_frames {V E} (g : Graph.t V E) (st : tarjan_state V E) : Prop :=
  tarjan_tree_path g (map frame_node (frames st)).

Lemma tarjan_step_tree {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st :
  ready EV g p -> tarjan_control g st -> tarjan_tree_frames (induced EV keep g) st ->
  tarjan_tree_frames (induced EV keep g) (tarjan_step p keep st).
Proof.
  intros Hready Hcontrol Htree; unfold tarjan_tree_frames in Htree |- *.
  unfold tarjan_step; destruct (frames st) as [|[v [|e es]] rest] eqn:Hframes;
    [rewrite Hframes; exact Htree| |].
  - rewrite (proj1 (tarjan_close_control_fields EV v rest st)).
    exact (proj2 Htree).
  - destruct (FinSet.mem EV (Graph.target g e) keep) eqn:Hkeep; [|exact Htree].
    destruct (Map.get EV (Graph.target g e) (disc st)) as [d|].
    + destruct (Map.get EV (Graph.target g e) (low st)); [|exact Htree].
      rewrite (proj1 (tarjan_lower_control_fields EV v d _)); exact Htree.
    + change ((exists a, In a (Graph.out (induced EV keep g) v) /\
        Graph.target (induced EV keep g) a = Graph.target g e) /\
        tarjan_tree_path (induced EV keep g) (v :: map frame_node rest)).
      split; [|exact Htree]; exists e; split; [|reflexivity].
      apply filter_In; split; [|exact Hkeep].
      destruct (Hcontrol (TarjanFrame v (e :: es))
        ltac:(rewrite Hframes; left; reflexivity)) as [_ Hedges].
      apply Hedges; left; reflexivity.
Qed.

(** The full invariant couples lowlinks, the DFS path, examined edges and emitted classes.
    I1 is output strong connectivity and edge rank, with maximality in [tarjan_emitted_exact].
    I2 is the bookkeeping partition, discovery numbering, pending subsequence and frame path.
    I3 is the lowlink witness and its mutual reachability in [tarjan_lowlink_mutual].
    I4 uses the frontier to collect closed children's lowlinks and the examined-edge bounds
    to close a whole component; [tarjan_emission_exact] and [tarjan_close_root_criterion]
    give the precise root test. Every explicit transition preserves all these facts. *)
Record tarjan_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) : Prop := {
  tarjan_invariant_low : tarjan_low_invariant EV g st;
  tarjan_invariant_frontier : tarjan_frontier EV st;
  tarjan_invariant_examined : tarjan_examined EV g st;
  tarjan_invariant_output : tarjan_output_valid EV g st;
  tarjan_invariant_tree : tarjan_tree_frames g st
}.

Lemma tarjan_initial_invariant {V E} (EV : encoding V) (g : Graph.t V E) :
  tarjan_invariant EV g (@tarjan_initial V E).
Proof.
  constructor.
  - apply tarjan_initial_low_invariant.
  - intros a w da dw la lw Hfalse; cbn [tarjan_initial frames map In] in Hfalse;
      contradiction.
  - intros v e Hfalse; cbn [tarjan_initial pending In] in Hfalse; contradiction.
  - constructor.
    + intros c Hfalse; cbn [tarjan_initial emitted components In] in Hfalse; contradiction.
    + intros u e i Hfalse; cbn [tarjan_initial emitted comp_of] in Hfalse.
      rewrite Map.get_empty in Hfalse; discriminate.
  - exact I.
Qed.

Lemma tarjan_close_output_valid {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v rest :
  tarjan_invariant EV g st -> frames st = TarjanFrame v [] :: rest ->
  tarjan_output_valid EV g (tarjan_close EV v rest st).
Proof.
  intros Hinv Hframes.
  pose proof (tarjan_invariant_output _ _ _ Hinv) as Houtput.
  unfold tarjan_close.
  destruct (Map.get EV v (low st)) as [l|] eqn:Hlink;
    destruct (Map.get EV v (disc st)) as [d|] eqn:Hdisc; try exact Houtput.
  destruct (Pos.eqb l d) eqn:Heq.
  - apply Pos.eqb_eq in Heq; subst l.
    pose proof (tarjan_emit_output_valid EV g st v rest d
      (tarjan_invariant_low _ _ _ Hinv) (tarjan_invariant_frontier _ _ _ Hinv)
      (tarjan_invariant_examined _ _ _ Hinv) Houtput Hframes Hdisc Hlink) as Hemit.
    unfold tarjan_emit in Hemit |- *; cbn [pending low emitted].
    destruct (tarjan_pop EV v (tarjan_next_id (emitted st)) (pending st) (low st)
      (comp_of (emitted st))) as [[[members tail] links] owners]; exact Hemit.
  - destruct rest as [|parent rest]; [exact Houtput|].
    unfold tarjan_lower; cbn [low].
    destruct (Map.get EV (frame_node parent) (low st)); exact Houtput.
Qed.

Lemma tarjan_step_output_valid {V E} (EV : encoding V) (g h : Graph.t V E)
    (p : prepared EV g) keep st :
  tarjan_invariant EV h st -> tarjan_output_valid EV h (tarjan_step p keep st).
Proof.
  intro Hinv; pose proof (tarjan_invariant_output _ _ _ Hinv) as Houtput.
  unfold tarjan_step; destruct (frames st) as [|[v [|e es]] rest] eqn:Hframes;
    [exact Houtput| |].
  - apply (tarjan_close_output_valid EV h st v rest); assumption.
  - destruct (FinSet.mem EV (Graph.target g e) keep); [|exact Houtput].
    destruct (Map.get EV (Graph.target g e) (disc st)); [|exact Houtput].
    destruct (Map.get EV (Graph.target g e) (low st)); [|exact Houtput].
    unfold tarjan_lower; cbn [low]; destruct (Map.get EV v (low st)); exact Houtput.
Qed.

Lemma tarjan_step_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st :
  ready EV g p -> tarjan_control g st -> tarjan_invariant EV (induced EV keep g) st ->
  tarjan_invariant EV (induced EV keep g) (tarjan_step p keep st).
Proof.
  intros Hready Hcontrol Hinv; pose proof (tarjan_invariant_low _ _ _ Hinv) as Hlow.
  constructor.
  - apply tarjan_step_low_invariant; assumption.
  - apply tarjan_step_frontier.
    + apply (tarjan_low_book _ _ _ Hlow).
    + apply (tarjan_low_numbers _ _ _ Hlow).
    + apply (tarjan_invariant_frontier _ _ _ Hinv).
  - apply tarjan_step_examined; try assumption; apply (tarjan_invariant_examined _ _ _ Hinv).
  - apply tarjan_step_output_valid; exact Hinv.
  - apply tarjan_step_tree; try assumption; apply (tarjan_invariant_tree _ _ _ Hinv).
Qed.

Lemma tarjan_run_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st n :
  ready EV g p -> tarjan_control g st -> tarjan_invariant EV (induced EV keep g) st ->
  tarjan_invariant EV (induced EV keep g) (tarjan_run p keep n st) /\
    tarjan_control g (tarjan_run p keep n st).
Proof.
  intros Hready Hcontrol Hinv; rewrite tarjan_run_agrees; induction n using Pos.peano_ind.
  - split; [apply tarjan_step_invariant|apply tarjan_step_control]; assumption.
  - rewrite Pos.iter_succ; destruct IHn as [Hstate Hstack].
    split; [apply tarjan_step_invariant|apply tarjan_step_control]; assumption.
Qed.

Lemma tarjan_root_start_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st v :
  ready EV g p -> In v (Graph.nodes g) -> tarjan_invariant EV (induced EV keep g) st ->
  frames st = [] -> Map.get EV v (disc st) = None ->
  tarjan_invariant EV (induced EV keep g) (tarjan_discover p v st).
Proof.
  intros Hready Hv Hinv Hempty Hfresh.
  pose proof (tarjan_invariant_low _ _ _ Hinv) as Hlow.
  pose proof (tarjan_low_book _ _ _ Hlow) as Hbook.
  assert (Hpending : pending st = []).
  { apply (tarjan_pending_empty EV (induced EV keep g) st);
      [exact Hbook|apply (tarjan_low_links _ _ _ Hlow)|
       apply (tarjan_low_closed _ _ _ Hlow)|exact Hempty]. }
  constructor.
  - apply tarjan_discover_low_invariant; [exact Hlow|exact Hfresh|].
    intros w Hfalse; rewrite Hpending in Hfalse; contradiction.
  - apply tarjan_discover_frontier; [exact Hbook|apply (tarjan_low_numbers _ _ _ Hlow)|
      apply (tarjan_invariant_frontier _ _ _ Hinv)|exact Hfresh].
  - apply tarjan_discover_examined; [exact Hbook|
      apply (tarjan_invariant_examined _ _ _ Hinv)|exact Hfresh|].
    intros e Hedge; apply filter_In in Hedge; destruct Hedge as [Hedge _].
    destruct Hready as [_ [_ Hlaws]]; rewrite (succ_agrees Hlaws _ Hv); exact Hedge.
  - exact (tarjan_invariant_output _ _ _ Hinv).
  - unfold tarjan_tree_frames; cbn [tarjan_discover frames map frame_node].
    rewrite Hempty; cbn [map tarjan_tree_path]; auto.
Qed.

Lemma tarjan_root_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep st v :
  ready EV g p -> In v (Graph.nodes g) -> tarjan_invariant EV (induced EV keep g) st ->
  frames st = [] -> tarjan_invariant EV (induced EV keep g) (tarjan_root p keep st v) /\
    frames (tarjan_root p keep st v) = [].
Proof.
  intros Hready Hv Hinv Hempty; split.
  - unfold tarjan_root; destruct (Map.get EV v (disc st)) as [d|] eqn:Hfresh;
      [exact Hinv|].
    assert (Hcontrol : tarjan_control g (tarjan_discover p v st)).
    { intros f [Heq|Hin]; [subst f|rewrite Hempty in Hin; contradiction].
      split; [exact Hv|].
      destruct Hready as [_ [_ Hlaws]]; cbn [tarjan_discover frame_node frame_edges].
      rewrite (succ_agrees Hlaws _ Hv); intros e He; exact He. }
    exact (proj1 (tarjan_run_invariant EV g p keep (tarjan_discover p v st) (fuel p)
      Hready Hcontrol (tarjan_root_start_invariant EV g p keep st v Hready Hv
        Hinv Hempty Hfresh))).
  - apply (proj2 (tarjan_root_terminates EV g p keep st v Hready Hempty Hv)).
Qed.

Lemma tarjan_fold_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) keep roots st :
  ready EV g p -> incl roots (Graph.nodes g) -> tarjan_invariant EV (induced EV keep g) st ->
  frames st = [] ->
  tarjan_invariant EV (induced EV keep g) (fold_left (tarjan_root p keep) roots st) /\
    frames (fold_left (tarjan_root p keep) roots st) = [].
Proof.
  intros Hready; revert st; induction roots as [|v roots IH]; intros st Hroots Hinv Hempty;
    [split; assumption|].
  cbn [fold_left].
  destruct (tarjan_root_invariant EV g p keep st v Hready (Hroots v (or_introl eq_refl))
    Hinv Hempty) as [Hstate Hframes].
  apply IH; [intros w Hw; apply Hroots; right; exact Hw|exact Hstate|exact Hframes].
Qed.

Lemma scc_within_semantics {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region :
  ready EV g p -> incl region (Graph.nodes g) ->
  (forall c, In c (components (scc_within p region)) ->
    forall u v, In u c -> In v c -> mutual (induced EV (FinSet.of_list EV region) g) u v) /\
  (forall u e i, Map.get EV u (comp_of (scc_within p region)) = Some i ->
    In e (Graph.out (induced EV (FinSet.of_list EV region) g) u) ->
    exists j, Map.get EV (Graph.target g e) (comp_of (scc_within p region)) = Some j /\
      (j <= i)%positive).
Proof.
  intros Hready Hregion.
  destruct (tarjan_fold_invariant EV g p (FinSet.of_list EV region) region tarjan_initial
    Hready Hregion (tarjan_initial_invariant EV _) eq_refl) as [Hinv Hframes].
  remember (fold_left (tarjan_root p (FinSet.of_list EV region)) region tarjan_initial)
    as result eqn:Hresult.
  unfold scc_within; rewrite <- Hresult; cbn [tarjan_result components comp_of].
  split.
  - intros c Hin; rewrite <- in_rev in Hin.
    exact (tarjan_output_strong _ _ _ (tarjan_invariant_output _ _ _ Hinv) c Hin).
  - apply (tarjan_output_rank _ _ _ (tarjan_invariant_output _ _ _ Hinv)).
Qed.

Lemma scc_owner_path_rank {V E} (EV : encoding V) (g : Graph.t V E) owners :
  (forall u e i, Map.get EV u owners = Some i -> In e (Graph.out g u) ->
    exists j, Map.get EV (Graph.target g e) owners = Some j /\ (j <= i)%positive) ->
  forall u es v, path g u es v -> forall i, Map.get EV u owners = Some i ->
    exists j, Map.get EV v owners = Some j /\ (j <= i)%positive.
Proof.
  intros Hrank u es v Hpath; induction Hpath as [v|e es w Hedge Hpath IH]; intros i Hi.
  - exists i; split; [exact Hi|apply Pos.le_refl].
  - destruct (Hrank _ e i Hi Hedge) as [j [Hj Hji]].
    destruct (IH j Hj) as [k [Hk Hkj]].
    exists k; split; [exact Hk|eapply Pos.le_trans; eauto].
Qed.

Lemma scc_within_owner_total {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region x :
  ready EV g p -> incl region (Graph.nodes g) -> In x region ->
  exists i, Map.get EV x (comp_of (scc_within p region)) = Some i.
Proof.
  intros Hready Hregion Hx.
  destruct (scc_within_indexes EV g p region) as [_ [_ [Hlength [Hat [_ [Howner _]]]]]].
  apply (proj2 (scc_within_members EV g p region Hready Hregion x)) in Hx.
  apply in_concat in Hx; destruct Hx as [c [Hc Hx]].
  destruct (tarjan_combine_total_right _ _ c Hlength Hc) as [i Hi].
  exists i; apply Howner; exists c; split; [apply Hat; exact Hi|exact Hx].
Qed.

Lemma scc_within_mutual {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region u v :
  ready EV g p -> incl region (Graph.nodes g) -> In u region -> In v region ->
  ((exists i, Map.get EV u (comp_of (scc_within p region)) = Some i /\
    Map.get EV v (comp_of (scc_within p region)) = Some i) <->
    mutual (induced EV (FinSet.of_list EV region) g) u v).
Proof.
  intros Hready Hregion Hu Hv.
  destruct (scc_within_semantics EV g p region Hready Hregion) as [Hstrong Hrank].
  destruct (scc_within_indexes EV g p region) as [_ [_ [_ [Hat [_ [Howner _]]]]]].
  split.
  - intros [i [Hi Hj]]; apply Howner in Hi, Hj.
    destruct Hi as [c [Hc Huc]], Hj as [d [Hd Hvd]].
    rewrite Hc in Hd; inversion Hd; subst d.
    apply (Hstrong c); [apply in_combine_r with
      (l := component_ids (scc_within p region)) (x := i); apply Hat; exact Hc|exact Huc|exact Hvd].
  - intros [[first Hfirst] [last Hlast]].
    destruct (scc_within_owner_total EV g p region u Hready Hregion Hu) as [i Hi].
    destruct (scc_owner_path_rank EV _ _ Hrank u first v Hfirst i Hi) as [j [Hj Hji]].
    destruct (scc_owner_path_rank EV _ _ Hrank v last u Hlast j Hj) as [k [Hk Hkj]].
    rewrite Hi in Hk; inversion Hk; subst k.
    assert (Heq : i = j) by (apply Pos.le_antisym; assumption).
    subst j; exists i; auto.
Qed.

Lemma tarjan_induced_path {V E} (EV : encoding V) (g : Graph.t V E) keep u es v :
  path (induced EV keep g) u es v -> path g u es v.
Proof.
  intro Hpath; induction Hpath as [v|e es w Hedge Hpath IH]; [constructor|].
  apply filter_In in Hedge; destruct Hedge as [Hedge _].
  apply (path_cons e es w Hedge IH).
Qed.

Lemma tarjan_induced_full_path {V E} (EV : encoding V) (g : Graph.t V E) u es v :
  graph_wf g -> path g u es v -> In u (Graph.nodes g) ->
  path (induced EV (FinSet.of_list EV (Graph.nodes g)) g) u es v.
Proof.
  intros Hwf Hpath; induction Hpath as [v|e es w Hedge Hpath IH]; intro Hu; [constructor|].
  assert (Ht : In (Graph.target g e) (Graph.nodes g)) by (eapply out_target_in; eauto).
  apply (@path_cons V E (induced EV (FinSet.of_list EV (Graph.nodes g)) g) e es w).
  - apply filter_In; split; [exact Hedge|apply FinSet.of_list_spec; exact Ht].
  - apply IH; exact Ht.
Qed.

Lemma tarjan_induced_full_mutual {V E} (EV : encoding V) (g : Graph.t V E) u v :
  graph_wf g -> In u (Graph.nodes g) -> In v (Graph.nodes g) ->
  (mutual (induced EV (FinSet.of_list EV (Graph.nodes g)) g) u v <-> mutual g u v).
Proof.
  intros Hwf Hu Hv; split; intros [[first Hfirst] [last Hlast]]; split.
  - exists first; eapply tarjan_induced_path; exact Hfirst.
  - exists last; eapply tarjan_induced_path; exact Hlast.
  - exists first; apply tarjan_induced_full_path; assumption.
  - exists last; apply tarjan_induced_full_path; assumption.
Qed.

(** * Public exactness theorems *)

Section Gra3a.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (u v : V) (e : E) (region : list V).
Local Abbreviation R := (scc p).

(** Components partition the region and their indexes identify exactly its mutual reachability. *)
Theorem scc_within_exact : ready EV g p -> incl region (Graph.nodes g) ->
  NoDup (concat (components (scc_within p region))) /\
  (forall x, In x (concat (components (scc_within p region))) <-> In x region) /\
  (forall c, In c (components (scc_within p region)) -> c <> []) /\
  length (component_ids (scc_within p region)) = length (components (scc_within p region)) /\
  (forall i c, Trie.get i (component_at (scc_within p region)) = Some c <->
    In (i, c) (combine (component_ids (scc_within p region))
      (components (scc_within p region)))) /\
  NoDup (component_ids (scc_within p region)) /\
  (forall x i, Map.get EV x (comp_of (scc_within p region)) = Some i <->
    exists c, Trie.get i (component_at (scc_within p region)) = Some c /\ In x c) /\
  (In u region -> In v region ->
    ((exists i, Map.get EV u (comp_of (scc_within p region)) = Some i /\
      Map.get EV v (comp_of (scc_within p region)) = Some i) <->
      mutual (induced EV (FinSet.of_list EV region) g) u v)).
Proof.
  intros Hready Hregion.
  destruct (scc_within_indexes EV g p region)
    as [Hnodup [Hnonempty [Hlength [Hat [Hids [Howner Horder]]]]]].
  split; [exact Hnodup|]; split; [apply scc_within_members; assumption|].
  split; [exact Hnonempty|]; split; [exact Hlength|]; split; [exact Hat|].
  split; [exact Hids|]; split; [exact Howner|].
  apply scc_within_mutual; assumption.
Qed.

(** Every edge goes to a component emitted no later than its source component. *)
Theorem scc_reverse_topological : ready EV g p -> incl region (Graph.nodes g) ->
  In e (Graph.out g (Graph.source g e)) -> In (Graph.source g e) region ->
  In (Graph.target g e) region ->
  exists i j, Map.get EV (Graph.source g e) (comp_of (scc_within p region)) = Some i /\
    Map.get EV (Graph.target g e) (comp_of (scc_within p region)) = Some j /\ (j <= i)%positive.
Proof.
  intros Hready Hregion Hedge Hsource Htarget.
  destruct (scc_within_owner_total EV g p region _ Hready Hregion Hsource) as [i Hi].
  destruct (scc_within_semantics EV g p region Hready Hregion) as [_ Hrank].
  assert (Hedge' : In e (Graph.out (induced EV (FinSet.of_list EV region) g)
    (Graph.source g e))).
  { apply filter_In; split; [exact Hedge|apply FinSet.of_list_spec; exact Htarget]. }
  destruct (Hrank _ e i Hi Hedge') as [j [Hj Hbound]]; exists i, j; auto.
Qed.

(** Whole-graph components are exactly the graph's mutual-reachability classes. *)
Theorem scc_exact : ready EV g p ->
  NoDup (concat (components R)) /\
  (forall x, In x (concat (components R)) <-> In x (Graph.nodes g)) /\
  (In u (Graph.nodes g) -> In v (Graph.nodes g) ->
    ((exists i, Map.get EV u (comp_of R) = Some i /\ Map.get EV v (comp_of R) = Some i) <->
      mutual g u v)).
Proof.
  intro Hready.
  destruct (scc_within_indexes EV g p (Graph.nodes g)) as [Hnodup _].
  split; [exact Hnodup|]; split.
  - exact (scc_within_members EV g p (Graph.nodes g) Hready (fun _ H => H)).
  - intros Hu Hv; rewrite (scc_within_mutual EV g p (Graph.nodes g) u v Hready
      (fun _ H => H) Hu Hv).
    apply tarjan_induced_full_mutual; [exact (proj1 Hready)|exact Hu|exact Hv].
Qed.

(** Condensation preserves cross edges and entries and is a well-formed ordered DAG. *)
Theorem condensation_correct : ready EV g p ->
  graph_wf (condensation p R) /\ (forall c, NoDup (Graph.out (condensation p R) c)) /\
  acyclic (condensation p R) /\
  topological_order (condensation p R) (rev (component_ids R)) /\
  (forall c e', In e' (Graph.out (condensation p R) c) <->
    exists x j, In x (Graph.nodes g) /\ In e' (Graph.out g x) /\
      Map.get EV x (comp_of R) = Some c /\
      Map.get EV (Graph.target g e') (comp_of R) = Some j /\ j <> c) /\
  (forall c, In c (Graph.entries (condensation p R)) <->
    exists s, In s (Graph.entries g) /\ Map.get EV s (comp_of R) = Some c) /\
  NoDup (Graph.entries (condensation p R)) /\
  (forall e', In (Graph.source g e') (Graph.nodes g) -> In (Graph.target g e') (Graph.nodes g) ->
    exists i j, Map.get EV (Graph.source g e') (comp_of R) = Some i /\
      Map.get EV (Graph.target g e') (comp_of R) = Some j /\
      Graph.source (condensation p R) e' = i /\ Graph.target (condensation p R) e' = j).
Proof.
  intro Hready.
  destruct (scc_condensation_structure EV g p Hready)
    as [Hwf [Hout [Hedges [Hentries [Hunique Hendpoints]]]]].
  pose proof (scc_covers_nodes EV g p Hready) as Hcovers.
  destruct (scc_within_indexes EV g p (Graph.nodes g))
    as [_ [_ [_ [_ [Hids [_ Horder]]]]]].
  assert (Hrank : forall e' i j, In (Graph.source g e') (Graph.nodes g) ->
    In e' (Graph.out g (Graph.source g e')) ->
    Map.get EV (Graph.source g e') (comp_of R) = Some i ->
    Map.get EV (Graph.target g e') (comp_of R) = Some j -> (j <= i)%positive).
  { intros e' i j Hsource Hedge Hi Hj.
    assert (Htarget : In (Graph.target g e') (Graph.nodes g)).
    { eapply out_target_in; [exact (proj1 Hready)|exact Hsource|exact Hedge]. }
    destruct (scc_within_semantics EV g p (Graph.nodes g) Hready (fun _ H => H))
      as [_ Hedgesrank].
    assert (Hedge' : In e' (Graph.out
      (induced EV (FinSet.of_list EV (Graph.nodes g)) g) (Graph.source g e'))).
    { apply filter_In; split; [exact Hedge|apply FinSet.of_list_spec; exact Htarget]. }
    destruct (Hedgesrank _ e' i Hi Hedge') as [j' [Hj' Hbound]].
    change (Map.get EV (Graph.target g e') (comp_of R) = Some j') in Hj'.
    rewrite Hj in Hj'; inversion Hj'; subst j'; exact Hbound. }
  split; [exact Hwf|]; split; [exact Hout|].
  split; [apply condensation_acyclic; assumption|].
  split; [apply condensation_topological; assumption|].
  split; [exact Hedges|]; split; [exact Hentries|]; split; assumption.
Qed.

End Gra3a.

(** * Semantic consequences of I1–I4 *)

Lemma tarjan_emitted_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) :
  tarjan_invariant EV g st -> forall c u, In c (components (emitted st)) -> In u c ->
    forall w, In w c <-> mutual g u w.
Proof.
  intros Hinv c u Hc Hu w.
  pose proof (tarjan_invariant_output _ _ _ Hinv) as Houtput.
  pose proof (tarjan_book_index _ _ (tarjan_low_book _ _ _
    (tarjan_invariant_low _ _ _ Hinv))) as Hindex.
  split; [intro Hw; apply (tarjan_output_strong _ _ _ Houtput c Hc u w Hu Hw)|].
  intros [[first Hfirst] [last Hlast]].
  destruct (tarjan_combine_total_right _ _ c (tarjan_index_length _ _ Hindex) Hc)
    as [i Hi].
  assert (Hui : Map.get EV u (comp_of (emitted st)) = Some i).
  { apply (tarjan_index_owner _ _ Hindex); exists c; auto. }
  destruct (scc_owner_path_rank EV g _ (tarjan_output_rank _ _ _ Houtput)
    u first w Hfirst i Hui) as [j [Hwj Hji]].
  destruct (scc_owner_path_rank EV g _ (tarjan_output_rank _ _ _ Houtput)
    w last u Hlast j Hwj) as [k [Huk Hkj]].
  rewrite Hui in Huk; inversion Huk; subst k.
  assert (Heq : i = j) by (apply Pos.le_antisym; assumption); subst j.
  apply (tarjan_index_owner _ _ Hindex) in Hwj; destruct Hwj as [d [Hd Hw]].
  apply (tarjan_index_at _ _ Hindex) in Hi, Hd; rewrite Hi in Hd; inversion Hd; subst d.
  exact Hw.
Qed.

Lemma tarjan_lowlink_mutual {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) w l :
  tarjan_low_invariant EV g st -> Map.get EV w (low st) = Some l ->
  exists d x, Map.get EV w (disc st) = Some d /\ (l <= d)%positive /\
    In x (pending st) /\ Map.get EV x (disc st) = Some l /\ mutual g w x.
Proof.
  intros Hinv Hlink.
  destruct (tarjan_low_links _ _ _ Hinv w l Hlink)
    as [d [x [Hdisc [Hbound [Hx [Hnumber Hreach]]]]]].
  exists d, x; split; [exact Hdisc|]; split; [exact Hbound|]; split; [exact Hx|].
  split; [exact Hnumber|]; split; [exact Hreach|].
  apply (tarjan_low_paths _ _ _ Hinv x w l d Hx); [|exact Hnumber|exact Hdisc|exact Hbound].
  apply (tarjan_book_low _ _ (tarjan_low_book _ _ _ Hinv)); exists l; exact Hlink.
Qed.

Lemma tarjan_path_closed {V E} (g : Graph.t V E) (P : V -> Prop) :
  (forall u e, P u -> In e (Graph.out g u) -> P (Graph.target g e)) ->
  forall u es v, path g u es v -> P u -> P v.
Proof.
  intros Hclosed u es v Hpath; induction Hpath as [v|e es w Hedge Hpath IH]; intro Hu.
  - exact Hu.
  - apply IH; apply (Hclosed _ e Hu Hedge).
Qed.

Lemma tarjan_black_closed {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) :
  tarjan_bookkeeping EV st -> tarjan_output_valid EV g st ->
  forall w e, In w (concat (components (emitted st))) -> In e (Graph.out g w) ->
    In (Graph.target g e) (concat (components (emitted st))).
Proof.
  intros Hbook Houtput w e Hw Hedge.
  destruct (tarjan_index_member_owner EV _ w (tarjan_book_index _ _ Hbook) Hw) as [i Hi].
  destruct (tarjan_output_rank _ _ _ Houtput w e i Hi Hedge) as [j [Hj _]].
  exact (proj1 (tarjan_index_owner_member EV _ _ _ (tarjan_book_index _ _ Hbook) Hj)).
Qed.

Lemma tarjan_emission_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v rest members tail links owners d :
  tarjan_invariant EV g st -> frames st = TarjanFrame v [] :: rest ->
  Map.get EV v (disc st) = Some d -> Map.get EV v (low st) = Some d ->
  tarjan_pop EV v (tarjan_next_id (emitted st)) (pending st) (low st)
    (comp_of (emitted st)) = (members, tail, links, owners) ->
  forall u w, In u members -> (In w members <-> mutual g u w).
Proof.
  intros Hinv Hframes Hdisc Hlink Hpop u w Hu.
  pose proof (tarjan_invariant_low _ _ _ Hinv) as Hlow.
  pose proof (tarjan_low_book _ _ _ Hlow) as Hbook.
  pose proof (tarjan_black_closed EV g st Hbook (tarjan_invariant_output _ _ _ Hinv))
    as Hblack.
  pose proof (tarjan_emission_closed EV g st v rest members tail links owners d Hlow
    (tarjan_invariant_frontier _ _ _ Hinv) (tarjan_invariant_examined _ _ _ Hinv)
    Hframes Hdisc Hlink Hpop) as Hclosed.
  assert (Hunion : forall x e, In x members \/ In x (concat (components (emitted st))) ->
    In e (Graph.out g x) ->
    In (Graph.target g e) members \/ In (Graph.target g e) (concat (components (emitted st)))).
  { intros x e [Hx|Hx] Hedge; [apply (Hclosed x e Hx Hedge)|right; apply (Hblack x e Hx Hedge)]. }
  split.
  - intro Hw; apply (tarjan_emission_strong EV g st v rest members tail links owners);
      assumption.
  - intros [[first Hfirst] [last Hlast]].
    destruct (tarjan_path_closed g _ Hunion u first w Hfirst (or_introl Hu)) as [Hw|Hw];
      [exact Hw|].
    pose proof (tarjan_path_closed g _ Hblack w last u Hlast Hw) as Hublack.
    pose proof (tarjan_pop_split EV v (tarjan_next_id (emitted st))
      (pending st) (low st) (comp_of (emitted st))) as Hsplit.
    rewrite Hpop in Hsplit; cbn in Hsplit; destruct Hsplit as [Hsplit _].
    exfalso; apply (tarjan_nodup_disjoint _ _ (tarjan_book_distinct _ _ Hbook) u);
      [rewrite Hsplit; apply in_or_app; left; exact Hu|exact Hublack].
Qed.

Lemma tarjan_close_root_criterion {V E} (EV : encoding V) (g : Graph.t V E)
    (st : tarjan_state V E) v rest l d :
  tarjan_invariant EV g st -> frames st = TarjanFrame v [] :: rest ->
  Map.get EV v (low st) = Some l -> Map.get EV v (disc st) = Some d ->
  (l = d <-> ~ exists x dx, In x (pending st) /\ Map.get EV x (disc st) = Some dx /\
    (dx < d)%positive /\ mutual g v x).
Proof.
  intros Hinv Hframes Hlink Hdisc; split.
  - intro Heq; subst l; intros [x [dx [Hx [Hxd [Hstrict Hmutual]]]]].
    pose proof (tarjan_low_book _ _ _ (tarjan_invariant_low _ _ _ Hinv)) as Hbook.
    assert (Hv : In v (pending st)).
    { apply (tarjan_stack_member _ _ (tarjan_book_frames _ _ Hbook)); rewrite Hframes.
      left; reflexivity. }
    pose proof (tarjan_pop_split EV v (tarjan_next_id (emitted st))
      (pending st) (low st) (comp_of (emitted st))) as Hsplit.
    destruct (tarjan_pop EV v (tarjan_next_id (emitted st))
      (pending st) (low st) (comp_of (emitted st)))
      as [[[members tail] links] owners] eqn:Hpop.
    cbn in Hsplit; destruct Hsplit as [_ Hroot].
    pose proof (proj2 (tarjan_emission_exact EV g st v rest members tail links owners d
      Hinv Hframes Hdisc Hlink Hpop v x (Hroot Hv)) Hmutual) as Hmember.
    pose proof (tarjan_popped_number EV st v [] rest members tail links owners x d dx
      Hbook (tarjan_low_numbers _ _ _ (tarjan_invariant_low _ _ _ Hinv))
      Hframes Hpop Hmember Hdisc Hxd) as Hbound.
    exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hbound Hstrict)).
  - intro Hnone; destruct (Pos.eq_dec l d) as [Heq|Hne]; [exact Heq|].
    destruct (tarjan_lowlink_mutual EV g st v l (tarjan_invariant_low _ _ _ Hinv) Hlink)
      as [dv [x [Hvd [Hbound [Hx [Hxd Hmutual]]]]]].
    rewrite Hdisc in Hvd; inversion Hvd; subst dv.
    exfalso; apply Hnone; exists x, l; split; [exact Hx|]; split; [exact Hxd|].
    split; [|exact Hmutual]; apply Pos.le_lteq in Hbound.
    destruct Hbound as [Hstrict|Heq]; [exact Hstrict|contradiction].
Qed.
