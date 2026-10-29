(** * Observation-oriented SCC iteration

    A prepared component schedule retains each predecessor until its last declared reader finishes.
    For example, a value read throughout a successor cycle is evicted only after that cycle ends.
    Builds on: FixpointNested, FixpointSchedule, GraphScc and GraphWto. *)

From Stdlib Require Import List Bool Arith PeanoNat PArith Lia Permutation
  Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphWto.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCycles
  FixpointWorklist FixpointTotal FixpointSchedule FixpointNested.
Import List.ListNotations.

(** * Public plans and preparation *)

(** A plan lists components in execution order and indexes expirations by their first members. *)
Record observation_plan (X : Type) : Type := ObservationPlan {
  observation_components : list (list X);
  observation_expire : Map.t X (list X)
}.

Arguments ObservationPlan {X}.
Arguments observation_components {X}.
Arguments observation_expire {X}.

Definition observation_key_eqb {X} (EX : encoding X) (x y : X) : bool :=
  Pos.eqb (encode EX x) (encode EX y).

Definition observation_seteq {X} (EX : encoding X) (xs ys : list X) : bool :=
  forallb (fun x => existsb (observation_key_eqb EX x) ys) xs &&
    forallb (fun y => existsb (observation_key_eqb EX y) xs) ys.

Definition observation_expire_check {X} (EX : encoding X) (left right : Map.t X (list X)) : bool :=
  let agrees := fun xs other => observation_seteq EX xs
    (match other with
    | Some ys => ys
    | None => []
    end) in
  Map.forall2 agrees left right && Map.forall2 agrees right left.

Fixpoint observation_nodup_check {X} (EX : encoding X) (xs : list X) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (existsb (observation_key_eqb EX x) rest) && observation_nodup_check EX rest
  end.

Fixpoint observation_boundaries {X} (order : list (list X)) : list (list X * list (list X)) :=
  match order with
  | [] => []
  | component :: rest => (component, rest) :: observation_boundaries rest
  end.

Definition observation_boundary_check {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (component : list X) (suffix : list (list X)) : bool :=
  let members := FinSet.of_list EX component in
  let later := FinSet.of_list EX (concat suffix) in
  forallb (fun c => if FinSet.mem EX (System.target S c) members then
    forallb (fun x => negb (FinSet.mem EX x later)) (deps SS c) else true) (System.constraints S).

Definition observation_forward_check {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (order : list (list X)) : bool :=
  forallb (fun boundary => observation_boundary_check EX S SS (fst boundary) (snd boundary))
    (observation_boundaries order).

(** Topological validity prevents a completed component from reading any later component. *)
Definition observation_forward_valid {X C A} (S : System.t X C A) (SS : System.static S)
    (order : list (list X)) : Prop :=
  forall prefix component suffix, order = prefix ++ component :: suffix ->
    forall c, In c (System.constraints S) -> In (System.target S c) component ->
      forall x, In x (deps SS c) -> ~ In x (concat suffix).

Definition observation_side_free {X C A} (S : System.t X C A) (SS : System.static S) :
    bool :=
  forallb (fun c => match side_targets SS c with [] => true | _ => false end)
    (System.constraints S).

Definition observation_roots_check {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (roots : list X) : bool :=
  let universe := FinSet.of_list EX (unknowns EX S SS) in
  forallb (fun x => FinSet.mem EX x universe) roots.

Definition observation_order {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : list (list X) :=
  rev (components (scc (prepare EX (dependency_graph EX S SS)))).

Definition observation_components_check {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (order : list (list X)) : bool :=
  let classes := observation_order EX S SS in
  observation_nodup_check EX (concat order) &&
    observation_seteq EX (concat order) (unknowns EX S SS) &&
    forallb (fun component =>
      match component with
      | [] => false
      | _ => true
      end) order &&
    forallb (fun component => existsb (observation_seteq EX component) classes) order &&
    observation_forward_check EX S SS order.

(** Every member counts as a use in its own component, even if it has no declared reader. *)
Definition observation_component_uses {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (members : FinSet.t X) (x : X) : bool :=
  FinSet.mem EX x members ||
    existsb (fun c => FinSet.mem EX (System.target S c) members) (readers_of EX ix x).

Fixpoint observation_last_reader {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (x : X) : option X :=
  match order with
  | [] => None
  | [] :: rest => observation_last_reader EX S ix rest x
  | (h :: body) :: rest =>
    match observation_last_reader EX S ix rest x with
    | Some last => Some last
    | None =>
      if observation_component_uses EX S ix (FinSet.of_list EX (h :: body)) x
      then Some h else None
    end
  end.

(** Lifetimes are prepared once; iteration reads only the just-completed representative's list. *)
Definition observation_expirations {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (order : list (list X)) :
    Map.t X (list X) :=
  fold_right (fun x expiration =>
    match observation_last_reader EX S ix order x with
    | Some h => index_push EX x h expiration
    | None => expiration
    end) Map.empty (unknowns EX S SS).

Definition observation_canonical {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) : observation_plan X :=
  let order := observation_order EX S SS in
  ObservationPlan order (observation_expirations EX S SS ix order).

(** Preparation rejects side targets and observations outside the declared universe. *)
Definition observation_prepare {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (roots : list X) :
    option (observation_plan X) :=
  if observation_side_free S SS && observation_roots_check EX S SS roots
  then Some (observation_canonical EX S SS ix) else None.

(** Untrusted plans validate SCC membership, topological flow and exact lifetime membership. *)
Definition observation_plan_check {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (roots : list X)
    (p : observation_plan X) : bool :=
  observation_side_free S SS && observation_roots_check EX S SS roots &&
    observation_components_check EX S SS (observation_components p) &&
    observation_expire_check EX (observation_expire p)
      (observation_expirations EX S SS ix (observation_components p)).

(** Projection explicitly stores bottom observations and coalesces duplicate keys. *)
Definition observation_project {X A} (EX : encoding X) (L : lattice A) (roots : list X)
    (m : assignment X A) : assignment X A :=
  fold_left (fun result x => Map.set EX x (lookup EX L m x) result) roots Map.empty.

(** * Preparation guarantees *)

Lemma observation_key_eqb_spec {X} (EX : encoding X) (x y : X) :
  observation_key_eqb EX x y = true <-> x = y.
Proof.
  unfold observation_key_eqb; rewrite Pos.eqb_eq; split.
  - apply encode_injective.
  - now intros ->.
Qed.

Lemma observation_existsb_key {X} (EX : encoding X) (x : X) (xs : list X) :
  existsb (observation_key_eqb EX x) xs = true <-> In x xs.
Proof.
  rewrite existsb_exists; split.
  - intros [y [Hy Hsame]]; apply observation_key_eqb_spec in Hsame; now subst y.
  - intro Hin; exists x; split; [exact Hin|apply observation_key_eqb_spec; reflexivity].
Qed.

Lemma observation_existsb_key_false {X} (EX : encoding X) (x : X) (xs : list X) :
  existsb (observation_key_eqb EX x) xs = false <-> ~ In x xs.
Proof.
  rewrite <- not_true_iff_false, (observation_existsb_key EX x xs); reflexivity.
Qed.

(** * Indexed constraint occurrences *)

(** Internal occurrence identifiers preserve duplicates without requiring a client encoding. *)
Fixpoint observation_number {C} (next : nat) (cs : list C) : Map.t nat C :=
  match cs with
  | [] => Map.empty
  | c :: rest => Map.set nat_encoding next c (observation_number (S next) rest)
  end.

Definition observation_label {C} (fallback : C) (table : Map.t nat C) (i : nat) : C :=
  match Map.get nat_encoding i table with
  | Some c => c
  | None => fallback
  end.

Definition observation_system {X C A} (S : System.t X C A) (fallback : C) :
    System.t X nat A :=
  let label := observation_label fallback (observation_number 0 (System.constraints S)) in
  System.Make (seq 0 (length (System.constraints S)))
    (fun i => System.target S (label i)) (fun i => System.rhs S (label i)).

Definition observation_static {X C A} (S : System.t X C A) (SS : System.static S)
    (fallback : C) : System.static (observation_system S fallback).
Proof.
  let label := constr:(observation_label fallback (observation_number 0 (System.constraints S))) in
  refine (System.Static (fun i => deps SS (label i))
    (fun i => side_targets SS (label i)) _ _).
  - intros i s; exact (System.reads_within SS
      (observation_label fallback (observation_number 0 (System.constraints S)) i) s).
  - intros i s; exact (System.sides_within SS
      (observation_label fallback (observation_number 0 (System.constraints S)) i) s).
Defined.

Lemma observation_number_get {C} (cs : list C) (next offset : nat) :
  Map.get nat_encoding (next + offset) (observation_number next cs) = nth_error cs offset.
Proof.
  revert next offset; induction cs as [|c cs IH]; intros next [|offset].
  - apply Map.get_empty.
  - apply Map.get_empty.
  - cbn [observation_number nth_error]; rewrite Nat.add_0_r; apply Map.get_set_same.
  - cbn [observation_number nth_error]; rewrite Map.get_set_other by lia.
    replace (next + S offset) with (S next + offset) by lia; apply IH.
Qed.

Lemma observation_labels {C} (fallback : C) (cs : list C) (next : nat) :
  map (observation_label fallback (observation_number next cs)) (seq next (length cs)) = cs.
Proof.
  apply nth_error_ext; intro offset; rewrite nth_error_map.
  destruct (lt_dec offset (length cs)) as [Hlt|Hge].
  - rewrite nth_error_seq, (proj2 (Nat.ltb_lt _ _) Hlt).
    change (Some (observation_label fallback (observation_number next cs) (next + offset)) =
      nth_error cs offset).
    unfold observation_label; rewrite observation_number_get.
    destruct (nth_error cs offset) eqn:Hnth; [reflexivity|].
    apply nth_error_None in Hnth; lia.
  - rewrite nth_error_seq, (proj2 (Nat.ltb_ge _ _) (proj1 (Nat.nlt_ge _ _) Hge)).
    cbn [option_map]; symmetry; apply nth_error_None; lia.
Qed.

(** * Deterministic component schedules *)

(** All component members are entries, so the induced WTO also visits isolated unknowns. *)
Definition observation_graph {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (members : list X) : Graph.t X (X * X) :=
  set_entries (induced EX (FinSet.of_list EX members) (dependency_graph EX S SS)) members.

Definition observation_local_code {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (members : list X) : nested_code X :=
  nested_tree (wto_total (prepare EX (observation_graph EX S SS members))).

Module ObservationComponent.

(** A prepared component carries its code, local output keys and boundary expiration list. *)
Record t (X C : Type) : Type := Make {
  members : list X;
  code : NestedPlan.t X C;
  outputs : list X;
  expire : list X
}.

Arguments Make {X C}.
Arguments members {X C}.
Arguments code {X C}.
Arguments outputs {X C}.
Arguments expire {X C}.

End ObservationComponent.
Import ObservationComponent.

Definition observation_restrict_targets {X C} (EX : encoding X) (targets : Map.t X (list C))
    (members : list X) : Map.t X (list C) :=
  fold_right (fun x restricted => Map.set EX x (index_get EX targets x) restricted)
    Map.empty members.

Definition observation_component_on {X D E} (EX : encoding X) (graph : Graph.t X E)
    (targets : Map.t X (list D)) (roots : FinSet.t X)
    (expiration : Map.t X (list X)) (members : list X) : ObservationComponent.t X D :=
  let local_graph := set_entries (induced EX (FinSet.of_list EX members) graph) members in
  let code := nested_tree (wto_total (prepare EX local_graph)) in
  let plan := NestedPlan.Make code (nested_members EX code)
    (observation_restrict_targets EX targets members)
    (FinSet.of_list EX (nested_heads code)) in
  ObservationComponent.Make members plan (filter (fun x => FinSet.mem EX x roots) members)
    (match members with [] => [] | h :: _ => index_get EX expiration h end).

Definition observation_component {X C D A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (targets : Map.t X (list D)) (roots : FinSet.t X)
    (expiration : Map.t X (list X)) (members : list X) : ObservationComponent.t X D :=
  observation_component_on EX (dependency_graph EX S SS) targets roots expiration members.

Definition observation_compile_targets {X C D A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (targets : Map.t X (list D)) (roots : list X)
    (p : observation_plan X) : list (ObservationComponent.t X D) :=
  let graph := dependency_graph EX S SS in
  let selected := FinSet.of_list EX roots in
  map (observation_component_on EX graph targets selected (observation_expire p))
    (observation_components p).

Definition observation_compile {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (fallback : C) (roots : list X) (p : observation_plan X) :
    list (ObservationComponent.t X nat) :=
  observation_compile_targets EX S SS (nested_targets EX (observation_system S fallback)) roots p.

(** * Component-boundary machine *)

Module ObservationState.

(** The selected output map is retained separately from the evictable working assignment. *)
Record t (X C A : Type) : Type := Make {
  active : ObservationComponent.t X C;
  pending : list (ObservationComponent.t X C);
  local : NestedState.t X C A;
  observed : assignment X A
}.

Arguments Make {X C A}.
Arguments active {X C A}.
Arguments pending {X C A}.
Arguments local {X C A}.
Arguments observed {X C A}.

End ObservationState.
Import ObservationState.

Definition observation_start_local {X C A} (component : ObservationComponent.t X C)
    (values : assignment X A) : NestedState.t X C A :=
  NestedState.Make values [] [NestedFrame.Make (NestedPlan.root (code component)) None]
    FinSet.empty false.

Definition observation_record {X A} (EX : encoding X) (L : lattice A) (keys : list X)
    (values output : assignment X A) : assignment X A :=
  fold_left (fun output x => Map.set EX x (lookup EX L values x) output) keys output.

Definition observation_evict {X A} (EX : encoding X) (keys : list X)
    (values : assignment X A) : assignment X A :=
  fold_left (fun values x => Map.remove EX x values) keys values.

(** A tick pays one nested transition; recording, eviction and starting the next SCC are free. *)
Definition observation_tick {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (evict : bool)
    (result : ObservationState.t X C A + (assignment X A * assignment X A)) :
    ObservationState.t X C A + (assignment X A * assignment X A) :=
  match result with
  | inr finished => inr finished
  | inl state =>
    let component := active state in
    match nested_step EX L (code component) st S (local state) with
    | Some next => inl (ObservationState.Make component (pending state) next (observed state))
    | None =>
      let values := NestedState.current (local state) in
      let output := observation_record EX L (outputs component) values (observed state) in
      let retained := if evict then observation_evict EX (expire component) values else values in
      match pending state with
      | [] => inr (retained, output)
      | next :: rest =>
        inl (ObservationState.Make next rest (observation_start_local next retained) output)
      end
    end
  end.

(** Binary function composition bounds stack depth independently of the number of iterations. *)
Fixpoint observation_repeat {B} (tick : B -> B) (fuel : positive) (state : B) : B :=
  match fuel with
  | xH => tick state
  | xO smaller => observation_repeat tick smaller (observation_repeat tick smaller state)
  | xI smaller => tick (observation_repeat tick smaller (observation_repeat tick smaller state))
  end.

Definition observation_execute {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (schedule : list (ObservationComponent.t X C)) (evict : bool)
    (fuel : positive) : option (assignment X A * assignment X A) :=
  match schedule with
  | [] => Some (Map.empty, Map.empty)
  | first :: rest =>
    let initial := ObservationState.Make first rest
      (observation_start_local first Map.empty) Map.empty in
    match observation_repeat (observation_tick EX L st S evict) fuel (inl initial) with
    | inl _ => None
    | inr result => Some result
    end
  end.

(** The full reference follows the fixed component schedule and retains its complete assignment. *)
Definition observation_full_reference {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
    (p : observation_plan X) (fuel : positive) : option (assignment X A) :=
  if observation_plan_check EX S SS ix roots p then
    match System.constraints S with
    | [] => Some Map.empty
    | fallback :: _ =>
      let numbered := observation_system S fallback in
      let targets := nested_targets EX numbered in
      option_map fst (observation_execute EX L st numbered
        (observation_compile_targets EX S SS targets roots p) false fuel)
    end
  else None.

(** The observation reference projects the complete fixed-schedule result. *)
Definition observation_reference {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
    (p : observation_plan X) (fuel : positive) : option (assignment X A) :=
  option_map (observation_project EX L roots)
    (observation_full_reference EX L st S SS ix roots p fuel).

(** The memory-conscious runner returns only its separately retained observations. *)
Definition observation_run {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
    (p : observation_plan X) (fuel : positive) : option (assignment X A) :=
  if observation_plan_check EX S SS ix roots p then
    match System.constraints S with
    | [] => Some Map.empty
    | fallback :: _ =>
      let numbered := observation_system S fallback in
      let targets := nested_targets EX numbered in
      option_map snd (observation_execute EX L st numbered
        (observation_compile_targets EX S SS targets roots p) true fuel)
    end
  else None.

(** Reference observations are exactly the projection of the complete fixed-schedule execution. *)
Theorem observation_reference_projection {X C A} (EX : encoding X) (L : lattice A)
    (st : strategy) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (roots : list X) (p : observation_plan X) (fuel : positive) :
  observation_reference EX L st S SS ix roots p fuel =
    option_map (observation_project EX L roots)
      (observation_full_reference EX L st S SS ix roots p fuel).
Proof.
  reflexivity.
Qed.

Lemma observation_side_free_spec {X C A} (S : System.t X C A) (SS : System.static S) :
  observation_side_free S SS = true <->
  forall c, In c (System.constraints S) -> side_targets SS c = [].
Proof.
  unfold observation_side_free; rewrite forallb_forall; split.
  - intros H c Hc; specialize (H c Hc); destruct (side_targets SS c); congruence.
  - intros H c Hc; rewrite H by exact Hc; reflexivity.
Qed.

Lemma observation_roots_check_spec {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (roots : list X) :
  observation_roots_check EX S SS roots = true <->
  forall x, In x roots -> In x (unknowns EX S SS).
Proof.
  unfold observation_roots_check; rewrite forallb_forall.
  split; intros H x Hx; specialize (H x Hx).
  - now apply FinSet.of_list_spec in H.
  - now apply FinSet.of_list_spec.
Qed.

(** Every side-free static system admits a plan for observations in its universe. *)
Theorem observation_plan_complete {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  sys_index_laws EX S SS ix ->
  (forall c, In c (System.constraints S) -> side_targets SS c = []) ->
  (forall x, In x roots -> In x (unknowns EX S SS)) ->
  exists p, observation_prepare EX S SS ix roots = Some p.
Proof.
  intros Hix Hsides Hroots; exists (observation_canonical EX S SS ix).
  unfold observation_prepare.
  rewrite (proj2 (observation_side_free_spec S SS) Hsides).
  rewrite (proj2 (observation_roots_check_spec EX S SS roots) Hroots); reflexivity.
Qed.

(** * Component order and local WTO validation *)

Lemma observation_map_combine {B D} (f : D -> B) (xs : list B) (ys : list D) :
  length xs = length ys ->
  (forall x y, In (x, y) (combine xs ys) -> f y = x) -> map f ys = xs.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] Hlength Hagree;
    cbn in Hlength; try discriminate; [reflexivity|].
  cbn; rewrite (Hagree x y (or_introl eq_refl)); f_equal.
  apply IH; [lia|intros a b Hin; apply Hagree; now right].
Qed.

Definition observation_owner {X} (EX : encoding X) (r : scc_result X)
    (members : list X) : positive :=
  match members with
  | [] => 1%positive
  | h :: _ => scc_owner EX r h
  end.

Lemma observation_nth_error_combine {B D} (xs : list B) (ys : list D)
    (n : nat) (x : B) (y : D) :
  nth_error xs n = Some x -> nth_error ys n = Some y ->
  nth_error (combine xs ys) n = Some (x, y).
Proof.
  revert xs ys; induction n as [|n IH]; intros [|a xs] [|b ys] Hx Hy;
    cbn in *; try discriminate; [congruence|eapply IH; eassumption].
Qed.

Lemma observation_component_owner {X E} (EX : encoding X) (g : Graph.t X E)
    (p : prepared EX g) (members : list X) (x : X) :
  In members (components (scc p)) -> In x members ->
  Map.get EX x (comp_of (scc p)) = Some (observation_owner EX (scc p) members).
Proof.
  intros Hcomponent Hx.
  destruct (scc_within_indexes EX g p (Graph.nodes g))
    as [_ [Hnonempty [Hlength [Hat [Hids [Howner Horder]]]]]].
  change (length (component_ids (scc p)) = length (components (scc p))) in Hlength.
  assert (Hpair : exists i, In (i, members)
    (combine (component_ids (scc p)) (components (scc p)))).
  { apply in_split in Hcomponent; destruct Hcomponent as [before [after Hsplit]].
    destruct (nth_error (component_ids (scc p)) (length before)) as [i|] eqn:Hnth.
    - exists i; apply (nth_error_In (combine _ _) (length before)).
      apply observation_nth_error_combine; [exact Hnth|].
      rewrite Hsplit, nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity.
    - apply nth_error_None in Hnth; rewrite Hsplit, length_app in Hlength.
      cbn [length] in Hlength; lia. }
  destruct Hpair as [i Hi]; apply Hat in Hi.
  assert (Hget : forall y, In y members -> Map.get EX y (comp_of (scc p)) = Some i).
  { intros y Hy; apply Howner; exists members; auto. }
  destruct members as [|h body]; [contradiction|].
  unfold observation_owner, scc_owner.
  rewrite (Hget h (or_introl eq_refl)); apply Hget; exact Hx.
Qed.

Lemma observation_owner_order {X E} (EX : encoding X) (g : Graph.t X E)
    (p : prepared EX g) :
  map (observation_owner EX (scc p)) (rev (components (scc p))) =
    rev (component_ids (scc p)).
Proof.
  rewrite map_rev; f_equal.
  destruct (scc_within_indexes EX g p (Graph.nodes g))
    as [_ [Hnonempty [Hlength [Hat [Hids [Howner Horder]]]]]].
  apply observation_map_combine; [exact Hlength|].
  intros i members Hi.
  assert (Hmembers : In members (components (scc p))) by (eapply in_combine_r; exact Hi).
  apply Hat in Hi; destruct members as [|h body].
  - exfalso; exact (Hnonempty [] Hmembers eq_refl).
  - unfold observation_owner, scc_owner.
    assert (Hget : Map.get EX h (comp_of (scc p)) = Some i).
    { apply Howner; exists (h :: body); split; [exact Hi|now left]. }
    now rewrite Hget.
Qed.

(** SCCs cover each unknown once, and empty components are never emitted. *)
Lemma observation_order_partition {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) :
  NoDup (concat (observation_order EX S SS)) /\
  (forall x, In x (concat (observation_order EX S SS)) <-> In x (unknowns EX S SS)) /\
  forall members, In members (observation_order EX S SS) -> members <> [].
Proof.
  unfold observation_order.
  destruct (scc_within_indexes EX (dependency_graph EX S SS)
    (prepare EX (dependency_graph EX S SS)) (unknowns EX S SS))
    as [Hdistinct [Hnonempty Hrest]].
  split.
  - eapply Permutation_NoDup; [apply Permutation_sym, tarjan_concat_rev|exact Hdistinct].
  - split.
    + intro x; rewrite tarjan_concat_rev_in.
      apply scc_within_members; [apply dependency_graph_ready|intros y Hy; exact Hy].
    + intros members Hin; apply Hnonempty; now apply in_rev.
Qed.

(** A declared read of the current component cannot come from a later component. *)
Lemma observation_order_no_future {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (prefix : list (list X)) (members : list X)
    (suffix : list (list X)) (x y : X) :
  observation_order EX S SS = prefix ++ members :: suffix ->
  In x members -> flows SS y x -> ~ In y (concat suffix).
Proof.
  intros Hsplit Hx Hflow Hy.
  apply in_concat in Hy; destruct Hy as [later [Hlater Hy]].
  set (g := dependency_graph EX S SS).
  set (p := prepare EX g).
  set (r := scc p).
  assert (Hmembers : In members (components r)).
  { apply in_rev; change (In members (observation_order EX S SS)).
    rewrite Hsplit; apply in_or_app; right; now left. }
  assert (Hlater_component : In later (components r)).
  { apply in_rev; change (In later (observation_order EX S SS)).
    rewrite Hsplit; apply in_or_app; right; now right. }
  pose proof (observation_component_owner EX g p members x Hmembers Hx) as Howner_x.
  pose proof (observation_component_owner EX g p later y Hlater_component Hy) as Howner_y.
  set (i := observation_owner EX r members) in *.
  set (j := observation_owner EX r later) in *.
  change (Map.get EX x (comp_of r) = Some i) in Howner_x.
  change (Map.get EX y (comp_of r) = Some j) in Howner_y.
  assert (Hbefore : before (rev (component_ids r)) i j).
  { unfold i, j, r; rewrite <- (observation_owner_order EX g p).
    apply wto_before_map.
    apply in_split in Hlater; destruct Hlater as [middle [tail Hlater]].
    exists prefix, middle, tail.
    change (observation_order EX S SS = prefix ++ members :: middle ++ later :: tail).
    now rewrite Hsplit, Hlater. }
  destruct (scc_within_indexes EX g p (Graph.nodes g))
    as [_ [_ [_ [_ [Hids [_ Horder]]]]]].
  assert (Hdistinct : NoDup (rev (component_ids r))) by now apply NoDup_rev.
  assert (Hdifferent : i <> j).
  { intro Heq; rewrite <- Heq in Hbefore; exact (dfs_before_irrefl _ _ Hdistinct Hbefore). }
  assert (Hedge : In (y, x) (Graph.out g y)).
  { apply dependency_out_spec; auto. }
  destruct (flows_unknowns EX S SS y x Hflow) as [Hy_unknown Hx_unknown].
  destruct (scc_reverse_topological EX g p (y, x) (Graph.nodes g)
    (dependency_graph_ready EX S SS) (fun _ H => H) Hedge Hy_unknown Hx_unknown)
    as [source_id [target_id [Hsource [Htarget Hbound]]]].
  change (Map.get EX y (comp_of r) = Some source_id) in Hsource.
  change (Map.get EX x (comp_of r) = Some target_id) in Htarget.
  rewrite Howner_x in Htarget; rewrite Howner_y in Hsource.
  inversion Htarget; inversion Hsource; subst target_id source_id.
  assert (Hstrict : (i < j)%positive) by lia.
  assert (Hi : In i (component_ids r)).
  { apply in_rev; apply dfs_before_indices in Hbefore.
    destruct Hbefore as [a [b [_ [Ha _]]]]; eapply nth_error_In; exact Ha. }
  assert (Hj : In j (component_ids r)).
  { apply in_rev; apply dfs_before_indices in Hbefore.
    destruct Hbefore as [a [b [_ [_ Hb]]]]; eapply nth_error_In; exact Hb. }
  pose proof (Horder j i Hj Hi Hstrict) as Hreverse.
  apply (dfs_before_irrefl _ i Hdistinct).
  eapply dfs_before_trans; eassumption.
Qed.

(** * Semantic validation of supplied plans *)

Lemma observation_seteq_spec {X} (EX : encoding X) (xs ys : list X) :
  observation_seteq EX xs ys = true <-> forall x, In x xs <-> In x ys.
Proof.
  unfold observation_seteq; rewrite andb_true_iff, !forallb_forall.
  split.
  - intros [Hleft Hright] x; split; intro Hin.
    + exact (proj1 (observation_existsb_key EX x ys) (Hleft x Hin)).
    + exact (proj1 (observation_existsb_key EX x xs) (Hright x Hin)).
  - intro Hagree; split; intros x Hin; apply observation_existsb_key, (Hagree x); exact Hin.
Qed.

Lemma observation_seteq_refl {X} (EX : encoding X) (xs : list X) :
  observation_seteq EX xs xs = true.
Proof.
  apply observation_seteq_spec; tauto.
Qed.

Lemma observation_expire_check_refl {X} (EX : encoding X) (expiration : Map.t X (list X)) :
  observation_expire_check EX expiration expiration = true.
Proof.
  unfold observation_expire_check; apply andb_true_iff; split;
    (apply Map.forall2_spec; intros p xs Hget; rewrite Hget; apply observation_seteq_refl).
Qed.

Lemma observation_nodup_check_spec {X} (EX : encoding X) (xs : list X) :
  observation_nodup_check EX xs = true <-> NoDup xs.
Proof.
  induction xs as [|x xs IH]; cbn [observation_nodup_check].
  - split; [intro H; constructor|reflexivity].
  - rewrite andb_true_iff, negb_true_iff, observation_existsb_key_false, IH, NoDup_cons_iff.
    tauto.
Qed.

Lemma observation_boundaries_spec {X} (order : list (list X)) (component : list X)
    (suffix : list (list X)) :
  In (component, suffix) (observation_boundaries order) <->
    exists prefix, order = prefix ++ component :: suffix.
Proof.
  induction order as [|head order IH]; cbn [observation_boundaries In].
  - split; [contradiction|intros [[|p prefix] Heq]; discriminate].
  - split.
    + intros [Heq|Hin].
      * inversion Heq; subst; exists []; reflexivity.
      * apply IH in Hin; destruct Hin as [prefix Heq]; exists (head :: prefix); now rewrite Heq.
    + intros [[|p prefix] Heq].
      * cbn [app] in Heq; inversion Heq; subst; now left.
      * cbn [app] in Heq; right; apply IH; exists prefix.
        injection Heq as Hhead Htail; exact Htail.
Qed.

Lemma observation_boundary_check_spec {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (component : list X) (suffix : list (list X)) :
  observation_boundary_check EX S SS component suffix = true <->
  forall c, In c (System.constraints S) -> In (System.target S c) component ->
    forall x, In x (deps SS c) -> ~ In x (concat suffix).
Proof.
  unfold observation_boundary_check; rewrite forallb_forall; split.
  - intros Hcheck c Hc Htarget x Hread Hin.
    specialize (Hcheck c Hc).
    rewrite (proj2 (FinSet.of_list_spec EX (System.target S c) component) Htarget) in Hcheck.
    apply forallb_forall with (x := x) in Hcheck; [|exact Hread].
    apply negb_true_iff in Hcheck.
    rewrite (proj2 (FinSet.of_list_spec EX x (concat suffix)) Hin) in Hcheck; discriminate.
  - intros Hforward c Hc.
    destruct (FinSet.mem EX (System.target S c) (FinSet.of_list EX component)) eqn:Htarget;
      [|reflexivity].
    apply FinSet.of_list_spec in Htarget; apply forallb_forall; intros x Hread.
    apply negb_true_iff.
    destruct (FinSet.mem EX x (FinSet.of_list EX (concat suffix))) eqn:Hmem; [|reflexivity].
    exfalso; apply (Hforward c Hc Htarget x Hread).
    now apply FinSet.of_list_spec in Hmem.
Qed.

Lemma observation_forward_check_spec {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (order : list (list X)) :
  observation_forward_check EX S SS order = true <-> observation_forward_valid S SS order.
Proof.
  unfold observation_forward_check; rewrite forallb_forall; split.
  - intros Hcheck prefix component suffix Hsplit.
    apply (proj1 (observation_boundary_check_spec EX S SS component suffix)).
    apply (Hcheck (component, suffix)).
    apply observation_boundaries_spec; now exists prefix.
  - intros Hforward [component suffix] Hin; apply observation_boundaries_spec in Hin.
    destruct Hin as [prefix Hsplit].
    apply (proj2 (observation_boundary_check_spec EX S SS component suffix)).
    apply (Hforward prefix component suffix Hsplit).
Qed.

Lemma observation_components_checked {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (order : list (list X)) :
  observation_components_check EX S SS order = true ->
  NoDup (concat order) /\
  (forall x, In x (concat order) <-> In x (unknowns EX S SS)) /\
  (forall component, In component order -> component <> []) /\
  observation_forward_valid S SS order.
Proof.
  unfold observation_components_check; rewrite !andb_true_iff.
  intros [[[[Hdistinct Hcover] Hnonempty] Hclasses] Hforward].
  split; [exact (proj1 (observation_nodup_check_spec EX (concat order)) Hdistinct)|].
  split; [exact (proj1 (observation_seteq_spec EX _ _) Hcover)|]; split.
  - intros component Hin Heq; apply forallb_forall with (x := component) in Hnonempty;
      [now rewrite Heq in Hnonempty|exact Hin].
  - exact (proj1 (observation_forward_check_spec EX S SS order) Hforward).
Qed.

(** Accepted components are exactly whole SCC classes, independently of their member ordering. *)
Lemma observation_components_classes {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (order : list (list X)) :
  observation_components_check EX S SS order = true ->
  forall component, In component order -> exists members,
    In members (observation_order EX S SS) /\ forall x, In x component <-> In x members.
Proof.
  unfold observation_components_check; rewrite !andb_true_iff.
  intros [[[[Hdistinct Hcover] Hnonempty] Hclasses] Hforward] component Hin.
  apply forallb_forall with (x := component) in Hclasses; [|exact Hin].
  apply existsb_exists in Hclasses; destruct Hclasses as [members [Hmembers Hagree]].
  exists members; split; [exact Hmembers|].
  exact (proj1 (observation_seteq_spec EX component members) Hagree).
Qed.

(** Every supplied SCC partition satisfying the semantic conditions passes component validation. *)
Lemma observation_components_check_complete {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (order : list (list X)) :
  NoDup (concat order) ->
  (forall x, In x (concat order) <-> In x (unknowns EX S SS)) ->
  (forall component, In component order -> component <> []) ->
  (forall component, In component order -> exists members,
    In members (observation_order EX S SS) /\ forall x, In x component <-> In x members) ->
  observation_forward_valid S SS order -> observation_components_check EX S SS order = true.
Proof.
  intros Hdistinct Hcover Hnonempty Hclasses Hforward.
  unfold observation_components_check; apply andb_true_iff; split.
  - apply andb_true_iff; split.
    + apply andb_true_iff; split.
      * apply andb_true_iff; split.
        -- now apply observation_nodup_check_spec.
        -- now apply observation_seteq_spec.
      * apply forallb_forall; intros [|h body] Hin; [exfalso; apply (Hnonempty [] Hin)|];
          reflexivity.
    + apply forallb_forall; intros component Hin.
      destruct (Hclasses component Hin) as [members [Hmembers Hagree]].
      apply existsb_exists; exists members; split; [exact Hmembers|].
      apply observation_seteq_spec; exact Hagree.
  - now apply observation_forward_check_spec.
Qed.

Lemma observation_canonical_components_checked {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) :
  observation_components_check EX S SS (observation_order EX S SS) = true.
Proof.
  destruct (observation_order_partition EX S SS) as [Hdistinct [Hcover Hnonempty]].
  unfold observation_components_check; apply andb_true_iff; split.
  - apply andb_true_iff; split.
    + apply andb_true_iff; split.
      * apply andb_true_iff; split.
        -- now apply observation_nodup_check_spec.
        -- now apply observation_seteq_spec.
      * apply forallb_forall; intros [|h body] Hin; [exfalso; apply (Hnonempty [] Hin)|];
          reflexivity.
    + apply forallb_forall; intros component Hin; apply existsb_exists.
      exists component; split; [exact Hin|apply observation_seteq_refl].
  - apply observation_forward_check_spec.
    intros prefix component suffix Hsplit c Hc Htarget x Hread.
    apply (observation_order_no_future EX S SS prefix component suffix
      (System.target S c) x Hsplit Htarget).
    exists c; auto.
Qed.

(** Every prepared plan passes validation of the contracted semantic conditions. *)
Theorem observation_prepare_checked {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (roots : list X) (p : observation_plan X) :
  sys_index_laws EX S SS ix -> observation_prepare EX S SS ix roots = Some p ->
  observation_plan_check EX S SS ix roots p = true.
Proof.
  intros Hix; unfold observation_prepare.
  destruct (observation_side_free S SS && observation_roots_check EX S SS roots)
    eqn:Hvalid; intro Hprepare; [|discriminate].
  inversion Hprepare; subst p; unfold observation_plan_check.
  rewrite Hvalid; cbn [andb observation_canonical observation_components observation_expire].
  rewrite observation_canonical_components_checked; cbn [andb].
  apply observation_expire_check_refl.
Qed.

Lemma observation_graph_ready {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (members : list X) :
  incl members (unknowns EX S SS) ->
  ready EX (observation_graph EX S SS members)
    (prepare EX (observation_graph EX S SS members)).
Proof.
  intro Hmembers.
  destruct (dependency_graph_flows EX S SS) as [Hwf [Hout Hflows]].
  apply prepare_ready.
  - constructor.
    + apply NoDup_filter; apply nodes_nodup; exact Hwf.
    + intros x Hx; apply filter_In; split; [apply Hmembers; exact Hx|].
      apply FinSet.of_list_spec; exact Hx.
    + intros x e He; apply filter_In in He; exact (out_source Hwf x e (proj1 He)).
    + intros x e Hx He; apply filter_In in Hx, He; apply filter_In; split.
      * exact (out_target_in Hwf x e (proj1 Hx) (proj1 He)).
      * exact (proj2 He).
  - intro x; apply NoDup_filter, Hout.
Qed.

Lemma observation_graph_nodes {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (members : list X) (x : X) :
  incl members (unknowns EX S SS) ->
  (reachable (observation_graph EX S SS members) x <-> In x members).
Proof.
  intro Hmembers; split.
  - intro Hreach.
    pose proof (reachable_in_nodes _ x (proj1 (observation_graph_ready EX S SS members
      Hmembers)) Hreach) as Hin.
    apply filter_In in Hin; exact (proj1 (FinSet.of_list_spec EX x members) (proj2 Hin)).
  - intro Hin; apply reachable_entry; exact Hin.
Qed.

(** Each local WTO visits exactly its component, including members with no constraints. *)
Lemma observation_local_covers {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (members : list X) :
  incl members (unknowns EX S SS) ->
  NoDup (nested_vertices (observation_local_code EX S SS members)) /\
  forall x, In x (nested_vertices (observation_local_code EX S SS members)) <-> In x members.
Proof.
  intro Hmembers.
  pose proof (wto_total_valid _ _ _ (observation_graph_ready EX S SS members Hmembers))
    as [Hbalanced [Hdistinct [Hcover Hedges]]].
  unfold observation_local_code; rewrite <- nested_vertices_tokens.
  rewrite nested_tree_tokens by exact Hbalanced; rewrite <- wto_order_vertices.
  split; [exact Hdistinct|].
  intro x; rewrite Hcover; apply observation_graph_nodes; exact Hmembers.
Qed.

Lemma observation_restrict_targets_get {X C} (EX : encoding X) (targets : Map.t X (list C))
    (members : list X) (x : X) :
  index_get EX (observation_restrict_targets EX targets members) x =
    if existsb (observation_key_eqb EX x) members then index_get EX targets x else [].
Proof.
  unfold observation_restrict_targets; induction members as [|y members IH].
  - apply index_get_empty.
  - cbn [fold_right existsb]; unfold index_get at 1.
    destruct (observation_key_eqb EX x y) eqn:Heq.
    + apply observation_key_eqb_spec in Heq; subst y; rewrite Map.get_set_same; reflexivity.
    + rewrite Map.get_set_other.
      * exact IH.
      * intro Hequal; subst y; unfold observation_key_eqb in Heq.
        rewrite Pos.eqb_refl in Heq; discriminate.
Qed.

Definition observation_subsystem {X C A} (EX : encoding X) (S : System.t X C A)
    (members : list X) : System.t X C A :=
  let selected := FinSet.of_list EX members in
  System.Make (filter (fun c => FinSet.mem EX (System.target S c) selected)
    (System.constraints S)) (System.target S) (System.rhs S).

Definition observation_substatic {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (members : list X) :
    System.static (observation_subsystem EX S members) :=
  @System.Static X C A (observation_subsystem EX S members)
    (deps SS) (side_targets SS) (System.reads_within SS) (System.sides_within SS).

Lemma observation_sides_empty {X C A} (S : System.t X C A) (SS : System.static S)
    (c : C) (s : X -> A) :
  side_targets SS c = [] -> Query.sides (System.rhs S c) s = [].
Proof.
  intro Hdeclared; destruct (Query.sides (System.rhs S c) s) as [|[x a] rest] eqn:Hsides;
    [reflexivity|].
  exfalso; pose proof (System.sides_within SS c s x) as Hwithin.
  rewrite Hsides, Hdeclared in Hwithin; exact (Hwithin (or_introl eq_refl)).
Qed.

Lemma observation_wto_cycle_head {V E} (g : Graph.t V E) (w : wto V)
    (v : V) (es : list E) :
  wto_valid g w -> reachable g v -> es <> [] -> path g v es v ->
  exists h, In h (schedule_heads w) /\ (h = v \/ In h (map (Graph.target g) es)).
Proof.
  intros Hvalid Hv Hnonempty Hpath.
  destruct (wto_valid_cycles g w Hvalid v es Hv Hnonempty Hpath) as [h [Hh Hcontains]].
  assert (Hrow : exists stack, In (v, stack) (annotate [] w)).
  { apply (proj2 (proj1 (proj2 (proj2 Hvalid)) v)) in Hv.
    unfold wto_order in Hv; apply in_map_iff in Hv.
    destruct Hv as [[x stack] [Heq Hin]]; cbn in Heq; subst x; now exists stack. }
  destruct Hrow as [stack Hrow].
  specialize (Hcontains v stack (or_introl eq_refl) Hrow).
  destruct (schedule_annotate_heads w [] v h stack Hrow Hcontains) as [Hbad|Hhead];
    [contradiction|exists h; auto].
Qed.

Lemma observation_flow_path {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (members : list X) (R : X -> X -> Prop) (W : X -> bool) :
  (forall y x, R y x -> flows SS y x /\ In x members) ->
  forall u v, clos_trans X (fun y x => R y x /\ W x = false) u v ->
  In v members /\ W v = false /\
    exists es, es <> [] /\ path (observation_graph EX S SS members) u es v /\
      forall e, In e es -> W (snd e) = false.
Proof.
  intros Hflow u v Hpath; induction Hpath as [u v [Hedge HW]|u v z Huv IHuv Hvz IHvz].
  - destruct (Hflow u v Hedge) as [Hdeclared Hv].
    split; [exact Hv|]; split; [exact HW|]; exists [(u, v)].
    split; [discriminate|]; split.
    + apply (@path_cons X (X * X) (observation_graph EX S SS members) (u, v) [] v).
      * apply filter_In; split; [apply dependency_out_spec; auto|].
        apply FinSet.of_list_spec; exact Hv.
      * constructor.
    + intros e [Heq|Hbad]; [now subst e|contradiction].
  - destruct IHuv as [_ [_ [first [Hfirst [Hpath_first Htargets_first]]]]].
    destruct IHvz as [Hz [HWz [last [Hlast [Hpath_last Htargets_last]]]]].
    split; [exact Hz|]; split; [exact HWz|]; exists (first ++ last).
    split; [intro Hnil; apply app_eq_nil in Hnil; tauto|]; split.
    + eapply tarjan_path_append; eassumption.
    + intros e Hin; apply in_app_iff in Hin; destruct Hin; auto.
Qed.

(** Local WTO heads cut cycles on their induced component, independently of global heads. *)
Lemma observation_local_cuts {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (T : System.t X D B) (TS : System.static T)
    (members : list X) :
  incl members (unknowns EX S SS) ->
  (forall y x, flows TS y x -> flows SS y x /\ In x members) ->
  cuts_every_cycle TS (fun x =>
    FinSet.mem EX x (FinSet.of_list EX (nested_heads (observation_local_code EX S SS members)))).
Proof.
  intros Hmembers Hflows v Hcycle.
  set (W := fun x => FinSet.mem EX x
    (FinSet.of_list EX (nested_heads (observation_local_code EX S SS members)))) in *.
  destruct (observation_flow_path EX S SS members (flows TS) W Hflows v v Hcycle)
    as [Hv [Hfree [es [Hnonempty [Hpath Htargets]]]]].
  set (g := observation_graph EX S SS members) in *.
  pose proof (wto_total_valid _ _ _ (observation_graph_ready EX S SS members Hmembers))
    as Hvalid.
  destruct (observation_wto_cycle_head g (wto_total (prepare EX g)) v es Hvalid
    (@reachable_entry X (X * X) g v Hv) Hnonempty Hpath) as [h [Hhead Hh]].
  assert (Hmem : W h = true).
  { unfold W, observation_local_code; rewrite <- nested_heads_tokens.
    rewrite nested_tree_tokens by exact (proj1 Hvalid); apply FinSet.of_list_spec; exact Hhead. }
  assert (Hnot : W h = false).
  { destruct Hh as [Heq|Hin]; [now subst h|].
    apply in_map_iff in Hin; destruct Hin as [e [Heq Hin]]; subst h; exact (Htargets e Hin). }
  congruence.
Qed.

Lemma observation_subflow {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (members : list X) :
  (forall c, In c (System.constraints S) -> side_targets SS c = []) ->
  forall y x, flows (observation_substatic EX S SS members) y x ->
    flows SS y x /\ In x members.
Proof.
  intros Hsides y x [c [Hc [Hy Hx]]].
  apply filter_In in Hc; destruct Hc as [Hc Htarget].
  change (x = System.target S c \/ In x (side_targets SS c)) in Hx.
  destruct Hx as [Hx|Hx].
  - subst x; split; [exists c; auto|now apply FinSet.of_list_spec in Htarget].
  - rewrite Hsides in Hx by exact Hc; contradiction.
Qed.

Lemma observation_label_in {X C A} (S : System.t X C A) (fallback : C) (i : nat) :
  In i (System.constraints (observation_system S fallback)) ->
  In (observation_label fallback (observation_number 0 (System.constraints S)) i)
    (System.constraints S).
Proof.
  intro Hi.
  pose proof (in_map (observation_label fallback (observation_number 0 (System.constraints S)))
    (seq 0 (length (System.constraints S))) i Hi) as Hmapped.
  rewrite observation_labels in Hmapped; exact Hmapped.
Qed.

Lemma observation_label_covers {X C A} (S : System.t X C A) (fallback : C) (c : C) :
  In c (System.constraints S) -> exists i,
    In i (System.constraints (observation_system S fallback)) /\
    observation_label fallback (observation_number 0 (System.constraints S)) i = c.
Proof.
  rewrite <- (observation_labels fallback (System.constraints S) 0) at 1.
  intros Hin; apply in_map_iff in Hin; destruct Hin as [i [Heq Hi]]; exists i; auto.
Qed.

Lemma observation_system_flows {X C A} (S : System.t X C A) (SS : System.static S)
    (fallback : C) (y x : X) :
  flows (observation_static S SS fallback) y x <-> flows SS y x.
Proof.
  split.
  - intros [i [Hi [Hy Hx]]].
    exists (observation_label fallback (observation_number 0 (System.constraints S)) i).
    split; [apply observation_label_in; exact Hi|]; split; assumption.
  - intros [c [Hc [Hy Hx]]].
    destruct (observation_label_covers S fallback c Hc) as [i [Hi Hlabel]].
    exists i; split; [exact Hi|].
    change (In y (deps SS (observation_label fallback
      (observation_number 0 (System.constraints S)) i)) /\
      (x = System.target S (observation_label fallback
        (observation_number 0 (System.constraints S)) i) \/
       In x (side_targets SS (observation_label fallback
        (observation_number 0 (System.constraints S)) i)))).
    now rewrite Hlabel.
Qed.

(** * Exact last-reader lifetimes *)

Lemma observation_last_reader_member {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (x h : X) :
  observation_last_reader EX S ix order x = Some h -> In h (concat order).
Proof.
  induction order as [|[|head body] rest IH]; cbn [observation_last_reader concat];
    intro Hlast; [discriminate|apply IH; exact Hlast|].
  destruct (observation_last_reader EX S ix rest x) as [last|] eqn:Hrest.
  - inversion Hlast; subst last; apply in_or_app; right; apply IH; reflexivity.
  - destruct (observation_component_uses EX S ix (FinSet.of_list EX (head :: body)) x);
      [inversion Hlast; subst h; apply in_or_app; left; now left|discriminate].
Qed.

Lemma observation_last_reader_app {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (first last : list (list X)) (x : X) :
  observation_last_reader EX S ix (first ++ last) x =
    match observation_last_reader EX S ix last x with
    | Some h => Some h
    | None => observation_last_reader EX S ix first x
    end.
Proof.
  induction first as [|[|head body] first IH]; cbn [app observation_last_reader].
  - destruct (observation_last_reader EX S ix last x); reflexivity.
  - exact IH.
  - rewrite IH; destruct (observation_last_reader EX S ix last x); [reflexivity|].
    destruct (observation_last_reader EX S ix first x); reflexivity.
Qed.

Lemma observation_last_reader_none {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (x : X) :
  observation_last_reader EX S ix order x = None ->
  forall component, In component order ->
    observation_component_uses EX S ix (FinSet.of_list EX component) x = false.
Proof.
  induction order as [|[|head body] rest IH]; cbn [observation_last_reader];
    intros Hlast component Hin; [contradiction| |].
  - destruct Hin as [Heq|Hin].
    + subst component; unfold observation_component_uses.
      change (FinSet.of_list EX []) with (@FinSet.empty X).
      rewrite FinSet.mem_empty; cbn [orb]; induction (readers_of EX ix x) as [|c cs IHcs];
        cbn [existsb]; [reflexivity|now rewrite FinSet.mem_empty, IHcs].
    + apply IH; assumption.
  - destruct (observation_last_reader EX S ix rest x) as [last|] eqn:Hrest;
      [discriminate|].
    destruct (observation_component_uses EX S ix (FinSet.of_list EX (head :: body)) x)
      eqn:Huses; [discriminate|].
    destruct Hin as [Heq|Hin]; [now subst component|apply IH; assumption].
Qed.

Lemma observation_expiration_fold {X C A} (EX : encoding X) (S : System.t X C A)
    (ix : sys_index X C) (order : list (list X)) (xs : list X) (x h : X) :
  In x (index_get EX (fold_right (fun y expiration =>
    match observation_last_reader EX S ix order y with
    | Some last => index_push EX y last expiration
    | None => expiration
    end) Map.empty xs) h) <->
  In x xs /\ observation_last_reader EX S ix order x = Some h.
Proof.
  induction xs as [|y xs IH]; cbn [fold_right].
  - rewrite index_get_empty; cbn; tauto.
  - destruct (observation_last_reader EX S ix order y) as [last|] eqn:Hlast.
    + rewrite index_get_push.
      destruct (Pos.eqb (encode EX h) (encode EX last)) eqn:Heq.
      * apply Pos.eqb_eq in Heq; apply (encode_injective EX) in Heq; subst last.
        cbn [In]; rewrite IH; split.
        -- intros [Heq|[Hin Hreader]]; [subst x; auto|auto].
        -- intros [[Heq|Hin] Hreader]; [now left|right; auto].
      * rewrite IH; cbn [In]; split; [tauto|].
        intros [[Heqxy|Hin] Hreader]; [|auto].
        subst x; rewrite Hlast in Hreader; inversion Hreader; subst last.
        rewrite Pos.eqb_refl in Heq; discriminate.
    + rewrite IH; cbn [In]; split; [tauto|].
      intros [[Heq|Hin] Hreader]; [subst x; congruence|auto].
Qed.

(** An expiration list contains exactly values whose final producer-or-reader is its key. *)
Lemma observation_expirations_spec {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (order : list (list X)) (x h : X) :
  In x (index_get EX (observation_expirations EX S SS ix order) h) <->
  In x (unknowns EX S SS) /\ observation_last_reader EX S ix order x = Some h.
Proof.
  apply observation_expiration_fold.
Qed.

(** Live agreement includes pending producers and every declared input of a pending constraint. *)
Definition observation_needed {X C A} (S : System.t X C A) (SS : System.static S)
    (order : list (list X)) (x : X) : Prop :=
  In x (concat order) \/ exists c, In c (System.constraints S) /\
    In (System.target S c) (concat order) /\ In x (deps SS c).

Lemma observation_needed_suffix {X C A} (S : System.t X C A) (SS : System.static S)
    (first rest : list (list X)) (x : X) :
  observation_needed S SS rest x -> observation_needed S SS (first ++ rest) x.
Proof.
  unfold observation_needed; rewrite concat_app; intro Hneeded.
  destruct Hneeded as [Hin|[c [Hc [Htarget Hread]]]].
  - left; apply in_or_app; now right.
  - right; exists c; split; [exact Hc|]; split; [apply in_or_app; now right|exact Hread].
Qed.

(** At a boundary, every expiring key is absent from all later producers and declared reads. *)
Lemma observation_expiration_safe {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (order prefix : list (list X))
    (h : X) (body : list X) (suffix : list (list X)) (x : X) :
  sys_index_laws EX S SS ix -> NoDup (concat order) ->
  order = prefix ++ (h :: body) :: suffix ->
  In x (index_get EX (observation_expirations EX S SS ix order) h) ->
  ~ observation_needed S SS suffix x.
Proof.
  intros Hix Hdistinct Hsplit Hexpire.
  apply observation_expirations_spec in Hexpire; destruct Hexpire as [_ Hlast].
  assert (Hnot : ~ In h (concat suffix)).
  { rewrite Hsplit, concat_app in Hdistinct; cbn [concat] in Hdistinct.
    change (NoDup (concat prefix ++ h :: (body ++ concat suffix))) in Hdistinct.
    intro Hin; apply (NoDup_remove_2 (concat prefix) (body ++ concat suffix) h Hdistinct).
    apply in_or_app; right; apply in_or_app; now right. }
  assert (Hnone : observation_last_reader EX S ix suffix x = None).
  { rewrite Hsplit, observation_last_reader_app in Hlast.
    cbn [observation_last_reader] in Hlast.
    destruct (observation_last_reader EX S ix suffix x) as [last|] eqn:Hsuffix;
      [|reflexivity].
    inversion Hlast; subst last; exfalso; apply Hnot.
    eapply observation_last_reader_member; exact Hsuffix. }
  intro Hneeded; destruct Hneeded as [Hin|[c [Hc [Htarget Hread]]]].
  - apply in_concat in Hin; destruct Hin as [component [Hcomponent Hin]].
    pose proof (observation_last_reader_none EX S ix suffix x Hnone component Hcomponent)
      as Huses.
    unfold observation_component_uses in Huses; apply orb_false_iff in Huses.
    destruct Huses as [Hunused _].
    assert (Hmem : FinSet.mem EX x (FinSet.of_list EX component) = true).
    { apply FinSet.of_list_spec; exact Hin. }
    congruence.
  - apply in_concat in Htarget; destruct Htarget as [component [Hcomponent Htarget]].
    pose proof (observation_last_reader_none EX S ix suffix x Hnone component Hcomponent)
      as Huses.
    unfold observation_component_uses in Huses; apply orb_false_iff in Huses.
    destruct Huses as [_ Hunused].
    assert (Hreader : In c (readers_of EX ix x)).
    { apply (readers_agree Hix); auto. }
    assert (Hused : existsb (fun d => FinSet.mem EX (System.target S d)
      (FinSet.of_list EX component)) (readers_of EX ix x) = true).
    { apply existsb_exists; exists c; split; [exact Hreader|].
      apply FinSet.of_list_spec; exact Htarget. }
    congruence.
Qed.

(** * Observable map operations *)

Lemma observation_record_get {X A} (EX : encoding X) (L : lattice A) (keys : list X)
    (values output : assignment X A) (x : X) :
  Map.get EX x (observation_record EX L keys values output) =
    if existsb (observation_key_eqb EX x) keys
    then Some (lookup EX L values x) else Map.get EX x output.
Proof.
  revert output; induction keys as [|y keys IH]; intro output; [reflexivity|].
  change (Map.get EX x (observation_record EX L keys values
    (Map.set EX y (lookup EX L values y) output)) =
    if existsb (observation_key_eqb EX x) (y :: keys)
    then Some (lookup EX L values x) else Map.get EX x output).
  rewrite IH; cbn [existsb].
  destruct (observation_key_eqb EX x y) eqn:Heq.
  - apply observation_key_eqb_spec in Heq; subst y; rewrite Map.get_set_same.
    destruct (existsb (observation_key_eqb EX x) keys); reflexivity.
  - rewrite Map.get_set_other.
    + destruct (existsb (observation_key_eqb EX x) keys); reflexivity.
    + intro Hequal; subst y; assert (Hsame : observation_key_eqb EX x x = true)
        by (apply observation_key_eqb_spec; reflexivity); congruence.
Qed.

(** Projection contains exactly the distinct selected keys, including explicit bottom entries. *)
Lemma observation_project_get {X A} (EX : encoding X) (L : lattice A) (roots : list X)
    (values : assignment X A) (x : X) :
  Map.get EX x (observation_project EX L roots values) =
    if existsb (observation_key_eqb EX x) roots then Some (lookup EX L values x) else None.
Proof.
  change (Map.get EX x (observation_record EX L roots values Map.empty) =
    if existsb (observation_key_eqb EX x) roots then Some (lookup EX L values x) else None).
  rewrite observation_record_get, Map.get_empty; reflexivity.
Qed.

Lemma observation_record_wf {X A} (EX : encoding X) (L : lattice A) (keys : list X)
    (values output : assignment X A) :
  Map.wf EX output -> Map.wf EX (observation_record EX L keys values output).
Proof.
  revert output; induction keys as [|x keys IH]; intros output Hwf; [exact Hwf|].
  apply IH, Map.wf_set; exact Hwf.
Qed.

Lemma observation_evict_get {X A} (EX : encoding X) (keys : list X)
    (values : assignment X A) (x : X) :
  Map.get EX x (observation_evict EX keys values) =
    if existsb (observation_key_eqb EX x) keys then None else Map.get EX x values.
Proof.
  revert values; induction keys as [|y keys IH]; intro values; [reflexivity|].
  change (Map.get EX x (observation_evict EX keys (Map.remove EX y values)) =
    if existsb (observation_key_eqb EX x) (y :: keys) then None else Map.get EX x values).
  rewrite IH; cbn [existsb].
  destruct (observation_key_eqb EX x y) eqn:Heq.
  - apply observation_key_eqb_spec in Heq; subst y; rewrite Map.get_remove_same.
    destruct (existsb (observation_key_eqb EX x) keys); reflexivity.
  - rewrite Map.get_remove_other.
    + destruct (existsb (observation_key_eqb EX x) keys); reflexivity.
    + intro Hequal; subst y; assert (Hsame : observation_key_eqb EX x x = true)
        by (apply observation_key_eqb_spec; reflexivity); congruence.
Qed.

Lemma observation_evict_keeps {X A} (EX : encoding X) (L : lattice A) (keys : list X)
    (values : assignment X A) (x : X) :
  ~ In x keys -> lookup EX L (observation_evict EX keys values) x = lookup EX L values x.
Proof.
  intro Hnot; unfold lookup; rewrite observation_evict_get.
  destruct (existsb (observation_key_eqb EX x) keys) eqn:Hmem; [|reflexivity].
  apply observation_existsb_key in Hmem; contradiction.
Qed.

(** * Validated prepared schedules *)

Lemma observation_expire_check_sound {X} (EX : encoding X) (left right : Map.t X (list X)) :
  observation_expire_check EX left right = true ->
  forall h x, In x (index_get EX left h) <-> In x (index_get EX right h).
Proof.
  unfold observation_expire_check; rewrite andb_true_iff, !Map.forall2_spec.
  intros [Hleft Hright] h x; unfold index_get, Map.get.
  destruct (Map.code_get (encode EX h) left) as [xs|] eqn:Hget_left;
    destruct (Map.code_get (encode EX h) right) as [ys|] eqn:Hget_right.
  - specialize (Hleft _ _ Hget_left); rewrite Hget_right in Hleft.
    exact (proj1 (observation_seteq_spec EX xs ys) Hleft x).
  - specialize (Hleft _ _ Hget_left); rewrite Hget_right in Hleft.
    exact (proj1 (observation_seteq_spec EX xs []) Hleft x).
  - specialize (Hright _ _ Hget_right); rewrite Hget_left in Hright.
    symmetry; exact (proj1 (observation_seteq_spec EX ys []) Hright x).
  - tauto.
Qed.

Lemma observation_expire_forall2_complete {X} (EX : encoding X) (left right : Map.t X (list X)) :
  Map.wf EX left ->
  (forall h x, In x (index_get EX left h) <-> In x (index_get EX right h)) ->
  Map.forall2 (fun xs other => observation_seteq EX xs
    (match other with
    | Some ys => ys
    | None => []
    end)) left right = true.
Proof.
  intros Hwf Hmembers; apply Map.forall2_spec; intros p xs Hget.
  unfold Map.code_get in Hget; destruct (Trie.get p left) as [[h ys]|] eqn:Hpair;
    cbn in Hget; [|discriminate].
  injection Hget as Hvalue; subst ys.
  pose proof (Hwf p h xs Hpair) as Hcode.
  apply observation_seteq_spec; intro x; specialize (Hmembers h x).
  unfold index_get, Map.get, Map.code_get in Hmembers; rewrite Hcode, Hpair in Hmembers.
  exact Hmembers.
Qed.

(** Lifetime comparison accepts every well-formed index with the same eviction membership. *)
Lemma observation_expire_check_complete {X} (EX : encoding X) (left right : Map.t X (list X)) :
  Map.wf EX left -> Map.wf EX right ->
  (forall h x, In x (index_get EX left h) <-> In x (index_get EX right h)) ->
  observation_expire_check EX left right = true.
Proof.
  intros Hleft Hright Hmembers; unfold observation_expire_check; apply andb_true_iff; split.
  - apply observation_expire_forall2_complete; assumption.
  - apply observation_expire_forall2_complete; [exact Hright|].
    intros h x; symmetry; apply Hmembers.
Qed.

Lemma observation_plan_checked {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (roots : list X) (p : observation_plan X) :
  observation_plan_check EX S SS ix roots p = true ->
  (forall c, In c (System.constraints S) -> side_targets SS c = []) /\
  (forall x, In x roots -> In x (unknowns EX S SS)) /\
  (NoDup (concat (observation_components p)) /\
   (forall x, In x (concat (observation_components p)) <-> In x (unknowns EX S SS)) /\
   (forall component, In component (observation_components p) -> component <> []) /\
   observation_forward_valid S SS (observation_components p)) /\
  forall h x, In x (index_get EX (observation_expire p) h) <->
    In x (index_get EX (observation_expirations EX S SS ix (observation_components p)) h).
Proof.
  unfold observation_plan_check; rewrite !andb_true_iff.
  intros [[[Hsides Hroots] Horder] Hexpiration].
  split; [now apply observation_side_free_spec|].
  split; [now apply observation_roots_check_spec|].
  split.
  - apply observation_components_checked; exact Horder.
  - apply observation_expire_check_sound; exact Hexpiration.
Qed.

Lemma observation_targets_spec {X C A} (EX : encoding X) (S : System.t X C A)
    (members : list X) (x : X) (c : C) :
  In c (index_get EX (observation_restrict_targets EX (nested_targets EX S) members) x) <->
    In c (System.constraints S) /\ System.target S c = x /\ In x members.
Proof.
  rewrite observation_restrict_targets_get.
  destruct (existsb (observation_key_eqb EX x) members) eqn:Hmember.
  - apply observation_existsb_key in Hmember.
    rewrite nested_targets_agree, filter_In, Pos.eqb_eq.
    split.
    + intros [Hc Heq]; apply (encode_injective EX) in Heq; auto.
    + intros [Hc [Heq Hx]]; subst x; auto.
  - cbn; split; [contradiction|].
    intros [_ [_ Hin]].
    pose proof (proj2 (observation_existsb_key EX x members) Hin); congruence.
Qed.

Lemma observation_start_control {X C A} (EX : encoding X) (S : System.t X C A)
    (component : ObservationComponent.t X C) (values : assignment X A) :
  nested_control_valid EX (code component) S (observation_start_local component values).
Proof.
  split.
  - constructor; [split; [apply Nat.le_refl|exact I]|constructor].
  - split; [constructor|]; split; [apply Map.wf_empty|reflexivity].
Qed.

Lemma observation_component_cover {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (T : System.t X D B) (roots : FinSet.t X)
    (expiration : Map.t X (list X)) (members : list X) :
  incl members (unknowns EX S SS) ->
  let component := observation_component EX S SS (nested_targets EX T) roots expiration members in
  forall c, In c (System.constraints (observation_subsystem EX T members)) ->
    exists x, In x (nested_vertices (NestedPlan.root (code component))) /\
      In c (index_get EX (NestedPlan.targets (code component)) x).
Proof.
  intros Hmembers component c Hc; apply filter_In in Hc; destruct Hc as [Hc Htarget].
  apply FinSet.of_list_spec in Htarget; exists (System.target T c); split.
  - apply (proj2 (proj2 (observation_local_covers EX S SS members Hmembers) _)); exact Htarget.
  - apply observation_targets_spec; auto.
Qed.

Lemma observation_component_targets {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (T : System.t X D B) (roots : FinSet.t X)
    (expiration : Map.t X (list X)) (members : list X) :
  let component := observation_component EX S SS (nested_targets EX T) roots expiration members in
  forall x, incl (index_get EX (NestedPlan.targets (code component)) x)
    (System.constraints (observation_subsystem EX T members)).
Proof.
  intros component x c Hc; apply observation_targets_spec in Hc.
  destruct Hc as [Hc [Htarget Hmember]]; apply filter_In; split; [exact Hc|].
  apply FinSet.of_list_spec; now rewrite Htarget.
Qed.

Lemma observation_start_sound {X C D A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (T : System.t X D B) (L : lattice B) (roots : FinSet.t X)
    (expiration : Map.t X (list X)) (members : list X) (values : assignment X B) :
  incl members (unknowns EX S SS) ->
  let component := observation_component EX S SS (nested_targets EX T) roots expiration members in
  nested_sound_state EX L (code component) (observation_subsystem EX T members)
    (observation_start_local component values).
Proof.
  intros Hmembers component; apply nested_root_sound.
  apply observation_component_cover; exact Hmembers.
Qed.

(** * Identical local execution *)

Definition observation_local_control {X C A} (state : NestedState.t X C A) :=
  (NestedState.ready state, NestedState.frames state, NestedState.dirty state,
    NestedState.changed state).

(** Local machines share every control field and the exact values on all pending inputs. *)
Definition observation_local_agrees {X C A} (EX : encoding X) (L : lattice A)
    (needed : X -> Prop) (left right : NestedState.t X C A) : Prop :=
  observation_local_control left = observation_local_control right /\
  forall x, needed x ->
    lookup EX L (NestedState.current left) x = lookup EX L (NestedState.current right) x.

Lemma observation_update_agrees {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (needed : X -> Prop) (x : X) (a : A)
    (left right : NestedState.t X C A) :
  needed x -> observation_local_agrees EX L needed left right ->
  observation_local_agrees EX L needed
    (nested_update EX L plan st (x, a) left) (nested_update EX L plan st (x, a) right).
Proof.
  intros Hx [Hcontrol Hagree].
  destruct left as [left ready frames dirty changed],
    right as [right ready' frames' dirty' changed'];
    cbn [observation_local_control] in Hcontrol; inversion Hcontrol; subst.
  cbn [NestedState.current] in Hagree.
  unfold nested_update; cbn [NestedState.current]; rewrite (Hagree x Hx).
  destruct (leb L a (lookup EX L right x)).
  - split; [reflexivity|exact Hagree].
  - split; [reflexivity|].
    intros y Hy; cbn [nested_mark NestedState.current].
    destruct (observation_key_eqb EX y x) eqn:Heq.
    + apply observation_key_eqb_spec in Heq; subst y; now rewrite !lookup_set_same.
    + assert (Hdifferent : y <> x).
      { intro Hequal; subst y; unfold observation_key_eqb in Heq.
        rewrite Pos.eqb_refl in Heq; discriminate. }
      rewrite !lookup_set_other by exact Hdifferent; apply Hagree; exact Hy.
Qed.

Lemma observation_updates_agree {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (needed : X -> Prop) (updates : list (X * A)) :
  (forall x a, In (x, a) updates -> needed x) ->
  forall left right, observation_local_agrees EX L needed left right ->
  observation_local_agrees EX L needed
    (nested_updates EX L plan st updates left) (nested_updates EX L plan st updates right).
Proof.
  intros Hupdates; induction updates as [|[x a] updates IH]; intros left right Hagree;
    [exact Hagree|].
  apply IH.
  - intros y b Hin; apply (Hupdates y b); now right.
  - apply observation_update_agrees; [apply (Hupdates x a); now left|exact Hagree].
Qed.

(** The event exposes the constraint and its complete query trace, before any update. *)
Definition observation_local_event {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (state : NestedState.t X C A) :
    option (C * (A * list X * list (X * A))) :=
  match NestedState.ready state with
  | [] => None
  | c :: _ => Some (c, Query.run (System.rhs S c) (lookup EX L (NestedState.current state)))
  end.

Lemma observation_query_agrees {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (needed : X -> Prop)
    (left right : NestedState.t X C A) (c : C) :
  observation_local_agrees EX L needed left right ->
  (forall x, In x (deps SS c) -> needed x) ->
  Query.run (System.rhs S c) (lookup EX L (NestedState.current left)) =
    Query.run (System.rhs S c) (lookup EX L (NestedState.current right)).
Proof.
  intros [_ Hagree] Hneeded; rewrite !run_spec.
  destruct (query_determined (System.rhs S c)
    (lookup EX L (NestedState.current left)) (lookup EX L (NestedState.current right)))
    as [Hvalue [Hreads Hsides]].
  - intros x Hread; apply Hagree, Hneeded; exact (System.reads_within SS c _ x Hread).
  - now rewrite Hvalue, Hreads, Hsides.
Qed.

(** Agreement fixes the complete local trace, and hence the inputs to every widening. *)
Lemma observation_local_event_agrees {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (needed : X -> Prop)
    (left right : NestedState.t X C A) :
  observation_local_agrees EX L needed left right ->
  (forall c, In c (NestedState.ready left) -> forall x, In x (deps SS c) -> needed x) ->
  observation_local_event EX L S left = observation_local_event EX L S right.
Proof.
  intros Hagree Hneeded; pose proof (proj1 Hagree) as Hcontrol.
  assert (Hready : NestedState.ready left = NestedState.ready right).
  { unfold observation_local_control in Hcontrol; now inversion Hcontrol. }
  unfold observation_local_event; rewrite <- Hready.
  destruct (NestedState.ready left) as [|c rest] eqn:Hcs; [reflexivity|].
  rewrite (observation_query_agrees EX L S SS needed left right c Hagree).
  - reflexivity.
  - apply Hneeded; now left.
Qed.

(** Each paid transition preserves agreement and has identical completion or exhaustion control. *)
Lemma observation_local_step_agrees {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (S : System.t X C A) (SS : System.static S)
    (needed : X -> Prop) (left right : NestedState.t X C A) :
  observation_local_agrees EX L needed left right ->
  (forall c, In c (NestedState.ready left) ->
    (forall x, In x (deps SS c) -> needed x) /\ needed (System.target S c) /\
      (forall x, In x (side_targets SS c) -> needed x)) ->
  match nested_step EX L plan st S left, nested_step EX L plan st S right with
  | Some next_left, Some next_right => observation_local_agrees EX L needed next_left next_right
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros Hagreement Hneeded; destruct Hagreement as [Hcontrol Hagree].
  destruct left as [left ready frames dirty changed],
    right as [right ready' frames' dirty' changed'];
    cbn [observation_local_control] in Hcontrol; inversion Hcontrol; subst.
  destruct ready' as [|c rest].
  - unfold nested_step; cbn [NestedState.ready NestedState.current NestedState.dirty
      NestedState.changed NestedState.frames].
    destruct frames' as [|[body restart] frames]; [exact I|].
    cbn [NestedFrame.remaining NestedFrame.restart]; destruct body.
    + destruct restart as [[h pass]|].
      * destruct (FinSet.mem EX h dirty'); (split; [reflexivity|exact Hagree]).
      * destruct changed'; [split; [reflexivity|exact Hagree]|exact I].
    + split; [reflexivity|exact Hagree].
    + split; [reflexivity|exact Hagree].
  - destruct (Hneeded c (or_introl eq_refl)) as [Hreads [Htarget Hsides]].
    assert (Hquery : Query.run (System.rhs S c) (lookup EX L left) =
      Query.run (System.rhs S c) (lookup EX L right)).
    { apply (observation_query_agrees EX L S SS needed
        (NestedState.Make left (c :: rest) frames' dirty' changed')
        (NestedState.Make right (c :: rest) frames' dirty' changed') c).
      - split; [reflexivity|exact Hagree].
      - exact Hreads. }
    unfold nested_step; cbn [NestedState.ready NestedState.current NestedState.dirty
      NestedState.changed NestedState.frames]; rewrite Hquery, run_spec.
    apply observation_updates_agree.
    + intros x a [Hpair|Hin]; [inversion Hpair; subst x; exact Htarget|].
      apply Hsides, (System.sides_within SS c (lookup EX L right)).
      apply in_map_iff; exists (x, a); auto.
    + split; [reflexivity|exact Hagree].
Qed.

(** * Schedule invariants *)

Definition observation_keys {X C} (schedule : list (ObservationComponent.t X C)) : list X :=
  concat (map ObservationComponent.members schedule).

Lemma observation_keys_app {X C} (first last : list (ObservationComponent.t X C)) :
  observation_keys (first ++ last) = observation_keys first ++ observation_keys last.
Proof.
  unfold observation_keys; now rewrite map_app, concat_app.
Qed.

(** Component validity connects its prepared target buckets to its local constraint system. *)
Record observation_component_valid {X C A} (EX : encoding X) (S : System.t X C A)
    (roots : list X) (component : ObservationComponent.t X C) : Prop := {
  observation_targets_within : forall x,
    incl (index_get EX (NestedPlan.targets (code component)) x)
      (System.constraints (observation_subsystem EX S (ObservationComponent.members component)));
  observation_targets_cover : forall c,
    In c (System.constraints
      (observation_subsystem EX S (ObservationComponent.members component))) ->
    exists x, In x (nested_vertices (NestedPlan.root (code component))) /\
      In c (index_get EX (NestedPlan.targets (code component)) x);
  observation_outputs_exact : outputs component =
    filter (fun x => FinSet.mem EX x (FinSet.of_list EX roots))
      (ObservationComponent.members component)
}.

Arguments observation_targets_within {X C A EX S roots component}.
Arguments observation_targets_cover {X C A EX S roots component}.
Arguments observation_outputs_exact {X C A EX S roots component}.

(** Validation fixes coverage, topological flow and the exact boundary lifetime obligations. *)
Record observation_schedule_valid {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (roots : list X)
    (schedule : list (ObservationComponent.t X C)) : Prop := {
  observation_schedule_nodup : NoDup (observation_keys schedule);
  observation_schedule_targets : forall c, In c (System.constraints S) ->
    In (System.target S c) (observation_keys schedule);
  observation_schedule_roots : forall x, In x roots -> In x (observation_keys schedule);
  observation_schedule_side_free : forall c, In c (System.constraints S) -> side_targets SS c = [];
  observation_schedule_components : forall component, In component schedule ->
    observation_component_valid EX S roots component;
  observation_schedule_forward : forall first last, schedule = first ++ last ->
    forall c, In c (System.constraints S) -> In (System.target S c) (observation_keys first) ->
    forall x, In x (deps SS c) -> ~ In x (observation_keys last);
  observation_schedule_expiration : forall first component last,
    schedule = first ++ component :: last -> forall x, In x (expire component) ->
      ~ observation_needed S SS (map ObservationComponent.members last) x
}.

Arguments observation_schedule_nodup {X C A EX S SS roots schedule}.
Arguments observation_schedule_targets {X C A EX S SS roots schedule}.
Arguments observation_schedule_roots {X C A EX S SS roots schedule}.
Arguments observation_schedule_side_free {X C A EX S SS roots schedule}.
Arguments observation_schedule_components {X C A EX S SS roots schedule}.
Arguments observation_schedule_forward {X C A EX S SS roots schedule}.
Arguments observation_schedule_expiration {X C A EX S SS roots schedule}.

Lemma observation_update_frame {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (x y : X) (a : A)
    (state : NestedState.t X C A) :
  y <> x -> lookup EX L (NestedState.current (nested_update EX L plan st (x, a) state)) y =
    lookup EX L (NestedState.current state) y.
Proof.
  intro Hdifferent; unfold nested_update; destruct (leb L a _); [reflexivity|].
  cbn [nested_mark NestedState.current]; apply lookup_set_other; exact Hdifferent.
Qed.

(** A side-free local transition changes only members of its current component. *)
Lemma observation_local_step_frame {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (S : System.t X C A) (SS : System.static S)
    (members : list X) (state next : NestedState.t X C A) :
  (forall c, In c (NestedState.ready state) ->
    In (System.target S c) members /\ side_targets SS c = []) ->
  nested_step EX L plan st S state = Some next -> forall x, ~ In x members ->
    lookup EX L (NestedState.current next) x = lookup EX L (NestedState.current state) x.
Proof.
  intros Hready Hstep x Hnot; unfold nested_step in Hstep.
  destruct (NestedState.ready state) as [|c rest] eqn:Hcs.
  - destruct (NestedState.frames state) as [|[body restart] frames]; [discriminate|].
    cbn [NestedFrame.remaining NestedFrame.restart] in Hstep; destruct body;
      try (inversion Hstep; reflexivity).
    destruct restart as [[h pass]|].
    + destruct (FinSet.mem EX h (NestedState.dirty state)); inversion Hstep; reflexivity.
    + destruct (NestedState.changed state); [inversion Hstep; reflexivity|discriminate].
  - destruct (Hready c (or_introl eq_refl)) as [Htarget Hsides].
    rewrite run_spec, (observation_sides_empty S SS c _ Hsides) in Hstep.
    inversion Hstep; subst next; cbn [nested_updates fold_left].
    apply (observation_update_frame EX L plan st (System.target S c) x
      (Query.eval (System.rhs S c) (lookup EX L (NestedState.current state)))
      (NestedState.Make (NestedState.current state) rest (NestedState.frames state)
        (NestedState.dirty state) (NestedState.changed state))).
    intro Heq; subst x; contradiction.
Qed.

Lemma observation_constraint_frame {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (c : C) (before after : assignment X A) :
  (forall x, In x (deps SS c) -> lookup EX L before x = lookup EX L after x) ->
  lookup EX L before (System.target S c) = lookup EX L after (System.target S c) ->
  (forall x, In x (side_targets SS c) -> lookup EX L before x = lookup EX L after x) ->
  constraint_satisfied L S c (lookup EX L before) ->
  constraint_satisfied L S c (lookup EX L after).
Proof.
  intros Hreads Htarget Hside_targets Hsatisfied.
  destruct (query_determined (System.rhs S c) (lookup EX L before) (lookup EX L after))
    as [Hvalue [_ Hsides]].
  - intros x Hread; apply Hreads; exact (System.reads_within SS c _ x Hread).
  - destruct Hsatisfied as [Hvalue_below Hsides_below]; split.
    + now rewrite <- Hvalue, <- Htarget.
    + intros x a Hin; rewrite <- Hsides in Hin.
      rewrite <- Hside_targets.
      * exact (Hsides_below x a Hin).
      * apply (System.sides_within SS c (lookup EX L before)).
        apply in_map_iff; exists (x, a); auto.
Qed.

Lemma observation_record_agrees {X A} (EX : encoding X) (L : lattice A) (keys : list X)
    (left right output : assignment X A) :
  (forall x, In x keys -> lookup EX L left x = lookup EX L right x) ->
  observation_record EX L keys left output = observation_record EX L keys right output.
Proof.
  intro Hagree; revert output; induction keys as [|x keys IH]; intro output; [reflexivity|].
  change (observation_record EX L keys left (Map.set EX x (lookup EX L left x) output) =
    observation_record EX L keys right (Map.set EX x (lookup EX L right x) output)).
  rewrite (Hagree x (or_introl eq_refl)); apply IH.
  intros y Hy; apply Hagree; now right.
Qed.

Lemma observation_ready_domains {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (component : ObservationComponent.t X C)
    (rest : list (ObservationComponent.t X C)) (state : NestedState.t X C A) :
  (forall c, In c (System.constraints S) -> side_targets SS c = []) ->
  nested_control_valid EX (code component)
    (observation_subsystem EX S (ObservationComponent.members component)) state ->
  forall c, In c (NestedState.ready state) ->
    (forall x, In x (deps SS c) ->
      observation_needed S SS (map ObservationComponent.members (component :: rest)) x) /\
    observation_needed S SS (map ObservationComponent.members (component :: rest))
      (System.target S c) /\
    (forall x, In x (side_targets SS c) ->
      observation_needed S SS (map ObservationComponent.members (component :: rest)) x).
Proof.
  intros Hsides [_ [Hready _]] c Hc; rewrite Forall_forall in Hready.
  specialize (Hready c Hc); apply filter_In in Hready; destruct Hready as [Hc_system Htarget].
  apply FinSet.of_list_spec in Htarget.
  assert (Hpending : In (System.target S c)
    (concat (map ObservationComponent.members (component :: rest)))).
  { cbn [map concat]; apply in_or_app; now left. }
  split.
  - intros x Hread; right; exists c; auto.
  - split; [now left|intros x Hside; rewrite Hsides in Hside by exact Hc_system; contradiction].
Qed.

(** Boundary agreement retains exactly the working values needed by unfinished components. *)
Definition observation_execution_agrees {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S)
    (schedule : list (ObservationComponent.t X C))
    (left right : ObservationState.t X C A + (assignment X A * assignment X A)) : Prop :=
  match left, right with
  | inl full, inl live =>
    active full = active live /\ pending full = pending live /\ observed full = observed live /\
    exists prefix, schedule = prefix ++ active full :: pending full /\
      nested_control_valid EX (code (active full))
        (observation_subsystem EX S (ObservationComponent.members (active full))) (local full) /\
      observation_local_agrees EX L
        (observation_needed S SS
          (map ObservationComponent.members (active full :: pending full)))
        (local full) (local live)
  | inr (_, full_output), inr (_, live_output) => full_output = live_output
  | _, _ => False
  end.

Lemma observation_tick_agrees {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (roots : list X)
    (schedule : list (ObservationComponent.t X C)) :
  observation_schedule_valid EX S SS roots schedule ->
  forall full live, observation_execution_agrees EX L S SS schedule full live ->
    observation_execution_agrees EX L S SS schedule
      (observation_tick EX L st S false full) (observation_tick EX L st S true live).
Proof.
  intros Hvalid [full|[full_values full_output]] [live|[live_values live_output]] Hagree;
    try contradiction; [|exact Hagree].
  destruct full as [component rest full output], live as [component' rest' live output'];
    cbn [observation_execution_agrees active pending observed local] in Hagree.
  destruct Hagree as [Hcomponent [Hrest [Houtput [prefix [Hschedule [Hcontrol Hagree]]]]]];
    subst component' rest' output'.
  assert (Hcomponent_in : In component schedule).
  { rewrite Hschedule; apply in_or_app; right; now left. }
  pose proof (observation_schedule_components Hvalid component Hcomponent_in) as Hcomponent_valid.
  pose proof (observation_local_step_agrees EX L (code component) st S SS
    (observation_needed S SS (map ObservationComponent.members (component :: rest)))
    full live Hagree (observation_ready_domains EX L S SS component rest full
      (observation_schedule_side_free Hvalid) Hcontrol)) as Hsteps.
  unfold observation_tick; cbn [active pending observed local].
  destruct (nested_step EX L (code component) st S full) as [next_full|] eqn:Hfull;
    destruct (nested_step EX L (code component) st S live) as [next_live|] eqn:Hlive;
    try contradiction.
  - cbn [observation_execution_agrees active pending observed local]; split; [reflexivity|].
    split; [reflexivity|]; split; [reflexivity|]; exists prefix; split; [exact Hschedule|].
    split; [|exact Hsteps].
    eapply nested_step_control; [apply (observation_targets_within Hcomponent_valid)|
      exact Hcontrol|exact Hfull].
  - assert (Houtput : observation_record EX L (outputs component)
      (NestedState.current full) output = observation_record EX L (outputs component)
        (NestedState.current live) output).
    { apply observation_record_agrees; intros x Hx; apply (proj2 Hagree); left.
      cbn [map concat]; apply in_or_app; left.
      rewrite (observation_outputs_exact Hcomponent_valid) in Hx.
      apply filter_In in Hx; exact (proj1 Hx). }
    destruct rest as [|next rest].
    + exact Houtput.
    + cbn [observation_execution_agrees active pending observed local].
      split; [reflexivity|]; split; [reflexivity|]; split; [exact Houtput|].
      exists (prefix ++ [component]); split.
      * rewrite Hschedule, <- app_assoc; reflexivity.
      * split; [apply observation_start_control|]; split; [reflexivity|].
        intros x Hneeded; cbn [observation_start_local NestedState.current].
        rewrite observation_evict_keeps.
        -- apply (proj2 Hagree).
           change (observation_needed S SS ([ObservationComponent.members component] ++
             map ObservationComponent.members (next :: rest)) x).
           apply observation_needed_suffix; exact Hneeded.
        -- intro Hexpire; exact (observation_schedule_expiration Hvalid prefix component
             (next :: rest) Hschedule x Hexpire Hneeded).
Qed.

Lemma observation_repeat_related {B D} (left_tick : B -> B) (right_tick : D -> D)
    (R : B -> D -> Prop) :
  (forall left right, R left right -> R (left_tick left) (right_tick right)) ->
  forall fuel left right, R left right ->
    R (observation_repeat left_tick fuel left) (observation_repeat right_tick fuel right).
Proof.
  intros Htick fuel; induction fuel as [fuel IH|fuel IH|]; intros left right Hagree;
    cbn [observation_repeat].
  - apply Htick, IH, IH; exact Hagree.
  - apply IH, IH; exact Hagree.
  - apply Htick; exact Hagree.
Qed.

(** * Full-memory semantic invariant *)

Definition observation_completed {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (roots : list X) (done_ : list (ObservationComponent.t X C))
    (values output : assignment X A) : Prop :=
  (forall c, In c (System.constraints S) -> In (System.target S c) (observation_keys done_) ->
    constraint_satisfied L S c (lookup EX L values)) /\ Map.wf EX output /\
  forall x, Map.get EX x output =
    if existsb (observation_key_eqb EX x) roots &&
      existsb (observation_key_eqb EX x) (observation_keys done_)
    then Some (lookup EX L values x) else None.

Lemma observation_schedule_disjoint {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (roots : list X)
    (schedule first last : list (ObservationComponent.t X C)) :
  observation_schedule_valid EX S SS roots schedule -> schedule = first ++ last ->
  forall x, In x (observation_keys first) -> ~ In x (observation_keys last).
Proof.
  intros Hvalid Hsplit.
  pose proof (observation_schedule_nodup Hvalid) as Hdistinct.
  rewrite Hsplit, observation_keys_app in Hdistinct.
  apply tarjan_nodup_disjoint; exact Hdistinct.
Qed.

Lemma observation_completed_empty {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (roots : list X) (values : assignment X A) :
  observation_completed EX L S roots [] values Map.empty.
Proof.
  split; [intros c Hc Hin; contradiction|]; split; [apply Map.wf_empty|].
  intro x; rewrite Map.get_empty; cbn [observation_keys map concat existsb].
  now rewrite andb_false_r.
Qed.

Lemma observation_completed_frame {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (roots : list X)
    (schedule prefix : list (ObservationComponent.t X C)) (component : ObservationComponent.t X C)
    (rest : list (ObservationComponent.t X C)) (before after output : assignment X A) :
  observation_schedule_valid EX S SS roots schedule -> schedule = prefix ++ component :: rest ->
  observation_completed EX L S roots prefix before output ->
  (forall x, ~ In x (ObservationComponent.members component) ->
    lookup EX L after x = lookup EX L before x) ->
  observation_completed EX L S roots prefix after output.
Proof.
  intros Hvalid Hsplit [Hsatisfied [Hwf Houtput]] Hframe.
  assert (Hdisjoint : forall x, In x (observation_keys prefix) ->
    ~ In x (ObservationComponent.members component)).
  { intros x Hx Hin; apply (observation_schedule_disjoint EX S SS roots schedule prefix
      (component :: rest) Hvalid Hsplit x Hx).
    cbn [observation_keys map concat]; apply in_or_app; now left. }
  split.
  - intros c Hc Htarget; eapply observation_constraint_frame.
    + intros x Hread; symmetry; apply Hframe; intro Hin.
      apply (observation_schedule_forward Hvalid prefix (component :: rest) Hsplit
        c Hc Htarget x Hread).
      cbn [observation_keys map concat]; apply in_or_app; now left.
    + symmetry; apply Hframe, Hdisjoint; exact Htarget.
    + intros x Hside; rewrite (observation_schedule_side_free Hvalid c Hc) in Hside;
        contradiction.
    + apply Hsatisfied; assumption.
  - split; [exact Hwf|]; intro x; rewrite Houtput.
    destruct (existsb (observation_key_eqb EX x) roots),
      (existsb (observation_key_eqb EX x) (observation_keys prefix)) eqn:Hmember;
      cbn [andb]; try reflexivity.
    rewrite Hframe; [reflexivity|apply Hdisjoint].
    now apply observation_existsb_key in Hmember.
Qed.

Lemma observation_outputs_mem {X C A} (EX : encoding X) (S : System.t X C A)
    (roots : list X) (component : ObservationComponent.t X C) (x : X) :
  observation_component_valid EX S roots component ->
  existsb (observation_key_eqb EX x) (outputs component) =
    existsb (observation_key_eqb EX x) roots &&
      existsb (observation_key_eqb EX x) (ObservationComponent.members component).
Proof.
  intro Hvalid; apply eq_true_iff_eq; rewrite andb_true_iff, !observation_existsb_key.
  rewrite (observation_outputs_exact Hvalid), filter_In, FinSet.of_list_spec; tauto.
Qed.

Lemma observation_completed_extend {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (roots : list X) (prefix : list (ObservationComponent.t X C))
    (component : ObservationComponent.t X C) (values output : assignment X A) :
  observation_component_valid EX S roots component ->
  observation_completed EX L S roots prefix values output ->
  post_solution L (observation_subsystem EX S (ObservationComponent.members component))
    (lookup EX L values) ->
  observation_completed EX L S roots (prefix ++ [component]) values
    (observation_record EX L (outputs component) values output).
Proof.
  intros Hcomponent [Hsatisfied [Hwf Houtput]] Hlocal.
  assert (Hkeys : observation_keys (prefix ++ [component]) =
    observation_keys prefix ++ ObservationComponent.members component).
  { rewrite observation_keys_app; cbn [observation_keys map concat]; now rewrite app_nil_r. }
  split.
  - intros c Hc Htarget; rewrite Hkeys in Htarget; apply in_app_iff in Htarget.
    destruct Htarget as [Hold|Hcurrent]; [apply Hsatisfied; assumption|].
    apply (Hlocal c); apply filter_In; split; [exact Hc|].
    apply FinSet.of_list_spec; exact Hcurrent.
  - split; [apply observation_record_wf; exact Hwf|].
    intro x; rewrite observation_record_get,
      (observation_outputs_mem EX S roots component x Hcomponent).
    rewrite Houtput, Hkeys, existsb_app.
    destruct (existsb (observation_key_eqb EX x) roots),
      (existsb (observation_key_eqb EX x) (observation_keys prefix)),
      (existsb (observation_key_eqb EX x) (ObservationComponent.members component)); reflexivity.
Qed.

(** Completed components accumulate precisely the projection of their full post-solution. *)
Lemma observation_completed_all {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (roots : list X)
    (schedule : list (ObservationComponent.t X C)) (values output : assignment X A) :
  observation_schedule_valid EX S SS roots schedule ->
  observation_completed EX L S roots schedule values output ->
  post_solution L S (lookup EX L values) /\ output = observation_project EX L roots values.
Proof.
  intros Hvalid [Hsatisfied [Hwf Houtput]]; split.
  - intros c Hc; apply Hsatisfied; [exact Hc|apply (observation_schedule_targets Hvalid c Hc)].
  - apply (Map.extensionality EX); [exact Hwf|apply observation_record_wf, Map.wf_empty|].
    intro x; rewrite Houtput, observation_project_get.
    destruct (existsb (observation_key_eqb EX x) roots) eqn:Hroot; [|reflexivity].
    apply observation_existsb_key in Hroot.
    assert (Hkey : existsb (observation_key_eqb EX x) (observation_keys schedule) = true).
    { apply observation_existsb_key, (observation_schedule_roots Hvalid); exact Hroot. }
    now rewrite Hkey.
Qed.

Definition observation_reference_invariant {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (roots : list X) (schedule : list (ObservationComponent.t X C))
    (result : ObservationState.t X C A + (assignment X A * assignment X A)) : Prop :=
  match result with
  | inl state => exists prefix, schedule = prefix ++ active state :: pending state /\
    nested_control_valid EX (code (active state))
      (observation_subsystem EX S (ObservationComponent.members (active state))) (local state) /\
    nested_sound_state EX L (code (active state))
      (observation_subsystem EX S (ObservationComponent.members (active state))) (local state) /\
    observation_completed EX L S roots prefix (NestedState.current (local state)) (observed state)
  | inr (values, output) => post_solution L S (lookup EX L values) /\
    output = observation_project EX L roots values
  end.

Lemma observation_reference_tick {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (roots : list X)
    (schedule : list (ObservationComponent.t X C)) :
  observation_schedule_valid EX S SS roots schedule -> forall result,
  observation_reference_invariant EX L S roots schedule result ->
  observation_reference_invariant EX L S roots schedule (observation_tick EX L st S false result).
Proof.
  intros Hvalid [state|[values output]] Hstate; [|exact Hstate].
  destruct state as [component rest state output].
  cbn [observation_reference_invariant active pending local observed] in Hstate.
  destruct Hstate as [prefix [Hschedule [Hcontrol [Hsound Hcompleted]]]].
  assert (Hcomponent_in : In component schedule).
  { rewrite Hschedule; apply in_or_app; right; now left. }
  pose proof (observation_schedule_components Hvalid component Hcomponent_in) as Hcomponent.
  unfold observation_tick; cbn [active pending local observed].
  destruct (nested_step EX L (code component) st S state) as [next|] eqn:Hstep.
  - cbn [observation_reference_invariant active pending local observed].
    exists prefix; split; [exact Hschedule|]; split.
    + eapply nested_step_control; [apply (observation_targets_within Hcomponent)|
        exact Hcontrol|exact Hstep].
    + split.
      * eapply nested_step_sound; [apply (observation_targets_cover Hcomponent)|
          exact Hsound|exact Hstep].
      * eapply observation_completed_frame; [exact Hvalid|exact Hschedule|exact Hcompleted|].
        apply (observation_local_step_frame EX L (code component) st S SS
          (ObservationComponent.members component) state next); [|exact Hstep].
        intros c Hc; destruct Hcontrol as [_ [Hready _]]; rewrite Forall_forall in Hready.
        specialize (Hready c Hc); apply filter_In in Hready; destruct Hready as [Hc_system Htarget].
        split; [now apply FinSet.of_list_spec in Htarget|].
        apply (observation_schedule_side_free Hvalid); exact Hc_system.
  - assert (Hlocal : post_solution L
      (observation_subsystem EX S (ObservationComponent.members component))
      (lookup EX L (NestedState.current state))).
    { eapply nested_finished_sound; [exact (proj2 (proj2 (proj2 Hcontrol)))|
        exact Hsound|exact Hstep]. }
    pose proof (observation_completed_extend EX L S roots prefix component
      (NestedState.current state) output Hcomponent Hcompleted Hlocal) as Hextended.
    destruct rest as [|next rest].
    + cbn [observation_reference_invariant].
      apply (observation_completed_all EX L S SS roots schedule); [exact Hvalid|].
      now rewrite Hschedule.
    + cbn [observation_reference_invariant active pending local observed].
      exists (prefix ++ [component]); split.
      * rewrite Hschedule, <- app_assoc; reflexivity.
      * split; [apply observation_start_control|]; split; [|exact Hextended].
        apply nested_root_sound.
        assert (Hnext : In next schedule).
        { rewrite Hschedule; apply in_or_app; right; right; now left. }
        apply (observation_targets_cover (observation_schedule_components Hvalid next Hnext)).
Qed.

Lemma observation_repeat_invariant {B} (tick : B -> B) (I : B -> Prop) :
  (forall state, I state -> I (tick state)) ->
  forall fuel state, I state -> I (observation_repeat tick fuel state).
Proof.
  intros Htick fuel; induction fuel as [fuel IH|fuel IH|]; intros state Hstate;
    cbn [observation_repeat].
  - apply Htick, IH, IH; exact Hstate.
  - apply IH, IH; exact Hstate.
  - apply Htick; exact Hstate.
Qed.

(** The full fixed schedule establishes all constraints and the exact retained projection. *)
Lemma observation_execute_spec {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (roots : list X)
    (schedule : list (ObservationComponent.t X C)) (fuel : positive)
    (values output : assignment X A) :
  observation_schedule_valid EX S SS roots schedule ->
  observation_execute EX L st S schedule false fuel = Some (values, output) ->
  post_solution L S (lookup EX L values) /\ output = observation_project EX L roots values.
Proof.
  intros Hvalid; destruct schedule as [|first rest].
  - cbn [observation_execute]; intro Hresult; inversion Hresult; subst values output.
    apply (observation_completed_all EX L S SS roots []); [exact Hvalid|].
    apply observation_completed_empty.
  - set (initial := @ObservationState.Make X C A first rest
      (observation_start_local first Map.empty) Map.empty).
    assert (Hinitial : observation_reference_invariant EX L S roots (first :: rest) (inl initial)).
    { exists []; split; [reflexivity|]; split; [apply observation_start_control|]; split.
      - apply nested_root_sound.
        apply (observation_targets_cover (observation_schedule_components Hvalid first
          (or_introl eq_refl))).
      - apply observation_completed_empty. }
    pose proof (observation_repeat_invariant (observation_tick EX L st S false)
      (observation_reference_invariant EX L S roots (first :: rest))
      (observation_reference_tick EX L st S SS roots (first :: rest) Hvalid)
      fuel (inl initial) Hinitial) as Hfinal.
    unfold observation_execute; fold initial.
    destruct (observation_repeat (observation_tick EX L st S false) fuel (inl initial))
      as [unfinished|[finished_values finished_output]];
      intro Hresult; [discriminate|inversion Hresult; subst; exact Hfinal].
Qed.

(** Eviction preserves completion and exhaustion at the identical binary fuel budget. *)
Lemma observation_execute_agrees {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (roots : list X)
    (schedule : list (ObservationComponent.t X C)) (fuel : positive) :
  observation_schedule_valid EX S SS roots schedule ->
  option_map snd (observation_execute EX L st S schedule true fuel) =
    option_map snd (observation_execute EX L st S schedule false fuel).
Proof.
  intro Hvalid; destruct schedule as [|first rest]; [reflexivity|].
  set (initial := @ObservationState.Make X C A first rest
    (observation_start_local first Map.empty) Map.empty).
  assert (Hinitial : observation_execution_agrees EX L S SS (first :: rest)
    (inl initial) (inl initial)).
  { split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    exists []; split; [reflexivity|]; split; [apply observation_start_control|].
    split; [reflexivity|intros x Hx; reflexivity]. }
  pose proof (observation_repeat_related (observation_tick EX L st S false)
    (observation_tick EX L st S true) (observation_execution_agrees EX L S SS (first :: rest))
    (observation_tick_agrees EX L st S SS roots (first :: rest) Hvalid)
    fuel (inl initial) (inl initial) Hinitial) as Hfinal.
  unfold observation_execute; fold initial.
  destruct (observation_repeat (observation_tick EX L st S false) fuel (inl initial))
    as [full|[full_values full_output]];
    destruct (observation_repeat (observation_tick EX L st S true) fuel (inl initial))
    as [live|[live_values live_output]]; cbn [option_map snd];
    try contradiction; [reflexivity|].
  cbn [observation_execution_agrees] in Hfinal; now rewrite Hfinal.
Qed.

(** * Prepared schedules satisfy the machine invariants *)

Lemma observation_order_forward {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (order prefix suffix : list (list X)) (c : C) (x : X) :
  observation_forward_valid S SS order -> order = prefix ++ suffix -> In c (System.constraints S) ->
  In (System.target S c) (concat prefix) -> In x (deps SS c) -> ~ In x (concat suffix).
Proof.
  intros Hforward Horder Hc Htarget Hread Hin.
  apply in_concat in Htarget; destruct Htarget as [component [Hcomponent Htarget]].
  apply in_split in Hcomponent; destruct Hcomponent as [before [after Hprefix]].
  assert (Hcombined : order = before ++ component :: (after ++ suffix)).
  { rewrite Horder, Hprefix, <- app_assoc; reflexivity. }
  apply (Hforward before component (after ++ suffix) Hcombined c Hc Htarget x Hread).
  rewrite concat_app; apply in_or_app; now right.
Qed.

Lemma observation_compile_members {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (fallback : C) (roots : list X) (p : observation_plan X) :
  map ObservationComponent.members (observation_compile EX S SS fallback roots p) =
    observation_components p.
Proof.
  unfold observation_compile, observation_compile_targets; rewrite map_map.
  change (map (fun xs : list X => xs) (observation_components p) = observation_components p).
  apply map_id.
Qed.

Lemma observation_needed_system {X C A} (S : System.t X C A) (SS : System.static S)
    (fallback : C) (order : list (list X)) (x : X) :
  observation_needed (observation_system S fallback) (observation_static S SS fallback) order x ->
  observation_needed S SS order x.
Proof.
  intros [Hin|[i [Hi [Htarget Hread]]]]; [now left|].
  right; exists (observation_label fallback (observation_number 0 (System.constraints S)) i).
  split; [apply observation_label_in; exact Hi|]; split; assumption.
Qed.

(** Semantic validation establishes every schedule obligation consumed by either execution. *)
Lemma observation_compile_valid {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (fallback : C) (roots : list X)
    (p : observation_plan X) :
  sys_index_laws EX S SS ix -> observation_plan_check EX S SS ix roots p = true ->
  observation_schedule_valid EX (observation_system S fallback) (observation_static S SS fallback)
    roots (observation_compile EX S SS fallback roots p).
Proof.
  intros Hix Hcheck.
  destruct (observation_plan_checked EX S SS ix roots p Hcheck)
    as [Hsides [Hroots [[Hdistinct [Hcover [Hnonempty Hforward]]] Hexpiration]]].
  set (schedule := observation_compile EX S SS fallback roots p).
  assert (Hmembers : map ObservationComponent.members schedule = observation_components p).
  { unfold schedule; apply observation_compile_members. }
  assert (Hkeys : observation_keys schedule = concat (observation_components p)).
  { unfold observation_keys; now rewrite Hmembers. }
  constructor.
  - now rewrite Hkeys.
  - intros i Hi; rewrite Hkeys; apply Hcover.
    apply (proj2 (proj2 (unknowns_spec EX S SS) _)).
    exists (observation_label fallback (observation_number 0 (System.constraints S)) i).
    split; [apply observation_label_in; exact Hi|now left].
  - intros x Hx; rewrite Hkeys; apply Hcover, Hroots; exact Hx.
  - intros i Hi; apply Hsides, (observation_label_in S fallback i); exact Hi.
  - intros component Hcomponent; unfold schedule, observation_compile in Hcomponent.
    apply in_map_iff in Hcomponent; destruct Hcomponent as [xs [Heq Hxs]]; subst component.
    assert (Hsubset : incl xs (unknowns EX S SS)).
    { intros x Hx; apply Hcover, in_concat; exists xs; split; [exact Hxs|exact Hx]. }
    constructor.
    + apply observation_component_targets.
    + apply observation_component_cover; exact Hsubset.
    + reflexivity.
  - intros first last Hsplit i Hi Htarget x Hread Hin.
    apply (observation_order_forward EX S SS (observation_components p)
      (map ObservationComponent.members first)
      (map ObservationComponent.members last)
      (observation_label fallback (observation_number 0 (System.constraints S)) i) x).
    + exact Hforward.
    + rewrite <- Hmembers, Hsplit, map_app; reflexivity.
    + apply observation_label_in; exact Hi.
    + exact Htarget.
    + exact Hread.
    + exact Hin.
  - intros first component last Hsplit x Hexpire Hneeded.
    assert (Hcomponent : In component schedule).
    { rewrite Hsplit; apply in_or_app; right; now left. }
    unfold schedule, observation_compile in Hcomponent; apply in_map_iff in Hcomponent.
    destruct Hcomponent as [xs [Heq Hxs]]; subst component.
    destruct xs as [|h body].
    + exact (Hnonempty [] Hxs eq_refl).
    + cbn [observation_component_on ObservationComponent.expire] in Hexpire.
      apply (proj1 (Hexpiration h x)) in Hexpire.
      apply (observation_expiration_safe EX S SS ix (observation_components p)
        (map ObservationComponent.members first)
        h body (map ObservationComponent.members last) x Hix Hdistinct).
      * rewrite <- Hmembers, Hsplit, map_app; reflexivity.
      * exact Hexpire.
      * apply observation_needed_system in Hneeded; exact Hneeded.
Qed.

Lemma observation_system_post {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (fallback : C) (values : assignment X A) :
  post_solution L (observation_system S fallback) (lookup EX L values) ->
  post_solution L S (lookup EX L values).
Proof.
  intros Hpost c Hc; destruct (observation_label_covers S fallback c Hc) as [i [Hi Hlabel]].
  specialize (Hpost i Hi).
  change (constraint_satisfied L S
    (observation_label fallback (observation_number 0 (System.constraints S)) i)
    (lookup EX L values)) in Hpost.
  now rewrite Hlabel in Hpost.
Qed.

Lemma observation_empty_roots {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (roots : list X) (p : observation_plan X) :
  observation_plan_check EX S SS ix roots p = true -> System.constraints S = [] -> roots = [].
Proof.
  intros Hcheck Hconstraints.
  destruct (observation_plan_checked EX S SS ix roots p Hcheck) as [_ [Hroots _]].
  assert (Hunknowns : unknowns EX S SS = []).
  { unfold unknowns; rewrite Hconstraints; reflexivity. }
  destruct roots as [|x rest]; [reflexivity|].
  specialize (Hroots x (or_introl eq_refl)); rewrite Hunknowns in Hroots; contradiction.
Qed.

(** A successful full-memory reference directly establishes the original post-solution. *)
Theorem observation_full_reference_sound {X C A} (EX : encoding X) (L : lattice A)
    (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (roots : list X) (p : observation_plan X) (fuel : positive)
    (m : assignment X A) :
  sys_index_laws EX S SS ix ->
  observation_full_reference EX L st S SS ix roots p fuel = Some m ->
  post_solution L S (lookup EX L m).
Proof.
  intros Hix; unfold observation_full_reference.
  destruct (observation_plan_check EX S SS ix roots p) eqn:Hcheck; [|discriminate].
  destruct (System.constraints S) as [|fallback rest] eqn:Hconstraints.
  - intros Hresult c Hc; rewrite Hconstraints in Hc; contradiction.
  - cbn zeta; fold (observation_compile EX S SS fallback roots p).
    destruct (observation_execute EX L st (observation_system S fallback)
      (observation_compile EX S SS fallback roots p) false fuel) as [[values output]|]
      eqn:Hrun; [|discriminate].
    cbn [option_map fst]; intro Hresult; inversion Hresult; subst m.
    apply (observation_system_post EX L S fallback values).
    exact (proj1 (observation_execute_spec EX L st (observation_system S fallback)
      (observation_static S SS fallback) roots (observation_compile EX S SS fallback roots p)
      fuel values output (observation_compile_valid EX S SS ix fallback roots p Hix Hcheck) Hrun)).
Qed.

(** Eviction preserves the reference observations at every budget, including exhaustion. *)
Theorem observation_run_refines {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
    (p : observation_plan X) (fuel : positive) :
  sys_index_laws EX S SS ix ->
  observation_run EX L st S SS ix roots p fuel =
    observation_reference EX L st S SS ix roots p fuel.
Proof.
  intro Hix; unfold observation_run, observation_reference, observation_full_reference.
  destruct (observation_plan_check EX S SS ix roots p) eqn:Hcheck; [|reflexivity].
  destruct (System.constraints S) as [|fallback rest] eqn:Hconstraints.
  - rewrite (observation_empty_roots EX S SS ix roots p Hcheck Hconstraints); reflexivity.
  - cbn zeta; fold (observation_compile EX S SS fallback roots p).
    pose proof (observation_compile_valid EX S SS ix fallback roots p Hix Hcheck) as Hvalid.
    rewrite (observation_execute_agrees EX L st (observation_system S fallback)
      (observation_static S SS fallback) roots (observation_compile EX S SS fallback roots p)
      fuel Hvalid).
    destruct (observation_execute EX L st (observation_system S fallback)
      (observation_compile EX S SS fallback roots p) false fuel) as [[values output]|]
      eqn:Hrun; [|reflexivity].
    cbn [option_map fst snd].
    pose proof (proj2 (observation_execute_spec EX L st (observation_system S fallback)
      (observation_static S SS fallback) roots (observation_compile EX S SS fallback roots p)
      fuel values output Hvalid Hrun)) as Houtput.
    now rewrite Houtput.
Qed.

(** * Eventual completion *)

(** Each prepared local iterator is accessible from every valid control state and input. *)
Lemma observation_component_acc {X C A} (EX : encoding X) (L : lattice A)
    (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
    (fallback : C) (roots : FinSet.t X) (expiration : Map.t X (list X)) (members : list X) :
  (forall c, In c (System.constraints S) -> side_targets SS c = []) ->
  incl members (unknowns EX S SS) -> terminates L SS (wto_scheduler EX S SS) st ->
  let T := observation_system S fallback in
  let component := observation_component EX S SS (nested_targets EX T) roots expiration members in
  forall state, nested_control_valid EX (code component)
    (observation_subsystem EX T members) state ->
  Acc (fun next state => nested_step EX L (code component) st T state = Some next) state.
Proof.
  intros Hsides Hmembers HT T component state Hcontrol.
  set (local_system := observation_subsystem EX T members).
  set (local_static := observation_substatic EX T (observation_static S SS fallback) members).
  assert (Htargets : forall x, incl (index_get EX (NestedPlan.targets (code component)) x)
    (System.constraints local_system)).
  { apply observation_component_targets. }
  destruct st.
  - destruct HT as [Hheight].
    apply (nested_valid_acc EX nat_encoding L HL (code component) Joining local_system local_static
      (fun _ => true) (fun _ a => bound Hheight - rank Hheight a) (fun _ => 1)).
    + intros x old a Hx Hbelow; apply (total_height_progress L HL Hheight); exact Hbelow.
    + intros c Hc; apply total_join_weight.
    + exact Htargets.
    + exact Hcontrol.
  - destruct HT as [[W] Hglobal_cut].
    set (points := widening_point (nested_scheduler EX (code component))).
    assert (Hcut : cuts_every_cycle local_static points).
    { apply (observation_local_cuts EX S SS local_system local_static members Hmembers).
      intros y x Hflow.
      assert (Hlocal_sides : forall i, In i (System.constraints T) ->
        side_targets (observation_static S SS fallback) i = []).
      { intros i Hi; apply Hsides, (observation_label_in S fallback i); exact Hi. }
      destruct (observation_subflow EX T (observation_static S SS fallback) members
        Hlocal_sides y x Hflow) as [Hsource Hmember].
      split; [apply observation_system_flows in Hsource; exact Hsource|exact Hmember]. }
    apply (nested_valid_acc EX nat_encoding L HL (code component) Widening
      local_system local_static points (fun x a => if points x then wrank W a else 0)
      (total_constraint_weight EX local_system local_static
        (index_system EX local_system local_static)
        points (index_system_laws EX local_system local_static) Hcut)).
    + intros x old a Hx Hbelow; unfold update_value; fold points.
      destruct (points x); cbn; [pose proof (widen_rank_progress W old a Hbelow); lia|auto].
    + intros c Hc; apply total_constraint_weight_dominates.
    + exact Htargets.
    + exact Hcontrol.
Qed.

Definition observation_begin {X C A} (schedule : list (ObservationComponent.t X C))
    (values output : assignment X A) :
    ObservationState.t X C A + (assignment X A * assignment X A) :=
  match schedule with
  | [] => inr (values, output)
  | first :: rest => inl (ObservationState.Make first rest
      (observation_start_local first values) output)
  end.

Lemma observation_repeat_iter {B} (tick : B -> B) (fuel : positive) :
  forall state, observation_repeat tick fuel state = Nat.iter (Pos.to_nat fuel) tick state.
Proof.
  induction fuel as [fuel IH|fuel IH|]; intro state; cbn [observation_repeat].
  - rewrite Pos2Nat.inj_xI.
    replace (S (2 * Pos.to_nat fuel)) with (S (Pos.to_nat fuel + Pos.to_nat fuel)) by lia.
    rewrite Nat.iter_succ, Nat.iter_add, !IH; reflexivity.
  - rewrite Pos2Nat.inj_xO.
    replace (2 * Pos.to_nat fuel) with (Pos.to_nat fuel + Pos.to_nat fuel) by lia.
    rewrite Nat.iter_add, !IH; reflexivity.
  - reflexivity.
Qed.

Lemma observation_iter_finished {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (evict : bool) (n : nat) (result : assignment X A * assignment X A) :
  Nat.iter n (observation_tick EX L st S evict) (inr result) = inr result.
Proof.
  induction n as [|n IH]; [reflexivity|rewrite Nat.iter_succ, IH; reflexivity].
Qed.

Lemma observation_execute_begin {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (schedule : list (ObservationComponent.t X C)) (fuel : positive) :
  observation_execute EX L st S schedule false fuel =
    match observation_repeat (observation_tick EX L st S false) fuel
      (observation_begin schedule Map.empty Map.empty) with
    | inl _ => None
    | inr result => Some result
    end.
Proof.
  destruct schedule as [|first rest]; [|reflexivity].
  cbn [observation_begin]; rewrite observation_repeat_iter, observation_iter_finished; reflexivity.
Qed.

(** Finite local executions compose through free component-boundary bookkeeping. *)
Lemma observation_finish_schedule {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (schedule : list (ObservationComponent.t X C)) :
  Forall (fun component => forall values : assignment X A,
    Acc (fun next state => nested_step EX L (code component) st S state = Some next)
      (observation_start_local component values)) schedule ->
  forall values output, exists n result,
    Nat.iter n (observation_tick EX L st S false) (observation_begin schedule values output) =
      inr result.
Proof.
  intro Hcomponents; induction Hcomponents as [|component rest Hcomponent Hrest IHrest];
    intros values output.
  - exists 0, (values, output); reflexivity.
  - assert (Hlocal : forall state output,
      Acc (fun next state => nested_step EX L (code component) st S state = Some next) state ->
      exists n result, Nat.iter n (observation_tick EX L st S false)
        (inl (ObservationState.Make component rest state output)) = inr result).
    { intros state initial_output Hacc; revert initial_output.
      induction Hacc as [state Hacc IHstate]; intro initial_output.
      destruct (nested_step EX L (code component) st S state) as [next|] eqn:Hstep.
      - destruct (IHstate next eq_refl initial_output) as [n [result Hfinish]].
        exists (Datatypes.S n), result; rewrite Nat.iter_succ_r.
        change (Nat.iter n (observation_tick EX L st S false)
          (observation_tick EX L st S false
            (inl (ObservationState.Make component rest state initial_output))) = inr result).
        unfold observation_tick at 2; cbn [active pending local observed]; now rewrite Hstep.
      - destruct (IHrest (NestedState.current state)
          (observation_record EX L (outputs component) (NestedState.current state) initial_output))
          as [n [result Hfinish]].
        exists (Datatypes.S n), result; rewrite Nat.iter_succ_r.
        change (Nat.iter n (observation_tick EX L st S false)
          (observation_tick EX L st S false
            (inl (ObservationState.Make component rest state initial_output))) = inr result).
        unfold observation_tick at 2; cbn [active pending local observed]; rewrite Hstep.
        destruct rest; exact Hfinish. }
    apply Hlocal, Hcomponent.
Qed.

Lemma observation_execute_eventually {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (schedule : list (ObservationComponent.t X C)) :
  Forall (fun component => forall values : assignment X A,
    Acc (fun next state => nested_step EX L (code component) st S state = Some next)
      (observation_start_local component values)) schedule ->
  exists fuel values output,
    observation_execute EX L st S schedule false fuel = Some (values, output).
Proof.
  intro Hcomponents.
  destruct (observation_finish_schedule EX L st S schedule Hcomponents Map.empty Map.empty)
    as [n [[values output] Hfinish]].
  exists (Pos.of_succ_nat n), values, output.
  rewrite observation_execute_begin, observation_repeat_iter, SuccNat2Pos.id_succ.
  rewrite Nat.iter_succ, Hfinish; reflexivity.
Qed.

Lemma observation_compile_accessible {X C A} (EX : encoding X) (L : lattice A)
    (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (fallback : C) (roots : list X) (p : observation_plan X) :
  observation_plan_check EX S SS ix roots p = true ->
  terminates L SS (wto_scheduler EX S SS) st ->
  Forall (fun component => forall values : assignment X A,
    Acc (fun next state => nested_step EX L (code component) st (observation_system S fallback)
      state = Some next) (observation_start_local component values))
    (observation_compile EX S SS fallback roots p).
Proof.
  intros Hcheck HT.
  destruct (observation_plan_checked EX S SS ix roots p Hcheck)
    as [Hsides [_ [[_ [Hcover _]] _]]].
  apply Forall_forall; intros component Hcomponent values.
  unfold observation_compile in Hcomponent; apply in_map_iff in Hcomponent.
  destruct Hcomponent as [xs [Heq Hxs]]; subst component.
  apply observation_component_acc;
    [exact HL|exact Hsides| |exact HT|apply observation_start_control].
  intros x Hx; apply (proj1 (Hcover x)).
  apply in_concat; exists xs; split; [exact Hxs|exact Hx].
Qed.

(** Finite height or a widening rank suffices for every independently derived local WTO. *)
Theorem observation_run_eventually {X C A} (EX : encoding X) (L : lattice A)
    (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (roots : list X) (p : observation_plan X) :
  sys_index_laws EX S SS ix -> observation_plan_check EX S SS ix roots p = true ->
  terminates L SS (wto_scheduler EX S SS) st ->
  exists fuel m, observation_run EX L st S SS ix roots p fuel = Some m.
Proof.
  intros Hix Hcheck HT.
  destruct (System.constraints S) as [|fallback rest] eqn:Hconstraints.
  - exists 1%positive, Map.empty; unfold observation_run; now rewrite Hcheck, Hconstraints.
  - destruct (observation_execute_eventually EX L st (observation_system S fallback)
      (observation_compile EX S SS fallback roots p)
      (observation_compile_accessible EX L HL st S SS ix fallback roots p Hcheck HT))
      as [fuel [values [output Hrun]]].
    exists fuel, (observation_project EX L roots values).
    rewrite observation_run_refines by exact Hix.
    unfold observation_reference, observation_full_reference; rewrite Hcheck, Hconstraints.
    cbn zeta; fold (observation_compile EX S SS fallback roots p); rewrite Hrun.
    reflexivity.
Qed.

(** * Complete trace and widening-history correspondence *)

(** An event retains the query trace, old value, effective new value and widening decision. *)
Definition observation_execution_event {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A)
    (result : ObservationState.t X C A + (assignment X A * assignment X A)) :
    option (C * (A * list X * list (X * A)) * A * A * bool) :=
  match result with
  | inr _ => None
  | inl state =>
    match NestedState.ready (local state) with
    | [] => None
    | c :: _ =>
      let run := Query.run (System.rhs S c) (lookup EX L (NestedState.current (local state))) in
      let old := lookup EX L (NestedState.current (local state)) (System.target S c) in
      let sch := nested_scheduler EX (code (active state)) in
      let new := if leb L (fst (fst run)) old then old
        else update_value L sch st (System.target S c) old (fst (fst run)) in
      let uses_widening := negb (leb L (fst (fst run)) old) && match st with
        | Joining => false
        | Widening => widening_point sch (System.target S c)
        end in
      Some (c, run, old, new, uses_widening)
    end
  end.

Lemma observation_execution_event_agrees {X C A} (EX : encoding X) (L : lattice A)
    (st : strategy) (S : System.t X C A) (SS : System.static S) (roots : list X)
    (schedule : list (ObservationComponent.t X C))
    (full live : ObservationState.t X C A + (assignment X A * assignment X A)) :
  observation_schedule_valid EX S SS roots schedule ->
  observation_execution_agrees EX L S SS schedule full live ->
  observation_execution_event EX L st S full = observation_execution_event EX L st S live.
Proof.
  intros Hvalid Hagree; destruct full as [full|[full_values full_output]],
    live as [live|[live_values live_output]];
    cbn [observation_execution_agrees] in Hagree; try contradiction; [|reflexivity].
  destruct Hagree as [Hactive [Hpending [Houtput [prefix [Hschedule [Hcontrol Hagree]]]]]].
  pose proof (proj1 Hagree) as Hlocal_control.
  assert (Hready : NestedState.ready (local full) = NestedState.ready (local live)).
  { unfold observation_local_control in Hlocal_control; now inversion Hlocal_control. }
  unfold observation_execution_event; rewrite <- Hready, <- Hactive.
  destruct (NestedState.ready (local full)) as [|c rest] eqn:Hcs; [reflexivity|].
  destruct (observation_ready_domains EX L S SS (active full) (pending full) (local full)
    (observation_schedule_side_free Hvalid) Hcontrol c ltac:(rewrite Hcs; now left))
    as [Hreads [Htarget Hsides]].
  rewrite (observation_query_agrees EX L S SS _ (local full) (local live) c Hagree Hreads).
  rewrite (proj2 Hagree (System.target S c) Htarget); reflexivity.
Qed.

Section ObservationHistories.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A).

(** This proof relation records any finite prefix of paid ticks, including administrative events. *)
Inductive observation_history (evict : bool) :
    ObservationState.t X C A + (assignment X A * assignment X A) ->
    list (option (C * (A * list X * list (X * A)) * A * A * bool)) ->
    ObservationState.t X C A + (assignment X A * assignment X A) -> Prop :=
  | ObservationHistoryNil : forall state, observation_history evict state [] state
  | ObservationHistoryCons : forall state trace final,
      observation_history evict (observation_tick EX L st S evict state) trace final ->
      observation_history evict state (observation_execution_event EX L st S state :: trace) final.

End ObservationHistories.

(** Every full-memory history has an identical evicting history, with the same widening inputs. *)
Lemma observation_history_agrees {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (roots : list X)
    (schedule : list (ObservationComponent.t X C)) :
  observation_schedule_valid EX S SS roots schedule ->
  forall full trace final, observation_history EX L st S false full trace final ->
  forall live, observation_execution_agrees EX L S SS schedule full live ->
  exists live_final, observation_history EX L st S true live trace live_final /\
    observation_execution_agrees EX L S SS schedule final live_final.
Proof.
  intros Hvalid full trace final Hhistory; induction Hhistory as [state|state trace final Htail IH];
    intros live Hagree.
  - exists live; split; [constructor|exact Hagree].
  - destruct (IH (observation_tick EX L st S true live)
      (observation_tick_agrees EX L st S SS roots schedule Hvalid state live Hagree))
      as [live_final [Hlive Hfinal]].
    exists live_final; split; [|exact Hfinal].
    rewrite (observation_execution_event_agrees EX L st S SS roots schedule
      state live Hvalid Hagree).
    constructor; exact Hlive.
Qed.
