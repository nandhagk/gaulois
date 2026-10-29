(** * Direct nested WTO iteration

    Explicit frames stabilize components and repeat the outer traversal after any changed value.
    For example, a side contribution into an earlier component forces another outer pass.
    Builds on: FixpointSchedule, FixpointTotal, GraphWto and OrderLattice. *)

From Stdlib Require Import List Bool Arith PeanoNat PArith Lia Wf_nat Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphWto.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointCycles FixpointWorklist FixpointTotal FixpointSchedule.
Import List.ListNotations.

(** * Prepared traversal *)

(** Components retain their body separately from the following siblings. *)
Inductive nested_code (X : Type) : Type :=
  | NestedEnd
  | NestedVisit (x : X) (rest : nested_code X)
  | NestedComponent (h : X) (body rest : nested_code X).

Arguments NestedEnd {X}.
Arguments NestedVisit {X}.
Arguments NestedComponent {X}.

Fixpoint nested_tokens {X} (code : nested_code X) : wto X :=
  match code with
  | NestedEnd => []
  | NestedVisit x rest => WVertex x :: nested_tokens rest
  | NestedComponent h body rest =>
    WOpen h :: nested_tokens body ++ WClose :: nested_tokens rest
  end.

Fixpoint nested_vertices {X} (code : nested_code X) : list X :=
  match code with
  | NestedEnd => []
  | NestedVisit x rest => x :: nested_vertices rest
  | NestedComponent h body rest => h :: nested_vertices body ++ nested_vertices rest
  end.

Fixpoint nested_heads {X} (code : nested_code X) : list X :=
  match code with
  | NestedEnd => []
  | NestedVisit _ rest => nested_heads rest
  | NestedComponent h body rest => h :: nested_heads body ++ nested_heads rest
  end.

(** The preparation bound is the token count; it never bounds stabilization iterations. *)
Fixpoint nested_parse {X} (bound : nat) (tokens : wto X) : nested_code X * wto X :=
  match bound with
  | 0 => (NestedEnd, tokens)
  | S smaller =>
    match tokens with
    | [] => (NestedEnd, [])
    | WClose :: rest => (NestedEnd, rest)
    | WVertex x :: rest =>
      let '(code, after) := nested_parse smaller rest in (NestedVisit x code, after)
    | WOpen h :: rest =>
      let '(body, after_body) := nested_parse smaller rest in
      let '(tail, after) := nested_parse smaller after_body in
      (NestedComponent h body tail, after)
    end
  end.

Definition nested_tree {X} (tokens : wto X) : nested_code X :=
  fst (nested_parse (S (length tokens)) (tokens ++ [WClose])).

Fixpoint nested_rows {X} (stack : list X) (code : nested_code X) : list (X * list X) :=
  match code with
  | NestedEnd => []
  | NestedVisit x rest => (x, stack) :: nested_rows stack rest
  | NestedComponent h body rest =>
    (h, h :: stack) :: nested_rows (h :: stack) body ++ nested_rows stack rest
  end.

Definition nested_members {X} (EX : encoding X) (code : nested_code X) : Map.t X (list X) :=
  fold_right (fun row ix => Map.set EX (fst row) (snd row) ix)
    Map.empty (nested_rows [] code).

Definition nested_targets {X C A} (EX : encoding X) (S : System.t X C A) :
    Map.t X (list C) :=
  fold_right (fun c ix => index_push EX c (System.target S c) ix)
    Map.empty (System.constraints S).

Module NestedPlan.
Record t (X C : Type) : Type := Make {
  root : nested_code X;
  members : Map.t X (list X);
  targets : Map.t X (list C);
  heads : FinSet.t X
}.
Arguments Make {X C}.
Arguments root {X C}.
Arguments members {X C}.
Arguments targets {X C}.
Arguments heads {X C}.
End NestedPlan.
Import NestedPlan.

Definition nested_prepare {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : NestedPlan.t X C :=
  let graph := dependency_graph EX S SS in
  let tokens := wto_total (prepare EX graph) in
  let code := nested_tree tokens in
  NestedPlan.Make code (nested_members EX code) (nested_targets EX S)
    (FinSet.of_list EX (nested_heads code)).

(** * Explicit frames and updates *)

Module NestedFrame.
Record t (X : Type) : Type := Make {
  remaining : nested_code X;
  restart : option (X * nested_code X)
}.
Arguments Make {X}.
Arguments remaining {X}.
Arguments restart {X}.
End NestedFrame.
Import NestedFrame.

Module NestedState.
Record t (X C A : Type) : Type := Make {
  current : assignment X A;
  ready : list C;
  frames : list (NestedFrame.t X);
  dirty : FinSet.t X;
  changed : bool
}.
Arguments Make {X C A}.
Arguments current {X C A}.
Arguments ready {X C A}.
Arguments frames {X C A}.
Arguments dirty {X C A}.
Arguments changed {X C A}.
End NestedState.
Import NestedState.

Definition nested_start {X C A} (plan : NestedPlan.t X C) : NestedState.t X C A :=
  NestedState.Make Map.empty [] [NestedFrame.Make (NestedPlan.root plan) None]
    FinSet.empty false.

(** A change marks every containing component, including suspended components. *)
Definition nested_mark {X C A} (EX : encoding X) (plan : NestedPlan.t X C) (x : X)
    (state : NestedState.t X C A) (values : assignment X A) : NestedState.t X C A :=
  NestedState.Make values (NestedState.ready state) (NestedState.frames state)
    (fold_left (fun dirty h => FinSet.add EX h dirty)
      (index_get EX (NestedPlan.members plan) x) (NestedState.dirty state)) true.

Definition nested_scheduler {X C} (EX : encoding X) (plan : NestedPlan.t X C) : scheduler X :=
  Scheduler (fun _ => 1%positive) (fun x => FinSet.mem EX x (NestedPlan.heads plan)).

Definition nested_update {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (xa : X * A)
    (state : NestedState.t X C A) : NestedState.t X C A :=
  let '(x, a) := xa in
  let old := lookup EX L (NestedState.current state) x in
  if leb L a old then state
  else nested_mark EX plan x state
    (Map.set EX x (update_value L (nested_scheduler EX plan)
      st x old a) (NestedState.current state)).

Definition nested_updates {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (updates : list (X * A))
    (state : NestedState.t X C A) : NestedState.t X C A :=
  fold_left (fun state xa => nested_update EX L plan st xa state) updates state.

(** One transition evaluates one constraint, or advances exactly one traversal frame. *)
Definition nested_step {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (S : System.t X C A)
    (state : NestedState.t X C A) : option (NestedState.t X C A) :=
  let values := NestedState.current state in
  let dirty := NestedState.dirty state in
  let changed := NestedState.changed state in
  match NestedState.ready state with
  | c :: rest =>
    let '(v, _, sides) := Query.run (System.rhs S c) (lookup EX L values) in
    Some (nested_updates EX L plan st ((System.target S c, v) :: sides)
      (NestedState.Make values rest (NestedState.frames state) dirty changed))
  | [] =>
    match NestedState.frames state with
    | [] => None
    | frame :: frames =>
      match NestedFrame.remaining frame with
      | NestedVisit x rest =>
        Some (NestedState.Make values (index_get EX (NestedPlan.targets plan) x)
          (NestedFrame.Make rest (NestedFrame.restart frame) :: frames) dirty changed)
      | NestedComponent h body rest =>
        let pass := NestedVisit h body in
        Some (NestedState.Make values []
          (NestedFrame.Make pass (Some (h, pass)) ::
            NestedFrame.Make rest (NestedFrame.restart frame) :: frames)
          (FinSet.remove EX h dirty) changed)
      | NestedEnd =>
        match NestedFrame.restart frame with
        | Some (h, pass) =>
          if FinSet.mem EX h dirty then
            Some (NestedState.Make values []
              (NestedFrame.Make pass (Some (h, pass)) :: frames)
              (FinSet.remove EX h dirty) changed)
          else Some (NestedState.Make values [] frames dirty changed)
        | None =>
          if changed then Some (NestedState.Make values []
            [NestedFrame.Make (NestedPlan.root plan) None] dirty false)
          else None
        end
      end
    end
  end.

Definition nested_tick {X C A}
    (step : NestedState.t X C A -> option (NestedState.t X C A))
    (result : NestedState.t X C A + assignment X A) :
    NestedState.t X C A + assignment X A :=
  match result with
  | inl state =>
    match step state with
    | None => inr (NestedState.current state)
    | Some next => inl next
    end
  | inr values => inr values
  end.

(** Binary composition keeps the Gallina recursion depth logarithmic in the fuel. *)
Fixpoint nested_loop {X C A} (step : NestedState.t X C A -> option (NestedState.t X C A))
    (fuel : positive) (state : NestedState.t X C A) :
    NestedState.t X C A + assignment X A :=
  let continue := nested_tick step in
  match fuel with
  | xH => continue (inl state)
  | xO smaller =>
    match nested_loop step smaller state with
    | inl next => nested_loop step smaller next
    | inr values => inr values
    end
  | xI smaller =>
    continue
      (match nested_loop step smaller state with
      | inl next => nested_loop step smaller next
      | inr values => inr values
      end)
  end.

(** A successful run finishes a no-change outer pass; exhaustion returns no assignment. *)
Definition nested_run {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (st : strategy) (S : System.t X C A) (SS : System.static S) (fuel : positive) :
    option (assignment X A) :=
  let plan := nested_prepare EX S SS in
  match nested_loop (nested_step EX L plan st S) fuel (nested_start plan) with
  | inl _ => None
  | inr values => Some values
  end.

(** * Preparation agreement *)

Lemma nested_tokens_balanced {X} (code : nested_code X) : wto_nested (nested_tokens code).
Proof.
  induction code; cbn [nested_tokens]; constructor; assumption.
Qed.

Lemma nested_tokens_surjective {X} (tokens : wto X) :
  wto_nested tokens -> exists code, nested_tokens code = tokens.
Proof.
  intro Hnested; induction Hnested as [|x tail Htail [rest Hrest]|
    h body tail Hbody [inside Hinside] Htail [rest Hrest]].
  - exists NestedEnd; reflexivity.
  - exists (NestedVisit x rest); cbn; now rewrite Hrest.
  - exists (NestedComponent h inside rest); cbn; now rewrite Hinside, Hrest.
Qed.

Lemma nested_parse_tokens {X} (code : nested_code X) :
  forall n tail, length (nested_tokens code) < n ->
  nested_parse n (nested_tokens code ++ WClose :: tail) = (code, tail).
Proof.
  induction code as [|x rest IH|h body IHbody rest IHrest]; intros [|n] tail Hbound;
    cbn [nested_tokens length] in Hbound; try lia.
  - reflexivity.
  - cbn [nested_tokens app nested_parse]; rewrite IH by lia; reflexivity.
  - cbn [nested_tokens app nested_parse]; rewrite <- app_assoc; cbn [app].
    rewrite IHbody by (rewrite length_app in Hbound; cbn in Hbound; lia).
    rewrite IHrest by (rewrite length_app in Hbound; cbn in Hbound; lia).
    reflexivity.
Qed.

Lemma nested_tree_tokens {X} (tokens : wto X) :
  balanced_from 0 tokens = true -> nested_tokens (nested_tree tokens) = tokens.
Proof.
  intro Hbalanced.
  destruct (nested_tokens_surjective tokens (balanced_nested tokens Hbalanced))
    as [code Hcode].
  subst tokens; unfold nested_tree; rewrite nested_parse_tokens by lia; reflexivity.
Qed.

Lemma nested_vertices_tokens {X} (code : nested_code X) :
  wto_vertices (nested_tokens code) = nested_vertices code.
Proof.
  induction code as [|x rest IH|h body IHbody rest IHrest]; cbn [nested_tokens
    nested_vertices wto_vertices]; [reflexivity|now rewrite IH|].
  rewrite wto_vertices_app; cbn [wto_vertices]; now rewrite IHbody, IHrest.
Qed.

Lemma nested_heads_tokens {X} (code : nested_code X) :
  schedule_heads (nested_tokens code) = nested_heads code.
Proof.
  assert (Happ : forall (left right : wto X),
    schedule_heads (left ++ right) = schedule_heads left ++ schedule_heads right).
  { intros left right; induction left as [|[x|h|] rest IH]; cbn; now rewrite ?IH. }
  induction code as [|x rest IH|h body IHbody rest IHrest]; cbn [nested_tokens
    nested_heads schedule_heads]; [reflexivity|exact IH|].
  rewrite Happ; cbn [schedule_heads]; now rewrite IHbody, IHrest.
Qed.

Lemma nested_rows_tokens {X} (code : nested_code X) :
  forall stack tail, annotate stack (nested_tokens code ++ tail) =
    nested_rows stack code ++ annotate stack tail.
Proof.
  induction code as [|x rest IH|h body IHbody rest IHrest]; intros stack tail;
    cbn [nested_tokens nested_rows app annotate]; [reflexivity|now rewrite IH|].
  rewrite <- app_assoc, IHbody; cbn [app annotate tl]; rewrite IHrest, app_assoc; reflexivity.
Qed.

Lemma nested_rows_vertices {X} (code : nested_code X) (stack : list X) :
  map fst (nested_rows stack code) = nested_vertices code.
Proof.
  revert stack; induction code; intro stack; cbn [nested_rows nested_vertices map];
    rewrite ?map_app, ?IHcode, ?IHcode1, ?IHcode2; reflexivity.
Qed.

Lemma nested_members_agree {X} (EX : encoding X) (code : nested_code X) (x h : X) :
  NoDup (nested_vertices code) ->
  (In h (index_get EX (nested_members EX code) x) <->
    exists stack, In (x, stack) (nested_rows [] code) /\ In h stack).
Proof.
  unfold nested_members; rewrite <- (nested_rows_vertices code []).
  generalize (nested_rows [] code) as rows; intro rows; induction rows as [|[y stack] rows IH];
    intro Hnodup; cbn [fold_right map fst] in *.
  - unfold index_get; rewrite Map.get_empty; cbn; firstorder.
  - inversion Hnodup as [|? ? Hfresh Htail]; subst.
    destruct (Pos.eq_dec (encode EX x) (encode EX y)) as [Heq|Hne].
    + apply (encode_injective EX) in Heq; subst x.
      unfold index_get at 1; rewrite Map.get_set_same; cbn.
      split; [intro Hin; exists stack; auto|].
      intros [other [[Heq|Hin] Hh]]; [inversion Heq; subst; exact Hh|].
      exfalso; apply Hfresh; apply in_map_iff; exists (y, other); auto.
    + unfold index_get at 1; rewrite Map.get_set_other by
        (intro Heq; subst y; contradiction).
      fold (index_get EX (fold_right
        (fun row ix => Map.set EX (fst row) (snd row) ix) Map.empty rows) x).
      rewrite IH by exact Htail.
      split; intros [other [Hin Hh]]; exists other; split; [now right|exact Hh| |exact Hh].
      destruct Hin as [Heq|Hin]; [inversion Heq; subst; contradiction|exact Hin].
Qed.

Lemma nested_targets_agree {X C A} (EX : encoding X) (S : System.t X C A) (x : X) :
  index_get EX (nested_targets EX S) x =
    filter (fun c => Pos.eqb (encode EX x) (encode EX (System.target S c)))
      (System.constraints S).
Proof.
  unfold nested_targets; induction (System.constraints S) as [|c cs IH]; cbn [fold_right].
  - apply index_get_empty.
  - rewrite index_get_push; cbn [filter].
    destruct (Pos.eqb (encode EX x) (encode EX (System.target S c))); now rewrite IH.
Qed.

Lemma nested_prepared_tokens {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) :
  nested_tokens (NestedPlan.root (nested_prepare EX S SS)) =
    wto_total (prepare EX (dependency_graph EX S SS)).
Proof.
  apply nested_tree_tokens.
  exact (proj1 (wto_total_valid _ _ _ (dependency_graph_ready EX S SS))).
Qed.

(** The parser's component heads are exactly the scheduler's widening points. *)
Lemma nested_prepared_heads {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (x : X) :
  FinSet.mem EX x (NestedPlan.heads (nested_prepare EX S SS)) =
    widening_point (wto_scheduler EX S SS) x.
Proof.
  unfold nested_prepare, wto_scheduler; cbn [NestedPlan.heads widening_point].
  rewrite <- nested_heads_tokens, nested_tree_tokens; [reflexivity|].
  exact (proj1 (wto_total_valid _ _ _ (dependency_graph_ready EX S SS))).
Qed.

Lemma nested_prepared_covers {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) :
  NoDup (nested_vertices (NestedPlan.root (nested_prepare EX S SS))) /\
  forall c, In c (System.constraints S) ->
    In (System.target S c) (nested_vertices (NestedPlan.root (nested_prepare EX S SS))).
Proof.
  pose proof (wto_total_valid _ _ _ (dependency_graph_ready EX S SS))
    as [Hbalanced [Hnodup [Hcover Hedges]]].
  rewrite <- nested_vertices_tokens, nested_prepared_tokens.
  rewrite <- (annotate_vertices _ []).
  split; [exact Hnodup|].
  intros c Hc; apply Hcover, reachable_entry.
  apply (proj2 (proj2 (unknowns_spec EX S SS) _)); exists c; auto.
Qed.

Lemma nested_prepared_outputs {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (c : C) (x : X) :
  In c (System.constraints S) -> (x = System.target S c \/ In x (side_targets SS c)) ->
  In x (nested_vertices (NestedPlan.root (nested_prepare EX S SS))).
Proof.
  intros Hc Houtput.
  pose proof (wto_total_valid _ _ _ (dependency_graph_ready EX S SS))
    as [_ [_ [Hcover _]]].
  rewrite <- nested_vertices_tokens, nested_prepared_tokens, <- (annotate_vertices _ []).
  apply Hcover, reachable_entry, (proj2 (proj2 (unknowns_spec EX S SS) x)).
  exists c; split; [exact Hc|destruct Houtput as [Heq|Hin]; auto].
Qed.

(** * Final-pass soundness *)

Section NestedSoundness.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (HL : lattice_laws L)
  (plan : NestedPlan.t X C) (st : strategy) (S : System.t X C A).

Definition nested_pending (state : NestedState.t X C A) (c : C) : Prop :=
  In c (NestedState.ready state) \/
  exists frame x, In frame (NestedState.frames state) /\
    In x (nested_vertices (NestedFrame.remaining frame)) /\
    In c (index_get EX (NestedPlan.targets plan) x).

(** During a clean outer pass, every constraint is still ahead or already satisfied. *)
Definition nested_sound_state (state : NestedState.t X C A) : Prop :=
  NestedState.changed state = true \/ forall c, In c (System.constraints S) ->
    nested_pending state c \/ constraint_satisfied L S c (lookup EX L (NestedState.current state)).

Lemma nested_update_changed (state : NestedState.t X C A) (xa : X * A) :
  NestedState.changed state = true ->
  NestedState.changed (nested_update EX L plan st xa state) = true.
Proof.
  destruct xa as [x a]; unfold nested_update; destruct (leb L a _); auto.
Qed.

Lemma nested_updates_changed (updates : list (X * A)) (state : NestedState.t X C A) :
  NestedState.changed state = true ->
  NestedState.changed (nested_updates EX L plan st updates state) = true.
Proof.
  revert state; induction updates as [|xa updates IH]; intros state Hchanged;
    cbn [nested_updates fold_left]; [exact Hchanged|].
  apply IH, nested_update_changed; exact Hchanged.
Qed.

Lemma nested_updates_clean (updates : list (X * A)) (state : NestedState.t X C A) :
  NestedState.changed (nested_updates EX L plan st updates state) = false ->
  nested_updates EX L plan st updates state = state /\
    forall x a, In (x, a) updates -> leb L a (lookup EX L (NestedState.current state) x) = true.
Proof.
  revert state; induction updates as [|[x a] updates IH]; intros state Hclean.
  - cbn [nested_updates]; split; [reflexivity|intros y b Hin; contradiction].
  - change (NestedState.changed (nested_updates EX L plan st updates
      (nested_update EX L plan st (x, a) state)) = false) in Hclean.
    unfold nested_update in Hclean.
    destruct (leb L a (lookup EX L (NestedState.current state) x)) eqn:Hbelow.
    + destruct (IH state Hclean) as [Heq Hbounds].
      cbn [nested_updates fold_left]; unfold nested_update; rewrite Hbelow.
      split; [exact Heq|].
      intros y b [Hpair|Hin]; [inversion Hpair; subst; exact Hbelow|apply Hbounds; exact Hin].
    + assert (Hchanged : forall values,
        NestedState.changed (nested_updates EX L plan st updates
          (nested_mark EX plan x state values)) = true).
      { intro values; apply nested_updates_changed; reflexivity. }
      rewrite Hchanged in Hclean; discriminate.
Qed.

Hypothesis Hcover : forall c, In c (System.constraints S) ->
  exists x, In x (nested_vertices (NestedPlan.root plan)) /\
    In c (index_get EX (NestedPlan.targets plan) x).

Lemma nested_root_sound (values : assignment X A) (dirty : FinSet.t X) :
  nested_sound_state (NestedState.Make values []
    [NestedFrame.Make (NestedPlan.root plan) None] dirty false).
Proof.
  right; intros c Hc; left; right.
  destruct (Hcover c Hc) as [x [Hx Hin]].
  exists (NestedFrame.Make (NestedPlan.root plan) None), x; cbn; auto.
Qed.

Lemma nested_evaluation_sound (state : NestedState.t X C A) (c : C) (rest : list C) :
  NestedState.ready state = c :: rest -> nested_sound_state state ->
  nested_sound_state
    (nested_updates EX L plan st
      (let '(v, _, sides) := Query.run (System.rhs S c)
        (lookup EX L (NestedState.current state)) in (System.target S c, v) :: sides)
      (NestedState.Make (NestedState.current state) rest (NestedState.frames state)
        (NestedState.dirty state) (NestedState.changed state))).
Proof.
  intros Hready Hsound.
  rewrite run_spec.
  set (updates := (System.target S c,
    Query.eval (System.rhs S c) (lookup EX L (NestedState.current state))) ::
    Query.sides (System.rhs S c) (lookup EX L (NestedState.current state))).
  set (next := NestedState.Make (NestedState.current state) rest (NestedState.frames state)
    (NestedState.dirty state) (NestedState.changed state)).
  destruct (NestedState.changed (nested_updates EX L plan st updates next)) eqn:Hchanged;
    [now left|right].
  destruct (nested_updates_clean updates next Hchanged) as [Heq Hbounds]; rewrite Heq.
  assert (Hcurrent : constraint_satisfied L S c (lookup EX L (NestedState.current state))).
  { split.
    - exact (Hbounds _ _ (or_introl eq_refl)).
    - intros x a Hin; exact (Hbounds x a (or_intror Hin)). }
  intros d Hd; destruct Hsound as [Hdirty|Hsound].
  - pose proof (nested_updates_changed updates next Hdirty); congruence.
  - destruct (Hsound d Hd) as [[Hin|Hpending]|Hsatisfied]; [|now left; right|now right].
    rewrite Hready in Hin; destruct Hin as [Heqdc|Hin]; [subst d; now right|now left; left].
Qed.

Lemma nested_step_sound (state next : NestedState.t X C A) :
  nested_sound_state state -> nested_step EX L plan st S state = Some next ->
  nested_sound_state next.
Proof.
  intros Hsound Hstep; unfold nested_step in Hstep.
  destruct (NestedState.ready state) as [|c rest] eqn:Hready.
  2: { rewrite run_spec in Hstep; inversion Hstep; subst next.
    pose proof (nested_evaluation_sound state c rest Hready Hsound) as Hnext.
    rewrite run_spec in Hnext; exact Hnext. }
  destruct (NestedState.frames state) as [|[code restart] frames] eqn:Hframes;
    [discriminate|].
  cbn [NestedFrame.remaining NestedFrame.restart] in Hstep.
  destruct code as [|x rest|h body rest].
  - destruct restart as [[h pass]|].
    + destruct (FinSet.mem EX h (NestedState.dirty state)); inversion Hstep; subst next;
        destruct Hsound as [Hchanged|Hsound]; [now left|right|now left|right];
        intros c Hc; specialize (Hsound c Hc);
        destruct Hsound as [[Hin|[frame [x [Hframe [Hx Hin]]]]]|Hsatisfied];
        try (rewrite Hready in Hin; contradiction); [|now right| |now right];
        left; right; rewrite Hframes in Hframe; destruct Hframe as [Heq|Hframe];
        [subst frame; contradiction| |subst frame; contradiction|];
        exists frame, x; cbn; auto.
    + destruct (NestedState.changed state); [|discriminate].
      inversion Hstep; subst next; apply nested_root_sound.
  - inversion Hstep; subst next.
    destruct Hsound as [Hchanged|Hsound]; [now left|right].
    intros c Hc; destruct (Hsound c Hc) as [[Hin|[frame [y [Hframe [Hy Hin]]]]]|Hsatisfied];
      [rewrite Hready in Hin; contradiction| |now right].
    rewrite Hframes in Hframe; destruct Hframe as [Heq|Hframe].
    + subst frame; cbn in Hy; destruct Hy as [Heq|Hy].
      * subst y; left; left; exact Hin.
      * left; right; exists (NestedFrame.Make rest restart), y; cbn; auto.
    + left; right; exists frame, y; cbn; auto.
  - inversion Hstep; subst next.
    destruct Hsound as [Hchanged|Hsound]; [now left|right].
    intros c Hc; destruct (Hsound c Hc) as [[Hin|[frame [y [Hframe [Hy Hin]]]]]|Hsatisfied];
      [rewrite Hready in Hin; contradiction| |now right].
    rewrite Hframes in Hframe; destruct Hframe as [Heq|Hframe].
    + subst frame; cbn in Hy; destruct Hy as [Heq|Hy].
      * subst y; left; right; exists (NestedFrame.Make (NestedVisit h body)
          (Some (h, NestedVisit h body))), h; cbn; auto.
      * apply in_app_or in Hy; destruct Hy as [Hy|Hy]; left; right.
        -- exists (NestedFrame.Make (NestedVisit h body) (Some (h, NestedVisit h body))), y;
             cbn; auto.
        -- exists (NestedFrame.Make rest restart), y; cbn; auto.
    + left; right; exists frame, y; cbn; auto.
Qed.

End NestedSoundness.

Fixpoint nested_rooted {X} (frames : list (NestedFrame.t X)) : Prop :=
  match frames with
  | [] => False
  | frame :: rest =>
    match NestedFrame.restart frame with
    | None => rest = []
    | Some _ => nested_rooted rest
    end
  end.

Lemma nested_updates_frames {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (updates : list (X * A))
    (state : NestedState.t X C A) :
  NestedState.frames (nested_updates EX L plan st updates state) = NestedState.frames state.
Proof.
  revert state; induction updates as [|[x a] updates IH]; intro state; [reflexivity|].
  change (NestedState.frames (nested_updates EX L plan st updates
    (nested_update EX L plan st (x, a) state)) = NestedState.frames state).
  rewrite IH; unfold nested_update; destruct (leb L a _); reflexivity.
Qed.

Lemma nested_step_rooted {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (S : System.t X C A)
    (state next : NestedState.t X C A) :
  nested_rooted (NestedState.frames state) -> nested_step EX L plan st S state = Some next ->
  nested_rooted (NestedState.frames next).
Proof.
  intros Hroot Hstep; unfold nested_step in Hstep.
  destruct (NestedState.ready state) as [|c rest] eqn:Hready.
  2: { rewrite run_spec in Hstep; injection Hstep as Hnext; rewrite <- Hnext.
    rewrite nested_updates_frames.
    destruct (leb L (Query.eval (System.rhs S c) (lookup EX L (NestedState.current state)))
      (lookup EX L (NestedState.current state) (System.target S c))); exact Hroot. }
  destruct (NestedState.frames state) as [|[code restart] frames] eqn:Hframes;
    [contradiction|].
  cbn [NestedFrame.remaining NestedFrame.restart] in Hstep.
  destruct code as [|x rest|h body rest].
  - destruct restart as [[h pass]|]; cbn [nested_rooted NestedFrame.restart] in Hroot.
    + destruct (FinSet.mem EX h (NestedState.dirty state)); inversion Hstep; subst next;
        exact Hroot.
    + destruct (NestedState.changed state); [|discriminate].
      inversion Hstep; reflexivity.
  - inversion Hstep; subst next; exact Hroot.
  - inversion Hstep; subst next; exact Hroot.
Qed.

Lemma nested_finished_sound {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (S : System.t X C A)
    (state : NestedState.t X C A) :
  nested_rooted (NestedState.frames state) -> nested_sound_state EX L plan S state ->
  nested_step EX L plan st S state = None ->
  post_solution L S (lookup EX L (NestedState.current state)).
Proof.
  intros Hroot Hsound Hstep; unfold nested_step in Hstep.
  destruct (NestedState.ready state) as [|c rest] eqn:Hready.
  2: { rewrite run_spec in Hstep; discriminate. }
  destruct (NestedState.frames state) as [|[code restart] frames] eqn:Hframes;
    [contradiction|].
  cbn [NestedFrame.remaining NestedFrame.restart] in Hstep.
  destruct code; try discriminate.
  destruct restart as [[h pass]|].
  - destruct (FinSet.mem EX h (NestedState.dirty state)); discriminate.
  - destruct (NestedState.changed state) eqn:Hchanged; [discriminate|].
    cbn [nested_rooted NestedFrame.restart] in Hroot; subst frames.
    destruct Hsound as [Hdirty|Hsound]; [congruence|].
    intros c Hc; destruct (Hsound c Hc) as [[Hin|[frame [x [Hframe [Hx Hin]]]]]|Hsatisfied];
      [rewrite Hready in Hin; contradiction| |exact Hsatisfied].
    rewrite Hframes in Hframe; destruct Hframe as [Heq|Hbad];
      [subst frame; contradiction|contradiction].
Qed.

(** Binary execution preserves an invariant until a proved finished result is returned. *)
Lemma nested_loop_invariant {X C A}
    (step : NestedState.t X C A -> option (NestedState.t X C A))
    (I : NestedState.t X C A -> Prop) (P : assignment X A -> Prop) :
  (forall state next, I state -> step state = Some next -> I next) ->
  (forall state, I state -> step state = None -> P (NestedState.current state)) ->
  forall fuel state, I state ->
    match nested_loop step fuel state with
    | inl next => I next
    | inr values => P values
    end.
Proof.
  intros Hnext Hdone fuel; induction fuel as [fuel IH|fuel IH|]; intros state Hstate;
    cbn [nested_loop].
  - pose proof (IH state Hstate) as Hfirst.
    destruct (nested_loop step fuel state) as [first|values]; [|exact Hfirst].
    pose proof (IH first Hfirst) as Hsecond.
    destruct (nested_loop step fuel first) as [second|values]; [|exact Hsecond].
    cbn [nested_tick].
    destruct (step second) as [next|] eqn:Hstep.
    + exact (Hnext second next Hsecond Hstep).
    + exact (Hdone second Hsecond Hstep).
  - pose proof (IH state Hstate) as Hfirst.
    destruct (nested_loop step fuel state) as [first|values]; [|exact Hfirst].
    exact (IH first Hfirst).
  - cbn [nested_tick]; destruct (step state) as [next|] eqn:Hstep.
    + exact (Hnext state next Hstate Hstep).
    + exact (Hdone state Hstate Hstep).
Qed.

(** Completion of the final clean pass bounds every target and side contribution directly. *)
Theorem nested_run_sound {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
    (fuel : positive) (m : assignment X A) :
  nested_run EX EC L st S SS fuel = Some m -> post_solution L S (lookup EX L m).
Proof.
  assert (Hcover : forall c, In c (System.constraints S) ->
    exists x, In x (nested_vertices (NestedPlan.root (nested_prepare EX S SS))) /\
      In c (index_get EX (NestedPlan.targets (nested_prepare EX S SS)) x)).
  { intros c Hc; exists (System.target S c); split.
    - apply nested_prepared_covers; exact Hc.
    - change (In c (index_get EX (nested_targets EX S) (System.target S c))).
      rewrite nested_targets_agree; apply filter_In; split; [exact Hc|apply Pos.eqb_refl]. }
  set (plan := nested_prepare EX S SS) in *.
  pose proof (nested_loop_invariant (nested_step EX L plan st S)
    (fun state => nested_rooted (NestedState.frames state) /\ nested_sound_state EX L plan S state)
    (fun values => post_solution L S (lookup EX L values))) as Hloop.
  specialize (Hloop ltac:(intros state next [Hroot Hsound] Hstep; split;
    [eapply nested_step_rooted; eassumption|
      eapply nested_step_sound; eassumption])
    ltac:(intros state [Hroot Hsound] Hstep; eapply nested_finished_sound; eassumption)
    fuel (nested_start plan) ltac:(split; [reflexivity|apply nested_root_sound; exact Hcover])).
  unfold nested_run; fold plan.
  destruct (nested_loop (nested_step EX L plan st S) fuel (nested_start plan));
    intro Hresult; [discriminate|inversion Hresult; subst; exact Hloop].
Qed.

(** The fuel solver returns the computed assignment, or the sound everywhere-top fallback. *)
Definition nested_solve_fuel {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (HL : lattice_laws L) (T : top L) (st : strategy)
    (S : System.t X C A) (SS : System.static S) (fuel : positive) :
    {s : X -> A | post_solution L S s} :=
  match nested_run EX EC L st S SS fuel as result return
      nested_run EX EC L st S SS fuel = result -> {s : X -> A | post_solution L S s} with
  | Some values => fun Hresult =>
    exist _ (lookup EX L values) (nested_run_sound EX EC L HL st S SS fuel values Hresult)
  | None => fun _ => exist _ (fun _ => top_value T) (top_post_solution L S T)
  end eq_refl.

(** * A schedule-independent measure for effective evaluations *)

Definition nested_bad {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (values : assignment X A) (c : C) : bool :=
  let '(v, _, sides) := Query.run (System.rhs S c) (lookup EX L values) in
  negb (leb L v (lookup EX L values (System.target S c)) &&
    forallb (fun xa => leb L (snd xa) (lookup EX L values (fst xa))) sides).

Lemma nested_bad_spec {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (values : assignment X A) (c : C) :
  nested_bad EX L S values c = false <-> constraint_satisfied L S c (lookup EX L values).
Proof.
  unfold nested_bad, constraint_satisfied; rewrite run_spec.
  rewrite negb_false_iff, andb_true_iff, forallb_forall.
  split; intros [Hv Hs]; split; [exact Hv| |exact Hv|].
  - intros x a Hin; exact (Hs (x, a) Hin).
  - intros [x a] Hin; exact (Hs x a Hin).
Qed.

Lemma nested_updates_below {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (updates : list (X * A))
    (state : NestedState.t X C A) :
  (forall x a, In (x, a) updates -> leb L a (lookup EX L (NestedState.current state) x) = true) ->
  nested_updates EX L plan st updates state = state.
Proof.
  revert state; induction updates as [|[x a] updates IH]; intros state Hbelow; [reflexivity|].
  change (nested_updates EX L plan st updates (nested_update EX L plan st (x, a) state) = state).
  unfold nested_update; rewrite Hbelow by now left.
  apply IH; intros y b Hin; apply Hbelow; now right.
Qed.

(** Ghost queues are used only by the measure proof; the iterator executes no priority queue. *)
Lemma nested_updates_projection {X C A} (EX : encoding X) (EC : encoding C)
    (L : lattice A) (plan : NestedPlan.t X C) (st : strategy) (S : System.t X C A)
    (dep : dependencies S) (r : Map.t X (FinSet.t C)) (updates : list (X * A)) :
  forall (state : NestedState.t X C A) (q : PQueue.t C),
  fst (engine_updates EX EC L (nested_scheduler EX plan) st S dep r updates
    (NestedState.current state, q)) =
    NestedState.current (nested_updates EX L plan st updates state).
Proof.
  induction updates as [|[x a] updates IH]; intros state q; [reflexivity|].
  change (fst (engine_updates EX EC L (nested_scheduler EX plan) st S dep r updates
    (engine_update EX EC L (nested_scheduler EX plan) st S dep r (x, a)
      (NestedState.current state, q))) =
    NestedState.current (nested_updates EX L plan st updates
      (nested_update EX L plan st (x, a) state))).
  unfold engine_update, nested_update; cbn [fst snd].
  destruct (leb L a (lookup EX L (NestedState.current state) x)); [apply IH|].
  exact (IH (nested_mark EX plan x state
    (Map.set EX x (update_value L (nested_scheduler EX plan) st x
      (lookup EX L (NestedState.current state) x) a) (NestedState.current state))) _).
Qed.

Lemma nested_weight_remove {C} (EC : encoding C) (w : C -> nat) (bad : C -> bool)
    (cs : list C) (c : C) :
  In c cs -> bad c = true ->
  w c + total_sum w (filter (fun d => bad d && negb (Pos.eqb (encode EC c) (encode EC d))) cs)
    <= total_sum w (filter bad cs).
Proof.
  induction cs as [|d cs IH]; intros Hin Hbad; [contradiction|].
  cbn [filter]; destruct Hin as [Heq|Hin].
  - subst d; rewrite Hbad, Pos.eqb_refl; cbn [negb andb total_sum].
    assert (Hle : total_sum w
      (filter (fun d => bad d && negb (Pos.eqb (encode EC c) (encode EC d))) cs) <=
      total_sum w (filter bad cs)).
    { rewrite !total_sum_filter; apply total_sum_le; intros d Hd.
      destruct (bad d), (Pos.eqb (encode EC c) (encode EC d)); cbn; lia. }
    lia.
  - specialize (IH Hin Hbad).
    destruct (bad d), (Pos.eqb (encode EC c) (encode EC d)); cbn [andb negb total_sum]; lia.
Qed.

Section NestedEvaluationMeasure.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (plan : NestedPlan.t X C) (st : strategy)
  (S : System.t X C A) (SS : System.static S).
Let ix := index_system EX S SS.
Let sch := nested_scheduler EX plan.
Variables (tracked : X -> bool) (credit : X -> A -> nat) (weight : C -> nat).
Hypothesis Hprogress : forall x old a, In x (total_unknowns SS) -> leb L a old = false ->
  credit x (update_value L sch st x old a) <= credit x old /\
  (credit x (update_value L sch st x old a) = credit x old -> tracked x = false).
Hypothesis Hweight : forall c, In c (System.constraints S) ->
  total_sum weight (flat_map (readers_of EX ix)
    (filter (fun x => negb (tracked x)) (total_outputs SS c))) < weight c.

Definition nested_credit (values : assignment X A) : nat := total_credit EX L S SS credit values.
Definition nested_debt (values : assignment X A) : nat :=
  total_sum weight (filter (nested_bad EX L S values) (total_constraints EC S)).

Lemma nested_bad_support (c : C) (before after : assignment X A) (later : list C) :
  fun_leb L (lookup EX L before) (lookup EX L after) ->
  (forall x a, In (x, a) ((System.target S c,
    Query.eval (System.rhs S c) (lookup EX L before)) ::
      Query.sides (System.rhs S c) (lookup EX L before)) ->
    leb L a (lookup EX L after x) = true) ->
  (forall d, In d (System.constraints S) -> ~ In d later ->
    forall x, In x (Query.reads (System.rhs S d) (lookup EX L before)) ->
      lookup EX L after x = lookup EX L before x) ->
  incl (filter (nested_bad EX L S after) (total_constraints EC S))
    (filter (fun d => nested_bad EX L S before d &&
      negb (Pos.eqb (encode EC c) (encode EC d))) (total_constraints EC S) ++ later).
Proof.
  intros Hup Hbounds Hreads d Hin; apply filter_In in Hin; destruct Hin as [Hd Hbad_final].
  destruct (in_dec (fun a b =>
    match Pos.eq_dec (encode EC a) (encode EC b) with
    | left Heq => left (encode_injective EC a b Heq)
    | right Hne => right (fun Heq => Hne (f_equal (encode EC) Heq))
    end) d later) as [Hlater|Hnot]; [apply in_or_app; now right|].
  assert (Hsystem : In d (System.constraints S)) by now apply total_constraints_spec in Hd.
  assert (Hdifferent : c <> d).
  { intro Heq; subst d.
    destruct (query_determined (System.rhs S c) (lookup EX L before) (lookup EX L after))
      as [Hv [_ Hs]].
    - intros x Hx; symmetry; exact (Hreads c Hsystem Hnot x Hx).
    - assert (Hgood : nested_bad EX L S after c = false).
      { apply nested_bad_spec; split; [rewrite <- Hv; apply Hbounds; now left|].
        intros x a Ha; rewrite <- Hs in Ha; apply Hbounds; now right. }
      congruence. }
  assert (Hbad_old : nested_bad EX L S before d = true).
  { destruct (nested_bad EX L S before d) eqn:Hold; [reflexivity|].
    apply nested_bad_spec in Hold.
    destruct (constraint_satisfied_transport L S HL d _ _ Hup
      (Hreads d Hsystem Hnot) Hold) as [Hgood _].
    apply nested_bad_spec in Hgood; congruence. }
  apply in_or_app; left; apply filter_In; split; [exact Hd|].
  apply andb_true_iff; split; [exact Hbad_old|apply negb_true_iff, Pos.eqb_neq].
  intro Heq; apply Hdifferent, (encode_injective EC); exact Heq.
Qed.

Lemma nested_evaluation_debt (c : C) (before after : assignment X A) (q : PQueue.t C) :
  let ups := (System.target S c, Query.eval (System.rhs S c) (lookup EX L before)) ::
    Query.sides (System.rhs S c) (lookup EX L before) in
  engine_updates EX EC L sch st S (Declared SS ix) Map.empty ups (before, PQueue.empty) =
    (after, q) ->
  (forall d, total_present EC q d = true -> total_present EC PQueue.empty d = true \/
    exists x a, In (x, a) ups /\ In d (readers_of EX ix x) /\
      (nested_credit after = nested_credit before -> tracked x = false)) ->
  nested_credit after = nested_credit before -> nested_bad EX L S before c = true ->
  In c (System.constraints S) -> nested_debt after < nested_debt before.
Proof.
  cbn zeta; intros Hupdates Hsupport Hequal Hbad Hc.
  destruct (engine_updates_properties EX EC L sch st S (Declared SS ix) HL Map.empty _
    before after PQueue.empty q (PQueue.wf_empty EC) Hupdates)
    as [_ [Hup [Hbounds [_ Hagree]]]].
  set (later := flat_map (readers_of EX ix)
    (filter (fun x => negb (tracked x)) (total_outputs SS c))).
  assert (Hpending : forall d, PQueue.priority EC d q <> None -> In d later).
  { intros d Hd; apply total_present_spec in Hd; destruct (Hsupport d Hd)
      as [Hempty|[x [a [Hin [Hread Htrack]]]]].
    - unfold total_present in Hempty; rewrite PQueue.priority_empty in Hempty; discriminate.
    - apply in_flat_map; exists x; split; [|exact Hread].
      apply filter_In; split; [eapply total_run_outputs; exact Hin|].
      apply negb_true_iff, Htrack; exact Hequal. }
  assert (Hreads : forall d, In d (System.constraints S) -> ~ In d later ->
    forall x, In x (Query.reads (System.rhs S d) (lookup EX L before)) ->
      lookup EX L after x = lookup EX L before x).
  { intros d Hd Hnot x Hread; eapply (Hagree d x).
    - change (In d (readers_of EX ix x)); apply (readers_agree (index_system_laws EX S SS));
        split; [exact Hd|].
      exact (System.reads_within SS d (lookup EX L before) x Hread).
    - destruct (PQueue.priority EC d q) eqn:Hget; [exfalso; apply Hnot, Hpending; congruence|].
      reflexivity. }
  pose proof (nested_bad_support c before after later Hup Hbounds Hreads) as Hincl.
  pose proof (total_sum_incl weight _ _
    (NoDup_filter _ (total_constraints_nodup EC S)) Hincl) as Hsum.
  rewrite total_sum_app in Hsum.
  pose proof (nested_weight_remove EC weight (nested_bad EX L S before)
    (total_constraints EC S) c (proj2 (total_constraints_spec EC S c) Hc) Hbad) as Hremove.
  specialize (Hweight c Hc); unfold nested_debt; fold later in Hweight; lia.
Qed.

Lemma nested_evaluate_measure (c : C) (state : NestedState.t X C A) :
  In c (System.constraints S) ->
  let updates :=
    (let '(v, _, sides) := Query.run (System.rhs S c) (lookup EX L (NestedState.current state))
      in (System.target S c, v) :: sides) in
  let next := nested_updates EX L plan st updates state in
  next = state \/
  nested_credit (NestedState.current next) < nested_credit (NestedState.current state) \/
  (nested_credit (NestedState.current next) = nested_credit (NestedState.current state) /\
    nested_debt (NestedState.current next) < nested_debt (NestedState.current state)).
Proof.
  intro Hc; rewrite run_spec; cbn zeta.
  set (ups := (System.target S c,
    Query.eval (System.rhs S c) (lookup EX L (NestedState.current state))) ::
      Query.sides (System.rhs S c) (lookup EX L (NestedState.current state))).
  destruct (nested_bad EX L S (NestedState.current state) c) eqn:Hbad.
  2: { left; apply nested_updates_below.
    apply nested_bad_spec in Hbad; destruct Hbad as [Hv Hs].
    intros x a [Heq|Hin]; [inversion Heq; subst; exact Hv|apply Hs; exact Hin]. }
  set (mq := engine_updates EX EC L sch st S (Declared SS ix) Map.empty ups
    (NestedState.current state, PQueue.empty)).
  destruct mq as [values q] eqn:Hmq.
  assert (Hupdates : engine_updates EX EC L sch st S (Declared SS ix) Map.empty ups
    (NestedState.current state, PQueue.empty) = (values, q)) by exact Hmq.
  assert (Hprojection : values = NestedState.current (nested_updates EX L plan st ups state)).
  { pose proof (nested_updates_projection EX EC L plan st S (Declared SS ix) Map.empty
      ups state PQueue.empty) as Hproj; fold sch in Hproj; rewrite Hupdates in Hproj;
      exact Hproj. }
  assert (Hr : total_recorded_valid EX EC S SS Map.empty).
  { split; [apply recorded_empty_wf|].
    intros x d Hin; unfold recorded_at in Hin; rewrite Map.get_empty, FinSet.mem_empty in Hin;
      discriminate. }
  assert (Hout : forall x a, In (x, a) ups -> In x (total_unknowns SS)).
  { apply (total_run_unknowns SS c _ Hc). }
  destruct (total_updates_measure EX EC L sch st S SS ix (Declared SS ix)
    (fun r Hr x d Hd => Hd) tracked credit Hprogress Map.empty ups
    (NestedState.current state) values PQueue.empty q Hr Hout (PQueue.wf_empty EC) Hupdates)
    as [Hwf [Hcredit Hsupport]].
  change (nested_credit values <= nested_credit (NestedState.current state)) in Hcredit.
  rewrite <- Hprojection.
  destruct (Nat.lt_ge_cases (nested_credit values) (nested_credit (NestedState.current state)))
    as [Hless|Hmore]; [now right; left|].
  assert (Hequal : nested_credit values = nested_credit (NestedState.current state)) by lia.
  right; right; split; [exact Hequal|].
  exact (nested_evaluation_debt c (NestedState.current state) values q Hupdates Hsupport
    Hequal Hbad Hc).
Qed.

End NestedEvaluationMeasure.

(** * Finite traversal between effective evaluations *)

Fixpoint nested_cost {X C} (EX : encoding X) (plan : NestedPlan.t X C)
    (code : nested_code X) : nat :=
  match code with
  | NestedEnd => 0
  | NestedVisit x rest => 1 + length (index_get EX (NestedPlan.targets plan) x) +
    nested_cost EX plan rest
  | NestedComponent h body rest => 3 + length (index_get EX (NestedPlan.targets plan) h) +
    nested_cost EX plan body + nested_cost EX plan rest
  end.

Definition nested_frame_valid {X C} (EX : encoding X) (plan : NestedPlan.t X C)
    (frame : NestedFrame.t X) : Prop :=
  nested_cost EX plan (NestedFrame.remaining frame) <= nested_cost EX plan (NestedPlan.root plan) /\
  match NestedFrame.restart frame with
  | None => True
  | Some (_, pass) => nested_cost EX plan pass <= nested_cost EX plan (NestedPlan.root plan)
  end.

Definition nested_control_valid {X C A} (EX : encoding X) (plan : NestedPlan.t X C)
    (S : System.t X C A) (state : NestedState.t X C A) : Prop :=
  Forall (nested_frame_valid EX plan) (NestedState.frames state) /\
  Forall (fun c => In c (System.constraints S)) (NestedState.ready state) /\
  FinSet.wf EX (NestedState.dirty state) /\ nested_rooted (NestedState.frames state).

Definition nested_admin {X C A} (EX : encoding X) (plan : NestedPlan.t X C)
    (state : NestedState.t X C A) : nat :=
  length (NestedState.ready state) +
  total_sum (fun frame => 1 + nested_cost EX plan (NestedFrame.remaining frame))
    (NestedState.frames state) +
  (1 + nested_cost EX plan (NestedPlan.root plan)) * FinSet.size (NestedState.dirty state) +
  if NestedState.changed state then 1 + nested_cost EX plan (NestedPlan.root plan) else 0.

Lemma nested_remove_size {X} (EX : encoding X) (h : X) (dirty : FinSet.t X) :
  FinSet.wf EX dirty ->
  FinSet.size (FinSet.remove EX h dirty) <= FinSet.size dirty /\
  (FinSet.mem EX h dirty = true ->
    FinSet.size (FinSet.remove EX h dirty) < FinSet.size dirty).
Proof.
  intro Hwf.
  assert (Hremove : FinSet.wf EX (FinSet.remove EX h dirty)) by now apply Map.wf_remove.
  assert (Hsubset : FinSet.subset EX (FinSet.remove EX h dirty) dirty = true).
  { apply (FinSet.subset_spec EX); [exact Hremove|].
    intros x Hx; apply FinSet.mem_remove in Hx; exact (proj2 Hx). }
  split; [apply (FinSet.size_subset EX); assumption|].
  intro Hmem; apply (FinSet.size_lt EX); try assumption.
  destruct (FinSet.subset EX dirty (FinSet.remove EX h dirty)) eqn:Hback; [|reflexivity].
  pose proof (proj1 (FinSet.subset_spec EX dirty (FinSet.remove EX h dirty) Hwf)
    Hback h Hmem) as Hbad.
  apply FinSet.mem_remove in Hbad; tauto.
Qed.

Lemma nested_updates_control {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (S : System.t X C A)
    (updates : list (X * A)) (state : NestedState.t X C A) :
  nested_control_valid EX plan S state ->
  nested_control_valid EX plan S (nested_updates EX L plan st updates state).
Proof.
  revert state; induction updates as [|[x a] updates IH]; intros state Hvalid; [exact Hvalid|].
  change (nested_control_valid EX plan S (nested_updates EX L plan st updates
    (nested_update EX L plan st (x, a) state))).
  apply IH; unfold nested_update; destruct (leb L a _); [exact Hvalid|].
  destruct Hvalid as [Hframes [Hready [Hdirty Hroot]]]; unfold nested_control_valid, nested_mark;
    cbn; split; [exact Hframes|]; split; [exact Hready|]; split; [|exact Hroot].
  apply FinSet.wf_fold_add; exact Hdirty.
Qed.

Section NestedControl.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (plan : NestedPlan.t X C)
  (st : strategy) (S : System.t X C A).
Hypothesis Htargets : forall x, incl (index_get EX (NestedPlan.targets plan) x)
  (System.constraints S).

Lemma nested_control_start : nested_control_valid EX plan S (@nested_start X C A plan).
Proof.
  split.
  - constructor; [split; [apply Nat.le_refl|exact I]|constructor].
  - split; [constructor|]; split; [apply Map.wf_empty|reflexivity].
Qed.

Lemma nested_step_control (state next : NestedState.t X C A) :
  nested_control_valid EX plan S state -> nested_step EX L plan st S state = Some next ->
  nested_control_valid EX plan S next.
Proof.
  intros Hvalid Hstep.
  assert (Hroot := nested_step_rooted EX L plan st S state next
    (proj2 (proj2 (proj2 Hvalid))) Hstep).
  destruct Hvalid as [Hframes [Hready [Hdirty Hroot_old]]].
  unfold nested_step in Hstep.
  destruct (NestedState.ready state) as [|c rest] eqn:Hready_state.
  2: { rewrite run_spec in Hstep.
    apply (f_equal (fun result =>
      match result with
      | Some next => nested_control_valid EX plan S next
      | None => False
      end)) in Hstep.
    rewrite <- Hstep; apply nested_updates_control.
    split; [exact Hframes|]; split; [inversion Hready; assumption|]; now split. }
  destruct (NestedState.frames state) as [|[code restart] frames] eqn:Hframes_state;
    [discriminate|].
  inversion Hframes as [|frame tail [Hcode Hrestart] Htail]; subst frame tail.
  cbn [NestedFrame.remaining NestedFrame.restart] in Hstep, Hcode, Hrestart.
  destruct code as [|x rest|h body rest].
  - destruct restart as [[h pass]|].
    + destruct (FinSet.mem EX h (NestedState.dirty state)); inversion Hstep; subst next;
        split; [constructor; [split; [exact Hrestart|exact Hrestart]|exact Htail]|
          |exact Htail|]; split; [constructor| |constructor|]; split;
        try (apply Map.wf_remove; exact Hdirty); assumption.
    + destruct (NestedState.changed state); [|discriminate]; inversion Hstep; subst next.
      split; [constructor; [split; [apply Nat.le_refl|exact I]|constructor]|].
      split; [constructor|]; split; assumption.
  - inversion Hstep; subst next; split.
    + constructor; [split; [cbn [NestedFrame.remaining nested_cost];
        cbn [nested_cost] in Hcode; lia|exact Hrestart]|exact Htail].
    + split; [apply Forall_forall; intros c Hc; apply Htargets in Hc; exact Hc|].
      split; assumption.
  - inversion Hstep; subst next; split.
    + cbn [nested_cost] in Hcode.
      constructor; [split; cbn [NestedFrame.remaining nested_cost NestedFrame.restart]; lia|].
      constructor; [split; [cbn [NestedFrame.remaining]; lia|exact Hrestart]|exact Htail].
    + split; [constructor|]; split; [apply Map.wf_remove; exact Hdirty|exact Hroot].
Qed.

(** Every frame-only transition strictly reduces finite traversal and restart credit. *)
Lemma nested_admin_step (state next : NestedState.t X C A) :
  nested_control_valid EX plan S state -> NestedState.ready state = [] ->
  nested_step EX L plan st S state = Some next ->
  NestedState.current next = NestedState.current state /\
    nested_admin EX plan next < nested_admin EX plan state.
Proof.
  intros [Hframes [_ [Hdirty Hroot]]] Hready Hstep.
  unfold nested_step in Hstep; rewrite Hready in Hstep.
  destruct (NestedState.frames state) as [|[code restart] frames] eqn:Hframes_state;
    [discriminate|].
  inversion Hframes as [|frame tail [Hcode Hrestart] Htail]; subst frame tail.
  cbn [NestedFrame.remaining NestedFrame.restart] in Hstep, Hcode, Hrestart.
  destruct code as [|x rest|h body rest].
  - destruct restart as [[h pass]|].
    + destruct (FinSet.mem EX h (NestedState.dirty state)) eqn:Hmem;
        inversion Hstep; subst next; split; [reflexivity| |reflexivity|];
        unfold nested_admin; cbn [NestedState.current NestedState.ready NestedState.frames
          NestedState.dirty NestedState.changed total_sum NestedFrame.remaining nested_cost];
        rewrite Hready, Hframes_state; cbn [length total_sum NestedFrame.remaining nested_cost].
      * pose proof (proj2 (nested_remove_size EX h _ Hdirty) Hmem); nia.
      * nia.
    + cbn [nested_rooted NestedFrame.restart] in Hroot; subst frames.
      destruct (NestedState.changed state) eqn:Hchanged; [|discriminate].
      inversion Hstep; subst next; split; [reflexivity|].
      unfold nested_admin; rewrite Hready, Hframes_state, Hchanged;
        cbn [NestedState.ready NestedState.frames NestedState.dirty NestedState.changed
          total_sum length NestedFrame.remaining nested_cost]; nia.
  - inversion Hstep; subst next; split; [reflexivity|].
    unfold nested_admin; rewrite Hready, Hframes_state;
      cbn [NestedState.ready NestedState.frames NestedState.dirty NestedState.changed
        total_sum length NestedFrame.remaining nested_cost]; nia.
  - inversion Hstep; subst next; split; [reflexivity|].
    pose proof (proj1 (nested_remove_size EX h _ Hdirty)).
    unfold nested_admin; rewrite Hready, Hframes_state;
      cbn [NestedState.ready NestedState.frames NestedState.dirty NestedState.changed
        total_sum length NestedFrame.remaining nested_cost]; nia.
Qed.

End NestedControl.

(** * Accessibility and binary-fuel adequacy *)

Section NestedAccessibility.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (plan : NestedPlan.t X C) (st : strategy)
  (S : System.t X C A) (SS : System.static S).
Variables (tracked : X -> bool) (credit : X -> A -> nat) (weight : C -> nat).
Hypothesis Hprogress : forall x old a, In x (total_unknowns SS) -> leb L a old = false ->
  credit x (update_value L (nested_scheduler EX plan) st x old a) <= credit x old /\
  (credit x (update_value L (nested_scheduler EX plan) st x old a) = credit x old ->
    tracked x = false).
Hypothesis Hweight : forall c, In c (System.constraints S) ->
  total_sum weight (flat_map (readers_of EX (index_system EX S SS))
    (filter (fun x => negb (tracked x)) (total_outputs SS c))) < weight c.
Hypothesis Htargets : forall x, incl (index_get EX (NestedPlan.targets plan) x)
  (System.constraints S).
Let rank_state (state : NestedState.t X C A) :=
  nested_credit EX L S SS credit (NestedState.current state).
Let debt_state (state : NestedState.t X C A) :=
  nested_debt EX EC L S weight (NestedState.current state).

Lemma nested_step_measure (state next : NestedState.t X C A) :
  nested_control_valid EX plan S state -> nested_step EX L plan st S state = Some next ->
  rank_state next < rank_state state \/
  (rank_state next = rank_state state /\
    (debt_state next < debt_state state \/
      (debt_state next = debt_state state /\
        nested_admin EX plan next < nested_admin EX plan state))).
Proof.
  intros Hvalid Hstep.
  destruct (NestedState.ready state) as [|c rest] eqn:Hready.
  - destruct (nested_admin_step EX L plan st S state next Hvalid Hready Hstep) as [Heq Hless].
    right; unfold rank_state, debt_state; rewrite Heq; repeat split; auto.
  - assert (Hc : In c (System.constraints S)).
    { destruct Hvalid as [_ [Hcs _]]; rewrite Hready in Hcs; inversion Hcs; assumption. }
    set (base := NestedState.Make (NestedState.current state) rest (NestedState.frames state)
      (NestedState.dirty state) (NestedState.changed state)).
    unfold nested_step in Hstep; rewrite Hready, run_spec in Hstep.
    pose proof (nested_evaluate_measure EX EC L HL plan st S SS tracked credit weight
      Hprogress Hweight c base Hc) as Hmeasure.
    rewrite run_spec in Hmeasure; cbn zeta in Hmeasure.
    assert (Hnext : nested_updates EX L plan st
      ((System.target S c, Query.eval (System.rhs S c) (lookup EX L (NestedState.current base))) ::
        Query.sides (System.rhs S c) (lookup EX L (NestedState.current base))) base = next).
    { injection Hstep; exact (fun H => H). }
    rewrite Hnext in Hmeasure; destruct Hmeasure as [Heq|[Hrank|[Hrank Hdebt]]].
    + subst next; right; split; [reflexivity|right; split; [reflexivity|]].
      unfold nested_admin, base; cbn [NestedState.ready NestedState.frames NestedState.dirty
        NestedState.changed]; rewrite Hready; cbn [length]; lia.
    + left; exact Hrank.
    + right; split; [exact Hrank|now left].
Qed.

Lemma nested_valid_acc (state : NestedState.t X C A) :
  nested_control_valid EX plan S state ->
  Acc (fun next state => nested_step EX L plan st S state = Some next) state.
Proof.
  assert (Hacc : forall n d a state, rank_state state = n -> debt_state state = d ->
    nested_admin EX plan state = a -> nested_control_valid EX plan S state ->
    Acc (fun next state => nested_step EX L plan st S state = Some next) state).
  { intro n; induction n as [n IHn] using lt_wf_ind.
    intro d; induction d as [d IHd] using lt_wf_ind.
    intro a; induction a as [a IHa] using lt_wf_ind.
    intros current Hrank Hdebt Hadmin Hvalid; constructor; intros next Hstep.
    pose proof (nested_step_control EX L plan st S Htargets current next Hvalid Hstep) as Hnext.
    destruct (nested_step_measure current next Hvalid Hstep)
      as [Hrank_less|[Hrank_same [Hdebt_less|[Hdebt_same Hadmin_less]]]].
    - eapply (IHn (rank_state next)); [lia|reflexivity|reflexivity|reflexivity|exact Hnext].
    - eapply (IHd (debt_state next)); [lia|lia|reflexivity|reflexivity|exact Hnext].
    - eapply (IHa (nested_admin EX plan next)); [lia|lia|lia|reflexivity|exact Hnext]. }
  apply (Hacc (rank_state state) (debt_state state) (nested_admin EX plan state) state);
    reflexivity || assumption.
Qed.

End NestedAccessibility.

Lemma nested_iter_done {X C A}
    (step : NestedState.t X C A -> option (NestedState.t X C A))
    (n : nat) (values : assignment X A) :
  Nat.iter n (nested_tick step) (inr values) = inr values.
Proof.
  induction n; [reflexivity|rewrite Nat.iter_succ, IHn; reflexivity].
Qed.

(** The proof-only unary iteration counts exactly the transitions of the binary runner. *)
Lemma nested_loop_iter {X C A}
    (step : NestedState.t X C A -> option (NestedState.t X C A)) :
  forall fuel state, nested_loop step fuel state =
    Nat.iter (Pos.to_nat fuel) (nested_tick step) (inl state).
Proof.
  intro fuel; induction fuel as [fuel IH|fuel IH|]; intro state.
  - cbn [nested_loop]; rewrite Pos2Nat.inj_xI.
    replace (S (2 * Pos.to_nat fuel)) with (S (Pos.to_nat fuel + Pos.to_nat fuel)) by lia.
    rewrite Nat.iter_succ, Nat.iter_add, <- IH.
    destruct (nested_loop step fuel state) as [first|values];
      [now rewrite IH|now rewrite nested_iter_done].
  - cbn [nested_loop]; rewrite Pos2Nat.inj_xO.
    replace (2 * Pos.to_nat fuel) with (Pos.to_nat fuel + Pos.to_nat fuel) by lia.
    rewrite Nat.iter_add, <- IH.
    destruct (nested_loop step fuel state) as [first|values];
      [apply IH|symmetry; apply nested_iter_done].
  - reflexivity.
Qed.

Lemma nested_acc_finishes {X C A}
    (step : NestedState.t X C A -> option (NestedState.t X C A))
    (state : NestedState.t X C A) :
  Acc (fun next state => step state = Some next) state ->
  exists n values, Nat.iter n (nested_tick step) (inl state) = inr values.
Proof.
  intro Hacc; induction Hacc as [state Hacc IH].
  destruct (step state) as [next|] eqn:Hstep.
  - destruct (IH next eq_refl) as [n [values Hfinish]].
    exists (S n), values; rewrite Nat.iter_succ_r.
    replace (nested_tick step (inl state)) with
      (inl next : NestedState.t X C A + assignment X A) by
      (unfold nested_tick; rewrite Hstep; reflexivity).
    exact Hfinish.
  - exists 1, (NestedState.current state).
    change (nested_tick step (inl state) = inr (NestedState.current state)).
    cbn [nested_tick]; now rewrite Hstep.
Qed.

Lemma nested_acc_fuel {X C A}
    (step : NestedState.t X C A -> option (NestedState.t X C A))
    (state : NestedState.t X C A) :
  Acc (fun next state => step state = Some next) state ->
  exists fuel values, nested_loop step fuel state = inr values.
Proof.
  intro Hacc; destruct (nested_acc_finishes step state Hacc) as [n [values Hfinish]].
  exists (Pos.of_succ_nat n), values; rewrite nested_loop_iter, SuccNat2Pos.id_succ.
  rewrite Nat.iter_succ, Hfinish; reflexivity.
Qed.

(** Finite height, or widening ranks on a cycle cut, suffice for the actual nested machine. *)
Theorem nested_run_eventually {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S) :
  terminates L SS (wto_scheduler EX S SS) st ->
  exists fuel m, nested_run EX EC L st S SS fuel = Some m.
Proof.
  intro HT.
  set (plan := nested_prepare EX S SS).
  assert (Htargets : forall x, incl (index_get EX (NestedPlan.targets plan) x)
    (System.constraints S)).
  { intros x c Hc; change (In c (index_get EX (nested_targets EX S) x)) in Hc.
    rewrite nested_targets_agree in Hc; apply filter_In in Hc; exact (proj1 Hc). }
  assert (Hacc : Acc (fun next state => nested_step EX L plan st S state = Some next)
    (nested_start plan)).
  { destruct st.
    - destruct HT as [Hheight].
      eapply (nested_valid_acc EX EC L HL plan Joining S SS (fun _ => true)
        (fun _ a => bound Hheight - rank Hheight a) (fun _ => 1)).
      + intros x old a Hx Hbelow; apply (total_height_progress L HL Hheight); exact Hbelow.
      + intros c Hc; apply total_join_weight.
      + exact Htargets.
      + apply nested_control_start.
    - destruct HT as [[W] Hcut].
      set (points := widening_point (wto_scheduler EX S SS)) in *.
      eapply (nested_valid_acc EX EC L HL plan Widening S SS points
        (fun x a => if points x then wrank W a else 0)
        (total_constraint_weight EX S SS (index_system EX S SS) points
          (index_system_laws EX S SS) Hcut)).
      + intros x old a Hx Hbelow; unfold update_value, nested_scheduler.
        cbn [widening_point].
        change (FinSet.mem EX x (NestedPlan.heads plan)) with
          (FinSet.mem EX x (NestedPlan.heads (nested_prepare EX S SS))).
        rewrite nested_prepared_heads; fold points.
        destruct (points x); cbn; [pose proof (widen_rank_progress W old a Hbelow); lia|auto].
      + intros c Hc; apply total_constraint_weight_dominates.
      + exact Htargets.
      + apply nested_control_start. }
  destruct (nested_acc_fuel _ _ Hacc) as [fuel [values Hfinish]].
  exists fuel, values; unfold nested_run; fold plan; rewrite Hfinish; reflexivity.
Qed.

(** * Component membership and side-effect invalidation *)

(** Prepared membership is exactly the original WTO annotation, including a head itself. *)
Lemma nested_prepared_members {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (x h : X) :
  In h (index_get EX (NestedPlan.members (nested_prepare EX S SS)) x) <->
  exists stack, In (x, stack)
    (annotate [] (wto_total (prepare EX (dependency_graph EX S SS)))) /\ In h stack.
Proof.
  change (NestedPlan.members (nested_prepare EX S SS)) with
    (nested_members EX (NestedPlan.root (nested_prepare EX S SS))).
  rewrite nested_members_agree by apply nested_prepared_covers.
  rewrite <- nested_prepared_tokens.
  pose proof (nested_rows_tokens (NestedPlan.root (nested_prepare EX S SS)) [] []) as Hrows.
  rewrite app_nil_r in Hrows; cbn [annotate] in Hrows; rewrite app_nil_r in Hrows.
  now rewrite Hrows.
Qed.

Lemma nested_update_marks {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (state : NestedState.t X C A)
    (x h : X) (a : A) :
  leb L a (lookup EX L (NestedState.current state) x) = false ->
  In h (index_get EX (NestedPlan.members plan) x) ->
  FinSet.mem EX h (NestedState.dirty (nested_update EX L plan st (x, a) state)) = true.
Proof.
  intros Hbelow Hin; unfold nested_update; rewrite Hbelow.
  cbn [nested_mark NestedState.dirty]; apply FinSet.mem_fold_add; now left.
Qed.

(** No later side output in the same evaluation can erase an earlier dirty component. *)
Lemma nested_updates_dirty {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (updates : list (X * A))
    (state : NestedState.t X C A) (h : X) :
  FinSet.mem EX h (NestedState.dirty state) = true ->
  FinSet.mem EX h (NestedState.dirty (nested_updates EX L plan st updates state)) = true.
Proof.
  revert state; induction updates as [|[x a] updates IH]; intros state Hdirty; [exact Hdirty|].
  change (FinSet.mem EX h (NestedState.dirty (nested_updates EX L plan st updates
    (nested_update EX L plan st (x, a) state))) = true).
  apply IH; unfold nested_update; destruct (leb L a _); [exact Hdirty|].
  cbn [nested_mark NestedState.dirty]; apply FinSet.mem_fold_add; now right.
Qed.

(** * Coverage of a completed outer traversal *)

Lemma nested_updates_ready {X C A} (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) (st : strategy) (updates : list (X * A))
    (state : NestedState.t X C A) :
  NestedState.ready (nested_updates EX L plan st updates state) = NestedState.ready state.
Proof.
  revert state; induction updates as [|[x a] updates IH]; intro state; [reflexivity|].
  change (NestedState.ready (nested_updates EX L plan st updates
    (nested_update EX L plan st (x, a) state)) = NestedState.ready state).
  rewrite IH; unfold nested_update; destruct (leb L a _); reflexivity.
Qed.

Section NestedCoverage.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (plan : NestedPlan.t X C)
  (st : strategy) (S : System.t X C A).
Hypothesis Hcover : forall c, In c (System.constraints S) ->
  exists x, In x (nested_vertices (NestedPlan.root plan)) /\
    In c (index_get EX (NestedPlan.targets plan) x).

Lemma nested_pending_step (state next : NestedState.t X C A) (c : C) :
  In c (System.constraints S) -> nested_step EX L plan st S state = Some next ->
  nested_pending EX plan state c ->
  (exists rest, NestedState.ready state = c :: rest) \/ nested_pending EX plan next c.
Proof.
  intros Hc Hstep Hpending; unfold nested_step in Hstep.
  destruct (NestedState.ready state) as [|d rest] eqn:Hready.
  2: { rewrite run_spec in Hstep.
    assert (Hnext : nested_updates EX L plan st
      ((System.target S d, Query.eval (System.rhs S d) (lookup EX L (NestedState.current state))) ::
        Query.sides (System.rhs S d) (lookup EX L (NestedState.current state)))
      (NestedState.Make (NestedState.current state) rest (NestedState.frames state)
        (NestedState.dirty state) (NestedState.changed state)) = next).
    { injection Hstep; trivial. }
    unfold nested_pending in Hpending; rewrite Hready in Hpending.
    destruct Hpending as [[Heq|Hin]|Hpending]; [subst d; left; eauto|right; left|right; right].
    - rewrite <- Hnext, nested_updates_ready; exact Hin.
    - rewrite <- Hnext, nested_updates_frames; exact Hpending. }
  destruct (NestedState.frames state) as [|[code restart] frames] eqn:Hframes;
    [discriminate|].
  destruct Hpending as [Hin|[frame [x [Hframe [Hx Hin]]]]];
    [rewrite Hready in Hin; contradiction|].
  rewrite Hframes in Hframe.
  cbn [NestedFrame.remaining NestedFrame.restart] in Hstep.
  destruct code as [|y rest|h body rest].
  - destruct restart as [[h pass]|].
    + destruct (FinSet.mem EX h (NestedState.dirty state)); inversion Hstep; subst next;
        destruct Hframe as [Heq|Hframe]; [subst frame; contradiction| |subst frame; contradiction|];
        right; right; exists frame, x; cbn; auto.
    + destruct (NestedState.changed state); [|discriminate]; inversion Hstep; subst next.
      right; right; destruct (Hcover c Hc) as [y [Hy Htarget]].
      exists (NestedFrame.Make (NestedPlan.root plan) None), y; cbn; auto.
  - inversion Hstep; subst next; right; destruct Hframe as [Heq|Hframe].
    + subst frame; cbn in Hx; destruct Hx as [Heq|Hx].
      * subst y; left; exact Hin.
      * right; exists (NestedFrame.Make rest restart), x; cbn; auto.
    + right; exists frame, x; cbn; auto.
  - inversion Hstep; subst next; right; right; destruct Hframe as [Heq|Hframe].
    + subst frame; cbn in Hx; destruct Hx as [Heq|Hx].
      * subst x; exists (NestedFrame.Make (NestedVisit h body) (Some (h, NestedVisit h body))), h;
          cbn; auto.
      * apply in_app_or in Hx; destruct Hx as [Hx|Hx].
        -- exists (NestedFrame.Make (NestedVisit h body) (Some (h, NestedVisit h body))), x;
             cbn; auto.
        -- exists (NestedFrame.Make rest restart), x; cbn; auto.
    + exists frame, x; cbn; auto.
Qed.

(** A trace records exactly the ready constraint evaluated by each transition. *)
Inductive nested_trace : NestedState.t X C A -> list C -> NestedState.t X C A -> Prop :=
  | NestedTraceRefl : forall state, nested_trace state [] state
  | NestedTraceStep : forall state next trace final,
      nested_step EX L plan st S state = Some next -> nested_trace next trace final ->
      nested_trace state
        (match NestedState.ready state with [] => trace | c :: _ => c :: trace end) final.

Lemma nested_trace_pending (state final : NestedState.t X C A) (trace : list C) :
  nested_trace state trace final -> forall c, In c (System.constraints S) ->
  nested_pending EX plan state c -> In c trace \/ nested_pending EX plan final c.
Proof.
  intro Htrace; induction Htrace as [state|state next trace final Hstep Htrace IH];
    intros c Hc Hpending; [now right|].
  destruct (nested_pending_step state next c Hc Hstep Hpending) as [[rest Hready]|Hnext].
  - rewrite Hready; left; now left.
  - destruct (IH c Hc Hnext) as [Hin|Hin]; [left|now right].
    destruct (NestedState.ready state); cbn; auto.
Qed.

(** Every constraint is evaluated in an outer pass, including no-read side producers. *)
Lemma nested_outer_pass_covers (values : assignment X A) (dirty : FinSet.t X)
    (trace : list C) (final : NestedState.t X C A) :
  nested_trace (NestedState.Make values [] [NestedFrame.Make (NestedPlan.root plan) None]
    dirty false) trace final ->
  NestedState.ready final = [] ->
  NestedState.frames final = [NestedFrame.Make NestedEnd None] ->
  incl (System.constraints S) trace.
Proof.
  intros Htrace Hready Hframes c Hc.
  assert (Hpending : nested_pending EX plan
    (NestedState.Make values [] [NestedFrame.Make (NestedPlan.root plan) None] dirty false) c).
  { right; destruct (Hcover c Hc) as [x [Hx Hin]].
    exists (NestedFrame.Make (NestedPlan.root plan) None), x; cbn; auto. }
  destruct (nested_trace_pending _ _ _ Htrace c Hc Hpending) as [Hin|[Hin|Hahead]];
    [exact Hin|rewrite Hready in Hin; contradiction|].
  destruct Hahead as [frame [x [Hframe [Hx Hin]]]].
  rewrite Hframes in Hframe; destruct Hframe as [Heq|Hbad];
    [subst frame; contradiction|contradiction].
Qed.

End NestedCoverage.
