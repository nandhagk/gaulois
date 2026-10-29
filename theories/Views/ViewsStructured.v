(** * Graphs and analyses of structured skeletons

    Slot keys identify control edges without storing client operations in graph identities.
    For example, a conditional jump has distinct taken and skipped edge slots.
    Builds on: ViewsSkeleton, ViewsGraph, ViewsForward and ViewsAgreement. *)

From Stdlib Require Import List Bool Arith Lia PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCycles.
From Gaulois.Views Require Import
  ViewsSemantics ViewsGraph ViewsForward ViewsAgreement ViewsSkeleton.
Import List.ListNotations Skeleton.

(** Points distinguish entering a statement from completing it. *)
Inductive skel_point : Type :=
  | PEntry (p : position)
  | PExit (p : position).

(** Entry and exit codes use the tags of the position sum encoding. *)
Definition skel_point_encoding : encoding skel_point.
Proof.
  refine (Encoding _ (fun v => encode (sum_encoding position_encoding position_encoding)
    (match v with
    | PEntry p => inl p
    | PExit p => inr p
    end)) _).
  intros [] [] Hcode; apply (encode_injective (sum_encoding _ _)) in Hcode;
    inversion Hcode; reflexivity.
Defined.

(** Actions describe the client store effects and branch observations of an edge. *)
Inductive action (A G : Type) : Type :=
  | AAtom (a : A)
  | AGuard (g : G) (b : bool)
  | AIndexIs (g : G) (i : nat)
  | AIndexAtLeast (g : G) (len : nat)
  | AJump (p : position) (n : nat).

Arguments AAtom {A G}.
Arguments AGuard {A G}.
Arguments AIndexIs {A G}.
Arguments AIndexAtLeast {A G}.
Arguments AJump {A G}.

(** Edges contain their source and their slot among outgoing alternatives. *)
Record skel_edge (A G : Type) : Type := SkelEdge {
  from : skel_point;
  slot : nat
}.

Arguments SkelEdge {A G}.
Arguments from {A G}.
Arguments slot {A G}.

(** Edge codes encode the pair of source point and slot. *)
Definition skel_edge_encoding {A G} : encoding (skel_edge A G).
Proof.
  refine (Encoding _ (fun e => encode (pair_encoding skel_point_encoding nat_encoding)
    (from e, slot e)) _).
  intros [v i] [v' i'] Hcode; apply (encode_injective (pair_encoding _ _)) in Hcode.
  inversion Hcode; reflexivity.
Defined.

(** One action observes or changes the store, producing exactly its events. *)
Definition act_hold {A G St O} (C : skeleton_client A G St O) (x : action A G)
    (st : St) (l : list O) (st' : St) : Prop :=
  match x with
  | AAtom a => atom_step C a st l st'
  | AGuard g b => guard_bool C g st = Some b /\ l = [] /\ st' = st
  | AIndexIs g i => guard_index C g st = Some i /\ l = [] /\ st' = st
  | AIndexAtLeast g len =>
    (exists j, guard_index C g st = Some j /\ len <= j) /\ l = [] /\ st' = st
  | AJump p n => jump_effect C p n st st' /\ l = []
  end.

(** Action lists compose store transitions and concatenate their events. *)
Inductive acts_hold {A G St O} (C : skeleton_client A G St O) :
    list (action A G) -> St -> list O -> St -> Prop :=
  | holds_nil : forall st, acts_hold C [] st [] st
  | holds_cons : forall x xs st l1 st1 l2 st2,
      act_hold C x st l1 st1 -> acts_hold C xs st1 l2 st2 ->
      acts_hold C (x :: xs) st (l1 ++ l2) st2.

Arguments holds_nil {A G St O C}.
Arguments holds_cons {A G St O C}.

(** Machine phases have their corresponding entry or exit point. *)
Definition machine_point {St} (m : mstate St) : skel_point :=
  match m with
  | Go p _ _ => PEntry p
  | Ret p _ _ => PExit p
  end.

(** Resuming a label has a store-independent control destination. *)
Fixpoint resume_target (n : nat) (k : list frame) : option skel_point :=
  match k with
  | [] => None
  | FSeq _ :: k | FJoin _ :: k => resume_target n k
  | FBlock p :: k =>
    match n with
    | 0 => Some (PExit p)
    | S n => resume_target n k
    end
  | FLoop p :: k =>
    match n with
    | 0 => Some (PEntry (p ++ [DBody]))
    | S n => resume_target n k
    end
  end.

(** Proper prefixes retain their labels even if a later direction is invalid. *)
Fixpoint enclosing_from {A G} (s : stmt A G) (base p : position) (k : list frame) :
    list frame :=
  match p with
  | [] => k
  | d :: p =>
    match child s d with
    | Some t => enclosing_from t (base ++ [d]) p (child_frame s d base :: k)
    | None =>
      match s with
      | Block _ => FBlock base :: k
      | Loop _ => FLoop base :: k
      | _ => k
      end
    end
  end.

(** Relative labels count block and loop statements at the position's proper prefixes. *)
Definition label_point {A G} (prog : stmt A G) (p : position) (n : nat) :
    option skel_point := resume_target n (enclosing_from prog [] p []).

(** Missing jump labels contribute no edge. *)
Definition jump_out {A G} (prog : stmt A G) p n (xs : list (action A G)) :
    list (skel_point * list (action A G)) :=
  match label_point prog p n with
  | Some v => [(v, xs)]
  | None => []
  end.

(** Jump-table alternatives are indexed in one traversal, preserving duplicate targets. *)
Fixpoint table_out {A G} (prog : stmt A G) p g (ns : list nat) (i : nat) :
    list (skel_point * list (action A G)) :=
  match ns with
  | [] => []
  | n :: ns => jump_out prog p n [AIndexIs g i; AJump p n] ++
      table_out prog p g ns (S i)
  end.

(** An ordinary return executes the continuation stored by its nearest owner. *)
Definition return_point (f : frame) : skel_point :=
  match f with
  | FSeq p => PEntry (p ++ [DSecond])
  | FJoin p | FBlock p => PExit p
  | FLoop p => PEntry (p ++ [DBody])
  end.

(** The outgoing table follows statement alternatives and canonical return continuations. *)
Definition skel_out {A G} (prog : stmt A G) (v : skel_point) :
    list (skel_point * list (action A G)) :=
  match v with
  | PEntry p =>
    match sub prog p with
    | Some (Atom a) => [(PExit p, [AAtom a])]
    | Some (Seq _ _) => [(PEntry (p ++ [DFirst]), [])]
    | Some (If g _ _) =>
      [(PEntry (p ++ [DFirst]), [AGuard g true]);
       (PEntry (p ++ [DSecond]), [AGuard g false])]
    | Some (Block _) | Some (Loop _) => [(PEntry (p ++ [DBody]), [])]
    | Some (Jump n) => jump_out prog p n [AJump p n]
    | Some (JumpIf g n) =>
      jump_out prog p n [AGuard g true; AJump p n] ++ [(PExit p, [AGuard g false])]
    | Some (JumpTable g ns n) => table_out prog p g ns 0 ++
      jump_out prog p n [AIndexAtLeast g (length ns); AJump p n]
    | None => []
    end
  | PExit p =>
    match locate prog p with
    | Some (_, f :: _) => [(return_point f, [])]
    | _ => []
    end
  end.

(** Every valid position contributes both machine phases. *)
Definition skel_nodes {A G} (prog : stmt A G) : list skel_point :=
  flat_map (fun p => [PEntry p; PExit p]) (positions prog).

(** Numbering traverses an outgoing table once and retains every alternative's payload. *)
Fixpoint numbered_out {A G} (v : skel_point) (i : nat)
    (xs : list (skel_point * list (action A G))) :
    list (skel_edge A G * (skel_point * list (action A G))) :=
  match xs with
  | [] => []
  | x :: xs => (SkelEdge v i, x) :: numbered_out v (S i) xs
  end.

(** Both maps come from the same prepared rows, keyed by syntactic occurrence and slot. *)
Record skeleton_index (A G : Type) : Type := SkeletonIndex {
  indexed_out : Map.t skel_point (list (skel_edge A G));
  indexed_payload : Map.t (skel_edge A G) (skel_point * list (action A G))
}.

Arguments indexed_out {A G}.
Arguments indexed_payload {A G}.

(** Preparation computes each node's outgoing table once, before constructing the two maps. *)
Definition prepare_skeleton {A G} (prog : stmt A G) : skeleton_index A G :=
  let rows := map (fun v => (v, numbered_out v 0 (skel_out prog v))) (skel_nodes prog) in
  {| indexed_out := Map.of_list skel_point_encoding
       (map (fun row => (fst row, map fst (snd row))) rows);
     indexed_payload := Map.of_list skel_edge_encoding (flat_map snd rows) |}.

(** Preparation establishes the canonical-map key invariants internally. *)
Lemma prepared_skeleton_wf {A G} (prog : stmt A G) :
  Map.wf skel_point_encoding (indexed_out (prepare_skeleton prog)) /\
  Map.wf skel_edge_encoding (indexed_payload (prepare_skeleton prog)).
Proof.
  split; apply Map.wf_of_list.
Qed.

(** Missing points have no outgoing keys. *)
Definition indexed_keys {A G} (index : skeleton_index A G) (v : skel_point) :
    list (skel_edge A G) :=
  match Map.get skel_point_encoding v (indexed_out index) with
  | Some es => es
  | None => []
  end.

(** Missing edge keys target their source. *)
Definition indexed_to {A G} (index : skeleton_index A G) (e : skel_edge A G) : skel_point :=
  match Map.get skel_edge_encoding e (indexed_payload index) with
  | Some (t, _) => t
  | None => from e
  end.

(** Missing edge keys perform no actions. *)
Definition indexed_acts {A G} (index : skeleton_index A G) (e : skel_edge A G) :
    list (action A G) :=
  match Map.get skel_edge_encoding e (indexed_payload index) with
  | Some (_, a) => a
  | None => []
  end.

(** The target selector captures its prepared payload map before accepting edge queries. *)
Definition skel_to {A G} (prog : stmt A G) : forall (e : skel_edge A G), skel_point :=
  let index := prepare_skeleton prog in indexed_to index.

(** The action selector captures its prepared payload map before accepting edge queries. *)
Definition skel_acts {A G} (prog : stmt A G) : forall (e : skel_edge A G), list (action A G) :=
  let index := prepare_skeleton prog in indexed_acts index.

(** Graph callbacks close over prepared maps and only perform encoded lookups. *)
Definition indexed_graph {A G} (prog : stmt A G) (index : skeleton_index A G) :
    Graph.t skel_point (skel_edge A G) :=
  {| Graph.entries := [PEntry []];
     Graph.nodes := skel_nodes prog;
     Graph.out := indexed_keys index;
     Graph.source := from;
     Graph.target := indexed_to index |}.

(** The skeleton graph retains one index for all of its callbacks. *)
Definition skeleton_graph {A G} (prog : stmt A G) : Graph.t skel_point (skel_edge A G) :=
  let index := prepare_skeleton prog in indexed_graph prog index.

(** * Prepared lookup agreement *)

Lemma map_bindings_agree {K V} (E : encoding K) (rows : list (K * V)) (f : K -> option V) :
  (forall k v, In (k, v) rows <-> f k = Some v) ->
  forall k, Map.get E k (Map.of_list E rows) = f k.
Proof.
  intros Hrows k; rewrite Map.get_of_list.
  destruct (find (fun kv => Pos.eqb (encode E (fst kv)) (encode E k)) (rev rows))
    as [[a v]|] eqn:Hfind.
  - apply find_some in Hfind; destruct Hfind as [Hin Hcode].
    apply Pos.eqb_eq, (encode_injective E) in Hcode; cbn in Hcode; subst a.
    apply in_rev in Hin; cbn; symmetry; apply Hrows; exact Hin.
  - cbn; destruct (f k) as [v|] eqn:Hvalue; [|reflexivity].
    apply Hrows in Hvalue; apply (proj1 (in_rev _ _)) in Hvalue.
    pose proof (find_none _ _ Hfind (k, v) Hvalue) as Hcode.
    cbn in Hcode; rewrite Pos.eqb_refl in Hcode; discriminate.
Qed.

Lemma numbered_out_spec {A G} v i xs (e : skel_edge A G) x :
  In (e, x) (numbered_out v i xs) <->
  from e = v /\ exists j, slot e = i + j /\ nth_error xs j = Some x.
Proof.
  revert i; induction xs as [|y xs IH]; intro i; cbn [numbered_out In].
  - split; [contradiction|intros [_ [j [_ Hnth]]]; destruct j; discriminate].
  - rewrite IH; split.
    + intros [Heq|[Hfrom [j [Hslot Hnth]]]].
      * inversion Heq; subst; split; [reflexivity|exists 0; cbn; auto with arith].
      * split; [exact Hfrom|exists (S j); split; [cbn; lia|exact Hnth]].
    + intros [Hfrom [[|j] [Hslot Hnth]]].
      * cbn in Hnth; inversion Hnth; subst x; left; destruct e; cbn in *;
          subst; f_equal; f_equal; lia.
      * right; split; [exact Hfrom|exists j; split; [lia|exact Hnth]].
Qed.

Lemma numbered_out_keys {A G} v i (xs : list (skel_point * list (action A G))) :
  map fst (numbered_out v i xs) = map (SkelEdge v) (seq i (length xs)).
Proof.
  revert i; induction xs as [|x xs IH]; intro i; cbn; [reflexivity|rewrite IH; reflexivity].
Qed.

Lemma outgoing_source_node {A G} (prog : stmt A G) v i x :
  nth_error (skel_out prog v) i = Some x -> In v (skel_nodes prog).
Proof.
  destruct v as [p|p]; intro Hnth; apply in_flat_map; exists p; split.
  - apply (proj2 (positions_exact prog)); cbn [skel_out] in Hnth.
    destruct (sub prog p) as [s|] eqn:Hsub; [eexists; reflexivity|].
    destruct i; discriminate.
  - cbn; auto.
  - apply (proj2 (positions_exact prog)); cbn [skel_out] in Hnth.
    destruct (locate prog p) as [[s k]|] eqn:Hloc.
    + exists s; exact (proj2 (locate_context prog p s k Hloc)).
    + destruct i; discriminate.
  - cbn; auto.
Qed.

(** Every payload lookup agrees with the reference selector, including absent sources and slots. *)
Lemma prepared_payload_agrees {A G} (prog : stmt A G) (e : skel_edge A G) :
  Map.get skel_edge_encoding e (indexed_payload (prepare_skeleton prog)) =
    nth_error (skel_out prog (from e)) (slot e).
Proof.
  apply (map_bindings_agree skel_edge_encoding _
    (fun edge => nth_error (skel_out prog (from edge)) (slot edge))).
  intros edge x; cbn [prepare_skeleton indexed_payload].
  rewrite in_flat_map; split.
  - intros [row [Hrow Hedge]]; apply in_map_iff in Hrow.
    destruct Hrow as [v [<- Hnode]]; cbn in Hedge.
    apply numbered_out_spec in Hedge; destruct Hedge as [Hfrom [j [Hslot Hnth]]].
    cbn in Hslot; rewrite Hfrom, Hslot; exact Hnth.
  - intro Hnth; exists (from edge, numbered_out (from edge) 0 (skel_out prog (from edge))).
    split.
    + apply in_map_iff; exists (from edge); split; [reflexivity|].
      eapply outgoing_source_node; exact Hnth.
    + apply numbered_out_spec; split; [reflexivity|exists (slot edge); split;
        [reflexivity|exact Hnth]].
Qed.

Lemma skel_point_eq_dec (u v : skel_point) : {u = v} + {u <> v}.
Proof.
  decide equality; apply list_eq_dec; decide equality.
Defined.

(** Outgoing lookups retain the reference order and return no keys at invalid positions. *)
Lemma prepared_keys_agree {A G} (prog : stmt A G) v :
  indexed_keys (prepare_skeleton prog) v =
    map (SkelEdge v) (seq 0 (length (skel_out prog v))).
Proof.
  assert (Hget : Map.get skel_point_encoding v (indexed_out (prepare_skeleton prog)) =
    if in_dec skel_point_eq_dec v (skel_nodes prog)
    then Some (map fst (numbered_out v 0 (skel_out prog v))) else None).
  { apply (map_bindings_agree skel_point_encoding _ (fun u =>
      if in_dec skel_point_eq_dec u (skel_nodes prog)
      then Some (map fst (numbered_out u 0 (skel_out prog u))) else None)).
    intros u es; repeat rewrite map_map; rewrite in_map_iff.
    destruct (in_dec skel_point_eq_dec u (skel_nodes prog)) as [Hin|Hnot].
    - split.
      + intros [w [Heq Hnode]]; inversion Heq; reflexivity.
      + intro Heq; inversion Heq; exists u; split; [reflexivity|exact Hin].
    - split.
      + intros [w [Heq Hnode]]; inversion Heq; subst; contradiction.
      + discriminate. }
  unfold indexed_keys; rewrite Hget; destruct (in_dec _ _ _) as [Hin|Hnot].
  - apply numbered_out_keys.
  - destruct (skel_out prog v) as [|x xs] eqn:Hout; [reflexivity|].
    exfalso; apply Hnot; eapply outgoing_source_node with (i := 0) (x := x).
    rewrite Hout; reflexivity.
Qed.

(** The target reference equation holds for every edge key. *)
Lemma skel_to_agrees {A G} (prog : stmt A G) e :
  skel_to prog e =
    match nth_error (skel_out prog (from e)) (slot e) with
    | Some (t, _) => t
    | None => from e
    end.
Proof.
  unfold skel_to, indexed_to; rewrite prepared_payload_agrees; reflexivity.
Qed.

(** The action reference equation holds for every edge key. *)
Lemma skel_acts_agrees {A G} (prog : stmt A G) e :
  skel_acts prog e =
    match nth_error (skel_out prog (from e)) (slot e) with
    | Some (_, xs) => xs
    | None => []
    end.
Proof.
  unfold skel_acts, indexed_acts; rewrite prepared_payload_agrees; reflexivity.
Qed.

(** Graph outgoing keys agree with dense reference slots at every point. *)
Lemma skeleton_graph_out_agrees {A G} (prog : stmt A G) v :
  Graph.out (skeleton_graph prog) v =
    map (SkelEdge v) (seq 0 (length (skel_out prog v))).
Proof.
  apply prepared_keys_agree.
Qed.

(** All graph fields preserve their reference observations without function extensionality. *)
Lemma skeleton_graph_agrees {A G} (prog : stmt A G) :
  Graph.entries (skeleton_graph prog) = [PEntry []] /\
  Graph.nodes (skeleton_graph prog) = skel_nodes prog /\
  (forall v, Graph.out (skeleton_graph prog) v =
    map (SkelEdge v) (seq 0 (length (skel_out prog v)))) /\
  (forall e, Graph.source (skeleton_graph prog) e = from e) /\
  (forall e, Graph.target (skeleton_graph prog) e = skel_to prog e).
Proof.
  split; [reflexivity|]; split; [reflexivity|]; split.
  - apply skeleton_graph_out_agrees.
  - split; intro e; reflexivity.
Qed.

(** Invalid positions have no outgoing edges in either phase. *)
Lemma skel_out_invalid {A G} (prog : stmt A G) p :
  sub prog p = None -> skel_out prog (PEntry p) = [] /\ skel_out prog (PExit p) = [].
Proof.
  intro Hsub; split; cbn [skel_out].
  - rewrite Hsub; reflexivity.
  - pose proof (locate_from_sub prog [] p []) as Hloc.
    change (option_map fst (locate prog p) = sub prog p) in Hloc.
    rewrite Hsub in Hloc; destruct (locate prog p) as [[s k]|];
      [discriminate|reflexivity].
Qed.

(** Every machine step takes an edge whose actions describe its client-store transition. *)
Definition skeleton_view {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
    graph_view (mstate St) O skel_point (skel_edge A G) :=
  {| cfg := skeleton_graph prog;
     point := machine_point;
     taken := fun m l m' e =>
       In e (Graph.out (skeleton_graph prog) (machine_point m)) /\
       machine_point m' = skel_to prog e /\
       acts_hold C (skel_acts prog e) (store_of m) l (store_of m');
     stays := fun _ _ _ => False |}.

(** Loop heads are body entries of loop statements, in statement preorder. *)
Definition loop_heads {A G} (prog : stmt A G) : list skel_point :=
  flat_map (fun p =>
    match sub prog p with
    | Some (Loop _) => [PEntry (p ++ [DBody])]
    | _ => []
    end) (positions prog).

(** Splitting the final direction takes one traversal of a position. *)
Fixpoint split_last (p : position) : option (position * dir) :=
  match p with
  | [] => None
  | d :: [] => Some ([], d)
  | d :: rest =>
    match split_last rest with
    | Some (base, last) => Some (d :: base, last)
    | None => None
    end
  end.

(** A body entry is a loop head exactly when its owner is a loop. *)
Definition is_loop_head {A G} (prog : stmt A G) (n : skel_point) : bool :=
  match n with
  | PEntry p =>
    match split_last p with
    | Some (base, DBody) =>
      match sub prog base with
      | Some (Loop _) => true
      | _ => false
      end
    | _ => false
    end
  | PExit _ => false
  end.

(** Trapping at a statement depends only on its store. *)
Definition traps_at {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    (p : position) (st : St) : Prop :=
  trapped (skeleton_endings prog C) (Go p [] st).

(** Resource stopping at a statement depends only on its store. *)
Definition stops_at {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    (p : position) (st : St) : Prop :=
  stopped (skeleton_endings prog C) (Go p [] st).

(** Store agreement observes the store component of each machine state. *)
Definition store_agreement {Fa St} (Ra : agreement Fa St) : agreement Fa (mstate St) :=
  Agreement _ _ (fun a m n => agree Ra a (store_of m) (store_of n)).

(** Only the root entry receives the initial forward seed. *)
Definition skel_root (n : skel_point) : bool :=
  match n with
  | PEntry [] => true
  | _ => false
  end.

(** Prepared forward transfers only read the retained payload map. *)
Definition indexed_fwd {A G Fa} (index : skeleton_index A G) (act : action A G -> Fa -> Fa) :
    skel_edge A G -> Fa -> Fa :=
  fun e f => fold_left (fun f x => act x f) (indexed_acts index e) f.

(** Forward edge transfer captures preparation before receiving an edge or fact. *)
Definition edge_fwd {A G Fa} (prog : stmt A G) (act : action A G -> Fa -> Fa) :
    forall (e : skel_edge A G) (f : Fa), Fa :=
  let index := prepare_skeleton prog in indexed_fwd index act.

(** Prepared backward transfers only read the retained payload map. *)
Definition indexed_bwd {A G Fa} (index : skeleton_index A G) (actb : action A G -> Fa -> Fa) :
    skel_edge A G -> Fa -> Fa :=
  fun e f => fold_right actb f (indexed_acts index e).

(** Backward edge transfer captures preparation before receiving an edge or fact. *)
Definition edge_bwd {A G Fa} (prog : stmt A G) (actb : action A G -> Fa -> Fa) :
    forall (e : skel_edge A G) (f : Fa), Fa :=
  let index := prepare_skeleton prog in indexed_bwd index actb.

(** Forward constraints are the dense constraints of the skeleton graph. *)
Definition skeleton_forward {A G Fa} (L : lattice Fa) (prog : stmt A G) (init : Fa)
    (act : action A G -> Fa -> Fa) :
    System.t skel_point (dense_constraint skel_point (skel_edge A G)) Fa :=
  let index := prepare_skeleton prog in
  forward_system (indexed_graph prog index) (fun n => if skel_root n then init else bot L)
    (indexed_fwd index act).

(** Forward static dependencies are the sources of flow edges. *)
Definition skeleton_forward_static {A G Fa} (L : lattice Fa) (prog : stmt A G) (init : Fa)
    (act : action A G -> Fa -> Fa) : System.static (skeleton_forward L prog init act) :=
  let index := prepare_skeleton prog in
  forward_static (indexed_graph prog index) (fun n => if skel_root n then init else bot L)
    (indexed_fwd index act).

(** Backward constraints seed every point and propagate edge needs backwards. *)
Definition skeleton_backward {A G Fa} (prog : stmt A G) (exitf : skel_point -> Fa)
    (actb : action A G -> Fa -> Fa) :
    System.t skel_point (dense_constraint skel_point (skel_edge A G)) Fa :=
  let index := prepare_skeleton prog in
  backward_system (indexed_graph prog index) exitf (indexed_bwd index actb).

(** Backward static dependencies are the targets of flow edges. *)
Definition skeleton_backward_static {A G Fa} (prog : stmt A G) (exitf : skel_point -> Fa)
    (actb : action A G -> Fa -> Fa) : System.static (skeleton_backward prog exitf actb) :=
  let index := prepare_skeleton prog in
  backward_static (indexed_graph prog index) exitf (indexed_bwd index actb).

(** Prepared forward folding preserves the action list's first-to-last order. *)
Lemma edge_fwd_agrees {A G Fa} (prog : stmt A G) (act : action A G -> Fa -> Fa) e f :
  edge_fwd prog act e f = fold_left (fun f x => act x f) (skel_acts prog e) f.
Proof.
  reflexivity.
Qed.

(** Prepared backward folding preserves the action list's last-to-first order. *)
Lemma edge_bwd_agrees {A G Fa} (prog : stmt A G) (actb : action A G -> Fa -> Fa) e f :
  edge_bwd prog actb e f = fold_right actb f (skel_acts prog e).
Proof.
  reflexivity.
Qed.

(** Forward rows preserve the full reference observations for arbitrary rows and assignments. *)
Lemma skeleton_forward_agrees {A G Fa} (L : lattice Fa) (prog : stmt A G) init act :
  let actual := skeleton_forward L prog init act in
  let reference := forward_system (skeleton_graph prog)
    (fun n => if skel_root n then init else bot L) (edge_fwd prog act) in
  System.constraints actual = System.constraints reference /\
  forall c, System.target actual c = System.target reference c /\
  forall sigma,
    Query.eval (System.rhs actual c) sigma = Query.eval (System.rhs reference c) sigma /\
    Query.reads (System.rhs actual c) sigma = Query.reads (System.rhs reference c) sigma /\
    Query.sides (System.rhs actual c) sigma = Query.sides (System.rhs reference c) sigma.
Proof.
  split; [reflexivity|]; intro c; split; [reflexivity|]; intro sigma.
  split; [reflexivity|]; split; reflexivity.
Qed.

(** Backward rows preserve the full reference observations for arbitrary rows and assignments. *)
Lemma skeleton_backward_agrees {A G Fa} (prog : stmt A G) (exitf : skel_point -> Fa) actb :
  let actual := skeleton_backward prog exitf actb in
  let reference := backward_system (skeleton_graph prog) exitf (edge_bwd prog actb) in
  System.constraints actual = System.constraints reference /\
  forall c, System.target actual c = System.target reference c /\
  forall sigma,
    Query.eval (System.rhs actual c) sigma = Query.eval (System.rhs reference c) sigma /\
    Query.reads (System.rhs actual c) sigma = Query.reads (System.rhs reference c) sigma /\
    Query.sides (System.rhs actual c) sigma = Query.sides (System.rhs reference c) sigma.
Proof.
  split; [reflexivity|]; intro c; split; [reflexivity|]; intro sigma.
  split; [reflexivity|]; split; reflexivity.
Qed.

(** Forward static callbacks preserve both reference summaries for every row key. *)
Lemma skeleton_forward_static_agrees {A G Fa} (L : lattice Fa) (prog : stmt A G) init act c :
  let actual := skeleton_forward_static L prog init act in
  let reference := forward_static (skeleton_graph prog)
    (fun n => if skel_root n then init else bot L) (edge_fwd prog act) in
  deps actual c = deps reference c /\ side_targets actual c = side_targets reference c.
Proof.
  split; reflexivity.
Qed.

(** Backward static callbacks preserve both reference summaries for every row key. *)
Lemma skeleton_backward_static_agrees {A G Fa} (prog : stmt A G)
    (exitf : skel_point -> Fa) actb c :
  let actual := skeleton_backward_static prog exitf actb in
  let reference := backward_static (skeleton_graph prog) exitf (edge_bwd prog actb) in
  deps actual c = deps reference c /\ side_targets actual c = side_targets reference c.
Proof.
  split; reflexivity.
Qed.

(** * Control destinations and graph well-formedness *)

Lemma resume_target_map {St} n k (st : St) :
  option_map machine_point (resume n k st) = resume_target n k.
Proof.
  revert n; induction k as [|f k IH]; intro n; [reflexivity|].
  destruct f; cbn; try apply IH.
  all: destruct n; [reflexivity|apply IH].
Qed.

Lemma enclosing_locate {A G} (s : stmt A G) base p k t k' :
  locate_from s base p k = Some (t, k') -> enclosing_from s base p k = k'.
Proof.
  revert s base k; induction p as [|d p IH]; intros s base k Hloc; cbn in *.
  - congruence.
  - destruct (child s d); [eapply IH; exact Hloc|discriminate].
Qed.

Lemma context_enclosing {A G} (prog : stmt A G) p k :
  context prog p k -> enclosing_from prog [] p [] = k.
Proof.
  intro Hctx; destruct (context_locate prog p k Hctx) as [s [Hloc _]].
  eapply enclosing_locate; exact Hloc.
Qed.

Lemma enclosing_valid {A G} (prog s : stmt A G) base p k :
  context prog base k -> sub prog base = Some s ->
  stack_valid prog (enclosing_from s base p k).
Proof.
  revert s base k; induction p as [|d p IH]; intros s base k Hctx Hsub; cbn.
  - eapply context_stack_valid; exact Hctx.
  - destruct (child s d) as [t|] eqn:Hchild.
    + eapply IH.
      * eapply context_child; eassumption.
      * rewrite (sub_child prog base s d Hsub); exact Hchild.
    + pose proof (context_stack_valid prog base k Hctx) as Hvalid.
      destruct s; cbn; try exact Hvalid.
      all: split; [exact Hvalid|split; [exact Hctx|eexists; exact Hsub]].
Qed.

Lemma label_point_resume {A G St} (prog : stmt A G) p k n (st : St) m :
  context prog p k -> resume n k st = Some m ->
  label_point prog p n = Some (machine_point m).
Proof.
  intros Hctx Hresume; unfold label_point; rewrite (context_enclosing prog p k Hctx).
  rewrite <- (resume_target_map n k st), Hresume; reflexivity.
Qed.

(** A graph point is valid when its position has a canonical context. *)
Definition point_valid {A G} (prog : stmt A G) (v : skel_point) : Prop :=
  match v with
  | PEntry p | PExit p => exists k, context prog p k
  end.

Lemma skel_nodes_spec {A G} (prog : stmt A G) v :
  In v (skel_nodes prog) <-> point_valid prog v.
Proof.
  unfold skel_nodes; rewrite in_flat_map; destruct v as [p|p]; split.
  all: try solve [intros [q [Hin [Heq|[Heq|Hfalse]]]]; try contradiction;
    inversion Heq; subst q; apply (proj2 (positions_exact prog)) in Hin;
    destruct Hin as [s Hsub]; eapply sub_context; exact Hsub].
  all: intros [k Hctx]; exists p; split;
    [apply (proj2 (positions_exact prog)); eapply context_sub; exact Hctx|cbn; tauto].
Qed.

Lemma phase_nodes_nodup (ps : list position) :
  NoDup ps -> NoDup (flat_map (fun p => [PEntry p; PExit p]) ps).
Proof.
  intro Hnodup; induction Hnodup as [|p ps Hnot Hnodup IH]; cbn; [constructor|].
  constructor.
  - intros [Hbad|Hin]; [discriminate|].
    apply in_flat_map in Hin; destruct Hin as [q [Hin [Heq|[Heq|Hfalse]]]];
      try contradiction; inversion Heq; subst; contradiction.
  - constructor; [|exact IH].
    intro Hin; apply in_flat_map in Hin; destruct Hin as [q [Hin [Heq|[Heq|Hfalse]]]];
      try contradiction; inversion Heq; subst; contradiction.
Qed.

Lemma label_point_valid {A G} (prog : stmt A G) p n v :
  label_point prog p n = Some v -> point_valid prog v.
Proof.
  unfold label_point; set (k := enclosing_from prog [] p []).
  intro Htarget; pose proof (resume_target_map n k tt) as Hmap.
  rewrite Htarget in Hmap; destruct (resume n k tt) as [m|] eqn:Hresume;
    cbn in Hmap; [|discriminate].
  inversion Hmap; subst v.
  pose proof (resume_context prog n k tt m
    (enclosing_valid prog prog [] p [] context_root eq_refl) Hresume) as Hctx.
  destruct m; eexists; exact Hctx.
Qed.

Lemma return_point_valid {A G} (prog : stmt A G) f k :
  stack_valid prog (f :: k) -> point_valid prog (return_point f).
Proof.
  intros [_ Hframe]; destruct f as [p|p|p|p]; destruct Hframe as [Hctx Howner]; cbn.
  - destruct Howner as [s1 [s2 Hsub]]; exists (FJoin p :: k).
    eapply (context_child (s := Seq s1 s2) (d := DSecond)); eassumption || reflexivity.
  - exists k; exact Hctx.
  - exists k; exact Hctx.
  - destruct Howner as [s Hsub]; exists (FLoop p :: k).
    eapply (context_child (s := Loop s) (d := DBody)); eassumption || reflexivity.
Qed.

Lemma jump_out_valid {A G} (prog : stmt A G) p n xs v ys :
  In (v, ys) (jump_out prog p n xs) -> point_valid prog v.
Proof.
  unfold jump_out; destruct (label_point prog p n) as [t|] eqn:Hlabel; cbn;
    [intros [Heq|Hfalse]; [inversion Heq; subst; eapply label_point_valid; exact Hlabel|
      contradiction]|tauto].
Qed.

Lemma table_out_valid {A G} (prog : stmt A G) p g ns i v xs :
  In (v, xs) (table_out prog p g ns i) -> point_valid prog v.
Proof.
  revert i; induction ns as [|n ns IH]; intros i Hin; [contradiction|].
  cbn in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  - eapply jump_out_valid; exact Hin.
  - eapply IH; exact Hin.
Qed.

Lemma skel_out_valid {A G} (prog : stmt A G) u v xs :
  point_valid prog u -> In (v, xs) (skel_out prog u) -> point_valid prog v.
Proof.
  destruct u as [p|p]; intros [k Hctx]; cbn [skel_out].
  - destruct (context_sub prog p k Hctx) as [s Hsub]; rewrite Hsub.
    destruct s as [a|s1 s2|g s1 s2|s|s|n|g n|g ns n]; cbn.
    + intros [Heq|Hfalse]; [inversion Heq; subst; exists k; exact Hctx|contradiction].
    + intros [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      exists (FSeq p :: k); eapply (context_child (s := Seq s1 s2) (d := DFirst));
        eassumption || reflexivity.
    + intros [Heq|[Heq|Hfalse]]; try contradiction; inversion Heq; subst.
      * exists (FJoin p :: k); eapply (context_child (s := If g s1 s2) (d := DFirst));
          eassumption || reflexivity.
      * exists (FJoin p :: k); eapply (context_child (s := If g s1 s2) (d := DSecond));
          eassumption || reflexivity.
    + intros [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      exists (FBlock p :: k); eapply (context_child (s := Block s) (d := DBody));
        eassumption || reflexivity.
    + intros [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      exists (FLoop p :: k); eapply (context_child (s := Loop s) (d := DBody));
        eassumption || reflexivity.
    + apply jump_out_valid.
    + intro Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hfalse]].
      * eapply jump_out_valid; exact Hin.
      * inversion Heq; subst; exists k; exact Hctx.
      * contradiction.
    + intro Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      * eapply table_out_valid; exact Hin.
      * eapply jump_out_valid; exact Hin.
  - destruct (context_locate prog p k Hctx) as [s [Hloc _]]; rewrite Hloc.
    destruct k as [|f k]; cbn; [tauto|].
    intros [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
    apply (return_point_valid prog f k); eapply context_stack_valid; exact Hctx.
Qed.

Lemma skeleton_out_slot {A G} (prog : stmt A G) v (e : skel_edge A G) :
  In e (Graph.out (skeleton_graph prog) v) <->
  from e = v /\ slot e < length (skel_out prog v).
Proof.
  rewrite skeleton_graph_out_agrees; destruct e as [u i]; cbn [from slot].
  rewrite in_map_iff; split.
  - intros [j [Heq Hin]]; inversion Heq; subst; split; [reflexivity|].
    apply in_seq in Hin; lia.
  - intros [-> Hbound]; exists i; split; [reflexivity|apply in_seq; lia].
Qed.

(** The skeleton graph has distinct nodes and closed, correctly sourced edges. *)
Lemma skeleton_graph_wf {A G} (prog : stmt A G) : graph_wf (skeleton_graph prog).
Proof.
  constructor.
  - apply phase_nodes_nodup; exact (proj1 (positions_exact prog)).
  - intros v [<-|Hfalse]; [apply skel_nodes_spec; exists []; constructor|contradiction].
  - intros v e Hin; exact (proj1 (proj1 (skeleton_out_slot prog v e) Hin)).
  - intros v e Hnode Hedge; apply skeleton_out_slot in Hedge; destruct Hedge as [Hfrom Hbound].
    change (In (skel_to prog e) (skel_nodes prog)).
    rewrite skel_to_agrees, Hfrom.
    destruct (nth_error (skel_out prog v) (slot e)) as [[t xs]|] eqn:Hnth.
    + apply skel_nodes_spec; eapply skel_out_valid.
      * apply skel_nodes_spec; exact Hnode.
      * apply nth_error_In in Hnth; exact Hnth.
    + apply nth_error_None in Hnth; lia.
Qed.

(** * Machine steps and graph edges *)

Lemma holds_single {A G St O} (C : skeleton_client A G St O) x st l st' :
  act_hold C x st l st' -> acts_hold C [x] st l st'.
Proof.
  intro Hact; rewrite <- (app_nil_r l); econstructor; [exact Hact|constructor].
Qed.

Lemma holds_guard_jump {A G St O} (C : skeleton_client A G St O) g b p n st st' :
  guard_bool C g st = Some b -> jump_effect C p n st st' ->
  acts_hold C [AGuard g b; AJump p n] st [] st'.
Proof.
  intros Hguard Heffect; change (acts_hold C [AGuard g b; AJump p n] st ([] ++ []) st').
  econstructor; [repeat split; assumption || reflexivity|].
  apply holds_single; split; [exact Heffect|reflexivity].
Qed.

Lemma jump_out_in {A G} (prog : stmt A G) p n xs v :
  label_point prog p n = Some v -> In (v, xs) (jump_out prog p n xs).
Proof.
  intro Hlabel; unfold jump_out; rewrite Hlabel; left; reflexivity.
Qed.

Lemma table_out_nth {A G} (prog : stmt A G) p g ns i j n v :
  nth_error ns j = Some n -> label_point prog p n = Some v ->
  In (v, [AIndexIs g (i + j); AJump p n]) (table_out prog p g ns i).
Proof.
  revert i j; induction ns as [|a ns IH]; intros i [|j] Hnth Hlabel; cbn in Hnth;
    try discriminate; cbn [table_out].
  - inversion Hnth; subst; apply in_or_app; left; rewrite Nat.add_0_r.
    apply jump_out_in; exact Hlabel.
  - apply in_or_app; right; replace (i + S j) with (S i + j) by lia.
    eapply IH; eassumption.
Qed.

Lemma resume_store {St} n k (st : St) m :
  resume n k st = Some m -> store_of m = st.
Proof.
  revert n; induction k as [|f k IH]; intros n Hresume; [discriminate|].
  destruct f; cbn in Hresume; try (eapply IH; exact Hresume).
  all: destruct n; [inversion Hresume; reflexivity|eapply IH; exact Hresume].
Qed.

Lemma table_out_selected {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    p k st g ns n i st' m :
  context prog p k -> guard_index C g st = Some i ->
  jump_effect C p (nth i ns n) st st' -> resume (nth i ns n) k st' = Some m ->
  exists xs, In (machine_point m, xs)
    (table_out prog p g ns 0 ++
      jump_out prog p n [AIndexAtLeast g (length ns); AJump p n]) /\
    acts_hold C xs st [] (store_of m).
Proof.
  intros Hctx Hguard Heffect Hresume.
  assert (Hstore : store_of m = st').
  { eapply resume_store; exact Hresume. }
  pose proof (label_point_resume prog p k (nth i ns n) st' m Hctx Hresume) as Hlabel.
  destruct (lt_dec i (length ns)) as [Hin|Hout].
  - exists [AIndexIs g i; AJump p (nth i ns n)]; split.
    + apply in_or_app; left; replace i with (0 + i) at 1 by lia.
      eapply table_out_nth; [apply nth_error_nth'; exact Hin|exact Hlabel].
    + rewrite Hstore; change (acts_hold C [AIndexIs g i; AJump p (nth i ns n)]
        st ([] ++ []) st').
      econstructor; [repeat split; assumption || reflexivity|].
      apply holds_single; split; [exact Heffect|reflexivity].
  - rewrite nth_overflow in Heffect, Hlabel by lia.
    exists [AIndexAtLeast g (length ns); AJump p n]; split.
    + apply in_or_app; right; apply jump_out_in; exact Hlabel.
    + rewrite Hstore; change (acts_hold C [AIndexAtLeast g (length ns); AJump p n]
        st ([] ++ []) st').
      econstructor.
      * split; [exists i; split; [exact Hguard|lia]|split; reflexivity].
      * apply holds_single; split; [exact Heffect|reflexivity].
Qed.

Lemma machine_step_out {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    m l m' : machine_valid prog m -> skel_step prog C m l m' ->
  exists xs, In (machine_point m', xs) (skel_out prog (machine_point m)) /\
    acts_hold C xs (store_of m) l (store_of m').
Proof.
  intros Hvalid Hstep; destruct Hstep; cbn [machine_valid machine_point store_of] in *.
  all: try match goal with
  | Hsub : sub _ _ = Some _ |- _ => cbn [skel_out]; rewrite Hsub
  end.
  - exists [AAtom a]; split; [left; reflexivity|apply holds_single; assumption].
  - exists []; split; [left; reflexivity|constructor].
  - exists [AGuard g b]; split.
    + destruct b; cbn; tauto.
    + apply holds_single; repeat split; assumption || reflexivity.
  - exists []; split; [left; reflexivity|constructor].
  - exists []; split; [left; reflexivity|constructor].
  - exists [AJump p n]; split.
    + apply jump_out_in; eapply label_point_resume; eassumption.
    + rewrite (resume_store _ _ _ _ ltac:(eassumption)); apply holds_single; split;
        assumption || reflexivity.
  - exists [AGuard g true; AJump p n]; split.
    + apply in_or_app; left; apply jump_out_in; eapply label_point_resume; eassumption.
    + rewrite (resume_store _ _ _ _ ltac:(eassumption)); apply holds_guard_jump; assumption.
  - exists [AGuard g false]; split.
    + apply in_or_app; right; left; reflexivity.
    + apply holds_single; repeat split; assumption || reflexivity.
  - eapply table_out_selected; eassumption.
  - destruct (context_locate prog c (FSeq p :: k) Hvalid) as [s [Hloc _]].
    exists []; split; [cbn [skel_out]; rewrite Hloc; left; reflexivity|constructor].
  - destruct (context_locate prog c (FJoin p :: k) Hvalid) as [s [Hloc _]].
    exists []; split; [cbn [skel_out]; rewrite Hloc; left; reflexivity|constructor].
  - destruct (context_locate prog c (FBlock p :: k) Hvalid) as [s [Hloc _]].
    exists []; split; [cbn [skel_out]; rewrite Hloc; left; reflexivity|constructor].
  - destruct (context_locate prog c (FLoop p :: k) Hvalid) as [s [Hloc _]].
    exists []; split; [cbn [skel_out]; rewrite Hloc; left; reflexivity|constructor].
Qed.

Lemma machine_step_taken {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    m l m' : machine_valid prog m -> skel_step prog C m l m' ->
  exists e, taken (skeleton_view prog C) m l m' e.
Proof.
  intros Hvalid Hstep; destruct (machine_step_out prog C m l m' Hvalid Hstep)
    as [xs [Hin Hacts]].
  apply In_nth_error in Hin; destruct Hin as [i Hnth].
  exists (SkelEdge (machine_point m) i); split.
  - apply skeleton_out_slot; split; [reflexivity|].
    cbn [slot]; apply nth_error_Some; rewrite Hnth; discriminate.
  - cbn [skeleton_view taken]; rewrite skel_to_agrees, skel_acts_agrees; cbn [from slot];
      rewrite Hnth; split; [reflexivity|exact Hacts].
Qed.

(** Every program and client gives a graph view of its reachable machine steps. *)
Theorem skeleton_view_laws_hold {A G St O} (prog : stmt A G)
    (C : skeleton_client A G St O) :
  graph_view_laws (skeleton_semantics prog C) (skeleton_view prog C).
Proof.
  constructor.
  - apply skeleton_graph_wf.
  - intros m [st [-> Hinit]]; left; reflexivity.
  - intros m l m' Hreachable Hstep; right; apply machine_step_taken;
      [eapply reachable_machine_valid; exact Hreachable|exact Hstep].
  - intros m l m' e _ _ [Hout [Htarget Hacts]]; split; [exact Hout|symmetry; exact Htarget].
  - intros m l m' _ _ Hfalse; contradiction.
Qed.

(** * Forward transfer soundness *)

Lemma acts_forward_sound {A G St O Fa} (Gc : concretisation Fa St)
    (C : skeleton_client A G St O) (act : action A G -> Fa -> Fa) :
  (forall x f st l st', gamma Gc f st -> act_hold C x st l st' -> gamma Gc (act x f) st') ->
  forall xs st l st', acts_hold C xs st l st' -> forall f,
    gamma Gc f st -> gamma Gc (fold_left (fun f x => act x f) xs f) st'.
Proof.
  intros Hact xs st l st' Hacts; induction Hacts as
    [st|x xs st l1 st1 l2 st2 Hhead Htail IH]; intros f Hfact; cbn.
  - exact Hfact.
  - apply IH; eapply Hact; eassumption.
Qed.

(** Forward post-solutions describe the stores of every reachable machine state. *)
Theorem skeleton_forward_sound {A G St O Fa} (L : lattice Fa) (Gc : concretisation Fa St)
    (prog : stmt A G) (C : skeleton_client A G St O) (init : Fa)
    (act : action A G -> Fa -> Fa) (sigma : skel_point -> Fa) :
  concretisation_laws L Gc -> (forall st, init_store C st -> gamma Gc init st) ->
  (forall x f st l st', gamma Gc f st -> act_hold C x st l st' -> gamma Gc (act x f) st') ->
  post_solution L (skeleton_forward L prog init act) sigma ->
  forall m, reachable_state (skeleton_semantics prog C) m ->
    gamma Gc (sigma (point (skeleton_view prog C) m)) (store_of m).
Proof.
  intros HG Hinit Hact Hpost.
  apply (forward_invariant_sound (skeleton_semantics prog C) (skeleton_view prog C) L
    (fun _ => Concretisation _ _ (fun f m => gamma Gc f (store_of m)))
    (fun n => if skel_root n then init else bot L) (edge_fwd prog act) sigma).
  - apply skeleton_view_laws_hold.
  - constructor; intros a b m Hle Hfact; eapply (gamma_monotone HG); eassumption.
  - intros m [st [-> Hinitial]]; apply Hinit; exact Hinitial.
  - intros e m l m' _ _ [_ [_ Hacts]] Hfact.
    exact (acts_forward_sound Gc C act Hact _ _ _ _ Hacts _ Hfact).
  - intros m l m' _ _ Hfalse; contradiction.
  - exact Hpost.
Qed.

(** * Backward action matching *)

Lemma acts_backward_match {A G St O Fa} (Ra : agreement Fa St)
    (C : skeleton_client A G St O) (actb : action A G -> Fa -> Fa) :
  (forall x a st1 l st1' st2, act_hold C x st1 l st1' -> agree Ra (actb x a) st1 st2 ->
    exists st2', act_hold C x st2 l st2' /\ agree Ra a st1' st2') ->
  forall xs st1 l st1', acts_hold C xs st1 l st1' -> forall a st2,
    agree Ra (fold_right actb a xs) st1 st2 ->
    exists st2', acts_hold C xs st2 l st2' /\ agree Ra a st1' st2'.
Proof.
  intros Hact xs st1 l st1' Hacts; induction Hacts as
    [st|x xs st l1 mid l2 last Hhead Htail IH]; intros a st2 Hagree.
  - exists st2; split; [constructor|exact Hagree].
  - destruct (Hact x (fold_right actb a xs) st l1 mid st2 Hhead Hagree)
      as [mid2 [Hhead2 Hagree2]].
    destruct (IH a mid2 Hagree2) as [last2 [Htail2 Hagree3]].
    exists last2; split; [econstructor; eassumption|exact Hagree3].
Qed.

Lemma holds_nil_inv {A G St O} (C : skeleton_client A G St O) st l st' :
  acts_hold C [] st l st' -> l = [] /\ st' = st.
Proof.
  intro Hacts; inversion Hacts; subst; split; reflexivity.
Qed.

Lemma holds_single_inv {A G St O} (C : skeleton_client A G St O) x st l st' :
  acts_hold C [x] st l st' -> act_hold C x st l st'.
Proof.
  intro Hacts; inversion Hacts as [|y ys start l1 mid l2 last Hhead Htail]; subst.
  apply holds_nil_inv in Htail; destruct Htail as [-> ->]; rewrite app_nil_r; exact Hhead.
Qed.

Lemma holds_pair_inv {A G St O} (C : skeleton_client A G St O) x y st l st' :
  acts_hold C [x; y] st l st' ->
  exists l1 mid l2, l = l1 ++ l2 /\ act_hold C x st l1 mid /\ act_hold C y mid l2 st'.
Proof.
  intro Hacts; inversion Hacts as [|z zs start l1 mid l2 last Hhead Htail]; subst.
  exists l1, mid, l2; split; [reflexivity|split; [exact Hhead|]].
  apply holds_single_inv; exact Htail.
Qed.

Lemma label_resume_exists {A G St} (prog : stmt A G) p k n v (st : St) :
  context prog p k -> label_point prog p n = Some v ->
  exists m, resume n k st = Some m /\ machine_point m = v /\ store_of m = st.
Proof.
  intros Hctx Hlabel; unfold label_point in Hlabel.
  rewrite (context_enclosing prog p k Hctx) in Hlabel.
  pose proof (resume_target_map n k st) as Hmap; rewrite Hlabel in Hmap.
  destruct (resume n k st) as [m|] eqn:Hresume; cbn in Hmap; [|discriminate].
  exists m; split; [reflexivity|split; [congruence|eapply resume_store; exact Hresume]].
Qed.

Lemma table_out_inv {A G} (prog : stmt A G) p g ns i v xs :
  In (v, xs) (table_out prog p g ns i) ->
  exists j n, nth_error ns j = Some n /\ label_point prog p n = Some v /\
    xs = [AIndexIs g (i + j); AJump p n].
Proof.
  revert i; induction ns as [|a ns IH]; intros i Hin; [contradiction|].
  cbn in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  - unfold jump_out in Hin; destruct (label_point prog p a) as [t|] eqn:Hlabel;
      [|contradiction]; destruct Hin as [Heq|Hfalse]; [|contradiction].
    inversion Heq; subst; exists 0, a; rewrite Nat.add_0_r; repeat split; assumption || reflexivity.
  - destruct (IH (S i) Hin) as [j [n [Hnth [Hlabel Hxs]]]].
    exists (S j), n; split; [exact Hnth|split; [exact Hlabel|]].
    replace (i + S j) with (S i + j) by lia; exact Hxs.
Qed.

Lemma jump_out_inv {A G} (prog : stmt A G) p n xs v ys :
  In (v, ys) (jump_out prog p n xs) -> label_point prog p n = Some v /\ ys = xs.
Proof.
  unfold jump_out; destruct (label_point prog p n) as [t|] eqn:Hlabel; cbn; [|tauto].
  intros [Heq|Hfalse]; [inversion Heq; subst; split; reflexivity|contradiction].
Qed.

Lemma nth_error_value {X} (xs : list X) i x d :
  nth_error xs i = Some x -> nth i xs d = x.
Proof.
  revert i; induction xs as [|y xs IH]; intros [|i] Hnth; cbn in *;
    try discriminate; [congruence|apply IH; exact Hnth].
Qed.

Lemma jump_if_out_realise {A G St O} (prog : stmt A G)
    (C : skeleton_client A G St O) p k st g n v xs l st' :
  context prog p k -> sub prog p = Some (JumpIf g n) ->
  In (v, xs) (jump_out prog p n [AGuard g true; AJump p n] ++
    [(PExit p, [AGuard g false])]) -> acts_hold C xs st l st' ->
  exists m', skel_step prog C (Go p k st) l m' /\
    machine_point m' = v /\ store_of m' = st'.
Proof.
  intros Hctx Hsub Hin Hacts; apply in_app_or in Hin.
  destruct Hin as [Hin|[Heq|Hfalse]]; [| |contradiction].
  - apply jump_out_inv in Hin; destruct Hin as [Hlabel ->].
    apply holds_pair_inv in Hacts; destruct Hacts as [l1 [mid [l2 [Hl [Ha Hb]]]]].
    destruct Ha as [Hguard [-> ->]], Hb as [Hjump ->]; cbn in Hl; subst l.
    destruct (label_resume_exists prog p k n v st' Hctx Hlabel)
      as [m [Hresume [Hpoint Hstore]]].
    exists m; split; [eapply step_jump_if_taken; eassumption|split; assumption].
  - inversion Heq; subst; apply holds_single_inv in Hacts.
    destruct Hacts as [Hguard [-> ->]].
    exists (Ret p k st); split;
      [eapply step_jump_if_skipped; eassumption|split; reflexivity].
Qed.

Lemma table_out_realise {A G St O} (prog : stmt A G)
    (C : skeleton_client A G St O) p k st g ns n v xs l st' :
  context prog p k -> sub prog p = Some (JumpTable g ns n) ->
  In (v, xs) (table_out prog p g ns 0 ++
    jump_out prog p n [AIndexAtLeast g (length ns); AJump p n]) ->
  acts_hold C xs st l st' ->
  exists m', skel_step prog C (Go p k st) l m' /\
    machine_point m' = v /\ store_of m' = st'.
Proof.
  intros Hctx Hsub Hin Hacts; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  - apply table_out_inv in Hin; destruct Hin as [i [target [Hnth [Hlabel ->]]]].
    apply holds_pair_inv in Hacts; destruct Hacts as [l1 [mid [l2 [Hl [Ha Hb]]]]].
    destruct Ha as [Hguard [-> ->]], Hb as [Hjump ->]; cbn in Hl; subst l.
    pose proof (nth_error_value ns i target n Hnth) as Hvalue.
    destruct (label_resume_exists prog p k target v st' Hctx Hlabel)
      as [m [Hresume [Hpoint Hstore]]].
    exists m; split; [|split; assumption].
    eapply step_jump_table with (i := i); [exact Hsub|exact Hguard| |].
    + rewrite Hvalue; exact Hjump.
    + rewrite Hvalue; exact Hresume.
  - apply jump_out_inv in Hin; destruct Hin as [Hlabel ->].
    apply holds_pair_inv in Hacts; destruct Hacts as [l1 [mid [l2 [Hl [Ha Hb]]]]].
    destruct Ha as [[i [Hguard Hbound]] [-> ->]], Hb as [Hjump ->]; cbn in Hl; subst l.
    destruct (label_resume_exists prog p k n v st' Hctx Hlabel)
      as [m [Hresume [Hpoint Hstore]]].
    exists m; split; [|split; assumption].
    eapply step_jump_table with (i := i); [exact Hsub|exact Hguard| |].
    + rewrite nth_overflow by exact Hbound; exact Hjump.
    + rewrite nth_overflow by exact Hbound; exact Hresume.
Qed.

Lemma out_realise {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    m v xs l st' :
  machine_valid prog m -> In (v, xs) (skel_out prog (machine_point m)) ->
  acts_hold C xs (store_of m) l st' ->
  exists m', skel_step prog C m l m' /\ machine_point m' = v /\ store_of m' = st'.
Proof.
  destruct m as [p k st|p k st]; cbn [machine_valid machine_point store_of];
    intros Hctx Hin Hacts.
  - destruct (context_sub prog p k Hctx) as [s Hsub].
    cbn [skel_out] in Hin; rewrite Hsub in Hin.
    destruct s as [a|s1 s2|g s1 s2|s|s|n|g n|g ns n].
    + destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      exists (Ret p k st'); split; [eapply step_atom; [exact Hsub|]|split; reflexivity].
      apply holds_single_inv in Hacts; exact Hacts.
    + destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      apply holds_nil_inv in Hacts; destruct Hacts as [-> ->].
      eexists; split; [eapply step_seq; exact Hsub|split; reflexivity].
    + destruct Hin as [Heq|[Heq|Hfalse]]; try contradiction; inversion Heq; subst;
        apply holds_single_inv in Hacts; destruct Hacts as [Hguard [-> ->]].
      * eexists; split; [eapply step_if; [exact Hsub|exact Hguard]|split; reflexivity].
      * eexists; split; [eapply step_if; [exact Hsub|exact Hguard]|split; reflexivity].
    + destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      apply holds_nil_inv in Hacts; destruct Hacts as [-> ->].
      eexists; split; [eapply step_block; exact Hsub|split; reflexivity].
    + destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      apply holds_nil_inv in Hacts; destruct Hacts as [-> ->].
      eexists; split; [eapply step_loop; exact Hsub|split; reflexivity].
    + apply jump_out_inv in Hin; destruct Hin as [Hlabel ->].
      apply holds_single_inv in Hacts; destruct Hacts as [Hjump ->].
      destruct (label_resume_exists prog p k n v st' Hctx Hlabel)
        as [m [Hresume [Hpoint Hstore]]].
      exists m; split; [eapply step_jump; eassumption|split; assumption].
    + eapply jump_if_out_realise; eassumption.
    + eapply table_out_realise; eassumption.
  - destruct (context_locate prog p k Hctx) as [s [Hloc _]].
    cbn [skel_out] in Hin; rewrite Hloc in Hin; destruct k as [|f k]; [contradiction|].
    destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
    apply holds_nil_inv in Hacts; destruct Hacts as [-> ->].
    destruct f as [q|q|q|q].
    + exists (Go (q ++ [DSecond]) (FJoin q :: k) st); split;
        [apply step_ret_seq|split; reflexivity].
    + exists (Ret q k st); split; [apply step_ret_join|split; reflexivity].
    + exists (Ret q k st); split; [apply step_ret_block|split; reflexivity].
    + exists (Go (q ++ [DBody]) (FLoop q :: k) st); split;
        [apply step_ret_loop|split; reflexivity].
Qed.

Lemma machine_point_same_control {A G St} (prog : stmt A G) (m n : mstate St) :
  machine_valid prog m -> machine_valid prog n -> machine_point n = machine_point m ->
  match m, n with
  | Go p k _, Go q k' _ | Ret p k _, Ret q k' _ => p = q /\ k = k'
  | _, _ => False
  end.
Proof.
  destruct m, n; cbn; intros Hctx Hctx' Hpoint; inversion Hpoint; subst.
  all: split; [reflexivity|eapply context_unique; eassumption].
Qed.

Lemma skeleton_step_agrees {A G St O Fa} (Ra : agreement Fa St) (prog : stmt A G)
    (C : skeleton_client A G St O) (actb : action A G -> Fa -> Fa)
    (sigma : skel_point -> Fa) :
  (forall x a st1 l st1' st2, act_hold C x st1 l st1' -> agree Ra (actb x a) st1 st2 ->
    exists st2', act_hold C x st2 l st2' /\ agree Ra a st1' st2') ->
  step_agrees (skeleton_semantics prog C) (skeleton_view prog C) (store_agreement Ra)
    (reachable_state (skeleton_semantics prog C)) (edge_bwd prog actb) sigma.
Proof.
  intro Hact; split.
  - intros e m l m' n Hreach Hreach' Hpoint Hstep [Hout [Htarget Hacts]] Hagree.
    destruct (acts_backward_match Ra C actb Hact _ _ _ _ Hacts _ _ Hagree)
      as [st' [Hacts' Hagree']].
    assert (Hnth : nth_error (skel_out prog (from e)) (slot e) =
      Some (skel_to prog e, skel_acts prog e)).
    { apply skeleton_out_slot in Hout; destruct Hout as [Hfrom Hbound].
      rewrite skel_to_agrees, skel_acts_agrees.
      destruct (nth_error (skel_out prog (from e)) (slot e)) as [[v xs]|] eqn:Hnth;
        [reflexivity|].
      rewrite Hfrom in Hnth; apply nth_error_None in Hnth; lia. }
    assert (Hin : In (skel_to prog e, skel_acts prog e)
      (skel_out prog (machine_point n))).
    { apply skeleton_out_slot in Hout; destruct Hout as [Hfrom _].
      change (machine_point n = machine_point m) in Hpoint.
      rewrite Hpoint, <- Hfrom; apply nth_error_In in Hnth; exact Hnth. }
    destruct (out_realise prog C n (skel_to prog e) (skel_acts prog e) l st'
      (reachable_machine_valid prog C n Hreach') Hin Hacts')
      as [n' [Hstep' [Hpoint' Hstore']]].
    change (machine_point n = machine_point m) in Hpoint.
    exists n'; split; [exact Hstep'|split].
    + cbn [skeleton_view taken]; split; [rewrite Hpoint; exact Hout|split; [exact Hpoint'|]].
      rewrite Hstore'; exact Hacts'.
    + cbn [store_agreement agree]; rewrite Hstore'; exact Hagree'.
  - intros m l m' n _ _ _ _ Hfalse; contradiction.
Qed.

Lemma skeleton_ends_agree {A G St O Fa} (Ra : agreement Fa St) (prog : stmt A G)
    (C : skeleton_client A G St O) (exitf : skel_point -> Fa) :
  (forall p st1 st2, agree Ra (exitf (PEntry p)) st1 st2 ->
    (traps_at prog C p st1 <-> traps_at prog C p st2) /\
    (stops_at prog C p st1 <-> stops_at prog C p st2)) ->
  ends_agree (skeleton_semantics prog C) (skeleton_endings prog C)
    (skeleton_view prog C) (store_agreement Ra)
    (reachable_state (skeleton_semantics prog C)) exitf.
Proof.
  intros Hends m n Hreach Hreach' Hpoint Hagree.
  pose proof (reachable_machine_valid prog C m Hreach) as Hvalid.
  pose proof (reachable_machine_valid prog C n Hreach') as Hvalid'.
  pose proof (machine_point_same_control prog m n Hvalid Hvalid' Hpoint) as Hcontrol.
  destruct m as [p k st|p k st], n as [q k' st'|q k' st'];
    cbn in Hcontrol; try contradiction; destruct Hcontrol as [-> ->].
  - destruct (Hends q st st' Hagree) as [Htrap Hstop]; split; [cbn; tauto|].
    split; assumption.
  - repeat split; cbn; tauto.
Qed.

(** Backward post-solutions turn store agreement into a lock-step machine bisimulation. *)
Theorem skeleton_agreement_bisimulation {A G St O Fa} (L : lattice Fa)
    (Ra : agreement Fa St) (prog : stmt A G) (C : skeleton_client A G St O)
    (exitf : skel_point -> Fa) (actb : action A G -> Fa -> Fa) (sigma : skel_point -> Fa) :
  agreement_laws L Ra -> agreement_symmetric Ra ->
  (forall x a st1 l st1' st2, act_hold C x st1 l st1' -> agree Ra (actb x a) st1 st2 ->
     exists st2', act_hold C x st2 l st2' /\ agree Ra a st1' st2') ->
  (forall p st1 st2, agree Ra (exitf (PEntry p)) st1 st2 ->
     (traps_at prog C p st1 <-> traps_at prog C p st2) /\
     (stops_at prog C p st1 <-> stops_at prog C p st2)) ->
  post_solution L (skeleton_backward prog exitf actb) sigma ->
  bisimulation (skeleton_semantics prog C) (skeleton_endings prog C)
    (skeleton_semantics prog C) (skeleton_endings prog C)
    (agreeing (skeleton_view prog C) (store_agreement Ra)
       (reachable_state (skeleton_semantics prog C)) sigma).
Proof.
  intros HR Hsym Hact Hends Hpost.
  apply (agreement_bisimulation (skeleton_semantics prog C) (skeleton_endings prog C)
    (skeleton_view prog C) L (fun _ => store_agreement Ra)
    (reachable_state (skeleton_semantics prog C)) exitf (edge_bwd prog actb) sigma).
  - apply skeleton_view_laws_hold.
  - constructor.
    + intros a m; apply (agree_refl HR).
    + intros a b m n Hle Hagree; eapply (agree_antitone HR); eassumption.
  - intros a m n Hagree; apply Hsym; exact Hagree.
  - apply reachable_invariant.
  - apply skeleton_step_agrees; exact Hact.
  - apply skeleton_ends_agree; exact Hends.
  - exact Hpost.
Qed.

(** * Loop heads and forward ranks *)

Lemma split_last_snoc p d : split_last (p ++ [d]) = Some (p, d).
Proof.
  induction p as [|x p IH]; [reflexivity|].
  destruct p as [|y p]; cbn in *; [reflexivity|rewrite IH; reflexivity].
Qed.

Lemma split_last_spec p q d : split_last p = Some (q, d) -> p = q ++ [d].
Proof.
  revert q; induction p as [|x p IH]; intros q Hsplit; [discriminate|].
  destruct p as [|y p].
  - cbn in Hsplit; inversion Hsplit; reflexivity.
  - change (match split_last (y :: p) with
      | Some (base, last) => Some (x :: base, last)
      | None => None
      end = Some (q, d)) in Hsplit.
    destruct (split_last (y :: p)) as [[r e]|] eqn:Htail; [|discriminate].
    inversion Hsplit; subst; cbn; f_equal; apply IH; reflexivity.
Qed.

(** The loop-head test recognizes exactly the enumerated body entries. *)
Theorem is_loop_head_iff {A G} (prog : stmt A G) (n : skel_point) :
  is_loop_head prog n = true <-> In n (loop_heads prog).
Proof.
  unfold loop_heads; rewrite in_flat_map; destruct n as [p|p]; split.
  - cbn [is_loop_head]; destruct (split_last p) as [[q d]|] eqn:Hsplit;
      [destruct d|]; try discriminate.
    destruct (sub prog q) as [s|] eqn:Hsub; [destruct s|]; try discriminate.
    intros _; exists q; split.
    + apply (proj2 (positions_exact prog)); eexists; exact Hsub.
    + rewrite Hsub; cbn; left; f_equal; symmetry; apply split_last_spec; exact Hsplit.
  - intros [q [Hin Hnode]]; destruct (sub prog q) as [s|] eqn:Hsub;
      [destruct s|]; try contradiction.
    destruct Hnode as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
    cbn [is_loop_head]; rewrite split_last_snoc, Hsub; reflexivity.
  - discriminate.
  - intros [q [_ Hnode]]; destruct (sub prog q) as [s|]; [destruct s|];
      cbn in Hnode; try contradiction; destruct Hnode as [Hbad|Hfalse];
      [discriminate|contradiction].
Qed.

Lemma loop_body_head {A G} (prog : stmt A G) p s :
  sub prog p = Some (Loop s) -> is_loop_head prog (PEntry (p ++ [DBody])) = true.
Proof.
  intro Hsub; cbn [is_loop_head]; rewrite split_last_snoc, Hsub; reflexivity.
Qed.

(** Spans reserve two ranks for a statement's entry and exit. *)
Fixpoint statement_span {A G} (s : stmt A G) : nat :=
  match s with
  | Seq s1 s2 | If _ s1 s2 => 2 + statement_span s1 + statement_span s2
  | Block s | Loop s => 2 + statement_span s
  | _ => 2
  end.

(** A second binary child begins after the first child's complete span. *)
Definition child_offset {A G} (s : stmt A G) (d : dir) : nat :=
  match s, d with
  | Seq s1 _, DSecond | If _ s1 _, DSecond => 1 + statement_span s1
  | _, _ => 1
  end.

(** Entry ranks follow the finite tree order, placing each owner before its children. *)
Fixpoint entry_rank {A G} (s : stmt A G) (p : position) : nat :=
  match p with
  | [] => 0
  | d :: p =>
    match child s d with
    | Some t => child_offset s d + entry_rank t p
    | None => 0
    end
  end.

(** Exit ranks place each owner after its complete subtree. *)
Definition exit_rank {A G} (prog : stmt A G) (p : position) : nat :=
  entry_rank prog p +
    match sub prog p with
    | Some s => statement_span s - 1
    | None => 0
    end.

(** The point order lists entry, children from left to right, and exit. *)
Definition point_rank {A G} (prog : stmt A G) (v : skel_point) : nat :=
  match v with
  | PEntry p => entry_rank prog p
  | PExit p => exit_rank prog p
  end.

Lemma statement_span_positive {A G} (s : stmt A G) : 2 <= statement_span s.
Proof.
  destruct s; cbn; lia.
Qed.

Lemma entry_rank_app {A G} (prog : stmt A G) p s q :
  sub prog p = Some s -> entry_rank prog (p ++ q) = entry_rank prog p + entry_rank s q.
Proof.
  revert prog s; induction p as [|d p IH]; intros prog s Hsub; cbn in *.
  - inversion Hsub; reflexivity.
  - destruct (child prog d) as [t|] eqn:Hchild; [|discriminate].
    rewrite (IH t s Hsub); lia.
Qed.

Lemma child_span_bounds {A G} (s t : stmt A G) d :
  child s d = Some t -> 0 < child_offset s d /\
    child_offset s d + statement_span t < statement_span s.
Proof.
  destruct s; destruct d; cbn; intro Hchild; try discriminate;
    inversion Hchild; subst; cbn; lia.
Qed.

Lemma child_rank_bounds {A G} (prog : stmt A G) p s d t :
  sub prog p = Some s -> child s d = Some t ->
  entry_rank prog p < entry_rank prog (p ++ [d]) /\
    exit_rank prog (p ++ [d]) < exit_rank prog p.
Proof.
  intros Hsub Hchild; unfold exit_rank.
  rewrite (sub_child prog p s d Hsub), Hchild, Hsub, (entry_rank_app prog p s [d] Hsub).
  cbn [entry_rank]; rewrite Hchild; cbn [entry_rank].
  pose proof (child_span_bounds s t d Hchild) as Hbounds.
  pose proof (statement_span_positive t); pose proof (statement_span_positive s); lia.
Qed.

Lemma entry_before_exit {A G} (prog : stmt A G) p :
  (exists s, sub prog p = Some s) -> entry_rank prog p < exit_rank prog p.
Proof.
  intros [s Hsub]; unfold exit_rank; rewrite Hsub.
  pose proof (statement_span_positive s); lia.
Qed.

Lemma seq_first_before_second {A G} (prog : stmt A G) p s1 s2 :
  sub prog p = Some (Seq s1 s2) ->
  exit_rank prog (p ++ [DFirst]) < entry_rank prog (p ++ [DSecond]).
Proof.
  intro Hsub; unfold exit_rank; rewrite (sub_child prog p _ DFirst Hsub).
  rewrite (entry_rank_app prog p _ [DFirst] Hsub),
    (entry_rank_app prog p _ [DSecond] Hsub); cbn.
  pose proof (statement_span_positive s1); lia.
Qed.

(** A continuation either goes to a loop head or lies after the current subtree. *)
Definition continuation_after {A G} (prog : stmt A G) p (f : frame) : Prop :=
  is_loop_head prog (return_point f) = true \/
    exit_rank prog p < point_rank prog (return_point f).

Lemma context_continuations {A G} (prog : stmt A G) p k :
  context prog p k -> Forall (continuation_after prog p) k.
Proof.
  intro Hctx; induction Hctx as [|p k s d t Hctx IH Hsub Hchild]; [constructor|].
  pose proof (child_rank_bounds prog p s d t Hsub Hchild) as [_ Hexit].
  constructor.
  - destruct s; destruct d; cbn in Hchild; try discriminate; cbn [child_frame].
    + right; exact (seq_first_before_second prog p s1 s2 Hsub).
    + right; exact Hexit.
    + right; exact Hexit.
    + right; exact Hexit.
    + right; exact Hexit.
    + left; eapply loop_body_head; exact Hsub.
  - eapply Forall_impl; [|exact IH].
    intros f [Hloop|Hrank]; [left; exact Hloop|right; lia].
Qed.

Lemma context_entry_continuations {A G} (prog : stmt A G) p k :
  context prog p k -> Forall (fun f => is_loop_head prog (return_point f) = true \/
    entry_rank prog p < point_rank prog (return_point f)) k.
Proof.
  intro Hctx; pose proof (context_continuations prog p k Hctx) as Hall.
  pose proof (entry_before_exit prog p (context_sub prog p k Hctx)) as Hentry.
  eapply Forall_impl; [|exact Hall].
  intros f [Hloop|Hrank]; [left; exact Hloop|right; lia].
Qed.

Lemma enclosing_after {A G} (prog s : stmt A G) base p k :
  context prog base k -> sub prog base = Some s ->
  Forall (fun f => is_loop_head prog (return_point f) = true \/
    entry_rank prog (base ++ p) < point_rank prog (return_point f))
    (enclosing_from s base p k).
Proof.
  revert s base k; induction p as [|d p IH]; intros s base k Hctx Hsub.
  - rewrite app_nil_r; apply context_entry_continuations; exact Hctx.
  - cbn [enclosing_from]; destruct (child s d) as [t|] eqn:Hchild.
    + replace (base ++ d :: p) with ((base ++ [d]) ++ p) by
        (rewrite <- app_assoc; reflexivity).
      eapply IH; [eapply context_child; eassumption|].
      rewrite (sub_child prog base s d Hsub); exact Hchild.
    + assert (Hrank : entry_rank prog (base ++ d :: p) = entry_rank prog base).
      { rewrite (entry_rank_app prog base s (d :: p) Hsub).
        cbn [entry_rank]; rewrite Hchild; lia. }
      rewrite Hrank; pose proof (context_entry_continuations prog base k Hctx) as Hall.
      destruct s; cbn; try exact Hall.
      * constructor; [right; apply entry_before_exit; eexists; exact Hsub|exact Hall].
      * constructor; [left; eapply loop_body_head; exact Hsub|exact Hall].
Qed.

Lemma resume_target_rank {A G} (prog : stmt A G) low k n v :
  Forall (fun f => is_loop_head prog (return_point f) = true \/
    low < point_rank prog (return_point f)) k -> resume_target n k = Some v ->
  is_loop_head prog v = true \/ low < point_rank prog v.
Proof.
  revert n; induction k as [|f k IH]; intros n Hall Htarget; [discriminate|].
  inversion Hall as [|? ? Hhead Htail]; subst; destruct f; cbn in Htarget;
    try (eapply IH; eassumption).
  all: destruct n; [inversion Htarget; subst; exact Hhead|eapply IH; eassumption].
Qed.

Lemma label_point_after {A G} (prog : stmt A G) p n v :
  label_point prog p n = Some v ->
  is_loop_head prog v = true \/ entry_rank prog p < point_rank prog v.
Proof.
  intro Htarget; eapply resume_target_rank; [|exact Htarget].
  exact (enclosing_after prog prog [] p [] context_root eq_refl).
Qed.

Lemma skel_out_source_valid {A G} (prog : stmt A G) u v xs :
  In (v, xs) (skel_out prog u) -> point_valid prog u.
Proof.
  destruct u as [p|p]; cbn [skel_out].
  - destruct (sub prog p) as [s|] eqn:Hsub; [|cbn; tauto].
    intros _; eapply sub_context; exact Hsub.
  - destruct (locate prog p) as [[s k]|] eqn:Hloc; [|cbn; tauto].
    intros _; exists k; exact (proj1 (locate_context prog p s k Hloc)).
Qed.

Lemma jump_out_after {A G} (prog : stmt A G) p n xs v ys :
  In (v, ys) (jump_out prog p n xs) ->
  is_loop_head prog v = true \/ entry_rank prog p < point_rank prog v.
Proof.
  intro Hin; apply jump_out_inv in Hin; destruct Hin as [Hlabel _].
  eapply label_point_after; exact Hlabel.
Qed.

Lemma table_out_after {A G} (prog : stmt A G) p g ns i v xs :
  In (v, xs) (table_out prog p g ns i) ->
  is_loop_head prog v = true \/ entry_rank prog p < point_rank prog v.
Proof.
  intro Hin; apply table_out_inv in Hin; destruct Hin as [j [n [_ [Hlabel _]]]].
  eapply label_point_after; exact Hlabel.
Qed.

Lemma skel_out_after {A G} (prog : stmt A G) u v xs :
  In (v, xs) (skel_out prog u) ->
  is_loop_head prog v = true \/ point_rank prog u < point_rank prog v.
Proof.
  intro Hin; pose proof (skel_out_source_valid prog u v xs Hin) as Hvalid.
  destruct u as [p|p]; destruct Hvalid as [k Hctx]; cbn [skel_out] in Hin.
  - destruct (context_sub prog p k Hctx) as [s Hsub]; rewrite Hsub in Hin.
    destruct s as [a|s1 s2|g s1 s2|s|s|n|g n|g ns n].
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
      right; apply entry_before_exit; eexists; exact Hsub.
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
      right; exact (proj1 (child_rank_bounds prog p _ DFirst s1 Hsub eq_refl)).
    + destruct Hin as [Heq|[Heq|Hfalse]]; try contradiction; inversion Heq; subst; right.
      * exact (proj1 (child_rank_bounds prog p _ DFirst s1 Hsub eq_refl)).
      * exact (proj1 (child_rank_bounds prog p _ DSecond s2 Hsub eq_refl)).
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
      right; exact (proj1 (child_rank_bounds prog p _ DBody s Hsub eq_refl)).
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
      left; eapply loop_body_head; exact Hsub.
    + eapply jump_out_after; exact Hin.
    + apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hfalse]].
      * eapply jump_out_after; exact Hin.
      * inversion Heq; subst; right; apply entry_before_exit; eexists; exact Hsub.
      * contradiction.
    + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      * eapply table_out_after; exact Hin.
      * eapply jump_out_after; exact Hin.
  - destruct (context_locate prog p k Hctx) as [s [Hloc _]]; rewrite Hloc in Hin.
    destruct k as [|f k]; [contradiction|].
    destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
    pose proof (context_continuations prog p (f :: k) Hctx) as Hall.
    inversion Hall; assumption.
Qed.

Lemma skeleton_edge_after {A G} (prog : stmt A G) e :
  In e (Graph.out (skeleton_graph prog) (from e)) ->
  is_loop_head prog (skel_to prog e) = true \/
    point_rank prog (from e) < point_rank prog (skel_to prog e).
Proof.
  intro Hedge; apply skeleton_out_slot in Hedge; destruct Hedge as [_ Hbound].
  rewrite skel_to_agrees; destruct (nth_error (skel_out prog (from e)) (slot e))
    as [[v xs]|] eqn:Hnth.
  - eapply skel_out_after; apply nth_error_In in Hnth; exact Hnth.
  - apply nth_error_None in Hnth; lia.
Qed.

Lemma path_start_source {N E} (g : Graph.t N E) u e es v :
  path g u (e :: es) v -> u = Graph.source g e.
Proof.
  intro Hpath; inversion Hpath; reflexivity.
Qed.

Lemma path_targets_false {N E} (g : Graph.t N E) (W : N -> bool) u es v :
  path g u es v -> (forall e, In e es -> W (Graph.source g e) = false) ->
  W v = false -> forall e, In e es -> W (Graph.target g e) = false.
Proof.
  intro Hpath; induction Hpath as [u|a es v Hedge Hpath IH]; intros Hsources Hlast e Hin;
    [contradiction|].
  destruct Hin as [<-|Hin].
  - destruct es as [|b es].
    + inversion Hpath; subst; exact Hlast.
    + rewrite (path_start_source g _ b es v Hpath); apply Hsources; right; left; reflexivity.
  - apply IH; [intros b Hb; apply Hsources; right; exact Hb|exact Hlast|exact Hin].
Qed.

Lemma skeleton_path_rank {A G} (prog : stmt A G) u es v :
  path (skeleton_graph prog) u es v ->
  (forall e, In e es -> is_loop_head prog (skel_to prog e) = false) ->
  point_rank prog u <= point_rank prog v /\
    (es <> [] -> point_rank prog u < point_rank prog v).
Proof.
  intro Hpath; induction Hpath as [u|e es v Hedge Hpath IH]; intro Htargets.
  - split; [lia|tauto].
  - destruct (IH ltac:(intros a Ha; apply Htargets; right; exact Ha)) as [Hle _].
    destruct (skeleton_edge_after prog e Hedge) as [Hloop|Hrank].
    + pose proof (Htargets e (or_introl eq_refl)); congruence.
    + change (point_rank prog (skel_to prog e) <= point_rank prog v) in Hle.
      change (point_rank prog (from e) <= point_rank prog v /\
        (e :: es <> [] -> point_rank prog (from e) < point_rank prog v)).
      split; [lia|intros _; lia].
Qed.

(** Every nonempty cycle visits a loop head. *)
Theorem skeleton_cut_points {A G} (prog : stmt A G) :
  meets_every_cycle (skeleton_graph prog) (is_loop_head prog).
Proof.
  intros v es Hnonempty Hpath.
  destruct (existsb (fun e => is_loop_head prog (from e)) es) eqn:Hheads.
  - apply existsb_exists in Hheads; exact Hheads.
  - assert (Hsources : forall e, In e es -> is_loop_head prog (from e) = false).
    { intros e Hin; destruct (is_loop_head prog (from e)) eqn:Hhead; [|reflexivity].
      assert (existsb (fun e => is_loop_head prog (from e)) es = true).
      { apply existsb_exists; exists e; split; assumption. }
      congruence. }
    assert (Hlast : is_loop_head prog v = false).
    { destruct es as [|e es]; [contradiction|].
      rewrite (path_start_source _ v e es v Hpath); apply Hsources; left; reflexivity. }
    pose proof (path_targets_false _ _ _ _ _ Hpath Hsources Hlast) as Htargets.
    destruct (skeleton_path_rank prog v es v Hpath Htargets) as [_ Hstrict].
    specialize (Hstrict Hnonempty); lia.
Qed.

(** Loop heads cut the static dependency cycles of the forward generator. *)
Theorem skeleton_forward_cuts {A G Fa} (L : lattice Fa) (prog : stmt A G) (init : Fa)
    (act : action A G -> Fa -> Fa) :
  cuts_every_cycle (skeleton_forward_static L prog init act) (is_loop_head prog).
Proof.
  apply forward_cuts_every_cycle; [apply skeleton_graph_wf|apply skeleton_cut_points].
Qed.

(** Loop heads also cut the reversed dependencies of the backward generator. *)
Theorem skeleton_backward_cuts {A G Fa} (prog : stmt A G) (exitf : skel_point -> Fa)
    (actb : action A G -> Fa -> Fa) :
  cuts_every_cycle (skeleton_backward_static prog exitf actb) (is_loop_head prog).
Proof.
  apply backward_cuts_every_cycle; [apply skeleton_graph_wf|apply skeleton_cut_points].
Qed.
