(** * Full SSA graph and historical allocation sites

    This file connects framed executions to a finite program graph and byte memory.
    For example, freeing allocation 0 preserves its site while making its bytes unreadable.
    Builds on: ExamplesSsaSemantics, ExamplesSsaBridge, ViewsGraph and ViewsMemory. *)

From Stdlib Require Import List ZArith Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemory.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaBridge.
Import List.ListNotations.
Local Open Scope nat_scope.

(** A full point retains the function identity as well as the local program counter. *)
Definition full_node : Type := (func * label * nat)%type.

(** A full edge distinguishes parallel control-flow occurrences by their slot. *)
Record full_edge : Type := FullEdge {
  fsrc : full_node;
  fdst : full_node;
  fslot : nat
}.

Definition full_node_encoding : encoding full_node :=
  pair_encoding (pair_encoding nat_encoding nat_encoding) nat_encoding.

Definition full_edge_encoding : encoding full_edge.
Proof.
  pose (E := pair_encoding (pair_encoding full_node_encoding full_node_encoding) nat_encoding).
  refine (Encoding _ (fun e => encode E ((fsrc e, fdst e), fslot e)) _).
  intros [src dst slot] [src' dst' slot'] Heq.
  apply (encode_injective E) in Heq; cbn in Heq; injection Heq as <- <- <-; reflexivity.
Defined.

Definition full_frame_point (fr : sframe) : full_node := (ffunc fr, flabel fr, fpc fr).

Definition full_point (s : state) : full_node :=
  match stack s with
  | fr :: _ => full_frame_point fr
  | [] => (0, 0, 0)
  end.

(** * Prepared full-program graph *)

Definition full_program_blocks (P : program) : list (func * label * ssa_block) :=
  flat_map (fun ffd => map (fun lb => (fst ffd, fst lb, snd lb)) (blocks (snd ffd)))
    (funcs P).

Definition full_nodes_of (bs : list (func * label * ssa_block)) : list full_node :=
  flat_map (fun flb =>
    map (fun pc => (fst (fst flb), snd (fst flb), pc))
      (seq 0 (S (S (length (bbody (snd flb))))))) bs.

Definition full_raw_nodes (P : program) : list full_node :=
  full_nodes_of (full_program_blocks P).

Definition full_node_set (P : program) : FinSet.t full_node :=
  FinSet.of_list full_node_encoding (full_raw_nodes P).

Definition full_entries (P : program) : list full_node :=
  map (fun ffd => (fst ffd, fentry (snd ffd), 0)) (funcs P).

(** Direct entries and all possible return continuations are prepared before block traversal.
    Indirect calls conservatively include every program entry; return edges include every
    syntactic call continuation. Parallel branch and switch occurrences retain their own slots. *)
Definition full_entry_index (P : program) : Map.t func fdef := first_index (funcs P).

Definition full_continuations_of (bs : list (func * label * ssa_block)) : list full_node :=
  flat_map (fun flb =>
    match bterm (snd flb) with
    | TCall _ _ cont => [(fst (fst flb), cont, 0)]
    | _ => []
    end) bs.

Definition full_continuations (P : program) : list full_node :=
  full_continuations_of (full_program_blocks P).

Definition full_call_targets (entries : list full_node) (direct : Map.t func fdef)
    (c : callee) : list full_node :=
  match c with
  | CDirect f =>
    match Map.get nat_encoding f direct with
    | Some fd => [(f, fentry fd, 0)]
    | None => []
    end
  | CIndirect _ _ _ => entries
  end.

Fixpoint full_number {A} (start : nat) (xs : list A) : list (nat * A) :=
  match xs with
  | [] => []
  | x :: rest => (start, x) :: full_number (S start) rest
  end.

Definition full_block_edges (entries continuations : list full_node)
    (direct : Map.t func fdef) (flb : func * label * ssa_block) : list full_edge :=
  let f := fst (fst flb) in
  let l := snd (fst flb) in
  let b := snd flb in
  let len := length (bbody b) in
  map (fun pc => FullEdge (f, l, pc) (f, l, S pc) 0) (seq 0 len) ++
  match bterm b with
  | TCall c _ _ =>
    map (fun target => FullEdge (f, l, len) target 0)
      (full_call_targets entries direct c)
  | TRet _ =>
    FullEdge (f, l, len) (f, l, S len) 0 ::
      map (fun target => FullEdge (f, l, len) target 0) continuations
  | t =>
    map (fun slot_edge =>
      FullEdge (f, l, len) (f, fst (snd slot_edge), 0) (fst slot_edge))
      (full_number 0 (term_edges t))
  end.

Definition full_raw_edges (P : program) : list full_edge :=
  let entries := full_entries P in
  let continuations := full_continuations P in
  let direct := full_entry_index P in
  flat_map (full_block_edges entries continuations direct) (full_program_blocks P).

Definition full_valid_edges (P : program) : list full_edge :=
  let nodes := full_node_set P in
  filter (fun e => FinSet.mem full_node_encoding (fdst e) nodes) (full_raw_edges P).

Definition full_graph (P : program) : Graph.t full_node full_edge :=
  let bs := full_program_blocks P in
  let nodes := FinSet.of_list full_node_encoding (full_nodes_of bs) in
  let direct := full_entry_index P in
  let roots := match Map.get nat_encoding (main P) direct with
    | Some fd => [(main P, fentry fd, 0)]
    | None => []
    end in
  let entries := full_entries P in
  let continuations := full_continuations_of bs in
  let edges := filter (fun e => FinSet.mem full_node_encoding (fdst e) nodes)
    (flat_map (full_block_edges entries continuations direct) bs) in
  Graph.Make
    (filter (fun n => FinSet.mem full_node_encoding n nodes) roots)
    (FinSet.elements nodes)
    (ssa_get full_node_encoding
      (ssa_outgoing_index full_node_encoding fsrc (map (fun e => (e, e)) edges)) [])
    fsrc fdst.

(** The slot is determined by the actual source instruction or selected terminator occurrence. *)
Definition full_selected_slot (P : program) (s : state) (slot : nat) : Prop :=
  match stack s with
  | [] => False
  | fr :: _ =>
    (exists i, at_instr P fr i /\ slot = 0) \/
    (exists t, at_term P fr t /\ ssa_term_slot (fenv fr) t = Some slot)
  end.

(** Every classified step takes an edge, including calls, returns and observable final returns. *)
Definition ssa_full_view (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    : graph_view state event full_node full_edge :=
  let graph := full_graph P in
  GraphView graph full_point
    (fun s _ t e => In e (Graph.out graph (full_point s)) /\
      fdst e = full_point t /\ full_selected_slot P s (fslot e))
    (fun _ _ _ => False).

Lemma full_node_set_wf P : FinSet.wf full_node_encoding (full_node_set P).
Proof.
  unfold full_node_set, FinSet.of_list.
  apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

Lemma full_nodes_member P n :
  In n (Graph.nodes (full_graph P)) <-> In n (full_raw_nodes P).
Proof.
  change (In n (FinSet.elements (full_node_set P)) <-> In n (full_raw_nodes P)).
  rewrite (FinSet.elements_spec full_node_encoding n _ (full_node_set_wf P)).
  apply FinSet.of_list_spec.
Qed.

Lemma full_out_member P n e :
  In e (Graph.out (full_graph P) n) <-> In e (full_valid_edges P) /\ fsrc e = n.
Proof.
  change (In e (ssa_get full_node_encoding
    (ssa_outgoing_index full_node_encoding fsrc
      (map (fun edge => (edge, edge)) (full_valid_edges P))) [] n) <->
    In e (full_valid_edges P) /\ fsrc e = n).
  rewrite ssa_outgoing_member; split.
  - intros [p [Hrow Hsource]]; apply in_map_iff in Hrow.
    destruct Hrow as [edge [Heq Hin]]; injection Heq as <- <-; split; assumption.
  - intros [Hin Hsource]; exists e; split; [|exact Hsource].
    apply in_map_iff; exists e; split; [reflexivity|exact Hin].
Qed.

Lemma full_graph_wf P : graph_wf (full_graph P).
Proof.
  constructor.
  - apply FinSet.elements_nodup with (E := full_node_encoding); apply full_node_set_wf.
  - intros n Hin; apply filter_In in Hin as [_ Hmem].
    apply (FinSet.elements_spec full_node_encoding n _ (full_node_set_wf P)); exact Hmem.
  - intros n e Hin; apply full_out_member in Hin; exact (proj2 Hin).
  - intros n e Hnode Hin; apply full_out_member in Hin as [Hin _].
    apply filter_In in Hin as [_ Hmem].
    apply (FinSet.elements_spec full_node_encoding (fdst e) _ (full_node_set_wf P)).
    exact Hmem.
Qed.

Lemma full_block_member P f fd l b :
  find_func P f = Some fd -> find_block fd l = Some b ->
  In (f, l, b) (full_program_blocks P).
Proof.
  intros Hfunction Hblock; apply in_flat_map; exists (f, fd); split.
  - apply first_index_sound; exact Hfunction.
  - apply in_map_iff; exists (l, b); split; [reflexivity|].
    apply first_index_sound; exact Hblock.
Qed.

Lemma full_node_at P f fd l b pc :
  find_func P f = Some fd -> find_block fd l = Some b -> pc <= S (length (bbody b)) ->
  In (f, l, pc) (Graph.nodes (full_graph P)).
Proof.
  intros Hfunction Hblock Hpc; apply full_nodes_member, in_flat_map.
  exists (f, l, b); split; [eapply full_block_member; eassumption|].
  apply in_map_iff; exists pc; split; [reflexivity|apply in_seq; cbn; lia].
Qed.

Lemma full_advance_node P fr i env :
  at_instr P fr i -> In (full_frame_point (advance fr env)) (Graph.nodes (full_graph P)).
Proof.
  intros [fd [b [Hfunction [Hblock Hnth]]]].
  unfold full_frame_point; cbn [advance].
  apply (full_node_at P (ffunc fr) fd (flabel fr) b (S (fpc fr)) Hfunction Hblock).
  assert (Hbound : fpc fr < length (bbody b)).
  { apply nth_error_Some; rewrite Hnth; discriminate. }
  lia.
Qed.

Lemma full_jump_node P fr l vs env :
  jump_env P fr l vs = Some env ->
  In (full_frame_point (enter fr l env)) (Graph.nodes (full_graph P)).
Proof.
  unfold jump_env; destruct (find_func P (ffunc fr)) as [fd|] eqn:Hfunction;
    [|discriminate].
  destruct (find_block fd l) as [b|] eqn:Hblock; [|discriminate].
  intro Hbind; unfold full_frame_point; cbn [enter].
  apply (full_node_at P (ffunc fr) fd l b 0 Hfunction Hblock); lia.
Qed.

Lemma full_raw_advance P fr i env :
  at_instr P fr i ->
  In (FullEdge (full_frame_point fr) (full_frame_point (advance fr env)) 0)
    (full_raw_edges P).
Proof.
  intros [fd [b [Hfunction [Hblock Hnth]]]].
  unfold full_raw_edges; apply in_flat_map; exists (ffunc fr, flabel fr, b); split.
  - eapply full_block_member; eassumption.
  - unfold full_block_edges, full_frame_point; cbn [fst snd advance].
    apply in_or_app; left; apply in_map_iff; exists (fpc fr); split; [reflexivity|].
    apply in_seq; split; [lia|].
    apply nth_error_Some; rewrite Hnth; discriminate.
Qed.

Lemma full_number_member {A} start (xs : list A) i x :
  nth_error xs i = Some x -> In (start + i, x) (full_number start xs).
Proof.
  revert start i; induction xs as [|a xs IH]; intros start [|i] Hnth;
    cbn [nth_error] in Hnth; try discriminate.
  - injection Hnth as <-; cbn [full_number]; left; f_equal; lia.
  - cbn [full_number]; right; replace (start + S i) with (S start + i) by lia.
    apply IH; exact Hnth.
Qed.

Lemma full_raw_transfer P fr term slot l args env :
  at_term P fr term ->
  (forall c xs cont, term <> TCall c xs cont) -> (forall x, term <> TRet x) ->
  nth_error (term_edges term) slot = Some (l, args) ->
  In (FullEdge (full_frame_point fr) (full_frame_point (enter fr l env)) slot)
    (full_raw_edges P).
Proof.
  intros [fd [b [Hfunction [Hblock [Hpc Hterm]]]]] Hcall Hreturn Hnth.
  unfold full_raw_edges; apply in_flat_map; exists (ffunc fr, flabel fr, b); split.
  - eapply full_block_member; eassumption.
  - unfold full_block_edges, full_frame_point; cbn [fst snd enter].
    apply in_or_app; right; rewrite Hterm.
    destruct term; try solve [exfalso; eapply Hcall; reflexivity];
      try solve [exfalso; eapply Hreturn; reflexivity];
      apply in_map_iff; exists (slot, (l, args)); split.
    all: try (cbn; rewrite Hpc; reflexivity).
    all: replace slot with (0 + slot) at 1 by lia; apply full_number_member; exact Hnth.
Qed.

Lemma full_callee_member P env c f fd b :
  callee_def P env c = Some (f, fd, b) ->
  In (f, fentry fd, 0) (full_call_targets (full_entries P) (full_entry_index P) c).
Proof.
  intro Hcallee.
  destruct (callee_def_target P env c f fd b Hcallee) as [Hfunction [Hblock Hsignature]].
  destruct c as [g|x ps r].
  - unfold callee_def in Hcallee.
    destruct (find_func P g) as [gd|] eqn:Hg; [|discriminate].
    destruct (find_block gd (fentry gd)) as [gb|]; [|discriminate].
    injection Hcallee as <- <- <-.
    cbn [full_call_targets full_entry_index]; change (In (g, fentry gd, 0)
      (match find_func P g with Some d => [(g, fentry d, 0)] | None => [] end)).
    rewrite Hg; left; reflexivity.
  - cbn [full_call_targets]; unfold full_entries; apply in_map_iff.
    exists (f, fd); split; [reflexivity|apply first_index_sound; exact Hfunction].
Qed.

Lemma full_raw_call P fr c args cont env f fd b :
  at_term P fr (TCall c args cont) -> callee_def P env c = Some (f, fd, b) ->
  In (FullEdge (full_frame_point fr) (f, fentry fd, 0) 0) (full_raw_edges P).
Proof.
  intros [source [block [Hfunction [Hblock [Hpc Hterm]]]]] Hcallee.
  unfold full_raw_edges; apply in_flat_map; exists (ffunc fr, flabel fr, block); split.
  - eapply full_block_member; eassumption.
  - unfold full_block_edges, full_frame_point; cbn [fst snd].
    apply in_or_app; right; rewrite Hterm; apply in_map_iff.
    exists (f, fentry fd, 0); split; [rewrite Hpc; reflexivity|].
    eapply full_callee_member; exact Hcallee.
Qed.

Lemma full_continuation_member P fr c args cont :
  at_term P fr (TCall c args cont) ->
  In (ffunc fr, cont, 0) (full_continuations P).
Proof.
  intros [fd [b [Hfunction [Hblock [Hpc Hterm]]]]].
  unfold full_continuations; apply in_flat_map; exists (ffunc fr, flabel fr, b); split.
  - eapply full_block_member; eassumption.
  - cbn [fst snd]; rewrite Hterm; left; reflexivity.
Qed.

Lemma full_raw_return P fr x target :
  at_term P fr (TRet x) ->
  (target = full_frame_point (advance fr (fenv fr)) \/ In target (full_continuations P)) ->
  In (FullEdge (full_frame_point fr) target 0) (full_raw_edges P).
Proof.
  intros [fd [b [Hfunction [Hblock [Hpc Hterm]]]]] Htarget.
  unfold full_raw_edges; apply in_flat_map; exists (ffunc fr, flabel fr, b); split.
  - eapply full_block_member; eassumption.
  - unfold full_block_edges, full_frame_point; cbn [fst snd]; apply in_or_app; right.
    rewrite Hterm; destruct Htarget as [->|Htarget].
    + left; unfold full_frame_point, advance; cbn [ffunc flabel fpc].
      rewrite Hpc; reflexivity.
    + right; apply in_map_iff; exists target; split; [rewrite Hpc; reflexivity|exact Htarget].
Qed.

Lemma full_valid_member P e :
  In e (full_raw_edges P) -> In (fdst e) (Graph.nodes (full_graph P)) ->
  In e (full_valid_edges P).
Proof.
  intros Hedge Hnode; apply filter_In; split; [exact Hedge|].
  apply (FinSet.elements_spec full_node_encoding (fdst e) _ (full_node_set_wf P)).
  exact Hnode.
Qed.

Lemma full_taken_make ext P lim s tr t slot :
  In (FullEdge (full_point s) (full_point t) slot) (full_raw_edges P) ->
  In (full_point t) (Graph.nodes (full_graph P)) -> full_selected_slot P s slot ->
  taken (ssa_full_view ext P lim) s tr t (FullEdge (full_point s) (full_point t) slot).
Proof.
  intros Hedge Htarget Hslot; split; [|split; [reflexivity|exact Hslot]].
  apply full_out_member; split; [apply full_valid_member; assumption|reflexivity].
Qed.

Lemma full_instruction_taken ext P lim fr rest m nb tr env m' nb' i :
  at_instr P fr i ->
  exists e, taken (ssa_full_view ext P lim) (State (fr :: rest) m nb) tr
    (State (advance fr env :: rest) m' nb') e.
Proof.
  intro Hat; eexists; apply full_taken_make.
  - apply full_raw_advance with (i := i); exact Hat.
  - apply full_advance_node with (i := i); exact Hat.
  - left; exists i; split; [exact Hat|reflexivity].
Qed.

Lemma full_transfer_taken ext P lim fr rest m nb tr term slot l args cs env :
  at_term P fr term ->
  (forall c xs cont, term <> TCall c xs cont) -> (forall x, term <> TRet x) ->
  nth_error (term_edges term) slot = Some (l, args) ->
  ssa_term_slot (fenv fr) term = Some slot -> jump_env P fr l cs = Some env ->
  exists e, taken (ssa_full_view ext P lim) (State (fr :: rest) m nb) tr
    (State (enter fr l env :: rest) m nb) e.
Proof.
  intros Hat Hcall Hreturn Hnth Hslot Hjump.
  eexists; apply full_taken_make.
  - eapply full_raw_transfer; eassumption.
  - eapply full_jump_node; exact Hjump.
  - right; exists term; split; assumption.
Qed.

Lemma full_call_taken ext P lim fr rest m nb tr c args cont f fd b env :
  at_term P fr (TCall c args cont) ->
  callee_def P (fenv fr) c = Some (f, fd, b) ->
  exists e, taken (ssa_full_view ext P lim) (State (fr :: rest) m nb) tr
    (State (SFrame f (fentry fd) 0 env 0 ::
      SFrame (ffunc fr) (flabel fr) (fpc fr) (fenv fr) cont :: rest) m nb) e.
Proof.
  intros Hat Hcallee; eexists; apply full_taken_make.
  - cbn [full_point full_frame_point]; eapply full_raw_call; eassumption.
  - destruct (callee_def_target P (fenv fr) c f fd b Hcallee)
      as [Hfunction [Hblock Hsignature]].
    cbn [full_point full_frame_point].
    apply (full_node_at P f fd (fentry fd) b 0 Hfunction Hblock); lia.
  - right; exists (TCall c args cont); split; [exact Hat|reflexivity].
Qed.

Lemma full_return_taken ext P lim fr caller rest m nb tr x v env :
  at_term P fr (TRet x) -> return_link P fr caller ->
  jump_env P caller (fret caller) [v] = Some env ->
  exists e, taken (ssa_full_view ext P lim) (State (fr :: caller :: rest) m nb) tr
    (State (enter caller (fret caller) env :: rest) m nb) e.
Proof.
  intros Hat [fd [c [args [cont [ps [Hfunction [Hcall [Hcont Hsig]]]]]]]] Hjump.
  eexists; apply full_taken_make.
  - apply full_raw_return with (x := x); [exact Hat|right].
    change (In (ffunc caller, fret caller, 0) (full_continuations P)); rewrite Hcont.
    exact (full_continuation_member P caller c args cont Hcall).
  - eapply full_jump_node; exact Hjump.
  - right; exists (TRet x); split; [exact Hat|reflexivity].
Qed.

Lemma full_main_return_taken ext P lim fr m nb tr x :
  at_term P fr (TRet x) ->
  exists e, taken (ssa_full_view ext P lim) (State [fr] m nb) tr
    (State [advance fr (fenv fr)] m nb) e.
Proof.
  intro Hat; eexists; apply full_taken_make.
  - apply full_raw_return with (x := x); [exact Hat|left; reflexivity].
  - destruct Hat as [fd [b [Hfunction [Hblock [Hpc Hterm]]]]].
    cbn [full_point full_frame_point advance].
    apply (full_node_at P (ffunc fr) fd (flabel fr) b (S (fpc fr)) Hfunction Hblock).
    lia.
  - right; exists (TRet x); split; [exact Hat|reflexivity].
Qed.

(** Every reachable transition is represented by its selected full-graph edge. *)
Lemma full_step_covered ext P lim s tr t :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  step_s ext P lim s tr t -> exists e, taken (ssa_full_view ext P lim) s tr t e.
Proof.
  intros Hwf Hreachable Hstep; destruct Hstep as
    [fr rest m nb x o args cs v Hat Hread Heval
    |fr rest m nb x n z Hat Hvalue Hlimit
    |fr rest m nb p b mb Hat Hvalue Hblock Hlive
    |fr rest m nb x ty sz p b off mb v Hat Hvalue Hblock Hload
    |fr rest m nb sz p x b off mb v mb' Hat Hpointer Hvalue Hblock Hstore
    |fr rest m nb x v Hat Hvalue
    |fr rest m nb l args cs env Hat Hread Hjump
    |fr rest m nb c l1 a1 l2 a2 z l args cs env Hat Hvalue Hselect Hread Hjump
    |fr rest m nb c cases d da z l args cs env Hat Hvalue Hselect Hread Hjump
    |fr rest m nb c args cont cs f fd b env Hat Hread Hcallee Hbind Hlimit
    |fr caller rest m nb x v env Hat Hvalue Hjump
    |fr m nb x v Hat Hvalue].
  - eapply full_instruction_taken; exact Hat.
  - eapply full_instruction_taken; exact Hat.
  - eapply full_instruction_taken; exact Hat.
  - eapply full_instruction_taken; exact Hat.
  - eapply full_instruction_taken; exact Hat.
  - eapply full_instruction_taken; exact Hat.
  - eapply full_transfer_taken with (term := TJump l args) (slot := 0) (args := args).
    all: try eassumption; try discriminate; reflexivity.
  - eapply full_transfer_taken with (term := TBr c l1 a1 l2 a2)
      (slot := if Z.eqb z 0 then 1 else 0) (args := args).
    + exact Hat.
    + discriminate.
    + discriminate.
    + cbn [term_edges]; destruct (Z.eqb z 0); injection Hselect as <- <-; reflexivity.
    + cbn [ssa_term_slot]; rewrite Hvalue; reflexivity.
    + exact Hjump.
  - eapply full_transfer_taken with (term := TSwitch c cases d da)
      (slot := ssa_switch_slot z cases) (args := args).
    + exact Hat.
    + discriminate.
    + discriminate.
    + rewrite <- Hselect; apply ssa_switch_slot_target.
    + cbn [ssa_term_slot]; rewrite Hvalue; reflexivity.
    + exact Hjump.
  - eapply full_call_taken; eassumption.
  - destruct (reachable_good ext P lim _ Hwf Hreachable) as [_ Hlinks].
    cbn [stack stack_links] in Hlinks.
    eapply full_return_taken; [exact Hat|exact (proj1 Hlinks)|exact Hjump].
  - eapply full_main_return_taken; exact Hat.
Qed.

(** The finite full-program supergraph covers every reachable framed execution step. *)
Theorem ssa_full_view_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P ->
  graph_view_laws (ssa_semantics ext P lim) (ssa_full_view ext P lim).
Proof.
  intro Hwf; constructor.
  - apply full_graph_wf.
  - intros s [fd [b [vs [env [Hfunction [Hblock [Htypes [Hvalid [Hbind ->]]]]]]]]].
    change (In (main P, fentry fd, 0)
      (filter (fun n => FinSet.mem full_node_encoding n (full_node_set P))
        (match find_func P (main P) with
         | Some d => [(main P, fentry d, 0)]
         | None => []
         end))).
    rewrite Hfunction; apply filter_In; split; [left; reflexivity|].
    apply (FinSet.elements_spec full_node_encoding _ _ (full_node_set_wf P)).
    apply (full_node_at P (main P) fd (fentry fd) b 0 Hfunction Hblock); lia.
  - intros s tr t Hreachable Hstep; right; eapply full_step_covered; eassumption.
  - intros s tr t e Hreachable Hstep [Hout [Htarget Hslot]]; split; assumption.
  - intros s tr t Hreachable Hstep Hstay; contradiction.
Qed.

(** Instruction lookup is prepared once, rather than rescanning bodies at each memory query. *)
Definition full_instruction_rows (P : program) : list (full_node * instr) :=
  flat_map (fun ffd => flat_map (fun lb =>
    map (fun pi => ((fst ffd, fst lb, fst pi), snd pi))
      (full_number 0 (bbody (snd lb))))
    (Map.elements (first_index (blocks (snd ffd)))))
    (Map.elements (first_index (funcs P))).

Definition full_instruction_index (P : program) : Map.t full_node instr :=
  Map.of_list full_node_encoding (full_instruction_rows P).

Lemma full_number_sound {A} (xs : list A) start pc i :
  In (pc, i) (full_number start xs) ->
  start <= pc /\ nth_error xs (pc - start) = Some i.
Proof.
  revert start pc; induction xs as [|a xs IH]; intros start pc Hin; [contradiction|].
  cbn [full_number] in Hin; destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; rewrite Nat.sub_diag; split; [lia|reflexivity].
  - destruct (IH (S start) pc Hin) as [Hbound Hnth]; split; [lia|].
    replace (pc - start) with (S (pc - S start)) by lia; exact Hnth.
Qed.

Lemma full_instruction_row P fr i :
  at_instr P fr i -> In (full_frame_point fr, i) (full_instruction_rows P).
Proof.
  intros [fd [b [Hfunction [Hblock Hnth]]]].
  unfold full_instruction_rows; apply in_flat_map; exists (ffunc fr, fd); split.
  - apply (Map.elements_complete nat_encoding); [apply first_index_wf|exact Hfunction].
  - apply in_flat_map; exists (flabel fr, b); split.
    + apply (Map.elements_complete nat_encoding); [apply first_index_wf|exact Hblock].
    + apply in_map_iff; exists (fpc fr, i); split; [reflexivity|].
      change (In (0 + fpc fr, i) (full_number 0 (bbody b))).
      apply full_number_member; exact Hnth.
Qed.

Lemma full_instruction_row_at P fr i :
  In (full_frame_point fr, i) (full_instruction_rows P) -> at_instr P fr i.
Proof.
  intro Hrow; apply in_flat_map in Hrow; destruct Hrow as [[f fd] [Hfunction Hrow]].
  apply in_flat_map in Hrow; destruct Hrow as [[l b] [Hblock Hrow]].
  apply in_map_iff in Hrow; destruct Hrow as [[pc operation] [Heq Hnumber]].
  unfold full_frame_point in Heq; cbn [fst snd] in Heq.
  injection Heq as Hf Hl Hpc Hi; subst f l pc operation.
  exists fd, b; split.
  - apply (Map.elements_sound nat_encoding); [apply first_index_wf|exact Hfunction].
  - split.
    + apply (Map.elements_sound nat_encoding); [apply first_index_wf|exact Hblock].
    + destruct (full_number_sound _ 0 _ _ Hnumber) as [_ Hnth].
      rewrite Nat.sub_0_r in Hnth; exact Hnth.
Qed.

Lemma full_at_instr_unique P fr i j : at_instr P fr i -> at_instr P fr j -> i = j.
Proof.
  intros [fd [b [Hfunction [Hblock Hnth]]]] [fd' [b' [Hfunction' [Hblock' Hnth']]]].
  rewrite Hfunction in Hfunction'; injection Hfunction' as <-.
  rewrite Hblock in Hblock'; injection Hblock' as <-; congruence.
Qed.

(** Prepared memory instruction lookup agrees with source lookup, including first bindings. *)
Lemma full_instruction_lookup P fr i :
  at_instr P fr i ->
  Map.get full_node_encoding (full_frame_point fr) (full_instruction_index P) = Some i.
Proof.
  intro Hat; apply ssa_map_get_complete.
  - apply full_instruction_row; exact Hat.
  - intros j Hrow; eapply full_at_instr_unique; [eapply full_instruction_row_at; exact Hrow|
      exact Hat].
Qed.

Definition full_mem_op (i : instr) : option (mem_op vid vid) :=
  match i with
  | IAlloc x n => Some (MemAlloc x n)
  | IFree p => Some (MemFree p)
  | ILoad _ _ sz p => Some (MemLoad p 0%Z (size_bytes sz))
  | IStore sz p v => Some (MemStore p 0%Z (size_bytes sz) v)
  | _ => None
  end.

(** Locations refer to existing identities, including identities whose storage has been freed. *)
Definition ssa_mem_view (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    : mem_view state vid cval nat vid :=
  let instructions := full_instruction_index P in
  MemView
    (fun s =>
      match stack s with
      | [] => None
      | fr :: _ =>
        match Map.get full_node_encoding (full_frame_point fr) instructions with
        | Some i => full_mem_op i
        | None => None
        end
      end)
    (fun s c =>
      match c with
      | VPtr b _ =>
        match mem s b with
        | Some _ => Some b
        | None => None
        end
      | _ => None
      end)
    (fun s b => option_map msite (mem s b))
    (fun _ c =>
      match c with
      | VPtr _ o => o
      | _ => 0%Z
      end).

(** The memory view reports exactly the next source instruction's memory operation. *)
Lemma full_mem_instr_at ext P lim fr rest m nb i :
  at_instr P fr i ->
  mem_instr (ssa_mem_view ext P lim) (State (fr :: rest) m nb) = full_mem_op i.
Proof.
  intro Hat; cbn [ssa_mem_view mem_instr stack].
  rewrite (full_instruction_lookup P fr i Hat); reflexivity.
Qed.

(** All identities at or above the next fresh identity are absent. *)
Definition full_memory_fresh (s : state) : Prop :=
  forall b, next_block s <= b -> mem s b = None.

Lemma full_memory_fresh_step ext P lim s tr t :
  full_memory_fresh s -> step_s ext P lim s tr t -> full_memory_fresh t.
Proof.
  intros Hfresh Hstep; destruct Hstep; unfold full_memory_fresh in *;
    cbn [mem next_block] in *; try exact Hfresh.
  - intros a Ha; unfold memory_set; destruct (Nat.eq_dec a nb) as [->|Hne].
    + lia.
    + apply Hfresh; lia.
  - intros a Ha; unfold memory_set; destruct (Nat.eq_dec a b) as [->|Hne].
    + match goal with Hget : m b = Some mb |- _ =>
        rewrite (Hfresh b Ha) in Hget; discriminate end.
    + apply Hfresh; exact Ha.
  - intros a Ha; unfold memory_set; destruct (Nat.eq_dec a b) as [->|Hne].
    + match goal with Hget : m b = Some mb |- _ =>
        rewrite (Hfresh b Ha) in Hget; discriminate end.
    + apply Hfresh; exact Ha.
Qed.

Lemma full_memory_fresh_reachable ext P lim s :
  reachable_state (ssa_semantics ext P lim) s -> full_memory_fresh s.
Proof.
  intros [start [tr [Hinitial Hrun]]].
  assert (Hfresh : full_memory_fresh start).
  { destruct Hinitial as [fd [b [vs [env [_ [_ [_ [_ [_ ->]]]]]]]]].
    intros a Ha; reflexivity. }
  clear Hinitial.
  revert Hfresh; induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intro Hfresh.
  - exact Hfresh.
  - apply IH; exact (full_memory_fresh_step ext P lim s l s' Hfresh Hstep).
Qed.

Lemma full_store_site sz mb off v mb' :
  memory_store sz mb off v = Some mb' -> msite mb' = msite mb.
Proof.
  unfold memory_store; destruct (access_ok mb off sz && store_shape sz v);
    [intro Heq; injection Heq as <-; reflexivity|discriminate].
Qed.

Lemma full_site_step ext P lim s tr t location site :
  full_memory_fresh s -> step_s ext P lim s tr t ->
  option_map msite (mem s location) = Some site ->
  option_map msite (mem t location) = Some site.
Proof.
  intros Hfresh Hstep; destruct Hstep; unfold full_memory_fresh in Hfresh;
    cbn [mem next_block] in *; try exact (fun H => H).
  - intro Hsite; unfold memory_set; destruct (Nat.eq_dec location nb) as [->|Hne].
    + rewrite (Hfresh nb (Nat.le_refl nb)) in Hsite; discriminate.
    + exact Hsite.
  - intro Hsite; unfold memory_set; destruct (Nat.eq_dec location b) as [->|Hne].
    + match goal with Hget : m b = Some mb |- _ => rewrite Hget in Hsite end.
      exact Hsite.
    + exact Hsite.
  - intro Hsite; unfold memory_set; destruct (Nat.eq_dec location b) as [->|Hne].
    + match goal with Hget : m b = Some mb |- _ => rewrite Hget in Hsite end.
      cbn; rewrite (full_store_site sz mb off v mb'); assumption.
    + exact Hsite.
Qed.

(** Every full-machine step preserves the historical site of every existing identity. *)
Theorem ssa_mem_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P -> mem_view_laws (ssa_semantics ext P lim) (ssa_mem_view ext P lim).
Proof.
  intro Hwf; constructor; intros s tr t b site Hreachable Hstep Hsite.
  eapply full_site_step; [eapply full_memory_fresh_reachable; exact Hreachable|exact Hstep|].
  exact Hsite.
Qed.
