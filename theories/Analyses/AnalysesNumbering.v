(** * Checked value numbering and loop invariants

    Finite congruence checks connect symbolic classes to ranked concrete observations.
    For example, two pure additions with equal operand classes have equal observed results.
    Builds on: CollectionsMap, CollectionsFinSet, ViewsSsa and ViewsDominated. *)

From Stdlib Require Import List Bool Arith Lia Wf_nat PArith NArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTable.
From Gaulois.Graph Require Import GraphCore GraphDominance GraphPrepare GraphDfs GraphDominators.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsDominated.
Import List.ListNotations.

(** A numbering problem supplies its SSA view, pure operators and finite value inventory. *)
Record numbering_problem (S O N E V K C : Type) : Type := NumberingProblem {
  nsv : ssa_view S O N E V K C;
  pure : K -> bool;
  nvalues : list V
}.

Arguments NumberingProblem {S O N E V K C}.
Arguments nsv {S O N E V K C}.
Arguments pure {S O N E V K C}.
Arguments nvalues {S O N E V K C}.

(** Contexts distinguish observations, including separate visits to the same concrete state. *)
Record numbering_observation (H S N E V : Type) : Type := NumberingObservation {
  observation_state : H -> S;
  observation_ready : H -> V -> Prop;
  observation_rank : H -> V -> nat;
  observation_previous : H -> N -> option (E * H)
}.

Arguments NumberingObservation {H S N E V}.
Arguments observation_state {H S N E V}.
Arguments observation_ready {H S N E V}.
Arguments observation_rank {H S N E V}.
Arguments observation_previous {H S N E V}.

(** Local equations relate ready definitions to smaller, ready observations of their operands. *)
Record numbering_observation_laws {H S O N E V K C} (m : semantics S O)
    (np : numbering_problem S O N E V K C) (ob : numbering_observation H S N E V) : Prop :=
    NumberingObservationLaws {
  observed_op : forall h x o args c,
    observation_ready ob h x -> def (nsv np) x = Op o args -> pure np o = true ->
    val (nsv np) (observation_state ob h) x = Some c ->
    exists cs, Forall2 (fun y d => observation_ready ob h y /\
      observation_rank ob h y < observation_rank ob h x /\
      val (nsv np) (observation_state ob h) y = Some d) args cs /\
      op_eval (nsv np) o cs = Some c;
  observed_param : forall h x b i c,
    observation_ready ob h x -> def (nsv np) x = Param b i ->
    ~ In b (Graph.entries (cfg (base (nsv np)))) ->
    val (nsv np) (observation_state ob h) x = Some c ->
    exists e h' z l t tr, observation_previous ob h b = Some (e, h') /\
      In e (edges_of (cfg (base (nsv np)))) /\ Graph.target (cfg (base (nsv np))) e = b /\
      nth_error (edge_args (nsv np) e) i = Some z /\ observation_ready ob h' z /\
      observation_rank ob h' z < observation_rank ob h x /\
      val (nsv np) (observation_state ob h') z = Some c /\
      reachable_state m (observation_state ob h') /\
      step m (observation_state ob h') l t /\
      taken (base (nsv np)) (observation_state ob h') l t e /\
      exec m t tr (observation_state ob h)
}.

(** Every changed pure operation binding is a successful evaluation in the preceding state. *)
Record numbering_loop_laws {S O N E V K C} (m : semantics S O)
    (np : numbering_problem S O N E V K C) : Prop := NumberingLoopLaws {
  loop_op_binding : forall s l t x o args,
    reachable_state m s -> step m s l t -> def (nsv np) x = Op o args ->
    pure np o = true -> val (nsv np) t x <> val (nsv np) s x ->
    exists cs c, Forall2 (fun y d => val (nsv np) s y = Some d) args cs /\
      op_eval (nsv np) o cs = Some c /\ val (nsv np) t x = Some c
}.

(** A loop identifies its header and body membership predicate. *)
Record loop_info (N : Type) : Type := LoopInfo {
  header : N;
  body : N -> bool
}.

Arguments LoopInfo {N}.
Arguments header {N}.
Arguments body {N}.

(** Loop bodies have one dominating header and no other entry from outside. *)
Record loop_info_wf {N E} (g : Graph.t N E) (lp : loop_info N) : Prop := {
  header_in_body : body lp (header lp) = true;
  header_dominates : forall n, body lp n = true -> dominates g (header lp) n;
  single_entry : forall e, In e (edges_of g) -> body lp (Graph.target g e) = true ->
    body lp (Graph.source g e) = false -> Graph.target g e = header lp
}.

(** Direct operands remain unchanged throughout each restricted loop execution. *)
Definition loop_operands_stable {S O N E V K C} (m : semantics S O)
    (np : numbering_problem S O N E V K C) (lp : loop_info N) (x : V) : Prop :=
  forall o args y s tr t, body lp (home (nsv np) x) = true ->
    def (nsv np) x = Op o args -> pure np o = true -> In y args -> reachable_state m s ->
    exec_in m (fun u => body lp (point (base (nsv np)) u) = true) s tr t ->
    val (nsv np) s y = val (nsv np) t y.

(** * Prepared finite congruence signatures *)

Module NumberingIndex.

(** Argument positions are indexed once, before any class signatures are compared. *)
Fixpoint arguments_from {V} (i : nat) (xs : list V) : Map.t nat V :=
  match xs with
  | [] => Map.empty
  | x :: rest => Map.set nat_encoding i x (arguments_from (S i) rest)
  end.

Lemma arguments_from_get {V} (xs : list V) i j :
  Map.get nat_encoding (i + j) (arguments_from i xs) = nth_error xs j.
Proof.
  revert i j; induction xs as [|x xs IH]; intros i [|j]; cbn [arguments_from nth_error].
  - apply Map.get_empty.
  - apply Map.get_empty.
  - rewrite Nat.add_0_r; apply Map.get_set_same.
  - rewrite Map.get_set_other by lia.
    replace (i + S j) with (S i + j) by lia; apply IH.
Qed.

Definition argument_index {V} (xs : list V) : Map.t nat V := arguments_from 0 xs.

Lemma argument_index_get {V} (xs : list V) i :
  Map.get nat_encoding i (argument_index xs) = nth_error xs i.
Proof.
  exact (arguments_from_get xs 0 i).
Qed.

Definition rows {N V} (EN : encoding N) (b : N) (ix : Map.t N (list (Map.t nat V))) :=
  match Map.get EN b ix with
  | Some rs => rs
  | None => []
  end.

Fixpoint incoming {N E V} (EN : encoding N) (target : E -> N) (args : E -> list V)
    (es : list E) : Map.t N (list (Map.t nat V)) :=
  match es with
  | [] => Map.empty
  | e :: rest =>
    let ix := incoming EN target args rest in
    Map.set EN (target e) (argument_index (args e) :: rows EN (target e) ix) ix
  end.

Lemma incoming_member {N E V} (EN : encoding N) target args (es : list E) e :
  In e es -> In (argument_index (args e))
    (rows EN (target e) (@incoming N E V EN target args es)).
Proof.
  induction es as [|a es IH]; cbn [incoming]; intro He; [contradiction|].
  destruct He as [<-|He].
  - unfold rows at 1; rewrite Map.get_set_same; now left.
  - destruct (Pos.eqb (encode EN (target e)) (encode EN (target a))) eqn:Heq.
    + apply Pos.eqb_eq, (encode_injective EN) in Heq.
      unfold rows at 1; rewrite Heq, Map.get_set_same; right.
      rewrite <- Heq; apply IH; exact He.
    + apply Pos.eqb_neq in Heq.
      unfold rows at 1; rewrite Map.get_set_other.
      * apply IH; exact He.
      * intro H; apply Heq; now rewrite H.
Qed.

Fixpoint read_rows {V} (rs : list (Map.t nat V)) (i : nat) : option (list V) :=
  match rs with
  | [] => Some []
  | r :: rest =>
    match Map.get nat_encoding i r, read_rows rest i with
    | Some x, Some xs => Some (x :: xs)
    | _, _ => None
    end
  end.

Lemma read_rows_pair {V W} (f : V -> W) rs i j xs ys r :
  read_rows rs i = Some xs -> read_rows rs j = Some ys ->
  map f xs = map f ys -> In r rs ->
  exists x y, Map.get nat_encoding i r = Some x /\
    Map.get nat_encoding j r = Some y /\ In x xs /\ In y ys /\ f x = f y.
Proof.
  revert xs ys; induction rs as [|a rs IH]; intros xs ys Hx Hy Heq Hr; [contradiction|].
  cbn [read_rows] in Hx, Hy.
  destruct (Map.get nat_encoding i a) as [x|] eqn:Hxi; [|discriminate].
  destruct (Map.get nat_encoding j a) as [y|] eqn:Hyj; [|discriminate].
  destruct (read_rows rs i) as [xs'|] eqn:Hxs; [|discriminate].
  destruct (read_rows rs j) as [ys'|] eqn:Hys; [|discriminate].
  injection Hx as <-; injection Hy as <-; cbn in Heq; injection Heq as Hhead Htail.
  destruct Hr as [<-|Hr].
  - exists x, y; repeat split; try assumption; now left.
  - destruct (IH _ _ eq_refl eq_refl Htail Hr) as [u [v [Hu [Hv [Hin [Hjn Heq]]]]]].
    exists u, v; repeat split; try assumption; now right.
Qed.

End NumberingIndex.
Import NumberingIndex.

(** Encoded signature comparison agrees with equality of the complete signature. *)
Definition numbering_key_eqb (xs ys : list positive) : bool :=
  Pos.eqb (encode (list_encoding positive_encoding) xs)
    (encode (list_encoding positive_encoding) ys).

Lemma numbering_key_eqb_spec xs ys : numbering_key_eqb xs ys = true <-> xs = ys.
Proof.
  unfold numbering_key_eqb; rewrite Pos.eqb_eq; split.
  - apply encode_injective.
  - intros ->; reflexivity.
Qed.

Section Signatures.
Context {S O N E V K C : Type} (EN : encoding N) (EV : encoding V) (EK : encoding K)
  (np : numbering_problem S O N E V K C).
Let sv := nsv np.
Let g := cfg (base sv).

Definition numbering_inventory : FinSet.t V := FinSet.of_list EV (nvalues np).
Definition numbering_entries : FinSet.t N := FinSet.of_list EN (Graph.entries g).
Definition numbering_incoming := incoming EN (Graph.target g) (edge_args sv) (edges_of g).

Definition numbering_single (x : V) : list positive := [1%positive; encode EV x].

(** Failed or unlisted operands get an individual signature rather than a shared sentinel. *)
Definition numbering_signature : (V -> V) -> V -> list positive :=
  let inventory := numbering_inventory in
  let entries := numbering_entries in
  let incoming := numbering_incoming in
  fun rep x =>
  match def sv x with
  | Op o args =>
    if pure np o && forallb (fun y => FinSet.mem EV y inventory) args
    then 2%positive :: encode EK o :: map (fun y => encode EV (rep y)) args
    else numbering_single x
  | Param b i =>
    if FinSet.mem EN b entries then numbering_single x
    else match read_rows (rows EN b incoming) i with
    | Some args =>
      if forallb (fun y => FinSet.mem EV y inventory) args
      then 3%positive :: encode EN b :: map (fun y => encode EV (rep y)) args
      else numbering_single x
    | None => numbering_single x
    end
  | Arbitrary => numbering_single x
  end.

(** One class anchor is prepared for each proposed representative. *)
Fixpoint numbering_anchors (rep : V -> V) (xs : list V) : Map.t V V :=
  match xs with
  | [] => Map.empty
  | x :: rest => Map.set EV (rep x) x (numbering_anchors rep rest)
  end.

Lemma numbering_anchors_member rep xs x : In x xs ->
  exists y, Map.get EV (rep x) (numbering_anchors rep xs) = Some y /\ rep y = rep x.
Proof.
  induction xs as [|a xs IH]; intro Hx; [contradiction|]; cbn [numbering_anchors].
  destruct (Pos.eqb (encode EV (rep x)) (encode EV (rep a))) eqn:Heq.
  - apply Pos.eqb_eq, (encode_injective EV) in Heq.
    exists a; rewrite Heq, Map.get_set_same; split; reflexivity.
  - apply Pos.eqb_neq in Heq; destruct Hx as [<-|Hx]; [contradiction Heq; reflexivity|].
    rewrite Map.get_set_other by (intro H; apply Heq; now rewrite H).
    apply IH; exact Hx.
Qed.

(** Every listed value must agree structurally with the prepared anchor of its class. *)
Definition numbering_check_with : (V -> V) -> bool :=
  let signature := numbering_signature in
  fun rep =>
  let anchors := numbering_anchors rep (nvalues np) in
  forallb (fun x => match Map.get EV (rep x) anchors with
    | Some y => numbering_key_eqb (signature rep x) (signature rep y)
    | None => false
    end) (nvalues np).

End Signatures.

(** The checker compares structural signatures only over the finite supplied inventory. *)
Definition numbering_check {S O N E V K C} (EN : encoding N) (EV : encoding V) (EK : encoding K)
    (np : numbering_problem S O N E V K C) : (V -> V) -> bool :=
  numbering_check_with EN EV EK np.

(** Accepted representatives assign equal complete signatures to listed class members. *)
Lemma numbering_check_signatures {S O N E V K C} EN EV EK
    (np : numbering_problem S O N E V K C) rep x y :
  numbering_check EN EV EK np rep = true -> In x (nvalues np) -> In y (nvalues np) ->
  rep x = rep y ->
  numbering_signature EN EV EK np rep x = numbering_signature EN EV EK np rep y.
Proof.
  unfold numbering_check, numbering_check_with; intros Hcheck Hx Hy Heq.
  apply forallb_forall with (x := x) in Hcheck as Hcx; [|exact Hx].
  apply forallb_forall with (x := y) in Hcheck as Hcy; [|exact Hy].
  rewrite Heq in Hcx.
  destruct (Map.get EV (rep y) (numbering_anchors EV rep (nvalues np))) as [z|];
    [|discriminate].
  apply numbering_key_eqb_spec in Hcx, Hcy; congruence.
Qed.

(** Individual classes always pass, independently of the SSA laws and inventory completeness. *)
Theorem numbering_check_identity {S O N E V K C} EN EV EK
    (np : numbering_problem S O N E V K C) :
  numbering_check EN EV EK np (fun x => x) = true.
Proof.
  unfold numbering_check, numbering_check_with; apply forallb_forall; intros x Hx.
  destruct (numbering_anchors_member EV (fun x => x) (nvalues np) x Hx)
    as [y [Hget Heq]]; cbn in Heq; subst y; rewrite Hget.
  apply numbering_key_eqb_spec; reflexivity.
Qed.

Section StructuralSoundness.
Context {S O N E V K C : Type} (EN : encoding N) (EV : encoding V) (EK : encoding K)
  (np : numbering_problem S O N E V K C) (rep : V -> V).
Let sv := nsv np.
Let g := cfg (base sv).

Definition numbering_related (x y : V) : Prop :=
  In x (nvalues np) /\ In y (nvalues np) /\ rep x = rep y.

Lemma numbering_signature_cases x :
  numbering_signature EN EV EK np rep x = numbering_single EV x \/
  (exists o args, def sv x = Op o args /\ pure np o = true /\
    Forall (fun z => In z (nvalues np)) args /\
    numbering_signature EN EV EK np rep x =
      2%positive :: encode EK o :: map (fun z => encode EV (rep z)) args) \/
  (exists b i args, def sv x = Param b i /\ ~ In b (Graph.entries g) /\
    read_rows (rows EN b (numbering_incoming EN np)) i = Some args /\
    Forall (fun z => In z (nvalues np)) args /\
    numbering_signature EN EV EK np rep x =
      3%positive :: encode EN b :: map (fun z => encode EV (rep z)) args).
Proof.
  unfold numbering_signature; fold sv g.
  destruct (def sv x) as [o args|b i|] eqn:Hdef; [| |now left].
  - destruct (pure np o && forallb (fun y => FinSet.mem EV y (numbering_inventory EV np)) args)
      eqn:Hok; [|now left].
    apply andb_true_iff in Hok as [Hp Ha].
    right; left; exists o, args; repeat split; try assumption.
    apply Forall_forall; intros z Hz.
    apply forallb_forall with (x := z) in Ha; [|exact Hz].
    apply (proj1 (FinSet.of_list_spec EV z (nvalues np))); exact Ha.
  - destruct (FinSet.mem EN b (numbering_entries EN np)) eqn:Hentry; [now left|].
    destruct (read_rows (rows EN b (numbering_incoming EN np)) i) as [args|] eqn:Hargs;
      [|now left].
    destruct (forallb (fun y => FinSet.mem EV y (numbering_inventory EV np)) args)
      eqn:Hlisted; [|now left].
    right; right; exists b, i, args; repeat split; try assumption.
    + intro Hb; apply (proj2 (FinSet.of_list_spec EN b (Graph.entries g))) in Hb.
      unfold numbering_entries in Hentry; fold sv g in Hentry; congruence.
    + apply Forall_forall; intros z Hz.
      apply forallb_forall with (x := z) in Hlisted; [|exact Hz].
      apply (proj1 (FinSet.of_list_spec EV z (nvalues np))); exact Hlisted.
Qed.

Lemma numbering_argument_classes xs ys :
  Forall (fun z => In z (nvalues np)) xs -> Forall (fun z => In z (nvalues np)) ys ->
  map (fun z => encode EV (rep z)) xs = map (fun z => encode EV (rep z)) ys ->
  Forall2 numbering_related xs ys.
Proof.
  intro Hx; revert ys; induction Hx as [|x xs Hx Hxs IH];
    intros ys Hy Heq; inversion Hy as [|y ys' Hy' Hys]; subst; cbn in Heq;
    try discriminate; [constructor|].
  injection Heq as Hhead Htail; constructor.
  - split; [exact Hx|split; [exact Hy'|apply (encode_injective EV); exact Hhead]].
  - apply IH; assumption.
Qed.

(** Structural congruence records exactly the finite-inventory operation and phi boundary. *)
Definition numbering_congruent (x y : V) : Prop :=
  x = y \/
  (exists o xs ys, def sv x = Op o xs /\ def sv y = Op o ys /\
    pure np o = true /\ Forall2 numbering_related xs ys) \/
  (exists b i j, def sv x = Param b i /\ def sv y = Param b j /\
    ~ In b (Graph.entries g) /\
    forall e, In e (edges_of g) -> Graph.target g e = b ->
    exists a d, nth_error (edge_args sv e) i = Some a /\
      nth_error (edge_args sv e) j = Some d /\ numbering_related a d).

(** Equal signatures yield structural congruence without any semantic equality assumption. *)
Lemma numbering_signature_congruent x y :
  numbering_signature EN EV EK np rep x = numbering_signature EN EV EK np rep y ->
  numbering_congruent x y.
Proof.
  intro Heq.
  destruct (numbering_signature_cases x) as [Hx|[Hx|Hx]];
    destruct (numbering_signature_cases y) as [Hy|[Hy|Hy]].
  - rewrite Hx, Hy in Heq; unfold numbering_single in Heq.
    injection Heq as Heq; left; apply (encode_injective EV); exact Heq.
  - destruct Hy as [o [args [_ [_ [_ Hy]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hy as [b [i [args [_ [_ [_ [_ Hy]]]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [o [args [_ [_ [_ Hx]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [o [xs [Hdx [Hp [Hxs Hx]]]]].
    destruct Hy as [p [ys [Hdy [_ [Hys Hy]]]]].
    rewrite Hx, Hy in Heq; injection Heq as Hop Hargs.
    apply (encode_injective EK) in Hop; subst p; right; left; exists o, xs, ys.
    repeat split; try assumption; apply numbering_argument_classes; assumption.
  - destruct Hx as [o [args [_ [_ [_ Hx]]]]].
    destruct Hy as [b [i [ys [_ [_ [_ [_ Hy]]]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [b [i [args [_ [_ [_ [_ Hx]]]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [b [i [xs [_ [_ [_ [_ Hx]]]]]]].
    destruct Hy as [o [args [_ [_ [_ Hy]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [b [i [xs [Hdx [Hentry [Hreadx [Hxs Hx]]]]]]].
    destruct Hy as [b' [j [ys [Hdy [_ [Hready [Hys Hy]]]]]]].
    rewrite Hx, Hy in Heq; injection Heq as Hb Hargs.
    apply (encode_injective EN) in Hb; subst b'.
    right; right; exists b, i, j; repeat split; try assumption.
    intros e He Htarget.
    assert (Hr : In (argument_index (edge_args sv e))
      (rows EN b (numbering_incoming EN np))).
    { rewrite <- Htarget; apply incoming_member; exact He. }
    destruct (read_rows_pair (fun z => encode EV (rep z)) _ _ _ _ _ _
      Hreadx Hready Hargs Hr) as [a [d [Ha [Hd [Hax [Hdy' Had]]]]]].
    rewrite !argument_index_get in Ha, Hd; exists a, d; repeat split; try assumption.
    + apply (proj1 (Forall_forall _ _) Hxs a Hax).
    + apply (proj1 (Forall_forall _ _) Hys d Hdy').
    + apply (encode_injective EV); exact Had.
Qed.

(** Acceptance establishes congruence for every pair of listed members of a proposed class. *)
Theorem numbering_check_congruent x y :
  numbering_check EN EV EK np rep = true -> numbering_related x y ->
  numbering_congruent x y.
Proof.
  intros Hcheck [Hx [Hy Heq]]; apply numbering_signature_congruent.
  eapply numbering_check_signatures; eassumption.
Qed.

End StructuralSoundness.

(** * Canonical grouping and finite refinement *)

Fixpoint numbering_group_anchors {V} (key : V -> list positive) (xs : list V) : Table.t V :=
  match xs with
  | [] => Table.empty
  | x :: rest => Table.set (key x) x (numbering_group_anchors key rest)
  end.

Lemma numbering_group_anchors_origin {V} key xs k (y : V) :
  Table.get k (numbering_group_anchors key xs) = Some y -> In y xs /\ key y = k.
Proof.
  induction xs as [|x xs IH]; cbn [numbering_group_anchors].
  - rewrite Table.get_empty; discriminate.
  - destruct (numbering_key_eqb k (key x)) eqn:Heq.
    + apply numbering_key_eqb_spec in Heq; subst k; rewrite Table.get_set_same.
      intro Hy; injection Hy as <-; split; [now left|reflexivity].
    + assert (Hne : k <> key x).
      { intro Heq'; subst k; rewrite (proj2 (numbering_key_eqb_spec _ _) eq_refl) in Heq;
          discriminate. }
      rewrite Table.get_set_other by exact Hne.
      intro Hy; destruct (IH Hy) as [Hin Hkey]; split; [now right|exact Hkey].
Qed.

Lemma numbering_group_anchors_member {V} key xs (x : V) :
  In x xs -> exists y, Table.get (key x) (numbering_group_anchors key xs) = Some y.
Proof.
  induction xs as [|a xs IH]; intro Hx; [contradiction|]; cbn [numbering_group_anchors].
  destruct (numbering_key_eqb (key x) (key a)) eqn:Heq.
  - apply numbering_key_eqb_spec in Heq; rewrite Heq, Table.get_set_same; eexists; reflexivity.
  - assert (Hne : key x <> key a).
    { intro H; rewrite H, (proj2 (numbering_key_eqb_spec _ _) eq_refl) in Heq; discriminate. }
    rewrite Table.get_set_other by exact Hne.
    destruct Hx as [<-|Hx]; [contradiction|apply IH; exact Hx].
Qed.

(** Grouping indexes signatures once and preserves the identity of every unlisted value. *)
Definition numbering_group {V} (EV : encoding V) (xs : list V)
    : (V -> list positive) -> V -> V :=
  let inventory := FinSet.of_list EV xs in
  fun key =>
  let anchors := numbering_group_anchors key xs in
  fun x => if FinSet.mem EV x inventory then
    match Table.get (key x) anchors with
    | Some y => y
    | None => x
    end
  else x.

Lemma numbering_group_member {V} (EV : encoding V) xs key x : In x xs ->
  In (numbering_group EV xs key x) xs /\ key (numbering_group EV xs key x) = key x.
Proof.
  intro Hx; unfold numbering_group; rewrite (proj2 (FinSet.of_list_spec EV x xs) Hx).
  destruct (numbering_group_anchors_member key xs x Hx) as [y Hget]; rewrite Hget.
  apply numbering_group_anchors_origin in Hget; exact Hget.
Qed.

Lemma numbering_group_eq {V} (EV : encoding V) xs key x y : In x xs -> In y xs ->
  (numbering_group EV xs key x = numbering_group EV xs key y <-> key x = key y).
Proof.
  intros Hx Hy; split.
  - intro Heq; pose proof (proj2 (numbering_group_member EV xs key x Hx)) as Hkx.
    pose proof (proj2 (numbering_group_member EV xs key y Hy)) as Hky; congruence.
  - intro Heq; unfold numbering_group.
    rewrite (proj2 (FinSet.of_list_spec EV x xs) Hx),
      (proj2 (FinSet.of_list_spec EV y xs) Hy), Heq.
    destruct (numbering_group_anchors_member key xs y Hy) as [z Hget]; now rewrite Hget.
Qed.

Lemma numbering_anchors_origin {V} (EV : encoding V) rep xs k (y : V) :
  Map.get EV k (numbering_anchors EV rep xs) = Some y -> In y xs /\ rep y = k.
Proof.
  induction xs as [|x xs IH]; cbn [numbering_anchors].
  - rewrite Map.get_empty; discriminate.
  - destruct (Pos.eqb (encode EV k) (encode EV (rep x))) eqn:Heq.
    + apply Pos.eqb_eq, (encode_injective EV) in Heq; subst k; rewrite Map.get_set_same.
      intro Hy; injection Hy as <-; split; [now left|reflexivity].
    + apply Pos.eqb_neq in Heq; rewrite Map.get_set_other.
      * intro Hy; destruct (IH Hy) as [Hin Hrep]; split; [now right|exact Hrep].
      * intro H; apply Heq; now rewrite H.
Qed.

Fixpoint numbering_count {A} (f : A -> bool) (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: rest => (if f x then 1 else 0) + numbering_count f rest
  end.

Lemma numbering_count_bound {A} f (xs : list A) : numbering_count f xs <= length xs.
Proof.
  induction xs as [|x xs IH]; cbn [numbering_count length]; [lia|].
  destruct (f x); lia.
Qed.

Lemma numbering_count_le {A} f g (xs : list A) :
  (forall x, In x xs -> f x = true -> g x = true) ->
  numbering_count f xs <= numbering_count g xs.
Proof.
  induction xs as [|x xs IH]; intro Hsub; cbn [numbering_count]; [lia|].
  assert (Htail : numbering_count f xs <= numbering_count g xs).
  { apply IH; intros y Hy; apply Hsub; now right. }
  specialize (Hsub x (or_introl eq_refl)); destruct (f x), (g x); cbn in *;
    try lia; discriminate.
Qed.

Lemma numbering_count_lt {A} f g (xs : list A) :
  (forall x, In x xs -> f x = true -> g x = true) ->
  (exists x, In x xs /\ f x = false /\ g x = true) ->
  numbering_count f xs < numbering_count g xs.
Proof.
  induction xs as [|x xs IH]; intros Hsub [y [Hy [Hfy Hgy]]]; [contradiction|].
  cbn [numbering_count]; destruct Hy as [<-|Hy].
  - rewrite Hfy, Hgy; cbn.
    assert (Hle : numbering_count f xs <= numbering_count g xs).
    { apply numbering_count_le; intros z Hz; apply Hsub; now right. }
    lia.
  - assert (Hlt : numbering_count f xs < numbering_count g xs).
    { apply IH; [intros z Hz; apply Hsub; now right|exists y; repeat split; assumption]. }
    specialize (Hsub x (or_introl eq_refl)); destruct (f x), (g x); cbn in *;
      try lia; discriminate.
Qed.

Lemma numbering_forallb_false {A} (f : A -> bool) xs :
  forallb f xs = false -> exists x, In x xs /\ f x = false.
Proof.
  induction xs as [|x xs IH]; cbn; [discriminate|].
  destruct (f x) eqn:Hx; cbn.
  - intro Htail; destruct (IH Htail) as [y [Hy Hfy]]; exists y; split; [now right|exact Hfy].
  - intros _; exists x; split; [now left|exact Hx].
Qed.

Section Refinement.
Context {S O N E V K C : Type} (EN : encoding N) (EV : encoding V) (EK : encoding K)
  (np : numbering_problem S O N E V K C).

Definition numbering_refine : (V -> V) -> V -> V :=
  let signature := numbering_signature EN EV EK np in
  let group := numbering_group EV (nvalues np) in
  fun rep =>
  group
    (fun x => encode EV (rep x) :: signature rep x).

Definition numbering_pairs : list (V * V) :=
  flat_map (fun x => map (fun y => (x, y)) (nvalues np)) (nvalues np).

Definition numbering_pair_equal (rep : V -> V) (xy : V * V) : bool :=
  Pos.eqb (encode EV (rep (fst xy))) (encode EV (rep (snd xy))).

Definition numbering_measure (rep : V -> V) : nat :=
  numbering_count (numbering_pair_equal rep) numbering_pairs.

Lemma numbering_pairs_spec x y : In (x, y) numbering_pairs <->
  In x (nvalues np) /\ In y (nvalues np).
Proof.
  unfold numbering_pairs; rewrite in_flat_map; split.
  - intros [a [Ha Hpair]]; apply in_map_iff in Hpair as [b [Heq Hb]].
    injection Heq as <- <-; split; assumption.
  - intros [Hx Hy]; exists x; split; [exact Hx|apply in_map; exact Hy].
Qed.

Lemma numbering_refine_eq rep x y : In x (nvalues np) -> In y (nvalues np) ->
  (numbering_refine rep x = numbering_refine rep y <->
    rep x = rep y /\ numbering_signature EN EV EK np rep x =
      numbering_signature EN EV EK np rep y).
Proof.
  intros Hx Hy; unfold numbering_refine; rewrite numbering_group_eq by assumption.
  split.
  - intro Heq; injection Heq as Hrep Hsig; split; [apply (encode_injective EV)|]; assumption.
  - intros [Heq Hsig]; now rewrite Heq, Hsig.
Qed.

Lemma numbering_refine_decreases rep : numbering_check EN EV EK np rep = false ->
  numbering_measure (numbering_refine rep) < numbering_measure rep.
Proof.
  intro Hbad; unfold numbering_measure; apply numbering_count_lt.
  - intros [x y] Hxy; apply numbering_pairs_spec in Hxy as [Hx Hy].
    unfold numbering_pair_equal; cbn; rewrite !Pos.eqb_eq.
    intro Heq; apply (encode_injective EV) in Heq.
    apply (proj1 (numbering_refine_eq rep x y Hx Hy)) in Heq as [Heq _].
    now rewrite Heq.
  - unfold numbering_check, numbering_check_with in Hbad.
    apply numbering_forallb_false in Hbad as [x [Hx Hbad]].
    destruct (numbering_anchors_member EV rep (nvalues np) x Hx) as [y [Hget Hrep]].
    rewrite Hget in Hbad.
    pose proof (numbering_anchors_origin EV rep (nvalues np) (rep x) y Hget)
      as [Hy Hrep_y].
    exists (x, y); split; [apply numbering_pairs_spec; split; assumption|split].
    + unfold numbering_pair_equal; cbn; apply Pos.eqb_neq; intro Heq.
      apply (encode_injective EV) in Heq.
      apply (proj1 (numbering_refine_eq rep x y Hx Hy)) in Heq as [_ Hsig].
      rewrite Hsig, (proj2 (numbering_key_eqb_spec _ _) eq_refl) in Hbad; discriminate.
    + unfold numbering_pair_equal; cbn; rewrite Hrep; apply Pos.eqb_refl.
Qed.

End Refinement.

Arguments observed_op {H S O N E V K C m np ob} _ h x o args c _ _ _ _.
Arguments observed_param {H S O N E V K C m np ob} _ h x b i c _ _ _ _.
Arguments loop_op_binding {S O N E V K C m np} _ s l t x o args _ _ _ _ _.

(** * Ranked observation soundness *)

Section ObservationSoundness.
Context {H S O N E V K C : Type} (m : semantics S O)
  (EN : encoding N) (EV : encoding V) (EK : encoding K)
  (np : numbering_problem S O N E V K C) (ob : numbering_observation H S N E V)
  (rep : V -> V).
Let sv := nsv np.
Hypothesis Hobs : numbering_observation_laws m np ob.
Hypothesis Hcheck : numbering_check EN EV EK np rep = true.

Lemma numbering_observed_arguments h rx ry xs ys cs ds :
  (forall a b c d,
    observation_rank ob h a + observation_rank ob h b < rx + ry ->
    numbering_related np rep a b -> observation_ready ob h a -> observation_ready ob h b ->
    val sv (observation_state ob h) a = Some c ->
    val sv (observation_state ob h) b = Some d -> c = d) ->
  Forall2 (numbering_related np rep) xs ys ->
  Forall2 (fun a c => observation_ready ob h a /\ observation_rank ob h a < rx /\
    val sv (observation_state ob h) a = Some c) xs cs ->
  Forall2 (fun b d => observation_ready ob h b /\ observation_rank ob h b < ry /\
    val sv (observation_state ob h) b = Some d) ys ds -> cs = ds.
Proof.
  intros Hsmaller Hrelated; revert cs ds.
  induction Hrelated as [|a b xs ys Hab Hrelated IH]; intros cs ds Hcs Hds.
  - inversion Hcs; inversion Hds; reflexivity.
  - inversion Hcs as [|a' c xs' cs' [Hra [Hrank_a Hval_a]] Htail_a]; subst.
    inversion Hds as [|b' d ys' ds' [Hrb [Hrank_b Hval_b]] Htail_b]; subst.
    f_equal.
    + eapply Hsmaller; try eassumption; lia.
    + apply IH; assumption.
Qed.

(** Ready, defined members agree by well-founded descent on their two observation ranks. *)
Theorem numbering_observations_equal h x y c d :
  numbering_related np rep x y -> observation_ready ob h x -> observation_ready ob h y ->
  val sv (observation_state ob h) x = Some c ->
  val sv (observation_state ob h) y = Some d -> c = d.
Proof.
  assert (Hrank : forall n h x y c d,
    observation_rank ob h x + observation_rank ob h y = n ->
    numbering_related np rep x y -> observation_ready ob h x -> observation_ready ob h y ->
    val sv (observation_state ob h) x = Some c ->
    val sv (observation_state ob h) y = Some d -> c = d).
  { intro n; induction n as [n IH] using lt_wf_ind;
      intros h' a b ca cb Hsum Hab Hra Hrb Hva Hvb.
    destruct (numbering_check_congruent EN EV EK np rep a b Hcheck Hab)
      as [Heq|[Hops|Hparams]].
    - subst b; congruence.
    - destruct Hops as [o [xs [ys [Hda [Hdb [Hp Hargs]]]]]].
      destruct (observed_op Hobs h' a o xs ca Hra Hda Hp Hva) as [cs [Hcs Heca]].
      destruct (observed_op Hobs h' b o ys cb Hrb Hdb Hp Hvb) as [ds [Hds Hecb]].
      assert (Hsame : cs = ds).
      { eapply numbering_observed_arguments; [|exact Hargs|exact Hcs|exact Hds].
        intros u v cu cv Hless Huv Hru Hrv Hvu Hvv.
        eapply (IH (observation_rank ob h' u + observation_rank ob h' v));
          [lia|reflexivity|exact Huv|exact Hru|exact Hrv|exact Hvu|exact Hvv]. }
      subst ds; congruence.
    - destruct Hparams as [block [i [j [Hda [Hdb [Hentry Hargs]]]]]].
      destruct (observed_param Hobs h' a block i ca Hra Hda Hentry Hva)
        as [e [ha [za [la [ta [tra [Hpa [He [Htarget [Hza [Hrza [Hrank_a
          [Hvza Hactual_a]]]]]]]]]]]]].
      destruct (observed_param Hobs h' b block j cb Hrb Hdb Hentry Hvb)
        as [f [hb [zb [lb [tb [trb [Hpb [Hf [Htarget_b [Hzb [Hrzb [Hrank_b
          [Hvzb Hactual_b]]]]]]]]]]]]].
      rewrite Hpa in Hpb; injection Hpb as <- <-.
      destruct (Hargs e He Htarget) as [u [v [Hu [Hv Huv]]]].
      rewrite Hza in Hu; injection Hu as <-.
      rewrite Hzb in Hv; injection Hv as <-.
      eapply (IH (observation_rank ob ha za + observation_rank ob ha zb));
        [lia|reflexivity|exact Huv|exact Hrza|exact Hrzb|exact Hvza|exact Hvzb]. }
  apply (Hrank (observation_rank ob h x + observation_rank ob h y) h x y c d eq_refl).
Qed.

End ObservationSoundness.

(** A ready, defined checked class mate holds the freshly bound value. *)
Theorem numbering_check_sound {H S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) (EK : encoding K)
    (np : numbering_problem S O N E V K C) (ob : numbering_observation H S N E V)
    (rep : V -> V) :
  ssa_view_laws m (nsv np) -> strict_ssa_laws m (nsv np) ->
  numbering_observation_laws m np ob -> numbering_check EN EV EK np rep = true ->
  forall x y s l s' c, rep x = rep y -> reachable_state m s -> step m s l s' ->
    In x (nvalues np) -> In y (nvalues np) ->
    val (nsv np) s' x = Some c -> val (nsv np) s x <> Some c ->
    (strictly_dominates (cfg (base (nsv np))) (home (nsv np) y) (home (nsv np) x) \/
     exists b i j, def (nsv np) x = Param b i /\ def (nsv np) y = Param b j) ->
    (exists h d, observation_state ob h = s' /\ observation_ready ob h x /\
      observation_ready ob h y /\ val (nsv np) s' y = Some d) ->
    val (nsv np) s' y = Some c.
Proof.
  intros Hssa Hstrict Hobs Hcheck x y s l s' c Heq Hreachable Hstep Hx Hy Hval Hnew
    Hscope [h [d [Hstate [Hrx [Hry Hyval]]]]].
  subst s'.
  assert (Hcd : c = d).
  { eapply numbering_observations_equal; [exact Hobs|exact Hcheck| |exact Hrx|exact Hry|
      exact Hval|exact Hyval].
    repeat split; assumption. }
  now rewrite Hcd.
Qed.

(** Ready, defined class members agree at a dominated use in their shared observation context. *)
Theorem numbering_use_sound {H S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) (EK : encoding K)
    (np : numbering_problem S O N E V K C) (ob : numbering_observation H S N E V)
    (rep : V -> V) :
  ssa_view_laws m (nsv np) -> strict_ssa_laws m (nsv np) ->
  numbering_observation_laws m np ob -> numbering_check EN EV EK np rep = true ->
  forall x y s, rep x = rep y -> reachable_state m s ->
    In x (nvalues np) -> In y (nvalues np) ->
    strictly_dominates (cfg (base (nsv np))) (home (nsv np) x) (point (base (nsv np)) s) ->
    strictly_dominates (cfg (base (nsv np))) (home (nsv np) y) (point (base (nsv np)) s) ->
    (exists h c d, observation_state ob h = s /\ observation_ready ob h x /\
      observation_ready ob h y /\ val (nsv np) s x = Some c /\ val (nsv np) s y = Some d) ->
    exists c, val (nsv np) s x = Some c /\ val (nsv np) s y = Some c.
Proof.
  intros Hssa Hstrict Hobs Hcheck x y s Heq Hreachable Hx Hy Hdomx Hdomy
    [h [c [d [Hstate [Hrx [Hry [Hvalx Hvaly]]]]]]].
  subst s; exists c; split; [exact Hvalx|].
  assert (Hcd : c = d).
  { eapply numbering_observations_equal; [exact Hobs|exact Hcheck| |exact Hrx|exact Hry|
      exact Hvalx|exact Hvaly].
    repeat split; assumption. }
  now rewrite Hcd.
Qed.

(** * Bounded structural invariance *)

(** Binary iteration uses structural recursion on the bits of a positive budget. *)
Fixpoint numbering_iterate {A} (fuel : positive) (f : A -> A) (a : A) : A :=
  match fuel with
  | xH => f a
  | xO rest => numbering_iterate rest f (numbering_iterate rest f a)
  | xI rest => f (numbering_iterate rest f (numbering_iterate rest f a))
  end.

Lemma numbering_iterate_preserves {A} (P : A -> Prop) (f : A -> A) :
  (forall a, P a -> P (f a)) -> forall fuel a, P a -> P (numbering_iterate fuel f a).
Proof.
  intros Hf fuel; induction fuel as [p IH|p IH|]; intros a Ha; cbn [numbering_iterate].
  - apply Hf, IH, IH; exact Ha.
  - apply IH, IH; exact Ha.
  - apply Hf; exact Ha.
Qed.

Lemma numbering_iterate_accepted {A} (check : A -> bool) (f : A -> A) :
  (forall a, check a = true -> f a = a) ->
  forall fuel a, check a = true -> numbering_iterate fuel f a = a.
Proof.
  intros Hfixed fuel; induction fuel as [p IH|p IH|]; intros a Ha;
    cbn [numbering_iterate].
  - rewrite (IH a Ha), (IH a Ha); apply Hfixed; exact Ha.
  - rewrite (IH a Ha), (IH a Ha); reflexivity.
  - apply Hfixed; exact Ha.
Qed.

Lemma numbering_iterate_bad {A} (check : A -> bool) (measure : A -> nat) (f : A -> A) :
  (forall a, check a = true -> f a = a) ->
  (forall a, check a = false -> measure (f a) < measure a) ->
  forall fuel a, check (numbering_iterate fuel f a) = false ->
    measure (numbering_iterate fuel f a) + Pos.to_nat fuel <= measure a.
Proof.
  intros Hfixed Hdecrease.
  assert (Hback : forall fuel a, check (numbering_iterate fuel f a) = false -> check a = false).
  { intros fuel a Hbad; destruct (check a) eqn:Hcheck; [|reflexivity].
    rewrite (numbering_iterate_accepted check f Hfixed fuel a Hcheck), Hcheck in Hbad;
      discriminate. }
  assert (Hstep : forall a, check (f a) = false -> check a = false).
  { intros a Hbad; apply (Hback 1%positive a); exact Hbad. }
  intro fuel; induction fuel as [p IH|p IH|]; intros a Hbad; cbn [numbering_iterate] in *.
  - pose proof (Hstep _ Hbad) as Hmidbad.
    pose proof (Hback p _ Hmidbad) as Hfirstbad.
    pose proof (IH _ Hmidbad) as Hsecond.
    pose proof (IH _ Hfirstbad) as Hfirst.
    pose proof (Hdecrease _ Hmidbad) as Hlast.
    rewrite Pos2Nat.inj_xI; lia.
  - pose proof (Hback p _ Hbad) as Hmidbad.
    pose proof (IH _ Hbad) as Hsecond.
    pose proof (IH _ Hmidbad) as Hfirst.
    rewrite Pos2Nat.inj_xO; lia.
  - pose proof (Hdecrease _ (Hstep _ Hbad)); cbn; lia.
Qed.

Definition numbering_optimistic_step {S O N E V K C} EN EV EK
    (np : numbering_problem S O N E V K C) : (V -> V) -> V -> V :=
  let check := numbering_check EN EV EK np in
  let refine := numbering_refine EN EV EK np in
  fun rep => if check rep then rep else refine rep.

(** Optimistic numbering refines operator and block classes to the coarsest stable congruence. *)
Definition numbering_finish {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (EK : encoding K) (np : numbering_problem S O N E V K C) (initial : V -> V) : V -> V :=
  numbering_iterate (Pos.of_succ_nat (length (nvalues np) * length (nvalues np)))
    (numbering_optimistic_step EN EV EK np) initial.

(** Optimistic numbering starts with one class per operator or non-entry parameter block. *)
Definition optimistic_numbering {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (EK : encoding K) (np : numbering_problem S O N E V K C) : V -> V :=
  let signature := numbering_signature EN EV EK np (fun y => y) in
  numbering_finish EN EV EK np (numbering_group EV (nvalues np)
    (fun x => firstn 2 (signature x))).

Lemma numbering_pairs_length {S O N E V K C} (np : numbering_problem S O N E V K C) :
  length (numbering_pairs np) = length (nvalues np) * length (nvalues np).
Proof.
  assert (Hlength : forall (xs ys : list V),
    length (flat_map (fun x => map (fun y => (x, y)) ys) xs) = length xs * length ys).
  { intros xs ys; induction xs as [|x xs IH]; cbn [flat_map length Nat.mul]; [reflexivity|].
    rewrite length_app, length_map, IH; reflexivity. }
  apply Hlength.
Qed.

(** The strict pair-count decrease gives unconditional acceptance without a singleton fallback. *)
Lemma numbering_finish_checked {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (EK : encoding K) (np : numbering_problem S O N E V K C) (initial : V -> V) :
  numbering_check EN EV EK np (numbering_finish EN EV EK np initial) = true.
Proof.
  unfold numbering_finish.
  destruct (numbering_check EN EV EK np
    (numbering_iterate (Pos.of_succ_nat (length (nvalues np) * length (nvalues np)))
      (numbering_optimistic_step EN EV EK np) initial)) eqn:Hcheck; [reflexivity|].
  exfalso.
  assert (Hfixed : forall rep, numbering_check EN EV EK np rep = true ->
    numbering_optimistic_step EN EV EK np rep = rep).
  { intros rep Hrep; unfold numbering_optimistic_step; now rewrite Hrep. }
  assert (Hdecrease : forall rep, numbering_check EN EV EK np rep = false ->
    numbering_measure EV np (numbering_optimistic_step EN EV EK np rep) <
      numbering_measure EV np rep).
  { intros rep Hrep; unfold numbering_optimistic_step; rewrite Hrep.
    apply numbering_refine_decreases; exact Hrep. }
  pose proof (numbering_iterate_bad _ _ _ Hfixed Hdecrease _ initial Hcheck) as Hbound.
  pose proof (numbering_count_bound (numbering_pair_equal EV initial) (numbering_pairs np))
    as Hinitial.
  rewrite numbering_pairs_length in Hinitial; rewrite SuccNat2Pos.id_succ in Hbound.
  unfold numbering_measure in Hbound; lia.
Qed.

(** Optimistic numbering always passes, without semantic assumptions on its input view. *)
Theorem optimistic_numbering_checked {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (EK : encoding K) (np : numbering_problem S O N E V K C) :
  numbering_check EN EV EK np (optimistic_numbering EN EV EK np) = true.
Proof.
  apply numbering_finish_checked.
Qed.

(** * Dominator scopes *)

Fixpoint numbering_homes {N V} (EN : encoding N) (home : V -> N) (xs : list V)
    : Map.t N (list V) :=
  match xs with
  | [] => Map.empty
  | x :: rest =>
    let ix := numbering_homes EN home rest in
    let previous := match Map.get EN (home x) ix with Some ys => ys | None => [] end in
    Map.set EN (home x) (x :: previous) ix
  end.

Definition numbering_lookup {V} (EV : encoding V) (leaders : Map.t V V) (x : V) : V :=
  match Map.get EV x leaders with
  | Some y => y
  | None => x
  end.

Section DominatorScopes.
Context {S O N E V K C : Type} (EN : encoding N) (EV : encoding V) (EK : encoding K)
  (np : numbering_problem S O N E V K C).

Definition numbering_scope_value : Table.t V * Map.t V V -> V -> Table.t V * Map.t V V :=
  let signature := numbering_signature EN EV EK np in
  fun state x =>
  let '(symbols, leaders) := state in
  let key := signature (numbering_lookup EV leaders) x in
  match Table.get key symbols with
  | Some y => (symbols, Map.set EV x y leaders)
  | None => (Table.set key x symbols, Map.set EV x x leaders)
  end.

Definition numbering_scope_block (tree : dom_tree N) (homes : Map.t N (list V))
    : Map.t N (Table.t V) * Map.t V V -> N -> Map.t N (Table.t V) * Map.t V V :=
  let visit := numbering_scope_value in
  fun state b =>
  let '(scopes, leaders) := state in
  let symbols := match Map.get EN b (idom tree) with
    | Some parent => match Map.get EN parent scopes with Some t => t | None => Table.empty end
    | None => Table.empty
    end in
  let values := match Map.get EN b homes with Some xs => xs | None => [] end in
  let '(symbols', leaders') := fold_left visit values (symbols, leaders) in
  (Map.set EN b symbols' scopes, leaders').

(** The depth-first dominator order gives each block exactly its parent's saved symbol scope. *)
Definition numbering_scoped_candidate : V -> V :=
  let p := prepare EN (cfg (base (nsv np))) in
  let tree := dominator_tree p in
  let order := preorder (dom_search p (idom tree)) in
  let homes := numbering_homes EN (home (nsv np)) (nvalues np) in
  let state := fold_left (numbering_scope_block tree homes) order (Map.empty, Map.empty) in
  numbering_lookup EV (snd state).

End DominatorScopes.

(** Scoped dominator numbering refines any unstable classes before exposing its representatives. *)
Definition dominator_numbering {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (EK : encoding K) (np : numbering_problem S O N E V K C) : V -> V :=
  numbering_finish EN EV EK np (numbering_scoped_candidate EN EV EK np).

(** Dominator numbering always passes, including malformed or incomplete finite inventories. *)
Theorem dominator_numbering_checked {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (EK : encoding K) (np : numbering_problem S O N E V K C) :
  numbering_check EN EV EK np (dominator_numbering EN EV EK np) = true.
Proof.
  apply numbering_finish_checked.
Qed.

Definition numbering_invariant_round {S O N E V K C}
    (np : numbering_problem S O N E V K C) (lp : loop_info N) (previous : V -> bool)
    (x : V) : bool :=
  if body lp (home (nsv np) x) then
    match def (nsv np) x with
    | Op o args => pure np o && forallb previous args
    | _ => false
    end
  else true.

(** The finite depth budget rejects cycles of inside-body operations. *)
Definition invariant_in {S O N E V K C} (np : numbering_problem S O N E V K C)
    (lp : loop_info N) (x : V) : bool :=
  let initial := fun y => negb (body lp (home (nsv np) y)) in
  match N.of_nat (length (nvalues np)) with
  | N0 => initial x
  | Npos fuel => numbering_iterate fuel (numbering_invariant_round np lp) initial x
  end.

Lemma invariant_in_shape {S O N E V K C} (np : numbering_problem S O N E V K C) lp x :
  invariant_in np lp x = true -> body lp (home (nsv np) x) = false \/
    exists o args, def (nsv np) x = Op o args /\ pure np o = true.
Proof.
  pose (P := fun f : V -> bool => forall y, f y = true ->
    body lp (home (nsv np) y) = false \/
    exists o args, def (nsv np) y = Op o args /\ pure np o = true).
  assert (Hinitial : P (fun y => negb (body lp (home (nsv np) y)))).
  { intros y Hy; left; now apply negb_true_iff. }
  assert (Hround : forall f, P f -> P (numbering_invariant_round np lp f)).
  { intros f Hf y; unfold numbering_invariant_round.
    destruct (body lp (home (nsv np) y)) eqn:Hbody; [|intros _; now left].
    destruct (def (nsv np) y) as [o args|b i|] eqn:Hdef; try discriminate.
    intro Hy; apply andb_true_iff in Hy as [Hp _]; right; exists o, args;
      split; [reflexivity|exact Hp]. }
  unfold invariant_in; destruct (N.of_nat (length (nvalues np))) as [|fuel].
  - apply Hinitial.
  - apply (numbering_iterate_preserves P _ Hround fuel _ Hinitial).
Qed.

(** * Constructive loop execution *)

Lemma numbering_exec_in_start {S O} (m : semantics S O) P s tr t :
  exec_in m P s tr t -> P s.
Proof.
  intro Hrun; destruct Hrun; assumption.
Qed.

Lemma numbering_values_determined {S O N E V K C} (sv : ssa_view S O N E V K C)
    s args cs ds :
  Forall2 (fun y c => val sv s y = Some c) args cs ->
  Forall2 (fun y d => val sv s y = Some d) args ds -> cs = ds.
Proof.
  intro Hcs; revert ds; induction Hcs as [|y c args cs Hc Hcs IH]; intros ds Hds.
  - inversion Hds; reflexivity.
  - inversion Hds as [|y' d args' ds' Hd Hds']; subst.
    f_equal; [congruence|apply IH; exact Hds'].
Qed.

Section LoopSoundness.
Context {S O N E V K C : Type} (m : semantics S O)
  (np : numbering_problem S O N E V K C) (lp : loop_info N) (x : V).
Let sv := nsv np.
Let inside := fun s => body lp (point (base sv) s) = true.
Hypothesis Hssa : ssa_view_laws m sv.
Hypothesis Hstrict : strict_ssa_laws m sv.
Hypothesis Hloop : numbering_loop_laws m np.

Lemma numbering_outside_frame s tr t :
  body lp (home sv x) = false -> reachable_state m s -> exec_in m inside s tr t ->
  val sv t x = val sv s x.
Proof.
  intros Houtside Hreachable Hrun; revert Hreachable.
  induction Hrun as [s Hinside|s l u tr t Hinside Hstep Hrun IH]; intro Hreachable.
  - reflexivity.
  - rewrite (IH (reachable_state_step m _ _ _ Hreachable Hstep)).
    destruct (edge_covers (base_laws Hssa) _ _ _ Hreachable Hstep)
      as [Hstay|[e Htaken]].
    + eapply frame_in_stay; [exact Hstrict|exact Hreachable|exact Hstep|exact Hstay|].
      intro Heq; unfold inside in Hinside; rewrite Heq, Houtside in Hinside; discriminate.
    + eapply frame_on_edge; [exact Hstrict|exact Hreachable|exact Hstep|exact Htaken|].
      pose proof (numbering_exec_in_start m inside _ _ _ Hrun) as Hu.
      intro Heq; unfold inside in Hu; rewrite <- Heq, Houtside in Hu; discriminate.
Qed.

(** Operation steps either preserve the old option or construct a successful pure result. *)
Lemma numbering_operation_step s l t o args :
  def sv x = Op o args -> pure np o = true -> reachable_state m s -> step m s l t ->
  val sv t x = val sv s x \/
  exists cs c, Forall2 (fun y d => val sv s y = Some d) args cs /\
    op_eval sv o cs = Some c /\ val sv t x = Some c.
Proof.
  intros Hdef Hp Hreachable Hstep; destruct (val sv t x) as [c|] eqn:Hpost.
  - destruct (value_origin Hssa _ _ _ _ _ Hreachable Hstep Hpost) as [Hsame|Horigin].
    + left; symmetry; exact Hsame.
    + destruct Horigin as [[o' [args' [cs [Hdef' [Hcs Heval]]]]]|[Hparam|Harbitrary]].
      * rewrite Hdef in Hdef'; injection Hdef' as <- <-.
        right; exists cs, c; repeat split; assumption.
      * destruct Hparam as [e [b [i [z [Hparam _]]]]]; rewrite Hdef in Hparam; discriminate.
      * rewrite Hdef in Harbitrary; discriminate.
  - destruct (val sv s x) as [c|] eqn:Hpre; [|left; reflexivity].
    assert (Hchanged : val sv t x <> val sv s x) by (rewrite Hpost, Hpre; discriminate).
    destruct (loop_op_binding Hloop _ _ _ _ _ _ Hreachable Hstep Hdef Hp Hchanged)
      as [cs [d [_ [_ Hsome]]]].
    change (val sv t x = Some d) in Hsome; rewrite Hpost in Hsome; discriminate.
Qed.

Lemma numbering_arguments_transport o args s tr t cs :
  body lp (home sv x) = true -> def sv x = Op o args -> pure np o = true ->
  loop_operands_stable m np lp x -> reachable_state m s -> exec_in m inside s tr t ->
  Forall2 (fun y d => val sv t y = Some d) args cs ->
  Forall2 (fun y d => val sv s y = Some d) args cs.
Proof.
  intros Hinside Hdef Hp Hstable Hreachable Hrun Hargs.
  assert (Hsame : forall y, In y args -> val sv s y = val sv t y).
  { intros y Hy; apply (Hstable o args y s tr t Hinside Hdef Hp Hy Hreachable Hrun). }
  clear Hdef.
  revert Hsame; induction Hargs as [|y d args cs Hd Hargs IH]; intro Hsame.
  - constructor.
  - constructor.
    + rewrite (Hsame y (or_introl eq_refl)); exact Hd.
    + apply IH; intros z Hz; apply Hsame; now right.
Qed.

(** A restricted run preserves the old option or ends in a computation of its initial operands. *)
Lemma numbering_operation_run o args s tr t :
  body lp (home sv x) = true -> def sv x = Op o args -> pure np o = true ->
  loop_operands_stable m np lp x -> reachable_state m s -> exec_in m inside s tr t ->
  val sv t x = val sv s x \/
  exists cs c, Forall2 (fun y d => val sv s y = Some d) args cs /\
    op_eval sv o cs = Some c /\ val sv t x = Some c.
Proof.
  intros Hinside Hdef Hp Hstable Hreachable Hrun; revert Hreachable.
  induction Hrun as [s Hs|s l u tr t Hs Hstep Hrun IH]; intro Hreachable.
  - left; reflexivity.
  - destruct (IH (reachable_state_step m _ _ _ Hreachable Hstep))
      as [Hsame|[cs [c [Hargs [Heval Hval]]]]].
    + destruct (numbering_operation_step s l u o args Hdef Hp Hreachable Hstep)
        as [Hpreserved|[cs [c [Hargs [Heval Hval]]]]].
      * left; congruence.
      * right; exists cs, c; repeat split; try assumption; congruence.
    + right; exists cs, c; repeat split; try assumption.
      eapply numbering_arguments_transport; try eassumption.
      pose proof (numbering_exec_in_start m inside _ _ _ Hrun) as Hu.
      exact (exec_in_step s l u [] u Hs Hstep (exec_in_refl u Hu)).
Qed.

End LoopSoundness.

(** Once an invariant changes within a loop execution, its stable operands prevent another
    change. *)
Theorem loop_invariant_sound {S O N E V K C} (m : semantics S O)
    (np : numbering_problem S O N E V K C) (lp : loop_info N) (x : V) :
  ssa_view_laws m (nsv np) -> strict_ssa_laws m (nsv np) -> numbering_loop_laws m np ->
  loop_info_wf (cfg (base (nsv np))) lp -> invariant_in np lp x = true ->
  loop_operands_stable m np lp x ->
  forall s tr1 u1 tr2 u2 tr3 u3, reachable_state m s ->
    exec_in m (fun u => body lp (point (base (nsv np)) u) = true) s tr1 u1 ->
    exec_in m (fun u => body lp (point (base (nsv np)) u) = true) u1 tr2 u2 ->
    exec_in m (fun u => body lp (point (base (nsv np)) u) = true) u2 tr3 u3 ->
    val (nsv np) u1 x <> val (nsv np) u2 x -> val (nsv np) u2 x = val (nsv np) u3 x.
Proof.
  intros Hssa Hstrict Hloop Hwf Hinvariant Hstable s tr1 u1 tr2 u2 tr3 u3 Hreachable
    Hrun1 Hrun2 Hrun3 Hchanged.
  assert (Hr1 : reachable_state m u1).
  { eapply reachable_state_exec; [exact Hreachable|eapply exec_in_exec; exact Hrun1]. }
  assert (Hr2 : reachable_state m u2).
  { eapply reachable_state_exec; [exact Hr1|eapply exec_in_exec; exact Hrun2]. }
  destruct (invariant_in_shape np lp x Hinvariant) as [Houtside|[o [args [Hdef Hp]]]].
  - exfalso; apply Hchanged; symmetry; eapply numbering_outside_frame; eassumption.
  - destruct (body lp (home (nsv np) x)) eqn:Hinside.
    2: { exfalso; apply Hchanged; symmetry; eapply numbering_outside_frame; eassumption. }
    destruct (numbering_operation_run m np lp x Hssa Hloop o args _ _ _
      Hinside Hdef Hp Hstable Hr1 Hrun2) as [Hsame|[cs [c [Hcs [Hec Hc]]]]].
    + exfalso; apply Hchanged; symmetry; exact Hsame.
    + destruct (numbering_operation_run m np lp x Hssa Hloop o args _ _ _
        Hinside Hdef Hp Hstable Hr2 Hrun3) as [Hsame|[ds [d [Hds [Hed Hd]]]]].
      * symmetry; exact Hsame.
      * pose proof (numbering_arguments_transport m np lp x o args _ _ _ ds
          Hinside Hdef Hp Hstable Hr1 Hrun2 Hds) as Hds'.
        pose proof (numbering_values_determined (nsv np) u1 args cs ds Hcs Hds') as Heq.
        subst ds; congruence.
Qed.

(** * The coarsest stable optimistic partition *)

Section Coarsest.
Context {S O N E V K C : Type} (EN : encoding N) (EV : encoding V) (EK : encoding K)
  (np : numbering_problem S O N E V K C).
Let sv := nsv np.

Lemma numbering_signature_op rep x o args :
  def sv x = Op o args -> pure np o = true ->
  Forall (fun y => In y (nvalues np)) args ->
  numbering_signature EN EV EK np rep x =
    2%positive :: encode EK o :: map (fun y => encode EV (rep y)) args.
Proof.
  intros Hdef Hp Hlisted; unfold numbering_signature; fold sv; rewrite Hdef, Hp; cbn.
  assert (Hargs : forallb (fun y => FinSet.mem EV y (numbering_inventory EV np)) args = true).
  { apply forallb_forall; intros y Hy; apply (proj2 (FinSet.of_list_spec EV y (nvalues np))).
    exact (proj1 (Forall_forall _ _) Hlisted y Hy). }
  now rewrite Hargs.
Qed.

Lemma numbering_signature_param rep x b i args :
  def sv x = Param b i -> ~ In b (Graph.entries (cfg (base sv))) ->
  read_rows (rows EN b (numbering_incoming EN np)) i = Some args ->
  Forall (fun y => In y (nvalues np)) args ->
  numbering_signature EN EV EK np rep x =
    3%positive :: encode EN b :: map (fun y => encode EV (rep y)) args.
Proof.
  intros Hdef Hentry Hread Hlisted; unfold numbering_signature; fold sv; rewrite Hdef.
  assert (Hnot : FinSet.mem EN b (numbering_entries EN np) = false).
  { destruct (FinSet.mem EN b (numbering_entries EN np)) eqn:Hb; [|reflexivity].
    exfalso; apply Hentry; apply (proj1 (FinSet.of_list_spec EN b _)); exact Hb. }
  rewrite Hnot, Hread.
  assert (Hargs : forallb (fun y => FinSet.mem EV y (numbering_inventory EV np)) args = true).
  { apply forallb_forall; intros y Hy; apply (proj2 (FinSet.of_list_spec EV y (nvalues np))).
    exact (proj1 (Forall_forall _ _) Hlisted y Hy). }
  now rewrite Hargs.
Qed.

Lemma numbering_maps_refine rep other xs ys :
  (forall a b, numbering_related np other a b -> rep a = rep b) ->
  Forall2 (numbering_related np other) xs ys ->
  map (fun y => encode EV (rep y)) xs = map (fun y => encode EV (rep y)) ys.
Proof.
  intros Hrefine Hargs; induction Hargs as [|a b xs ys Hab Hargs IH]; cbn; [reflexivity|].
  rewrite (Hrefine a b Hab), IH; reflexivity.
Qed.

Lemma numbering_signature_refines rep other x y :
  (forall a b, numbering_related np other a b -> rep a = rep b) ->
  numbering_signature EN EV EK np other x = numbering_signature EN EV EK np other y ->
  numbering_signature EN EV EK np rep x = numbering_signature EN EV EK np rep y.
Proof.
  intros Hrefine Heq.
  destruct (numbering_signature_cases EN EV EK np other x) as [Hx|[Hx|Hx]];
    destruct (numbering_signature_cases EN EV EK np other y) as [Hy|[Hy|Hy]].
  - rewrite Hx, Hy in Heq; unfold numbering_single in Heq; injection Heq as Heq.
    apply (encode_injective EV) in Heq; now subst y.
  - destruct Hy as [o [args [_ [_ [_ Hy]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hy as [b [i [args [_ [_ [_ [_ Hy]]]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [o [args [_ [_ [_ Hx]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [o [xs [Hdx [Hp [Hxs Hx]]]]].
    destruct Hy as [p [ys [Hdy [Hp' [Hys Hy]]]]].
    rewrite Hx, Hy in Heq; injection Heq as Hop Hargs.
    apply (encode_injective EK) in Hop; subst p.
    rewrite (numbering_signature_op rep x o xs Hdx Hp Hxs),
      (numbering_signature_op rep y o ys Hdy Hp Hys).
    f_equal; f_equal; eapply numbering_maps_refine; [exact Hrefine|].
    apply (numbering_argument_classes EV np other); assumption.
  - destruct Hx as [o [args [_ [_ [_ Hx]]]]].
    destruct Hy as [b [i [ys [_ [_ [_ [_ Hy]]]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [b [i [args [_ [_ [_ [_ Hx]]]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [b [i [args [_ [_ [_ [_ Hx]]]]]]].
    destruct Hy as [o [ys [_ [_ [_ Hy]]]]]; rewrite Hx, Hy in Heq; discriminate.
  - destruct Hx as [b [i [xs [Hdx [Hentry [Hreadx [Hxs Hx]]]]]]].
    destruct Hy as [b' [j [ys [Hdy [Hentry' [Hready [Hys Hy]]]]]]].
    rewrite Hx, Hy in Heq; injection Heq as Hb Hargs.
    apply (encode_injective EN) in Hb; subst b'.
    rewrite (numbering_signature_param rep x b i xs Hdx Hentry Hreadx Hxs),
      (numbering_signature_param rep y b j ys Hdy Hentry Hready Hys).
    f_equal; f_equal; eapply numbering_maps_refine; [exact Hrefine|].
    apply (numbering_argument_classes EV np other); assumption.
Qed.

Lemma numbering_signature_header rep x :
  firstn 2 (numbering_signature EN EV EK np rep x) =
    firstn 2 (numbering_signature EN EV EK np (fun y => y) x).
Proof.
  unfold numbering_signature; fold sv.
  destruct (def sv x) as [o args|b i|]; [| |reflexivity].
  - destruct (pure np o && forallb (fun y => FinSet.mem EV y (numbering_inventory EV np)) args);
      reflexivity.
  - destruct (FinSet.mem EN b (numbering_entries EN np)); [reflexivity|].
    destruct (read_rows (rows EN b (numbering_incoming EN np)) i) as [args|];
      [|reflexivity].
    destruct (forallb (fun y => FinSet.mem EV y (numbering_inventory EV np)) args);
      reflexivity.
Qed.

(** Every accepted congruence is contained in the stable partition returned by optimistic
    numbering. *)
Theorem optimistic_numbering_coarsest other : numbering_check EN EV EK np other = true ->
  forall x y, numbering_related np other x y ->
    optimistic_numbering EN EV EK np x = optimistic_numbering EN EV EK np y.
Proof.
  intro Hother.
  pose (P := fun rep : V -> V => forall x y, numbering_related np other x y -> rep x = rep y).
  assert (Hinitial : P (numbering_group EV (nvalues np)
      (fun x => firstn 2 (numbering_signature EN EV EK np (fun y => y) x)))).
  { intros x y [Hx [Hy Heq]]; apply (proj2 (numbering_group_eq EV _ _ x y Hx Hy)).
    rewrite <- (numbering_signature_header other x), <- (numbering_signature_header other y).
    f_equal; eapply numbering_check_signatures; eassumption. }
  assert (Hstep : forall rep, P rep -> P (numbering_optimistic_step EN EV EK np rep)).
  { intros rep Hrep; unfold numbering_optimistic_step.
    destruct (numbering_check EN EV EK np rep); [exact Hrep|].
    intros x y Hxy; destruct Hxy as [Hx [Hy Heq]].
    apply (proj2 (numbering_refine_eq EN EV EK np rep x y Hx Hy)); split.
    - apply Hrep; repeat split; assumption.
    - eapply numbering_signature_refines; [exact Hrep|].
      eapply numbering_check_signatures; eassumption. }
  exact (numbering_iterate_preserves P _ Hstep _ _ Hinitial).
Qed.

End Coarsest.
