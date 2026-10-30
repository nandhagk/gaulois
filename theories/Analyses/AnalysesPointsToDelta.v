(** * Indexed delta propagation for Andersen constraints

    Facts and activated inclusion edges are deduplicated events in a shared worklist.
    For example, processing a new heap-to-value edge propagates the heap's old facts as well.
    Builds on: AnalysesPointsToBase and canonical encoded maps and sets. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointLeast.
From Gaulois.Views Require Import ViewsSemantics.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesPointsToBase.
Import List.ListNotations.

Module PtsDelta.

Section Engine.
Context {K A : Type} (EK : encoding K) (EA : encoding A).

(** An event is one atom added to one indexed source bucket. *)
Definition event := (K * A)%type.

Definition event_encoding : encoding event := pair_encoding EK EA.

(** Each bucket is a canonical finite set; absent buckets are empty. *)
Definition database := Map.t K (FinSet.t A).

Definition row (db : database) (k : K) : FinSet.t A :=
  match Map.get EK k db with
  | Some s => s
  | None => FinSet.empty
  end.

Definition holds (db : database) (e : event) : Prop :=
  FinSet.mem EA (snd e) (row db (fst e)) = true.

Definition put_row (e : event) (db : database) : database :=
  Map.set EK (fst e) (FinSet.add EA (snd e) (row db (fst e))) db.

Lemma row_put e db k :
  row (put_row e db) k =
    if Pos.eqb (encode EK k) (encode EK (fst e))
    then FinSet.add EA (snd e) (row db (fst e)) else row db k.
Proof.
  unfold row, put_row; destruct (Pos.eqb (encode EK k) (encode EK (fst e))) eqn:Heq.
  - apply Pos.eqb_eq, (encode_injective EK) in Heq; subst k.
    rewrite Map.get_set_same; reflexivity.
  - assert (Hne : k <> fst e) by (intro H; subst k; rewrite Pos.eqb_refl in Heq; discriminate).
    rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Lemma holds_put e db x : holds (put_row e db) x <-> x = e \/ holds db x.
Proof.
  unfold holds; rewrite row_put; destruct x as [k a], e as [j b]; cbn [fst snd] in *.
  destruct (Pos.eqb (encode EK k) (encode EK j)) eqn:Heq.
  - apply Pos.eqb_eq, (encode_injective EK) in Heq; subst k.
    rewrite FinSet.mem_add; split; intros [H|H]; try (now right).
    + left; now subst a.
    + left; now injection H.
  - assert (Hne : k <> j) by (intro H; subst k; rewrite Pos.eqb_refl in Heq; discriminate).
    split; [now right|intros [H|H]; [injection H; contradiction|exact H]].
Qed.

Definition rows_wf (db : database) : Prop :=
  Map.wf EK db /\ forall k, FinSet.wf EA (row db k).

Lemma rows_empty : rows_wf Map.empty.
Proof.
  split; [apply Map.wf_empty|intro k; unfold row; rewrite Map.get_empty; apply Map.wf_empty].
Qed.

Lemma holds_empty e : ~ holds Map.empty e.
Proof.
  unfold holds, row; rewrite Map.get_empty, FinSet.mem_empty; discriminate.
Qed.

Lemma rows_put e db : rows_wf db -> rows_wf (put_row e db).
Proof.
  intros [Hmap Hrows]; split; [apply Map.wf_set; exact Hmap|].
  intro k; rewrite row_put; destruct (Pos.eqb _ _).
  - apply Map.wf_set, Hrows.
  - apply Hrows.
Qed.

(** Processed events and pending events partition the indexed database. *)
Record state : Type := State {
  current : database;
  pending : list event;
  processed : FinSet.t event
}.

Definition empty : state := State Map.empty [] FinSet.empty.

Definition insert (e : event) (st : state) : state :=
  if FinSet.mem EA (snd e) (row (current st) (fst e)) then st else
    State (put_row e (current st)) (e :: pending st) (processed st).

Fixpoint insert_all (es : list event) (st : state) : state :=
  match es with
  | [] => st
  | e :: rest => insert_all rest (insert e st)
  end.

Lemma insert_holds e st x :
  holds (current (insert e st)) x <-> x = e \/ holds (current st) x.
Proof.
  unfold insert; destruct (FinSet.mem EA (snd e) (row (current st) (fst e))) eqn:Hmem.
  - cbn; change (holds (current st) e) in Hmem; split; [now right|].
    intros [->|H]; assumption.
  - cbn; apply holds_put.
Qed.

Lemma insert_processed e st : processed (insert e st) = processed st.
Proof.
  unfold insert; destruct (FinSet.mem _ _ _); reflexivity.
Qed.

Lemma insert_all_holds es st x :
  holds (current (insert_all es st)) x <-> In x es \/ holds (current st) x.
Proof.
  revert st; induction es as [|e es IH]; intro st; cbn [insert_all].
  - cbn [In]; tauto.
  - rewrite IH, insert_holds; cbn [In]; intuition congruence.
Qed.

Lemma insert_all_processed es st : processed (insert_all es st) = processed st.
Proof.
  revert st; induction es as [|e es IH]; intro st; cbn [insert_all]; [reflexivity|].
  rewrite IH, insert_processed; reflexivity.
Qed.

Variable universe : list event.

(** Validity records finite support, cache agreement through [holds], and exact queue coverage. *)
Record valid (st : state) : Prop := Valid {
  current_wf : rows_wf (current st);
  processed_wf : FinSet.wf event_encoding (processed st);
  current_supported : forall e, holds (current st) e -> In e universe;
  pending_nodup : NoDup (pending st);
  pending_spec : forall e, In e (pending st) <->
    holds (current st) e /\ ~ FinSet.mem event_encoding e (processed st) = true;
  processed_present : forall e, FinSet.mem event_encoding e (processed st) = true ->
    holds (current st) e
}.

Lemma valid_empty : valid empty.
Proof.
  constructor; cbn [empty current pending processed].
  - apply rows_empty.
  - apply Map.wf_empty.
  - intros e He; exfalso; exact (holds_empty e He).
  - constructor.
  - intro e; split; [contradiction|intros [He _]; exfalso; exact (holds_empty e He)].
  - intros e He; rewrite FinSet.mem_empty in He; discriminate.
Qed.

Lemma valid_insert e st : valid st -> In e universe -> valid (insert e st).
Proof.
  intros Hvalid He; unfold insert; destruct (FinSet.mem EA (snd e)
    (row (current st) (fst e))) eqn:Hmem; [exact Hvalid|].
  destruct Hvalid as [Hrows Hdone Hsupport Hnodup Hpending Hpresent].
  assert (Hfresh : ~ holds (current st) e) by (unfold holds; rewrite Hmem; discriminate).
  assert (Hnotdone : ~ FinSet.mem event_encoding e (processed st) = true).
  { intro H; apply Hfresh, Hpresent; exact H. }
  constructor; cbn [current pending processed].
  - apply rows_put; exact Hrows.
  - exact Hdone.
  - intros x Hx; apply holds_put in Hx; destruct Hx as [->|Hx]; [exact He|apply Hsupport; exact Hx].
  - constructor; [intro H; apply Hfresh; apply Hpending in H; tauto|exact Hnodup].
  - intro x; rewrite holds_put; cbn [In]; rewrite Hpending.
    split.
    + intros [->|[Hx Hnd]]; auto.
    + intros [[->|Hx] Hnd]; auto.
  - intros x Hx; apply holds_put; right; apply Hpresent; exact Hx.
Qed.

Lemma valid_insert_all es st : valid st -> incl es universe -> valid (insert_all es st).
Proof.
  revert st; induction es as [|e es IH]; intros st Hvalid Hin; cbn [insert_all]; [exact Hvalid|].
  apply IH; [apply valid_insert; [exact Hvalid|apply Hin; now left]|].
  intros x Hx; apply Hin; now right.
Qed.

Definition finish_event (e : event) (rest : list event) (st : state) : state :=
  State (current st) rest (FinSet.add event_encoding e (processed st)).

Lemma valid_finish e rest st : valid st -> pending st = e :: rest ->
  valid (finish_event e rest st).
Proof.
  intros Hvalid Hqueue; destruct Hvalid as [Hrows Hdone Hsupport Hnodup Hpending Hpresent].
  assert (He : holds (current st) e) by (apply Hpending; rewrite Hqueue; now left).
  assert (Hfresh : ~ FinSet.mem event_encoding e (processed st) = true).
  { apply Hpending; rewrite Hqueue; now left. }
  rewrite Hqueue in Hnodup; inversion Hnodup as [|? ? Hnotin Htail]; subst.
  constructor; cbn [finish_event current pending processed].
  - exact Hrows.
  - apply Map.wf_set; exact Hdone.
  - exact Hsupport.
  - exact Htail.
  - intro x; rewrite FinSet.mem_add; split.
    + intro Hx; assert (Hwhole : In x (pending st)) by (rewrite Hqueue; now right).
      apply Hpending in Hwhole; destruct Hwhole as [Hxmem Hxdone]; split; [exact Hxmem|].
      intros [->|H]; [contradiction|contradiction].
    + intros [Hxmem Hxdone]; assert (Hin : In x (pending st)) by (apply Hpending; tauto).
      rewrite Hqueue in Hin; destruct Hin as [->|Hin]; [exfalso; apply Hxdone; now left|exact Hin].
  - intros x Hx; apply FinSet.mem_add in Hx; destruct Hx as [->|Hx];
      [exact He|apply Hpresent; exact Hx].
Qed.

Lemma processed_bound st : valid st -> FinSet.size (processed st) <= length universe.
Proof.
  intro Hv; apply (FinSet.size_le_length event_encoding); [exact (processed_wf st Hv)|].
  intros e He; apply (current_supported st Hv), (processed_present st Hv); exact He.
Qed.

Lemma processed_grows e rest st : valid st -> pending st = e :: rest ->
  FinSet.size (processed st) < FinSet.size (processed (finish_event e rest st)).
Proof.
  intros Hv Hqueue; cbn [finish_event processed]; apply (FinSet.size_lt event_encoding).
  - exact (processed_wf st Hv).
  - apply Map.wf_set; exact (processed_wf st Hv).
  - apply FinSet.subset_spec; [exact (processed_wf st Hv)|].
    intros x Hx; apply FinSet.mem_add; now right.
  - apply Bool.not_true_is_false; intro Hsub.
    assert (Hadded : FinSet.mem event_encoding e
      (FinSet.add event_encoding e (processed st)) = true) by (apply FinSet.mem_add; now left).
    apply (set_member_subset event_encoding _ _ Hsub) in Hadded.
    assert (Hpending : In e (pending st)) by (rewrite Hqueue; now left).
    apply (pending_spec st Hv) in Hpending; tauto.
Qed.

Variable produce : database -> event -> list event.
Hypothesis produce_supported : forall st e, valid st -> holds (current st) e ->
  incl (produce (current st) e) universe.

(** One event is processed once, and only genuinely new consequences enter the queue. *)
Definition advance (st : state) : state :=
  match pending st with
  | [] => st
  | e :: rest => insert_all (produce (current st) e) (finish_event e rest st)
  end.

Lemma advance_valid st : valid st -> valid (advance st).
Proof.
  intro Hv; unfold advance; destruct (pending st) as [|e rest] eqn:Hqueue; [exact Hv|].
  apply valid_insert_all; [apply valid_finish; assumption|].
  apply produce_supported; [exact Hv|apply (pending_spec st Hv); rewrite Hqueue; now left].
Qed.

Lemma advance_holds st e rest x : pending st = e :: rest ->
  (holds (current (advance st)) x <->
    In x (produce (current st) e) \/ holds (current st) x).
Proof.
  intro Hqueue; unfold advance; rewrite Hqueue, insert_all_holds; reflexivity.
Qed.

Lemma advance_processed st e rest : pending st = e :: rest ->
  processed (advance st) = FinSet.add event_encoding e (processed st).
Proof.
  intro Hqueue; unfold advance; rewrite Hqueue, insert_all_processed; reflexivity.
Qed.

Lemma advance_empty st : pending st = [] -> advance st = st.
Proof.
  intro Hqueue; unfold advance; now rewrite Hqueue.
Qed.

Lemma advance_nonempty st : pending (advance st) <> [] -> pending st <> [].
Proof.
  intros Hout Hin; apply Hout; rewrite advance_empty by exact Hin; exact Hin.
Qed.

Lemma advance_progress st : valid st -> pending (advance st) <> [] ->
  FinSet.size (processed st) < FinSet.size (processed (advance st)).
Proof.
  intros Hv Hout; assert (Hin := advance_nonempty st Hout).
  unfold advance; destruct (pending st) as [|e rest] eqn:Hqueue; [contradiction|].
  rewrite insert_all_processed; apply processed_grows; assumption.
Qed.

(** Binary fuel counts individual events, using logarithmic recursion depth. *)
Fixpoint run (fuel : positive) (st : state) : state :=
  match fuel with
  | xH => advance st
  | xO p => run p (run p st)
  | xI p => advance (run p (run p st))
  end.

Lemma run_invariant (P : state -> Prop) :
  (forall st, P st -> P (advance st)) ->
  forall fuel st, P st -> P (run fuel st).
Proof.
  intros Hstep fuel; induction fuel as [p IH|p IH|]; intros st HP; cbn [run].
  - apply Hstep, IH, IH; exact HP.
  - apply IH, IH; exact HP.
  - apply Hstep; exact HP.
Qed.

Lemma run_valid fuel st : valid st -> valid (run fuel st).
Proof.
  apply run_invariant, advance_valid.
Qed.

Lemma run_empty fuel st : pending st = [] -> run fuel st = st.
Proof.
  revert st; induction fuel as [p IH|p IH|]; intros st Hempty; cbn [run].
  - rewrite !(IH st Hempty); apply advance_empty; exact Hempty.
  - rewrite !(IH st Hempty); reflexivity.
  - apply advance_empty; exact Hempty.
Qed.

Lemma run_nonempty fuel st : pending (run fuel st) <> [] -> pending st <> [].
Proof.
  intros Hout Hin; apply Hout; rewrite run_empty by exact Hin; exact Hin.
Qed.

Lemma run_progress fuel st : valid st -> pending (run fuel st) <> [] ->
  FinSet.size (processed st) + Pos.to_nat fuel <= FinSet.size (processed (run fuel st)).
Proof.
  revert st; induction fuel as [p IH|p IH|]; intros st Hv Hout; cbn [run] in *.
  - pose proof (run_valid p st Hv) as Hv1.
    pose proof (run_valid p (run p st) Hv1) as Hv2.
    assert (Hout2 := advance_nonempty _ Hout).
    assert (Hout1 := run_nonempty p _ Hout2).
    pose proof (IH st Hv Hout1) as Hfirst.
    pose proof (IH (run p st) Hv1 Hout2) as Hsecond.
    pose proof (advance_progress _ Hv2 Hout) as Hlast.
    rewrite Pos2Nat.inj_xI; lia.
  - pose proof (run_valid p st Hv) as Hv1.
    assert (Hout1 := run_nonempty p _ Hout).
    pose proof (IH st Hv Hout1) as Hfirst.
    pose proof (IH (run p st) Hv1 Hout) as Hsecond.
    rewrite Pos2Nat.inj_xO; lia.
  - pose proof (advance_progress st Hv Hout); cbn; lia.
Qed.

(** The finite event universe bounds all required work, including newly activated edges. *)
Lemma run_quiescent st : valid st ->
  pending (run (Pos.of_succ_nat (length universe)) st) = [].
Proof.
  intro Hv; destruct (pending (run (Pos.of_succ_nat (length universe)) st))
    as [|e rest] eqn:Hqueue; [reflexivity|].
  assert (Hnonempty : pending (run (Pos.of_succ_nat (length universe)) st) <> [])
    by (rewrite Hqueue; discriminate).
  pose proof (run_progress _ st Hv Hnonempty) as Hprogress.
  pose proof (processed_bound _ (run_valid (Pos.of_succ_nat (length universe)) st Hv)) as Hbound.
  rewrite SuccNat2Pos.id_succ in Hprogress; lia.
Qed.

End Engine.

Arguments State {K A}.
Arguments current {K A}.
Arguments pending {K A}.
Arguments processed {K A}.

End PtsDelta.
Import PtsDelta.

Module AndersenDelta.

Section Solver.
Context {V T : Type} (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T)).

Local Definition key := pts_key V T.
Local Definition atom := (T + key)%type.
Local Definition EK := pts_encoding EV ET.
Local Definition EA := sum_encoding ET EK.
Local Definition EE := pair_encoding EK EA.
Local Definition event := (key * atom)%type.
Local Definition state := @PtsDelta.state key atom.
Local Definition database := @PtsDelta.database key atom.

Definition fact (k : key) (t : T) : event := (k, inl t).
Definition edge (src dst : key) : event := (src, inr dst).

Definition present (st : state) (e : event) : Prop := holds EK EA (current st) e.

(** Load and store subscriptions share the pointer operand's index bucket. *)
Definition subscriptions := Map.t V (list (V + V)).

Definition subscriptions_at (ix : subscriptions) (p : V) : list (V + V) :=
  match Map.get EV p ix with
  | Some subs => subs
  | None => []
  end.

Definition subscribe (p : V) (sub : V + V) (ix : subscriptions) : subscriptions :=
  Map.set EV p (sub :: subscriptions_at ix p) ix.

Fixpoint index_subscriptions (source : list (ptr_op V T)) : subscriptions :=
  match source with
  | [] => Map.empty
  | PLoad x p :: rest => subscribe p (inl x) (index_subscriptions rest)
  | PStore p y :: rest => subscribe p (inr y) (index_subscriptions rest)
  | _ :: rest => index_subscriptions rest
  end.

Lemma subscribe_mem p sub ix q item :
  In item (subscriptions_at (subscribe p sub ix) q) <->
  (q = p /\ item = sub) \/ In item (subscriptions_at ix q).
Proof.
  unfold subscriptions_at, subscribe.
  destruct (Pos.eq_dec (encode EV q) (encode EV p)) as [Heq|Hne].
  - apply (encode_injective EV) in Heq; subst q; rewrite Map.get_set_same; cbn;
      intuition congruence.
  - assert (Hqp : q <> p) by (intro H; subst q; contradiction).
    rewrite Map.get_set_other by exact Hqp; intuition congruence.
Qed.

(** The immutable index contains precisely the listed dereference subscriptions. *)
Lemma subscriptions_spec source p item :
  In item (subscriptions_at (index_subscriptions source) p) <->
  match item with
  | inl x => In (PLoad x p) source
  | inr y => In (PStore p y) source
  end.
Proof.
  induction source as [|op source IH].
  - change (In item (match Map.get EV p (@Map.empty V (list (V + V))) with
      | Some subs => subs
      | None => []
      end) <-> match item with
      | inl x => In (@PLoad V T x p) []
      | inr y => In (@PStore V T p y) []
      end).
    rewrite Map.get_empty; destruct item; reflexivity.
  - destruct op as [x t|x y|x q|q y|x]; cbn [index_subscriptions];
      rewrite ?subscribe_mem, ?IH; destruct item; cbn [In]; intuition congruence.
Qed.

(** Allocation seeds and copy edges are indexed before the first event is processed. *)
Fixpoint seeds (source : list (ptr_op V T)) : list event :=
  match source with
  | [] => []
  | PAlloc x t :: rest => fact (PVal x) t :: seeds rest
  | PCopy x y :: rest => edge (PVal y) (PVal x) :: seeds rest
  | _ :: rest => seeds rest
  end.

Definition operands (op : ptr_op V T) : list V :=
  match op with
  | PAlloc x _ | PEscape x => [x]
  | PCopy x y | PLoad x y | PStore x y => [x; y]
  end.

Definition keys : list key :=
  map PVal (flat_map operands ops) ++ map PHeap (site_universe ET ops).

Definition atoms : list atom := map inl (site_universe ET ops) ++ map inr keys.

(** This proof-only product bounds all facts and all possible activated inclusion edges. *)
Definition universe : list event := list_prod keys atoms.

Lemma value_key op x : In op ops -> In x (operands op) -> In (PVal x) keys.
Proof.
  intros Hop Hx; unfold keys; apply in_or_app; left; apply in_map, in_flat_map.
  exists op; auto.
Qed.

Lemma heap_key t : In t (site_universe ET ops) -> In (PHeap t) keys.
Proof.
  intro Ht; unfold keys; apply in_or_app; right; apply in_map; exact Ht.
Qed.

Lemma fact_supported k t : In (fact k t) universe <->
  In k keys /\ In t (site_universe ET ops).
Proof.
  change (In (k, @inl T key t) (list_prod keys atoms) <->
    In k keys /\ In t (site_universe ET ops)).
  rewrite (in_prod_iff keys atoms k (inl t)); unfold atoms; rewrite in_app_iff.
  split.
  - intros [Hk [Ht|Ht]]; apply in_map_iff in Ht; destruct Ht as [u [Heq Hin]];
      [injection Heq as <-; auto|discriminate].
  - intros [Hk Ht]; split; [exact Hk|left; apply in_map; exact Ht].
Qed.

Lemma edge_supported s d : In (edge s d) universe <-> In s keys /\ In d keys.
Proof.
  change (In (s, @inr T key d) (list_prod keys atoms) <-> In s keys /\ In d keys).
  rewrite (in_prod_iff keys atoms s (inr d)); unfold atoms; rewrite in_app_iff.
  split.
  - intros [Hs [Hd|Hd]]; apply in_map_iff in Hd; destruct Hd as [u [Heq Hin]];
      [discriminate|injection Heq as <-; auto].
  - intros [Hs Hd]; split; [exact Hs|right; apply in_map; exact Hd].
Qed.

Lemma seeds_supported source : incl source ops -> incl (seeds source) universe.
Proof.
  induction source as [|op source IH]; intros Hsource e He; cbn [seeds] in He; [contradiction|].
  assert (Hop : In op ops) by (apply Hsource; now left).
  assert (Htail : incl source ops) by (intros x Hx; apply Hsource; now right).
  destruct op as [x t|x y|x p|p y|x]; cbn [seeds] in He;
    try (apply (IH Htail); exact He).
  - destruct He as [<-|He]; [|apply (IH Htail); exact He].
    apply fact_supported; split; [eapply value_key; [exact Hop|cbn; auto]|].
    eapply allocation_site_in; exact Hop.
  - destruct He as [<-|He]; [|apply (IH Htail); exact He].
    apply edge_supported; split; eapply value_key; [exact Hop|cbn; auto|exact Hop|cbn; auto].
Qed.

(** Activation creates a heap-to-value load edge or a value-to-heap store edge. *)
Definition activate (ix : subscriptions) (k : key) (t : T) : list event :=
  match k with
  | PVal p => map (fun sub => match sub with
    | inl x => edge (PHeap t) (PVal x)
    | inr y => edge (PVal y) (PHeap t)
    end) (subscriptions_at ix p)
  | PHeap _ => []
  end.

Definition propagate_fact (db : database) (s : key) (t : T) : list event :=
  flat_map (fun a => match a with
    | inl _ => []
    | inr d => [fact d t]
    end) (FinSet.elements (row EK db s)).

Definition propagate_edge (db : database) (s d : key) : list event :=
  flat_map (fun a => match a with
    | inl t => [fact d t]
    | inr _ => []
    end) (FinSet.elements (row EK db s)).

(** A new edge schedules the source's whole accumulated set; new facts use existing edges. *)
Definition consequences (ix : subscriptions) (db : database) (e : event) : list event :=
  match e with
  | (s, inl t) => propagate_fact db s t ++ activate ix s t
  | (s, inr d) => propagate_edge db s d
  end.

Lemma fact_propagation db s t e :
  rows_wf EK EA db ->
  (In e (propagate_fact db s t) <->
    exists d, holds EK EA db (edge s d) /\ e = fact d t).
Proof.
  intros [_ Hrows]; unfold propagate_fact; rewrite in_flat_map; split.
  - intros [a [Ha He]]; destruct a as [u|d]; cbn in He; [contradiction|].
    destruct He as [<-|[]]; exists d; split; [|reflexivity].
    unfold holds, edge; cbn [fst snd]; apply (FinSet.elements_spec EA); [apply Hrows|exact Ha].
  - intros [d [Hd ->]]; exists (inr d); split.
    + apply (FinSet.elements_spec EA); [apply Hrows|exact Hd].
    + cbn; auto.
Qed.

Lemma edge_propagation db s d e :
  rows_wf EK EA db ->
  (In e (propagate_edge db s d) <->
    exists t, holds EK EA db (fact s t) /\ e = fact d t).
Proof.
  intros [_ Hrows]; unfold propagate_edge; rewrite in_flat_map; split.
  - intros [a [Ha He]]; destruct a as [t|k]; cbn in He; [|contradiction].
    destruct He as [<-|[]]; exists t; split; [|reflexivity].
    unfold holds, fact; cbn [fst snd]; apply (FinSet.elements_spec EA); [apply Hrows|exact Ha].
  - intros [t [Ht ->]]; exists (inl t); split.
    + apply (FinSet.elements_spec EA); [apply Hrows|exact Ht].
    + cbn; auto.
Qed.

Lemma activation_spec k t e :
  In e (activate (index_subscriptions ops) k t) <->
  (exists p x, k = PVal p /\ In (PLoad x p) ops /\ e = edge (PHeap t) (PVal x)) \/
  (exists p y, k = PVal p /\ In (PStore p y) ops /\ e = edge (PVal y) (PHeap t)).
Proof.
  destruct k as [p|u]; cbn [activate].
  - rewrite in_map_iff; split.
    + intros [[x|y] [<- Hsub]]; apply subscriptions_spec in Hsub; [left|right]; eauto.
    + intros [[q [x [Heq [Hop ->]]]]|[q [y [Heq [Hop ->]]]]]; injection Heq as <-.
      * exists (inl x); split; [reflexivity|apply subscriptions_spec; exact Hop].
      * exists (inr y); split; [reflexivity|apply subscriptions_spec; exact Hop].
  - split; [contradiction|].
    intros [[p [x [Heq _]]]|[p [y [Heq _]]]]; discriminate.
Qed.

Lemma consequences_supported st e : valid EK EA universe st -> present st e ->
  incl (consequences (index_subscriptions ops) (current st) e) universe.
Proof.
  intros Hv He out Hout; pose proof (current_supported EK EA universe st Hv e He) as Hes.
  destruct e as [s [t|d]]; cbn [consequences] in Hout.
  - apply fact_supported in Hes; destruct Hes as [Hs Ht]; apply in_app_or in Hout.
    destruct Hout as [Hprop|Hactivate].
    + apply (fact_propagation _ _ _ _ (current_wf EK EA universe st Hv)) in Hprop.
      destruct Hprop as [d [Hd ->]]; apply fact_supported; split; [|exact Ht].
      apply (current_supported EK EA universe st Hv), edge_supported in Hd; tauto.
    + apply activation_spec in Hactivate; destruct Hactivate as
        [[p [x [Heq [Hop ->]]]]|[p [y [Heq [Hop ->]]]]];
        apply edge_supported; split; try (apply heap_key; exact Ht);
        eapply value_key; [exact Hop|cbn; auto|exact Hop|cbn; auto].
  - apply edge_supported in Hes; destruct Hes as [Hs Hd].
    apply (edge_propagation _ _ _ _ (current_wf EK EA universe st Hv)) in Hout.
    destruct Hout as [t [Ht ->]]; apply fact_supported; split; [exact Hd|].
    apply (current_supported EK EA universe st Hv), fact_supported in Ht; tauto.
Qed.

(** Every event has a finite inclusion derivation, independently of the worklist. *)
Inductive derivable : event -> Prop :=
  | derive_alloc : forall x t, In (PAlloc x t) ops -> derivable (fact (PVal x) t)
  | derive_copy : forall x y, In (PCopy x y) ops -> derivable (edge (PVal y) (PVal x))
  | derive_load : forall x p t, In (PLoad x p) ops -> derivable (fact (PVal p) t) ->
      derivable (edge (PHeap t) (PVal x))
  | derive_store : forall p y t, In (PStore p y) ops -> derivable (fact (PVal p) t) ->
      derivable (edge (PVal y) (PHeap t))
  | derive_propagate : forall s d t, derivable (fact s t) -> derivable (edge s d) ->
      derivable (fact d t).

Lemma seeds_derivable source : incl source ops -> forall e, In e (seeds source) -> derivable e.
Proof.
  induction source as [|op source IH]; intros Hin e He; [contradiction|].
  assert (Hop : In op ops) by (apply Hin; now left).
  assert (Htail : incl source ops) by (intros x Hx; apply Hin; now right).
  destruct op as [x t|x y|x p|p y|x]; cbn [seeds] in He;
    try (apply (IH Htail); exact He).
  - destruct He as [<-|He]; [apply derive_alloc; exact Hop|apply (IH Htail); exact He].
  - destruct He as [<-|He]; [apply derive_copy; exact Hop|apply (IH Htail); exact He].
Qed.

Lemma allocation_seed source x t : In (PAlloc x t) source -> In (fact (PVal x) t) (seeds source).
Proof.
  induction source as [|op source IH]; intros Hin; [contradiction|].
  destruct Hin as [Heq|Hin]; [subst op; cbn [seeds]; now left|].
  specialize (IH Hin); destruct op; cbn [seeds]; try exact IH; right; exact IH.
Qed.

Lemma copy_seed source x y : In (PCopy x y) source -> In (edge (PVal y) (PVal x)) (seeds source).
Proof.
  induction source as [|op source IH]; intros Hin; [contradiction|].
  destruct Hin as [Heq|Hin]; [subst op; cbn [seeds]; now left|].
  specialize (IH Hin); destruct op; cbn [seeds]; try exact IH; right; exact IH.
Qed.

Lemma consequences_derivable st e : rows_wf EK EA (current st) ->
  (forall a, present st a -> derivable a) -> derivable e ->
  forall a, In a (consequences (index_subscriptions ops) (current st) e) -> derivable a.
Proof.
  intros Hrows Hderived He a Ha; destruct e as [s [t|d]]; cbn [consequences] in Ha.
  - apply in_app_or in Ha; destruct Ha as [Hprop|Hactive].
    + apply (fact_propagation _ _ _ _ Hrows) in Hprop; destruct Hprop as [d [Hd ->]].
      eapply derive_propagate; [exact He|apply Hderived; exact Hd].
    + apply activation_spec in Hactive; destruct Hactive as
        [[p [x [-> [Hop ->]]]]|[p [y [-> [Hop ->]]]]].
      * eapply derive_load; eassumption.
      * eapply derive_store; eassumption.
  - apply (edge_propagation _ _ _ _ Hrows) in Ha; destruct Ha as [t [Ht ->]].
    eapply derive_propagate; [apply Hderived; exact Ht|exact He].
Qed.

Definition initial : state := insert_all EK EA (seeds ops) PtsDelta.empty.

Definition step (st : state) : state :=
  advance EK EA (consequences (index_subscriptions ops)) st.

Definition done_event (st : state) (e : event) : Prop :=
  FinSet.mem EE e (processed st) = true.

(** Processed premises have generated all their unary and binary propagation obligations. *)
Record invariant (st : state) : Prop := Invariant {
  engine_valid : valid EK EA universe st;
  events_derivable : forall e, present st e -> derivable e;
  seeds_present : forall e, In e (seeds ops) -> present st e;
  activation_covered : forall k t, done_event st (fact k t) ->
    forall e, In e (activate (index_subscriptions ops) k t) -> present st e;
  propagation_covered : forall s d t,
    done_event st (fact s t) -> done_event st (edge s d) -> present st (fact d t)
}.

Lemma initial_invariant : invariant initial.
Proof.
  constructor.
  - apply valid_insert_all; [apply valid_empty|apply seeds_supported; intros x Hx; exact Hx].
  - intros e He; apply insert_all_holds in He; destruct He as [He|He].
    + eapply seeds_derivable; [intros x Hx; exact Hx|exact He].
    + exfalso; exact (holds_empty EK EA e He).
  - intros e He; apply insert_all_holds; now left.
  - intros k t Hdone; unfold done_event, initial in Hdone; rewrite insert_all_processed in Hdone.
    change (FinSet.mem EE (fact k t) FinSet.empty = true) in Hdone.
    rewrite FinSet.mem_empty in Hdone; discriminate.
  - intros s d t Hdone; unfold done_event, initial in Hdone; rewrite insert_all_processed in Hdone.
    change (FinSet.mem EE (fact s t) FinSet.empty = true) in Hdone.
    rewrite FinSet.mem_empty in Hdone; discriminate.
Qed.

Lemma step_invariant st : invariant st -> invariant (step st).
Proof.
  intro Hinv; destruct (pending st) as [|e rest] eqn:Hqueue.
  - unfold step; rewrite advance_empty by exact Hqueue; exact Hinv.
  - pose proof (engine_valid st Hinv) as Hv.
    assert (Hpending : In e (pending st)) by (rewrite Hqueue; now left).
    assert (He : present st e) by
      (exact (proj1 (proj1 (pending_spec EK EA universe st Hv e) Hpending))).
    assert (Hnew : forall x, present (step st) x <->
      In x (consequences (index_subscriptions ops) (current st) e) \/ present st x).
    { intro x; apply advance_holds with (rest := rest); exact Hqueue. }
    assert (Hdone : forall x, done_event (step st) x <-> x = e \/ done_event st x).
    { intro x; unfold done_event, step; rewrite (advance_processed EK EA _ st e rest Hqueue).
      apply FinSet.mem_add. }
    constructor.
    + apply advance_valid; [exact consequences_supported|exact Hv].
    + intros x Hx; apply Hnew in Hx; destruct Hx as [Hx|Hx].
      * eapply consequences_derivable; [exact (current_wf EK EA universe st Hv)|
          exact (events_derivable st Hinv)|apply (events_derivable st Hinv); exact He|exact Hx].
      * apply (events_derivable st Hinv); exact Hx.
    + intros x Hx; apply Hnew; right; apply (seeds_present st Hinv); exact Hx.
    + intros k t Hprocessed out Hactive; apply Hdone in Hprocessed; apply Hnew.
      destruct Hprocessed as [<-|Hprocessed].
      * left; cbn [consequences fact]; apply in_or_app; now right.
      * right; eapply activation_covered; eassumption.
    + intros s d t Hfact Hedge; apply Hdone in Hfact; apply Hdone in Hedge; apply Hnew.
      destruct Hfact as [Hfact|Hfact]; destruct Hedge as [Hedge|Hedge].
      * rewrite <- Hfact in Hedge; discriminate.
      * left; rewrite <- Hfact; cbn [consequences fact]; apply in_or_app; left.
        apply (fact_propagation _ _ _ _ (current_wf EK EA universe st Hv)).
        exists d; split; [apply (processed_present EK EA universe st Hv); exact Hedge|reflexivity].
      * left; rewrite <- Hedge; cbn [consequences edge].
        apply (edge_propagation _ _ _ _ (current_wf EK EA universe st Hv)).
        exists t; split; [apply (processed_present EK EA universe st Hv); exact Hfact|reflexivity].
      * right; eapply propagation_covered; eassumption.
Qed.

(** Every derivation is below every independent query post-solution. *)
Lemma derivation_below (sigma : key -> pts_set ET ops) :
  pts_closed ET ops sigma -> forall e, derivable e ->
  match e with
  | (k, inl t) => fmem ET t (sigma k) = true
  | (s, inr d) => forall t, fmem ET t (sigma s) = true -> fmem ET t (sigma d) = true
  end.
Proof.
  intros Hclosed e Hderive; induction Hderive as
    [x t Hop|x y Hop|x p t Hop Hpointer IH|p y t Hop Hpointer IH|
      s d t Hfact IHfact Hedge IHedge]; cbn [fact edge] in *.
  - eapply pts_alloc_closed; eassumption.
  - intros t Ht; eapply pts_copy_closed; eassumption.
  - intros u Hu; eapply pts_load_closed; eassumption.
  - intros u Hu; eapply pts_store_closed; eassumption.
  - apply IHedge; exact IHfact.
Qed.

(** The executable bound computes a cardinality formula, without constructing the product. *)
Definition event_bound : nat :=
  let key_count := length keys in key_count * (length (site_universe ET ops) + key_count).

Lemma universe_length : length universe = event_bound.
Proof.
  change (length (list_prod keys atoms) =
    length keys * (length (site_universe ET ops) + length keys)).
  rewrite (length_prod keys atoms); unfold atoms; rewrite length_app, !length_map; reflexivity.
Qed.

(** The index and initialized copy-edge buckets are shared by every iteration. *)
Definition solved : state :=
  let ix := index_subscriptions ops in
  let start := initial in
  run EK EA (consequences ix) (Pos.of_succ_nat event_bound) start.

Lemma solved_invariant : invariant solved.
Proof.
  unfold solved; apply run_invariant; [apply step_invariant|apply initial_invariant].
Qed.

(** All queued work, including late edge activation, has been discharged. *)
Lemma solved_quiescent : pending solved = [].
Proof.
  unfold solved; rewrite <- universe_length.
  apply run_quiescent with (universe := universe).
  - exact consequences_supported.
  - exact (engine_valid initial initial_invariant).
Qed.

Lemma quiescent_processed st : invariant st -> pending st = [] ->
  forall e, present st e -> done_event st e.
Proof.
  intros Hinv Hempty e He; unfold done_event.
  destruct (FinSet.mem EE e (processed st)) eqn:Hdone; [reflexivity|].
  exfalso; assert (Hnotdone : ~ FinSet.mem EE e (processed st) = true)
    by (rewrite Hdone; discriminate).
  pose proof (proj2 (pending_spec EK EA universe st (engine_valid st Hinv) e)
    (conj He Hnotdone)) as Hin.
  exact (eq_ind (pending st) (fun es => In e es) Hin [] Hempty).
Qed.

(** Output projects the fact atoms from a source bucket, retaining their canonical set. *)
Definition values (db : database) (k : key) : FinSet.t T :=
  FinSet.of_list ET (flat_map (fun a => match a with
    | inl t => [t]
    | inr _ => []
    end) (FinSet.elements (row EK db k))).

Lemma values_mem db k t : rows_wf EK EA db ->
  (FinSet.mem ET t (values db k) = true <-> holds EK EA db (fact k t)).
Proof.
  intros [_ Hrows]; unfold values; rewrite FinSet.of_list_spec, in_flat_map; split.
  - intros [[u|d] [Hu Ht]]; cbn in Ht; [|contradiction].
    destruct Ht as [->|[]]; apply (FinSet.elements_spec EA); [apply Hrows|exact Hu].
  - intro Ht; exists (inl t); split.
    + apply (FinSet.elements_spec EA); [apply Hrows|exact Ht].
    + cbn; auto.
Qed.

Lemma values_within st : valid EK EA universe st ->
  forall k, within_set ET (site_universe ET ops) (values (current st) k).
Proof.
  intros Hv k; split; [apply FinSet.wf_fold_add, Map.wf_empty|].
  intros t Ht; apply (values_mem _ _ _ (current_wf EK EA universe st Hv)) in Ht.
  apply (current_supported EK EA universe st Hv), fact_supported in Ht; tauto.
Qed.

Definition result (st : state) (Hv : valid EK EA universe st) : key -> pts_set ET ops :=
  fun k => exist _ (values (current st) k) (values_within st Hv k).

(** The production result runs only the indexed delta producer. *)
Definition answer : key -> pts_set ET ops :=
  let st := solved in result st (engine_valid st solved_invariant).

Lemma answer_mem k t : fmem ET t (answer k) = true <-> present solved (fact k t).
Proof.
  apply values_mem; exact (current_wf EK EA universe solved (engine_valid solved solved_invariant)).
Qed.

Lemma answer_closed : pts_closed ET ops answer.
Proof.
  pose proof solved_invariant as Hinv; pose proof solved_quiescent as Hempty.
  pose proof (quiescent_processed solved Hinv Hempty) as Hdone.
  constructor.
  - intros x t Hop; apply answer_mem, (seeds_present solved Hinv), allocation_seed; exact Hop.
  - intros x y t Hop Ht; apply answer_mem in Ht; apply answer_mem.
    eapply propagation_covered; [exact Hinv|apply Hdone; exact Ht|].
    apply Hdone, (seeds_present solved Hinv), copy_seed; exact Hop.
  - intros x p u t Hop Hu Ht; apply answer_mem in Hu; apply answer_mem in Ht; apply answer_mem.
    assert (Hedge : present solved (edge (PHeap u) (PVal x))).
    { eapply activation_covered; [exact Hinv|apply Hdone; exact Hu|].
      apply activation_spec; left; exists p, x; auto. }
    eapply propagation_covered; [exact Hinv|apply Hdone; exact Ht|apply Hdone; exact Hedge].
  - intros p y u t Hop Hu Ht; apply answer_mem in Hu; apply answer_mem in Ht; apply answer_mem.
    assert (Hedge : present solved (edge (PVal y) (PHeap u))).
    { eapply activation_covered; [exact Hinv|apply Hdone; exact Hu|].
      apply activation_spec; right; exists p, y; auto. }
    eapply propagation_covered; [exact Hinv|apply Hdone; exact Ht|apply Hdone; exact Hedge].
Qed.

(** The direct producer returns the least independent inclusion solution. *)
Lemma answer_least : least_solution (pts_lattice ET ops) (andersen_system EV ET ops) answer.
Proof.
  split; [apply pts_closed_post, answer_closed|].
  intros sigma Hpost k; apply pts_le; intros t Ht; apply answer_mem in Ht.
  exact (derivation_below sigma (pts_post_closed EV ET ops sigma Hpost) _
    (events_derivable solved solved_invariant _ Ht)).
Qed.

End Solver.

End AndersenDelta.
Import AndersenDelta.

(** Compute the directly proved indexed delta solution, sharing the prepared producer result. *)
Definition andersen_delta {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) : pts_key V T -> pts_set ET ops :=
  AndersenDelta.answer EV ET ops.

(** Delta propagation computes the least solution of the independent constraint system. *)
Theorem andersen_delta_least {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) :
  least_solution (pts_lattice ET ops) (andersen_system EV ET ops) (andersen_delta EV ET ops).
Proof.
  apply AndersenDelta.answer_least.
Qed.

(** The actual delta result contains every concrete reachable value and heap points-to fact. *)
Theorem andersen_delta_sound {S O V C L T} (m : semantics S O)
    (pv : ptr_view S V C L T) (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) :
  ptr_view_laws m pv ops ->
  forall s, reachable_state m s ->
    (forall x t, pts_of pv s x = Some t ->
      fmem ET t (andersen_delta EV ET ops (PVal x)) = true) /\
    (forall t0 t, heap_pts pv s t0 t ->
      fmem ET t (andersen_delta EV ET ops (PHeap t0)) = true).
Proof.
  intro Hlaws; exact (andersen_sound m pv EV ET ops (andersen_delta EV ET ops)
    Hlaws (proj1 (andersen_delta_least EV ET ops))).
Qed.
