(** * Andersen inclusion constraints

    Pointer effects specify a finite system independently of its production solver.
    For example, storing y through p includes y's sites in every heap cell named by p.
    Builds on: CollectionsFinSet, OrderPowerset, FixpointTotal and ViewsMemory. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast
  FixpointWorklist FixpointTotal.
From Gaulois.Views Require Import ViewsSemantics ViewsMemory.
From Gaulois.Analyses Require Import AnalysesLiveness.
Import List.ListNotations.

(** Pointer effects distinguish allocation, inclusion, dereference and escape. *)
Inductive ptr_op (V T : Type) : Type :=
  | PAlloc (x : V) (site : T)
  | PCopy (x y : V)
  | PLoad (x p : V)
  | PStore (p y : V)
  | PEscape (x : V).

Arguments PAlloc {V T}.
Arguments PCopy {V T}.
Arguments PLoad {V T}.
Arguments PStore {V T}.
Arguments PEscape {V T}.

(** Value and heap unknowns inhabit disjoint namespaces. *)
Inductive pts_key (V T : Type) : Type :=
  | PVal (x : V)
  | PHeap (t : T).

Arguments PVal {V T}.
Arguments PHeap {V T}.

(** Only allocation sites appearing in the program belong to the finite universe. *)
Definition site_universe {V T} (ET : encoding T) (ops : list (ptr_op V T)) : list T :=
  FinSet.elements (FinSet.of_list ET
    (flat_map (fun op => match op with PAlloc _ t => [t] | _ => [] end) ops)).

(** Points-to facts carry well-formedness and finite support evidence. *)
Definition pts_set {V T} (ET : encoding T) (ops : list (ptr_op V T)) : Type :=
  finite_set ET (site_universe ET ops).

(** Points-to facts are ordered by inclusion and joined by union. *)
Definition pts_lattice {V T} (ET : encoding T) (ops : list (ptr_op V T)) :
    lattice (pts_set ET ops) := finite_powerset_lattice ET (site_universe ET ops).

(** Tagged codes encode value and heap unknowns injectively. *)
Definition pts_encoding {V T} (EV : encoding V) (ET : encoding T) :
    encoding (pts_key V T).
Proof.
  refine (Encoding _ (fun k => match k with
    | PVal x => xO (encode EV x)
    | PHeap t => xI (encode ET t)
    end) _).
  intros [x|t] [y|u] Heq; cbn in Heq; try discriminate;
    injection Heq as Heq; f_equal; eapply encode_injective; exact Heq.
Defined.

(** Bounded positions retain each occurrence, including duplicate instructions. *)
Fixpoint pts_positions (n : nat) : list {i : nat | i < n} :=
  match n as k return list {i : nat | i < k} with
  | 0 => []
  | S k => exist _ 0 (Nat.lt_0_succ k) ::
    map (fun i : {i : nat | i < k} => exist _ (S (proj1_sig i))
      (proj1 (Nat.succ_lt_mono (proj1_sig i) k) (proj2_sig i))) (pts_positions k)
  end.

(** The position projection is the ordered interval required by C54. *)
Lemma pts_positions_projection n : map (@proj1_sig _ _) (pts_positions n) = seq 0 n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [pts_positions map]; rewrite map_map.
  change (0 :: map (fun i : {i : nat | i < n} => S (proj1_sig i))
    (pts_positions n) = 0 :: seq 1 n).
  rewrite <- (map_map (@proj1_sig nat (fun i => i < n)) S (pts_positions n)).
  rewrite IH, seq_shift; reflexivity.
Qed.

(** Each bounded occurrence appears once, even when its instruction is duplicated. *)
Lemma pts_positions_nodup n : NoDup (pts_positions n).
Proof.
  apply (NoDup_map_inv (@proj1_sig nat (fun i => i < n))).
  rewrite pts_positions_projection; apply seq_NoDup.
Qed.

Fixpoint pts_nth {A} (xs : list A) : forall n, n < length xs -> A :=
  match xs as ys return forall n, n < length ys -> A with
  | [] => fun n Hbound => False_rect A (Nat.nlt_0_r n Hbound)
  | a :: ys => fun n => match n as k return k < S (length ys) -> A with
    | 0 => fun _ => a
    | S k => fun Hbound => pts_nth ys k
      (proj2 (Nat.succ_lt_mono k (length ys)) Hbound)
    end
  end.

(** A bounded lookup never needs a default instruction or an inhabited carrier. *)
Definition pts_at {A} (xs : list A) (i : {n : nat | n < length xs}) : A :=
  pts_nth xs (proj1_sig i) (proj2_sig i).

Lemma pts_nth_lookup {A} (xs : list A) n Hbound :
  nth_error xs n = Some (pts_nth xs n Hbound).
Proof.
  revert n Hbound; induction xs as [|a xs IH]; intros n Hbound; [cbn in Hbound; lia|].
  destruct n; cbn [pts_nth nth_error]; [reflexivity|apply IH].
Qed.

Lemma pts_at_lookup {A} (xs : list A) i :
  nth_error xs (proj1_sig i) = Some (pts_at xs i).
Proof.
  apply pts_nth_lookup.
Qed.

Lemma pts_at_in {A} (xs : list A) i : In (pts_at xs i) xs.
Proof.
  eapply nth_error_In; apply pts_at_lookup.
Qed.

Lemma pts_occurrence {A} (xs : list A) a : In a xs ->
  exists i, In i (pts_positions (length xs)) /\ pts_at xs i = a.
Proof.
  intro Hin; apply In_nth_error in Hin; destruct Hin as [n Hlookup].
  assert (Hbound : n < length xs).
  { apply nth_error_Some; rewrite Hlookup; discriminate. }
  assert (Hn : In n (map (@proj1_sig _ _) (pts_positions (length xs)))).
  { rewrite pts_positions_projection; apply in_seq; lia. }
  apply in_map_iff in Hn; destruct Hn as [i [Hi Hin]].
  exists i; split; [exact Hin|].
  rewrite <- Hi in Hlookup; rewrite pts_at_lookup in Hlookup; now injection Hlookup.
Qed.

Lemma site_universe_nodup {V T} (ET : encoding T) (ops : list (ptr_op V T)) :
  NoDup (site_universe ET ops).
Proof.
  apply (FinSet.elements_nodup ET), FinSet.wf_fold_add, Map.wf_empty.
Qed.

Lemma allocation_site_in {V T} (ET : encoding T) (ops : list (ptr_op V T)) x t :
  In (PAlloc x t) ops -> In t (site_universe ET ops).
Proof.
  intro Hin; apply (FinSet.elements_spec ET); [apply FinSet.wf_fold_add, Map.wf_empty|].
  apply FinSet.of_list_spec, in_flat_map; exists (PAlloc x t); split; [exact Hin|].
  cbn; auto.
Qed.

(** A singleton is clamped only to make the helper total outside listed allocations. *)
Definition pts_singleton {V T} (ET : encoding T) (ops : list (ptr_op V T)) t :
    pts_set ET ops :=
  finite_clamp ET (site_universe ET ops) (FinSet.add ET t FinSet.empty).

(** A load reads each selected heap unknown and unions the results. *)
Definition pts_load {V T} (ET : encoding T) (ops : list (ptr_op V T)) (ts : list T) :
    Query.t (pts_key V T) (pts_set ET ops) :=
  ask_all (map PHeap ts)
    (fun bs => Query.Ret (fold_right (join (pts_lattice ET ops))
      (bot (pts_lattice ET ops)) bs)).

(** A store emits one contribution for each pointed-to heap site. *)
Definition pts_store {V T} (ET : encoding T) (ops : list (ptr_op V T))
    (ts : list T) (b : pts_set ET ops) : Query.t (pts_key V T) (pts_set ET ops) :=
  side_all (map (fun t => (PHeap t, b)) ts) (Query.Ret (bot (pts_lattice ET ops))).

(** Each operation has exactly the independent inclusion query specified by ANA-9. *)
Definition pts_rhs {V T} (ET : encoding T) (ops : list (ptr_op V T)) (op : ptr_op V T) :
    Query.t (pts_key V T) (pts_set ET ops) :=
  match op with
  | PAlloc x t => Query.Ret (pts_singleton ET ops t)
  | PCopy x y => Query.Ask (PVal y) (fun a => Query.Ret a)
  | PLoad x p => Query.Ask (PVal p) (fun a => pts_load ET ops (FinSet.elements (proj1_sig a)))
  | PStore p y => Query.Ask (PVal p) (fun a => Query.Ask (PVal y)
    (fun b => pts_store ET ops (FinSet.elements (proj1_sig a)) b))
  | PEscape x => Query.Ret (bot (pts_lattice ET ops))
  end.

Definition pts_target {V T} (op : ptr_op V T) : pts_key V T :=
  match op with
  | PAlloc x _ | PCopy x _ | PLoad x _ | PEscape x => PVal x
  | PStore p _ => PVal p
  end.

(** One bounded occurrence supplies one target and one right-hand side. *)
Definition andersen_system {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) :
    System.t (pts_key V T) {i : nat | i < length ops} (pts_set ET ops) :=
  {| System.constraints := pts_positions (length ops);
     System.target := fun i => pts_target (pts_at ops i);
     System.rhs := fun i => pts_rhs ET ops (pts_at ops i) |}.

(** Pointer views expose concrete pointer observations independently of the analysis. *)
Record ptr_view (S V C L T : Type) : Type := PtrView {
  pmem : mem_view S V C L T;
  pval : S -> V -> option C;
  pop : S -> list (ptr_op V T);
  held : S -> C -> option C;
  pbyte : S -> C -> option nat
}.

Arguments PtrView {S V C L T}.
Arguments pmem {S V C L T}.
Arguments pval {S V C L T}.
Arguments pop {S V C L T}.
Arguments held {S V C L T}.
Arguments pbyte {S V C L T}.

(** A defined pointer value identifies its allocation's site. *)
Definition pts_of {S V C L T} (pv : ptr_view S V C L T) (s : S) (x : V) : option T :=
  match pval pv s x with
  | Some c => match loc_of (pmem pv) s c with
    | Some l => loc_site (pmem pv) s l
    | None => None
    end
  | None => None
  end.

(** Heap facts summarize pointers stored in any allocation of the source site. *)
Definition heap_pts {S V C L T} (pv : ptr_view S V C L T) (s : S) (t0 t : T) : Prop :=
  exists c c' l l', loc_of (pmem pv) s c = Some l /\ loc_site (pmem pv) s l = Some t0 /\
    held pv s c = Some c' /\ loc_of (pmem pv) s c' = Some l' /\
    loc_site (pmem pv) s l' = Some t.

(** Every new concrete fact has a listed allocation, copy, load or store origin. *)
Record ptr_view_laws {S O V C L T} (m : semantics S O) (pv : ptr_view S V C L T)
    (ops : list (ptr_op V T)) : Prop := {
  pop_listed : forall s op, reachable_state m s -> In op (pop pv s) -> In op ops;
  pts_initial : forall s x t, initial m s -> pts_of pv s x = Some t -> False;
  heap_initial : forall s t0 t, initial m s -> heap_pts pv s t0 t -> False;
  pts_origin : forall s l s' x t, reachable_state m s -> step m s l s' ->
    pts_of pv s' x = Some t ->
    pts_of pv s x = Some t \/ In (PAlloc x t) (pop pv s) \/
    (exists y, In (PCopy x y) (pop pv s) /\ pts_of pv s y = Some t) \/
    (exists p t0, In (PLoad x p) (pop pv s) /\ pts_of pv s p = Some t0 /\
      heap_pts pv s t0 t);
  heap_origin : forall s l s' t0 t, reachable_state m s -> step m s l s' ->
    heap_pts pv s' t0 t -> heap_pts pv s t0 t \/
    (exists p y, In (PStore p y) (pop pv s) /\ pts_of pv s p = Some t0 /\
      pts_of pv s y = Some t)
}.

Arguments pop_listed {S O V C L T m pv ops}.
Arguments pts_initial {S O V C L T m pv ops}.
Arguments heap_initial {S O V C L T m pv ops}.
Arguments pts_origin {S O V C L T m pv ops}.
Arguments heap_origin {S O V C L T m pv ops}.

(** * Membership and query observations *)

Lemma pts_le {V T} (ET : encoding T) (ops : list (ptr_op V T)) (a b : pts_set ET ops) :
  leb (pts_lattice ET ops) a b = true <->
  forall t, fmem ET t a = true -> fmem ET t b = true.
Proof.
  apply FinSet.subset_spec; exact (proj1 (proj2_sig a)).
Qed.

Lemma pts_members {V T} (ET : encoding T) (ops : list (ptr_op V T)) (a : pts_set ET ops) t :
  In t (FinSet.elements (proj1_sig a)) <-> fmem ET t a = true.
Proof.
  apply FinSet.elements_spec; exact (proj1 (proj2_sig a)).
Qed.

Lemma pts_join_mem {V T} (ET : encoding T) (ops : list (ptr_op V T)) a b t :
  fmem ET t (join (pts_lattice ET ops) a b) = true <->
  fmem ET t a = true \/ fmem ET t b = true.
Proof.
  apply FinSet.mem_union.
Qed.

Lemma pts_singleton_mem {V T} (ET : encoding T) (ops : list (ptr_op V T)) t u :
  fmem ET u (pts_singleton ET ops t) = true <-> In u (site_universe ET ops) /\ u = t.
Proof.
  unfold fmem, pts_singleton, finite_clamp; cbn [proj1_sig].
  rewrite FinSet.of_list_spec, filter_In, FinSet.mem_add, FinSet.mem_empty.
  intuition discriminate.
Qed.

Lemma pts_union_mem {V T} (ET : encoding T) (ops : list (ptr_op V T)) bs t :
  fmem ET t (fold_right (join (pts_lattice ET ops)) (bot (pts_lattice ET ops)) bs) = true <->
  exists b, In b bs /\ fmem ET t b = true.
Proof.
  induction bs as [|b bs IH]; cbn [fold_right].
  - change (FinSet.mem ET t FinSet.empty = true <->
      exists b : pts_set ET ops, In b [] /\ fmem ET t b = true).
    rewrite FinSet.mem_empty; split; [discriminate|intros [? [[] _]]].
  - rewrite pts_join_mem, IH; split.
    + intros [Hmem|[a [Hin Hmem]]]; [exists b|exists a]; cbn; auto.
    + intros [a [[Heq|Hin] Hmem]]; [subst a; now left|right; eauto].
Qed.

Lemma pts_load_observations {V T} (ET : encoding T) (ops : list (ptr_op V T)) ts sigma :
  Query.reads (pts_load ET ops ts) sigma = map PHeap ts /\
  Query.eval (pts_load ET ops ts) sigma =
    fold_right (join (pts_lattice ET ops)) (bot (pts_lattice ET ops))
      (map (fun t => sigma (PHeap t)) ts) /\
  Query.sides (pts_load ET ops ts) sigma = [].
Proof.
  unfold pts_load; destruct (ask_all_spec sigma (map PHeap ts)
    (fun bs => Query.Ret (fold_right (join (pts_lattice ET ops))
      (bot (pts_lattice ET ops)) bs))) as [Hr [Hv Hs]].
  cbn in Hr, Hv, Hs; rewrite app_nil_r in Hr; rewrite map_map in Hv; auto.
Qed.

Lemma pts_load_mem {V T} (ET : encoding T) (ops : list (ptr_op V T)) ts sigma t :
  fmem ET t (Query.eval (pts_load ET ops ts) sigma) = true <->
  exists u, In u ts /\ fmem ET t (sigma (PHeap u)) = true.
Proof.
  rewrite (proj1 (proj2 (pts_load_observations ET ops ts sigma))), pts_union_mem.
  split.
  - intros [b [Hin Hmem]]; apply in_map_iff in Hin; destruct Hin as [u [<- Hin]]; eauto.
  - intros [u [Hin Hmem]]; exists (sigma (PHeap u)); split;
      [exact (in_map (fun u => sigma (PHeap u)) ts u Hin)|exact Hmem].
Qed.

Lemma pts_store_observations {V T} (ET : encoding T) (ops : list (ptr_op V T)) ts b sigma :
  Query.eval (pts_store ET ops ts b) sigma = bot (pts_lattice ET ops) /\
  Query.reads (pts_store ET ops ts b) sigma = [] /\
  Query.sides (pts_store ET ops ts b) sigma = map (fun t => (PHeap t, b)) ts.
Proof.
  unfold pts_store; destruct (side_all_spec (Query.Ret (bot (pts_lattice ET ops)))
    sigma (map (fun t => (PHeap t, b)) ts)) as [Hv [Hr Hs]].
  cbn in Hv, Hr, Hs; rewrite app_nil_r in Hs; auto.
Qed.

(** Static dependencies cover every dynamic heap read and contribution. *)
Definition pts_deps {V T} (ET : encoding T) (ops : list (ptr_op V T)) (op : ptr_op V T) :
    list (pts_key V T) :=
  match op with
  | PCopy _ y => [PVal y]
  | PLoad _ p => PVal p :: map PHeap (site_universe ET ops)
  | PStore p y => [PVal p; PVal y]
  | _ => []
  end.

Definition pts_side_targets {V T} (ET : encoding T) (ops : list (ptr_op V T))
    (op : ptr_op V T) : list (pts_key V T) :=
  match op with
  | PStore _ _ => map PHeap (site_universe ET ops)
  | _ => []
  end.

Lemma pts_reads_within {V T} (ET : encoding T) (ops : list (ptr_op V T)) op sigma :
  incl (Query.reads (pts_rhs ET ops op) sigma) (pts_deps ET ops op).
Proof.
  destruct op as [x t|x y|x p|p y|x]; cbn [pts_rhs pts_deps Query.reads];
    try (intros z Hin; exact Hin).
  - rewrite (proj1 (pts_load_observations ET ops _ sigma)); intros z [<-|Hin]; [now left|].
    right; apply in_map_iff in Hin; destruct Hin as [u [<- Hin]]; apply in_map.
    apply (proj2 (proj2_sig (sigma (PVal p)))), pts_members; exact Hin.
  - rewrite (proj1 (proj2 (pts_store_observations ET ops _ _ sigma))).
    intros z Hin; exact Hin.
Qed.

Lemma pts_sides_within {V T} (ET : encoding T) (ops : list (ptr_op V T)) op sigma :
  incl (map fst (Query.sides (pts_rhs ET ops op) sigma)) (pts_side_targets ET ops op).
Proof.
  destruct op as [x t|x y|x p|p y|x]; cbn [pts_rhs pts_side_targets Query.sides map];
    try (intros z Hin; exact Hin).
  - rewrite (proj2 (proj2 (pts_load_observations ET ops _ sigma))); cbn; intros z Hin; exact Hin.
  - rewrite (proj2 (proj2 (pts_store_observations ET ops _ _ sigma))), map_map.
    intros z Hin; apply in_map_iff in Hin; destruct Hin as [u [<- Hin]].
    change (In (@PHeap V T u) (map PHeap (site_universe ET ops))); apply in_map.
    apply (proj2 (proj2_sig (sigma (PVal p)))), pts_members; exact Hin.
Qed.

(** The system's prepared static summary follows its bounded occurrence lookup. *)
Definition andersen_static {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) : System.static (andersen_system EV ET ops).
Proof.
  refine (@System.Static _ _ _ (andersen_system EV ET ops)
    (fun i => pts_deps ET ops (pts_at ops i))
    (fun i => pts_side_targets ET ops (pts_at ops i)) _ _).
  - intros i sigma; apply pts_reads_within.
  - intros i sigma; apply pts_sides_within.
Defined.

(** The independent closure rules are the four Andersen inclusions. *)
Record pts_closed {V T} (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) : Prop := {
  pts_alloc_closed : forall x t, In (PAlloc x t) ops -> fmem ET t (sigma (PVal x)) = true;
  pts_copy_closed : forall x y t, In (PCopy x y) ops ->
    fmem ET t (sigma (PVal y)) = true -> fmem ET t (sigma (PVal x)) = true;
  pts_load_closed : forall x p u t, In (PLoad x p) ops ->
    fmem ET u (sigma (PVal p)) = true -> fmem ET t (sigma (PHeap u)) = true ->
    fmem ET t (sigma (PVal x)) = true;
  pts_store_closed : forall p y u t, In (PStore p y) ops ->
    fmem ET u (sigma (PVal p)) = true -> fmem ET t (sigma (PVal y)) = true ->
    fmem ET t (sigma (PHeap u)) = true
}.

Arguments pts_alloc_closed {V T ET ops sigma}.
Arguments pts_copy_closed {V T ET ops sigma}.
Arguments pts_load_closed {V T ET ops sigma}.
Arguments pts_store_closed {V T ET ops sigma}.

Lemma pts_post_operation {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) sigma :
  post_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma ->
  forall op, In op ops ->
    leb (pts_lattice ET ops) (Query.eval (pts_rhs ET ops op) sigma)
      (sigma (pts_target op)) = true /\
    forall k a, In (k, a) (Query.sides (pts_rhs ET ops op) sigma) ->
      leb (pts_lattice ET ops) a (sigma k) = true.
Proof.
  intros Hpost op Hin; destruct (pts_occurrence ops op Hin) as [i [Hi Hat]].
  specialize (Hpost i Hi).
  change (leb (pts_lattice ET ops) (Query.eval (pts_rhs ET ops (pts_at ops i)) sigma)
    (sigma (pts_target (pts_at ops i))) = true /\
    forall k a, In (k, a) (Query.sides (pts_rhs ET ops (pts_at ops i)) sigma) ->
      leb (pts_lattice ET ops) a (sigma k) = true) in Hpost.
  now rewrite Hat in Hpost.
Qed.

(** Every query post-solution satisfies the independent inclusion rules. *)
Lemma pts_post_closed {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) sigma :
  post_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma ->
  pts_closed ET ops sigma.
Proof.
  intro Hpost; pose proof (pts_post_operation EV ET ops sigma Hpost) as Hop; constructor.
  - intros x t Hin; destruct (Hop _ Hin) as [Hle _].
    apply (proj1 (pts_le ET ops _ _) Hle).
    apply pts_singleton_mem; split; [eapply allocation_site_in; exact Hin|reflexivity].
  - intros x y t Hin Hmem; destruct (Hop _ Hin) as [Hle _].
    exact (proj1 (pts_le ET ops _ _) Hle t Hmem).
  - intros x p u t Hin Hu Ht; destruct (Hop _ Hin) as [Hle _].
    apply (proj1 (pts_le ET ops _ _) Hle).
    apply pts_load_mem; exists u; split; [apply pts_members; exact Hu|exact Ht].
  - intros p y u t Hin Hu Ht; destruct (Hop _ Hin) as [_ Hsides].
    cbn [pts_rhs Query.sides] in Hsides.
    rewrite (proj2 (proj2 (pts_store_observations ET ops _ _ sigma))) in Hsides.
    assert (Hcontribution : In (@PHeap V T u, sigma (PVal y))
      (map (fun t => (PHeap t, sigma (PVal y)))
        (FinSet.elements (proj1_sig (sigma (PVal p)))))).
    { apply in_map_iff; exists u; split; [reflexivity|apply pts_members; exact Hu]. }
    exact (proj1 (pts_le ET ops _ _) (Hsides _ _ Hcontribution) t Ht).
Qed.

(** Inclusion closure satisfies every return and side contribution of the specification. *)
Lemma pts_closed_post {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) sigma :
  pts_closed ET ops sigma ->
  post_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma.
Proof.
  intros Hclosed i Hi; pose proof (pts_at_in ops i) as Hin.
  change (leb (pts_lattice ET ops) (Query.eval (pts_rhs ET ops (pts_at ops i)) sigma)
    (sigma (pts_target (pts_at ops i))) = true /\
    forall k a, In (k, a) (Query.sides (pts_rhs ET ops (pts_at ops i)) sigma) ->
      leb (pts_lattice ET ops) a (sigma k) = true).
  destruct (pts_at ops i) as [x u|x y|x p|p y|x];
    cbn [pts_rhs pts_target Query.eval Query.sides] in *.
  - split.
    + apply pts_le; intros t Ht; apply pts_singleton_mem in Ht; destruct Ht as [_ ->].
      eapply pts_alloc_closed; eassumption.
    + intros k a Ha; contradiction.
  - split.
    + apply pts_le; intros t Ht; eapply pts_copy_closed; eassumption.
    + intros k a Ha; contradiction.
  - split.
    + apply pts_le; intros t Ht; apply pts_load_mem in Ht; destruct Ht as [u [Hu Ht]].
      eapply pts_load_closed; [exact Hclosed|exact Hin|apply pts_members; exact Hu|exact Ht].
    + rewrite (proj2 (proj2 (pts_load_observations ET ops _ sigma))).
      intros k a Ha; contradiction.
  - rewrite (proj1 (pts_store_observations ET ops _ _ sigma)),
      (proj2 (proj2 (pts_store_observations ET ops _ _ sigma))).
    split; [apply bot_least, finite_powerset_laws|].
    intros k a Ha; apply in_map_iff in Ha; destruct Ha as [u [Heq Hu]].
    injection Heq as <- <-; apply pts_le; intros t Ht.
    eapply pts_store_closed; [exact Hclosed|exact Hin|apply pts_members; exact Hu|exact Ht].
  - split; [apply bot_least, finite_powerset_laws|intros k a Ha; contradiction].
Qed.

(** * Soundness and solver properties *)

Lemma pts_semantic_step {S O V C L T} (m : semantics S O) (pv : ptr_view S V C L T)
    (ET : encoding T) ops sigma (Hlaws : ptr_view_laws m pv ops)
    (Hclosed : pts_closed ET ops sigma) s l s' :
  reachable_state m s -> step m s l s' ->
  (forall x t, pts_of pv s x = Some t -> fmem ET t (sigma (PVal x)) = true) ->
  (forall u t, heap_pts pv s u t -> fmem ET t (sigma (PHeap u)) = true) ->
  (forall x t, pts_of pv s' x = Some t -> fmem ET t (sigma (PVal x)) = true) /\
  (forall u t, heap_pts pv s' u t -> fmem ET t (sigma (PHeap u)) = true).
Proof.
  intros Hreach Hstep Hval Hheap; split.
  - intros x t Hpts; destruct (pts_origin Hlaws s l s' x t Hreach Hstep Hpts)
      as [Hold|[Halloc|[[y [Hcopy Hy]]|[p [u [Hload [Hp Ht]]]]]]].
    + apply Hval; exact Hold.
    + eapply pts_alloc_closed; [exact Hclosed|eapply pop_listed; eassumption].
    + eapply pts_copy_closed; [exact Hclosed|eapply pop_listed; eassumption|apply Hval; exact Hy].
    + eapply pts_load_closed; [exact Hclosed|eapply pop_listed; eassumption|
        apply Hval; exact Hp|apply Hheap; exact Ht].
  - intros u t Hpts; destruct (heap_origin Hlaws s l s' u t Hreach Hstep Hpts)
      as [Hold|[p [y [Hstore [Hp Hy]]]]].
    + apply Hheap; exact Hold.
    + eapply pts_store_closed; [exact Hclosed|eapply pop_listed; eassumption|
        apply Hval; exact Hp|apply Hval; exact Hy].
Qed.

(** Every concrete pointer in a reachable state belongs to any post-solution. *)
Theorem andersen_sound {S O V C L T} (m : semantics S O) (pv : ptr_view S V C L T)
    (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) :
  ptr_view_laws m pv ops ->
  post_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma ->
  forall s, reachable_state m s ->
    (forall x t, pts_of pv s x = Some t -> fmem ET t (sigma (PVal x)) = true) /\
    (forall t0 t, heap_pts pv s t0 t -> fmem ET t (sigma (PHeap t0)) = true).
Proof.
  intros Hlaws Hpost s [s0 [tr [Hinitial Hrun]]].
  assert (Hclosed := pts_post_closed EV ET ops sigma Hpost).
  assert (Hstart : reachable_state m s0) by (exists s0, []; split; [exact Hinitial|constructor]).
  assert (Hfacts :
    (forall x t, pts_of pv s0 x = Some t -> fmem ET t (sigma (PVal x)) = true) /\
    (forall u t, heap_pts pv s0 u t -> fmem ET t (sigma (PHeap u)) = true)).
  { split; intros; exfalso; [eapply pts_initial|eapply heap_initial]; eassumption. }
  clear Hinitial; revert Hstart Hfacts.
  induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intros Hreach [Hval Hheap].
  - auto.
  - apply IH; [eapply reachable_state_step; eassumption|].
    eapply pts_semantic_step; eassumption.
Qed.

(** Each query preserves inclusion, including the dynamically selected heap contributions. *)
Theorem andersen_monotone {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) :
  monotone_system (pts_lattice ET ops) (andersen_system EV ET ops).
Proof.
  intros i Hi; change (monotone_query (pts_lattice ET ops) (pts_rhs ET ops (pts_at ops i))).
  destruct (pts_at ops i) as [x u|x y|x p|p y|x];
    split; cbn [pts_rhs Query.eval Query.sides].
  - intros s1 s2 Hle; apply leb_refl, finite_powerset_laws.
  - intros s1 s2 Hle k a Ha; contradiction.
  - intros s1 s2 Hle; apply Hle.
  - intros s1 s2 Hle k a Ha; contradiction.
  - intros s1 s2 Hle; apply pts_le; intros t Ht; apply pts_load_mem in Ht.
    destruct Ht as [u [Hu Ht]]; apply pts_load_mem; exists u; split.
    + apply pts_members, (proj1 (pts_le ET ops _ _) (Hle (PVal p))), pts_members; exact Hu.
    + apply (proj1 (pts_le ET ops _ _) (Hle (PHeap u))); exact Ht.
  - intros s1 s2 Hle k a Ha.
    rewrite (proj2 (proj2 (pts_load_observations ET ops _ s1))) in Ha; contradiction.
  - intros s1 s2 Hle; rewrite !(proj1 (pts_store_observations ET ops _ _ _)).
    apply leb_refl, finite_powerset_laws.
  - intros s1 s2 Hle k a Ha.
    rewrite (proj2 (proj2 (pts_store_observations ET ops _ _ s1))) in Ha.
    apply in_map_iff in Ha; destruct Ha as [u [Heq Hu]]; injection Heq as <- <-.
    exists (s2 (PVal y)); split; [|apply Hle].
    rewrite (proj2 (proj2 (pts_store_observations ET ops _ _ s2))).
    apply in_map_iff; exists u; split; [reflexivity|].
    apply pts_members, (proj1 (pts_le ET ops _ _) (Hle (PVal p))), pts_members; exact Hu.
  - intros s1 s2 Hle; apply leb_refl, finite_powerset_laws.
  - intros s1 s2 Hle k a Ha; contradiction.
Qed.

(** The deduplicated site universe supplies finite-height termination under every scheduler. *)
Theorem andersen_terminates {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) (sch : scheduler (pts_key V T)) :
  terminates (pts_lattice ET ops) (andersen_static EV ET ops) sch Joining.
Proof.
  exact (inhabits (base_height
    (finite_powerset_height ET (site_universe ET ops) (site_universe_nodup ET ops)))).
Qed.
