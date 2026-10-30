(** * Finite matched interprocedural tabulation

    Balanced summaries and reachable prefixes describe paths with an unbounded call stack.
    For example, a return labelled [p] closes the most recent call labelled [p].
    Builds on: CollectionsEncoding, CollectionsMap, OrderBasic and FixpointTotal. *)

From Stdlib Require Import List Bool PArith Arith Lia Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointLeast
  FixpointWorklist FixpointTotal.
Import List.ListNotations.

(** * Problems and stack semantics *)

(** An edge either preserves, pushes, or pops the call stack. *)
Inductive ip_kind (P : Type) : Type :=
  | IpInternal
  | IpCall (site : P)
  | IpReturn (site : P).

Arguments IpInternal {P}.
Arguments IpCall {P}.
Arguments IpReturn {P}.

(** Every listed pair is an exploded edge, with [None] denoting zero. *)
Record ip_edge (N P D : Type) : Type := IpEdge {
  ip_source : N;
  ip_target : N;
  ip_action : ip_kind P;
  ip_pairs : list (option D * option D)
}.

Arguments IpEdge {N P D}.
Arguments ip_source {N P D}.
Arguments ip_target {N P D}.
Arguments ip_action {N P D}.
Arguments ip_pairs {N P D}.

(** The finite universes contain all nodes, sites, facts, and edge occurrences. *)
Record ip_problem (N P D : Type) : Type := IpProblem {
  ip_nodes : list N;
  ip_sites : list P;
  ip_facts : list D;
  ip_edges : list (ip_edge N P D)
}.

Arguments IpProblem {N P D}.
Arguments ip_nodes {N P D}.
Arguments ip_sites {N P D}.
Arguments ip_facts {N P D}.
Arguments ip_edges {N P D}.

(** Well-formedness closes all edge endpoints and pairs over the finite universes. *)
Definition ip_problem_wf {N P D} (q : ip_problem N P D) : Prop :=
  NoDup (ip_nodes q) /\ NoDup (ip_sites q) /\ NoDup (ip_facts q) /\
  (forall e, In e (ip_edges q) -> In (ip_source e) (ip_nodes q) /\
    In (ip_target e) (ip_nodes q) /\ In (None, None) (ip_pairs e) /\
    (match ip_action e with IpInternal => True | IpCall p | IpReturn p =>
       In p (ip_sites q) end) /\
    forall x y, In (x, y) (ip_pairs e) ->
      (match x with None => True | Some d => In d (ip_facts q) end) /\
      (match y with None => True | Some d => In d (ip_facts q) end)).

(** A return can pop exactly the matching topmost call site. *)
Inductive ip_step {N P D} (q : ip_problem N P D) :
    N * option D * list P -> ip_edge N P D -> N * option D * list P -> Prop :=
  | ip_step_internal : forall e x y stack,
      In e (ip_edges q) -> ip_action e = IpInternal -> In (x, y) (ip_pairs e) ->
      ip_step q (ip_source e, x, stack) e (ip_target e, y, stack)
  | ip_step_call : forall e p x y stack,
      In e (ip_edges q) -> ip_action e = IpCall p -> In (x, y) (ip_pairs e) ->
      ip_step q (ip_source e, x, stack) e (ip_target e, y, p :: stack)
  | ip_step_return : forall e p x y stack,
      In e (ip_edges q) -> ip_action e = IpReturn p -> In (x, y) (ip_pairs e) ->
      ip_step q (ip_source e, x, p :: stack) e (ip_target e, y, stack).

(** Finite paths retain the complete matched stack behavior. *)
Inductive ip_path {N P D} (q : ip_problem N P D) :
    N * option D * list P -> N * option D * list P -> Prop :=
  | ip_path_refl : forall c, ip_path q c c
  | ip_path_step : forall c e c' c'', ip_step q c e c' -> ip_path q c' c'' ->
      ip_path q c c''.

Lemma ip_path_trans {N P D} (q : ip_problem N P D) c c' c'' :
  ip_path q c c' -> ip_path q c' c'' -> ip_path q c c''.
Proof.
  intros Hpath Htail; induction Hpath as [c | c e d z Hstep Hpath IH].
  - exact Htail.
  - eapply ip_path_step; [exact Hstep | apply IH; exact Htail].
Qed.

(** * Finite indexed Horn tabulation *)

Module IpHorn.

(** Rules have bounded arity, so executing a constraint never searches a rule list. *)
Inductive rule (K : Type) : Type :=
  | Seed (target : K)
  | Unary (read target : K)
  | Binary (left right target : K).

Arguments Seed {K}.
Arguments Unary {K}.
Arguments Binary {K}.

Definition code {K} (EK : encoding K) (r : rule K) : K + (K * K + K * K * K) :=
  match r with
  | Seed x => inl x
  | Unary x y => inr (inl (x, y))
  | Binary x y z => inr (inr (x, y, z))
  end.

Definition rule_encoding {K} (EK : encoding K) : encoding (rule K).
Proof.
  refine (Encoding _ (fun r => encode
    (sum_encoding EK (sum_encoding (pair_encoding EK EK)
      (pair_encoding (pair_encoding EK EK) EK))) (code EK r)) _).
  intros r s Heq; apply encode_injective in Heq.
  destruct r, s; cbn [code] in Heq; congruence.
Defined.

Definition target {K} (r : rule K) : K :=
  match r with
  | Seed x => x
  | Unary _ x => x
  | Binary _ _ x => x
  end.

Definition query {K} (r : rule K) : Query.t K bool :=
  match r with
  | Seed _ => Query.Ret true
  | Unary x _ => Query.Ask x (fun b => Query.Ret b)
  | Binary x y _ => Query.Ask x (fun b => Query.Ask y (fun c => Query.Ret (b && c)))
  end.

Definition reads {K} (r : rule K) : list K :=
  match r with
  | Seed _ => []
  | Unary x _ => [x]
  | Binary x y _ => [x; y]
  end.

Definition system {K} (rs : list (rule K)) : System.t K (rule K) bool :=
  System.Make rs target query.

Definition static {K} (rs : list (rule K)) : System.static (system rs).
Proof.
  refine (System.Static reads (fun _ => []) _ _).
  - intros [x | x y | x y z] s a Ha; cbn in *; exact Ha.
  - intros [x | x y | x y z] s a Ha; exact Ha.
Defined.

Definition schedule {K} : scheduler K := Scheduler (fun _ => 1%positive) (fun _ => false).

Definition termination {K} (rs : list (rule K)) :
    terminates bool_lattice (static rs) schedule Joining :=
  inhabits (base_height bool_height).

(** Derivability is independent of the executable indexed worklist. *)
Inductive derives {K} (rs : list (rule K)) : K -> Prop :=
  | derives_seed : forall x, In (Seed x) rs -> derives rs x
  | derives_unary : forall x y, In (Unary x y) rs -> derives rs x -> derives rs y
  | derives_binary : forall x y z, In (Binary x y z) rs ->
      derives rs x -> derives rs y -> derives rs z.

Definition solve {K} (EK : encoding K) (rs : list (rule K)) : K -> bool :=
  proj1_sig (solve_total EK (rule_encoding EK) bool_lattice bool_laws schedule Joining
    (system rs) (static rs) (termination rs)).

Lemma query_sides {K} (r : rule K) s : Query.sides (query r) s = [].
Proof.
  destruct r; reflexivity.
Qed.

Lemma query_derives {K} (rs : list (rule K)) s r :
  In r rs -> (forall x, s x = true -> derives rs x) ->
  Query.eval (query r) s = true -> derives rs (target r).
Proof.
  intros Hr Hs; destruct r as [x | x y | x y z]; cbn.
  - intros _; apply derives_seed; exact Hr.
  - intro Hx; eapply derives_unary; [exact Hr | apply Hs; exact Hx].
  - rewrite andb_true_iff; intros [Hx Hy]; eapply derives_binary;
      [exact Hr | apply Hs; exact Hx | apply Hs; exact Hy].
Qed.

Lemma raise_derives {K} (EK : encoding K) (rs : list (rule K)) s t :
  (forall x, s x = true -> derives rs x) ->
  raise EK bool_lattice (system rs) s t -> forall x, t x = true -> derives rs x.
Proof.
  intros Hs [r [Hr Ht]] x Hx; rewrite Ht in Hx.
  unfold run_updates in Hx; rewrite run_spec in Hx; cbn [system System.rhs System.target] in Hx.
  rewrite query_sides in Hx; cbn [apply_updates fold_left] in Hx.
  unfold join_update in Hx; cbn [fst snd] in Hx.
  destruct (Pos.eqb (encode EK (target r)) (encode EK x)) eqn:Heq.
  - apply Pos.eqb_eq, (encode_injective EK) in Heq; subst x.
    change ((if implb (Query.eval (query r) s) (s (target r))
      then s (target r) else s (target r) || Query.eval (query r) s) = true) in Hx.
    destruct (s (target r)) eqn:Hold; [apply Hs; exact Hold |].
    destruct (Query.eval (query r) s) eqn:Hnew; cbn in Hx; [|discriminate].
    exact (query_derives rs s r Hr Hs Hnew).
  - apply Hs; exact Hx.
Qed.

Lemma reached_derives {K} (EK : encoding K) (rs : list (rule K)) s :
  reached EK bool_lattice (system rs) s -> forall x, s x = true -> derives rs x.
Proof.
  intros [initial [Hbot Hrun]].
  assert (Hpreserve : forall a b,
    clos_refl_trans (K -> bool) (raise EK bool_lattice (system rs)) a b ->
    (forall x, a x = true -> derives rs x) -> forall x, b x = true -> derives rs x).
  { intros a b Hsteps; induction Hsteps as [a b Hstep | a | a b c Hab IHab Hbc IHbc].
    - intro Ha; apply (raise_derives EK rs a b Ha Hstep).
    - exact (fun Ha => Ha).
    - intro Ha; apply IHbc, IHab; exact Ha. }
  apply (Hpreserve initial s Hrun); intros x Hx; rewrite Hbot in Hx; discriminate.
Qed.

Lemma solve_sound {K} (EK : encoding K) (rs : list (rule K)) x :
  solve EK rs x = true -> derives rs x.
Proof.
  apply (reached_derives EK rs); apply solve_total_reached.
Qed.

Lemma solve_complete {K} (EK : encoding K) (rs : list (rule K)) x :
  derives rs x -> solve EK rs x = true.
Proof.
  pose proof (proj2_sig (solve_total EK (rule_encoding EK) bool_lattice bool_laws
    schedule Joining (system rs) (static rs) (termination rs))) as Hpost.
  change (post_solution bool_lattice (system rs) (solve EK rs)) in Hpost.
  intro Hderive; induction Hderive as [x Hr | x y Hr Hx IHx | x y z Hr Hx IHx Hy IHy].
  - exact (proj1 (Hpost _ Hr)).
  - pose proof (proj1 (Hpost _ Hr)) as Hy.
    change (implb (solve EK rs x) (solve EK rs y) = true) in Hy.
    rewrite IHx in Hy; exact Hy.
  - pose proof (proj1 (Hpost _ Hr)) as Hz.
    change (implb (solve EK rs x && solve EK rs y) (solve EK rs z) = true) in Hz.
    rewrite IHx, IHy in Hz; exact Hz.
Qed.

(** The finite tabulation returns exactly the inductive rule closure. *)
Theorem solve_exact {K} (EK : encoding K) (rs : list (rule K)) x :
  solve EK rs x = true <-> derives rs x.
Proof.
  split; [apply solve_sound | apply solve_complete].
Qed.

(** The indexed queue has a finite completed execution, with no exhaustion fallback. *)
Theorem solve_terminates {K} (EK : encoding K) (rs : list (rule K)) :
  exists f, forall fuel, (f <= fuel)%positive -> exists m,
    run_worklist EK (rule_encoding EK) bool_lattice schedule Joining (system rs)
      (Declared (static rs) (index_system EK (system rs) (static rs))) fuel = Some m /\
    solve EK rs = lookup EK bool_lattice m.
Proof.
  apply solve_total_run.
Qed.

Definition probe {K} (EK : encoding K) (rs : list (rule K)) (fuel : positive) :
    option (Map.t K bool) :=
  run_worklist EK (rule_encoding EK) bool_lattice schedule Joining (system rs)
    (Declared (static rs) (index_system EK (system rs) (static rs))) fuel.

(** A completed finite observation computes the very same indexed total engine. *)
Theorem solve_probe {K} (EK : encoding K) (rs : list (rule K)) fuel m :
  probe EK rs fuel = Some m -> solve EK rs = lookup EK bool_lattice m.
Proof.
  intro Hprobe; destruct (solve_terminates EK rs) as [bound Hbound].
  destruct (Hbound bound (Pos.le_refl bound)) as [result [Hrun Heq]].
  pose proof (total_completed_runs_unique EK (rule_encoding EK) bool_lattice schedule Joining
    (system rs) _ bound fuel result m Hrun Hprobe) as Hsame.
  now rewrite Hsame in Heq.
Qed.

Lemma query_reads {K} (r : rule K) s : Query.reads (query r) s = reads r.
Proof.
  destruct r; reflexivity.
Qed.

(** Every unqueued rule is satisfied and its reads retain their prepared reader entries. *)
Theorem pending_coverage {K} (EK : encoding K) (rs : list (rule K)) e :
  engine_reachable EK (rule_encoding EK) bool_lattice schedule Joining (system rs)
    (Declared (static rs) (index_system EK (system rs) (static rs))) e ->
  forall r, In r rs -> PQueue.priority (rule_encoding EK) r (Engine.queue e) = None ->
    (Query.eval (query r) (lookup EK bool_lattice (Engine.current e)) = true ->
      lookup EK bool_lattice (Engine.current e) (target r) = true) /\
    forall x, In x (reads r) ->
      In r (readers_of EK (index_system EK (system rs) (static rs)) x).
Proof.
  intro Hreachable.
  pose proof (engine_reachable_invariant EK (rule_encoding EK) bool_lattice schedule Joining
    (system rs) (Declared (static rs) (index_system EK (system rs) (static rs))) bool_laws
    (index_system_laws EK (system rs) (static rs)) e Hreachable) as [_ [_ Hcovered]].
  intros r Hr Hnone; destruct (Hcovered r Hr Hnone) as [[Hvalue _] Hreaders]; split.
  - intro Htrue; change (implb
      (Query.eval (query r) (lookup EK bool_lattice (Engine.current e)))
      (lookup EK bool_lattice (Engine.current e) (target r)) = true) in Hvalue.
    rewrite Htrue in Hvalue; exact Hvalue.
  - intros x Hx; apply Hreaders; cbn [system System.rhs]; rewrite query_reads; exact Hx.
Qed.

End IpHorn.
Import IpHorn.

(** * Exploded-edge indexes and balanced paths *)

Module IpTab.

Definition vertex (N D : Type) : Type := (N * option D)%type.

Definition fact (N D : Type) : Type := (vertex N D * vertex N D + vertex N D)%type.

Definition vertex_encoding {N D} (EN : encoding N) (ED : encoding D) :
    encoding (vertex N D) := pair_encoding EN (option_encoding ED).

Definition fact_encoding {N D} (EN : encoding N) (ED : encoding D) :
    encoding (fact N D) :=
  let EV := vertex_encoding EN ED in sum_encoding (pair_encoding EV EV) EV.

Definition kind_code {P} (k : ip_kind P) : unit + (P + P) :=
  match k with
  | IpInternal => inl tt
  | IpCall p => inr (inl p)
  | IpReturn p => inr (inr p)
  end.

Definition kind_encoding {P} (EP : encoding P) : encoding (ip_kind P).
Proof.
  refine (Encoding _ (fun k => encode
    (sum_encoding unit_encoding (sum_encoding EP EP)) (kind_code k)) _).
  intros k l Heq; apply encode_injective in Heq.
  destruct k, l; cbn [kind_code] in Heq; congruence.
Defined.

Definition bucket {K V} (EK : encoding K) (idx : Map.t K (list V)) (k : K) : list V :=
  match Map.get EK k idx with
  | Some vs => vs
  | None => []
  end.

Definition index {K V} (EK : encoding K) (rows : list (K * V)) : Map.t K (list V) :=
  fold_right (fun kv idx => Map.set EK (fst kv) (snd kv :: bucket EK idx (fst kv)) idx)
    Map.empty rows.

Lemma index_exact {K V} (EK : encoding K) (rows : list (K * V)) k v :
  In v (bucket EK (index EK rows) k) <-> In (k, v) rows.
Proof.
  induction rows as [|[j w] rows IH]; cbn [index fold_right fst snd].
  - unfold bucket; rewrite Map.get_empty; reflexivity.
  - destruct (Pos.eqb (encode EK k) (encode EK j)) eqn:Heq.
    + apply Pos.eqb_eq, (encode_injective EK) in Heq; subst j.
      unfold bucket at 1; rewrite Map.get_set_same; cbn [In].
      rewrite IH; intuition congruence.
    + assert (Hne : k <> j) by (intro H; subst j; rewrite Pos.eqb_refl in Heq; discriminate).
      unfold bucket at 1; rewrite Map.get_set_other by exact Hne.
      fold (bucket EK (index EK rows) k); rewrite IH; cbn [In]; intuition congruence.
Qed.

Section Problem.
Context {N P D : Type} (q : ip_problem N P D).

Definition valid_fact (d : option D) : Prop :=
  match d with
  | None => True
  | Some x => In x (ip_facts q)
  end.

Definition vertices : list (vertex N D) :=
  flat_map (fun n => map (fun d => (n, d)) (None :: map (@Some D) (ip_facts q)))
    (ip_nodes q).

Lemma vertices_exact n d : In (n, d) vertices <-> In n (ip_nodes q) /\ valid_fact d.
Proof.
  unfold vertices; rewrite in_flat_map; split.
  - intros [m [Hm Hpair]]; apply in_map_iff in Hpair.
    destruct Hpair as [x [Heq Hx]]; injection Heq as Hm' Hx'; subst m x.
    split; [exact Hm | destruct d as [d |]; [|exact I]].
    cbn [In] in Hx; destruct Hx as [Hbad | Hx]; [discriminate |].
    apply in_map_iff in Hx; destruct Hx as [y [Heq Hy]]; injection Heq as Heq.
    subst y; exact Hy.
  - intros [Hn Hd]; exists n; split; [exact Hn | apply in_map].
    destruct d as [d |]; [right; apply in_map; exact Hd | now left].
Qed.

(** Every pair occurrence is retained before action and matching-site indexing. *)
Definition arcs : list (ip_kind P * (vertex N D * vertex N D)) :=
  flat_map (fun e => map (fun xy => (ip_action e,
    ((ip_source e, fst xy), (ip_target e, snd xy)))) (ip_pairs e)) (ip_edges q).

Definition arc (k : ip_kind P) (u v : vertex N D) : Prop := In (k, (u, v)) arcs.

Lemma arc_exact k u v : arc k u v <-> exists e,
  In e (ip_edges q) /\ ip_action e = k /\ ip_source e = fst u /\
  ip_target e = fst v /\ In (snd u, snd v) (ip_pairs e).
Proof.
  destruct u as [n x], v as [m y]; unfold arc, arcs; rewrite in_flat_map; cbn [fst snd].
  split.
  - intros [e [He Hpair]]; apply in_map_iff in Hpair.
    destruct Hpair as [[a b] [Heq Hpair]]; cbn [fst snd] in Heq.
    injection Heq as Hkind Hn Hx Hm Hy; subst a b.
    exists e; repeat split; assumption.
  - intros [e [He [Hkind [Hn [Hm Hpair]]]]]; exists e; split; [exact He |].
    apply in_map_iff; exists (x, y); split; [cbn; now rewrite Hkind, Hn, Hm | exact Hpair].
Qed.

Lemma arc_vertices k u v : ip_problem_wf q -> arc k u v -> In u vertices /\ In v vertices.
Proof.
  intros [_ [_ [_ Hwf]]] Harc; apply arc_exact in Harc.
  destruct Harc as [e [He [_ [Hsource [Htarget Hpairs]]]]].
  destruct (Hwf e He) as [Hn [Hm [_ [_ Hfacts]]]].
  destruct (Hfacts _ _ Hpairs) as [Hx Hy].
  destruct u as [n x], v as [m y]; cbn in *.
  split; apply vertices_exact; split.
  - now rewrite <- Hsource.
  - exact Hx.
  - now rewrite <- Htarget.
  - exact Hy.
Qed.

Definition config (v : vertex N D) (stack : list P) : N * option D * list P :=
  (fst v, snd v, stack).

Lemma arc_internal u v stack : arc IpInternal u v ->
  exists e, ip_step q (config u stack) e (config v stack).
Proof.
  intros Harc; apply arc_exact in Harc; destruct Harc as [e [He [Hkind [Hu [Hv Hpair]]]]].
  destruct u as [n x], v as [m y]; cbn in *; subst n m; exists e.
  apply ip_step_internal; assumption.
Qed.

Lemma arc_call p u v stack : arc (IpCall p) u v ->
  exists e, ip_step q (config u stack) e (config v (p :: stack)).
Proof.
  intros Harc; apply arc_exact in Harc; destruct Harc as [e [He [Hkind [Hu [Hv Hpair]]]]].
  destruct u as [n x], v as [m y]; cbn in *; subst n m; exists e.
  apply ip_step_call; assumption.
Qed.

Lemma arc_return p u v stack : arc (IpReturn p) u v ->
  exists e, ip_step q (config u (p :: stack)) e (config v stack).
Proof.
  intros Harc; apply arc_exact in Harc; destruct Harc as [e [He [Hkind [Hu [Hv Hpair]]]]].
  destruct u as [n x], v as [m y]; cbn in *; subst n m; exists e.
  apply ip_step_return; assumption.
Qed.

(** A summary stays above its incoming stack and returns to the same stack. *)
Inductive balanced : vertex N D -> vertex N D -> Prop :=
  | balanced_refl : forall u, In u vertices -> balanced u u
  | balanced_internal : forall a u v, balanced a u -> arc IpInternal u v -> balanced a v
  | balanced_call : forall a u entry exit v p,
      balanced a u -> arc (IpCall p) u entry -> balanced entry exit ->
      arc (IpReturn p) exit v -> balanced a v.

Lemma balanced_trans a b c : balanced a b -> balanced b c -> balanced a c.
Proof.
  intros Hab Hbc; revert a Hab.
  induction Hbc as [b Hb | b u v Hbu IH Harc |
    b u entry exit v p Hbu IHouter Hcall Hinner IHinner Hreturn]; intros a Hab.
  - exact Hab.
  - eapply balanced_internal; [apply IH; exact Hab | exact Harc].
  - eapply balanced_call; [apply IHouter; exact Hab | exact Hcall | exact Hinner | exact Hreturn].
Qed.

Lemma balanced_vertices a b : ip_problem_wf q -> balanced a b ->
  In a vertices /\ In b vertices.
Proof.
  intros Hwf Hbalanced; induction Hbalanced as [u Hu | a u v Hbal IH Harc |
    a u entry exit v p Hbal IH Hcall Hinner IHinner Hreturn].
  - split; exact Hu.
  - split; [exact (proj1 IH) | exact (proj2 (arc_vertices _ _ _ Hwf Harc))].
  - split; [exact (proj1 IH) | exact (proj2 (arc_vertices _ _ _ Hwf Hreturn))].
Qed.

Lemma balanced_sound a b : balanced a b -> forall stack,
  ip_path q (config a stack) (config b stack).
Proof.
  intro Hbalanced; induction Hbalanced as [u Hu | a u v Hbal IH Harc |
    a u entry exit v p Hbal IH Hcall Hinner IHinner Hreturn]; intro stack.
  - apply ip_path_refl.
  - eapply ip_path_trans; [apply IH |].
    destruct (arc_internal u v stack Harc) as [e Hstep].
    eapply ip_path_step; [exact Hstep | apply ip_path_refl].
  - eapply ip_path_trans; [apply IH |].
    destruct (arc_call p u entry stack Hcall) as [e Hstep].
    eapply ip_path_step; [exact Hstep |].
    eapply ip_path_trans; [apply IHinner |].
    destruct (arc_return p exit v stack Hreturn) as [r Hstepreturn].
    eapply ip_path_step; [exact Hstepreturn | apply ip_path_refl].
Qed.

(** Prefix derivations keep unfinished calls, while completed calls use balanced summaries. *)
Inductive prefix (root : vertex N D) : vertex N D -> Prop :=
  | prefix_root : prefix root root
  | prefix_balanced : forall u v, prefix root u -> balanced u v -> prefix root v
  | prefix_call : forall p u v, prefix root u -> arc (IpCall p) u v -> prefix root v.

Lemma prefix_sound root v : prefix root v ->
  exists stack, ip_path q (config root []) (config v stack).
Proof.
  intro Hprefix; induction Hprefix as [|u v Hprefix [stack Hpath] Hbalanced |
    p u v Hprefix [stack Hpath] Hcall].
  - exists []; apply ip_path_refl.
  - exists stack; eapply ip_path_trans; [exact Hpath | apply balanced_sound; exact Hbalanced].
  - exists (p :: stack); eapply ip_path_trans; [exact Hpath |].
    destruct (arc_call p u v stack Hcall) as [e Hstep].
    eapply ip_path_step; [exact Hstep | apply ip_path_refl].
Qed.

(** Coverage retains the balanced segment for every pending frame of this same path. *)
Inductive covered (root : vertex N D) : vertex N D -> list P -> Prop :=
  | covered_root : forall v, balanced root v -> covered root v []
  | covered_call : forall p u entry v stack, covered root u stack ->
      arc (IpCall p) u entry -> balanced entry v -> covered root v (p :: stack).

Lemma covered_balanced root u stack v : covered root u stack -> balanced u v ->
  covered root v stack.
Proof.
  intros Hcovered Hbalanced; destruct Hcovered as [u Hroot |
    p u entry current stack Hcovered Hcall Htail].
  - apply covered_root; eapply balanced_trans; eassumption.
  - eapply covered_call; [exact Hcovered | exact Hcall |].
    eapply balanced_trans; eassumption.
Qed.

Lemma covered_prefix root v stack : covered root v stack -> prefix root v.
Proof.
  intro Hcovered; induction Hcovered as [v Hbalanced |
    p u entry v stack Hcovered IH Hcall Hbalanced].
  - eapply prefix_balanced; [apply prefix_root | exact Hbalanced].
  - eapply prefix_balanced; [eapply prefix_call; eassumption | exact Hbalanced].
Qed.

Lemma covered_step root n x stack e n' y stack' : ip_problem_wf q ->
  covered root (n, x) stack -> ip_step q (n, x, stack) e (n', y, stack') ->
  covered root (n', y) stack'.
Proof.
  intros Hwf Hcovered Hstep.
  rename x into source_fact; rename y into target_fact; rename e into selected.
  rename stack into source_stack; rename stack' into target_stack.
  inversion Hstep as [e x y stack He Hkind Hpair |
    e p x y stack He Hkind Hpair | e p x y stack He Hkind Hpair]; subst.
  - assert (Harc : arc IpInternal (ip_source selected, source_fact)
      (ip_target selected, target_fact)).
    { apply arc_exact; exists selected; repeat split; assumption. }
    apply (covered_balanced _ _ _ _ Hcovered).
    eapply balanced_internal; [apply balanced_refl; exact (proj1 (arc_vertices _ _ _ Hwf Harc)) |
      exact Harc].
  - assert (Harc : arc (IpCall p) (ip_source selected, source_fact)
      (ip_target selected, target_fact)).
    { apply arc_exact; exists selected; repeat split; assumption. }
    eapply covered_call; [exact Hcovered | exact Harc |].
    apply balanced_refl; exact (proj2 (arc_vertices _ _ _ Hwf Harc)).
  - assert (Harc : arc (IpReturn p) (ip_source selected, source_fact)
      (ip_target selected, target_fact)).
    { apply arc_exact; exists selected; repeat split; assumption. }
    inversion Hcovered as [|p' u entry v stack' Houter Hcall Hinner Heq Hstack]; subst.
    apply (covered_balanced _ _ _ _ Houter).
    eapply balanced_call; [apply balanced_refl | exact Hcall | exact Hinner | exact Harc].
    exact (proj1 (arc_vertices _ _ _ Hwf Hcall)).
Qed.

Lemma path_covered root c c' : ip_problem_wf q -> ip_path q c c' ->
  (forall n d stack, c = (n, d, stack) -> covered root (n, d) stack) ->
  forall n d stack, c' = (n, d, stack) -> covered root (n, d) stack.
Proof.
  intros Hwf Hpath; induction Hpath as [c | c e c' c'' Hstep Hpath IH]; intro Hcovered.
  - exact Hcovered.
  - apply IH; intros n d stack Heq; subst c'.
    destruct c as [[m x] incoming].
    eapply covered_step; [exact Hwf | apply Hcovered; reflexivity | exact Hstep].
Qed.

(** Every stack path is represented by balanced segments and unfinished calls. *)
Theorem prefix_complete root v stack : ip_problem_wf q -> In root vertices ->
  ip_path q (config root []) (config v stack) -> prefix root v.
Proof.
  intros Hwf Hroot Hpath; apply (covered_prefix root v stack).
  destruct root as [n x], v as [m y].
  apply (path_covered (n, x) _ _ Hwf Hpath).
  - intros j d incoming Heq; injection Heq as Hj Hd Hstack; subst j d incoming.
    apply covered_root, balanced_refl; exact Hroot.
  - reflexivity.
Qed.

(** All empty-stack paths have a tabulatable balanced derivation. *)
Theorem balanced_complete u v : ip_problem_wf q -> In u vertices ->
  ip_path q (config u []) (config v []) -> balanced u v.
Proof.
  intros Hwf Hu Hpath; destruct u as [n x], v as [m y].
  assert (Hcovered : covered (n, x) (m, y) []).
  { apply (path_covered (n, x) _ _ Hwf Hpath).
    - intros j d incoming Heq; injection Heq as Hj Hd Hstack; subst j d incoming.
      apply covered_root, balanced_refl; exact Hu.
    - reflexivity. }
  inversion Hcovered; assumption.
Qed.

Lemma prefix_vertex root v : ip_problem_wf q -> In root vertices -> prefix root v ->
  In v vertices.
Proof.
  intros Hwf Hroot Hprefix; induction Hprefix as [|u v Hprefix IH Hbalanced |
    p u v Hprefix IH Hcall].
  - exact Hroot.
  - exact (proj2 (balanced_vertices _ _ Hwf Hbalanced)).
  - exact (proj2 (arc_vertices _ _ _ Hwf Hcall)).
Qed.

Variable EP : encoding P.

(** Action buckets are built once, before any worklist iteration. *)
Definition actions : Map.t (ip_kind P) (list (vertex N D * vertex N D)) :=
  index (kind_encoding EP) arcs.

Definition action_rows (kind : ip_kind P) : list (vertex N D * vertex N D) :=
  bucket (kind_encoding EP) actions kind.

Lemma action_rows_exact kind u v : In (u, v) (action_rows kind) <-> arc kind u v.
Proof.
  apply index_exact.
Qed.

Definition calls : list (P * (vertex N D * vertex N D)) :=
  flat_map (fun p => map (fun uv => (p, uv)) (action_rows (IpCall p))) (ip_sites q).

Lemma arc_site p u v : ip_problem_wf q -> arc (IpCall p) u v -> In p (ip_sites q).
Proof.
  intros [_ [_ [_ Hwf]]] Harc; apply arc_exact in Harc.
  destruct Harc as [e [He [Hkind _]]].
  destruct (Hwf e He) as [_ [_ [_ [Hsite _]]]]; rewrite Hkind in Hsite; exact Hsite.
Qed.

Lemma calls_exact p u v : ip_problem_wf q ->
  (In (p, (u, v)) calls <-> arc (IpCall p) u v).
Proof.
  intro Hwf; unfold calls; rewrite in_flat_map; split.
  - intros [p' [_ Hin]]; apply in_map_iff in Hin.
    destruct Hin as [uv [Heq Hin]]; injection Heq as Hp Huv; subst p' uv.
    apply action_rows_exact; exact Hin.
  - intro Harc; exists p; split; [eapply arc_site; eassumption |].
    apply in_map_iff; exists (u, v); split; [reflexivity | apply action_rows_exact; exact Harc].
Qed.

(** Matching consults the return bucket at the exact call-site encoding. *)
Definition matches : list (vertex N D * (vertex N D * (vertex N D * vertex N D))) :=
  flat_map (fun call => let '(p, (u, entry)) := call in
    map (fun ret => (u, (entry, ret))) (action_rows (IpReturn p))) calls.

Lemma matches_exact u entry exit v : ip_problem_wf q ->
  (In (u, (entry, (exit, v))) matches <->
    exists p, arc (IpCall p) u entry /\ arc (IpReturn p) exit v).
Proof.
  intro Hwf; unfold matches; rewrite in_flat_map; split.
  - intros [[p [a b]] [Hcall Hmatch]]; apply in_map_iff in Hmatch.
    destruct Hmatch as [[c d] [Heq Hreturn]]; injection Heq as Hu He Hx Hv.
    subst a b c d; exists p; split.
    + apply calls_exact; assumption.
    + apply action_rows_exact; exact Hreturn.
  - intros [p [Hcall Hreturn]]; exists (p, (u, entry)); split.
    + apply calls_exact; assumption.
    + apply in_map_iff; exists (exit, v); split; [reflexivity |].
      apply action_rows_exact; exact Hreturn.
Qed.

(** Ground constraints implement balanced closure and prefix propagation. *)
Definition rules (root : vertex N D) : list (IpHorn.rule (fact N D)) :=
  IpHorn.Seed (inr root) ::
    map (fun u => IpHorn.Seed (inl (u, u))) vertices ++
    flat_map (fun uv => map (fun a =>
      IpHorn.Unary (inl (a, fst uv)) (inl (a, snd uv))) vertices)
      (action_rows IpInternal) ++
    flat_map (fun matched => let '(u, (entry, (exit, v))) := matched in
      map (fun a => IpHorn.Binary (inl (a, u)) (inl (entry, exit)) (inl (a, v)))
        vertices) matches ++
    flat_map (fun u => map (fun v =>
      IpHorn.Binary (inr u) (inl (u, v)) (inr v)) vertices) vertices ++
    map (fun call => let '(_, (u, v)) := call in IpHorn.Unary (inr u) (inr v)) calls.

(** This declarative rule view fixes the balanced and prefix inference rules. *)
Inductive production (root : vertex N D) : IpHorn.rule (fact N D) -> Prop :=
  | production_root : production root (IpHorn.Seed (inr root))
  | production_refl : forall u, In u vertices ->
      production root (IpHorn.Seed (inl (u, u)))
  | production_internal : forall a u v, In a vertices -> arc IpInternal u v ->
      production root (IpHorn.Unary (inl (a, u)) (inl (a, v)))
  | production_matched : forall a u entry exit v p,
      In a vertices -> arc (IpCall p) u entry -> arc (IpReturn p) exit v ->
      production root (IpHorn.Binary (inl (a, u)) (inl (entry, exit)) (inl (a, v)))
  | production_prefix : forall u v, In u vertices -> In v vertices ->
      production root (IpHorn.Binary (inr u) (inl (u, v)) (inr v))
  | production_call : forall p u v, arc (IpCall p) u v ->
      production root (IpHorn.Unary (inr u) (inr v)).

Lemma rules_sound root r : ip_problem_wf q -> In r (rules root) -> production root r.
Proof.
  intros Hwf Hin; unfold rules in Hin; cbn [In] in Hin.
  destruct Hin as [Heq | Hin]; [subst r; apply production_root |].
  repeat rewrite in_app_iff in Hin; destruct Hin as [Hin | [Hin | [Hin | [Hin | Hin]]]].
  - apply in_map_iff in Hin; destruct Hin as [u [Heq Hu]]; subst r.
    apply production_refl; exact Hu.
  - apply in_flat_map in Hin; destruct Hin as [[u v] [Harc Hin]].
    apply in_map_iff in Hin; destruct Hin as [a [Heq Ha]]; subst r.
    apply production_internal; [exact Ha | apply action_rows_exact; exact Harc].
  - apply in_flat_map in Hin; destruct Hin as [[u [entry [exit v]]] [Hmatch Hin]].
    apply in_map_iff in Hin; destruct Hin as [a [Heq Ha]]; subst r.
    apply matches_exact in Hmatch; [|exact Hwf]; destruct Hmatch as [p [Hcall Hreturn]].
    eapply production_matched; eassumption.
  - apply in_flat_map in Hin; destruct Hin as [u [Hu Hin]].
    apply in_map_iff in Hin; destruct Hin as [v [Heq Hv]]; subst r.
    apply production_prefix; assumption.
  - apply in_map_iff in Hin; destruct Hin as [[p [u v]] [Heq Hcall]]; subst r.
    apply (production_call root p); apply calls_exact; assumption.
Qed.

Lemma rules_complete root r : ip_problem_wf q -> production root r -> In r (rules root).
Proof.
  intros Hwf Hproduction; unfold rules; cbn [In].
  destruct Hproduction as [|u Hu | a u v Ha Harc |
    a u entry exit v p Ha Hcall Hreturn | u v Hu Hv | p u v Hcall].
  - now left.
  - right; apply in_app_iff; left; apply in_map_iff; exists u; split; [reflexivity | exact Hu].
  - right; apply in_app_iff; right; apply in_app_iff; left.
    apply in_flat_map; exists (u, v); split; [apply action_rows_exact; exact Harc |].
    apply in_map_iff; exists a; split; [reflexivity | exact Ha].
  - right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
    apply in_flat_map; exists (u, (entry, (exit, v))); split.
    + apply matches_exact; [exact Hwf | exists p; split; assumption].
    + apply in_map_iff; exists a; split; [reflexivity | exact Ha].
  - right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right.
    apply in_app_iff; left; apply in_flat_map; exists u; split; [exact Hu |].
    apply in_map_iff; exists v; split; [reflexivity | exact Hv].
  - right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right.
    apply in_app_iff; right; apply in_map_iff; exists (p, (u, v)); split; [reflexivity |].
    apply calls_exact; assumption.
Qed.

Definition meaning (root : vertex N D) (f : fact N D) : Prop :=
  match f with
  | inl (u, v) => balanced u v
  | inr v => prefix root v
  end.

Lemma production_closed root r : production root r ->
  (forall f, In f (IpHorn.reads r) -> meaning root f) -> meaning root (IpHorn.target r).
Proof.
  intros Hproduction Hreads; destruct Hproduction as [|u Hu | a u v Ha Harc |
    a u entry exit v p Ha Hcall Hreturn | u v Hu Hv | p u v Hcall];
    cbn [meaning IpHorn.target] in *.
  - apply prefix_root.
  - apply balanced_refl; exact Hu.
  - eapply balanced_internal; [apply (Hreads (inl (a, u))); now left | exact Harc].
  - eapply balanced_call; [apply (Hreads (inl (a, u))); now left | exact Hcall |
      apply (Hreads (inl (entry, exit))); right; now left | exact Hreturn].
  - eapply prefix_balanced; [apply (Hreads (inr u)); now left |
      apply (Hreads (inl (u, v))); right; now left].
  - eapply prefix_call; [apply (Hreads (inr u)); now left | exact Hcall].
Qed.

Lemma derives_meaning root f : ip_problem_wf q ->
  IpHorn.derives (rules root) f -> meaning root f.
Proof.
  intros Hwf Hderive; induction Hderive as [f Hr | f g Hr Hf IHf |
    f g h Hr Hf IHf Hg IHg]; apply (production_closed root _ (rules_sound root _ Hwf Hr)).
  - intros x Hx; contradiction.
  - intros x [Heq | Hbad]; [now subst x | contradiction].
  - intros x [Heq | [Heq | Hbad]]; [now subst x | now subst x | contradiction].
Qed.

Lemma balanced_derives root a b : ip_problem_wf q -> balanced a b ->
  IpHorn.derives (rules root) (inl (a, b)).
Proof.
  intros Hwf Hbalanced; induction Hbalanced as [u Hu | a u v Hbalanced IH Harc |
    a u entry exit v p Hbalanced IH Hcall Hinner IHinner Hreturn].
  - apply IpHorn.derives_seed, rules_complete; [exact Hwf | apply production_refl; exact Hu].
  - eapply IpHorn.derives_unary; [apply rules_complete; [exact Hwf |] | exact IH].
    apply production_internal; [exact (proj1 (balanced_vertices _ _ Hwf Hbalanced)) | exact Harc].
  - eapply IpHorn.derives_binary;
      [apply rules_complete; [exact Hwf |] | exact IH | exact IHinner].
    eapply production_matched; [exact (proj1 (balanced_vertices _ _ Hwf Hbalanced)) |
      exact Hcall | exact Hreturn].
Qed.

Lemma prefix_derives root v : ip_problem_wf q -> In root vertices -> prefix root v ->
  IpHorn.derives (rules root) (inr v).
Proof.
  intros Hwf Hroot Hprefix; induction Hprefix as [|u v Hprefix IH Hbalanced |
    p u v Hprefix IH Hcall].
  - apply IpHorn.derives_seed, rules_complete; [exact Hwf | apply production_root].
  - eapply IpHorn.derives_binary with (x := inr u) (y := inl (u, v)).
    + apply rules_complete; [exact Hwf |].
      apply production_prefix; [eapply prefix_vertex; eassumption |
        exact (proj2 (balanced_vertices _ _ Hwf Hbalanced))].
    + exact IH.
    + apply balanced_derives; assumption.
  - eapply IpHorn.derives_unary; [apply rules_complete; [exact Hwf |] | exact IH].
    eapply production_call; exact Hcall.
Qed.

(** Generated balanced summaries are precisely the empty-stack paths. *)
Theorem summaries_exact root a b : ip_problem_wf q -> In a vertices ->
  (IpHorn.derives (rules root) (inl (a, b)) <->
    ip_path q (config a []) (config b [])).
Proof.
  intros Hwf Ha; split.
  - intro Hderive; apply balanced_sound.
    exact (derives_meaning root _ Hwf Hderive).
  - intro Hpath; apply balanced_derives; [exact Hwf |].
    apply balanced_complete; assumption.
Qed.

End Problem.

End IpTab.
Import IpTab.

(** The selected IFDS engine tabulates balanced summaries and reachable prefixes. *)
Definition ifds_solve {N P D} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (q : ip_problem N P D) (start : N) (seed : option D) : N -> option D -> bool :=
  let result := IpHorn.solve (fact_encoding EN ED) (rules q EP (start, seed)) in
  fun n d => result (inr (n, d)).

(** Reachability is exact for arbitrary finite matched paths, including pending calls. *)
Theorem ifds_solve_exact {N P D} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (q : ip_problem N P D) (start : N) (seed : option D) :
  ip_problem_wf q -> In start (ip_nodes q) ->
  (match seed with None => True | Some d => In d (ip_facts q) end) ->
  forall n d, ifds_solve EN EP ED q start seed n d = true <->
    exists stack, ip_path q (start, seed, []) (n, d, stack).
Proof.
  intros Hwf Hstart Hseed n d; unfold ifds_solve; rewrite IpHorn.solve_exact; split.
  - intro Hderive; apply (prefix_sound q (start, seed) (n, d)).
    exact (derives_meaning q EP (start, seed) _ Hwf Hderive).
  - intros [stack Hpath]; apply prefix_derives; [exact Hwf | apply vertices_exact; split;
      assumption |].
    apply (prefix_complete q (start, seed) (n, d) stack); [exact Hwf | | exact Hpath].
    apply vertices_exact; split; assumption.
Qed.

(** * Weighted paths *)

(** Weights decorate individual exploded-edge occurrences with value transformers. *)
Record ide_problem (N P D A : Type) : Type := IdeProblem {
  ide_graph : ip_problem N P D;
  ide_lattice : lattice A;
  ide_values : list A;
  ide_weight : ip_edge N P D -> option D -> option D -> A -> A
}.

Arguments IdeProblem {N P D A}.
Arguments ide_graph {N P D A}.
Arguments ide_lattice {N P D A}.
Arguments ide_values {N P D A}.
Arguments ide_weight {N P D A}.

(** IDE requires a finite value carrier and distributive edge weights over actual pairs. *)
Record ide_laws {N P D A} (q : ide_problem N P D A) : Prop := {
  ide_graph_wf : ip_problem_wf (ide_graph q);
  ide_value_finite : forall a, In a (ide_values q);
  ide_lat_laws : lattice_laws (ide_lattice q);
  ide_lub_laws : lub_laws (ide_lattice q);
  ide_distributive : forall e x y a b, In e (ip_edges (ide_graph q)) ->
    In (x, y) (ip_pairs e) ->
    equivalent (ide_lattice q)
      (ide_weight q e x y (join (ide_lattice q) a b))
      (join (ide_lattice q) (ide_weight q e x y a) (ide_weight q e x y b))
}.

Arguments ide_graph_wf {N P D A q}.
Arguments ide_value_finite {N P D A q}.
Arguments ide_lat_laws {N P D A q}.
Arguments ide_lub_laws {N P D A q}.
Arguments ide_distributive {N P D A q}.

(** A weighted path applies each selected pair's transformer in trace order. *)
Inductive ide_path {N P D A} (q : ide_problem N P D A) :
    N * option D * list P -> A -> N * option D * list P -> A -> Prop :=
  | ide_path_refl : forall c a, ide_path q c a c a
  | ide_path_step : forall n x stack e n' y stack' a c b,
      ip_step (ide_graph q) (n, x, stack) e (n', y, stack') ->
      ide_path q (n', y, stack') (ide_weight q e x y a) c b ->
      ide_path q (n, x, stack) a c b.

Lemma ide_path_graph {N P D A} (q : ide_problem N P D A) c a c' b :
  ide_path q c a c' b -> ip_path (ide_graph q) c c'.
Proof.
  intro Hpath; induction Hpath as [c a | n x stack e n' y stack' a c b Hstep Hpath IH].
  - apply ip_path_refl.
  - eapply ip_path_step; eassumption.
Qed.

(** * Finite extensional function tables *)

Module IdeTable.

(** A vector has one output per input position, with all outputs in the finite range. *)
Fixpoint vectors {A B} (positions : list A) (range : list B) : list (list B) :=
  match positions with
  | [] => [[]]
  | _ :: rest => flat_map (fun b => map (fun tail => b :: tail) (vectors rest range)) range
  end.

Lemma vectors_exact {A B} (positions : list A) (range : list B) values :
  In values (vectors positions range) <->
    length values = length positions /\ Forall (fun b => In b range) values.
Proof.
  revert values; induction positions as [|position positions IH]; intros [|b values]; cbn.
  - split; [intros _; split; [reflexivity | constructor] | intros _; now left].
  - split; [intros [Hbad | Hbad]; [discriminate | contradiction] | intros [Hbad _]; discriminate].
  - rewrite in_flat_map; split.
    + intros [c [_ Hin]]; apply in_map_iff in Hin; destruct Hin as [tail [Hbad _]]; discriminate.
    + intros [Hbad _]; discriminate.
  - rewrite in_flat_map; split.
    + intros [c [Hc Hin]]; apply in_map_iff in Hin.
      destruct Hin as [tail [Heq Htail]]; injection Heq as Hc' Htail'; subst c tail.
      apply IH in Htail; destruct Htail as [Hlength Hall].
      split; [now rewrite Hlength | constructor; assumption].
    + intros [Hlength Hall]; inversion Hall as [|? ? Hb Htail]; subst.
      exists b; split; [exact Hb | apply in_map_iff; exists values; split; [reflexivity |]].
      apply IH; split; [lia | exact Htail].
Qed.

Section Tables.
Context {A : Type} (EA : encoding A) (L : lattice A) (domain : list A).

(** Keys are indexed once; applying a table subsequently uses trie lookup. *)
Fixpoint build (inputs outputs : list A) : Map.t A A :=
  match inputs, outputs with
  | input :: inputs', output :: outputs' => Map.set EA input output (build inputs' outputs')
  | _, _ => Map.empty
  end.

Definition apply_table (table : Map.t A A) (a : A) : A :=
  match Map.get EA a table with
  | Some b => b
  | None => bot L
  end.

Definition eval (outputs : list A) (a : A) : A := apply_table (build domain outputs) a.

Lemma build_total inputs outputs a : length outputs = length inputs -> In a inputs ->
  exists b, Map.get EA a (build inputs outputs) = Some b.
Proof.
  revert outputs; induction inputs as [|x inputs IH]; intros [|y outputs] Hlength Hin;
    cbn in Hlength; try discriminate; [contradiction |].
  cbn [build]; destruct (Pos.eqb (encode EA a) (encode EA x)) eqn:Heq.
  - apply Pos.eqb_eq, (encode_injective EA) in Heq; subst x.
    exists y; apply Map.get_set_same.
  - assert (Hne : a <> x) by (intro H; subst x; rewrite Pos.eqb_refl in Heq; discriminate).
    rewrite Map.get_set_other by exact Hne; apply IH; [lia |].
    destruct Hin as [Heq' | Hin]; [congruence | exact Hin].
Qed.

Lemma build_identity inputs a : In a inputs -> Map.get EA a (build inputs inputs) = Some a.
Proof.
  induction inputs as [|x inputs IH]; intro Hin; [contradiction |].
  cbn [build]; destruct (Pos.eqb (encode EA a) (encode EA x)) eqn:Heq.
  - apply Pos.eqb_eq, (encode_injective EA) in Heq; subst x; apply Map.get_set_same.
  - assert (Hne : a <> x) by (intro H; subst x; rewrite Pos.eqb_refl in Heq; discriminate).
    rewrite Map.get_set_other by exact Hne; apply IH.
    destruct Hin as [Heq' | Hin]; [congruence | exact Hin].
Qed.

Lemma build_map inputs outputs f a :
  Map.get EA a (build inputs (map f outputs)) = option_map f (Map.get EA a (build inputs outputs)).
Proof.
  revert outputs; induction inputs as [|x inputs IH]; intros [|y outputs]; cbn [build map].
  - now rewrite Map.get_empty.
  - now rewrite Map.get_empty.
  - now rewrite Map.get_empty.
  - destruct (Pos.eqb (encode EA a) (encode EA x)) eqn:Heq.
    + apply Pos.eqb_eq, (encode_injective EA) in Heq; subst x.
      now rewrite !Map.get_set_same.
    + assert (Hne : a <> x) by (intro H; subst x; rewrite Pos.eqb_refl in Heq; discriminate).
      rewrite !Map.get_set_other by exact Hne; apply IH.
Qed.

Lemma build_injective inputs left right : NoDup inputs ->
  length left = length inputs -> length right = length inputs ->
  (forall a, In a inputs -> Map.get EA a (build inputs left) = Map.get EA a (build inputs right)) ->
  left = right.
Proof.
  revert left right; induction inputs as [|a inputs IH]; intros left right Hnodup Hl Hr Hget.
  - destruct left, right; cbn in *; congruence.
  - destruct left as [|b left], right as [|c right]; cbn in Hl, Hr; try discriminate.
    inversion Hnodup as [|? ? Hfresh Htail]; subst.
    pose proof (Hget a (or_introl eq_refl)) as Hhead; cbn [build] in Hhead.
    rewrite !Map.get_set_same in Hhead; injection Hhead as Hbc; subst c.
    f_equal; apply IH; [exact Htail | lia | lia |].
    intros x Hx; specialize (Hget x (or_intror Hx)); cbn [build] in Hget.
    assert (Hne : x <> a) by (intro Heq; subst x; contradiction).
    rewrite !Map.get_set_other in Hget by exact Hne; exact Hget.
Qed.

Lemma eval_identity a : In a domain -> eval domain a = a.
Proof.
  intro Hin; unfold eval, apply_table; now rewrite build_identity.
Qed.

(** Equal observations identify finite vectors when input positions are distinct. *)
Theorem eval_extensional left right : NoDup domain ->
  length left = length domain -> length right = length domain ->
  (forall a, In a domain -> eval left a = eval right a) -> left = right.
Proof.
  intros Hnodup Hl Hr Heval; apply (build_injective domain left right Hnodup Hl Hr).
  intros a Ha; destruct (build_total domain left a Hl Ha) as [b Hb].
  destruct (build_total domain right a Hr Ha) as [c Hc].
  specialize (Heval a Ha); unfold eval, apply_table in Heval; rewrite Hb, Hc in Heval.
  now rewrite Hb, Hc, Heval.
Qed.

(** Mapping a weight over a vector represents actual function composition. *)
Theorem eval_compose outputs f a : length outputs = length domain -> In a domain ->
  eval (map f outputs) a = f (eval outputs a).
Proof.
  intros Hlength Hin; destruct (build_total domain outputs a Hlength Hin) as [b Hb].
  unfold eval, apply_table; rewrite build_map, Hb; reflexivity.
Qed.

Definition compose (outer inner : list A) : list A := map (eval outer) inner.

Lemma compose_pointwise outer inner a : length inner = length domain -> In a domain ->
  eval (compose outer inner) a = eval outer (eval inner a).
Proof.
  apply eval_compose.
Qed.

Definition pointwise_join (left right : list A) : list A :=
  map (fun input => join L (eval left input) (eval right input)) domain.

Lemma build_tabulate inputs f a : In a inputs ->
  Map.get EA a (build inputs (map f inputs)) = Some (f a).
Proof.
  intro Hin; rewrite build_map, build_identity by exact Hin; reflexivity.
Qed.

(** The vector representation supports pointwise joins without function extensionality. *)
Theorem join_pointwise left right a : In a domain ->
  eval (pointwise_join left right) a = join L (eval left a) (eval right a).
Proof.
  intro Hin; unfold eval at 1; unfold pointwise_join, apply_table.
  now rewrite build_tabulate.
Qed.

Definition functions : list (list A) := vectors domain domain.

Definition registry : Map.t (list A) (Map.t A A) :=
  fold_right (fun outputs idx => Map.set (list_encoding EA) outputs (build domain outputs) idx)
    Map.empty functions.

Lemma registry_exact outputs : In outputs functions ->
  Map.get (list_encoding EA) outputs registry = Some (build domain outputs).
Proof.
  unfold registry; generalize functions as fs; intros fs.
  induction fs as [|f fs IH]; intro Hin; [contradiction |].
  cbn [fold_right]; destruct (Pos.eqb (encode (list_encoding EA) outputs)
    (encode (list_encoding EA) f)) eqn:Heq.
  - apply Pos.eqb_eq, (encode_injective (list_encoding EA)) in Heq; subst f.
    apply Map.get_set_same.
  - assert (Hne : outputs <> f) by
      (intro H; subst f; rewrite Pos.eqb_refl in Heq; discriminate).
    rewrite Map.get_set_other by exact Hne; apply IH.
    destruct Hin as [Heq' | Hin]; [congruence | exact Hin].
Qed.

Definition indexed_eval (idx : Map.t (list A) (Map.t A A)) (outputs : list A) (a : A) : A :=
  match Map.get (list_encoding EA) outputs idx with
  | Some table => apply_table table a
  | None => bot L
  end.

Lemma indexed_eval_exact outputs a : In outputs functions ->
  indexed_eval registry outputs a = eval outputs a.
Proof.
  intro Hin; unfold indexed_eval; now rewrite registry_exact.
Qed.

End Tables.

End IdeTable.
Import IdeTable.

(** * Indexed finite joins *)

Module IpJoin.

Section Joins.
Context {K A : Type} (EK : encoding K) (L : lattice A).

Definition put (k : K) (a : A) (m : Map.t K A) : Map.t K A :=
  Map.set EK k (join L a (lookup EK L m k)) m.

Definition collect (xs : list (K * A)) : Map.t K A :=
  fold_right (fun kv m => put (fst kv) (snd kv) m) Map.empty xs.

Lemma lookup_put k a m j : lookup EK L (put k a m) j =
  if Pos.eqb (encode EK j) (encode EK k)
  then join L a (lookup EK L m j) else lookup EK L m j.
Proof.
  destruct (Pos.eqb (encode EK j) (encode EK k)) eqn:Heq; unfold put, lookup at 1.
  - apply Pos.eqb_eq, (encode_injective EK) in Heq; subst j.
    now rewrite Map.get_set_same.
  - assert (Hne : j <> k) by (intro H; subst j; rewrite Pos.eqb_refl in Heq; discriminate).
    now rewrite Map.get_set_other by exact Hne.
Qed.

(** Each collected contribution lies below the result at its own key. *)
Theorem collect_upper (HL : lattice_laws L) xs k a : In (k, a) xs ->
  leb L a (lookup EK L (collect xs) k) = true.
Proof.
  induction xs as [|[j b] xs IH]; intro Hin; [contradiction |].
  cbn [collect fold_right fst snd]; rewrite lookup_put.
  destruct (Pos.eqb (encode EK k) (encode EK j)) eqn:Heq.
  - apply Pos.eqb_eq, (encode_injective EK) in Heq; subst j.
    destruct Hin as [Heq | Hin].
    + injection Heq as Heq; subst b; apply join_upper_l; exact HL.
    + eapply (leb_trans HL); [apply IH; exact Hin | apply join_upper_r; exact HL].
  - destruct Hin as [Heq' | Hin]; [injection Heq' as Hkey; subst j;
      rewrite Pos.eqb_refl in Heq; discriminate | apply IH; exact Hin].
Qed.

(** The collected result is below every upper bound of the contributions at that key. *)
Theorem collect_least (HL : lattice_laws L) (HJ : lub_laws L) xs k upper :
  (forall a, In (k, a) xs -> leb L a upper = true) ->
  leb L (lookup EK L (collect xs) k) upper = true.
Proof.
  induction xs as [|[j b] xs IH]; intro Hupper.
  - unfold collect, lookup; cbn [fold_right]; rewrite Map.get_empty; apply bot_least; exact HL.
  - cbn [collect fold_right fst snd]; rewrite lookup_put.
    destruct (Pos.eqb (encode EK k) (encode EK j)) eqn:Heq.
    + apply Pos.eqb_eq, (encode_injective EK) in Heq; subst j.
      apply (join_least HJ); [apply Hupper; now left | apply IH; intros a Ha;
        apply Hupper; now right].
    + apply IH; intros a Ha; apply Hupper; now right.
Qed.

End Joins.

End IpJoin.
Import IpJoin.

(** * Function-carrying matched tabulation *)

Module IdeTab.

Section Lift.
Context {N P D A : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (EA : encoding A) (q : ide_problem N P D A).

Definition domain : list A := FinSet.elements (FinSet.of_list EA (ide_values q)).

Lemma domain_exact a : In a domain <-> In a (ide_values q).
Proof.
  unfold domain; rewrite FinSet.elements_spec by apply FinSet.wf_fold_add, Map.wf_empty.
  apply FinSet.of_list_spec.
Qed.

Lemma domain_total (Hq : ide_laws q) a : In a domain.
Proof.
  apply domain_exact, (ide_value_finite Hq).
Qed.

Definition function_keys : list (list A) := IdeTable.functions domain.

Lemma function_identity : In domain function_keys.
Proof.
  apply vectors_exact; split; [reflexivity | apply Forall_forall; intros a Ha; exact Ha].
Qed.

Lemma function_compose (Hq : ide_laws q) f w : In f function_keys ->
  In (map w f) function_keys.
Proof.
  intro Hf; apply vectors_exact in Hf; destruct Hf as [Hlength Hall].
  apply vectors_exact; split; [now rewrite length_map |].
  apply Forall_forall; intros b Hb; apply domain_total; exact Hq.
Qed.

Definition lifted_fact : Type := (option D * list A)%type.

Definition lifted_encoding : encoding lifted_fact :=
  pair_encoding (option_encoding ED) (list_encoding EA).

Definition lifted_facts : list lifted_fact :=
  FinSet.elements (FinSet.of_list lifted_encoding
    (list_prod (None :: map (@Some D) (ip_facts (ide_graph q))) function_keys)).

Lemma lifted_facts_exact d f : In (d, f) lifted_facts <->
  valid_fact (ide_graph q) d /\ In f function_keys.
Proof.
  unfold lifted_facts; rewrite FinSet.elements_spec by apply FinSet.wf_fold_add, Map.wf_empty.
  rewrite FinSet.of_list_spec, in_prod_iff; split.
  - intros [Hd Hf]; split; [|exact Hf]; destruct d as [d |]; [|exact I].
    destruct Hd as [Hbad | Hd]; [discriminate |]; apply in_map_iff in Hd.
    destruct Hd as [x [Heq Hx]]; injection Heq as Heq; now subst x.
  - intros [Hd Hf]; split; [|exact Hf]; destruct d as [d |].
    + right; apply in_map; exact Hd.
    + now left.
Qed.

(** Composition is computed extensionally on every input position before indexing. *)
Definition edge (e : ip_edge N P D) : ip_edge N P lifted_fact :=
  IpEdge (ip_source e) (ip_target e) (ip_action e)
    ((None, None) :: flat_map (fun xy => map (fun f =>
      (Some (fst xy, f), Some (snd xy, map (ide_weight q e (fst xy) (snd xy)) f)))
      function_keys) (ip_pairs e)).

Definition graph : ip_problem N P lifted_fact :=
  IpProblem (ip_nodes (ide_graph q)) (ip_sites (ide_graph q)) lifted_facts
    (map edge (ip_edges (ide_graph q))).

Lemma edge_pairs e x f y g :
  In (Some (x, f), Some (y, g)) (ip_pairs (edge e)) <->
  In (x, y) (ip_pairs e) /\ In f function_keys /\ g = map (ide_weight q e x y) f.
Proof.
  cbn [edge ip_pairs In]; split.
  - intros [Hbad | Hin]; [discriminate |]; apply in_flat_map in Hin.
    destruct Hin as [[a b] [Hpair Hin]]; apply in_map_iff in Hin.
    destruct Hin as [h [Heq Hh]]; cbn [fst snd] in Heq.
    injection Heq as Hx Hf Hy Hg; subst a b h g; repeat split; assumption.
  - intros [Hpair [Hf ->]]; right; apply in_flat_map; exists (x, y); split; [exact Hpair |].
    apply in_map_iff; exists f; split; [reflexivity | exact Hf].
Qed.

Lemma edge_pairs_view e s t : In (s, t) (ip_pairs (edge e)) ->
  (s = None /\ t = None) \/ exists x y f,
    In (x, y) (ip_pairs e) /\ In f function_keys /\ s = Some (x, f) /\
    t = Some (y, map (ide_weight q e x y) f).
Proof.
  cbn [edge ip_pairs In]; intros [Heq | Hin].
  - injection Heq as Hs Ht; left; split; symmetry; assumption.
  - right; apply in_flat_map in Hin; destruct Hin as [[x y] [Hpair Hin]].
    apply in_map_iff in Hin; destruct Hin as [f [Heq Hf]].
    injection Heq as Hs Ht; exists x, y, f; repeat split; try assumption; symmetry; assumption.
Qed.

(** The lifted finite graph retains every weighted pair and an isolated administrative zero. *)
Theorem graph_wf (Hq : ide_laws q) : ip_problem_wf graph.
Proof.
  destruct (ide_graph_wf Hq) as [Hnodes [Hsites [Hfacts Hedges]]].
  split; [exact Hnodes |]; split; [exact Hsites |]; split.
  - apply (FinSet.elements_nodup lifted_encoding), FinSet.wf_fold_add, Map.wf_empty.
  - intros lifted Hin; apply in_map_iff in Hin; destruct Hin as [e [Heq He]]; subst lifted.
    destruct (Hedges e He) as [Hsource [Htarget [Hzero [Hsite Hpairs]]]].
    split; [exact Hsource |]; split; [exact Htarget |]; split; [now left |].
    split; [exact Hsite |]; intros x y Hpair; apply edge_pairs_view in Hpair.
    destruct Hpair as [[-> ->] | [a [b [f [Hab [Hf [-> ->]]]]]]]; [split; exact I |].
    destruct (Hpairs a b Hab) as [Ha Hb]; split; apply lifted_facts_exact; split.
    + exact Ha.
    + exact Hf.
    + exact Hb.
    + apply function_compose; assumption.
Qed.

Definition function_value (f : list A) (a : A) : A :=
  IdeTable.eval EA (ide_lattice q) domain f a.

Lemma function_value_identity (Hq : ide_laws q) a : function_value domain a = a.
Proof.
  apply eval_identity, domain_total; exact Hq.
Qed.

Lemma function_value_compose (Hq : ide_laws q) f w a : In f function_keys ->
  function_value (map w f) a = w (function_value f a).
Proof.
  intro Hf; apply vectors_exact in Hf.
  apply eval_compose; [exact (proj1 Hf) | apply domain_total; exact Hq].
Qed.

(** Canonical distinct input positions make table-vector equality extensional. *)
Theorem function_extensional f g : In f function_keys -> In g function_keys ->
  (forall a, function_value f a = function_value g a) -> f = g.
Proof.
  intros Hf Hg Heq; apply vectors_exact in Hf; apply vectors_exact in Hg.
  apply (eval_extensional EA (ide_lattice q) domain).
  - apply (FinSet.elements_nodup EA), FinSet.wf_fold_add, Map.wf_empty.
  - exact (proj1 Hf).
  - exact (proj1 Hg).
  - intros a Ha; apply Heq.
Qed.

Definition function_join f g : list A :=
  IdeTable.pointwise_join EA (ide_lattice q) domain f g.

Lemma function_join_closed (Hq : ide_laws q) f g : In (function_join f g) function_keys.
Proof.
  apply vectors_exact; unfold function_join, pointwise_join; split.
  - apply length_map.
  - apply Forall_forall; intros a Ha; apply domain_total; exact Hq.
Qed.

Lemma function_value_join (Hq : ide_laws q) f g a :
  function_value (function_join f g) a =
    join (ide_lattice q) (function_value f a) (function_value g a).
Proof.
  apply join_pointwise, domain_total; exact Hq.
Qed.

(** Edge composition distributes over finite pointwise table joins. *)
Theorem function_join_distributive (Hq : ide_laws q) e x y f g a :
  In f function_keys -> In g function_keys ->
  In e (ip_edges (ide_graph q)) -> In (x, y) (ip_pairs e) ->
  equivalent (ide_lattice q)
    (function_value (map (ide_weight q e x y) (function_join f g)) a)
    (function_value (function_join (map (ide_weight q e x y) f)
      (map (ide_weight q e x y) g)) a).
Proof.
  intros Hf Hg He Hxy.
  rewrite function_value_compose by (first [exact Hq | apply function_join_closed; exact Hq]).
  rewrite !function_value_join by exact Hq.
  rewrite !function_value_compose by assumption.
  apply (ide_distributive Hq); assumption.
Qed.

Definition lift_config (c : N * option D * list P) (f : list A) :
    N * option lifted_fact * list P :=
  let '(n, x, stack) := c in (n, Some (x, f), stack).

Lemma step_lift c e c' : ip_step (ide_graph q) c e c' -> forall f,
  In f function_keys -> ip_step graph (lift_config c f) (edge e)
    (lift_config c' (map (ide_weight q e (snd (fst c)) (snd (fst c'))) f)).
Proof.
  intro Hstep; destruct Hstep as [e x y stack He Hkind Hpair |
    e p x y stack He Hkind Hpair | e p x y stack He Hkind Hpair]; intros f Hf.
  - apply ip_step_internal with (e := edge e).
    + apply in_map; exact He.
    + exact Hkind.
    + apply edge_pairs; repeat split; try assumption; reflexivity.
  - eapply ip_step_call with (e := edge e).
    + apply in_map; exact He.
    + exact Hkind.
    + apply edge_pairs; repeat split; try assumption; reflexivity.
  - eapply ip_step_return with (e := edge e).
    + apply in_map; exact He.
    + exact Hkind.
    + apply edge_pairs; repeat split; try assumption; reflexivity.
Qed.

Lemma edge_from_some e x f t : In (Some (x, f), t) (ip_pairs (edge e)) ->
  exists y, In (x, y) (ip_pairs e) /\ In f function_keys /\
    t = Some (y, map (ide_weight q e x y) f).
Proof.
  intro Hpair; apply edge_pairs_view in Hpair.
  destruct Hpair as [[Hbad _] | [a [b [g [Hpair [Hg [Heq Ht]]]]]]]; [discriminate |].
  injection Heq as Hx Hf; subst a g; exists b; repeat split; assumption.
Qed.

Lemma step_unlift c lifted c' : ip_step graph c lifted c' ->
  forall n x f stack, c = (n, Some (x, f), stack) ->
  exists e n' y stack',
    c' = (n', Some (y, map (ide_weight q e x y) f), stack') /\
    In f function_keys /\ ip_step (ide_graph q) (n, x, stack) e (n', y, stack').
Proof.
  intro Hstep; destruct Hstep as [lifted s t incoming Hmember Hkind Hpair |
    lifted p s t incoming Hmember Hkind Hpair |
    lifted p s t incoming Hmember Hkind Hpair]; intros n x f stack Heq;
    apply in_map_iff in Hmember; destruct Hmember as [e [Hedge He]]; subst lifted;
    injection Heq as Hn Hs Hstack; subst n s.
  - subst stack; destruct (edge_from_some e x f t Hpair) as [y [Hxy [Hf Ht]]]; subst t.
    exists e, (ip_target e), y, incoming; split; [reflexivity |]; split; [exact Hf |].
    apply ip_step_internal; assumption.
  - subst stack; destruct (edge_from_some e x f t Hpair) as [y [Hxy [Hf Ht]]]; subst t.
    exists e, (ip_target e), y, (p :: incoming); split; [reflexivity |]; split; [exact Hf |].
    eapply ip_step_call; eassumption.
  - subst stack; destruct (edge_from_some e x f t Hpair) as [y [Hxy [Hf Ht]]]; subst t.
    exists e, (ip_target e), y, incoming; split; [reflexivity |]; split; [exact Hf |].
    eapply ip_step_return; eassumption.
Qed.

(** Each real weighted path is represented by an extensional function-table path. *)
Theorem path_lift (Hq : ide_laws q) c a c' b : ide_path q c a c' b ->
  forall f initial, In f function_keys -> function_value f initial = a ->
    exists g, In g function_keys /\ function_value g initial = b /\
      ip_path graph (lift_config c f) (lift_config c' g).
Proof.
  intro Hpath; induction Hpath as [c a | n x stack e n' y stack' a c b Hstep Hpath IH];
    intros f initial Hf Hvalue.
  - exists f; split; [exact Hf |]; split; [exact Hvalue | apply ip_path_refl].
  - assert (Hnext : In (map (ide_weight q e x y) f) function_keys).
    { apply function_compose; assumption. }
    assert (Hnextvalue : function_value (map (ide_weight q e x y) f) initial =
      ide_weight q e x y a).
    { rewrite function_value_compose by assumption; now rewrite Hvalue. }
    destruct (IH _ initial Hnext Hnextvalue) as [g [Hg [Hresult Hlift]]].
    exists g; split; [exact Hg |]; split; [exact Hresult |].
    eapply ip_path_step; [apply step_lift; [exact Hstep | exact Hf] | exact Hlift].
Qed.

(** A lifted path always has a real source path; the administrative zero stays unreachable. *)
Theorem path_unlift (Hq : ide_laws q) initial c c' : ip_path graph c c' ->
  forall n x f stack, c = (n, Some (x, f), stack) -> In f function_keys ->
    exists n' y g stack', c' = (n', Some (y, g), stack') /\ In g function_keys /\
      ide_path q (n, x, stack) (function_value f initial)
        (n', y, stack') (function_value g initial).
Proof.
  intro Hpath; induction Hpath as [c | c lifted c' c'' Hstep Hpath IH];
    intros n x f stack Heq Hf.
  - subst c; exists n, x, f, stack; split; [reflexivity |]; split; [exact Hf |].
    apply ide_path_refl.
  - destruct (step_unlift _ _ _ Hstep n x f stack Heq) as
      [e [next [y [nextstack [Hnext [_ Horiginal]]]]]].
    assert (Hnextfunction : In (map (ide_weight q e x y) f) function_keys).
    { apply function_compose; assumption. }
    destruct (IH next y _ nextstack Hnext Hnextfunction) as
      [last [z [g [laststack [Hlast [Hg Horiginalpath]]]]]].
    exists last, z, g, laststack; split; [exact Hlast |]; split; [exact Hg |].
    rewrite function_value_compose in Horiginalpath by assumption.
    eapply ide_path_step; [exact Horiginal | exact Horiginalpath].
Qed.

Definition reachable (start : N) (seed : option D) : N -> option lifted_fact -> bool :=
  ifds_solve EN EP lifted_encoding graph start (Some (seed, domain)).

Lemma reachable_domain (Hq : ide_laws q) start seed :
  In start (ip_nodes (ide_graph q)) -> valid_fact (ide_graph q) seed ->
  In start (ip_nodes graph) /\ In (seed, domain) (ip_facts graph).
Proof.
  intros Hstart Hseed; split; [exact Hstart |]; apply lifted_facts_exact; split;
    [exact Hseed | apply function_identity].
Qed.

Lemma reachable_sound (Hq : ide_laws q) start seed initial n d f :
  In start (ip_nodes (ide_graph q)) -> valid_fact (ide_graph q) seed ->
  reachable start seed n (Some (d, f)) = true ->
  In f function_keys /\ exists stack,
    ide_path q (start, seed, []) initial (n, d, stack) (function_value f initial).
Proof.
  intros Hstart Hseed Hreachable.
  destruct (reachable_domain Hq start seed Hstart Hseed) as [Hnode Hfact].
  apply (proj1 (ifds_solve_exact EN EP lifted_encoding graph start (Some (seed, domain))
    (graph_wf Hq) Hnode Hfact n (Some (d, f)))) in Hreachable.
  destruct Hreachable as [stack Hpath].
  destruct (path_unlift Hq initial _ _ Hpath start seed domain [] eq_refl function_identity) as
    [last [y [g [laststack [Heq [Hg Horiginal]]]]]].
  injection Heq as Hn Hd Hf Hstack; subst last y g laststack.
  split; [exact Hg | exists stack].
  rewrite function_value_identity in Horiginal by exact Hq; exact Horiginal.
Qed.

Lemma reachable_complete (Hq : ide_laws q) start seed initial n d stack b :
  In start (ip_nodes (ide_graph q)) -> valid_fact (ide_graph q) seed ->
  ide_path q (start, seed, []) initial (n, d, stack) b ->
  exists f, In f function_keys /\ reachable start seed n (Some (d, f)) = true /\
    function_value f initial = b.
Proof.
  intros Hstart Hseed Hpath.
  destruct (path_lift Hq _ _ _ _ Hpath domain initial function_identity
    (function_value_identity Hq initial)) as [f [Hf [Hvalue Hlift]]].
  exists f; split; [exact Hf |]; split; [|exact Hvalue].
  destruct (reachable_domain Hq start seed Hstart Hseed) as [Hnode Hfact].
  apply (proj2 (ifds_solve_exact EN EP lifted_encoding graph start (Some (seed, domain))
    (graph_wf Hq) Hnode Hfact n (Some (d, f)))); exists stack; exact Hlift.
Qed.

Definition value_index : Map.t (list A) (Map.t A A) := IdeTable.registry EA domain.

Definition registered_value (f : list A) (a : A) : A :=
  IdeTable.indexed_eval EA (ide_lattice q) value_index f a.

Lemma registered_value_exact f a : In f function_keys ->
  registered_value f a = function_value f a.
Proof.
  apply indexed_eval_exact.
Qed.

(** Flatten once; each aggregation callback uses only prepared table and reachability lookups. *)
Definition contributions (start : N) (seed : option D) (initial : A) :
    list (vertex N D * A) :=
  let result := reachable start seed in
  let tables := value_index in
  flat_map (fun query => let '((n, d), f) := query in
    if result n (Some (d, f)) then
      [((n, d), IdeTable.indexed_eval EA (ide_lattice q) tables f initial)] else [])
    (list_prod (vertices (ide_graph q)) function_keys).

Lemma contributions_exact start seed initial n d b :
  In ((n, d), b) (contributions start seed initial) <-> exists f,
    In (n, d) (vertices (ide_graph q)) /\ In f function_keys /\
    reachable start seed n (Some (d, f)) = true /\ b = function_value f initial.
Proof.
  unfold contributions; rewrite in_flat_map; split.
  - intros [[[m x] f] [Hquery Hin]]; apply in_prod_iff in Hquery.
    destruct Hquery as [Hnode Hf].
    destruct (reachable start seed m (Some (x, f))) eqn:Hreach; [|contradiction].
    destruct Hin as [Heq | Hbad]; [|contradiction].
    injection Heq as Hn Hd Hb; subst m x b; exists f; repeat split; try assumption.
    apply registered_value_exact; exact Hf.
  - intros [f [Hnode [Hf [Hreach ->]]]]; exists ((n, d), f); split.
    + apply in_prod_iff; split; assumption.
    + rewrite Hreach; left; f_equal; apply registered_value_exact; exact Hf.
Qed.

Definition result (start : N) (seed : option D) (initial : A) : N -> option D -> A :=
  let collected := IpJoin.collect (vertex_encoding EN ED) (ide_lattice q)
    (contributions start seed initial) in
  fun n d => lookup (vertex_encoding EN ED) (ide_lattice q) collected (n, d).

Lemma path_vertex (Hq : ide_laws q) start seed initial n d stack b :
  In start (ip_nodes (ide_graph q)) -> valid_fact (ide_graph q) seed ->
  ide_path q (start, seed, []) initial (n, d, stack) b ->
  In (n, d) (vertices (ide_graph q)).
Proof.
  intros Hstart Hseed Hpath.
  assert (Hroot : In (start, seed) (vertices (ide_graph q))).
  { apply vertices_exact; split; assumption. }
  apply (prefix_vertex (ide_graph q) (start, seed) (n, d) (ide_graph_wf Hq) Hroot).
  apply (prefix_complete (ide_graph q) (start, seed) (n, d) stack);
    [apply ide_graph_wf; exact Hq | exact Hroot | apply ide_path_graph in Hpath; exact Hpath].
Qed.

(** Every actual weighted path is bounded by the value joined at its endpoint. *)
Theorem result_upper (Hq : ide_laws q) start seed initial :
  In start (ip_nodes (ide_graph q)) -> valid_fact (ide_graph q) seed ->
  forall n d stack b, ide_path q (start, seed, []) initial (n, d, stack) b ->
    leb (ide_lattice q) b (result start seed initial n d) = true.
Proof.
  intros Hstart Hseed n d stack b Hpath; apply IpJoin.collect_upper; [apply ide_lat_laws;
    exact Hq |].
  apply contributions_exact.
  destruct (reachable_complete Hq start seed initial n d stack b Hstart Hseed Hpath) as
    [f [Hf [Hreach Hvalue]]].
  exists f; split; [eapply path_vertex; eassumption |]; split; [exact Hf |]; split;
    [exact Hreach | symmetry; exact Hvalue].
Qed.

(** No value beyond the least upper bound of actual paths is contributed. *)
Theorem result_least (Hq : ide_laws q) start seed initial :
  In start (ip_nodes (ide_graph q)) -> valid_fact (ide_graph q) seed ->
  forall n d upper,
    (forall stack b, ide_path q (start, seed, []) initial (n, d, stack) b ->
      leb (ide_lattice q) b upper = true) ->
    leb (ide_lattice q) (result start seed initial n d) upper = true.
Proof.
  intros Hstart Hseed n d upper Hupper; apply IpJoin.collect_least;
    [apply ide_lat_laws; exact Hq | apply ide_lub_laws; exact Hq |].
  intros b Hin; apply contributions_exact in Hin; destruct Hin as [f [_ [Hf [Hreach ->]]]].
  destruct (reachable_sound Hq start seed initial n d f Hstart Hseed Hreach) as
    [_ [stack Hpath]]; apply (Hupper stack _ Hpath).
Qed.

End Lift.

End IdeTab.
Import IdeTab.

(** IDE joins exactly the values of reachable function tables, independently of absent paths. *)
Definition ide_solve {N P D A} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (EA : encoding A) (q : ide_problem N P D A) (start : N) (seed : option D) (a : A) :
    N -> option D -> A := IdeTab.result EN EP ED EA q start seed a.

(** The weighted result is the least upper bound over all matched path values. *)
Theorem ide_solve_exact {N P D A} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (EA : encoding A) (q : ide_problem N P D A) (start : N) (seed : option D) (a : A) :
  ide_laws q -> In start (ip_nodes (ide_graph q)) ->
  (match seed with None => True | Some d => In d (ip_facts (ide_graph q)) end) ->
  forall n d,
    (forall stack b, ide_path q (start, seed, []) a (n, d, stack) b ->
      leb (ide_lattice q) b (ide_solve EN EP ED EA q start seed a n d) = true) /\
    (forall upper, (forall stack b, ide_path q (start, seed, []) a (n, d, stack) b ->
       leb (ide_lattice q) b upper = true) ->
      leb (ide_lattice q) (ide_solve EN EP ED EA q start seed a n d) upper = true).
Proof.
  intros Hq Hstart Hseed n d; split.
  - apply result_upper; assumption.
  - apply result_least; assumption.
Qed.
