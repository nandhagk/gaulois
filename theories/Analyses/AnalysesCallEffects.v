(** * Normal returns and memory-effect summaries

    Local semantic laws connect matched paths and five-component summaries to concrete steps.
    For example, an unknown callback may read, write, allocate, free and impose ordering.
    Builds on: AnalysesInterprocedural, DomainsFootprint, Order and ViewsSummary. *)

From Stdlib Require Import List Bool.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderProduct OrderPowerset OrderLift.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Fixpoint Require Import FixpointSystem.
From Gaulois.Views Require Import ViewsSemantics ViewsCalls ViewsSummary.
From Gaulois.Analyses Require Import AnalysesInterprocedural AnalysesLiveness.
Import List.ListNotations.

(** * Normal-return projection *)

(** The projection retains matched call stacks and identifies only normal returns. *)
Record return_projection (S N P D : Type) : Type := ReturnProjection {
  return_config : S -> N * option D * list P;
  normal_return : S -> bool
}.

Arguments ReturnProjection {S N P D}.
Arguments return_config {S N P D}.
Arguments normal_return {S N P D}.

(** Each reachable step projects to a path, and every normal return projects to the exit. *)
Record return_projection_laws {S O N P D} (m : semantics S O)
    (q : ip_problem N P D) (rp : return_projection S N P D) (exit : N) : Prop := {
  return_local_step : forall s l t, reachable_state m s -> step m s l t ->
    ip_path q (return_config rp s) (return_config rp t);
  return_exit : forall s, normal_return rp s = true ->
    exists d stack, return_config rp s = (exit, d, stack)
}.

Arguments return_local_step {S O N P D m q rp exit}.
Arguments return_exit {S O N P D m q rp exit}.

(** Any reachable exit fact permits a normal return in the abstract problem. *)
Definition may_return {N P D} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (q : ip_problem N P D) (start exit : N) (seed : option D) : bool :=
  existsb (ifds_solve EN EP ED q start seed exit)
    (None :: map (@Some D) (ip_facts q)).

Lemma return_exec_path {S O N P D} (m : semantics S O) (q : ip_problem N P D)
    (rp : return_projection S N P D) exit :
  return_projection_laws m q rp exit -> forall s tr t, exec m s tr t ->
  reachable_state m s -> ip_path q (return_config rp s) (return_config rp t).
Proof.
  intros Hlaws s tr t Hrun; induction Hrun as [s | s l u tr t Hstep Hrun IH];
    intro Hreachable.
  - apply ip_path_refl.
  - eapply ip_path_trans.
    + exact (return_local_step Hlaws s l u Hreachable Hstep).
    + apply IH; eapply reachable_state_step; eassumption.
Qed.

Lemma return_step_fact {N P D} (q : ip_problem N P D) c e c' :
  ip_problem_wf q -> ip_step q c e c' -> IpTab.valid_fact q (snd (fst c')).
Proof.
  intros [_ [_ [_ Hedges]]] Hstep.
  destruct Hstep as [e x y stack He Haction Hpair |
    e p x y stack He Haction Hpair | e p x y stack He Haction Hpair];
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (Hedges e He)))) x y Hpair)).
Qed.

Lemma return_path_fact {N P D} (q : ip_problem N P D) c c' :
  ip_problem_wf q -> ip_path q c c' ->
  IpTab.valid_fact q (snd (fst c)) -> IpTab.valid_fact q (snd (fst c')).
Proof.
  intros Hwf Hpath; induction Hpath as [c | c e u t Hstep Hpath IH]; intro Hfact.
  - exact Hfact.
  - apply IH; eapply return_step_fact; eassumption.
Qed.

(** A false query excludes normal returns along every run, while allowing other endings. *)
Theorem may_return_sound {S O N P D} (m : semantics S O) (EN : encoding N)
    (EP : encoding P) (ED : encoding D) (q : ip_problem N P D)
    (rp : return_projection S N P D) (start exit : N) (seed : option D) (s : S) :
  ip_problem_wf q -> In start (ip_nodes q) ->
  (match seed with None => True | Some d => In d (ip_facts q) end) ->
  return_projection_laws m q rp exit -> reachable_state m s ->
  return_config rp s = (start, seed, []) ->
  may_return EN EP ED q start exit seed = false ->
  forall tr t, exec m s tr t -> normal_return rp t = false.
Proof.
  intros Hwf Hstart Hseed Hlaws Hreachable Hconfig Hno tr t Hrun.
  destruct (normal_return rp t) eqn:Hnormal; [|reflexivity].
  destruct (return_exit Hlaws t Hnormal) as [d [stack Hexit]].
  pose proof (return_exec_path m q rp exit Hlaws s tr t Hrun Hreachable) as Hpath.
  rewrite Hconfig, Hexit in Hpath.
  assert (Hfact : In d (None :: map (@Some D) (ip_facts q))).
  { pose proof (return_path_fact q _ _ Hwf Hpath Hseed) as Hd.
    destruct d as [d |]; [right; apply in_map; exact Hd | left; reflexivity]. }
  assert (Hyes : may_return EN EP ED q start exit seed = true).
  { apply existsb_exists; exists d; split; [exact Hfact |].
    apply (proj2 (ifds_solve_exact EN EP ED q start seed Hwf Hstart Hseed exit d)).
    exists stack; exact Hpath. }
  rewrite Hno in Hyes; discriminate.
Qed.

(** * Finite may-effect lattice *)

(** Unknown sets cover every footprint, with separate allocation, free and ordering flags. *)
Record modref (T : Type) (ET : encoding T) (U : list (footprint T)) : Type := ModRef {
  mr_reads : option (finite_set (footprint_encoding ET) U);
  mr_writes : option (finite_set (footprint_encoding ET) U);
  mr_allocates : bool;
  mr_frees : bool;
  mr_orders : bool
}.

Arguments ModRef {T ET U}.
Arguments mr_reads {T ET U}.
Arguments mr_writes {T ET U}.
Arguments mr_allocates {T ET U}.
Arguments mr_frees {T ET U}.
Arguments mr_orders {T ET U}.

(** A missing finite set denotes all footprints, including those outside the universe. *)
Definition mr_contains {T} {ET : encoding T} {U : list (footprint T)}
    (s : option (finite_set (footprint_encoding ET) U)) (f : footprint T) : bool :=
  match s with
  | None => true
  | Some v => fmem (footprint_encoding ET) f v
  end.

(** Unknown external activity conservatively enables all five observations. *)
Definition unknown_modref {T} (ET : encoding T) (U : list (footprint T)) : modref T ET U :=
  ModRef None None true true true.

Local Definition mr_set_pack {A} (s : option A) : lift_top A :=
  match s with
  | Some a => Elem a
  | None => Unknown
  end.

Local Definition mr_set_unpack {A} (s : lift_top A) : option A :=
  match s with
  | Elem a => Some a
  | Unknown => None
  end.

Local Definition mr_product {T} (ET : encoding T) (U : list (footprint T)) :=
  product_lattice (lift_top_lattice (finite_powerset_lattice (footprint_encoding ET) U))
    (product_lattice (lift_top_lattice (finite_powerset_lattice (footprint_encoding ET) U))
      (product_lattice bool_lattice (product_lattice bool_lattice bool_lattice))).

Local Definition mr_pack {T ET U} (a : modref T ET U) :=
  (mr_set_pack (mr_reads a),
    (mr_set_pack (mr_writes a), (mr_allocates a, (mr_frees a, mr_orders a)))).

Local Definition mr_unpack {T} {ET : encoding T} {U : list (footprint T)}
    (a : lift_top (finite_set (footprint_encoding ET) U) *
      (lift_top (finite_set (footprint_encoding ET) U) * (bool * (bool * bool)))) :
    modref T ET U :=
  ModRef (mr_set_unpack (fst a)) (mr_set_unpack (fst (snd a)))
    (fst (snd (snd a))) (fst (snd (snd (snd a)))) (snd (snd (snd (snd a)))).

Local Lemma mr_pack_unpack {T ET U} a :
  @mr_pack T ET U (mr_unpack a) = a.
Proof.
  destruct a as [[r |] [[w |] [alloc [free order]]]]; reflexivity.
Qed.

(** Inclusion and disjunction are transported from the five-coordinate product. *)
Definition modref_lattice {T} (ET : encoding T) (U : list (footprint T)) :
    lattice (modref T ET U) :=
  {| leb := fun a b => leb (mr_product ET U) (mr_pack a) (mr_pack b);
     bot := mr_unpack (bot (mr_product ET U));
     join := fun a b => mr_unpack (join (mr_product ET U) (mr_pack a) (mr_pack b));
     widen := fun a b => mr_unpack (widen (mr_product ET U) (mr_pack a) (mr_pack b));
     narrow := fun a b => mr_unpack (narrow (mr_product ET U) (mr_pack a) (mr_pack b)) |}.

Local Lemma mr_product_laws {T} (ET : encoding T) U : lattice_laws (mr_product ET U).
Proof.
  unfold mr_product; repeat apply product_laws;
    first [apply lift_top_laws, finite_powerset_laws | apply bool_laws].
Qed.

Local Lemma mr_product_lub {T} (ET : encoding T) U : lub_laws (mr_product ET U).
Proof.
  unfold mr_product; repeat apply product_lub;
    first [apply lift_top_lub, finite_powerset_lub | apply bool_lub].
Qed.

(** The summaries satisfy the weak laws and genuine least-upper-bound laws. *)
Theorem modref_lattice_laws {T} (ET : encoding T) (U : list (footprint T)) :
  lattice_laws (modref_lattice ET U) /\ lub_laws (modref_lattice ET U).
Proof.
  pose proof (mr_product_laws ET U) as Hlaws; split; constructor.
  - intro a; exact (leb_refl Hlaws (mr_pack a)).
  - intros a b c Hab Hbc; exact (leb_trans Hlaws _ _ _ Hab Hbc).
  - intro a; change (leb (mr_product ET U)
      (mr_pack (mr_unpack (bot (mr_product ET U)))) (mr_pack a) = true).
    rewrite mr_pack_unpack; apply (bot_least Hlaws).
  - intros a b; change (leb (mr_product ET U) (mr_pack a)
      (mr_pack (mr_unpack (join (mr_product ET U) (mr_pack a) (mr_pack b)))) = true).
    rewrite mr_pack_unpack; apply (join_upper_l Hlaws).
  - intros a b; change (leb (mr_product ET U) (mr_pack b)
      (mr_pack (mr_unpack (join (mr_product ET U) (mr_pack a) (mr_pack b)))) = true).
    rewrite mr_pack_unpack; apply (join_upper_r Hlaws).
  - intros a b; change (leb (mr_product ET U) (mr_pack a)
      (mr_pack (mr_unpack (widen (mr_product ET U) (mr_pack a) (mr_pack b)))) = true).
    rewrite mr_pack_unpack; apply (widen_upper_l Hlaws).
  - intros a b; change (leb (mr_product ET U) (mr_pack b)
      (mr_pack (mr_unpack (widen (mr_product ET U) (mr_pack a) (mr_pack b)))) = true).
    rewrite mr_pack_unpack; apply (widen_upper_r Hlaws).
  - intros a b Hba; change (leb (mr_product ET U)
      (mr_pack (mr_unpack (narrow (mr_product ET U) (mr_pack a) (mr_pack b))))
      (mr_pack a) = true); rewrite mr_pack_unpack.
    exact (narrow_lower Hlaws _ _ Hba).
  - intros a b Hba; change (leb (mr_product ET U) (mr_pack b)
      (mr_pack (mr_unpack (narrow (mr_product ET U) (mr_pack a) (mr_pack b)))) = true);
      rewrite mr_pack_unpack.
    exact (narrow_upper Hlaws _ _ Hba).
  - intros a b c Ha Hb; change (leb (mr_product ET U)
      (mr_pack (mr_unpack (join (mr_product ET U) (mr_pack a) (mr_pack b))))
      (mr_pack c) = true); rewrite mr_pack_unpack.
    exact (join_least (mr_product_lub ET U) _ _ _ Ha Hb).
Qed.

Local Definition mr_product_height {T} (ET : encoding T) U (Hnodup : NoDup U) :
    monotone_height (mr_product ET U) :=
  product_height (lift_top_laws _ (finite_powerset_laws _ _))
    (product_laws _ _ (lift_top_laws _ (finite_powerset_laws _ _))
      (product_laws _ _ bool_laws (product_laws _ _ bool_laws bool_laws)))
    (lift_top_height (finite_powerset_height (footprint_encoding ET) U Hnodup))
    (product_height (lift_top_laws _ (finite_powerset_laws _ _))
      (product_laws _ _ bool_laws (product_laws _ _ bool_laws bool_laws))
      (lift_top_height (finite_powerset_height (footprint_encoding ET) U Hnodup))
      (product_height bool_laws (product_laws _ _ bool_laws bool_laws)
        bool_height (product_height bool_laws bool_laws bool_height bool_height))).

(** A finite footprint universe bounds every strict summary growth. *)
Theorem modref_lattice_height {T} (ET : encoding T) (U : list (footprint T)) :
  NoDup U -> inhabited (height (modref_lattice ET U)).
Proof.
  intro Hnodup; pose (H := base_height (mr_product_height ET U Hnodup)).
  refine (inhabits {| rank := fun a => rank H (mr_pack a); bound := bound H |}).
  - intro a; apply rank_bounded.
  - intros a b Hstrict.
    change (leb (mr_product ET U)
      (mr_pack (mr_unpack (join (mr_product ET U) (mr_pack a) (mr_pack b))))
      (mr_pack a) = false) in Hstrict.
    change (rank H (mr_pack a) < rank H
      (mr_pack (mr_unpack (join (mr_product ET U) (mr_pack a) (mr_pack b))))).
    rewrite mr_pack_unpack in *.
    apply (join_rank_grows H); exact Hstrict.
Qed.

(** Callee summaries pass unchanged through each call site. *)
Definition modref_spec {F P T} (ET : encoding T) (U : list (footprint T))
    (local_effect : F -> modref T ET U) : summary_spec F P (modref T ET U) :=
  SummarySpec (modref_lattice ET U) local_effect (fun _ _ a => a).

(** * Concrete effect observations *)

(** The client observes footprint lists and three independent effects of a transition. *)
Record effect_observer (S O T : Type) : Type := EffectObserver {
  actual_reads : S -> list O -> S -> list (footprint T);
  actual_writes : S -> list O -> S -> list (footprint T);
  actual_allocates : S -> list O -> S -> bool;
  actual_frees : S -> list O -> S -> bool;
  actual_orders : S -> list O -> S -> bool
}.

Arguments EffectObserver {S O T}.
Arguments actual_reads {S O T}.
Arguments actual_writes {S O T}.
Arguments actual_allocates {S O T}.
Arguments actual_frees {S O T}.
Arguments actual_orders {S O T}.

(** Coverage includes every observed footprint and every enabled effect flag. *)
Definition modref_covers {S O T} {ET : encoding T} {U : list (footprint T)}
    (obs : effect_observer S O T) (a : modref T ET U) (s : S) (l : list O) (t : S) : Prop :=
  (forall f, In f (actual_reads obs s l t) -> mr_contains (mr_reads a) f = true) /\
  (forall f, In f (actual_writes obs s l t) -> mr_contains (mr_writes a) f = true) /\
  (actual_allocates obs s l t = true -> mr_allocates a = true) /\
  (actual_frees obs s l t = true -> mr_frees a = true) /\
  (actual_orders obs s l t = true -> mr_orders a = true).

(** The innermost function covers locally executed effects, including external activity. *)
Record modref_local_laws {S O F P T} (m : semantics S O) (cv : calls_view S F P)
    (ET : encoding T) (U : list (footprint T)) (obs : effect_observer S O T)
    (local_effect : F -> modref T ET U) : Prop := {
  modref_local_step : forall s l t, reachable_state m s -> step m s l t ->
    modref_covers obs (local_effect (here cv s)) s l t
}.

Arguments modref_local_step {S O F P T m cv ET U obs local_effect}.

Lemma mr_contains_monotone {T} {ET : encoding T} {U : list (footprint T)} a b f :
  leb (lift_top_lattice (finite_powerset_lattice (footprint_encoding ET) U))
    (mr_set_pack a) (mr_set_pack b) = true ->
  mr_contains a f = true -> mr_contains b f = true.
Proof.
  destruct a as [a |], b as [b |]; cbn [mr_set_pack lift_top_lattice mr_contains];
    intros Hle Hmem; try discriminate; try reflexivity.
  change (FinSet.subset (footprint_encoding ET) (proj1_sig a) (proj1_sig b) = true) in Hle.
  exact (proj1 (FinSet.subset_spec (footprint_encoding ET) (proj1_sig a) (proj1_sig b)
    (proj1 (proj2_sig a))) Hle f Hmem).
Qed.

(** Every coordinate of coverage is monotone in the summary order. *)
Lemma modref_covers_monotone {S O T} {ET : encoding T} {U : list (footprint T)}
    (obs : effect_observer S O T) (a b : modref T ET U) s l t :
  leb (modref_lattice ET U) a b = true ->
  modref_covers obs a s l t -> modref_covers obs b s l t.
Proof.
  intro Hle; change
    (leb (lift_top_lattice (finite_powerset_lattice (footprint_encoding ET) U))
      (mr_set_pack (mr_reads a)) (mr_set_pack (mr_reads b)) &&
      (leb (lift_top_lattice (finite_powerset_lattice (footprint_encoding ET) U))
        (mr_set_pack (mr_writes a)) (mr_set_pack (mr_writes b)) &&
        (implb (mr_allocates a) (mr_allocates b) &&
          (implb (mr_frees a) (mr_frees b) && implb (mr_orders a) (mr_orders b)))) = true)
    in Hle.
  repeat rewrite andb_true_iff in Hle.
  destruct Hle as [Hr [Hw [Ha [Hf Ho]]]].
  intros [Hreads [Hwrites [Halloc [Hfree Horder]]]]; split; [|split; [|split; [|split]]].
  - intros f Hin; eapply mr_contains_monotone; [exact Hr | apply Hreads; exact Hin].
  - intros f Hin; eapply mr_contains_monotone; [exact Hw | apply Hwrites; exact Hin].
  - intro Hactual; rewrite (Halloc Hactual) in Ha; exact Ha.
  - intro Hactual; rewrite (Hfree Hactual) in Hf; exact Hf.
  - intro Hactual; rewrite (Horder Hactual) in Ho; exact Ho.
Qed.

(** Unknown summaries cover any observation, including footprints outside the finite universe. *)
Lemma unknown_modref_covers {S O T} (ET : encoding T) U (obs : effect_observer S O T) s l t :
  modref_covers obs (unknown_modref ET U) s l t.
Proof.
  split; [|split; [|split; [|split]]]; intros; reflexivity.
Qed.

(** Every active frame's summary covers the actual transition in all five coordinates. *)
Theorem modref_sound {S O F P T} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (ET : encoding T) (U : list (footprint T))
    (obs : effect_observer S O T) (local_effect : F -> modref T ET U)
    (sigma : F -> modref T ET U) :
  calls_view_laws m cv resolve -> modref_local_laws m cv ET U obs local_effect ->
  post_solution (modref_lattice ET U)
    (summary_system cv resolve (modref_spec ET U local_effect)) sigma ->
  forall s l t f, reachable_state m s -> step m s l t -> In f (active cv s) ->
    modref_covers obs (sigma f) s l t.
Proof.
  intros Hcalls Hlocal Hpost.
  apply (summary_sound m cv resolve (modref_spec ET U local_effect)
    (StepCover (modref_covers obs)) sigma Hcalls); [|exact Hpost].
  constructor.
  - intros a b s l t Hle Hcover; eapply modref_covers_monotone; eassumption.
  - intros s l t Hreachable Hstep; exact (modref_local_step Hlocal s l t Hreachable Hstep).
  - intros p g a s l t Hreachable Hframe Hcover; exact Hcover.
Qed.
