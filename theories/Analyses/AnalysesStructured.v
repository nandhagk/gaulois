(** * Structured liveness and loop certificates

    Variable interfaces connect backward live facts, loop-head certificates and replay to behaviour.
    For example, a loop certificate stores its body-entry fact and reconstructs every other point.
    Builds on: ViewsStructured, OrderPowerset, FixpointCut and FixpointSchedule. *)

From Stdlib Require Import List Bool PArith Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderPowerset OrderMonotone.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCut
  FixpointSchedule FixpointCycles.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsAgreement ViewsSkeleton
  ViewsStructured.
From Gaulois.Analyses Require Import AnalysesLiveness.
Import List.ListNotations Skeleton.

(** A client lists the variables read, written and observed by its primitive actions. *)
Record skel_vars (A G X : Type) : Type := SkelVars {
  atom_uses : A -> list X;
  atom_defs : A -> list X;
  atom_trap_uses : A -> list X;
  guard_uses : G -> list X
}.

Arguments atom_uses {A G X}.
Arguments atom_defs {A G X}.
Arguments atom_trap_uses {A G X}.
Arguments guard_uses {A G X}.

(** Primitive transitions respect their declared variables and guard observations. *)
Record skel_vars_laws {A G St O X Cv} (C : skeleton_client A G St O)
    (sv : skel_vars A G X) (look : St -> X -> Cv) : Prop := {
  atom_frame : forall a st l st' x, atom_step C a st l st' -> ~ In x (atom_defs sv a) ->
    look st' x = look st x;
  atom_agrees : forall a st1 l st1' st2, atom_step C a st1 l st1' ->
    (forall x, In x (atom_uses sv a) -> look st1 x = look st2 x) ->
    exists st2', atom_step C a st2 l st2' /\
      forall x, In x (atom_defs sv a) -> look st1' x = look st2' x;
  guard_agrees : forall g st1 st2,
    (forall x, In x (guard_uses sv g) -> look st1 x = look st2 x) ->
    guard_bool C g st1 = guard_bool C g st2 /\ guard_index C g st1 = guard_index C g st2;
  trap_agrees : forall a st1 st2,
    (forall x, In x (atom_trap_uses sv a) -> look st1 x = look st2 x) ->
    (atom_trap C a st1 <-> atom_trap C a st2) /\ (atom_stop C a st1 <-> atom_stop C a st2);
  jump_keeps : forall p n st st' x, jump_effect C p n st st' -> look st' x = look st x
}.

(** An action inventory contains both its inputs and its outputs. *)
Definition act_vars {A G X} (sv : skel_vars A G X) (act : action A G) : list X :=
  match act with
  | AAtom a => atom_uses sv a ++ atom_defs sv a
  | AGuard g _ => guard_uses sv g
  | AIndexIs g _ => guard_uses sv g
  | AIndexAtLeast g _ => guard_uses sv g
  | AJump _ _ => []
  end.

(** * Structured live facts *)

(** Entry observations include primitive traps and partial guard evaluation. *)
Definition skel_exit_uses {A G X} (sv : skel_vars A G X) (prog : stmt A G)
    (n : skel_point) : list X :=
  match n with
  | PEntry p =>
    match sub prog p with
    | Some (Atom a) => atom_trap_uses sv a
    | Some (If g _ _) | Some (JumpIf g _) | Some (JumpTable g _ _) => guard_uses sv g
    | _ => []
    end
  | PExit _ => []
  end.

(** The universe includes every action variable and every ending observation. *)
Definition skel_universe {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) : list X :=
  let actions := skel_acts prog in
  let graph := skeleton_graph prog in
  FinSet.elements (FinSet.of_list EX
    (flat_map (fun e => flat_map (act_vars sv) (actions e)) (edges_of graph) ++
     flat_map (skel_exit_uses sv prog) (Graph.nodes graph))).

(** Live facts have finite support in the program's variable universe. *)
Definition skel_set {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) : Type := finite_set EX (skel_universe EX sv prog).

(** Structured needs are ordered by inclusion. *)
Definition skel_lattice {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) : lattice (skel_set EX sv prog) :=
  finite_powerset_lattice EX (skel_universe EX sv prog).

(** Raw backward actions expose the transfer independently of finite support. *)
Definition skel_raw_actb {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (act : action A G) (a : FinSet.t X) : FinSet.t X :=
  match act with
  | AAtom x => FinSet.union EX (FinSet.diff EX a (FinSet.of_list EX (atom_defs sv x)))
      (FinSet.of_list EX (atom_uses sv x))
  | AJump _ _ => a
  | _ => FinSet.union EX a (FinSet.of_list EX (act_vars sv act))
  end.

(** An action kills its definitions and adds its inputs before the preceding point. *)
Definition skel_actb {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) : action A G -> skel_set EX sv prog -> skel_set EX sv prog :=
  let universe := skel_universe EX sv prog in
  fun act a => finite_clamp EX universe
    (skel_raw_actb EX sv act (proj1_sig a)).

(** Backward skeleton constraints include every node's ending demands. *)
Definition structured_liveness_system {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) :
    System.t skel_point (dense_constraint skel_point (skel_edge A G)) (skel_set EX sv prog) :=
  let universe := skel_universe EX sv prog in
  skeleton_backward prog
    (fun n => finite_clamp EX universe
      (FinSet.of_list EX (skel_exit_uses sv prog n))) (skel_actb EX sv prog).

(** * Loop-head certificates *)

(** Certificates store facts in the exact preorder of loop heads. *)
Definition certificate {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) : Type := list (skel_point * skel_set EX sv prog).

(** Restriction retains the solution's original proof-carrying head facts. *)
Definition certificate_of {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (sigma : skel_point -> skel_set EX sv prog) : certificate EX sv prog :=
  map (fun n => (n, sigma n)) (loop_heads prog).

(** The static generator declares one dependency for each backward flow. *)
Definition structured_liveness_static {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) : System.static (structured_liveness_system EX sv prog) :=
  skeleton_backward_static prog _ _.

(** Prepare contributors once before planning and expansion. *)
Definition structured_liveness_index {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) :=
  index_system skel_point_encoding (structured_liveness_system EX sv prog)
    (structured_liveness_static EX sv prog).

Local Definition skel_point_eq_dec (x y : skel_point) : {x = y} + {x <> y}.
Proof.
  destruct (Pos.eq_dec (encode skel_point_encoding x) (encode skel_point_encoding y))
    as [Hsame|Hdifferent].
  - left; apply (encode_injective skel_point_encoding); exact Hsame.
  - right; intros ->; contradiction.
Defined.

(** A single preparation and expansion is shared by validation and observer replay. *)
Definition certificate_expand {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (cert : certificate EX sv prog) :
    option (list skel_point * assignment skel_point (skel_set EX sv prog)) :=
  let heads := loop_heads prog in
  if list_eq_dec skel_point_eq_dec (map fst cert) heads then
    let sys := structured_liveness_system EX sv prog in
    let ss := structured_liveness_static EX sv prog in
    let ix := structured_liveness_index EX sv prog in
    let cut := FinSet.of_list skel_point_encoding heads in
    match plan_of skel_point_encoding sys ss ix cut with
    | None => None
    | Some order =>
      match expand skel_point_encoding (skel_lattice EX sv prog) sys ss ix
        (CutCertificate cut (Map.of_list skel_point_encoding cert) order) with
      | None => None
      | Some values => Some (heads ++ order, values)
      end
    end
  else None.

(** Acceptance checks exact ordered keys and genuinely expands the cut certificate. *)
Definition certificate_check {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (cert : certificate EX sv prog) : bool :=
  match certificate_expand EX sv prog cert with Some _ => true | None => false end.

(** Replay visits cut points followed by the non-cut plan, using expanded facts. *)
Definition replay_live {A G X Ob} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (cert : certificate EX sv prog)
    (obs : Ob -> skel_point -> skel_set EX sv prog -> Ob) (z : Ob) : option Ob :=
  match certificate_expand EX sv prog cert with
  | None => None
  | Some (order, values) =>
    Some (replay obs z order (lookup skel_point_encoding (skel_lattice EX sv prog) values))
  end.

(** Replay succeeds exactly on accepted loop-head certificates. *)
Theorem replay_live_iff {A G X Ob} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (cert : certificate EX sv prog)
    (obs : Ob -> skel_point -> skel_set EX sv prog -> Ob) (z : Ob) :
  (exists r, replay_live EX sv prog cert obs z = Some r) <->
  certificate_check EX sv prog cert = true.
Proof.
  unfold replay_live, certificate_check.
  destruct (certificate_expand EX sv prog cert) as [[order values]|]; cbn.
  - split; [reflexivity|intro H; eexists; reflexivity].
  - split; [intros [r H]; discriminate|discriminate].
Qed.

Local Lemma structured_list_wf {K} (EK : encoding K) (xs : list K) :
  FinSet.wf EK (FinSet.of_list EK xs).
Proof.
  apply FinSet.wf_fold_add, Map.wf_empty.
Qed.

Local Lemma loop_head_list_nodup {A G} (prog : stmt A G) : NoDup (loop_heads prog).
Proof.
  unfold loop_heads.
  assert (Hunique : forall ps, NoDup ps -> NoDup
    (flat_map (fun p => match sub prog p with
      | Some (Loop _) => [PEntry (p ++ [DBody])] | _ => [] end) ps)).
  { intros ps Hnodup; induction Hnodup as [|p ps Hfresh Hnodup IH]; cbn; [constructor|].
    destruct (sub prog p) as [s|]; [destruct s|]; cbn; try exact IH.
    constructor; [|exact IH].
    intro Hin; apply in_flat_map in Hin as [q [Hq Hin]].
    destruct (sub prog q) as [t|]; [destruct t|]; cbn in Hin; try contradiction.
    destruct Hin as [Heq|Hfalse]; [|contradiction].
    injection Heq as Heq; apply app_inv_tail in Heq; subst q; contradiction. }
  apply Hunique; exact (proj1 (positions_exact prog)).
Qed.

Local Lemma structured_fold_absent {K V} (EK : encoding K) (rows : list (K * V)) (k : K) :
  ~ In k (map fst rows) -> forall acc,
    Map.get EK k (fold_left (fun m kv => Map.set EK (fst kv) (snd kv) m) rows acc) =
    Map.get EK k acc.
Proof.
  induction rows as [|[q v] rows IH]; cbn; intros Habsent acc; [reflexivity|].
  rewrite IH by tauto; apply Map.get_set_other; intro Heq; subst q; tauto.
Qed.

Local Lemma structured_fold_present {K V} (EK : encoding K) (rows : list (K * V)) :
  NoDup (map fst rows) -> forall k v, In (k, v) rows -> forall acc,
    Map.get EK k (fold_left (fun m kv => Map.set EK (fst kv) (snd kv) m) rows acc) = Some v.
Proof.
  induction rows as [|[q w] rows IH]; cbn; intros Hnodup k v Hin acc; [contradiction|].
  inversion Hnodup as [|q' keys Hfresh Htail]; subst q' keys.
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->; rewrite structured_fold_absent by exact Hfresh.
    apply Map.get_set_same.
  - apply IH; assumption.
Qed.

Local Lemma structured_stored_get {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (cert : certificate EX sv prog) (n : skel_point)
    (a : skel_set EX sv prog) :
  map fst cert = loop_heads prog -> In (n, a) cert ->
  lookup skel_point_encoding (skel_lattice EX sv prog)
    (Map.of_list skel_point_encoding cert) n = a.
Proof.
  intros Hkeys Hin; unfold lookup, Map.of_list.
  rewrite (structured_fold_present skel_point_encoding cert
    ltac:(rewrite Hkeys; apply loop_head_list_nodup) n a Hin Map.empty); reflexivity.
Qed.

Local Lemma structured_restore {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (cert : certificate EX sv prog) (sigma : skel_point -> skel_set EX sv prog) :
  map fst cert = loop_heads prog ->
  (forall n a, In (n, a) cert -> sigma n = a) -> certificate_of EX sv prog sigma = cert.
Proof.
  intros Hkeys Hvalues; unfold certificate_of; rewrite <- Hkeys.
  clear Hkeys.
  induction cert as [|[n a] rest IH]; cbn; [reflexivity|].
  f_equal; [f_equal; apply Hvalues; now left|apply IH; intros; apply Hvalues; now right].
Qed.

(** Accepted certificates expand to a post-solution retaining exactly their original head facts. *)
Theorem certificate_sound {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (cert : certificate EX sv prog) :
  certificate_check EX sv prog cert = true ->
  exists sigma, post_solution (skel_lattice EX sv prog)
    (structured_liveness_system EX sv prog) sigma /\ certificate_of EX sv prog sigma = cert.
Proof.
  unfold certificate_check, certificate_expand.
  destruct (list_eq_dec skel_point_eq_dec (map fst cert) (loop_heads prog)) as [Hkeys|];
    [|discriminate].
  cbn zeta.
  destruct (plan_of skel_point_encoding (structured_liveness_system EX sv prog)
    (structured_liveness_static EX sv prog) (structured_liveness_index EX sv prog)
    (FinSet.of_list skel_point_encoding (loop_heads prog))) as [order|] eqn:Hplan;
    [|discriminate].
  destruct (expand skel_point_encoding (skel_lattice EX sv prog)
    (structured_liveness_system EX sv prog) (structured_liveness_static EX sv prog)
    (structured_liveness_index EX sv prog)
    (CutCertificate (FinSet.of_list skel_point_encoding (loop_heads prog))
      (Map.of_list skel_point_encoding cert) order)) as [values|] eqn:Hexpand;
    [|discriminate].
  intros Haccepted.
  destruct (expand_sound skel_point_encoding (skel_lattice EX sv prog)
    (structured_liveness_system EX sv prog) values (structured_liveness_static EX sv prog)
    (structured_liveness_index EX sv prog)
    (CutCertificate (FinSet.of_list skel_point_encoding (loop_heads prog))
      (Map.of_list skel_point_encoding cert) order) (finite_powerset_laws EX _)
    (index_system_laws _ _ _) (structured_list_wf _ _) Hexpand) as [Hpost Hheads].
  exists (lookup skel_point_encoding (skel_lattice EX sv prog) values); split; [exact Hpost|].
  apply structured_restore; [exact Hkeys|].
  intros n a Hin; rewrite Hheads.
  - apply structured_stored_get; assumption.
  - apply FinSet.of_list_spec; rewrite <- Hkeys; apply in_map_iff; exists (n, a); auto.
Qed.

Local Lemma structured_clamp_spec {K} (EK : encoding K) (U : list K) raw x :
  FinSet.mem EK x (proj1_sig (finite_clamp EK U raw)) = true <->
  In x U /\ FinSet.mem EK x raw = true.
Proof.
  change (FinSet.mem EK x (FinSet.of_list EK (filter (fun k => FinSet.mem EK k raw) U)) = true
    <-> In x U /\ FinSet.mem EK x raw = true).
  rewrite FinSet.of_list_spec, filter_In; reflexivity.
Qed.

Local Lemma skel_actb_monotone {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (act : action A G) :
  monotone_fun (skel_lattice EX sv prog) (skel_lattice EX sv prog) (skel_actb EX sv prog act).
Proof.
  intros a b Hab; apply FinSet.subset_spec;
    [exact (proj1 (proj2_sig (skel_actb EX sv prog act a)))|].
  intros x Hx; apply structured_clamp_spec in Hx as [HU Hx].
  apply structured_clamp_spec; split; [exact HU|].
  pose proof (set_member_subset EX (proj1_sig a) (proj1_sig b) Hab x) as Hinclude.
  destruct act; cbn [skel_raw_actb] in *;
    repeat rewrite FinSet.mem_union in *; try rewrite FinSet.mem_diff in *;
    intuition auto.
Qed.

Local Lemma structured_fold_monotone {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (acts : list (action A G)) :
  monotone_fun (skel_lattice EX sv prog) (skel_lattice EX sv prog)
    (fun a => fold_right (skel_actb EX sv prog) a acts).
Proof.
  induction acts as [|act acts IH]; intros a b Hab; cbn; [exact Hab|].
  apply skel_actb_monotone, IH, Hab.
Qed.

(** The generated system is monotone, so expansion from post-solution cuts is complete. *)
Theorem structured_liveness_monotone {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) :
  monotone_system (skel_lattice EX sv prog) (structured_liveness_system EX sv prog).
Proof.
  intros [n|e] Hlisted; split.
  - intros a b Hab; apply (leb_refl (finite_powerset_laws EX _)).
  - intros a b Hab x v Hin; contradiction.
  - intros a b Hab; change (leb (skel_lattice EX sv prog)
      (edge_bwd prog (skel_actb EX sv prog) e (a (skel_to prog e)))
      (edge_bwd prog (skel_actb EX sv prog) e (b (skel_to prog e))) = true).
    rewrite !edge_bwd_agrees; apply structured_fold_monotone, Hab.
  - intros a b Hab x v Hin; contradiction.
Qed.

Local Lemma structured_plan_exists {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) :
  exists order, plan_of skel_point_encoding (structured_liveness_system EX sv prog)
    (structured_liveness_static EX sv prog) (structured_liveness_index EX sv prog)
    (FinSet.of_list skel_point_encoding (loop_heads prog)) = Some order.
Proof.
  apply (proj1 (proj1 (plan_of_valid skel_point_encoding _ _ _ _
    (index_system_laws _ _ _)))).
  assert (Htest : forall n, FinSet.mem skel_point_encoding n
    (FinSet.of_list skel_point_encoding (loop_heads prog)) = is_loop_head prog n).
  { intro n; apply eq_true_iff_eq; rewrite FinSet.of_list_spec, is_loop_head_iff; reflexivity. }
  intros n Hcycle; apply (skeleton_backward_cuts prog
    (fun n => finite_clamp EX (skel_universe EX sv prog)
      (FinSet.of_list EX (skel_exit_uses sv prog n))) (skel_actb EX sv prog) n).
  assert (Hconvert : forall x y,
    clos_trans skel_point
      (fun x y => flows (structured_liveness_static EX sv prog) x y /\
        FinSet.mem skel_point_encoding y
          (FinSet.of_list skel_point_encoding (loop_heads prog)) = false) x y ->
    clos_trans skel_point
      (fun x y => flows (structured_liveness_static EX sv prog) x y /\
        is_loop_head prog y = false) x y).
  { intros x y Hpath; induction Hpath as [x y [Hflow Hcut]|x y z Hxy IHxy Hyz IHyz].
    - apply t_step; split; [exact Hflow|rewrite <- Htest; exact Hcut].
    - eapply t_trans; eassumption. }
  apply Hconvert; exact Hcycle.
Qed.

(** Every post-solution restricts to an accepted loop-head certificate. *)
Theorem certificate_complete {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (sigma : skel_point -> skel_set EX sv prog) :
  post_solution (skel_lattice EX sv prog) (structured_liveness_system EX sv prog) sigma ->
  certificate_check EX sv prog (certificate_of EX sv prog sigma) = true.
Proof.
  intro Hpost.
  assert (Hkeys : map fst (certificate_of EX sv prog sigma) = loop_heads prog).
  { unfold certificate_of; rewrite map_map; apply map_id. }
  destruct (structured_plan_exists EX sv prog) as [order Horder].
  assert (Hstored : forall n, FinSet.mem skel_point_encoding n
      (FinSet.of_list skel_point_encoding (loop_heads prog)) = true ->
    lookup skel_point_encoding (skel_lattice EX sv prog)
      (Map.of_list skel_point_encoding (certificate_of EX sv prog sigma)) n = sigma n).
  { intros n Hin; apply structured_stored_get; [exact Hkeys|].
    apply FinSet.of_list_spec in Hin; unfold certificate_of; apply in_map_iff; exists n; auto. }
  destruct (expand_complete skel_point_encoding (skel_lattice EX sv prog)
    (structured_liveness_system EX sv prog) sigma (structured_liveness_static EX sv prog)
    (structured_liveness_index EX sv prog)
    (CutCertificate (FinSet.of_list skel_point_encoding (loop_heads prog))
      (Map.of_list skel_point_encoding (certificate_of EX sv prog sigma)) order)
    (finite_powerset_laws EX _) (finite_powerset_lub EX _)
    (structured_liveness_monotone EX sv prog) (index_system_laws _ _ _)
    (structured_list_wf _ _) Hpost) as [values [Hexpand Hbelow]].
  - exact (proj2 (plan_of_valid skel_point_encoding _ _ _ _ (index_system_laws _ _ _))
      order Horder).
  - exact Hstored.
  - unfold certificate_check, certificate_expand.
    destruct (list_eq_dec skel_point_eq_dec
      (map fst (certificate_of EX sv prog sigma)) (loop_heads prog)); [|contradiction].
    rewrite Horder, Hexpand; reflexivity.
Qed.

(** * Behavioural agreement *)

(** Raw needs compare the client's lookup at every member. *)
Definition skel_raw_agreement {St X Cv} (EX : encoding X) (look : St -> X -> Cv) :
    agreement (FinSet.t X) St :=
  Agreement _ _ (fun a s t => forall x, FinSet.mem EX x a = true -> look s x = look t x).

Local Lemma skel_raw_agreement_laws {St X Cv} (EX : encoding X) (look : St -> X -> Cv) :
  agreement_laws (powerset_lattice EX) (skel_raw_agreement EX look).
Proof.
  constructor.
  - intros a s x Hx; reflexivity.
  - intros a b s t Hab Hagree x Hx; apply Hagree; exact (set_member_subset EX a b Hab x Hx).
Qed.

Local Lemma skel_raw_action_match {A G St O X Cv} (EX : encoding X)
    (C : skeleton_client A G St O) (sv : skel_vars A G X) (look : St -> X -> Cv) :
  skeleton_client_laws C -> skel_vars_laws C sv look ->
  forall act a st1 l st1' st2, act_hold C act st1 l st1' ->
    agree (skel_raw_agreement EX look) (skel_raw_actb EX sv act a) st1 st2 ->
    exists st2', act_hold C act st2 l st2' /\ agree (skel_raw_agreement EX look) a st1' st2'.
Proof.
  intros Hclient Hvars [atom|g b|g i|g len|p n] a st1 l st1' st2 Hstep Hagree;
    cbn [act_hold skel_raw_actb skel_raw_agreement agree] in *.
  - assert (Huses : forall x, In x (atom_uses sv atom) -> look st1 x = look st2 x).
    { intros x Hx; apply Hagree, FinSet.mem_union; right; apply FinSet.of_list_spec; exact Hx. }
    destruct (atom_agrees C sv look Hvars atom st1 l st1' st2 Hstep Huses)
      as [st2' [Hstep' Hdefs]].
    exists st2'; split; [exact Hstep'|].
    intros x Hx; destruct (FinSet.mem EX x (FinSet.of_list EX (atom_defs sv atom))) eqn:Hdefined.
    + apply Hdefs; exact (proj1 (FinSet.of_list_spec EX x _) Hdefined).
    + assert (Hnotdef : ~ In x (atom_defs sv atom)).
      { intro Hin; apply (proj2 (FinSet.of_list_spec EX x _)) in Hin; congruence. }
      rewrite (atom_frame C sv look Hvars atom st1 l st1' x Hstep Hnotdef),
        (atom_frame C sv look Hvars atom st2 l st2' x Hstep' Hnotdef).
      apply Hagree, FinSet.mem_union; left; apply FinSet.mem_diff; auto.
  - destruct Hstep as [Hguard [-> ->]].
    assert (Huses : forall x, In x (guard_uses sv g) -> look st1 x = look st2 x).
    { intros x Hx; apply Hagree, FinSet.mem_union; right; apply FinSet.of_list_spec; exact Hx. }
    destruct (guard_agrees C sv look Hvars g st1 st2 Huses) as [Hbool Hindex].
    exists st2; split; [repeat split; congruence|].
    intros x Hx; apply Hagree, FinSet.mem_union; now left.
  - destruct Hstep as [Hguard [-> ->]].
    assert (Huses : forall x, In x (guard_uses sv g) -> look st1 x = look st2 x).
    { intros x Hx; apply Hagree, FinSet.mem_union; right; apply FinSet.of_list_spec; exact Hx. }
    destruct (guard_agrees C sv look Hvars g st1 st2 Huses) as [Hbool Hindex].
    exists st2; split; [repeat split; congruence|].
    intros x Hx; apply Hagree, FinSet.mem_union; now left.
  - destruct Hstep as [[j [Hguard Hbound]] [-> ->]].
    assert (Huses : forall x, In x (guard_uses sv g) -> look st1 x = look st2 x).
    { intros x Hx; apply Hagree, FinSet.mem_union; right; apply FinSet.of_list_spec; exact Hx. }
    destruct (guard_agrees C sv look Hvars g st1 st2 Huses) as [Hbool Hindex].
    exists st2; split.
    + split; [exists j; split; [congruence|exact Hbound]|auto].
    + intros x Hx; apply Hagree, FinSet.mem_union; now left.
  - destruct Hstep as [Hjump ->].
    destruct (jump_total Hclient p n st2) as [st2' Hjump'].
    exists st2'; split; [auto|].
    intros x Hx; rewrite (jump_keeps C sv look Hvars p n st1 st1' x Hjump),
      (jump_keeps C sv look Hvars p n st2 st2' x Hjump'); apply Hagree; exact Hx.
Qed.

Local Lemma skel_raw_exit_match {A G St O X Cv} (EX : encoding X)
    (C : skeleton_client A G St O) (sv : skel_vars A G X) (look : St -> X -> Cv)
    (prog : stmt A G) : skel_vars_laws C sv look ->
  forall p st1 st2,
    agree (skel_raw_agreement EX look) (FinSet.of_list EX (skel_exit_uses sv prog (PEntry p)))
      st1 st2 ->
    (traps_at prog C p st1 <-> traps_at prog C p st2) /\
    (stops_at prog C p st1 <-> stops_at prog C p st2).
Proof.
  intros Hvars p st1 st2 Hagree.
  unfold traps_at, stops_at, skeleton_endings; cbn [trapped stopped].
  unfold skel_exit_uses in Hagree.
  destruct (sub prog p) as [[a|x y|g x y|x|x|n|g n|g ns n]|] eqn:Hsub;
    try (split; tauto).
  - apply (trap_agrees C sv look Hvars a st1 st2).
    intros x Hx; apply Hagree, FinSet.of_list_spec, Hx.
  - destruct (guard_agrees C sv look Hvars g st1 st2)
      as [Hbool Hindex];
      [intros variable Hvariable; apply Hagree, FinSet.of_list_spec, Hvariable|].
    rewrite Hbool; split; tauto.
  - destruct (guard_agrees C sv look Hvars g st1 st2)
      as [Hbool Hindex];
      [intros variable Hvariable; apply Hagree, FinSet.of_list_spec, Hvariable|].
    rewrite Hbool; split; tauto.
  - destruct (guard_agrees C sv look Hvars g st1 st2)
      as [Hbool Hindex];
      [intros variable Hvariable; apply Hagree, FinSet.of_list_spec, Hvariable|].
    rewrite Hindex; split; tauto.
Qed.

Local Lemma skel_universe_action {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) e act x : In e (edges_of (skeleton_graph prog)) ->
  In act (skel_acts prog e) -> In x (act_vars sv act) -> In x (skel_universe EX sv prog).
Proof.
  intros He Hact Hx; unfold skel_universe.
  apply (proj2 (FinSet.elements_spec EX x _ (structured_list_wf EX _))),
    FinSet.of_list_spec, in_or_app; left; apply in_flat_map.
  exists e; split; [exact He|apply in_flat_map; exists act; auto].
Qed.

Local Lemma skel_universe_exit {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) n x : In n (Graph.nodes (skeleton_graph prog)) ->
  In x (skel_exit_uses sv prog n) -> In x (skel_universe EX sv prog).
Proof.
  intros Hn Hx; unfold skel_universe.
  apply (proj2 (FinSet.elements_spec EX x _ (structured_list_wf EX _))),
    FinSet.of_list_spec, in_or_app; right; apply in_flat_map; exists n; auto.
Qed.

Local Lemma skel_raw_actb_within {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) act (a : skel_set EX sv prog) :
  (forall x, In x (act_vars sv act) -> In x (skel_universe EX sv prog)) ->
  within_set EX (skel_universe EX sv prog) (skel_raw_actb EX sv act (proj1_sig a)).
Proof.
  intro Hvars; destruct (proj2_sig a) as [Hwf Hsupport]; split.
  - destruct act; cbn [skel_raw_actb]; try exact Hwf;
      apply FinSet.wf_union; try exact Hwf; try (apply FinSet.wf_diff; [exact Hwf|]);
      apply structured_list_wf.
  - intros x Hx; destruct act; cbn [skel_raw_actb] in Hx;
      try rewrite FinSet.mem_union in Hx; try rewrite FinSet.mem_diff in Hx;
      try rewrite FinSet.of_list_spec in Hx; cbn [act_vars] in Hvars;
      intuition eauto using in_or_app.
Qed.

Local Lemma structured_clamp_identity {K} (EK : encoding K) (U : list K) raw :
  within_set EK U raw -> proj1_sig (finite_clamp EK U raw) = raw.
Proof.
  intros [Hwf Hsupport]; apply (FinSet.extensionality EK).
  - exact (proj1 (proj2_sig (finite_clamp EK U raw))).
  - exact Hwf.
  - intro x; apply eq_true_iff_eq; rewrite structured_clamp_spec; intuition.
Qed.

Local Lemma skel_fold_projection {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) acts :
  (forall act x, In act acts -> In x (act_vars sv act) -> In x (skel_universe EX sv prog)) ->
  forall a, proj1_sig (fold_right (skel_actb EX sv prog) a acts) =
    fold_right (skel_raw_actb EX sv) (proj1_sig a) acts.
Proof.
  induction acts as [|act acts IH]; intros Hsupport a; [reflexivity|].
  change (proj1_sig (finite_clamp EX (skel_universe EX sv prog)
    (skel_raw_actb EX sv act (proj1_sig (fold_right (skel_actb EX sv prog) a acts)))) =
    skel_raw_actb EX sv act (fold_right (skel_raw_actb EX sv) (proj1_sig a) acts)).
  rewrite structured_clamp_identity.
  - rewrite IH; [reflexivity|].
    intros action x Haction Hx; eapply Hsupport; [right; exact Haction|exact Hx].
  - apply skel_raw_actb_within; intros x Hx.
    eapply Hsupport; [left; reflexivity|exact Hx].
Qed.

Local Lemma structured_raw_post {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (sigma : skel_point -> skel_set EX sv prog) :
  post_solution (skel_lattice EX sv prog) (structured_liveness_system EX sv prog) sigma ->
  post_solution (powerset_lattice EX)
    (skeleton_backward prog (fun n => FinSet.of_list EX (skel_exit_uses sv prog n))
      (skel_raw_actb EX sv)) (fun n => proj1_sig (sigma n)).
Proof.
  intro Hpost; apply backward_post_solution_iff in Hpost as [Hseed Hflow].
  apply backward_post_solution_iff; split.
  - intros n Hn; specialize (Hseed n Hn).
    change (FinSet.subset EX (proj1_sig (finite_clamp EX (skel_universe EX sv prog)
      (FinSet.of_list EX (skel_exit_uses sv prog n)))) (proj1_sig (sigma n)) = true) in Hseed.
    rewrite structured_clamp_identity in Hseed; [exact Hseed|].
    split; [apply structured_list_wf|intros x Hx; apply FinSet.of_list_spec in Hx;
      eapply skel_universe_exit; eassumption].
  - intros e He; specialize (Hflow e He).
    change (FinSet.subset EX (proj1_sig (edge_bwd prog (skel_actb EX sv prog) e
      (sigma (skel_to prog e)))) (proj1_sig (sigma (from e))) = true) in Hflow.
    rewrite edge_bwd_agrees, skel_fold_projection in Hflow.
    + exact Hflow.
    + intros act x Hact Hx; eapply skel_universe_action; eassumption.
Qed.

(** Agreement on structured live inputs preserves all skeleton-machine behaviours. *)
Theorem structured_liveness_sound {A G St O X Cv} (EX : encoding X)
    (C : skeleton_client A G St O) (sv : skel_vars A G X) (look : St -> X -> Cv)
    (prog : stmt A G) (sigma : skel_point -> skel_set EX sv prog) (s0 t0 : mstate St) :
  skeleton_client_laws C -> skel_vars_laws C sv look ->
  post_solution (skel_lattice EX sv prog) (structured_liveness_system EX sv prog) sigma ->
  initial (skeleton_semantics prog C) s0 -> initial (skeleton_semantics prog C) t0 ->
  (forall x, fmem EX x (sigma (PEntry nil)) = true ->
    look (store_of s0) x = look (store_of t0) x) ->
  same_behaviour (skeleton_semantics prog C) (skeleton_endings prog C) s0
    (skeleton_semantics prog C) (skeleton_endings prog C) t0.
Proof.
  intros Hclient Hvars Hpost Hs Ht Hagree.
  eapply bisimilar_same_behaviour.
  - eapply (skeleton_agreement_bisimulation (powerset_lattice EX) (skel_raw_agreement EX look)
      prog C (fun n => FinSet.of_list EX (skel_exit_uses sv prog n)) (skel_raw_actb EX sv)
      (fun n => proj1_sig (sigma n))).
    + apply skel_raw_agreement_laws.
    + intros a s t Hst x Hx; symmetry; apply Hst; exact Hx.
    + apply skel_raw_action_match; assumption.
    + apply skel_raw_exit_match; exact Hvars.
    + apply structured_raw_post; exact Hpost.
  - unfold agreeing; split.
    + destruct Hs as [s [-> Hs]], Ht as [t [-> Ht]]; reflexivity.
    + split; [apply (inv_initial (reachable_invariant _)); exact Hs|].
      split; [apply (inv_initial (reachable_invariant _)); exact Ht|].
      destruct Hs as [s [-> Hs]]; exact Hagree.
Qed.

(** Every accepted replay order visits each skeleton point exactly once. *)
Theorem certificate_expand_covers {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (cert : certificate EX sv prog) order values :
  certificate_expand EX sv prog cert = Some (order, values) ->
  NoDup order /\ forall n, In n (Graph.nodes (skeleton_graph prog)) -> In n order.
Proof.
  unfold certificate_expand.
  destruct (list_eq_dec skel_point_eq_dec (map fst cert) (loop_heads prog)) as [Hkeys|];
    [|discriminate]; cbn zeta.
  destruct (plan_of skel_point_encoding (structured_liveness_system EX sv prog)
    (structured_liveness_static EX sv prog) (structured_liveness_index EX sv prog)
    (FinSet.of_list skel_point_encoding (loop_heads prog))) as [schedule|] eqn:Hplan;
    [|discriminate].
  destruct (expand skel_point_encoding (skel_lattice EX sv prog)
    (structured_liveness_system EX sv prog) (structured_liveness_static EX sv prog)
    (structured_liveness_index EX sv prog)
    (CutCertificate (FinSet.of_list skel_point_encoding (loop_heads prog))
      (Map.of_list skel_point_encoding cert) schedule)) as [result|] eqn:Hexpand;
    [|discriminate].
  intro Hresult; injection Hresult as <- <-.
  destruct (expand_accepted skel_point_encoding (skel_lattice EX sv prog)
    (structured_liveness_system EX sv prog) (structured_liveness_static EX sv prog)
    (structured_liveness_index EX sv prog) _ result Hexpand)
    as [covered [Hprepare [Hcoverage _]]].
  destruct (cut_prepare_sound skel_point_encoding _ _ _ Hprepare)
    as [Hnodup [Hdisjoint Hcovered]].
  cbn [plan cuts] in Hnodup, Hdisjoint, Hcovered.
  split.
  - apply NoDup_app.
    + apply loop_head_list_nodup.
    + exact Hnodup.
    + intros n Hhead Hschedule.
      apply (proj2 (FinSet.of_list_spec skel_point_encoding n _)) in Hhead.
      rewrite (Hdisjoint n Hschedule) in Hhead; discriminate.
  - intros n Hn; apply in_or_app.
    assert (Hseed : In (Seed n) (System.constraints (structured_liveness_system EX sv prog))).
    { apply in_or_app; left; apply in_map; exact Hn. }
    pose proof (proj1 (cut_coverage_spec skel_point_encoding
      (structured_liveness_system EX sv prog) (structured_liveness_static EX sv prog) covered)
      Hcoverage (Seed n) Hseed n (or_introl eq_refl)) as Hpresent.
    apply Hcovered in Hpresent as [Hcut|Hschedule]; [left|now right].
    exact (proj1 (FinSet.of_list_spec skel_point_encoding n _) Hcut).
Qed.

(** The observer sees exactly the point/fact pairs of the accepted expanded assignment. *)
Theorem replay_live_expanded {A G X Ob} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) (cert : certificate EX sv prog)
    (obs : Ob -> skel_point -> skel_set EX sv prog -> Ob) z order values :
  certificate_expand EX sv prog cert = Some (order, values) ->
  replay_live EX sv prog cert obs z = Some
    (replay obs z order (lookup skel_point_encoding (skel_lattice EX sv prog) values)).
Proof.
  intro Hexpand; unfold replay_live; rewrite Hexpand; reflexivity.
Qed.
