(** * Dataflow analyses as stratified rules

    These programs extract graph facts once and compute liveness, neededness and reaching
    definitions with the Rules engine. For example, a use on either arm of a branch makes its
    variable live at the branch, unless a preceding edge defines it.
    Builds on: AnalysesLiveness, AnalysesDemand and RulesSolve. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset OrderPointwise OrderBasic.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast.
From Gaulois.Views Require Import ViewsGraph ViewsForward ViewsSsaPoints.
From Gaulois.Rules Require Import RulesSyntax RulesStratify RulesModel RulesSolve.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesDemand.
Import List.ListNotations.

(** The six input predicates and three derived predicates have disjoint codes. *)
Inductive pred : Type :=
  | PUse
  | PDef
  | PSucc
  | PNec
  | PDep
  | PExitUse
  | PLive
  | PNeeded
  | PReaches.

(** Predicate codes follow constructor order, beginning at one. *)
Definition pred_encoding : encoding pred.
Proof.
  refine (Encoding pred (fun p => match p with
    | PUse => 1
    | PDef => 2
    | PSucc => 3
    | PNec => 4
    | PDep => 5
    | PExitUse => 6
    | PLive => 7
    | PNeeded => 8
    | PReaches => 9
    end)%positive _).
  intros p q; destruct p, q; congruence.
Defined.

(** Every predicate has its fixed binary or ternary arity. *)
Definition pred_arity (p : pred) : nat :=
  match p with
  | PUse | PDef | PNec | PExitUse | PLive | PNeeded => 2
  | PSucc | PDep | PReaches => 3
  end.

(** A binary tuple encodes each argument with its own dictionary. *)
Definition args2 {A B} (EA : encoding A) (EB : encoding B) (a : A) (b : B) :
    list positive := [encode EA a; encode EB b].

(** A ternary tuple preserves argument order across its three dictionaries. *)
Definition args3 {A B C} (EA : encoding A) (EB : encoding B) (EC : encoding C)
    (a : A) (b : B) (c : C) : list positive := [encode EA a; encode EB b; encode EC c].

Local Definition succ_facts {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :=
  flat_map (fun n => map (fun e => (PSucc, args3 EN EE EN n e (Graph.target g e)))
    (Graph.out g n)) (Graph.nodes g).

(** Extraction visits listed edges for uses/definitions and listed nodes for successors/exits. *)
Definition extract_live_facts {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) : list (ground_atom pred) :=
  let g := cfg (gview vv) in
  flat_map (fun e => map (fun x => (PUse, args2 EE EX e x)) (uses vv e) ++
    map (fun x => (PDef, args2 EE EX e x)) (defs vv e)) (edges_of g) ++
  succ_facts EN EE g ++
  flat_map (fun n => map (fun x => (PExitUse, args2 EN EX n x)) (exit_uses vv n))
    (Graph.nodes g).

(** Neededness extraction keeps exactly true forced, backward and exit demands. *)
Definition extract_needed_facts {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (dv : demand_view S O N E X Cv bool) : list (ground_atom pred) :=
  let g := cfg (dgraph dv) in
  flat_map (fun e =>
    map (fun x => (PDef, args2 EE EX e x)) (ddefs dv e) ++
    map (fun xm => (PNec, args2 EE EX e (fst xm))) (filter snd (dnec dv e)) ++
    flat_map (fun x => map (fun ym => (PDep, args3 EE EX EX e x (fst ym)))
      (filter snd (dback dv e x true))) (ddefs dv e)) (edges_of g) ++
  succ_facts EN EE g ++
  flat_map (fun n => map (fun xm => (PExitUse, args2 EN EX n (fst xm)))
    (filter snd (dexit dv n))) (Graph.nodes g).

(** Rule variables are natural-number positions. *)
Definition v (i : nat) : RulesSyntax.term := TVar i.

(** Rule atoms pair a predicate with its ordered arguments. *)
Definition atm (p : pred) (ts : list RulesSyntax.term) : RulesSyntax.atom pred := Atom p ts.

(** Uses and exit uses seed backward liveness; definitions kill its propagation. *)
Definition liveness_program : program pred :=
  Program pred_encoding pred_arity
    [Rule (atm PLive [v 0; v 1])
       [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PUse [v 2; v 1])];
     Rule (atm PLive [v 0; v 1]) [LPos (atm PExitUse [v 0; v 1])];
     Rule (atm PLive [v 0; v 1])
       [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PLive [v 3; v 1]);
        LNeg (atm PDef [v 2; v 1])]].

(** Neededness adds true backward dependencies to the backward kill/seed rules. *)
Definition neededness_program : program pred :=
  Program pred_encoding pred_arity
    [Rule (atm PNeeded [v 0; v 1])
       [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PNec [v 2; v 1])];
     Rule (atm PNeeded [v 0; v 1]) [LPos (atm PExitUse [v 0; v 1])];
     Rule (atm PNeeded [v 0; v 1])
       [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PNeeded [v 3; v 1]);
        LNeg (atm PDef [v 2; v 1])];
     Rule (atm PNeeded [v 0; v 1])
       [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PDef [v 2; v 4]);
        LPos (atm PDep [v 2; v 4; v 1]); LPos (atm PNeeded [v 3; v 4])]].

(** Definitions seed forward reaching facts; redefinitions kill old writers. *)
Definition reaching_program : program pred :=
  Program pred_encoding pred_arity
    [Rule (atm PReaches [v 0; v 1; v 2])
       [LPos (atm PDef [v 0; v 1]); LPos (atm PSucc [v 3; v 0; v 2])];
     Rule (atm PReaches [v 0; v 1; v 2])
       [LPos (atm PReaches [v 0; v 1; v 3]); LPos (atm PSucc [v 3; v 4; v 2]);
        LNeg (atm PDef [v 4; v 1])]].

(** Decode live tuples only inside the view's finite variable universe. *)
Definition live_of_db {S O N E X Cv} (EN : encoding N) (EX : encoding X)
    (vv : var_view S O N E X Cv) (db : database pred) (n : N) : live_set EX vv :=
  finite_clamp EX (var_universe EX vv)
    (FinSet.of_list EX (filter (fun x =>
      db_holds liveness_program db PLive (args2 EN EX n x)) (var_universe EX vv))).

(** Decode needed tuples as true entries in the declared finite demand carrier. *)
Definition needed_of_db {S O N E X Cv} (EN : encoding N) (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) (db : database pred) (n : N) :
    finite_map EX (dvars dv) bool :=
  finite_map_clamp EX (dvars dv)
    (Map.of_list EX (map (fun x => (x, true)) (filter (fun x =>
      db_holds neededness_program db PNeeded (args2 EN EX n x)) (dvars dv)))).

(** Decode reaching tuples in writer/variable/node order into variable/writer pairs. *)
Definition reach_of_db {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) (db : database pred) (n : N) : reach_set EX EE vv :=
  finite_clamp (pair_encoding EX EE) (reach_universe EX EE vv)
    (FinSet.of_list (pair_encoding EX EE) (filter (fun xd =>
      db_holds reaching_program db PReaches (args3 EE EX EN (snd xd) (fst xd) n))
      (reach_universe EX EE vv))).

(** * Extraction and finite program checks *)

Local Lemma pair_map_member {A B C} (p : A) (ts : C) (q : A) (f : B -> C) xs :
  In (p, ts) (map (fun x => (q, f x)) xs) <->
  p = q /\ exists x, In x xs /\ ts = f x.
Proof.
  rewrite in_map_iff; split.
  - intros [x [Heq Hin]]; injection Heq as Hp Hts; subst; eauto.
  - intros [-> [x [Hin ->]]]; exists x; auto.
Qed.

Local Lemma succ_facts_spec {N E} EN EE (g : Graph.t N E) p ts :
  In (p, ts) (succ_facts EN EE g) <-> p = PSucc /\
  exists n e, In n (Graph.nodes g) /\ In e (Graph.out g n) /\
    ts = args3 EN EE EN n e (Graph.target g e).
Proof.
  unfold succ_facts; rewrite in_flat_map; setoid_rewrite pair_map_member; firstorder.
Qed.

Local Lemma live_facts_spec {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) p ts :
  In (p, ts) (extract_live_facts EN EE EX vv) <->
  (p = PUse /\ exists e x, In e (edges_of (cfg (gview vv))) /\ In x (uses vv e) /\
    ts = args2 EE EX e x) \/
  (p = PDef /\ exists e x, In e (edges_of (cfg (gview vv))) /\ In x (defs vv e) /\
    ts = args2 EE EX e x) \/
  (p = PSucc /\ exists n e, In n (Graph.nodes (cfg (gview vv))) /\
    In e (Graph.out (cfg (gview vv)) n) /\
    ts = args3 EN EE EN n e (Graph.target (cfg (gview vv)) e)) \/
  (p = PExitUse /\ exists n x, In n (Graph.nodes (cfg (gview vv))) /\
    In x (exit_uses vv n) /\ ts = args2 EN EX n x).
Proof.
  unfold extract_live_facts; rewrite !in_app_iff, succ_facts_spec, !in_flat_map.
  setoid_rewrite in_app_iff; setoid_rewrite pair_map_member; firstorder.
Qed.

Local Lemma needed_facts_spec {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) p ts :
  In (p, ts) (extract_needed_facts EN EE EX dv) <->
  (p = PDef /\ exists e x, In e (edges_of (cfg (dgraph dv))) /\ In x (ddefs dv e) /\
    ts = args2 EE EX e x) \/
  (p = PNec /\ exists e x, In e (edges_of (cfg (dgraph dv))) /\
    In (x, true) (dnec dv e) /\ ts = args2 EE EX e x) \/
  (p = PDep /\ exists e x y, In e (edges_of (cfg (dgraph dv))) /\ In x (ddefs dv e) /\
    In (y, true) (dback dv e x true) /\ ts = args3 EE EX EX e x y) \/
  (p = PSucc /\ exists n e, In n (Graph.nodes (cfg (dgraph dv))) /\
    In e (Graph.out (cfg (dgraph dv)) n) /\
    ts = args3 EN EE EN n e (Graph.target (cfg (dgraph dv)) e)) \/
  (p = PExitUse /\ exists n x, In n (Graph.nodes (cfg (dgraph dv))) /\
    In (x, true) (dexit dv n) /\ ts = args2 EN EX n x).
Proof.
  unfold extract_needed_facts; rewrite !in_app_iff, succ_facts_spec, !in_flat_map.
  repeat setoid_rewrite in_app_iff; repeat setoid_rewrite in_flat_map.
  repeat setoid_rewrite pair_map_member.
  split.
  - intros [Hedge|[Hsucc|Hexit]].
    + destruct Hedge as [e [He [Hdef|[Hnec|Hdep]]]].
      * left; destruct Hdef as [-> [x [Hx ->]]]; split; [reflexivity|].
        exists e, x; auto.
      * right; left; destruct Hnec as [-> [[x b] [Hxm ->]]].
        apply filter_In in Hxm; cbn in Hxm; destruct Hxm as [Hx ->]; cbn.
        split; [reflexivity|]; exists e, x; auto.
      * right; right; left; destruct Hdep as [x [Hx [-> [[y b] [Hym ->]]]]].
        apply filter_In in Hym; cbn in Hym; destruct Hym as [Hy ->]; cbn.
        split; [reflexivity|]; exists e, x, y; auto.
    + right; right; right; left; exact Hsucc.
    + right; right; right; right; destruct Hexit as [n [Hn [-> [[x b] [Hxm ->]]]]].
      apply filter_In in Hxm; cbn in Hxm; destruct Hxm as [Hx ->]; cbn.
      split; [reflexivity|]; exists n, x; auto.
  - intros [[-> [e [x [He [Hx ->]]]]]|[[-> [e [x [He [Hx ->]]]]]|
      [[-> [e [x [y [He [Hx [Hy ->]]]]]]]|[Hsucc|[-> [n [x [Hn [Hx ->]]]]]]]]].
    + left; exists e; split; [exact He|left; eauto].
    + left; exists e; split; [exact He|right; left]; split; [reflexivity|].
      exists (x, true); split; [apply filter_In; auto|reflexivity].
    + left; exists e; split; [exact He|right; right]; exists x; split; [exact Hx|].
      split; [reflexivity|]; exists (y, true); split; [apply filter_In; auto|reflexivity].
    + right; left; exact Hsucc.
    + right; right; exists n; split; [exact Hn|]; split; [reflexivity|].
      exists (x, true); split; [apply filter_In; auto|reflexivity].
Qed.

Local Definition analysis_strata : stratification pred :=
  Stratification (fun p => match p with PLive | PNeeded | PReaches => 1 | _ => 0 end) 2.

(* Finite program checks split only the explicitly listed rules and literals. *)
Local Ltac split_members :=
  repeat match goal with
  | H : False |- _ => contradiction
  | H : _ \/ _ |- _ => destruct H as [H|H]
  | H : _ = _ |- _ => first [discriminate H | progress subst |
      injection H; clear H; intros; subst]
  end.

Local Lemma analysis_programs_stratified :
  stratified liveness_program analysis_strata /\
  stratified neededness_program analysis_strata /\
  stratified reaching_program analysis_strata.
Proof.
  repeat split; try (intro p; destruct p; cbn; lia);
    intros r l Hr Hl; cbn in Hr; split_members; cbn in Hl; split_members; cbn; lia.
Qed.

(* Safety witnesses are positive literals already present in the rule body. *)
Local Ltac positive_witness ls :=
  lazymatch ls with
  | LPos ?a :: ?rest =>
    first [solve [exists a; split; cbn; tauto] | positive_witness rest]
  | _ :: ?rest => positive_witness rest
  end.

Local Ltac check_safe :=
  unfold safe_rule; intros i Hi; cbn in Hi;
  destruct Hi as [Hi|[a [Ha Hi]]];
  [split_members|split_members; cbn in Hi; split_members];
  match goal with
  | |- exists a, In (LPos a) ?ls /\ _ =>
    let literals := eval cbn in ls in positive_witness literals
  end.

Local Lemma analysis_programs_rules_wf :
  (forall r, In r (rules liveness_program) -> safe_rule r /\
    length (args (head r)) = pred_arity (RulesSyntax.pred (head r)) /\
    forall l, In l (body r) ->
      length (args (lit_atom l)) = pred_arity (RulesSyntax.pred (lit_atom l))) /\
  (forall r, In r (rules neededness_program) -> safe_rule r /\
    length (args (head r)) = pred_arity (RulesSyntax.pred (head r)) /\
    forall l, In l (body r) ->
      length (args (lit_atom l)) = pred_arity (RulesSyntax.pred (lit_atom l))) /\
  (forall r, In r (rules reaching_program) -> safe_rule r /\
    length (args (head r)) = pred_arity (RulesSyntax.pred (head r)) /\
    forall l, In l (body r) ->
      length (args (lit_atom l)) = pred_arity (RulesSyntax.pred (lit_atom l))).
Proof.
  split; [|split]; intros r Hr; cbn in Hr; split_members.
  all: split; [check_safe|split; [reflexivity|intros l Hl; cbn in Hl;
    split_members; reflexivity]].
Qed.

Local Lemma live_facts_arity {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) :
  forall f, In f (extract_live_facts EN EE EX vv) -> length (snd f) = pred_arity (fst f).
Proof.
  intros [p ts] Hin; apply live_facts_spec in Hin.
  destruct Hin as [[-> [e [x [_ [_ ->]]]]]|[[-> [e [x [_ [_ ->]]]]]|
    [[-> [n [e [_ [_ ->]]]]]|[-> [n [x [_ [_ ->]]]]]]]]; reflexivity.
Qed.

Local Lemma needed_facts_arity {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) :
  forall f, In f (extract_needed_facts EN EE EX dv) -> length (snd f) = pred_arity (fst f).
Proof.
  intros [p ts] Hin; apply needed_facts_spec in Hin.
  destruct Hin as [[-> [e [x [_ [_ ->]]]]]|[[-> [e [x [_ [_ ->]]]]]|
    [[-> [e [x [y [_ [_ [_ ->]]]]]]]|[[-> [n [e [_ [_ ->]]]]]|[-> [n [x [_ [_ ->]]]]]]]]];
    reflexivity.
Qed.

(** * Reasoning about the actual stratified model *)

(* This induction retains negative input tests, rather than turning the program into a
   monotone system that could enlarge its extensional definition relation. *)
Local Lemma model_induction (prog : program pred) facts (I : ground_atom pred -> Prop) :
  (exists st, stratified prog st) ->
  (forall f, In f facts -> I f) ->
  (forall r sigma, In r (rules prog) ->
    (forall a, In (LPos a) (body r) -> I (ground sigma a)) ->
    (forall a, In (LNeg a) (body r) -> ~ In (ground sigma a) facts) ->
    I (ground sigma (head r))) ->
  forall f, least_model prog facts f -> I f.
Proof.
  intros Hstrat Hfacts Hrules.
  destruct (stratify_complete prog Hstrat) as [st Hst].
  pose proof (stratify_sound prog st Hst) as Hvalid.
  unfold least_model; rewrite Hst; unfold perfect_model.
  assert (Hbelow : forall n f, model_below prog facts st n f -> I f).
  { intro n; induction n as [|n IH]; intros f Hmodel; [contradiction|].
    destruct Hmodel as [Hlow|Hderive]; [exact (IH f Hlow)|].
    induction Hderive as [f Hfact Hlevel|r sigma Hr Hlevel Hlow Hsame IHsame Hneg].
    - apply Hfacts; exact Hfact.
    - apply Hrules; [exact Hr| |].
      + intros a Ha.
        pose proof (proj2 Hvalid r (LPos a) Hr Ha) as Hle; cbn in Hle.
        destruct (Nat.eq_dec (level st (RulesSyntax.pred a)) n) as [Heq|Hne].
        * apply IHsame; assumption.
        * apply IH, Hlow; [exact Ha|lia].
      + intros a Ha Hfact; apply (Hneg a Ha).
        pose proof (proj2 Hvalid r (LNeg a) Hr Ha) as Hlt; cbn in Hlt.
        apply (proj2 (model_below_stage prog facts st n (ground sigma a) ltac:(cbn; lia))).
        apply derive_fact; [exact Hfact|reflexivity]. }
  apply Hbelow.
Qed.

Local Lemma model_input (prog : program pred) facts p ts :
  (exists st, stratified prog st) ->
  (forall r, In r (rules prog) -> RulesSyntax.pred (head r) <> p) ->
  (least_model prog facts (p, ts) <-> In (p, ts) facts).
Proof.
  intros Hstrat Hhead; split.
  - intro Hmodel.
    refine (model_induction prog facts (fun f => fst f = p -> In f facts)
      Hstrat _ _ (p, ts) Hmodel eq_refl).
    + intros f Hf _; exact Hf.
    + intros r sigma Hr _ _ Heq; cbn in Heq; exfalso; exact (Hhead r Hr Heq).
  - intro Hfact; destruct (stratify_complete prog Hstrat) as [st Hst].
    exact (proj1 (least_model_closed prog facts st (Rule (Atom p []) []) Hst) _ Hfact).
Qed.

Local Lemma solver_model (prog : program pred) facts db :
  program_wf prog facts -> (exists st, stratified prog st) ->
  solve_program prog facts = Some db ->
  forall p ts, db_holds prog db p ts = true <-> least_model prog facts (p, ts).
Proof.
  intros Hwf Hstrat Hsolve.
  destruct (solve_program_exact prog facts Hwf Hstrat) as [db' [Hsolve' Hmodel]].
  rewrite Hsolve in Hsolve'; injection Hsolve' as ->; exact (proj2 Hmodel).
Qed.

(* Model proofs use its induction/closure interface. Keeping this definition locally opaque
   prevents unification from evaluating stratification while searching unrelated list facts. *)
Local Opaque least_model.

(** The finite liveness program always stratifies and solves on extracted graph facts. *)
Theorem rules_liveness_solves {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) :
  graph_wf (cfg (gview vv)) ->
  exists db, solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db.
Proof.
  intro Hwf; destruct (solve_program_exact liveness_program (extract_live_facts EN EE EX vv))
    as [db [Hsolve Hmodel]].
  - split; [exact (proj1 analysis_programs_rules_wf)|apply live_facts_arity].
  - exists analysis_strata; exact (proj1 analysis_programs_stratified).
  - exists db; exact Hsolve.
Qed.

(** The finite neededness program succeeds independently of backward-demand strictness. *)
Theorem rules_neededness_solves {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (dv : demand_view S O N E X Cv bool) :
  graph_wf (cfg (dgraph dv)) ->
  exists db, solve_program neededness_program (extract_needed_facts EN EE EX dv) = Some db.
Proof.
  intro Hwf; destruct (solve_program_exact neededness_program (extract_needed_facts EN EE EX dv))
    as [db [Hsolve Hmodel]].
  - split; [exact (proj1 (proj2 analysis_programs_rules_wf))|apply needed_facts_arity].
  - exists analysis_strata; exact (proj1 (proj2 analysis_programs_stratified)).
  - exists db; exact Hsolve.
Qed.

(** The reaching program uses the same finite graph facts and succeeds. *)
Theorem rules_reaching_solves {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) :
  graph_wf (cfg (gview vv)) ->
  exists db, solve_program reaching_program (extract_live_facts EN EE EX vv) = Some db.
Proof.
  intro Hwf; destruct (solve_program_exact reaching_program (extract_live_facts EN EE EX vv))
    as [db [Hsolve Hmodel]].
  - split; [exact (proj2 (proj2 analysis_programs_rules_wf))|apply live_facts_arity].
  - exists analysis_strata; exact (proj2 (proj2 analysis_programs_stratified)).
  - exists db; exact Hsolve.
Qed.

Local Lemma live_use_input {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) ts :
  In (PUse, ts) (extract_live_facts EN EE EX vv) <->
  exists e x, In e (edges_of (cfg (gview vv))) /\ In x (uses vv e) /\ ts = args2 EE EX e x.
Proof.
  rewrite live_facts_spec; intuition discriminate.
Qed.

Local Lemma live_def_input {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) ts :
  In (PDef, ts) (extract_live_facts EN EE EX vv) <->
  exists e x, In e (edges_of (cfg (gview vv))) /\ In x (defs vv e) /\ ts = args2 EE EX e x.
Proof.
  rewrite live_facts_spec; intuition discriminate.
Qed.

Local Lemma live_succ_input {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) ts :
  In (PSucc, ts) (extract_live_facts EN EE EX vv) <->
  exists n e, In n (Graph.nodes (cfg (gview vv))) /\ In e (Graph.out (cfg (gview vv)) n) /\
    ts = args3 EN EE EN n e (Graph.target (cfg (gview vv)) e).
Proof.
  rewrite live_facts_spec; intuition discriminate.
Qed.

Local Lemma live_exit_input {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) ts :
  In (PExitUse, ts) (extract_live_facts EN EE EX vv) <->
  exists n x, In n (Graph.nodes (cfg (gview vv))) /\ In x (exit_uses vv n) /\
    ts = args2 EN EX n x.
Proof.
  rewrite live_facts_spec; intuition discriminate.
Qed.

Local Definition live_interpret {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv)
    (R : N -> X -> Prop) (f : ground_atom pred) : Prop :=
  match fst f with
  | PLive => exists n x, snd f = args2 EN EX n x /\ R n x
  | _ => In f (extract_live_facts EN EE EX vv)
  end.

Local Lemma live_model_induction {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv)
    (R : N -> X -> Prop) :
  (forall n x, In n (Graph.nodes (cfg (gview vv))) -> In x (exit_uses vv n) -> R n x) ->
  (forall n e x, In n (Graph.nodes (cfg (gview vv))) ->
    In e (Graph.out (cfg (gview vv)) n) -> In x (uses vv e) -> R n x) ->
  (forall n e x, In n (Graph.nodes (cfg (gview vv))) ->
    In e (Graph.out (cfg (gview vv)) n) -> R (Graph.target (cfg (gview vv)) e) x ->
    ~ In x (defs vv e) -> R n x) ->
  forall ts, least_model liveness_program (extract_live_facts EN EE EX vv) (PLive, ts) ->
    exists n x, ts = args2 EN EX n x /\ R n x.
Proof.
  intros Hexit Huse Hflow ts Hmodel.
  refine (model_induction liveness_program (extract_live_facts EN EE EX vv)
    (live_interpret EN EE EX vv R) _ _ _ (PLive, ts) Hmodel).
  - exists analysis_strata; exact (proj1 analysis_programs_stratified).
  - intros [p us] Hfact; destruct p; try exact Hfact.
    apply live_facts_spec in Hfact; intuition discriminate.
  - intros r sigma Hr Hpos Hneg; cbn in Hr.
    destruct Hr as [<-|[<-|[<-|Hr]]]; [| | |contradiction].
    + pose proof (Hpos (atm PSucc [v 0; v 2; v 3]) (or_introl eq_refl)) as Hsucc.
      pose proof (Hpos (atm PUse [v 2; v 1]) (or_intror (or_introl eq_refl))) as Hread.
      cbn [live_interpret ground atm v inst head fst snd] in Hsucc, Hread |- *.
      apply live_succ_input in Hsucc; apply live_use_input in Hread.
      destruct Hsucc as [n [e [Hn [He Hcodes]]]].
      destruct Hread as [e' [x [He' [Hx Hread]]]].
      unfold args2, args3 in *; injection Hcodes as Hncode Hecode Htcode.
      injection Hread as Hecode' Hxcode.
      assert (e' = e) by (apply (encode_injective EE); congruence); subst e'.
      exists n, x; split.
      * change ([sigma 0; sigma 1] = [encode EN n; encode EX x]); congruence.
      * exact (Huse n e x Hn He Hx).
    + pose proof (Hpos (atm PExitUse [v 0; v 1]) (or_introl eq_refl)) as Hseed.
      cbn [live_interpret ground atm v inst head fst snd] in Hseed |- *.
      apply live_exit_input in Hseed; destruct Hseed as [n [x [Hn [Hx Hcodes]]]].
      exists n, x; split; [exact Hcodes|exact (Hexit n x Hn Hx)].
    + pose proof (Hpos (atm PSucc [v 0; v 2; v 3]) (or_introl eq_refl)) as Hsucc.
      pose proof (Hpos (atm PLive [v 3; v 1]) (or_intror (or_introl eq_refl))) as Hlive.
      pose proof (Hneg (atm PDef [v 2; v 1]) (or_intror (or_intror (or_introl eq_refl))))
        as Hkill.
      cbn [live_interpret ground atm v inst head fst snd] in Hsucc, Hlive, Hkill |- *.
      apply live_succ_input in Hsucc; destruct Hsucc as [n [e [Hn [He Hcodes]]]].
      destruct Hlive as [t [x [Hlive HR]]].
      unfold args2, args3 in *; injection Hcodes as Hncode Hecode Htcode.
      injection Hlive as Htcode' Hxcode.
      assert (t = Graph.target (cfg (gview vv)) e)
        by (apply (encode_injective EN); congruence); subst t.
      exists n, x; split.
      * change ([sigma 0; sigma 1] = [encode EN n; encode EX x]); congruence.
      *
      eapply Hflow; [exact Hn|exact He|exact HR|].
      intro Hdef; apply Hkill, live_def_input; exists e, x.
      split; [unfold edges_of; apply in_flat_map; exists n; split; assumption|].
      split; [exact Hdef|].
      change ([sigma 2; sigma 1] = [encode EE e; encode EX x]); congruence.
Qed.

Local Definition valuation (a b c d e : positive) (i : nat) : positive :=
  nth i [a; b; c; d; e] 1%positive.

Local Lemma model_fire (prog : program pred) facts r sigma :
  (exists st, stratified prog st) -> In r (rules prog) ->
  (forall a, In (LPos a) (body r) -> least_model prog facts (ground sigma a)) ->
  (forall a, In (LNeg a) (body r) -> ~ least_model prog facts (ground sigma a)) ->
  least_model prog facts (ground sigma (head r)).
Proof.
  intros Hstrat Hr Hpos Hneg; destruct (stratify_complete prog Hstrat) as [st Hst].
  exact (proj2 (least_model_closed prog facts st r Hst) sigma Hr Hpos Hneg).
Qed.

Local Lemma live_base_model {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) p ts :
  p <> PLive ->
  (least_model liveness_program (extract_live_facts EN EE EX vv) (p, ts) <->
    In (p, ts) (extract_live_facts EN EE EX vv)).
Proof.
  intro Hne; apply model_input.
  - exists analysis_strata; exact (proj1 analysis_programs_stratified).
  - intros r Hr; cbn in Hr; split_members; cbn; congruence.
Qed.

Local Lemma live_model_seed {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) n x :
  In n (Graph.nodes (cfg (gview vv))) -> In x (exit_uses vv n) ->
  least_model liveness_program (extract_live_facts EN EE EX vv) (PLive, args2 EN EX n x).
Proof.
  intros Hn Hx.
  change (least_model liveness_program (extract_live_facts EN EE EX vv)
    (ground (valuation (encode EN n) (encode EX x) 1 1 1)
      (head (nth 1 (rules liveness_program) (Rule (atm PLive []) []))))).
  apply (model_fire liveness_program (extract_live_facts EN EE EX vv)
    (nth 1 (rules liveness_program) (Rule (atm PLive []) []))
    (valuation (encode EN n) (encode EX x) 1 1 1)).
  - exists analysis_strata; exact (proj1 analysis_programs_stratified).
  - cbn; auto.
  - intros a Ha; cbn in Ha; split_members;
    cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
    apply (proj2 (live_base_model EN EE EX vv PExitUse _ ltac:(discriminate)));
    apply live_exit_input; eauto.
  - intros a Ha; cbn in Ha; split_members.
Qed.

Local Lemma live_model_use {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) n e x :
  In n (Graph.nodes (cfg (gview vv))) -> In e (Graph.out (cfg (gview vv)) n) ->
  In x (uses vv e) ->
  least_model liveness_program (extract_live_facts EN EE EX vv) (PLive, args2 EN EX n x).
Proof.
  intros Hn He Hx.
  change (least_model liveness_program (extract_live_facts EN EE EX vv)
    (ground (valuation (encode EN n) (encode EX x) (encode EE e)
      (encode EN (Graph.target (cfg (gview vv)) e)) 1)
      (head (nth 0 (rules liveness_program) (Rule (atm PLive []) []))))).
  apply (model_fire liveness_program (extract_live_facts EN EE EX vv)
    (nth 0 (rules liveness_program) (Rule (atm PLive []) []))
    (valuation (encode EN n) (encode EX x) (encode EE e)
      (encode EN (Graph.target (cfg (gview vv)) e)) 1)).
  - exists analysis_strata; exact (proj1 analysis_programs_stratified).
  - cbn; auto.
  - intros a Ha; cbn in Ha; split_members;
    cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
    + apply (proj2 (live_base_model EN EE EX vv PSucc _ ltac:(discriminate)));
      apply live_succ_input; eauto.
    + apply (proj2 (live_base_model EN EE EX vv PUse _ ltac:(discriminate))); apply live_use_input.
      exists e, x; split; [unfold edges_of; apply in_flat_map; eauto|auto].
  - intros a Ha; cbn in Ha; split_members.
Qed.

Local Lemma live_model_flow {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) n e x :
  In n (Graph.nodes (cfg (gview vv))) -> In e (Graph.out (cfg (gview vv)) n) ->
  least_model liveness_program (extract_live_facts EN EE EX vv)
    (PLive, args2 EN EX (Graph.target (cfg (gview vv)) e) x) ->
  ~ In x (defs vv e) ->
  least_model liveness_program (extract_live_facts EN EE EX vv) (PLive, args2 EN EX n x).
Proof.
  intros Hn He Hlive Hnot.
  change (least_model liveness_program (extract_live_facts EN EE EX vv)
    (ground (valuation (encode EN n) (encode EX x) (encode EE e)
      (encode EN (Graph.target (cfg (gview vv)) e)) 1)
      (head (nth 2 (rules liveness_program) (Rule (atm PLive []) []))))).
  apply (model_fire liveness_program (extract_live_facts EN EE EX vv)
    (nth 2 (rules liveness_program) (Rule (atm PLive []) []))
    (valuation (encode EN n) (encode EX x) (encode EE e)
      (encode EN (Graph.target (cfg (gview vv)) e)) 1)).
  - exists analysis_strata; exact (proj1 analysis_programs_stratified).
  - cbn; auto.
  - intros a Ha; cbn in Ha; split_members;
    cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
    + apply (proj2 (live_base_model EN EE EX vv PSucc _ ltac:(discriminate)));
      apply live_succ_input; eauto.
    + exact Hlive.
  - intros a Ha; cbn in Ha; split_members;
    cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
    change (~ least_model liveness_program (extract_live_facts EN EE EX vv)
      (PDef, args2 EE EX e x)).
    rewrite (live_base_model EN EE EX vv PDef _ ltac:(discriminate)); rewrite live_def_input.
    intros [e' [y [_ [Hy Hcodes]]]]; unfold args2 in Hcodes.
    injection Hcodes as Heq Hxy; apply (encode_injective EE) in Heq.
    apply (encode_injective EX) in Hxy; subst e' y; contradiction.
Qed.

Local Lemma live_model_support {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) n x :
  least_model liveness_program (extract_live_facts EN EE EX vv) (PLive, args2 EN EX n x) ->
  In n (Graph.nodes (cfg (gview vv))) /\ In x (var_universe EX vv).
Proof.
  intro Hmodel.
  destruct (live_model_induction EN EE EX vv
    (fun n x => In n (Graph.nodes (cfg (gview vv))) /\ In x (var_universe EX vv)))
    with (ts := args2 EN EX n x) as [n' [x' [Hcodes Hsupport]]].
  - intros t y Ht Hy; split; [exact Ht|].
    exact (proj2 (proj2 (var_universe_covers EX vv)) t y Ht Hy).
  - intros t e y Ht He Hy; split; [exact Ht|].
    apply (proj1 (proj2 (var_universe_covers EX vv)) e y).
    + unfold edges_of; apply in_flat_map; eauto.
    + apply in_or_app; now left.
  - intros t e y Ht He [_ Hy] Hkill; auto.
  - exact Hmodel.
  - unfold args2 in Hcodes; injection Hcodes as Hn Hx.
    apply (encode_injective EN) in Hn; apply (encode_injective EX) in Hx.
    now subst n' x'.
Qed.

Local Lemma clamp_members {K} (EK : encoding K) U raw x :
  fmem EK x (finite_clamp EK U raw) = true <-> In x U /\ FinSet.mem EK x raw = true.
Proof.
  change (FinSet.mem EK x (FinSet.of_list EK (filter (fun y => FinSet.mem EK y raw) U)) = true
    <-> In x U /\ FinSet.mem EK x raw = true).
  rewrite FinSet.of_list_spec, filter_In; reflexivity.
Qed.

Local Lemma live_decode {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) db :
  solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db ->
  forall n x, fmem EX x (live_of_db EN EX vv db n) = true <->
    least_model liveness_program (extract_live_facts EN EE EX vv) (PLive, args2 EN EX n x).
Proof.
  intro Hsolve.
  assert (Hmodel : forall p ts, db_holds liveness_program db p ts = true <->
    least_model liveness_program (extract_live_facts EN EE EX vv) (p, ts)).
  { apply solver_model; [split; [exact (proj1 analysis_programs_rules_wf)|
      apply live_facts_arity]| |exact Hsolve].
    exists analysis_strata; exact (proj1 analysis_programs_stratified). }
  intros n x; unfold live_of_db; rewrite clamp_members, FinSet.of_list_spec, filter_In, Hmodel.
  split; [tauto|intro Hlive].
  pose proof (proj2 (live_model_support EN EE EX vv n x Hlive)); auto.
Qed.

Local Lemma finite_le {K} (EK : encoding K) U (a b : finite_set EK U) :
  leb (finite_powerset_lattice EK U) a b = true <->
  forall x, fmem EK x a = true -> fmem EK x b = true.
Proof.
  apply FinSet.subset_spec; exact (proj1 (proj2_sig a)).
Qed.

Local Lemma listed_edge {N E} (g : Graph.t N E) e :
  In e (edges_of g) -> exists n, In n (Graph.nodes g) /\ In e (Graph.out g n).
Proof.
  unfold edges_of; apply in_flat_map.
Qed.

Local Lemma live_model_post {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) db :
  graph_wf (cfg (gview vv)) ->
  solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db ->
  post_solution (live_lattice EX vv) (liveness_system EX vv) (live_of_db EN EX vv db).
Proof.
  intros Hwf Hsolve; unfold liveness_system; apply backward_post_solution_iff; split.
  - intros n Hn; apply finite_le; intros x Hx.
    apply (AnalysesLiveness.live_exit_spec EX vv n x Hn) in Hx.
    apply (live_decode EN EE EX vv db Hsolve), live_model_seed; assumption.
  - intros e He; apply finite_le; intros x Hx.
    apply (AnalysesLiveness.live_transfer_spec EX vv e _ x He) in Hx.
    destruct (listed_edge _ e He) as [n [Hn Hout]].
    rewrite (out_source Hwf n e Hout).
    apply (live_decode EN EE EX vv db Hsolve).
    destruct Hx as [[Hlive Hkill]|Huse].
    + eapply live_model_flow; [exact Hn|exact Hout| |exact Hkill].
      apply (live_decode EN EE EX vv db Hsolve); exact Hlive.
    + eapply live_model_use; eauto.
Qed.

Local Lemma live_model_below {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv)
    (sigma : N -> live_set EX vv) :
  graph_wf (cfg (gview vv)) ->
  post_solution (live_lattice EX vv) (liveness_system EX vv) sigma ->
  forall n x, least_model liveness_program (extract_live_facts EN EE EX vv)
    (PLive, args2 EN EX n x) -> fmem EX x (sigma n) = true.
Proof.
  intros Hwf Hpost n x Hmodel.
  destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
  destruct (live_model_induction EN EE EX vv (fun n x => fmem EX x (sigma n) = true))
    with (ts := args2 EN EX n x) as [n' [x' [Hcodes Hmem]]].
  - intros t y Ht Hy; apply (proj1 (finite_le _ _ _ _) (Hseed t Ht)).
    apply (AnalysesLiveness.live_exit_spec EX vv t y Ht); exact Hy.
  - intros t e y Ht He Hy.
    assert (Hedge : In e (edges_of (cfg (gview vv))))
      by (unfold edges_of; apply in_flat_map; eauto).
    rewrite <- (out_source Hwf t e He).
    apply (proj1 (finite_le _ _ _ _) (Hflow e Hedge)).
    apply (AnalysesLiveness.live_transfer_spec EX vv e _ y Hedge); now right.
  - intros t e y Ht He Hy Hkill.
    assert (Hedge : In e (edges_of (cfg (gview vv))))
      by (unfold edges_of; apply in_flat_map; eauto).
    rewrite <- (out_source Hwf t e He).
    apply (proj1 (finite_le _ _ _ _) (Hflow e Hedge)).
    apply (AnalysesLiveness.live_transfer_spec EX vv e _ y Hedge); left; auto.
  - exact Hmodel.
  - unfold args2 in Hcodes; injection Hcodes as Hn Hx.
    apply (encode_injective EN) in Hn; apply (encode_injective EX) in Hx.
    now subst n' x'.
Qed.

(** The Rules result satisfies every liveness constraint and lies below every post-solution. *)
Theorem rules_liveness_least {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db ->
  least_solution (live_lattice EX vv) (liveness_system EX vv) (live_of_db EN EX vv db).
Proof.
  intros Hwf Hsolve; split; [exact (live_model_post EN EE EX vv db Hwf Hsolve)|].
  intros sigma Hpost n; apply finite_le; intros x Hx.
  apply (live_model_below EN EE EX vv sigma Hwf Hpost).
  apply (live_decode EN EE EX vv db Hsolve); exact Hx.
Qed.

(** The declarative live relation agrees exactly with the decoded solver database. *)
Theorem rules_liveness_model {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db ->
  forall n x, holds (least_model liveness_program (extract_live_facts EN EE EX vv)) PLive
    (args2 EN EX n x) <-> fmem EX x (live_of_db EN EX vv db n) = true.
Proof.
  intros Hwf Hsolve n x; symmetry; apply (live_decode EN EE EX vv db Hsolve).
Qed.

(** The least Rules result is precisely finite-path syntactic liveness at listed nodes. *)
Theorem syntactic_live_rules {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db ->
  forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    (fmem EX x (live_of_db EN EX vv db n) = true <-> syntactic_live (var_point_uses vv) x n).
Proof.
  intros Hwf Hsolve; apply syntactic_live_least; [exact Hwf|].
  exact (rules_liveness_least EN EE EX vv db Hwf Hsolve).
Qed.

(** * Boolean neededness *)

Local Lemma needed_def_input {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) ts :
  In (PDef, ts) (extract_needed_facts EN EE EX dv) <->
  exists e x, In e (edges_of (cfg (dgraph dv))) /\ In x (ddefs dv e) /\ ts = args2 EE EX e x.
Proof.
  rewrite needed_facts_spec; intuition discriminate.
Qed.

Local Lemma needed_nec_input {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) ts :
  In (PNec, ts) (extract_needed_facts EN EE EX dv) <->
  exists e x, In e (edges_of (cfg (dgraph dv))) /\ In (x, true) (dnec dv e) /\
    ts = args2 EE EX e x.
Proof.
  rewrite needed_facts_spec; intuition discriminate.
Qed.

Local Lemma needed_dep_input {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) ts :
  In (PDep, ts) (extract_needed_facts EN EE EX dv) <->
  exists e x y, In e (edges_of (cfg (dgraph dv))) /\ In x (ddefs dv e) /\
    In (y, true) (dback dv e x true) /\ ts = args3 EE EX EX e x y.
Proof.
  rewrite needed_facts_spec; intuition discriminate.
Qed.

Local Lemma needed_succ_input {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) ts :
  In (PSucc, ts) (extract_needed_facts EN EE EX dv) <->
  exists n e, In n (Graph.nodes (cfg (dgraph dv))) /\ In e (Graph.out (cfg (dgraph dv)) n) /\
    ts = args3 EN EE EN n e (Graph.target (cfg (dgraph dv)) e).
Proof.
  rewrite needed_facts_spec; intuition discriminate.
Qed.

Local Lemma needed_exit_input {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) ts :
  In (PExitUse, ts) (extract_needed_facts EN EE EX dv) <->
  exists n x, In n (Graph.nodes (cfg (dgraph dv))) /\ In (x, true) (dexit dv n) /\
    ts = args2 EN EX n x.
Proof.
  rewrite needed_facts_spec; intuition discriminate.
Qed.

Local Definition needed_interpret {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) (R : N -> X -> Prop) (f : ground_atom pred) : Prop :=
  match fst f with
  | PNeeded => exists n x, snd f = args2 EN EX n x /\ R n x
  | _ => In f (extract_needed_facts EN EE EX dv)
  end.

Local Lemma needed_dependency_interpret {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) (R : N -> X -> Prop) sigma :
  (forall n e x y, In n (Graph.nodes (cfg (dgraph dv))) ->
    In e (Graph.out (cfg (dgraph dv)) n) -> In x (ddefs dv e) ->
    In (y, true) (dback dv e x true) -> R (Graph.target (cfg (dgraph dv)) e) x -> R n y) ->
  (forall a, In (LPos a)
    (body (nth 3 (rules neededness_program) (Rule (atm PNeeded []) []))) ->
    needed_interpret EN EE EX dv R (ground sigma a)) ->
  needed_interpret EN EE EX dv R
    (ground sigma (head (nth 3 (rules neededness_program) (Rule (atm PNeeded []) [])))).
Proof.
  intros Hdep Hpos.
  pose proof (Hpos (atm PSucc [v 0; v 2; v 3]) (or_introl eq_refl)) as Hsucc.
  pose proof (Hpos (atm PDep [v 2; v 4; v 1])
    (or_intror (or_intror (or_introl eq_refl)))) as Hback.
  pose proof (Hpos (atm PNeeded [v 3; v 4])
    (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Hneed.
  cbn [needed_interpret ground atm v inst head fst snd] in Hsucc, Hback, Hneed |- *.
  apply needed_succ_input in Hsucc; apply needed_dep_input in Hback.
  destruct Hsucc as [n [e [Hn [He Hcodes]]]].
  destruct Hback as [e' [x [y [_ [Hx [Hy Hback]]]]]].
  destruct Hneed as [t [x' [Hneed HR]]].
  unfold args2, args3 in *; injection Hcodes as Hnc Hec Htc.
  injection Hback as Hec' Hxc Hyc; injection Hneed as Htc' Hxc'.
  assert (e' = e) by (apply (encode_injective EE); congruence).
  assert (x' = x) by (apply (encode_injective EX); congruence).
  assert (t = Graph.target (cfg (dgraph dv)) e)
    by (apply (encode_injective EN); congruence); subst e' x' t.
  exists n, y; split.
  - change ([sigma 0; sigma 1] = [encode EN n; encode EX y]); congruence.
  - exact (Hdep n e x y Hn He Hx Hy HR).
Qed.

Local Lemma needed_model_induction {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) (R : N -> X -> Prop) :
  (forall n x, In n (Graph.nodes (cfg (dgraph dv))) -> In (x, true) (dexit dv n) -> R n x) ->
  (forall n e x, In n (Graph.nodes (cfg (dgraph dv))) ->
    In e (Graph.out (cfg (dgraph dv)) n) -> In (x, true) (dnec dv e) -> R n x) ->
  (forall n e x, In n (Graph.nodes (cfg (dgraph dv))) ->
    In e (Graph.out (cfg (dgraph dv)) n) -> R (Graph.target (cfg (dgraph dv)) e) x ->
    ~ In x (ddefs dv e) -> R n x) ->
  (forall n e x y, In n (Graph.nodes (cfg (dgraph dv))) ->
    In e (Graph.out (cfg (dgraph dv)) n) -> In x (ddefs dv e) ->
    In (y, true) (dback dv e x true) -> R (Graph.target (cfg (dgraph dv)) e) x -> R n y) ->
  forall ts, least_model neededness_program (extract_needed_facts EN EE EX dv) (PNeeded, ts) ->
    exists n x, ts = args2 EN EX n x /\ R n x.
Proof.
  intros Hexit Hnec Hflow Hdep ts Hmodel.
  refine (model_induction neededness_program (extract_needed_facts EN EE EX dv)
    (needed_interpret EN EE EX dv R) _ _ _ (PNeeded, ts) Hmodel).
  - exists analysis_strata; exact (proj1 (proj2 analysis_programs_stratified)).
  - intros [p us] Hfact; destruct p; try exact Hfact.
    apply needed_facts_spec in Hfact; intuition discriminate.
  - intros r sigma Hr Hpos Hneg; cbn in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|Hr]]]]; [| | | |contradiction].
    + pose proof (Hpos (atm PSucc [v 0; v 2; v 3]) (or_introl eq_refl)) as Hsucc.
      pose proof (Hpos (atm PNec [v 2; v 1]) (or_intror (or_introl eq_refl))) as Hforced.
      cbn [needed_interpret ground atm v inst head fst snd] in Hsucc, Hforced |- *.
      apply needed_succ_input in Hsucc; apply needed_nec_input in Hforced.
      destruct Hsucc as [n [e [Hn [He Hcodes]]]].
      destruct Hforced as [e' [x [_ [Hx Hforced]]]].
      unfold args2, args3 in *; injection Hcodes as Hnc Hec Htc.
      injection Hforced as Hec' Hxc.
      assert (e' = e) by (apply (encode_injective EE); congruence); subst e'.
      exists n, x; split.
      * change ([sigma 0; sigma 1] = [encode EN n; encode EX x]); congruence.
      * exact (Hnec n e x Hn He Hx).
    + pose proof (Hpos (atm PExitUse [v 0; v 1]) (or_introl eq_refl)) as Hseed.
      cbn [needed_interpret ground atm v inst head fst snd] in Hseed |- *.
      apply needed_exit_input in Hseed; destruct Hseed as [n [x [Hn [Hx Hcodes]]]].
      exists n, x; split; [exact Hcodes|exact (Hexit n x Hn Hx)].
    + pose proof (Hpos (atm PSucc [v 0; v 2; v 3]) (or_introl eq_refl)) as Hsucc.
      pose proof (Hpos (atm PNeeded [v 3; v 1]) (or_intror (or_introl eq_refl))) as Hneed.
      pose proof (Hneg (atm PDef [v 2; v 1]) (or_intror (or_intror (or_introl eq_refl))))
        as Hkill.
      cbn [needed_interpret ground atm v inst head fst snd] in Hsucc, Hneed, Hkill |- *.
      apply needed_succ_input in Hsucc; destruct Hsucc as [n [e [Hn [He Hcodes]]]].
      destruct Hneed as [t [x [Hneed HR]]].
      unfold args2, args3 in *; injection Hcodes as Hnc Hec Htc.
      injection Hneed as Htc' Hxc.
      assert (t = Graph.target (cfg (dgraph dv)) e)
        by (apply (encode_injective EN); congruence); subst t.
      exists n, x; split.
      * change ([sigma 0; sigma 1] = [encode EN n; encode EX x]); congruence.
      * eapply Hflow; [exact Hn|exact He|exact HR|].
        intro Hdef; apply Hkill, needed_def_input; exists e, x.
        split; [unfold edges_of; apply in_flat_map; exists n; split; assumption|].
        split; [exact Hdef|].
        change ([sigma 2; sigma 1] = [encode EE e; encode EX x]); congruence.
    + exact (needed_dependency_interpret EN EE EX dv R sigma Hdep Hpos).
Qed.

Local Lemma needed_base_model {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) p ts : p <> PNeeded ->
  (least_model neededness_program (extract_needed_facts EN EE EX dv) (p, ts) <->
    In (p, ts) (extract_needed_facts EN EE EX dv)).
Proof.
  intro Hne; apply model_input.
  - exists analysis_strata; exact (proj1 (proj2 analysis_programs_stratified)).
  - intros r Hr; cbn in Hr; split_members; cbn; congruence.
Qed.

Local Lemma needed_model_seed {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) n x :
  In n (Graph.nodes (cfg (dgraph dv))) -> In (x, true) (dexit dv n) ->
  least_model neededness_program (extract_needed_facts EN EE EX dv) (PNeeded, args2 EN EX n x).
Proof.
  intros Hn Hx.
  change (least_model neededness_program (extract_needed_facts EN EE EX dv)
    (ground (valuation (encode EN n) (encode EX x) 1 1 1)
      (head (nth 1 (rules neededness_program) (Rule (atm PNeeded []) []))))).
  apply (model_fire neededness_program (extract_needed_facts EN EE EX dv)
    (nth 1 (rules neededness_program) (Rule (atm PNeeded []) []))
    (valuation (encode EN n) (encode EX x) 1 1 1)).
  - exists analysis_strata; exact (proj1 (proj2 analysis_programs_stratified)).
  - cbn; auto.
  - intros a Ha; cbn in Ha; split_members;
    cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
    apply (proj2 (needed_base_model EN EE EX dv PExitUse _ ltac:(discriminate)));
    apply needed_exit_input; eauto.
  - intros a Ha; cbn in Ha; split_members.
Qed.

Local Lemma needed_model_dependency {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) n e x y :
  In e (edges_of (cfg (dgraph dv))) ->
  least_model neededness_program (extract_needed_facts EN EE EX dv)
    (PSucc, args3 EN EE EN n e (Graph.target (cfg (dgraph dv)) e)) ->
  In x (ddefs dv e) -> In (y, true) (dback dv e x true) ->
  least_model neededness_program (extract_needed_facts EN EE EX dv)
    (PNeeded, args2 EN EX (Graph.target (cfg (dgraph dv)) e) x) ->
  least_model neededness_program (extract_needed_facts EN EE EX dv) (PNeeded, args2 EN EX n y).
Proof.
  intros Hedge Hsucc Hx Hy Hneed.
  change (least_model neededness_program (extract_needed_facts EN EE EX dv)
    (ground (valuation (encode EN n) (encode EX y) (encode EE e)
      (encode EN (Graph.target (cfg (dgraph dv)) e)) (encode EX x))
      (head (nth 3 (rules neededness_program) (Rule (atm PNeeded []) []))))).
  apply (model_fire neededness_program (extract_needed_facts EN EE EX dv)
    (nth 3 (rules neededness_program) (Rule (atm PNeeded []) []))
    (valuation (encode EN n) (encode EX y) (encode EE e)
      (encode EN (Graph.target (cfg (dgraph dv)) e)) (encode EX x))).
  - exists analysis_strata; exact (proj1 (proj2 analysis_programs_stratified)).
  - cbn; auto.
  - intros a Ha; cbn in Ha; split_members;
    cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
    + exact Hsucc.
    + apply (proj2 (needed_base_model EN EE EX dv PDef _ ltac:(discriminate))).
      apply needed_def_input; eauto.
    + apply (proj2 (needed_base_model EN EE EX dv PDep _ ltac:(discriminate))).
      apply needed_dep_input; exists e, x, y; auto.
    + exact Hneed.
  - intros a Ha; cbn in Ha; split_members.
Qed.

Local Lemma needed_model_edge {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) n e :
  In n (Graph.nodes (cfg (dgraph dv))) -> In e (Graph.out (cfg (dgraph dv)) n) ->
  (forall x, In (x, true) (dnec dv e) ->
    least_model neededness_program (extract_needed_facts EN EE EX dv)
      (PNeeded, args2 EN EX n x)) /\
  (forall x, least_model neededness_program (extract_needed_facts EN EE EX dv)
      (PNeeded, args2 EN EX (Graph.target (cfg (dgraph dv)) e) x) -> ~ In x (ddefs dv e) ->
    least_model neededness_program (extract_needed_facts EN EE EX dv)
      (PNeeded, args2 EN EX n x)) /\
  (forall x y, In x (ddefs dv e) -> In (y, true) (dback dv e x true) ->
    least_model neededness_program (extract_needed_facts EN EE EX dv)
      (PNeeded, args2 EN EX (Graph.target (cfg (dgraph dv)) e) x) ->
    least_model neededness_program (extract_needed_facts EN EE EX dv)
      (PNeeded, args2 EN EX n y)).
Proof.
  intros Hn He.
  assert (Hedge : In e (edges_of (cfg (dgraph dv))))
    by (unfold edges_of; apply in_flat_map; eauto).
  assert (Hsucc : least_model neededness_program (extract_needed_facts EN EE EX dv)
    (PSucc, args3 EN EE EN n e (Graph.target (cfg (dgraph dv)) e))).
  { apply (proj2 (needed_base_model EN EE EX dv PSucc _ ltac:(discriminate)));
  apply needed_succ_input; eauto. }
  split; [|split].
  - intros x Hx.
    change (least_model neededness_program (extract_needed_facts EN EE EX dv)
      (ground (valuation (encode EN n) (encode EX x) (encode EE e)
        (encode EN (Graph.target (cfg (dgraph dv)) e)) 1)
        (head (nth 0 (rules neededness_program) (Rule (atm PNeeded []) []))))).
    apply (model_fire neededness_program (extract_needed_facts EN EE EX dv)
      (nth 0 (rules neededness_program) (Rule (atm PNeeded []) []))
      (valuation (encode EN n) (encode EX x) (encode EE e)
        (encode EN (Graph.target (cfg (dgraph dv)) e)) 1)).
    + exists analysis_strata; exact (proj1 (proj2 analysis_programs_stratified)).
    + cbn; auto.
    + intros a Ha; cbn in Ha; split_members;
      cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
      * exact Hsucc.
      * apply (proj2 (needed_base_model EN EE EX dv PNec _ ltac:(discriminate)));
        apply needed_nec_input; eauto.
    + intros a Ha; cbn in Ha; split_members.
  - intros x Hneed Hkill.
    change (least_model neededness_program (extract_needed_facts EN EE EX dv)
      (ground (valuation (encode EN n) (encode EX x) (encode EE e)
        (encode EN (Graph.target (cfg (dgraph dv)) e)) 1)
        (head (nth 2 (rules neededness_program) (Rule (atm PNeeded []) []))))).
    apply (model_fire neededness_program (extract_needed_facts EN EE EX dv)
      (nth 2 (rules neededness_program) (Rule (atm PNeeded []) []))
      (valuation (encode EN n) (encode EX x) (encode EE e)
        (encode EN (Graph.target (cfg (dgraph dv)) e)) 1)).
    + exists analysis_strata; exact (proj1 (proj2 analysis_programs_stratified)).
    + cbn; auto.
    + intros a Ha; cbn in Ha; split_members;
      cbn [ground atm v inst valuation nth RulesSyntax.pred args map]; assumption.
    + intros a Ha; cbn in Ha; split_members;
      cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
      change (~ least_model neededness_program (extract_needed_facts EN EE EX dv)
        (PDef, args2 EE EX e x)).
      rewrite (needed_base_model EN EE EX dv PDef _ ltac:(discriminate)); rewrite needed_def_input.
      intros [e' [y [_ [Hy Hcodes]]]]; unfold args2 in Hcodes.
      injection Hcodes as Heq Hxy; apply (encode_injective EE) in Heq.
      apply (encode_injective EX) in Hxy; subst e' y; contradiction.
  - intros x y Hx Hy Hneed.
    exact (needed_model_dependency EN EE EX dv n e x y Hedge Hsucc Hx Hy Hneed).
Qed.

Local Lemma needed_model_support {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) n x : demand_vars_ok dv ->
  least_model neededness_program (extract_needed_facts EN EE EX dv)
    (PNeeded, args2 EN EX n x) -> In n (Graph.nodes (cfg (dgraph dv))) /\ In x (dvars dv).
Proof.
  intros [_ [Hback [Hexit Hdef]]] Hmodel.
  destruct (needed_model_induction EN EE EX dv
    (fun n x => In n (Graph.nodes (cfg (dgraph dv))) /\ In x (dvars dv)))
    with (ts := args2 EN EX n x) as [n' [x' [Hcodes Hsupport]]].
  - intros t y Ht Hy; split; [exact Ht|exact (Hexit t y true Hy)].
  - intros t e y Ht He Hy; split; [exact Ht|].
    apply (Hback e y false y true); apply in_or_app; now left.
  - intros t e y Ht He [_ Hy] Hkill; auto.
  - intros t e z y Ht He Hz Hy HR; split; [exact Ht|].
    apply (Hback e z true y true); apply in_or_app; now right.
  - exact Hmodel.
  - unfold args2 in Hcodes; injection Hcodes as Hn Hx.
    apply (encode_injective EN) in Hn; apply (encode_injective EX) in Hx; now subst n' x'.
Qed.

Local Lemma true_map_members {X} (EX : encoding X) xs x :
  pointwise_lookup EX false (Map.of_list EX (map (fun y => (y, true)) xs)) x = true <-> In x xs.
Proof.
  induction xs using rev_ind.
  - change (pointwise_lookup EX false (@Map.empty X bool) x = true <-> False).
    unfold pointwise_lookup; rewrite Map.get_empty; intuition discriminate.
  - rewrite map_app; unfold Map.of_list at 1; rewrite fold_left_app; cbn [fold_left fst snd map].
    fold (Map.of_list EX (map (fun y => (y, true)) xs)).
    destruct (encoded_eq_dec EX x x0) as [->|Hne].
    + unfold pointwise_lookup; rewrite Map.get_set_same, in_app_iff; cbn; tauto.
    + unfold pointwise_lookup at 1; rewrite Map.get_set_other by exact Hne.
      change (pointwise_lookup EX false (Map.of_list EX (map (fun y => (y, true)) xs)) x =
        true <-> In x (xs ++ [x0])).
      rewrite IHxs, in_app_iff; cbn; intuition congruence.
Qed.

Local Lemma needed_decode {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) db : demand_vars_ok dv ->
  solve_program neededness_program (extract_needed_facts EN EE EX dv) = Some db ->
  forall n x, dget EX bool_lattice (needed_of_db EN EX dv db n) x = true <->
    least_model neededness_program (extract_needed_facts EN EE EX dv)
      (PNeeded, args2 EN EX n x).
Proof.
  intros Hvars Hsolve.
  assert (Hmodel : forall p ts, db_holds neededness_program db p ts = true <->
    least_model neededness_program (extract_needed_facts EN EE EX dv) (p, ts)).
  { apply solver_model; [split; [exact (proj1 (proj2 analysis_programs_rules_wf))|
      apply needed_facts_arity]| |exact Hsolve].
    exists analysis_strata; exact (proj1 (proj2 analysis_programs_stratified)). }
  intros n x; destruct (in_dec (encoded_eq_dec EX) x (dvars dv)) as [Hin|Hout].
  - unfold needed_of_db, dget, pointwise_lookup; rewrite finite_map_clamp_get by exact Hin.
    change (pointwise_lookup EX false (Map.of_list EX (map (fun y => (y, true))
      (filter (fun y => db_holds neededness_program db PNeeded (args2 EN EX n y))
        (dvars dv)))) x = true <->
      least_model neededness_program (extract_needed_facts EN EE EX dv)
        (PNeeded, args2 EN EX n x)).
    rewrite true_map_members, filter_In, Hmodel; tauto.
  - unfold dget, pointwise_lookup; rewrite finite_map_out by exact Hout; cbn [bot bool_lattice].
    split; [discriminate|intro Hneed; exfalso; apply Hout].
    exact (proj2 (needed_model_support EN EE EX dv n x Hvars Hneed)).
Qed.

Local Lemma needed_transfer_members {S O N E X Cv} EX
    (dv : demand_view S O N E X Cv bool) e d x :
  (forall e x, dback dv e x false = nil) ->
  (dget EX bool_lattice (demand_transfer EX bool_demand dv e d) x = true <->
  In x (dvars dv) /\
    ((~ In x (ddefs dv e) /\ dget EX bool_lattice d x = true) \/
     In (x, true) (dnec dv e) \/ exists y, In y (ddefs dv e) /\
       In (x, true) (dback dv e y true) /\ dget EX bool_lattice d y = true)).
Proof.
  intro Hstrict; rewrite demand_bool_transfer_true.
  assert (Hkill : FinSet.mem EX x (FinSet.of_list EX (ddefs dv e)) = false <->
    ~ In x (ddefs dv e)).
  { rewrite <- (FinSet.of_list_spec EX x (ddefs dv e)).
    destruct (FinSet.mem EX x (FinSet.of_list EX (ddefs dv e)));
      intuition congruence. }
  rewrite Hkill; split; intros [Hin [Hkeep|[Hnec|[y [Hy Hback]]]]];
    split; try exact Hin; try (left; exact Hkeep); try (right; left; exact Hnec).
  - right; right; exists y; split; [exact Hy|].
    destruct (dget EX bool_lattice d y) eqn:Hneed.
    + auto.
    + rewrite Hstrict in Hback; contradiction.
  - right; right; exists y; destruct Hback as [Hback Hneed]; rewrite Hneed; auto.
Qed.

Local Lemma needed_exit_members {S O N E X Cv} EX
    (dv : demand_view S O N E X Cv bool) n x : demand_vars_ok dv ->
  (dget EX bool_lattice
    (finite_map_clamp EX (dvars dv) (exit_map EX bool_lattice (dexit dv n))) x = true <->
    In (x, true) (dexit dv n)).
Proof.
  intros [_ [_ [Hexit _]]]; destruct (in_dec (encoded_eq_dec EX) x (dvars dv)) as [Hin|Hout].
  - unfold dget, pointwise_lookup; rewrite finite_map_clamp_get by exact Hin;
      apply demand_bool_exit_true.
  - unfold dget, pointwise_lookup; rewrite finite_map_out by exact Hout; cbn [bot bool_lattice].
    split; [discriminate|intro Hx; exfalso; exact (Hout (Hexit n x true Hx))].
Qed.

Local Lemma needed_model_post {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) db : graph_wf (cfg (dgraph dv)) ->
  demand_vars_ok dv -> (forall e x, dback dv e x false = nil) ->
  solve_program neededness_program (extract_needed_facts EN EE EX dv) = Some db ->
  post_solution (demand_lattice EX bool_demand dv) (demand_system EX bool_demand dv)
    (needed_of_db EN EX dv db).
Proof.
  intros Hwf Hvars Hstrict Hsolve; unfold demand_system; apply backward_post_solution_iff; split.
  - intros n Hn; apply demand_bool_leb_iff; intros x Hx.
    apply (needed_exit_members EX dv n x Hvars) in Hx.
    apply (needed_decode EN EE EX dv db Hvars Hsolve), needed_model_seed; assumption.
  - intros e He; apply demand_bool_leb_iff; intros x Hx.
    apply (needed_transfer_members EX dv e _ x Hstrict) in Hx; destruct Hx as [_ Hx].
    destruct (listed_edge _ e He) as [n [Hn Hout]].
    rewrite (out_source Hwf n e Hout); apply (needed_decode EN EE EX dv db Hvars Hsolve).
    destruct (needed_model_edge EN EE EX dv n e Hn Hout) as [Hnec [Hflow Hdep]].
    destruct Hx as [[Hkill Hneed]|[Hx|[y [Hy [Hx Hneed]]]]].
    + apply Hflow; [apply (needed_decode EN EE EX dv db Hvars Hsolve); exact Hneed|exact Hkill].
    + exact (Hnec x Hx).
    + apply (Hdep y x Hy Hx); apply (needed_decode EN EE EX dv db Hvars Hsolve); exact Hneed.
Qed.

Local Lemma needed_model_below {S O N E X Cv} EN EE EX
    (dv : demand_view S O N E X Cv bool) sigma : graph_wf (cfg (dgraph dv)) ->
  demand_vars_ok dv -> (forall e x, dback dv e x false = nil) ->
  post_solution (demand_lattice EX bool_demand dv) (demand_system EX bool_demand dv) sigma ->
  forall n x, least_model neededness_program (extract_needed_facts EN EE EX dv)
    (PNeeded, args2 EN EX n x) -> dget EX bool_lattice (sigma n) x = true.
Proof.
  intros Hwf Hvars Hstrict Hpost n x Hmodel.
  destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
  assert (Hedge : forall t e y, In t (Graph.nodes (cfg (dgraph dv))) ->
    In e (Graph.out (cfg (dgraph dv)) t) ->
    dget EX bool_lattice (demand_transfer EX bool_demand dv e
      (sigma (Graph.target (cfg (dgraph dv)) e))) y = true ->
    dget EX bool_lattice (sigma t) y = true).
  { intros t e y Ht He Hy; rewrite <- (out_source Hwf t e He).
    apply (proj1 (demand_bool_leb_iff _ _ _ _) (Hflow e
      (proj2 (in_flat_map _ _ _) (ex_intro _ t (conj Ht He)))) y Hy). }
  destruct (needed_model_induction EN EE EX dv
    (fun n x => dget EX bool_lattice (sigma n) x = true))
    with (ts := args2 EN EX n x) as [n' [x' [Hcodes Hmem]]].
  - intros t y Ht Hy; apply (proj1 (demand_bool_leb_iff _ _ _ _) (Hseed t Ht)).
    apply (needed_exit_members EX dv t y Hvars); exact Hy.
  - intros t e y Ht He Hy; apply (Hedge t e y Ht He).
    apply (needed_transfer_members EX dv e _ y Hstrict); split.
    + destruct Hvars as [_ [Hback _]]; apply (Hback e y false y true), in_or_app; now left.
    + right; now left.
  - intros t e y Ht He Hy Hkill; apply (Hedge t e y Ht He).
    apply (needed_transfer_members EX dv e _ y Hstrict); split.
    + destruct (Map.get EX y (proj1_sig (sigma (Graph.target (cfg (dgraph dv)) e))))
        eqn:Hget.
      * apply (proj2 (proj2_sig (sigma (Graph.target (cfg (dgraph dv)) e))) y).
        rewrite Hget; discriminate.
      *
      unfold dget, pointwise_lookup in Hy; rewrite Hget in Hy; discriminate.
    + left; auto.
  - intros t e z y Ht He Hz Hy Hneed; apply (Hedge t e y Ht He).
    apply (needed_transfer_members EX dv e _ y Hstrict); split.
    + destruct Hvars as [_ [Hback _]]; apply (Hback e z true y true), in_or_app; now right.
    + right; right; exists z; auto.
  - exact Hmodel.
  - unfold args2 in Hcodes; injection Hcodes as Hn Hx.
    apply (encode_injective EN) in Hn; apply (encode_injective EX) in Hx; now subst n' x'.
Qed.

(** Under false-demand strictness, the Rules result is the least node-wise demand solution. *)
Theorem rules_neededness_least {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (dv : demand_view S O N E X Cv bool) (db : database pred) :
  graph_wf (cfg (dgraph dv)) -> demand_vars_ok dv -> (forall e x, dback dv e x false = nil) ->
  solve_program neededness_program (extract_needed_facts EN EE EX dv) = Some db ->
  least_solution (demand_lattice EX bool_demand dv) (demand_system EX bool_demand dv)
    (needed_of_db EN EX dv db).
Proof.
  intros Hwf Hvars Hstrict Hsolve; split.
  - exact (needed_model_post EN EE EX dv db Hwf Hvars Hstrict Hsolve).
  - intros sigma Hpost n; apply demand_bool_leb_iff; intros x Hx.
    apply (needed_model_below EN EE EX dv sigma Hwf Hvars Hstrict Hpost).
    apply (needed_decode EN EE EX dv db Hvars Hsolve); exact Hx.
Qed.

(** The declarative needed relation agrees exactly with true entries of the decoded map. *)
Theorem rules_neededness_model {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (dv : demand_view S O N E X Cv bool) (db : database pred) :
  graph_wf (cfg (dgraph dv)) -> demand_vars_ok dv -> (forall e x, dback dv e x false = nil) ->
  solve_program neededness_program (extract_needed_facts EN EE EX dv) = Some db ->
  forall n x, holds (least_model neededness_program (extract_needed_facts EN EE EX dv)) PNeeded
    (args2 EN EX n x) <-> dget EX bool_lattice (needed_of_db EN EX dv db n) x = true.
Proof.
  intros Hwf Hvars Hstrict Hsolve n x; symmetry; apply (needed_decode EN EE EX dv db Hvars Hsolve).
Qed.

(** * Forward reaching definitions *)

Local Definition reach_interpret {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv)
    (R : N -> X -> E -> Prop) (f : ground_atom pred) : Prop :=
  match fst f with
  | PReaches => exists d x n, snd f = args3 EE EX EN d x n /\ R n x d
  | _ => In f (extract_live_facts EN EE EX vv)
  end.

Local Lemma reach_model_induction {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv)
    (R : N -> X -> E -> Prop) :
  (forall n e x, In n (Graph.nodes (cfg (gview vv))) ->
    In e (Graph.out (cfg (gview vv)) n) -> In x (defs vv e) ->
    R (Graph.target (cfg (gview vv)) e) x e) ->
  (forall n e x d, In n (Graph.nodes (cfg (gview vv))) ->
    In e (Graph.out (cfg (gview vv)) n) -> R n x d -> ~ In x (defs vv e) ->
    R (Graph.target (cfg (gview vv)) e) x d) ->
  forall ts, least_model reaching_program (extract_live_facts EN EE EX vv) (PReaches, ts) ->
    exists d x n, ts = args3 EE EX EN d x n /\ R n x d.
Proof.
  intros Hgen Hflow ts Hmodel.
  refine (model_induction reaching_program (extract_live_facts EN EE EX vv)
    (reach_interpret EN EE EX vv R) _ _ _ (PReaches, ts) Hmodel).
  - exists analysis_strata; exact (proj2 (proj2 analysis_programs_stratified)).
  - intros [p us] Hfact; destruct p; try exact Hfact.
    apply live_facts_spec in Hfact; intuition discriminate.
  - intros r sigma Hr Hpos Hneg; cbn in Hr; destruct Hr as [<-|[<-|Hr]]; [| |contradiction].
    + pose proof (Hpos (atm PDef [v 0; v 1]) (or_introl eq_refl)) as Hdef.
      pose proof (Hpos (atm PSucc [v 3; v 0; v 2]) (or_intror (or_introl eq_refl))) as Hsucc.
      cbn [reach_interpret ground atm v inst head fst snd] in Hsucc, Hdef |- *.
      apply live_succ_input in Hsucc; apply live_def_input in Hdef.
      destruct Hsucc as [n [e [Hn [He Hcodes]]]].
      destruct Hdef as [e' [x [_ [Hx Hdef]]]].
      unfold args2, args3 in *; injection Hcodes as Hnc Hec Htc.
      injection Hdef as Hec' Hxc.
      assert (e' = e) by (apply (encode_injective EE); congruence); subst e'.
      exists e, x, (Graph.target (cfg (gview vv)) e); split.
      * change ([sigma 0; sigma 1; sigma 2] =
          [encode EE e; encode EX x; encode EN (Graph.target (cfg (gview vv)) e)]); congruence.
      * exact (Hgen n e x Hn He Hx).
    + pose proof (Hpos (atm PReaches [v 0; v 1; v 3]) (or_introl eq_refl)) as Hreach.
      pose proof (Hpos (atm PSucc [v 3; v 4; v 2]) (or_intror (or_introl eq_refl))) as Hsucc.
      pose proof (Hneg (atm PDef [v 4; v 1]) (or_intror (or_intror (or_introl eq_refl))))
        as Hkill.
      cbn [reach_interpret ground atm v inst head fst snd] in Hsucc, Hreach, Hkill |- *.
      apply live_succ_input in Hsucc; destruct Hsucc as [n [e [Hn [He Hcodes]]]].
      destruct Hreach as [d [x [n' [Hreach HR]]]].
      unfold args2, args3 in *; injection Hcodes as Hnc Hec Htc.
      injection Hreach as Hdc Hxc Hnc'.
      assert (n' = n) by (apply (encode_injective EN); congruence); subst n'.
      exists d, x, (Graph.target (cfg (gview vv)) e); split.
      * change ([sigma 0; sigma 1; sigma 2] =
          [encode EE d; encode EX x; encode EN (Graph.target (cfg (gview vv)) e)]); congruence.
      * apply (Hflow n e x d Hn He HR); intro Hdef.
        apply Hkill, live_def_input; exists e, x; split.
        -- unfold edges_of; apply in_flat_map; exists n; split; assumption.
        -- split; [exact Hdef|].
           change ([sigma 4; sigma 1] = [encode EE e; encode EX x]); congruence.
Qed.

Local Lemma reach_base_model {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) p ts :
  p <> PReaches ->
  (least_model reaching_program (extract_live_facts EN EE EX vv) (p, ts) <->
    In (p, ts) (extract_live_facts EN EE EX vv)).
Proof.
  intro Hne; apply model_input.
  - exists analysis_strata; exact (proj2 (proj2 analysis_programs_stratified)).
  - intros r Hr; cbn in Hr; split_members; cbn; congruence.
Qed.

Local Lemma reach_model_seed {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) n e x :
  In n (Graph.nodes (cfg (gview vv))) -> In e (Graph.out (cfg (gview vv)) n) ->
  In x (defs vv e) -> least_model reaching_program (extract_live_facts EN EE EX vv)
    (PReaches, args3 EE EX EN e x (Graph.target (cfg (gview vv)) e)).
Proof.
  intros Hn He Hx.
  change (least_model reaching_program (extract_live_facts EN EE EX vv)
    (ground (valuation (encode EE e) (encode EX x)
      (encode EN (Graph.target (cfg (gview vv)) e)) (encode EN n) 1)
      (head (nth 0 (rules reaching_program) (Rule (atm PReaches []) []))))).
  apply (model_fire reaching_program (extract_live_facts EN EE EX vv)
    (nth 0 (rules reaching_program) (Rule (atm PReaches []) []))
    (valuation (encode EE e) (encode EX x)
      (encode EN (Graph.target (cfg (gview vv)) e)) (encode EN n) 1)).
  - exists analysis_strata; exact (proj2 (proj2 analysis_programs_stratified)).
  - cbn; auto.
  - intros a Ha; cbn in Ha; split_members;
    cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
    + apply (proj2 (reach_base_model EN EE EX vv PDef _ ltac:(discriminate)));
      apply live_def_input; exists e, x.
      split; [unfold edges_of; apply in_flat_map; exists n; split; assumption|auto].
    + apply (proj2 (reach_base_model EN EE EX vv PSucc _ ltac:(discriminate)));
      apply live_succ_input; eauto.
  - intros a Ha; cbn in Ha; split_members.
Qed.

Local Lemma reach_model_flow {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) n e x d :
  In n (Graph.nodes (cfg (gview vv))) -> In e (Graph.out (cfg (gview vv)) n) ->
  least_model reaching_program (extract_live_facts EN EE EX vv) (PReaches, args3 EE EX EN d x n) ->
  ~ In x (defs vv e) -> least_model reaching_program (extract_live_facts EN EE EX vv)
    (PReaches, args3 EE EX EN d x (Graph.target (cfg (gview vv)) e)).
Proof.
  intros Hn He Hreach Hkill.
  change (least_model reaching_program (extract_live_facts EN EE EX vv)
    (ground (valuation (encode EE d) (encode EX x)
      (encode EN (Graph.target (cfg (gview vv)) e)) (encode EN n) (encode EE e))
      (head (nth 1 (rules reaching_program) (Rule (atm PReaches []) []))))).
  apply (model_fire reaching_program (extract_live_facts EN EE EX vv)
    (nth 1 (rules reaching_program) (Rule (atm PReaches []) []))
    (valuation (encode EE d) (encode EX x)
      (encode EN (Graph.target (cfg (gview vv)) e)) (encode EN n) (encode EE e))).
  - exists analysis_strata; exact (proj2 (proj2 analysis_programs_stratified)).
  - cbn; auto.
  - intros a Ha; cbn in Ha; split_members;
    cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
    + exact Hreach.
    + apply (proj2 (reach_base_model EN EE EX vv PSucc _ ltac:(discriminate)));
      apply live_succ_input; eauto.
  - intros a Ha; cbn in Ha; split_members;
    cbn [ground atm v inst valuation nth RulesSyntax.pred args map].
    change (~ least_model reaching_program (extract_live_facts EN EE EX vv)
      (PDef, args2 EE EX e x)).
    rewrite (reach_base_model EN EE EX vv PDef _ ltac:(discriminate)); rewrite live_def_input.
    intros [e' [y [_ [Hy Hcodes]]]]; unfold args2 in Hcodes.
    injection Hcodes as Heq Hxy; apply (encode_injective EE) in Heq.
    apply (encode_injective EX) in Hxy; subst e' y; contradiction.
Qed.

Local Lemma reach_model_support {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) n x d :
  graph_wf (cfg (gview vv)) ->
  least_model reaching_program (extract_live_facts EN EE EX vv) (PReaches, args3 EE EX EN d x n) ->
  In n (Graph.nodes (cfg (gview vv))) /\ In (x, d) (reach_universe EX EE vv).
Proof.
  intros Hwf Hmodel.
  destruct (reach_model_induction EN EE EX vv
    (fun n x d => In n (Graph.nodes (cfg (gview vv))) /\ In (x, d) (reach_universe EX EE vv)))
    with (ts := args3 EE EX EN d x n) as [d' [x' [n' [Hcodes Hsupport]]]].
  - intros t e y Ht He Hy; split; [exact (out_target_in Hwf t e Ht He)|].
    apply AnalysesLiveness.reach_universe_covers; [|exact Hy].
    unfold edges_of; apply in_flat_map; exists t; split; assumption.
  - intros t e y w Ht He [_ Hy] Hkill; split; [exact (out_target_in Hwf t e Ht He)|exact Hy].
  - exact Hmodel.
  - unfold args3 in Hcodes; injection Hcodes as Hd Hx Hn.
    apply (encode_injective EE) in Hd; apply (encode_injective EX) in Hx.
    apply (encode_injective EN) in Hn; now subst d' x' n'.
Qed.

Local Lemma reach_decode {S O N E X Cv} EN EE EX (vv : var_view S O N E X Cv) db :
  graph_wf (cfg (gview vv)) ->
  solve_program reaching_program (extract_live_facts EN EE EX vv) = Some db ->
  forall n x d, fmem (pair_encoding EX EE) (x, d) (reach_of_db EN EE EX vv db n) = true <->
    least_model reaching_program (extract_live_facts EN EE EX vv) (PReaches, args3 EE EX EN d x n).
Proof.
  intros Hwf Hsolve.
  assert (Hmodel : forall p ts, db_holds reaching_program db p ts = true <->
    least_model reaching_program (extract_live_facts EN EE EX vv) (p, ts)).
  { apply solver_model; [split; [exact (proj2 (proj2 analysis_programs_rules_wf))|
      apply live_facts_arity]| |exact Hsolve].
    exists analysis_strata; exact (proj2 (proj2 analysis_programs_stratified)). }
  intros n x d; unfold reach_of_db; rewrite clamp_members, FinSet.of_list_spec, filter_In.
  cbn [fst snd]; rewrite Hmodel; split; [tauto|intro Hreach].
  pose proof (proj2 (reach_model_support EN EE EX vv n x d Hwf Hreach)); auto.
Qed.

(** The Rules database is the least solution of the indexed reaching-definition system. *)
Theorem rules_reaching_least {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program reaching_program (extract_live_facts EN EE EX vv) = Some db ->
  least_solution (reach_lattice EX EE vv) (reaching_system EX EE vv) (reach_of_db EN EE EX vv db).
Proof.
  intros Hwf Hsolve; split.
  - apply (proj2 (AnalysesLiveness.reaching_post_solution_iff EX EE vv _)).
    apply forward_post_solution_iff; split.
    + intros n Hn; apply (bot_least (finite_powerset_laws _ _)).
    + intros e He; apply finite_le; intros [x d] Hx.
      apply (AnalysesLiveness.reaching_transfer_spec EX EE vv e _ x d He) in Hx.
      destruct (listed_edge _ e He) as [n [Hn Hout]].
      apply (reach_decode EN EE EX vv db Hwf Hsolve).
      destruct Hx as [[Hreach Hkill]|[-> Hdef]].
      * eapply (reach_model_flow EN EE EX vv n e x d Hn Hout).
        -- rewrite <- (out_source Hwf n e Hout).
           apply (reach_decode EN EE EX vv db Hwf Hsolve); exact Hreach.
        -- apply (proj1 (AnalysesLiveness.mentions_false EX x (defs vv e))); exact Hkill.
      * exact (reach_model_seed EN EE EX vv n e x Hn Hout Hdef).
  - intros sigma Hpost n; apply finite_le; intros [x d] Hx.
    apply (reach_decode EN EE EX vv db Hwf Hsolve) in Hx.
    apply (proj1 (AnalysesLiveness.reaching_post_solution_iff EX EE vv sigma)) in Hpost.
    destruct (proj1 (forward_post_solution_iff _ _ _ _ _) Hpost) as [_ Hflow].
    destruct (reach_model_induction EN EE EX vv
      (fun n x d => fmem (pair_encoding EX EE) (x, d) (sigma n) = true))
      with (ts := args3 EE EX EN d x n) as [d' [x' [n' [Hcodes Hmem]]]].
    + intros t e y Ht He Hy.
      assert (Hedge : In e (edges_of (cfg (gview vv))))
        by (unfold edges_of; apply in_flat_map; exists t; split; assumption).
      apply (proj1 (finite_le _ _ _ _) (Hflow e Hedge)).
      apply (AnalysesLiveness.reaching_transfer_spec EX EE vv e _ y e Hedge); right; auto.
    + intros t e y w Ht He Hy Hkill.
      assert (Hedge : In e (edges_of (cfg (gview vv))))
        by (unfold edges_of; apply in_flat_map; exists t; split; assumption).
      apply (proj1 (finite_le _ _ _ _) (Hflow e Hedge)).
      apply (AnalysesLiveness.reaching_transfer_spec EX EE vv e _ y w Hedge); left; split.
      * rewrite (out_source Hwf t e He); exact Hy.
      * apply (proj2 (AnalysesLiveness.mentions_false EX y (defs vv e))); exact Hkill.
    + exact Hx.
    + unfold args3 in Hcodes; injection Hcodes as Hd Hvar Hn.
      apply (encode_injective EE) in Hd; apply (encode_injective EX) in Hvar.
      apply (encode_injective EN) in Hn; now subst d' x' n'.
Qed.

(** The declarative reaches relation agrees exactly with decoded variable/writer membership. *)
Theorem rules_reaching_model {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program reaching_program (extract_live_facts EN EE EX vv) = Some db ->
  forall n x d, holds (least_model reaching_program (extract_live_facts EN EE EX vv)) PReaches
    (args3 EE EX EN d x n) <->
    fmem (pair_encoding EX EE) (x, d) (reach_of_db EN EE EX vv db n) = true.
Proof.
  intros Hwf Hsolve n x d; symmetry; apply (reach_decode EN EE EX vv db Hwf Hsolve).
Qed.
