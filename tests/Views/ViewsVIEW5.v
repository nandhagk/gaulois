(** * Dominated refinement boundary examples

    These examples exercise dominated guards, repeated edges and constructive SSA frames.
    For example, entering a block binds its local value while preserving a guard defined earlier.
    Builds on: ViewsDominated, ViewsRefine and OrderFlat. *)

From Stdlib Require Import List Bool Arith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderLift OrderFlat.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDominance GraphDominators
  GraphEdgeDominance.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsRefine ViewsDominated.
Import List.ListNotations.

Definition dominated_test_graph : Graph.t bool bool :=
  {| Graph.entries := [false];
     Graph.nodes := [false; true];
     Graph.out := fun n => if n then [true; true] else [false];
     Graph.source := fun e => e;
     Graph.target := fun _ => true |}.

Definition dominated_test_context := make_dom_context bool_encoding dominated_test_graph.

Example repeated_self_loop_preserves_the_entering_edge_query :
  dominating_edges_in dominated_test_context true = [false].
Proof.
  vm_compute; reflexivity.
Qed.

Example entry_has_no_dominating_edge : dominating_edges_in dominated_test_context false = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example self_loop_is_not_reported_as_dominating :
  existsb (Bool.eqb true) (dominating_edges_in dominated_test_context true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_outgoing_edges_are_present :
  Graph.out dominated_test_graph true = [true; true] /\
  length (Graph.out dominated_test_graph true) = 2.
Proof.
  split; reflexivity.
Qed.

Example repeated_outgoing_list_is_not_nodup : ~ NoDup (Graph.out dominated_test_graph true).
Proof.
  intro Hdistinct; inversion Hdistinct as [|a xs Hfresh Hrest]; subst.
  apply Hfresh; left; reflexivity.
Qed.

Definition dominated_test_diamond : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun n => match n with
       | 0 => [(0, 1); (0, 2)]
       | 1 => [(1, 3)]
       | 2 => [(2, 3)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Example a_branch_edge_does_not_refine_the_join :
  dominating_edges_in (make_dom_context nat_encoding dominated_test_diamond) 3 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Section ConstructiveFrames.
Context {C : Type} (c : C).

Definition dominated_test_semantics : semantics bool unit :=
  Semantics (fun s => s = false) (fun _ l s' => l = [] /\ s' = true).

Definition dominated_test_base : graph_view bool unit bool bool :=
  {| cfg := dominated_test_graph;
     point := fun s => s;
     taken := fun s _ _ e => e = s;
     stays := fun s _ s' => s' = s |}.

Definition dominated_test_view : ssa_view bool unit bool bool bool unit C :=
  {| base := dominated_test_base;
     def := fun x : bool => if x then Arbitrary else Op tt [false];
     home := fun x => x;
     params := fun _ => [];
     edge_args := fun _ => [];
     edge_guard := fun e => if e then [] else [Condition false (GConst c)];
     val := fun s x => if x then if s then Some c else None else Some c;
     op_eval := fun _ cs => match cs with [d] => Some d | _ => None end;
     truth := fun _ => true |}.

Example constructive_view_laws : ssa_view_laws dominated_test_semantics dominated_test_view.
Proof.
  constructor.
  - constructor.
    + constructor.
      * repeat constructor; cbn; intuition discriminate.
      * intros s [Heq|Hin]; [subst s; cbn; auto|contradiction].
      * intros s e Hin; destruct s, e; cbn in *; intuition discriminate.
      * intros s e Hnode Hin; cbn; auto.
    + intros s Hinitial; cbn in Hinitial |- *; subst s; auto.
    + intros s l s' Hreach Hstep; right; exists s; reflexivity.
    + intros s l s' e Hreach [Hl Htarget] Htaken; cbn in Htaken; subst e s'.
      split; [destruct s; cbn; auto|reflexivity].
    + intros s l s' Hreach Hstep Hstay; exact Hstay.
  - intros x b i Hdef; destruct x; discriminate.
  - intros s l s' e Hreach Hstep Htaken; cbn in Htaken; subst e; destruct s; cbn.
    + constructor.
    + constructor; [exists c; split; reflexivity|constructor].
  - intros s l s' e Hreach Hstep Htaken cd o args Hcd Hdef.
    cbn in Htaken; subst e; destruct s; cbn in Hcd; [contradiction|].
    destruct Hcd as [Hcd|Hfalse]; [subst cd|contradiction].
    cbn in Hdef; inversion Hdef; subst o args.
    exists [c], c; split; [constructor; [reflexivity|constructor]|split; reflexivity].
  - intros s l s' x d Hreach Hstep Hvalue; destruct x.
    + right; right; right; reflexivity.
    + left; exact Hvalue.
Qed.

Example constructive_strict_laws : strict_ssa_laws dominated_test_semantics dominated_test_view.
Proof.
  constructor.
  - intros s l s' x Hreach Hstep Hstay Hchanged.
    cbn in Hstay; subst s'; exfalso; apply Hchanged; reflexivity.
  - intros s l s' e x Hreach [Hl Htarget] Htaken Hchanged.
    cbn in Htaken; subst s' e; destruct x, s; cbn in *; congruence.
  - intros s l s' x Hreach Hstep Hstay Haway.
    cbn in Hstay; subst s'; reflexivity.
  - intros s l s' e x Hreach [Hl Htarget] Htaken Haway.
    cbn in Htaken; subst s' e; destruct x, s; cbn in *; congruence.
  - intros e cd Hedge Hcd; destruct e; cbn in Hcd; [contradiction|].
    destruct Hcd as [Hcd|Hfalse]; [subst cd|contradiction].
    apply dominates_refl.
  - intros x o args y Hdef Hin; destruct x; cbn in Hdef; [discriminate|].
    inversion Hdef; subst o args; destruct Hin as [Hin|Hfalse]; [subst y|contradiction].
    apply dominates_refl.
Qed.

Example entering_edge_binds_at_its_target_and_preserves_the_guard :
  step dominated_test_semantics false [] true /\
  taken dominated_test_base false [] true false /\
  home dominated_test_view true = point dominated_test_base true /\
  val dominated_test_view false true = None /\
  val dominated_test_view true true = Some c /\
  val dominated_test_view true false = val dominated_test_view false false.
Proof.
  repeat split; reflexivity.
Qed.

Example positive_frame_preserves_an_arbitrary_concrete_carrier :
  val dominated_test_view true false = val dominated_test_view false false.
Proof.
  apply (frame_on_edge constructive_strict_laws false [] true false false).
  - exists false, []; split; [reflexivity|constructor].
  - split; reflexivity.
  - reflexivity.
  - discriminate.
Qed.

Example positive_stay_frame_preserves_an_arbitrary_concrete_carrier :
  val dominated_test_view true false = val dominated_test_view true false.
Proof.
  apply (frame_in_stay constructive_strict_laws true [] true false).
  - exists false, []; split; [reflexivity|].
    change (exec dominated_test_semantics false ([] ++ []) true).
    econstructor; [split; reflexivity|constructor].
  - split; reflexivity.
  - reflexivity.
  - discriminate.
Qed.

Definition dominated_test_domain : sparse_domain (flat unit) C unit :=
  {| fact_lat := flat_lattice (fun _ _ => true);
     fact_conc := flat_gamma (fun _ d => d = c);
     top_fact := FTop;
     op_abs := fun _ _ => FTop;
     assume_value := fun _ a => a;
     assume_args := fun _ _ fs => fs |}.

Example constructive_domain_laws :
  sparse_domain_laws dominated_test_domain (truth dominated_test_view)
    (op_eval dominated_test_view).
Proof.
  assert (Heq : forall x y : unit, true = true <-> x = y).
  { intros [] []; split; intro H; reflexivity. }
  constructor.
  - apply flat_laws; exact Heq.
  - apply flat_gamma_laws; exact Heq.
  - intros d Hfalse; exact Hfalse.
  - intro d; exact I.
  - intros o fs cs d Hfs Hop; exact I.
  - intros k a d Ha Hguard; exact Ha.
  - intros o b fs cs d Hfs Hop Htruth; exact Hfs.
Qed.

Definition dominated_test_problem := SparseProblem dominated_test_view dominated_test_domain
  [false; true] (fun _ => FVal tt).

Definition dominated_test_sigma (_ : sparse_unknown bool bool bool) : lift_bot (flat unit) :=
  Some (FVal tt).

Example refinement_walk_accepts_a_real_dominating_guard :
  dominating_edges_in dominated_test_context true = [false] /\
  refined_fact bool_encoding dominated_test_context dominated_test_problem
    dominated_test_sigma true false = Some (FVal tt).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example generic_refinement_soundness_allows_repeated_outgoing_edges :
  gamma (lift_bot_gamma (fact_conc dominated_test_domain))
    (refined_fact bool_encoding dominated_test_context dominated_test_problem
      dominated_test_sigma true false) c.
Proof.
  apply (refined_fact_sound dominated_test_semantics bool_encoding bool_encoding
    dominated_test_context dominated_test_problem dominated_test_sigma eq_refl
    constructive_view_laws constructive_strict_laws constructive_domain_laws true false c).
  - exists false, []; split; [reflexivity|].
    change (exec dominated_test_semantics false ([] ++ []) true).
    econstructor; [split; reflexivity|constructor].
  - intros x d Hvalue; destruct x; cbn in Hvalue; injection Hvalue as Heq; subst d; reflexivity.
  - reflexivity.
Qed.

End ConstructiveFrames.

Definition precise_guard_domain : sparse_domain (flat nat) nat unit :=
  {| fact_lat := flat_lattice Nat.eqb;
     fact_conc := flat_gamma eq;
     top_fact := FTop;
     op_abs := fun _ _ => FTop;
     assume_value := fun k a => match k, a with
       | GConst d, FTop => FVal d
       | _, _ => a
       end;
     assume_args := fun _ _ fs => fs |}.

Definition precise_guard_problem := SparseProblem (dominated_test_view 7) precise_guard_domain
  [false; true] (fun _ => FTop).

Example precise_guard_domain_laws :
  sparse_domain_laws precise_guard_domain (truth (dominated_test_view 7))
    (op_eval (dominated_test_view 7)).
Proof.
  constructor.
  - apply flat_laws; exact Nat.eqb_eq.
  - apply flat_gamma_laws; exact Nat.eqb_eq.
  - intros d Hfalse; exact Hfalse.
  - intro d; exact I.
  - intros o fs cs d Hfs Hop; exact I.
  - intros k a d Ha Hguard; destruct k, a; cbn in *; try exact Ha; try exact I; congruence.
  - intros o b fs cs d Hfs Hop Htruth; exact Hfs.
Qed.

Example dominated_constant_guard_improves_the_fact_at_the_read :
  refined_fact bool_encoding dominated_test_context precise_guard_problem
    (fun _ => Some FTop) true false = Some (FVal 7).
Proof.
  vm_compute; reflexivity.
Qed.

Example a_guard_does_not_refine_its_own_source :
  refined_fact bool_encoding dominated_test_context precise_guard_problem
    (fun _ => Some FTop) false false = Some FTop.
Proof.
  vm_compute; reflexivity.
Qed.
