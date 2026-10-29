(** * Executable SSA analysis clients

    The clients instantiate the shared engines on SSA instruction points and source values.
    For example, factorial's auxiliary counter is live but has no observable demand.
    Builds on: ExamplesSsaViews, AnalysesLiveness and DomainsConst. *)

From Stdlib Require Import List ZArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderBasic OrderConcrete OrderFlat OrderPointwise.
From Gaulois.Bits Require Import BitsWord.
From Gaulois.Domains Require Import DomainsNumeric DomainsConst.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesDemand.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsAgreement.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaActivation ExamplesSsaViews.
Import List.ListNotations.
Local Open Scope nat_scope.

(** Labels use the shared injective natural-number encoding. *)
Definition label_encoding : encoding label := nat_encoding.

Definition ssa_bop_code (o : bop) : nat :=
  match o with
  | BAdd => 0
  | BSub => 1
  | BMul => 2
  | BDivU => 3
  | BAnd => 4
  | BOr => 5
  | BXor => 6
  | BShl => 7
  | BShrU => 8
  | BEq => 9
  | BLtU => 10
  | BLtS => 11
  end.

Local Lemma ssa_bop_code_injective o p : ssa_bop_code o = ssa_bop_code p -> o = p.
Proof.
  destruct o, p; cbn; intro Heq; discriminate || reflexivity.
Qed.

Definition ssa_cval_code (c : cval) : nat * (nat * Z) :=
  match c with
  | VInt W32 z => (0, (0, z))
  | VInt W64 z => (1, (0, z))
  | VPtr b off => (2, (b, off))
  | VFun f => (3, (f, 0%Z))
  | VF32 bits => (4, (0, bits))
  | VF64 bits => (5, (0, bits))
  end.

Local Lemma ssa_cval_code_injective c d : ssa_cval_code c = ssa_cval_code d -> c = d.
Proof.
  destruct c as [[|] z|b off|f|z|z], d as [[|] z'|b' off'|f'|z'|z'];
    cbn; intro Heq; inversion Heq; reflexivity.
Qed.

Definition ssa_cval_encoding : encoding cval.
Proof.
  pose (E := pair_encoding nat_encoding (pair_encoding nat_encoding Z_encoding)).
  refine (Encoding _ (fun c => encode E (ssa_cval_code c)) _).
  intros c d Heq; apply ssa_cval_code_injective, (encode_injective E); exact Heq.
Defined.

Definition ssa_sop_code (o : sop) : (cval + ((nat * nat) + (nat * nat)))%type :=
  match o with
  | OConst c => inl c
  | OBin w op => inr (inl ((match w with W32 => 0 | W64 => 1 end), ssa_bop_code op))
  | OZext => inr (inr (0, 0))
  | OTrunc => inr (inr (1, 0))
  | OPtrAdd => inr (inr (2, 0))
  | OExt tag => inr (inr (3, tag))
  end.

(** Operation codes preserve tags, integer widths and every concrete constant payload. *)
Definition sop_encoding : encoding sop.
Proof.
  pose (E := sum_encoding ssa_cval_encoding
    (sum_encoding (pair_encoding nat_encoding nat_encoding)
      (pair_encoding nat_encoding nat_encoding))).
  refine (Encoding _ (fun o => encode E (ssa_sop_code o)) _).
  intros [c|w o| | | |tag] [d|w' p| | | |tag'] Heq;
    apply (encode_injective E) in Heq; cbn [ssa_sop_code] in Heq;
    try discriminate; try reflexivity; try (injection Heq as ->; reflexivity).
  destruct w, w'; cbn in Heq; try discriminate;
    injection Heq as Hcode; apply ssa_bop_code_injective in Hcode; subst p; reflexivity.
Defined.

(** The constant client uses the tagged flat integer domain. *)
Definition const_numeric : numeric_domain (tagged (flat Z)) := tagged_domain const_domain.

(** Constant concretisation retains the width tag and canonical word range. *)
Definition const_conc : concretisation (tagged (flat Z)) word := tagged_gamma const_gamma.

(** Raw liveness is the fact returned by the total shared dataflow engine. *)
Definition liveness_at (P : program) (pt : label * nat)
    : live_set var_encoding (ssa_var_view (fun _ _ => None) P 0) :=
  proj1_sig (solve_liveness (pair_encoding label_encoding nat_encoding) ssa_edge_encoding
    var_encoding (ssa_var_view (fun _ _ => None) P 0)) pt.

(** A closed demand permits changing one undemanded value at a reachable common point. *)
Theorem ssa_dead_value_removable (ext : nat -> list cval -> option cval) (P : program) (f : func)
    (d : finite_map var_encoding (dvars (ssa_demand_view ext P f)) bool) (x : vid) (s t : astate) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  demand_closed var_encoding bool_demand (ssa_demand_view ext P f) d ->
  dget var_encoding bool_lattice d x = false ->
  reachable_state (activation ext P f) s -> reachable_state (activation ext P f) t ->
  point (ssa_point_view ext P f) t = point (ssa_point_view ext P f) s ->
  (forall y, y <> x -> aenv s y = aenv t y) ->
  same_behaviour (activation ext P f) (activation_endings ext P f) s
    (activation ext P f) (activation_endings ext P f) t.
Proof.
  intros Hwf Hfunction Hclosed Hdead Hs Ht Hpoint Hsame.
  apply (dead_value_removable (activation ext P f) (activation_endings ext P f)
    (reachable_state (activation ext P f)) var_encoding bool_demand (ssa_demand_view ext P f)
    d x (ssa_demand_view_laws ext P f Hwf Hfunction)).
  - apply reachable_invariant.
  - exact Hclosed.
  - exact Hdead.
  - exact Hs.
  - exact Ht.
  - exact Hpoint.
  - exact Hsame.
Qed.

(** Factorial carries a separate counter whose increments are pure typed additions. *)
Definition factorial_ssa : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32)]
      [IOp 1 (OConst (VInt W32 1)) []; IOp 2 (OConst (VInt W32 0)) []]
      (TJump 1 [1; 0; 2]));
     (1, SBlock [(3, TyI32); (4, TyI32); (5, TyI32)]
      [IOp 6 (OBin W32 BMul) [3; 4];
       IOp 7 (OConst (VInt W32 1)) [];
       IOp 8 (OBin W32 BAdd) [5; 7];
       IOp 9 (OBin W32 BSub) [4; 7];
       IOp 10 (OConst (VInt W32 0)) [];
       IOp 11 (OBin W32 BLtU) [10; 9]]
      (TBr 11 1 [6; 9; 8] 2 [6]));
     (2, SBlock [(12, TyI32)] [IOutput 12] (TRet 12))] TyI32)] 0 [].

(** The auxiliary loop counter is source value five. *)
Definition z_value : vid := 5.

(** The observable accumulator is source value three. *)
Definition p_value : vid := 3.

(** Raw loop liveness is queried before the first loop instruction. *)
Definition loop_header_point : label * nat := (1, 0).
