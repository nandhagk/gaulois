(** * Computed SSA scalar-evolution client

    The actual count-up program supplies a five-trip arithmetic fixture and valid source inventory.
    For example, its invariant bound five gives an exact trip count and accepted no-wrap evidence.
    Builds on: ExamplesSsaScev and AnalysesScev. *)

From Stdlib Require Import List Bool Arith ZArith NArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsGraph ViewsSsa ViewsSemantics.
From Gaulois.Analyses Require Import AnalysesScev.
From Gaulois.Examples.Ssa Require Import ExamplesSsaScev ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaActivation ExamplesSsaSemantics ExamplesSsaViews.
Import List.ListNotations.
Local Open Scope nat_scope.

Example scev_count_up_trip :
  trip_count count_up_inv 32%positive Unsigned CmpLt count_up_chrec (IVar count_up_n) =
    Some 5%N /\
  nowrap_check 32%positive Unsigned count_up_inv count_up_chrec (IVar count_up_n) 5%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_count_up_instruction_stays :
  stay_arrivals ssa_edge_encoding count_up_loop [SsaEdge 0 1 0] = 0%nat /\
  aenv (count_up_header_zero 5%Z) 1 = Some (VInt W32 0%Z) /\
  aenv (count_up_header_zero 5%Z) 2 = Some (VInt W32 1%Z).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_current_stay_reentry :
  stay_arrivals ssa_edge_encoding count_up_loop
    [SsaEdge 0 1 0; SsaEdge 2 1 0; SsaEdge 2 1 0; SsaEdge 0 1 0; SsaEdge 2 1 0] = 1%nat.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_count_up_stale_comparison :
  aenv (count_up_header_one 1%Z) 4 = Some (VInt W32 1%Z) /\
  aenv (count_up_header_one 1%Z) 3 = Some (VInt W32 1%Z) /\
  ~ test_holds 32%positive Unsigned CmpLt 1 1.
Proof.
  vm_compute; split; [reflexivity|]; split; [reflexivity|discriminate].
Qed.

Example scev_count_up_missing_options :
  read_args (aenv (count_up_start 0%Z)) [3] = None /\
  bind_params (aenv (count_up_start 0%Z)) [(3, TyI32)] [] = None /\
  aenv (count_up_start 0%Z) 3 = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_count_up_single_body_ingress :
  filter (fun e =>
    negb (lbody count_up_loop (Graph.source (cfg (base (lssa count_up_loop))) e)) &&
      lbody count_up_loop (Graph.target (cfg (base (lssa count_up_loop))) e))
    (edges_of (cfg (base (lssa count_up_loop)))) = [SsaEdge 0 1 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_count_up_source_inventory :
  wf_check count_up = true /\ length (values_of count_up 0) = 6 /\
  forallb (fun x => existsb (Nat.eqb x) count_up_inventory) (values_of count_up 0) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_count_up_actual_header_values :
  aenv (count_up_header_zero 5%Z) 3 = Some (VInt W32 0%Z) /\
  aenv (count_up_header_one 5%Z) 3 = Some (VInt W32 1%Z) /\
  aenv count_up_zero_exit 3 = Some (VInt W32 0%Z).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
