(** * Typed extraction clients

    This client extracts representative collections, graph traversals and constraint solvers.

    For example, an OCaml caller can prepare a graph and run its depth-first search.
    Builds on: Collections, Order, Graph, Fixpoint and Rules. *)

From Stdlib.extraction Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Gaulois.Order Require Import OrderBasic OrderPowerset.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphWto.
From Gaulois.Fixpoint Require Import FixpointCheck FixpointWorklist FixpointTotal FixpointSchedule.
From Gaulois.Rules Require Import RulesSyntax RulesSolve.

Extraction Language OCaml.
Set Extraction Output Directory ".".

(** The finite universe constrains proofs; the lattice's executable operations never inspect it. *)
Extraction Implicit finite_powerset_lattice [3].
Extraction Implicit finite_powerset_top [3].

Extraction "algorithms.ml"
  positive_encoding nat_encoding Trie.get Trie.set Trie.elements
  FinSet.of_list FinSet.elements FinSet.size
  prepare dfs rpo scc wto_total wto_order check_wto
  bool_lattice check_post run_worklist solve_total rpo_scheduler.

(** A separate complete solver closure makes its proof-universe dependency audit explicit. *)
Extraction "rules_solver.ml" solve_program db_holds.
