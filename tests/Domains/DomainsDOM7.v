(** * Computed equality and symbolic-numbering boundaries

    These examples exercise class intersection, forgetting and table-backed expression IDs.
    For example, forgetting a class representative keeps its two former classmates equal.
    Builds on: DomainsEquality, DomainsSymbolic and BitsOp. *)

From Stdlib Require Import List PArith ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsTable
  CollectionsUnionFind.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderLift.
From Gaulois.Bits Require Import BitsWord BitsOp.
From Gaulois.Domains Require Import DomainsEquality DomainsSymbolic.
Import List.ListNotations.
Local Open Scope positive_scope.

Definition dom7_top : partition positive_encoding := top_value (partition_top positive_encoding).
Definition dom7_merge x y := partition_union positive_encoding x y.
Definition dom7_test x y p := fst (partition_test positive_encoding x y p).
Definition dom7_forget x p := partition_forget positive_encoding x p.
Definition dom7_123 := dom7_merge 2 3 (dom7_merge 1 2 dom7_top).
Definition dom7_234 := dom7_merge 3 4 (dom7_merge 2 3 dom7_top).

Example dom7_empty_discrete :
  (dom7_test 1 1 dom7_top, dom7_test 1 2 dom7_top) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_bottom_test_and_forget :
  (dom7_test 1 99 Unreached, dom7_forget 1 Unreached) = (true, Unreached).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_transitive_merge :
  (dom7_test 1 3 dom7_123, dom7_test 1 4 dom7_123) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_compressed_test_result :
  let p := snd (partition_test positive_encoding 3 1 dom7_123) in
  (dom7_test 1 3 p, dom7_test 1 4 p) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_reflexive_merge_records_support :
  (dom7_test 1 1 (dom7_merge 1 1 dom7_top),
   dom7_test 1 2 (dom7_merge 1 1 dom7_top)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_intersection_join :
  let p := join (partition_lattice positive_encoding) dom7_123 dom7_234 in
  (dom7_test 2 3 p, dom7_test 1 2 p, dom7_test 3 4 p) = (true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_disjoint_join :
  let p := join (partition_lattice positive_encoding)
    (dom7_merge 1 2 dom7_top) (dom7_merge 3 4 dom7_top) in
  (dom7_test 1 2 p, dom7_test 3 4 p, dom7_test 9 9 p) = (false, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_bottom_join :
  let L := partition_lattice positive_encoding in
  (dom7_test 1 3 (join L Unreached dom7_123),
   dom7_test 1 3 (join L dom7_123 Unreached)) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_forget_representative :
  let p := dom7_forget 1 dom7_123 in
  (dom7_test 2 3 p, dom7_test 1 2 p, dom7_test 1 1 p) = (true, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_forget_nonrepresentative :
  let p := dom7_forget 2 dom7_123 in
  (dom7_test 1 3 p, dom7_test 2 3 p, dom7_test 2 2 p) = (true, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_forget_outside_support :
  (dom7_test 1 3 (dom7_forget 99 dom7_123),
   dom7_test 1 99 (dom7_forget 99 dom7_123)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_forget_empty_and_repeat :
  (dom7_test 1 2 (dom7_forget 1 dom7_top),
   dom7_test 2 3 (dom7_forget 1 (dom7_forget 1 dom7_123))) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

(* This public well-formed forest deliberately has a linear parent chain, not union provenance. *)
Definition dom7_chain_raw : UnionFind.t positive :=
  UnionFind.Forest
    (Map.of_list positive_encoding [(1, 2); (2, 3); (3, 4); (4, 5); (5, 6); (6, 7); (7, 8)])
    (Map.of_list positive_encoding
      [(1, 0%nat); (2, 1%nat); (3, 2%nat); (4, 3%nat);
       (5, 4%nat); (6, 5%nat); (7, 6%nat); (8, 7%nat)]) 7%nat.

Example dom7_chain_wf : UnionFind.wf positive_encoding dom7_chain_raw.
Proof.
  assert (Hparents : Map.wf positive_encoding (UnionFind.parents dom7_chain_raw))
    by apply Map.wf_of_list.
  assert (Hranks : Map.wf positive_encoding (UnionFind.ranks dom7_chain_raw))
    by apply Map.wf_of_list.
  split; [exact Hparents|]; split; [exact Hranks|]; split.
  - intro x; unfold UnionFind.rank_of.
    destruct (Map.get positive_encoding x (UnionFind.ranks dom7_chain_raw)) as [r|]
      eqn:Hget; [|cbn; lia].
    pose proof (Map.elements_complete positive_encoding x r _ Hranks Hget) as Hin.
    vm_compute in Hin.
    repeat destruct Hin as [Hin|Hin]; try contradiction;
      inversion Hin; subst; cbn; lia.
  - intros x y Hget.
    pose proof (Map.elements_complete positive_encoding x y _ Hparents Hget) as Hin.
    vm_compute in Hin.
    repeat destruct Hin as [Hin|Hin]; try contradiction;
      inversion Hin; subst; vm_compute; repeat constructor.
Qed.

Definition dom7_chain : partition positive_encoding :=
  Reached (exist _ dom7_chain_raw dom7_chain_wf).

Example dom7_chain_cached_representatives :
  let cache := partition_prepare positive_encoding
    (UnionFind.keys positive_encoding dom7_chain_raw) dom7_chain_raw in
  (Map.get positive_encoding 1 cache, Map.get positive_encoding 7 cache,
   Map.get positive_encoding 8 cache, partition_cached_representative positive_encoding cache 99) =
  (Some 8, Some 8, Some 8, 99).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_chain_join :
  let p := join (partition_lattice positive_encoding) dom7_chain dom7_123 in
  (dom7_test 1 3 p, dom7_test 1 4 p, dom7_test 8 8 p) = (true, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_chain_forget_root :
  let p := dom7_forget 8 dom7_chain in
  (dom7_test 1 7 p, dom7_test 1 8 p, dom7_test 8 8 p) = (true, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_reverse_inclusion_order :
  let L := partition_lattice positive_encoding in
  (leb L dom7_123 (dom7_merge 1 2 dom7_top),
   leb L (dom7_merge 1 2 dom7_top) dom7_123,
   leb L dom7_123 (dom7_forget 1 dom7_123),
   leb L dom7_top Unreached) = (true, false, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_update_values :
  let s := key_update positive_encoding 2 9 (fun _ => 1) in
  (s 1, s 2, s 3) = (1, 9, 1).
Proof.
  vm_compute; reflexivity.
Qed.

Definition dom7_add12 := expr_key bvadd [1; 2].
Definition dom7_add21 := expr_key bvadd [2; 1].

Example dom7_commutative_interning :
  let '(i, n) := intern dom7_add12 numbering_empty in
  let '(j, n') := intern dom7_add21 n in
  (i, j, next n', Table.size (ids n')) = (1, 1, 2, 1%nat).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_empty_and_prefix_keys :
  let '(i, n1) := intern [] numbering_empty in
  let '(j, n2) := intern [1] n1 in
  let '(k, n3) := intern [1; 2] n2 in
  let '(i', n4) := intern [] n3 in
  (i, j, k, i', next n4, Table.size (ids n4)) = (1, 2, 3, 1, 4, 3%nat).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_noncommutative_order : expr_key bvsub [1; 2] <> expr_key bvsub [2; 1].
Proof.
  vm_compute; discriminate.
Qed.

Example dom7_distinct_operator_codes : expr_key bvadd [1; 2] <> expr_key bvmul [1; 2].
Proof.
  vm_compute; discriminate.
Qed.

Example dom7_duplicate_and_malformed_keys :
  (expr_key bvadd [2; 2], expr_key bvadd [3; 1; 2], expr_key bvadd [],
   expr_key bvnot [3; 1; 2]) =
  (encode op_encoding bvadd :: [2; 2], encode op_encoding bvadd :: [1; 2; 3],
   [encode op_encoding bvadd], encode op_encoding bvnot :: [3; 1; 2]).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_commutative_evaluation :
  let val := fun p => ((8, if Pos.eqb p 1 then 200%Z else 100%Z) : word) in
  (eval_op bvadd (map val [1; 2]), eval_op bvadd (map val [2; 1])) =
  (Some (8, 44%Z), Some (8, 44%Z)).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom7_malformed_evaluation :
  let val := fun _ : positive => ((8, 1%Z) : word) in
  (eval_op bvadd (map val []), eval_op bvadd (map val [1]),
   eval_op bvadd (map val [3; 1; 2])) = (None, None, None).
Proof.
  vm_compute; reflexivity.
Qed.
