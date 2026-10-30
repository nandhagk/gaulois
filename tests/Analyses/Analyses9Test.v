(** * Pointer unification, escape and reachable SSA regressions

    These examples compare concrete executions with independently computed pointer facts.
    For example, a stored dangling pointer is recognized after its future block is allocated.
    Builds on: AnalysesPointsTo and the SSA pointer adapters. *)

From Stdlib Require Import List Bool ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsUnionFind.
From Gaulois.Order Require Import OrderLattice OrderPowerset.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemory.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesPointsTo.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaViews ExamplesSsaBridge
  ExamplesSsaEffects ExamplesSsaMemory ExamplesSsaPointers ExamplesSsaAnalyses.
Import List.ListNotations.
Local Open Scope nat_scope.

(** * Small independent inclusion and shape cases *)

Definition inclusion_ops : list (ptr_op nat nat) :=
  [PAlloc 0 10; PAlloc 1 11; PCopy 2 0; PStore 0 1; PLoad 3 2; PEscape 2].

Definition inclusion_solution := andersen_delta nat_encoding nat_encoding inclusion_ops.
Definition inclusion_classes := steensgaard nat_encoding nat_encoding inclusion_ops.

Example allocation_copy_heap_and_escape :
  map (fun k => FinSet.elements (proj1_sig (inclusion_solution k)))
    [PVal 0; PVal 1; PVal 2; PVal 3; PHeap 10; PHeap 11] =
    [[10]; [11]; [10]; [11]; [11]; []] /\
  FinSet.elements (escaped_sites nat_encoding inclusion_ops inclusion_solution) = [11; 10].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example shape_unification_and_independent_classes :
  may_alias inclusion_classes 0 2 /\ may_alias inclusion_classes 1 3 /\
  ~ may_alias inclusion_classes 0 1.
Proof.
  vm_compute; repeat split; discriminate || reflexivity.
Qed.

Example nontrivial_points_checker_accepts :
  check_post (pts_lattice nat_encoding inclusion_ops)
    (andersen_system nat_encoding nat_encoding inclusion_ops) inclusion_solution = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_heap_contribution_rejected :
  check_post (pts_lattice nat_encoding inclusion_ops)
    (andersen_system nat_encoding nat_encoding inclusion_ops)
    (fun k => match k with
      | PHeap _ => bot (pts_lattice nat_encoding inclusion_ops)
      | _ => inclusion_solution k
      end) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_pointer_inventory :
  FinSet.elements (escaped_sites nat_encoding ([] : list (ptr_op nat nat))
    (andersen_delta nat_encoding nat_encoding [])) = [] /\
  ~ may_alias (steensgaard nat_encoding nat_encoding ([] : list (ptr_op nat nat))) 1 2.
Proof.
  vm_compute; split; [reflexivity|discriminate].
Qed.

Definition shape_ops : list (ptr_op nat nat) :=
  [PAlloc 0 10; PAlloc 1 11; PAlloc 2 12; PAlloc 3 13;
   PCopy 4 0; PCopy 4 1; PStore 0 2; PStore 1 3; PLoad 5 4].

Example unification_merges_dereference_shapes :
  may_alias (steensgaard nat_encoding nat_encoding shape_ops) 2 3 /\
  fmem nat_encoding 13 (andersen_delta nat_encoding nat_encoding shape_ops (PVal 2)) = false /\
  fmem nat_encoding 12 (andersen_delta nat_encoding nat_encoding shape_ops (PVal 3)) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** * Checked concrete stepping

    The evaluator below is used only to construct regression runs. Its soundness theorem connects
    every successful transition to the actual [step_s] relation, with its actual event list. *)

Definition next_bind {A B} (v : option A) (f : A -> option B) : option B :=
  match v with
  | Some a => f a
  | None => None
  end.

Definition pointer_next (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (s : state) : option state :=
  match stack s with
  | [] => None
  | fr :: rest =>
    let same env memory nb := Some (State (advance fr env :: rest) memory nb) in
    let jump dst args := next_bind (read_args (fenv fr) args) (fun cs =>
      next_bind (jump_env P fr dst cs) (fun env =>
        Some (State (enter fr dst env :: rest) (mem s) (next_block s)))) in
    match ssa_current P s with
    | Some (AnInstr (IOp x o args)) => next_bind (read_args (fenv fr) args) (fun cs =>
      next_bind (op_eval ext o cs) (fun v => same (env_set (fenv fr) x v) (mem s) (next_block s)))
    | Some (AnInstr (IAlloc x n)) => match fenv fr n with
      | Some (VInt W64 z) => if next_block s <? max_blocks lim then
        same (env_set (fenv fr) x (VPtr (next_block s) 0%Z))
          (memory_set (mem s) (next_block s) (MBlock (Z.to_nat z) (fun _ => MInt 0%Z) true x))
          (S (next_block s)) else None
      | _ => None
      end
    | Some (AnInstr (IFree p)) => match fenv fr p with
      | Some (VPtr b off) => if Z.eqb off 0 then next_bind (mem s b) (fun mb =>
        if mlive mb then same (fenv fr)
          (memory_set (mem s) b (MBlock (msz mb) (mbytes mb) false (msite mb))) (next_block s)
        else None) else None
      | _ => None
      end
    | Some (AnInstr (ILoad x ty sz p)) => match fenv fr p with
      | Some (VPtr b off) => next_bind (mem s b) (fun mb =>
        next_bind (memory_load ty sz mb off) (fun v =>
          same (env_set (fenv fr) x v) (mem s) (next_block s)))
      | _ => None
      end
    | Some (AnInstr (IStore sz p y)) => match fenv fr p, fenv fr y with
      | Some (VPtr b off), Some v => next_bind (mem s b) (fun mb =>
        next_bind (memory_store sz mb off v) (fun mb' =>
          same (fenv fr) (memory_set (mem s) b mb') (next_block s)))
      | _, _ => None
      end
    | Some (AnInstr (IOutput x)) => next_bind (fenv fr x) (fun _ =>
      same (fenv fr) (mem s) (next_block s))
    | Some (ATerm (TJump dst args)) => jump dst args
    | Some (ATerm (TBr c l1 a1 l2 a2)) => match fenv fr c with
      | Some (VInt W32 z) => if Z.eqb z 0 then jump l2 a2 else jump l1 a1
      | _ => None
      end
    | Some (ATerm (TSwitch c cases d da)) => match fenv fr c with
      | Some (VInt W32 z) => let '(dst, args) := switch_target z cases d da in jump dst args
      | _ => None
      end
    | Some (ATerm (TCall callee args cont)) =>
      next_bind (read_args (fenv fr) args) (fun cs =>
        next_bind (callee_def P (fenv fr) callee) (fun target =>
          let '(f, fd, b) := target in
          next_bind (bind_params (fun _ => None) (bparams b) cs) (fun env =>
            if length (fr :: rest) <? max_frames lim then
              Some (State (SFrame f (fentry fd) 0 env 0 ::
                SFrame (ffunc fr) (flabel fr) (fpc fr) (fenv fr) cont :: rest)
                (mem s) (next_block s)) else None)))
    | Some (ATerm (TRet x)) => next_bind (fenv fr x) (fun v => match rest with
      | [] => same (fenv fr) (mem s) (next_block s)
      | caller :: tail => next_bind (jump_env P caller (fret caller) [v]) (fun env =>
        Some (State (enter caller (fret caller) env :: tail) (mem s) (next_block s)))
      end)
    | None => None
    end
  end.

(** Each computed transition has a derivation in the full SSA semantics. *)
Example pointer_next_sound ext P lim s s' : pointer_next ext P lim s = Some s' ->
  exists tr, step_s ext P lim s tr s'.
Proof.
  destruct s as [[|fr rest] m nb]; [discriminate|].
  unfold pointer_next, next_bind; cbn [stack mem next_block].
  destruct (ssa_current P (State (fr :: rest) m nb)) as [[i|term]|] eqn:Hcurrent;
    [| |discriminate]; pose proof (ssa_current_sound P fr rest m nb _ Hcurrent) as Hat.
  - destruct i as [x o args|x n|p|x ty sz p|sz p y|x]; cbn [next_bind].
    + destruct (read_args (fenv fr) args) as [cs|] eqn:Hread; [|discriminate].
      destruct (op_eval ext o cs) as [v|] eqn:Heval; [|discriminate].
      intro Heq; injection Heq as <-; exists []; eapply SOp; eassumption.
    + destruct (fenv fr n) as [v|] eqn:Hvalue; [|discriminate].
      destruct v as [[|] z| | | |]; try discriminate.
      destruct (nb <? max_blocks lim) eqn:Hlimit; [|discriminate]; apply Nat.ltb_lt in Hlimit.
      intro Heq; injection Heq as <-; exists []; eapply SAlloc; eassumption.
    + destruct (fenv fr p) as [v|] eqn:Hvalue; [|discriminate].
      destruct v as [|b off| | |]; try discriminate.
      destruct (Z.eqb off 0) eqn:Hoff; [|discriminate]; apply Z.eqb_eq in Hoff; subst off.
      destruct (m b) as [mb|] eqn:Hblock; [|discriminate].
      destruct (mlive mb) eqn:Hlive; [|discriminate].
      intro Heq; injection Heq as <-; exists []; eapply SFree; eassumption.
    + destruct (fenv fr p) as [v|] eqn:Hvalue; [|discriminate].
      destruct v as [|b off| | |]; try discriminate.
      destruct (m b) as [mb|] eqn:Hblock; [|discriminate].
      destruct (memory_load ty sz mb off) as [v|] eqn:Hload; [|discriminate].
      intro Heq; injection Heq as <-; exists []; eapply SLoad; eassumption.
    + destruct (fenv fr p) as [pointer|] eqn:Hp; [|discriminate].
      destruct pointer as [|b off| | |]; try discriminate.
      destruct (fenv fr y) as [v|] eqn:Hy; [|discriminate].
      destruct (m b) as [mb|] eqn:Hblock; [|discriminate].
      destruct (memory_store sz mb off v) as [mb'|] eqn:Hstore; [|discriminate].
      intro Heq; injection Heq as <-; exists []; eapply SStore; eassumption.
    + destruct (fenv fr x) as [v|] eqn:Hvalue; [|discriminate].
      intro Heq; injection Heq as <-; exists [EvOut v]; eapply SOutput; eassumption.
  - destruct term as [dst args|c l1 a1 l2 a2|c cases d da|callee args cont|x];
      cbn [next_bind].
    + destruct (read_args (fenv fr) args) as [cs|] eqn:Hread; [|discriminate].
      destruct (jump_env P fr dst cs) as [env|] eqn:Hjump; [|discriminate].
      intro Heq; injection Heq as <-; exists []; eapply SJump; eassumption.
    + destruct (fenv fr c) as [v|] eqn:Hvalue; [|discriminate].
      destruct v as [[|] z| | | |]; try discriminate.
      destruct (Z.eqb z 0) eqn:Hselect;
        destruct (read_args (fenv fr) _) as [cs|] eqn:Hread; try discriminate;
        destruct (jump_env P fr _ cs) as [env|] eqn:Hjump; try discriminate;
        intro Heq; injection Heq as <-; exists [];
        eapply SBr; try eassumption; rewrite Hselect; reflexivity.
    + destruct (fenv fr c) as [v|] eqn:Hvalue; [|discriminate].
      destruct v as [[|] z| | | |]; try discriminate.
      destruct (switch_target z cases d da) as [dst args] eqn:Hselect.
      destruct (read_args (fenv fr) args) as [cs|] eqn:Hread; [|discriminate].
      destruct (jump_env P fr dst cs) as [env|] eqn:Hjump; [|discriminate].
      intro Heq; injection Heq as <-; exists []; eapply SSwitch; eassumption.
    + destruct (read_args (fenv fr) args) as [cs|] eqn:Hread; [|discriminate].
      destruct (callee_def P (fenv fr) callee) as [[[f fd] b]|] eqn:Hcallee; [|discriminate].
      destruct (bind_params (fun _ => None) (bparams b) cs) as [env|] eqn:Hbind;
        [|discriminate].
      destruct (length (fr :: rest) <? max_frames lim) eqn:Hlimit; [|discriminate].
      apply Nat.ltb_lt in Hlimit; intro Heq; injection Heq as <-.
      exists []; eapply SCall; eassumption.
    + destruct (fenv fr x) as [v|] eqn:Hvalue; [|discriminate].
      destruct rest as [|caller tail].
      * intro Heq; injection Heq as <-; exists [EvRet v]; eapply SReturnMain; eassumption.
      * destruct (jump_env P caller (fret caller) [v]) as [env|] eqn:Hjump; [|discriminate].
        intro Heq; injection Heq as <-; exists []; eapply SReturn; eassumption.
Qed.

Fixpoint pointer_run (fuel : positive) ext P lim s : option state :=
  match fuel with
  | xH => pointer_next ext P lim s
  | xO p => next_bind (pointer_run p ext P lim s) (pointer_run p ext P lim)
  | xI p => next_bind (next_bind (pointer_run p ext P lim s) (pointer_run p ext P lim))
      (pointer_next ext P lim)
  end.

(** Every successful binary-fuel regression run preserves actual semantic reachability. *)
Example pointer_run_reachable fuel ext P lim s s' :
  reachable_state (ssa_semantics ext P lim) s -> pointer_run fuel ext P lim s = Some s' ->
  reachable_state (ssa_semantics ext P lim) s'.
Proof.
  revert s s'; induction fuel as [p IH|p IH|]; intros s s' Hreach Hrun;
    cbn [pointer_run] in Hrun.
  - destruct (pointer_run p ext P lim s) as [middle|] eqn:Hfirst; [|discriminate].
    cbn [next_bind] in Hrun.
    destruct (pointer_run p ext P lim middle) as [last|] eqn:Hsecond; [|discriminate].
    destruct (pointer_next_sound ext P lim last s' Hrun) as [tr Hstep].
    eapply reachable_state_step; [eapply IH; [eapply IH; eassumption|exact Hsecond]|exact Hstep].
  - destruct (pointer_run p ext P lim s) as [middle|] eqn:Hfirst; [|discriminate].
    cbn [next_bind] in Hrun; eapply IH; [eapply IH; eassumption|exact Hrun].
  - destruct (pointer_next_sound ext P lim s s' Hrun) as [tr Hstep].
    eapply reachable_state_step; eassumption.
Qed.

Definition pointer_limits : limits := Limits 16 16.

Definition observed_run fuel ext P start : state :=
  match pointer_run fuel ext P pointer_limits start with
  | Some s => s
  | None => start
  end.

(** * Dangling main input recognized by allocation *)

Definition dangling_block := SBlock [(0, TyPtr); (1, TyI64)] [IAlloc 2 1] (TRet 2).
Definition dangling_function := FDef 0 [(0, dangling_block)] TyPtr.
Definition dangling_program := Program [(0, dangling_function)] 0 [].
Definition dangling_env := env_set (env_set (fun _ => None) 0 (VPtr 0 0%Z)) 1 (VInt W64 8%Z).
Definition dangling_start := State [SFrame 0 0 0 dangling_env 0] (fun _ => None) 0.
Definition dangling_after := observed_run 1 no_ext dangling_program dangling_start.

Example dangling_checker : wf_check dangling_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dangling_wf : wf_program no_ext dangling_program.
Proof.
  apply wf_check_sound; [apply ext_respects_nil; reflexivity|exact dangling_checker].
Qed.

Example dangling_initial : initial (ssa_semantics no_ext dangling_program pointer_limits)
    dangling_start.
Proof.
  exists dangling_function, dangling_block, [VPtr 0 0%Z; VInt W64 8%Z], dangling_env.
  repeat split; try reflexivity.
  constructor; [exact I|constructor; [cbn [valid_cval]; lia|constructor]].
Qed.

Example dangling_reachable : reachable_state (ssa_semantics no_ext dangling_program pointer_limits)
    dangling_after.
Proof.
  eapply pointer_run_reachable with (fuel := 1%positive) (s := dangling_start).
  - exists dangling_start, []; split; [exact dangling_initial|constructor].
  - vm_compute; reflexivity.
Qed.

Example dangling_actual_recognition :
  (pts_of (ssa_ptr_view no_ext dangling_program pointer_limits) dangling_start 0,
   pts_of (ssa_ptr_view no_ext dangling_program pointer_limits) dangling_after 0,
   pts_of (ssa_ptr_view no_ext dangling_program pointer_limits) dangling_after 2) =
  (None, Some 2, Some 2) /\
  ssa_ptr_ops dangling_program = [PAlloc 2 2; PAlloc 0 2].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example dangling_actual_solver_sound :
  fmem var_encoding 2
    (andersen_delta var_encoding var_encoding (ssa_ptr_ops dangling_program) (PVal 0)) = true.
Proof.
  apply (proj1 (ssa_andersen_sound no_ext dangling_program pointer_limits _ dangling_wf
    (proj1 (andersen_delta_least _ _ _)) dangling_after dangling_reachable) 0 2).
  vm_compute; reflexivity.
Qed.

Example dangling_actual_steensgaard :
  may_alias (steensgaard var_encoding var_encoding (ssa_ptr_ops dangling_program)) 0 2.
Proof.
  eapply (ssa_steensgaard_sound no_ext dangling_program pointer_limits dangling_wf
    dangling_after 0 2 2 dangling_reachable); vm_compute; reflexivity.
Qed.

(** * Stored dangling fragments, partial writes, overlapping stores and free *)

Definition fragment_block := SBlock [(0, TyI64); (1, TyPtr); (2, TyI32)]
  [IAlloc 3 0; IStore M8 3 1; IAlloc 4 0; ILoad 5 TyPtr M8 3;
   IOp 6 (OConst (VInt W64 4%Z)) []; IOp 7 OPtrAdd [3; 6];
   IStore M1 7 2; IStore M8 7 4; ILoad 8 TyPtr M8 7; IFree 3] (TRet 8).
Definition fragment_function := FDef 0 [(0, fragment_block)] TyPtr.
Definition fragment_program := Program [(0, fragment_function)] 0 [].
Definition fragment_env := env_set
  (env_set (env_set (fun _ => None) 0 (VInt W64 16%Z)) 1 (VPtr 1 0%Z)) 2 (VInt W32 7%Z).
Definition fragment_start := State [SFrame 0 0 0 fragment_env 0] (fun _ => None) 0.
Definition fragment_at fuel := observed_run fuel no_ext fragment_program fragment_start.
Definition fragment_sigma :=
  andersen_delta var_encoding var_encoding (ssa_ptr_ops fragment_program).

Example fragment_checker : wf_check fragment_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example fragment_wf : wf_program no_ext fragment_program.
Proof.
  apply wf_check_sound; [apply ext_respects_nil; reflexivity|exact fragment_checker].
Qed.

Example fragment_initial : initial (ssa_semantics no_ext fragment_program pointer_limits)
    fragment_start.
Proof.
  exists fragment_function, fragment_block,
    [VInt W64 16%Z; VPtr 1 0%Z; VInt W32 7%Z], fragment_env.
  repeat split; try reflexivity.
  constructor; [cbn [valid_cval]; lia|constructor; [exact I|]].
  constructor; [cbn [valid_cval]; lia|constructor].
Qed.

Example fragment_runs_succeed :
  map (fun fuel => option_map full_point
    (pointer_run fuel no_ext fragment_program pointer_limits fragment_start))
    [1%positive; 2%positive; 3%positive; 4%positive; 7%positive; 8%positive;
      9%positive; 10%positive] =
  map (@Some full_node) [(0, 0, 1); (0, 0, 2); (0, 0, 3); (0, 0, 4);
    (0, 0, 7); (0, 0, 8); (0, 0, 9); (0, 0, 10)].
Proof.
  vm_compute; reflexivity.
Qed.

Example fragment_after_store_reachable :
  reachable_state (ssa_semantics no_ext fragment_program pointer_limits) (fragment_at 2).
Proof.
  eapply pointer_run_reachable with (fuel := 2%positive) (s := fragment_start).
  - exists fragment_start, []; split; [exact fragment_initial|constructor].
  - vm_compute; reflexivity.
Qed.

Example fragment_after_recognition_reachable :
  reachable_state (ssa_semantics no_ext fragment_program pointer_limits) (fragment_at 3).
Proof.
  eapply pointer_run_reachable with (fuel := 3%positive) (s := fragment_start).
  - exists fragment_start, []; split; [exact fragment_initial|constructor].
  - vm_compute; reflexivity.
Qed.

Example fragment_after_partial_reachable :
  reachable_state (ssa_semantics no_ext fragment_program pointer_limits) (fragment_at 7).
Proof.
  eapply pointer_run_reachable with (fuel := 7%positive) (s := fragment_start).
  - exists fragment_start, []; split; [exact fragment_initial|constructor].
  - vm_compute; reflexivity.
Qed.

Example fragment_after_free_reachable :
  reachable_state (ssa_semantics no_ext fragment_program pointer_limits) (fragment_at 10).
Proof.
  eapply pointer_run_reachable with (fuel := 10%positive) (s := fragment_start).
  - exists fragment_start, []; split; [exact fragment_initial|constructor].
  - vm_compute; reflexivity.
Qed.

Example stored_dangling_recognition :
  (heap_pts (ssa_ptr_view no_ext fragment_program pointer_limits) (fragment_at 2) 3 4 -> False) /\
  heap_pts (ssa_ptr_view no_ext fragment_program pointer_limits) (fragment_at 3) 3 4.
Proof.
  split.
  - intros [c [v [a [a' [Hloc [Hsite [Hheld [Hloc' Hsite']]]]]]]].
    destruct a'; vm_compute in Hsite'; discriminate.
  - exists (VPtr 0 0%Z), (VPtr 1 0%Z), 0, 1; vm_compute; repeat split; reflexivity.
Qed.

Example individual_partial_fragment_retained :
  rel_heap (ssa_rel_ptr_view fragment_program) (fragment_at 7) 3 4 /\
  held (ssa_ptr_view no_ext fragment_program pointer_limits) (fragment_at 7) (VPtr 0 0%Z) = None.
Proof.
  split.
  - exists 0, (match mem (fragment_at 7) 0 with Some mb => mb | None => zero_block end),
      0%Z, (VPtr 1 0%Z), 0; vm_compute; repeat split; reflexivity || tauto.
  - vm_compute; reflexivity.
Qed.

Example overlapping_store_and_load :
  (held (ssa_ptr_view no_ext fragment_program pointer_limits) (fragment_at 8) (VPtr 0 0%Z),
   held (ssa_ptr_view no_ext fragment_program pointer_limits) (fragment_at 8) (VPtr 0 4%Z),
   pval (ssa_ptr_view no_ext fragment_program pointer_limits) (fragment_at 9) 8) =
  (None, Some (VPtr 1 0%Z), Some (VPtr 1 0%Z)).
Proof.
  vm_compute; reflexivity.
Qed.

Example freed_fragments_and_historical_site :
  rel_heap (ssa_rel_ptr_view fragment_program) (fragment_at 10) 3 4 /\
  (loc_site (ssa_mem_view no_ext fragment_program pointer_limits) (fragment_at 10) 0,
   held (ssa_ptr_view no_ext fragment_program pointer_limits) (fragment_at 10) (VPtr 0 4%Z),
   pbyte (ssa_ptr_view no_ext fragment_program pointer_limits) (fragment_at 10) (VPtr 0 15%Z)) =
  (Some 3, None, None).
Proof.
  split.
  - exists 0, (match mem (fragment_at 10) 0 with Some mb => mb | None => zero_block end),
      4%Z, (VPtr 1 0%Z), 0; vm_compute; repeat split; reflexivity || tauto.
  - vm_compute; reflexivity.
Qed.

Example fragment_solver_and_distinct_allocation_results :
  map (fun k => map (fun t => fmem var_encoding t (fragment_sigma k)) [3; 4])
    [PVal 1; PVal 3; PVal 4; PVal 5; PVal 7; PVal 8; PHeap 3] =
    [[true; true]; [true; false]; [false; true]; [true; true];
      [true; false]; [true; true]; [true; true]].
Proof.
  vm_compute; reflexivity.
Qed.

Example fresh_retained_and_freed_zero_observations :
  map (fun fuel =>
    (pbyte (ssa_ptr_view no_ext fragment_program pointer_limits) (fragment_at fuel) (VPtr 0 15%Z),
     loc_offset (ssa_mem_view no_ext fragment_program pointer_limits)
       (fragment_at fuel) (VPtr 0 15%Z))) [1%positive; 2%positive; 7%positive; 10%positive] =
  [(Some 0, 15%Z); (Some 0, 15%Z); (Some 0, 15%Z); (None, 15%Z)].
Proof.
  vm_compute; reflexivity.
Qed.

(** * Recursive push and return retain suspended locals and repeated allocation sites *)

Definition recursive_entry := SBlock [(0, TyI64); (1, TyI32)]
  [IAlloc 2 0; IOp 3 (OConst (VInt W32 0%Z)) []] (TBr 1 1 [] 2 []).
Definition recursive_function := FDef 0
  [(0, recursive_entry); (1, SBlock [] [] (TCall (CDirect 0) [0; 3] 3));
   (2, SBlock [] [] (TRet 2)); (3, SBlock [(4, TyPtr)] [IOutput 2] (TRet 4))] TyPtr.
Definition recursive_program := Program [(0, recursive_function)] 0 [].
Definition recursive_env := env_set (env_set (fun _ => None) 0 (VInt W64 8%Z))
  1 (VInt W32 1%Z).
Definition recursive_start := State [SFrame 0 0 0 recursive_env 0] (fun _ => None) 0.
Definition recursive_at fuel := observed_run fuel no_ext recursive_program recursive_start.
Definition suspended_env := env_set (env_set recursive_env 2 (VPtr 0 0%Z)) 3 (VInt W32 0%Z).

Example recursive_checker : wf_check recursive_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example recursive_wf : wf_program no_ext recursive_program.
Proof.
  apply wf_check_sound; [apply ext_respects_nil; reflexivity|exact recursive_checker].
Qed.

Example recursive_initial : initial (ssa_semantics no_ext recursive_program pointer_limits)
    recursive_start.
Proof.
  exists recursive_function, recursive_entry, [VInt W64 8%Z; VInt W32 1%Z], recursive_env.
  repeat split; try reflexivity.
  constructor; [cbn [valid_cval]; lia|constructor; [cbn [valid_cval]; lia|constructor]].
Qed.

Example recursive_push_reachable :
  reachable_state (ssa_semantics no_ext recursive_program pointer_limits) (recursive_at 4).
Proof.
  eapply pointer_run_reachable with (fuel := 4%positive) (s := recursive_start).
  - exists recursive_start, []; split; [exact recursive_initial|constructor].
  - vm_compute; reflexivity.
Qed.

Example recursive_return_reachable :
  reachable_state (ssa_semantics no_ext recursive_program pointer_limits) (recursive_at 8).
Proof.
  eapply pointer_run_reachable with (fuel := 8%positive) (s := recursive_start).
  - exists recursive_start, []; split; [exact recursive_initial|constructor].
  - vm_compute; reflexivity.
Qed.

Example suspended_recursive_local_observed :
  rel_value (ssa_rel_ptr_view recursive_program) (recursive_at 4) 2 2 /\
  pval (ssa_ptr_view no_ext recursive_program pointer_limits) (recursive_at 4) 2 = None /\
  map ffunc (stack (recursive_at 4)) = [0; 0].
Proof.
  split.
  - exists (SFrame 0 1 0 suspended_env 3), (VPtr 0 0%Z).
    split; [right; left; reflexivity|]; vm_compute; repeat split; reflexivity || tauto.
  - vm_compute; split; reflexivity.
Qed.

Example recursive_return_restores_caller_local :
  (pval (ssa_ptr_view no_ext recursive_program pointer_limits) (recursive_at 8) 2,
   pval (ssa_ptr_view no_ext recursive_program pointer_limits) (recursive_at 8) 4,
   full_point (recursive_at 8), next_block (recursive_at 8)) =
  (Some (VPtr 0 0%Z), Some (VPtr 1 0%Z), (0, 3, 0), 2) /\
  map (loc_site (ssa_mem_view no_ext recursive_program pointer_limits) (recursive_at 8)) [0; 1]
    = [Some 2; Some 2].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example recursive_suspended_local_in_solution :
  fmem var_encoding 2 (andersen_delta var_encoding var_encoding (ssa_ptr_ops recursive_program)
    (PVal 2)) = true.
Proof.
  apply (proj1 (relational_andersen_sound (ssa_semantics no_ext recursive_program pointer_limits)
    (ssa_rel_ptr_view recursive_program) var_encoding var_encoding (ssa_ptr_ops recursive_program)
    _ (ssa_rel_ptr_laws no_ext recursive_program pointer_limits _ recursive_wf (fun _ Hin => Hin))
    (proj1 (andersen_delta_least _ _ _)) (recursive_at 4) recursive_push_reachable) 2 2).
  exact (proj1 suspended_recursive_local_observed).
Qed.

Example actual_recursive_escape :
  FinSet.mem var_encoding 2 (escaped_sites var_encoding (ssa_ptr_ops recursive_program)
    (andersen_delta var_encoding var_encoding (ssa_ptr_ops recursive_program))) = true.
Proof.
  apply (proj1 (ssa_escape_sound no_ext recursive_program pointer_limits _ recursive_wf
    (proj1 (andersen_delta_least _ _ _)) (recursive_at 8) 2 2 2 recursive_return_reachable
    ltac:(vm_compute; now left) ltac:(vm_compute; reflexivity))).
Qed.

(** * Pointer constants, extensions, and every ordinary block-binding edge *)

Definition roots_entry := SBlock [(0, TyI64); (1, TyPtr); (2, TyI32)]
  [IAlloc 3 0; IAlloc 4 0; IOp 5 (OConst (VPtr 0 1%Z)) []; IOp 6 (OExt 9) []]
  (TJump 1 [3; 4; 1; 5; 6; 2]).
Definition roots_function := FDef 0
  [(0, roots_entry);
   (1, SBlock [(7, TyPtr); (8, TyPtr); (9, TyPtr); (10, TyPtr); (11, TyPtr); (12, TyI32)] []
     (TBr 12 2 [7; 8; 9; 10; 11] 3 [8; 7; 9; 10; 11]));
   (2, SBlock [(13, TyPtr); (14, TyPtr); (15, TyPtr); (16, TyPtr); (17, TyPtr)] []
     (TSwitch 12 [(1%Z, 4, [13; 14; 15; 16; 17])] 4 [14; 13; 15; 16; 17]));
   (3, SBlock [(18, TyPtr); (19, TyPtr); (20, TyPtr); (21, TyPtr); (22, TyPtr)] []
     (TSwitch 12 [(0%Z, 4, [18; 19; 20; 21; 22])] 4 [19; 18; 20; 21; 22]));
   (4, SBlock [(23, TyPtr); (24, TyPtr); (25, TyPtr); (26, TyPtr); (27, TyPtr)] [] (TRet 23))]
  TyPtr.
Definition roots_program := Program [(0, roots_function)] 0 [(9, ([], TyPtr))].
Definition pointer_ext (_ : nat) (_ : list cval) : option cval := Some (VPtr 1 2%Z).
Definition roots_env (condition : Z) := env_set
  (env_set (env_set (fun _ => None) 0 (VInt W64 8%Z)) 1 (VPtr 0 3%Z))
  2 (VInt W32 condition).
Definition roots_start condition := State [SFrame 0 0 0 (roots_env condition) 0] (fun _ => None) 0.
Definition roots_at fuel condition := observed_run fuel pointer_ext roots_program
  (roots_start condition).
Definition roots_sigma := andersen_delta var_encoding var_encoding (ssa_ptr_ops roots_program).

Example roots_checker : wf_check roots_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example roots_extension_respects : ext_respects pointer_ext roots_program.
Proof.
  intros tag ps r cs v [Heq|[]] Htypes Hvalid Hext.
  injection Heq as <- <- <-; injection Hext as <-; split; reflexivity || exact I.
Qed.

Example roots_wf : wf_program pointer_ext roots_program.
Proof.
  apply wf_check_sound; [exact roots_extension_respects|exact roots_checker].
Qed.

Example roots_initial condition : (0 <= condition < 2 ^ 32)%Z ->
  initial (ssa_semantics pointer_ext roots_program pointer_limits) (roots_start condition).
Proof.
  intro Hcondition; exists roots_function, roots_entry,
    [VInt W64 8%Z; VPtr 0 3%Z; VInt W32 condition], (roots_env condition).
  repeat split; try reflexivity.
  constructor; [cbn [valid_cval]; lia|constructor; [exact I|]].
  constructor; [exact Hcondition|constructor].
Qed.

Example all_parameter_edges_execute :
  map (fun condition => map (fun fuel => full_point (roots_at fuel condition))
    [5%positive; 6%positive; 7%positive]) [0%Z; 1%Z] =
  [[(0, 1, 0); (0, 3, 0); (0, 4, 0)]; [(0, 1, 0); (0, 2, 0); (0, 4, 0)]].
Proof.
  vm_compute; reflexivity.
Qed.

Example branch_zero_reachable :
  reachable_state (ssa_semantics pointer_ext roots_program pointer_limits) (roots_at 7 0%Z).
Proof.
  eapply pointer_run_reachable with (fuel := 7%positive) (s := roots_start 0%Z).
  - exists (roots_start 0%Z), []; split; [apply roots_initial; lia|constructor].
  - vm_compute; reflexivity.
Qed.

Example branch_one_reachable :
  reachable_state (ssa_semantics pointer_ext roots_program pointer_limits) (roots_at 7 1%Z).
Proof.
  eapply pointer_run_reachable with (fuel := 7%positive) (s := roots_start 1%Z).
  - exists (roots_start 1%Z), []; split; [apply roots_initial; lia|constructor].
  - vm_compute; reflexivity.
Qed.

Example pointer_roots_and_parallel_edge_bindings :
  map (fun condition => map (pval (ssa_ptr_view pointer_ext roots_program pointer_limits)
    (roots_at 7 condition)) [23; 24; 25; 26; 27]) [0%Z; 1%Z] =
  [[Some (VPtr 1 0%Z); Some (VPtr 0 0%Z); Some (VPtr 0 3%Z);
      Some (VPtr 0 1%Z); Some (VPtr 1 2%Z)];
   [Some (VPtr 0 0%Z); Some (VPtr 1 0%Z); Some (VPtr 0 3%Z);
      Some (VPtr 0 1%Z); Some (VPtr 1 2%Z)]].
Proof.
  vm_compute; reflexivity.
Qed.

Example static_root_seeds_preserve_independent_allocations :
  map (fun x => map (fun t => fmem var_encoding t (roots_sigma (PVal x))) [3; 4])
    [1; 3; 4; 5; 6; 7; 8; 13; 14; 18; 19; 23] =
  [[true; true]; [true; false]; [false; true]; [true; true]; [true; true];
   [true; false]; [false; true]; [true; false]; [false; true]; [false; true];
   [true; false]; [true; true]].
Proof.
  vm_compute; reflexivity.
Qed.

Example all_static_edge_copies_listed :
  forallb (fun op : ptr_op vid vid => existsb (fun candidate =>
    match op, candidate with
    | PCopy x y, PCopy a b => Nat.eqb x a && Nat.eqb y b
    | _, _ => false
    end) (ssa_ptr_ops roots_program))
    [PCopy 7 3; PCopy 8 4; PCopy 13 7; PCopy 18 8; PCopy 23 13;
     PCopy 23 14; PCopy 23 18; PCopy 23 19] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_sites_block := SBlock [(0, TyPtr)] [] (TRet 0).
Definition empty_sites_function := FDef 0 [(0, empty_sites_block)] TyPtr.
Definition empty_sites_program := Program [(0, empty_sites_function)] 0 [].

Example empty_sites_ssa :
  wf_check empty_sites_program = true /\ ssa_ptr_ops empty_sites_program = [] /\
  ssa_allocation_sites empty_sites_program = [] /\
  FinSet.elements (proj1_sig (andersen_delta nat_encoding nat_encoding
    (ssa_ptr_ops empty_sites_program) (PVal 0))) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example switch_default_reachable :
  reachable_state (ssa_semantics pointer_ext roots_program pointer_limits) (roots_at 7 2%Z) /\
  pval (ssa_ptr_view pointer_ext roots_program pointer_limits) (roots_at 7 2%Z) 23 =
    Some (VPtr 1 0%Z).
Proof.
  split.
  - eapply pointer_run_reachable with (fuel := 7%positive) (s := roots_start 2%Z).
    + exists (roots_start 2%Z), []; split; [apply roots_initial; lia|constructor].
    + vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Definition pointer_call_entry := SBlock [(0, TyPtr); (1, TyI64)]
  [IAlloc 2 1; IOp 3 (OConst (VFun 1)) []]
  (TCall (CIndirect 3 [TyPtr] TyPtr) [2] 1).
Definition pointer_call_caller := FDef 0
  [(0, pointer_call_entry); (1, SBlock [(4, TyPtr)] [] (TRet 4))] TyPtr.
Definition pointer_call_callee := FDef 0
  [(0, SBlock [(5, TyPtr)]
    [IOp 7 (OConst (VInt W64 1%Z)) []; IOp 6 OPtrAdd [5; 7]] (TRet 6))] TyPtr.
Definition pointer_call_program :=
  Program [(0, pointer_call_caller); (1, pointer_call_callee)] 0 [].
Definition pointer_call_start := State [SFrame 0 0 0 dangling_env 0] (fun _ => None) 0.
Definition pointer_call_at fuel := observed_run fuel no_ext pointer_call_program pointer_call_start.

Example pointer_call_checker : wf_check pointer_call_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example pointer_call_initial :
  initial (ssa_semantics no_ext pointer_call_program pointer_limits) pointer_call_start.
Proof.
  exists pointer_call_caller, pointer_call_entry, [VPtr 0 0%Z; VInt W64 8%Z], dangling_env.
  repeat split; try reflexivity.
  constructor; [exact I|constructor; [cbn [valid_cval]; lia|constructor]].
Qed.

Example pointer_argument_and_return_reachable :
  reachable_state (ssa_semantics no_ext pointer_call_program pointer_limits) (pointer_call_at 6) /\
  pval (ssa_ptr_view no_ext pointer_call_program pointer_limits) (pointer_call_at 6) 4 =
    Some (VPtr 0 1%Z) /\
  pop (ssa_ptr_view no_ext pointer_call_program pointer_limits) (pointer_call_at 2) =
    [PCopy 5 2; PEscape 2].
Proof.
  split.
  - eapply pointer_run_reachable with (fuel := 6%positive) (s := pointer_call_start).
    + exists pointer_call_start, []; split; [exact pointer_call_initial|constructor].
    + vm_compute; reflexivity.
  - vm_compute; split; reflexivity.
Qed.

Example pointer_call_solver :
  map (fun x => fmem var_encoding 2 (andersen_delta var_encoding var_encoding
    (ssa_ptr_ops pointer_call_program) (PVal x))) [0; 2; 4; 5; 6] =
  [true; true; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

(** * C59: real footprint coverage and retained-address endpoints *)

Definition zero_model : semantics bool unit := Semantics (fun s => s = false)
  (fun s tr s' => s = false /\ tr = [] /\ s' = true).
Definition zero_graph : Graph.t bool unit := Graph.Make [false] [false; true]
  (fun s => if s then [] else [tt]) (fun _ => false) (fun _ => true).
Definition zero_view : graph_view bool unit bool unit :=
  GraphView zero_graph (fun s => s) (fun _ _ _ _ => True) (fun _ _ _ => False).
Definition zero_memory : mem_view bool unit bool bool unit :=
  MemView (fun _ => None) (fun s _ => Some s) (fun _ _ => Some tt)
    (fun _ (c : bool) => if c then 1%Z else 0%Z).
Definition zero_pointers : ptr_view bool unit bool bool unit :=
  PtrView zero_memory (fun _ _ => None) (fun _ => []) (fun _ _ => None)
    (fun s c => Some (if s then if c then 0 else 1 else 0)).
Definition zero_fp (_ : unit) : list (footprint unit) := [Footprint tt 0%Z 1%Z].
Definition zero_EF := footprint_encoding unit_encoding.
Definition zero_sigma (_ : bool) : written_set zero_EF zero_view zero_fp :=
  finite_clamp zero_EF (write_universe zero_EF zero_view zero_fp)
    (FinSet.of_list zero_EF (zero_fp tt)).

Example zero_graph_laws : graph_view_laws zero_model zero_view.
Proof.
  constructor.
  - constructor.
    + repeat constructor; cbn; intuition discriminate.
    + intros x [<-|[]]; now left.
    + intros [|] [] Hin; cbn in *; intuition discriminate.
    + intros [|] [] Hnode Hin; cbn in *; intuition discriminate.
  - intros s ->; now left.
  - intros s tr s' Hreach Hstep; right; exists tt; exact I.
  - intros s tr s' [] Hreach [-> [-> ->]] Htaken; cbn; auto.
  - intros s tr s' Hreach Hstep Hstay; contradiction.
Qed.

Example zero_initial_reachable : reachable_state zero_model false.
Proof.
  exists false, []; split; [reflexivity|constructor].
Qed.

Example zero_final_reachable : reachable_state zero_model true.
Proof.
  eapply reachable_state_step with (s := false) (l := []);
    [exact zero_initial_reachable|repeat split; reflexivity].
Qed.

Example zero_footprint_endpoints :
  covered (zero_fp tt) tt 0%Z 1 /\ ~ covered (zero_fp tt) tt 1%Z 1 /\
  ~ covered (zero_fp tt) tt (-1)%Z 1.
Proof.
  split.
  - intros k Hk; exists (Footprint tt 0%Z 1%Z); cbn in *.
    split; [now left|split; [reflexivity|lia]].
  - split; intro Hcovered.
    + destruct (Hcovered 1%Z ltac:(cbn; lia)) as [f [[Heq|[]] [Hsite Hbounds]]].
      subst f; cbn in Hbounds; lia.
    + destruct (Hcovered (-1)%Z ltac:(cbn; lia)) as [f [[Heq|[]] [Hsite Hbounds]]].
      subst f; cbn in Hbounds; lia.
Qed.

Example zero_model_laws : zero_laws zero_model zero_view zero_pointers zero_fp.
Proof.
  constructor.
  - exact zero_graph_laws.
  - intros s tr s' Hstay; exact Hstay.
  - intros s c l0 [] n -> Hloc Hsite Hbyte; injection Hbyte as <-; reflexivity.
  - intros s tr s' e c l0 t n Hreach Hstep Htaken Hnone; discriminate.
  - intros s tr s' e c l0 l1 [] Hreach Hstep Htaken Hbefore Hafter Hsite.
    split; reflexivity.
  - intros s tr s' [] [|] l0 [] Hreach [-> [-> ->]] Htaken Hloc Hsite Houtside Hzero
      n Hbyte.
    + injection Hbyte as <-; reflexivity.
    + exfalso; apply Houtside; exact (proj1 zero_footprint_endpoints).
Qed.

Example nontrivial_zero_checker_accepts :
  check_post (finite_powerset_lattice zero_EF (write_universe zero_EF zero_view zero_fp))
    (zero_written_system zero_EF zero_view zero_fp) zero_sigma = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example zero_uncovered_retained_byte :
  (forall n, pbyte zero_pointers true true = Some n -> n = 0) /\
  loc_of zero_memory false true = Some false /\ loc_of zero_memory true true = Some true.
Proof.
  split.
  - intros n Hbyte; eapply (zero_written_sound zero_model zero_EF zero_view zero_pointers zero_fp
      zero_sigma
      zero_model_laws (proj1 (check_post_iff _ _ _) nontrivial_zero_checker_accepts)
      true true true tt n zero_final_reachable).
    + reflexivity.
    + reflexivity.
    + exact (proj1 (proj2 zero_footprint_endpoints)).
    + exact Hbyte.
  - split; reflexivity.
Qed.

Definition moving_memory : mem_view bool unit bool bool unit :=
  MemView (fun _ => None) (fun s _ => Some s) (fun _ _ => Some tt)
    (fun (s : bool) _ => if s then 1%Z else 0%Z).
Definition moving_pointers : ptr_view bool unit bool bool unit :=
  PtrView moving_memory (fun _ _ => None) (fun _ => []) (fun _ _ => None)
    (fun s _ => Some (if s then 1 else 0)).

Example changing_address_countermodel_rejected :
  ~ zero_laws zero_model zero_view moving_pointers zero_fp.
Proof.
  intro Hlaws.
  pose proof (proj2 (z_address Hlaws false [] true tt false false true tt
    zero_initial_reachable ltac:(repeat split; reflexivity) I eq_refl eq_refl eq_refl)) as Hbad.
  discriminate.
Qed.

Example actual_ssa_fresh_zero_field :
  forall n, pbyte (ssa_ptr_view no_ext fragment_program pointer_limits)
    (fragment_at 1) (VPtr 0 15%Z) = Some n -> n = 0.
Proof.
  intros n Hbyte.
  pose proof (ssa_zero_laws no_ext fragment_program pointer_limits fragment_wf) as Hlaws.
  destruct (pointer_next_sound no_ext fragment_program pointer_limits fragment_start
    (fragment_at 1) ltac:(vm_compute; reflexivity)) as [tr Hstep].
  assert (Hreach : reachable_state (ssa_semantics no_ext fragment_program pointer_limits)
    fragment_start).
  { exists fragment_start, []; split; [exact fragment_initial|constructor]. }
  destruct (full_step_covered no_ext fragment_program pointer_limits _ tr _ fragment_wf Hreach
    Hstep) as [e Htaken].
  eapply (z_fresh Hlaws fragment_start tr (fragment_at 1) e (VPtr 0 15%Z) 0 3 n
    Hreach Hstep Htaken); try exact Hbyte; vm_compute; reflexivity.
Qed.

Example actual_ssa_free_address_field :
  loc_site (ssa_mem_view no_ext fragment_program pointer_limits) (fragment_at 9) 0 = Some 3 /\
  loc_offset (ssa_mem_view no_ext fragment_program pointer_limits) (fragment_at 9) (VPtr 0 15%Z)
    = loc_offset (ssa_mem_view no_ext fragment_program pointer_limits)
      (fragment_at 10) (VPtr 0 15%Z).
Proof.
  pose proof (ssa_zero_laws no_ext fragment_program pointer_limits fragment_wf) as Hlaws.
  assert (Hreach : reachable_state (ssa_semantics no_ext fragment_program pointer_limits)
    (fragment_at 9)).
  { eapply pointer_run_reachable with (fuel := 9%positive) (s := fragment_start).
    - exists fragment_start, []; split; [exact fragment_initial|constructor].
    - vm_compute; reflexivity. }
  destruct (pointer_next_sound no_ext fragment_program pointer_limits (fragment_at 9)
    (fragment_at 10) ltac:(vm_compute; reflexivity)) as [tr Hstep].
  destruct (full_step_covered no_ext fragment_program pointer_limits _ tr _ fragment_wf Hreach
    Hstep) as [e Htaken].
  exact (z_address Hlaws (fragment_at 9) tr (fragment_at 10) e (VPtr 0 15%Z) 0 0 3
    Hreach Hstep Htaken eq_refl eq_refl eq_refl).
Qed.

Example actual_ssa_retained_zero_field :
  forall n, pbyte (ssa_ptr_view no_ext fragment_program pointer_limits)
    (fragment_at 5) (VPtr 0 15%Z) = Some n -> n = 0.
Proof.
  intros n Hbyte.
  pose proof (ssa_zero_laws no_ext fragment_program pointer_limits fragment_wf) as Hlaws.
  assert (Hreach : reachable_state (ssa_semantics no_ext fragment_program pointer_limits)
    (fragment_at 4)).
  { eapply pointer_run_reachable with (fuel := 4%positive) (s := fragment_start).
    - exists fragment_start, []; split; [exact fragment_initial|constructor].
    - vm_compute; reflexivity. }
  destruct (pointer_next_sound no_ext fragment_program pointer_limits (fragment_at 4)
    (fragment_at 5) ltac:(vm_compute; reflexivity)) as [tr Hstep].
  destruct (full_step_covered no_ext fragment_program pointer_limits _ tr _ fragment_wf Hreach
    Hstep) as [e Htaken].
  eapply (z_kept Hlaws (fragment_at 4) tr (fragment_at 5) e (VPtr 0 15%Z) 0 3
    Hreach Hstep Htaken eq_refl eq_refl); [| |exact Hbyte].
  - destruct (view_taken_edge _ _ _ _ _ _
      (ssa_full_view_laws no_ext fragment_program pointer_limits fragment_wf)
      Hreach Hstep Htaken) as [_ [Hsource Htarget]].
    change (fsrc e = full_point (fragment_at 4)) in Hsource.
    unfold ssa_footprints; rewrite Hsource.
    change (~ covered [] 3 15%Z 1).
    intros Hcovered; destruct (Hcovered 15%Z ltac:(cbn; lia)) as [f [Hfalse Hrest]].
    exact Hfalse.
  - intros k Hread; vm_compute in Hread; injection Hread as <-; reflexivity.
Qed.

Definition empty_sites_env := env_set (fun _ => None) 0 (VPtr 99 0%Z).
Definition empty_sites_start := State [SFrame 0 0 0 empty_sites_env 0] (fun _ => None) 0.

Example empty_sites_initial :
  initial (ssa_semantics no_ext empty_sites_program pointer_limits) empty_sites_start.
Proof.
  exists empty_sites_function, empty_sites_block, [VPtr 99 0%Z], empty_sites_env.
  repeat split; try reflexivity; constructor; [exact I|constructor].
Qed.

Example empty_inventory_actual_return :
  let after := observed_run 1 no_ext empty_sites_program empty_sites_start in
  reachable_state (ssa_semantics no_ext empty_sites_program pointer_limits) after /\
  pval (ssa_ptr_view no_ext empty_sites_program pointer_limits) after 0 = Some (VPtr 99 0%Z) /\
  pts_of (ssa_ptr_view no_ext empty_sites_program pointer_limits) after 0 = None.
Proof.
  cbn zeta; split.
  - eapply pointer_run_reachable with (fuel := 1%positive) (s := empty_sites_start).
    + exists empty_sites_start, []; split; [exact empty_sites_initial|constructor].
    + vm_compute; reflexivity.
  - vm_compute; split; reflexivity.
Qed.

Example zero_written_and_uncovered_values_differ :
  (pbyte zero_pointers true false, pbyte zero_pointers true true) = (Some 1, Some 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example omitted_write_footprint_rejected :
  check_post (finite_powerset_lattice zero_EF (write_universe zero_EF zero_view zero_fp))
    (zero_written_system zero_EF zero_view zero_fp)
    (fun _ => finite_clamp zero_EF (write_universe zero_EF zero_view zero_fp) FinSet.empty) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example escape_closure_excludes_disconnected_allocation :
  let ops : list (ptr_op nat nat) :=
    [PAlloc 0 10; PAlloc 1 11; PAlloc 2 12; PStore 0 1; PEscape 0] in
  map (fun t => FinSet.mem nat_encoding t
    (escaped_sites nat_encoding ops (andersen_delta nat_encoding nat_encoding ops))) [10; 11; 12]
    = [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.
