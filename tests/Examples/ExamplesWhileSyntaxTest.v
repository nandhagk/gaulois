(** * While computation examples

    These examples exercise word operations and structured control flow.
    For example, a jump can cross an inner loop to reach an outer loop.
    Builds on: While syntax, semantics and traced executions. *)

From Stdlib Require Import List ZArith.
From Gaulois.Views Require Import ViewsSemantics.
From Gaulois.Examples.While Require Import ExamplesWhileSyntax ExamplesWhileSemantics.
Import List.ListNotations.

Open Scope Z_scope.

Definition zero_store : store := fun _ => 0.

(** Arithmetic wraps at both ends of the 32-bit range. *)
Example while_wrap_boundaries :
  wrap32 (-1) = 4294967295 /\ eval_bin Add 4294967295 1 = 0 /\
  eval_bin Mul 2147483648 2 = 0.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Signed comparisons and arithmetic shifts use the signed interpretation. *)
Example while_signed_boundaries :
  signed32 2147483647 = 2147483647 /\ signed32 2147483648 = -2147483648 /\
  eval_bin LtS 4294967295 0 = 1 /\ eval_bin LtU 4294967295 0 = 0 /\
  eval_bin ShrS 2147483648 1 = 3221225472 /\ eval_bin Shl 1 32 = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Expressions evaluate through updates and wrap constants. *)
Example while_expression :
  eval_expr (update zero_store 1%nat 7) (EBin Add (EVar 1%nat) (EConst (-1))) = 6.
Proof.
  vm_compute; reflexivity.
Qed.

(** Nested jumps skip sequence and join frames and select the outer loop labels. *)
Example while_nested_jumps :
  jump_cont 2%nat [KJoin; KLoop SSkip; KExit; KSeq SSkip; KLoop (SOutput (EConst 3)); KExit] =
    Some (JRun (SOutput (EConst 3)) [KLoop (SOutput (EConst 3)); KExit]) /\
  jump_cont 3%nat [KJoin; KLoop SSkip; KExit; KSeq SSkip; KLoop SSkip; KExit] = Some (JFin []) /\
  jump_cont 4%nat [KLoop SSkip; KExit; KLoop SSkip; KExit] = None.
Proof.
  vm_compute; split; [reflexivity|split; reflexivity].
Qed.

(** Breaking two nested loops discards their frames and completes the outer loop. *)
Example while_nested_break_step :
  step_w (Run (SBreak 1%nat) [KJoin; KLoop SSkip; KExit; KLoop SSkip; KExit] zero_store)
    [] (WhileFin [] zero_store).
Proof.
  apply w_break. vm_compute; reflexivity.
Qed.

(** Continuing an outer loop discards the inner loop and restarts the outer body. *)
Example while_nested_continue_step :
  step_w (Run (SContinue 1%nat) [KLoop SSkip; KExit; KJoin; KLoop (SOutput (EConst 3)); KExit]
    zero_store) [] (Run (SOutput (EConst 3)) [KLoop (SOutput (EConst 3)); KExit] zero_store).
Proof.
  apply w_continue. vm_compute; reflexivity.
Qed.

(** An output transition emits the evaluated value. *)
Example while_output_step :
  step_w (Run (SOutput (EConst (-1))) [] zero_store) [4294967295] (WhileFin [] zero_store).
Proof.
  change (step_w (Run (SOutput (EConst (-1))) [] zero_store)
    [eval_expr zero_store (EConst (-1))] (WhileFin [] zero_store)).
  constructor.
Qed.

(** A break outside all loops is stuck, rather than a declared ending. *)
Example while_invalid_break_stuck :
  stuck (while_semantics (SBreak 0%nat) (fun _ => True)) while_endings
    (Run (SBreak 0%nat) [] zero_store).
Proof.
  repeat split.
  - intros [events [next Hstep]]. inversion Hstep; subst; discriminate.
  - intros [sigma Hfinal]. discriminate.
  - exact (fun H => H).
  - exact (fun H => H).
Qed.
