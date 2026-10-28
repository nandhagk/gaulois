(** * Word expressions

    Expressions evaluate variables, constants and operator applications with normalized values.
    For example, an eight-bit constant 260 evaluates to the word 4.
    Builds on: BitsWord and BitsOp. *)

From Stdlib Require Import ZArith List.
From Gaulois.Bits Require Import BitsWord BitsOp.
Import List.ListNotations.

Open Scope Z_scope.

Scheme All for list.

Module Bits.

(** Expressions have variables, width-tagged constants and lists of operator arguments. *)
Inductive expr : Type :=
  | Var (i : nat)
  | Const (w : width) (z : Z)
  | App (o : op) (args : list expr).

(** Evaluation wraps variables and constants and propagates operator shape failures. *)
Fixpoint eval (env : nat -> word) (e : expr) : option word :=
  match e with
  | Var i => Some (fst (env i), wrap (fst (env i)) (snd (env i)))
  | Const w z => Some (w, wrap w z)
  | App o args =>
    match (fix go (es : list expr) : option (list word) :=
      match es with
      | [] => Some []
      | e :: rest =>
        match eval env e, go rest with
        | Some x, Some xs => Some (x :: xs)
        | _, _ => None
        end
      end) args with
    | Some xs => eval_op o xs
    | None => None
    end
  end.

(** Argument evaluation preserves order and propagates the first failed argument. *)
Definition eval_args (env : nat -> word) (es : list expr) : option (list word) :=
  (fix go (es : list expr) : option (list word) :=
    match es with
    | [] => Some []
    | e :: rest =>
      match eval env e, go rest with
      | Some x, Some xs => Some (x :: xs)
      | _, _ => None
      end
    end) es.

(** A list environment gives the one-bit zero word for missing entries. *)
Definition env_of (xs : list word) : nat -> word :=
  fun i => List.nth i xs (1%positive, 0).

(** The first n variables enumerate an operator's arguments. *)
Definition vars (n : nat) : list expr := List.map Var (List.seq 0 n).

End Bits.
Import Bits.

(** Variables evaluate to their normalized environment entry. *)
Theorem eval_var : forall env i,
  eval env (Var i) = Some (fst (env i), wrap (fst (env i)) (snd (env i))).
Proof.
  reflexivity.
Qed.

(** Constants evaluate to their normalized literal. *)
Theorem eval_const : forall env w z, eval env (Const w z) = Some (w, wrap w z).
Proof.
  reflexivity.
Qed.

(** Applications evaluate their arguments before dispatching the operator. *)
Theorem eval_app : forall o env args, eval env (App o args) =
  match eval_args env args with Some xs => eval_op o xs | None => None end.
Proof.
  reflexivity.
Qed.

(** The empty argument list evaluates successfully. *)
Theorem eval_args_nil : forall env, eval_args env nil = Some nil.
Proof.
  reflexivity.
Qed.

(** Argument-list evaluation follows the head and the remaining arguments. *)
Theorem eval_args_cons : forall env e args, eval_args env (e :: args) =
  match eval env e, eval_args env args with
  | Some x, Some xs => Some (x :: xs)
  | _, _ => None
  end.
Proof.
  reflexivity.
Qed.

(** Every successful expression result is a word. *)
Theorem eval_is_word : forall r env e, eval env e = Some r -> is_word (fst r) (snd r).
Proof.
  intros r env [i|w z|o args] Hresult.
  - rewrite eval_var in Hresult. inversion Hresult. apply wrap_is_word.
  - rewrite eval_const in Hresult. inversion Hresult. apply wrap_is_word.
  - rewrite eval_app in Hresult. destruct (eval_args env args); [|discriminate].
    now apply (eval_op_is_word o l r).
Qed.
