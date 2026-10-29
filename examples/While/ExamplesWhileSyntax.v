(** * While syntax

    A small structured language uses expressions and relative loop jumps.
    For example, [SBreak 0] leaves the innermost loop.
    Builds on: Rocq Stdlib integers. *)

From Stdlib Require Import ZArith.

(** Variables are natural-number identifiers. *)
Definition var : Type := nat.

(** Unary word operators. *)
Inductive unop : Type :=
  | Neg
  | BNot
  | LNot.

(** Binary arithmetic, bitwise, shift and comparison operators. *)
Inductive binop : Type :=
  | Add
  | Sub
  | Mul
  | And
  | Or
  | Xor
  | Shl
  | ShrU
  | ShrS
  | Eq
  | Ne
  | LtU
  | LeU
  | LtS
  | LeS.

(** Expressions combine variables and integer constants with word operators. *)
Inductive expr : Type :=
  | EConst (w : Z)
  | EVar (x : var)
  | EUn (o : unop) (e : expr)
  | EBin (o : binop) (e1 e2 : expr).

(** Statements include structured loops and observable output. *)
Inductive stmt : Type :=
  | SSkip
  | SAssign (x : var) (e : expr)
  | SSeq (s1 s2 : stmt)
  | SIf (c : expr) (s1 s2 : stmt)
  | SLoop (s : stmt)
  | SBreak (n : nat)
  | SContinue (n : nat)
  | SOutput (e : expr).
