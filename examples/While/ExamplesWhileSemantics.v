(** * While semantics

    A continuation machine executes structured statements with 32-bit word operations.
    For example, output emits one integer event and an invalid jump gets stuck.
    Builds on: While syntax, word ranges, encodings and traced semantics. *)

From Stdlib Require Import List Arith ZArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Bits Require Import BitsWord.
From Gaulois.Views Require Import ViewsSemantics.
From Gaulois.Examples.While Require Import ExamplesWhileSyntax.
Import List.ListNotations.

Open Scope Z_scope.

(** Reduction modulo the 32-bit word modulus. *)
Definition wrap32 (z : Z) : Z := z mod 4294967296.

(** Signed interpretation of an unsigned 32-bit word. *)
Definition signed32 (z : Z) : Z :=
  if z <? 2147483648 then z else z - 4294967296.

(** Unary operations on word values. *)
Definition eval_un (o : unop) (a : Z) : Z :=
  match o with
  | Neg => wrap32 (-a)
  | BNot => 4294967295 - a
  | LNot => if Z.eqb a 0 then 1 else 0
  end.

(** Binary operations on word values, with shift amounts reduced modulo 32. *)
Definition eval_bin (o : binop) (a b : Z) : Z :=
  match o with
  | Add => wrap32 (a + b)
  | Sub => wrap32 (a - b)
  | Mul => wrap32 (a * b)
  | And => Z.land a b
  | Or => Z.lor a b
  | Xor => Z.lxor a b
  | Shl => wrap32 (Z.shiftl a (b mod 32))
  | ShrU => Z.shiftr a (b mod 32)
  | ShrS => wrap32 (Z.shiftr (signed32 a) (b mod 32))
  | Eq => if Z.eqb a b then 1 else 0
  | Ne => if Z.eqb a b then 0 else 1
  | LtU => if Z.ltb a b then 1 else 0
  | LeU => if Z.leb a b then 1 else 0
  | LtS => if Z.ltb (signed32 a) (signed32 b) then 1 else 0
  | LeS => if Z.leb (signed32 a) (signed32 b) then 1 else 0
  end.

(** A store assigns an integer to each variable. *)
Definition store : Type := var -> Z.

(** Updating one variable leaves all other bindings unchanged. *)
Definition update (sigma : store) (x : var) (z : Z) : store :=
  fun y => if Nat.eqb x y then z else sigma y.

(** Expression evaluation wraps constants and reads variables from the store. *)
Fixpoint eval_expr (sigma : store) (e : expr) : Z :=
  match e with
  | EConst w => wrap32 w
  | EVar x => sigma x
  | EUn o e' => eval_un o (eval_expr sigma e')
  | EBin o e1 e2 => eval_bin o (eval_expr sigma e1) (eval_expr sigma e2)
  end.

(** Continuations record sequencing, joins and loop labels. *)
Inductive wframe : Type :=
  | KSeq (s : stmt)
  | KJoin
  | KLoop (body : stmt)
  | KExit.

(** Machine states distinguish statement entry, loop entry and completion. *)
Inductive config : Type :=
  | Run (s : stmt) (k : list wframe) (sigma : store)
  | Enter (body : stmt) (k : list wframe) (sigma : store)
  | WhileFin (k : list wframe) (sigma : store).

(** A jump either restarts a loop or finishes at an exit. *)
Inductive target_cont : Type :=
  | JRun (s : stmt) (k : list wframe)
  | JFin (k : list wframe).

(** Count loop and exit labels from the innermost frame, skipping other frames. *)
Fixpoint jump_cont (d : nat) (k : list wframe) : option target_cont :=
  match k with
  | [] => None
  | KSeq _ :: rest => jump_cont d rest
  | KJoin :: rest => jump_cont d rest
  | KLoop s :: rest =>
      match d with
      | O => Some (JRun s (KLoop s :: rest))
      | S d' => jump_cont d' rest
      end
  | KExit :: rest =>
      match d with
      | O => Some (JFin rest)
      | S d' => jump_cont d' rest
      end
  end.

(** Each transition emits either no event or one output value. *)
Inductive step_w : config -> list Z -> config -> Prop :=
  | w_skip : forall k sigma, step_w (Run SSkip k sigma) nil (WhileFin k sigma)
  | w_assign : forall x e k sigma,
      step_w (Run (SAssign x e) k sigma) nil (WhileFin k (update sigma x (eval_expr sigma e)))
  | w_output : forall e k sigma,
      step_w (Run (SOutput e) k sigma) [eval_expr sigma e] (WhileFin k sigma)
  | w_seq : forall s1 s2 k sigma,
      step_w (Run (SSeq s1 s2) k sigma) nil (Run s1 (KSeq s2 :: k) sigma)
  | w_if : forall c s1 s2 k sigma,
      step_w (Run (SIf c s1 s2) k sigma) nil
        (Run (if Z.eqb (eval_expr sigma c) 0 then s2 else s1) (KJoin :: k) sigma)
  | w_loop : forall s k sigma, step_w (Run (SLoop s) k sigma) nil (Enter s (KExit :: k) sigma)
  | w_enter : forall s k sigma, step_w (Enter s k sigma) nil (Run s (KLoop s :: k) sigma)
  | w_break : forall n k k' sigma, jump_cont (2 * n + 1)%nat k = Some (JFin k') ->
      step_w (Run (SBreak n) k sigma) nil (WhileFin k' sigma)
  | w_continue : forall n k s k' sigma, jump_cont (2 * n)%nat k = Some (JRun s k') ->
      step_w (Run (SContinue n) k sigma) nil (Run s k' sigma)
  | w_fin_seq : forall s k sigma,
      step_w (WhileFin (KSeq s :: k) sigma) nil (Run s (KJoin :: k) sigma)
  | w_fin_join : forall k sigma, step_w (WhileFin (KJoin :: k) sigma) nil (WhileFin k sigma)
  | w_fin_exit : forall k sigma, step_w (WhileFin (KExit :: k) sigma) nil (WhileFin k sigma)
  | w_fin_loop : forall s k sigma,
      step_w (WhileFin (KLoop s :: k) sigma) nil (Run s (KLoop s :: k) sigma).

(** Initial states run the program with an allowed store. *)
Definition while_semantics (prog : stmt) (init : store -> Prop) : semantics config Z :=
  Semantics (fun c => exists sigma, init sigma /\ c = Run prog nil sigma) step_w.

(** Only completion with an empty continuation is a declared ending. *)
Definition while_endings : endings config :=
  Endings (fun c => exists sigma, c = WhileFin nil sigma) (fun _ => False) (fun _ => False).

(** Every machine state carries its current store. *)
Definition store_of_config (c : config) : store :=
  match c with
  | Run _ _ sigma => sigma
  | Enter _ _ sigma => sigma
  | WhileFin _ sigma => sigma
  end.

(** Word stores contain only unsigned 32-bit values. *)
Definition word_stores : store -> Prop := fun sigma => forall x, is_word 32%positive (sigma x).

(** Variables use the natural-number encoding. *)
Definition var_encoding : encoding var := nat_encoding.
