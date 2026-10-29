(** * Client operator bridges

    An operator bridge connects an independent client evaluator to word expressions.
    For example, a client's successful addition can be represented by a Bits addition.
    Builds on: BitsExpr and BitsWord. *)

From Stdlib Require Import List ZArith.
From Gaulois.Bits Require Import BitsWord BitsExpr.

(** A bridge supplies expressions for supported operators and partial word conversion. *)
Record op_bridge (K C : Type) : Type := OpBridge {
  op_expr : K -> option Bits.expr;
  to_word : C -> option word
}.

Arguments OpBridge {K C}.
Arguments op_expr {K C}.
Arguments to_word {K C}.

(** Successful client results agree with expression evaluation and nonzero truth. *)
Record op_bridge_laws {K C} (br : op_bridge K C)
    (op_eval : K -> list C -> option C) (truth : C -> bool) : Prop := {
  bridge_word : forall c w, to_word br c = Some w -> is_word (fst w) (snd w);
  bridge_eq : forall o cs r e, op_eval o cs = Some r -> op_expr br o = Some e ->
    exists ws wr, Forall2 (fun c w => to_word br c = Some w) cs ws /\
      Bits.eval (fun i => nth i ws (1%positive, 0%Z)) e = Some wr /\
      to_word br r = Some wr;
  bridge_truth : forall c w, to_word br c = Some w -> truth c = negb (Z.eqb (snd w) 0)
}.
