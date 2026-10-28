(** * Client bridges to word expressions

    A successful client operation can be interpreted by a word operator or by an expression.
    For example, the direct addition bridge is the expression adding variables zero and one.
    Builds on: BitsWord, BitsOp and BitsExpr. *)

From Stdlib Require Import ZArith List Lia.
From Gaulois.Bits Require Import BitsWord BitsOp BitsExpr.
Import List.ListNotations.
Import Bits.

Open Scope Z_scope.

(** An operator bridge agrees whenever the client operation returns a result. *)
Definition bridge_op {O V} (client_eval : O -> list V -> option V) (to_bits : V -> word)
  (bridge : O -> op) : Prop :=
  forall o xs r, client_eval o xs = Some r ->
    eval_op (bridge o) (List.map to_bits xs) = Some (to_bits r).

(** An expression bridge agrees whenever the client operation returns a result. *)
Definition bridge_expr {O V} (client_eval : O -> list V -> option V) (to_bits : V -> word)
  (bridge : O -> expr) : Prop :=
  forall o xs r, client_eval o xs = Some r ->
    eval (env_of (List.map to_bits xs)) (bridge o) = Some (to_bits r).

Lemma eval_variable_sequence : forall env n start,
  eval_args env (map Var (seq start n)) =
    Some (map (fun i => normalize_word (env i)) (seq start n)).
Proof.
  intros env n. induction n as [|n IH]; intro start.
  - reflexivity.
  - cbn [seq map]. rewrite eval_args_cons, eval_var, IH. reflexivity.
Qed.

Lemma nth_sequence : forall (A : Type) (d : A) xs,
  map (fun i => nth i xs d) (seq 0 (length xs)) = xs.
Proof.
  intros A d xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [length seq map nth]. rewrite <- seq_shift, map_map. cbn. now rewrite IH.
Qed.

Lemma eval_vars_words : forall xs,
  (forall x, In x xs -> is_word (fst x) (snd x)) ->
  eval_args (env_of xs) (vars (length xs)) = Some xs.
Proof.
  intros xs Hwords. unfold vars. rewrite eval_variable_sequence.
  unfold env_of. rewrite <- map_map, nth_sequence.
  f_equal. transitivity (map (fun x : word => x) xs); [|apply map_id].
  apply map_ext_in. intros [w x] Hin. unfold normalize_word. cbn.
  rewrite wrap_id; [reflexivity|exact (Hwords (w, x) Hin)].
Qed.

(** Every operator bridge induces the expression bridge using consecutive argument variables. *)
Theorem bridge_op_expr : forall {O V : Type}
  (client_eval : O -> list V -> option V) (to_bits : V -> word) (bridge : O -> op),
  (forall v, is_word (fst (to_bits v)) (snd (to_bits v))) ->
  bridge_op client_eval to_bits bridge ->
  bridge_expr client_eval to_bits (fun o => App (bridge o) (vars (arity (bridge o)))).
Proof.
  intros O V client_eval to_bits bridge Hwords Hbridge o xs r Hclient.
  specialize (Hbridge o xs r Hclient).
  pose proof (eval_op_arity _ _ _ Hbridge) as Harity.
  rewrite eval_app, <- Harity, eval_vars_words.
  - exact Hbridge.
  - intros x Hin. apply in_map_iff in Hin as [v [<- _]]. apply Hwords.
Qed.
