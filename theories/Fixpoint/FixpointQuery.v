(** * Observable query trees

    Queries return values, read unknowns and emit side contributions.
    For example, [Ask x (fun a => Side y a (Ret a))] copies a read into a contribution.
    Builds on: Stdlib lists. *)

From Stdlib Require Import List.
Import List.ListNotations.

Module Query.

(** A query exposes its reads and side contributions as tree constructors. *)
Inductive t (X A : Type) : Type :=
  | Ret (a : A)
  | Ask (x : X) (k : A -> t X A)
  | Side (x : X) (a : A) (q : t X A).

Arguments Ret {X A}.
Arguments Ask {X A}.
Arguments Side {X A}.

(** Evaluation ignores the side trace and returns the final value. *)
Fixpoint eval {X A} (q : t X A) (s : X -> A) : A :=
  match q with
  | Ret a => a
  | Ask x k => eval (k (s x)) s
  | Side _ _ q' => eval q' s
  end.

(** The read trace retains read order and repetitions. *)
Fixpoint reads {X A} (q : t X A) (s : X -> A) : list X :=
  match q with
  | Ret _ => []
  | Ask x k => x :: reads (k (s x)) s
  | Side _ _ q' => reads q' s
  end.

(** The contribution trace retains contribution order and repetitions. *)
Fixpoint sides {X A} (q : t X A) (s : X -> A) : list (X * A) :=
  match q with
  | Ret _ => []
  | Ask x k => sides (k (s x)) s
  | Side x a q' => (x, a) :: sides q' s
  end.

(** A single traversal returns the value and both observable traces. *)
Fixpoint run {X A} (q : t X A) (s : X -> A) : A * list X * list (X * A) :=
  match q with
  | Ret a => (a, [], [])
  | Ask x k =>
    let '(a, rs, ss) := run (k (s x)) s in (a, x :: rs, ss)
  | Side x a q' =>
    let '(r, rs, ss) := run q' s in (r, rs, (x, a) :: ss)
  end.

End Query.
Import Query.

(** Read a list in order and pass its values to the continuation. *)
Fixpoint ask_all {X A} (xs : list X) (k : list A -> Query.t X A) : Query.t X A :=
  match xs with
  | [] => k []
  | x :: xs' => Query.Ask x (fun a => ask_all xs' (fun vs => k (a :: vs)))
  end.

(** Emit a list of contributions before the continuation. *)
Fixpoint side_all {X A} (l : list (X * A)) (q : Query.t X A) : Query.t X A :=
  match l with
  | [] => q
  | (x, a) :: l' => Query.Side x a (side_all l' q)
  end.

Section QueryLaws.
Context {X A : Type}.

(** Agreement on the actual reads determines the result and both traces. *)
Theorem query_determined (q : Query.t X A) (s t : X -> A) :
  (forall x, In x (Query.reads q s) -> s x = t x) ->
  Query.eval q s = Query.eval q t /\ Query.reads q s = Query.reads q t /\
  Query.sides q s = Query.sides q t.
Proof.
  induction q as [a|x k IH|x a q IH]; intro Hagree; cbn in *.
  - auto.
  - assert (Hx : s x = t x) by (apply Hagree; now left).
    rewrite <- Hx.
    destruct (IH (s x)) as [Hv [Hr Hs]].
    + intros y Hy; apply Hagree; now right.
    + rewrite Hv, Hr, Hs; auto.
  - destruct (IH Hagree) as [Hv [Hr Hs]]; rewrite Hv, Hr, Hs; auto.
Qed.

(** Running once agrees exactly with the separate result and trace functions. *)
Theorem run_spec (q : Query.t X A) (s : X -> A) :
  Query.run q s = (Query.eval q s, Query.reads q s, Query.sides q s).
Proof.
  induction q as [a|x k IH|x a q IH]; cbn.
  - reflexivity.
  - rewrite IH; reflexivity.
  - rewrite IH; reflexivity.
Qed.

(** Sequenced reads precede all reads of the instantiated continuation. *)
Theorem ask_all_spec (s : X -> A) (xs : list X) (k : list A -> Query.t X A) :
  Query.reads (ask_all xs k) s = xs ++ Query.reads (k (map s xs)) s /\
  Query.eval (ask_all xs k) s = Query.eval (k (map s xs)) s /\
  Query.sides (ask_all xs k) s = Query.sides (k (map s xs)) s.
Proof.
  revert k; induction xs as [|x xs IH]; intro k; cbn.
  - auto.
  - destruct (IH (fun vs => k (s x :: vs))) as [Hr [Hv Hs]].
    rewrite Hr, Hv, Hs; auto.
Qed.

(** Sequenced contributions precede the continuation's contribution trace. *)
Theorem side_all_spec (q : Query.t X A) (s : X -> A) (l : list (X * A)) :
  Query.eval (side_all l q) s = Query.eval q s /\
  Query.reads (side_all l q) s = Query.reads q s /\
  Query.sides (side_all l q) s = l ++ Query.sides q s.
Proof.
  induction l as [|[x a] l IH]; cbn.
  - auto.
  - destruct IH as [Hv [Hr Hs]]; rewrite Hv, Hr, Hs; auto.
Qed.

End QueryLaws.
