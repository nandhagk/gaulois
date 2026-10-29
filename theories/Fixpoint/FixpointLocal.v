(** * Checked demand-driven local solving

    An indexed dependency traversal seeds the existing engine with just the local contributors.
    For example, asking for one member of a cycle discovers the other members before iteration.
    Builds on: FixpointPartial, FixpointIndex and FixpointWorklist. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointPartial FixpointWorklist.
Import List.ListNotations.

(** A local result supplies an explored region and a finite assignment, both initially untrusted. *)
Record local_result (X A : Type) : Type := LocalResult {
  explored : FinSet.t X;
  values : assignment X A
}.

Arguments LocalResult {X A}.
Arguments explored {X A}.
Arguments values {X A}.

Module LocalClosure.

(** Visited sets suppress repeated expansion of unknowns and constraints, including cycles. *)
Record state (X C : Type) : Type := State {
  unknowns : FinSet.t X;
  constraints : FinSet.t C;
  pending : list (X + C)
}.

Arguments State {X C}.
Arguments unknowns {X C}.
Arguments constraints {X C}.
Arguments pending {X C}.

Inductive outcome (X C : Type) : Type :=
  | Done (region : FinSet.t X) (selected : FinSet.t C)
  | Pending (s : state X C).

Arguments Done {X C}.
Arguments Pending {X C}.

Definition step {X C A} (EX : encoding X) (EC : encoding C) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (s : state X C) : outcome X C :=
  match pending s with
  | [] => Done (unknowns s) (constraints s)
  | inl x :: rest =>
    if FinSet.mem EX x (unknowns s) then Pending (State (unknowns s) (constraints s) rest)
    else Pending (State (FinSet.add EX x (unknowns s)) (constraints s)
      (fold_right (fun c todo => inr c :: todo) rest (contributors_of EX ix x)))
  | inr c :: rest =>
    if FinSet.mem EC c (constraints s) then Pending (State (unknowns s) (constraints s) rest)
    else Pending (State (unknowns s) (FinSet.add EC c (constraints s))
      (fold_right (fun x todo => inl x :: todo) rest (deps SS c)))
  end.

Definition then_walk {X C} (f : state X C -> outcome X C) (o : outcome X C) : outcome X C :=
  match o with
  | Done region selected => Done region selected
  | Pending s => f s
  end.

(** Binary fuel bounds traversal probes and keeps the recursion stack logarithmic in the budget. *)
Fixpoint walk {X C} (next : state X C -> outcome X C) (fuel : positive)
  (s : state X C) : outcome X C :=
  match fuel with
  | xH => next s
  | xO p => then_walk (walk next p) (walk next p s)
  | xI p => then_walk next (then_walk (walk next p) (walk next p s))
  end.

End LocalClosure.
Import LocalClosure.

(** Discover the root dependency closure, then run the declared engine from its contributors. *)
Definition local_solve {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (ix : sys_index X C) (roots : list X) (fuel : positive) : option (local_result X A) :=
  match LocalClosure.walk (LocalClosure.step EX EC S SS ix) fuel
    (LocalClosure.State FinSet.empty FinSet.empty (map (@inl X C) roots)) with
  | LocalClosure.Pending _ => None
  | LocalClosure.Done region selected =>
    let initial := Engine.State Map.empty
      (enqueue EC sch S (FinSet.elements selected) PQueue.empty) Map.empty in
    match loop (step_outcome EX EC L sch st S (Declared SS ix)) fuel initial with
    | FixpointWorklist.Done m => Some (LocalResult region m)
    | FixpointWorklist.Pending _ => None
    end
  end.

(** Normalize the producer's region, check its partial solution, and require every root. *)
Definition local_checked {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (st : strategy) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (roots : list X) (fuel : positive) : option (local_result X A) :=
  match local_solve EX EC L sch st S SS ix roots fuel with
  | Some r =>
    let E := FinSet.of_list EX (FinSet.elements (explored r)) in
    if check_partial EX L S SS ix E (values r) && forallb (fun x => FinSet.mem EX x E) roots
    then Some (LocalResult E (values r)) else None
  | None => None
  end.

(** Accepted local results form well-formed closed partial solutions that cover every root. *)
Theorem local_checked_sound {X C A} (EX : encoding X) (L : lattice A)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
  (EC : encoding C) (sch : scheduler X) (st : strategy)
  (roots : list X) (fuel : positive) (r : local_result X A) :
  sys_index_laws EX S SS ix -> local_checked EX EC L sch st S SS ix roots fuel = Some r ->
  FinSet.wf EX (explored r) /\
  closed_partial EX L S SS (explored r) (lookup EX L (values r)) /\
  forall x, In x roots -> FinSet.mem EX x (explored r) = true.
Proof.
  intros Hindex Hresult; unfold local_checked in Hresult.
  destruct (local_solve EX EC L sch st S SS ix roots fuel) as [candidate|] eqn:Hsolve;
    [|discriminate].
  set (E := FinSet.of_list EX (FinSet.elements (explored candidate))) in *.
  destruct (check_partial EX L S SS ix E (values candidate) &&
    forallb (fun x => FinSet.mem EX x E) roots) eqn:Htest; [|discriminate].
  inversion Hresult; subst r; cbn.
  assert (Hwf : FinSet.wf EX E) by (apply FinSet.wf_fold_add, Map.wf_empty).
  apply andb_true_iff in Htest as [Hpartial Hroots]; split; [exact Hwf|]; split.
  - exact (proj1 (check_partial_correct EX L S SS ix E (values candidate) Hindex Hwf) Hpartial).
  - exact (proj1 (forallb_forall _ _) Hroots).
Qed.
