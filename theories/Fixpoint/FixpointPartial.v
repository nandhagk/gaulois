(** * Closed partial solutions

    The checker visits indexed contributors of explored unknowns and checks their dynamic reads.
    For example, a partial assignment that omits a read of an explored target is rejected.
    Builds on: FixpointQuery, FixpointSystem, FixpointIndex and FixpointLeast. *)

From Stdlib Require Import List Bool.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointLeast.

(** Every touched constraint reads inside the explored set and bounds its outputs there. *)
Definition closed_partial {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (E : FinSet.t X) (s : X -> A) : Prop :=
  forall c, In c (System.constraints S) ->
    (FinSet.mem EX (System.target S c) E = true \/
       exists y, In y (side_targets SS c) /\ FinSet.mem EX y E = true) ->
    (forall y, In y (Query.reads (System.rhs S c) s) -> FinSet.mem EX y E = true) /\
    (FinSet.mem EX (System.target S c) E = true ->
       leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true) /\
    forall y a, In (y, a) (Query.sides (System.rhs S c) s) -> FinSet.mem EX y E = true ->
      leb L a (s y) = true.

(** Declared dependencies of every touched constraint belong to the explored set. *)
Definition dependency_closed {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (E : FinSet.t X) : Prop :=
  forall c, In c (System.constraints S) ->
    (FinSet.mem EX (System.target S c) E = true \/
       exists y, In y (side_targets SS c) /\ FinSet.mem EX y E = true) ->
    forall y, In y (deps SS c) -> FinSet.mem EX y E = true.

Definition partial_constraint_check {X C A} (EX : encoding X) (L : lattice A)
  (S : System.t X C A) (E : FinSet.t X) (s : X -> A) (c : C) : bool :=
  let '(v, rs, ss) := Query.run (System.rhs S c) s in
  forallb (fun y => FinSet.mem EX y E) rs &&
  (negb (FinSet.mem EX (System.target S c) E) || leb L v (s (System.target S c))) &&
  forallb (fun ya => negb (FinSet.mem EX (fst ya) E) || leb L (snd ya) (s (fst ya))) ss.

(** Check precisely the indexed contributors of explored unknowns, with one run per visit. *)
Definition check_partial {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (E : FinSet.t X) (m : assignment X A) : bool :=
  forallb (fun x => forallb (partial_constraint_check EX L S E (lookup EX L m))
    (contributors_of EX ix x)) (FinSet.elements E).

Lemma partial_guard_correct (p q : bool) : negb p || q = true <-> (p = true -> q = true).
Proof.
  destruct p, q; cbn; intuition discriminate.
Qed.

Lemma partial_constraint_check_correct {X C A} (EX : encoding X) (L : lattice A)
  (S : System.t X C A) (E : FinSet.t X) (s : X -> A) (c : C) :
  partial_constraint_check EX L S E s c = true <->
  (forall y, In y (Query.reads (System.rhs S c) s) -> FinSet.mem EX y E = true) /\
  (FinSet.mem EX (System.target S c) E = true ->
    leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true) /\
  forall y a, In (y, a) (Query.sides (System.rhs S c) s) -> FinSet.mem EX y E = true ->
    leb L a (s y) = true.
Proof.
  unfold partial_constraint_check; rewrite run_spec; cbn.
  rewrite !andb_true_iff, partial_guard_correct, !forallb_forall.
  split.
  - intros [[Hreads Hvalue] Hsides]; split; [exact Hreads|].
    split; [exact Hvalue|]; intros y a Hin.
    exact (proj1 (partial_guard_correct _ _) (Hsides (y, a) Hin)).
  - intros [Hreads [Hvalue Hsides]]; split; [now split|].
    intros [y a] Hin; apply partial_guard_correct; exact (Hsides y a Hin).
Qed.

Lemma partial_indexed_iff {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (E : FinSet.t X) (c : C) :
  sys_index_laws EX S SS ix -> FinSet.wf EX E ->
  ((exists x, In x (FinSet.elements E) /\ In c (contributors_of EX ix x)) <->
   In c (System.constraints S) /\
     (FinSet.mem EX (System.target S c) E = true \/
       exists y, In y (side_targets SS c) /\ FinSet.mem EX y E = true)).
Proof.
  intros Hindex Hwf; split.
  - intros [x [Hx Hc]]; apply (FinSet.elements_spec EX x E Hwf) in Hx.
    apply (contributors_agree Hindex) in Hc as [Hc [Htarget|Hside]]; split; [exact Hc| |exact Hc|].
    + left; now rewrite Htarget.
    + right; exists x; now split.
  - intros [Hc [Htarget|[x [Hside Hx]]]].
    + exists (System.target S c); split.
      * apply (FinSet.elements_spec EX _ E Hwf); exact Htarget.
      * apply (contributors_agree Hindex); split; [exact Hc|now left].
    + exists x; split.
      * apply (FinSet.elements_spec EX _ E Hwf); exact Hx.
      * apply (contributors_agree Hindex); split; [exact Hc|now right].
Qed.

Section PartialLaws.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (SS : System.static S).
Variables (ix : sys_index X C) (E : FinSet.t X) (m : assignment X A) (s t l : X -> A).

(** Indexed checking decides closed partial solutions on well-formed explored sets. *)
Theorem check_partial_correct : sys_index_laws EX S SS ix -> FinSet.wf EX E ->
  (check_partial EX L S SS ix E m = true <-> closed_partial EX L S SS E (lookup EX L m)).
Proof.
  intros Hindex Hwf; unfold check_partial, closed_partial; rewrite forallb_forall.
  split.
  - intros Hcheck c Hc Htouch.
    destruct (proj2 (partial_indexed_iff EX S SS ix E c Hindex Hwf) (conj Hc Htouch))
      as [x [Hx Hcx]].
    apply partial_constraint_check_correct.
    exact (proj1 (forallb_forall _ _) (Hcheck x Hx) c Hcx).
  - intros Hpartial x Hx; apply forallb_forall; intros c Hcx.
    apply partial_constraint_check_correct.
    destruct (proj1 (partial_indexed_iff EX S SS ix E c Hindex Hwf)
      (ex_intro _ x (conj Hx Hcx))) as [Hc Htouch].
    exact (Hpartial c Hc Htouch).
Qed.

Definition partial_extension (T : top L) (x : X) : A :=
  if FinSet.mem EX x E then s x else top_value T.

Lemma partial_extension_determined (T : top L) (c : C) :
  closed_partial EX L S SS E s -> In c (System.constraints S) ->
  (FinSet.mem EX (System.target S c) E = true \/
    exists y, In y (side_targets SS c) /\ FinSet.mem EX y E = true) ->
  Query.eval (System.rhs S c) s = Query.eval (System.rhs S c) (partial_extension T) /\
  Query.reads (System.rhs S c) s = Query.reads (System.rhs S c) (partial_extension T) /\
  Query.sides (System.rhs S c) s = Query.sides (System.rhs S c) (partial_extension T).
Proof.
  intros Hpartial Hc Htouch; apply query_determined; intros y Hy.
  unfold partial_extension; rewrite (proj1 (Hpartial c Hc Htouch) y Hy); reflexivity.
Qed.

Lemma partial_extension_post (T : top L) :
  closed_partial EX L S SS E s -> post_solution L S (partial_extension T).
Proof.
  intros Hpartial c Hc; split.
  - destruct (FinSet.mem EX (System.target S c) E) eqn:Htarget.
    + destruct (partial_extension_determined T c Hpartial Hc (or_introl Htarget))
        as [Hvalue _].
      rewrite <- Hvalue; unfold partial_extension; rewrite Htarget.
      exact (proj1 (proj2 (Hpartial c Hc (or_introl Htarget))) Htarget).
    + unfold partial_extension; rewrite Htarget; apply top_greatest.
  - intros y a Hside; destruct (FinSet.mem EX y E) eqn:Hy.
    + assert (Htouch : FinSet.mem EX (System.target S c) E = true \/
        exists x, In x (side_targets SS c) /\ FinSet.mem EX x E = true).
      { right; exists y; split; [|exact Hy].
        apply (System.sides_within SS c (partial_extension T)).
        apply in_map_iff; exists (y, a); now split. }
      destruct (partial_extension_determined T c Hpartial Hc Htouch) as [_ [_ Hsides]].
      rewrite <- Hsides in Hside; unfold partial_extension; rewrite Hy.
      exact (proj2 (proj2 (Hpartial c Hc Htouch)) y a Hside Hy).
    + unfold partial_extension; rewrite Hy; apply top_greatest.
Qed.

(** Extending with top preserves explored values and satisfies every global constraint. *)
Theorem closed_partial_extends (T : top L) : closed_partial EX L S SS E s ->
  exists t, post_solution L S t /\ forall x, FinSet.mem EX x E = true -> t x = s x.
Proof.
  intro Hpartial; exists (partial_extension T); split.
  - exact (partial_extension_post T Hpartial).
  - intros x Hx; unfold partial_extension; now rewrite Hx.
Qed.

(** The least global solution lies below every closed partial solution on its explored set. *)
Theorem closed_partial_above_least (T : top L) :
  closed_partial EX L S SS E s -> least_solution L S l ->
  forall x, FinSet.mem EX x E = true -> leb L (l x) (s x) = true.
Proof.
  intros Hpartial [_ Hleast] x Hx.
  destruct (closed_partial_extends T Hpartial) as [u [Hpost Hagrees]].
  rewrite <- (Hagrees x Hx); exact (Hleast u Hpost x).
Qed.

(** A dependency-closed restriction of a global post-solution is a closed partial solution. *)
Theorem post_solution_closed : post_solution L S t -> dependency_closed EX S SS E ->
  closed_partial EX L S SS E t.
Proof.
  intros Hpost Hclosed c Hc Htouch; destruct (Hpost c Hc) as [Hvalue Hsides].
  split.
  - intros y Hy; apply (Hclosed c Hc Htouch y); exact (System.reads_within SS c t y Hy).
  - split; [intro Htarget; exact Hvalue|].
    intros y a Hside Hy; exact (Hsides y a Hside).
Qed.

End PartialLaws.
