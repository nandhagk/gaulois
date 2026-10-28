(** * Full post-solution checking

    The full checker evaluates each listed constraint once and checks every output.
    For example, a side contribution exceeding its destination rejects the assignment.
    Builds on: FixpointQuery, FixpointSystem and OrderLattice. *)

From Stdlib Require Import List Bool.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.

(** Check every constraint return and side contribution in a single query traversal. *)
Definition check_post {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) : bool :=
  forallb (fun c =>
    let '(v, _, ss) := Query.run (System.rhs S c) s in
    leb L v (s (System.target S c)) && forallb (fun xa => leb L (snd xa) (s (fst xa))) ss)
    (System.constraints S).

(** The full checker decides the post-solution property without static summaries. *)
Theorem check_post_iff {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) :
  check_post L S s = true <-> post_solution L S s.
Proof.
  unfold check_post, post_solution; rewrite forallb_forall.
  split; intros Hcheck c Hc.
  - specialize (Hcheck c Hc); rewrite run_spec in Hcheck; cbn in Hcheck.
    apply andb_true_iff in Hcheck as [Hv Hs]; split; [exact Hv|].
    intros x a Ha; apply (proj1 (forallb_forall _ _) Hs (x, a) Ha).
  - specialize (Hcheck c Hc) as [Hv Hs]; rewrite run_spec; cbn.
    apply andb_true_iff; split; [exact Hv|].
    apply forallb_forall; intros [x a] Ha; exact (Hs x a Ha).
Qed.
