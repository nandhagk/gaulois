(** * Bottom-up summaries over active frames

    Summary constraints bound local steps and lift callee summaries through call sites.
    For example, a recursive call reads its function's own summary in a call row.
    Builds on: ViewsCalls, CollectionsEncoding, OrderLattice and FixpointSystem. *)

From Stdlib Require Import List.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Gaulois.Views Require Import ViewsSemantics ViewsCalls.
Import List.ListNotations.

(** A client supplies the summary lattice, local effects and call-site lifting. *)
Record summary_spec (F P A : Type) : Type := SummarySpec {
  slat : lattice A;
  local : F -> A;
  via_call : P -> F -> A -> A
}.

Arguments SummarySpec {F P A}.
Arguments slat {F P A}.
Arguments local {F P A}.
Arguments via_call {F P A}.

(** Coverage relates a summary to a concrete event-labelled transition. *)
Record step_cover (S O A : Type) : Type := StepCover {
  step_covers : A -> S -> list O -> S -> Prop
}.

Arguments StepCover {S O A}.
Arguments step_covers {S O A}.

(** Summary rows seed a function or lift a resolved callee through one call site. *)
Inductive summary_constraint (F P : Type) : Type :=
  | SLocal (f : F)
  | SCall (p : P) (g : F).

Arguments SLocal {F P}.
Arguments SCall {F P}.

(** Summary row codes agree with the tagged sum of functions and site-function pairs. *)
Definition summary_constraint_encoding {F P} (EF : encoding F) (EP : encoding P) :
    encoding (summary_constraint F P).
Proof.
  refine (Encoding _ (fun c => encode (sum_encoding EF (pair_encoding EP EF))
    (match c with
    | SLocal f => inl f
    | SCall p g => inr (p, g)
    end)) _).
  intros [f|p g] [f'|p' g'] Hcode;
    apply (encode_injective (sum_encoding EF (pair_encoding EP EF))) in Hcode;
    inversion Hcode; reflexivity.
Defined.

(** Local rows precede call rows enumerated in function, site and resolver-list order. *)
Definition summary_system {S F P A} (cv : calls_view S F P) (resolve : P -> list F)
    (sp : summary_spec F P A) : System.t F (summary_constraint F P) A :=
  {| System.constraints := map SLocal (functions cv) ++
       flat_map (fun f => flat_map (fun p => map (SCall p) (resolve p)) (sites_of cv f))
         (functions cv);
     System.target := fun c =>
       match c with
       | SLocal f => f
       | SCall p _ => caller_of cv p
       end;
     System.rhs := fun c =>
       match c with
       | SLocal f => Query.Ret (local sp f)
       | SCall p g => Query.Ask g (fun a => Query.Ret (via_call sp p g a))
       end |}.

(** Summary rows read only their callee and make no side contributions. *)
Definition summary_static {S F P A} (cv : calls_view S F P) (resolve : P -> list F)
    (sp : summary_spec F P A) : System.static (summary_system cv resolve sp).
Proof.
  refine {| System.deps := fun c =>
              match c with
              | SLocal _ => []
              | SCall _ g => [g]
              end;
            System.side_targets := fun _ => [] |}.
  - intros [f|p g] sigma; apply incl_refl.
  - intros [f|p g] sigma; apply incl_refl.
Defined.

(** Local coverage includes locally modeled external activity; calls lift through every frame. *)
Record summary_laws {S O F P A} (m : semantics S O) (cv : calls_view S F P)
    (sp : summary_spec F P A) (sc : step_cover S O A) : Prop := {
  covers_monotone : forall a b s l s', leb (slat sp) a b = true -> step_covers sc a s l s' ->
    step_covers sc b s l s';
  local_covers : forall s l s', reachable_state m s -> step m s l s' ->
    step_covers sc (local sp (here cv s)) s l s';
  call_covers : forall p g a s l s', reachable_state m s ->
    In (caller_of cv p, p) (frames cv s) ->
    step_covers sc a s l s' -> step_covers sc (via_call sp p g a) s l s'
}.

Arguments covers_monotone {S O F P A m cv sp sc}.
Arguments local_covers {S O F P A m cv sp sc}.
Arguments call_covers {S O F P A m cv sp sc}.

Lemma summary_local_bound {S F P A} (cv : calls_view S F P) resolve
    (sp : summary_spec F P A) sigma :
  post_solution (slat sp) (summary_system cv resolve sp) sigma ->
  forall f, In f (functions cv) -> leb (slat sp) (local sp f) (sigma f) = true.
Proof.
  intros Hpost f Hfunction.
  assert (Hrow : In (SLocal f) (System.constraints (summary_system cv resolve sp))).
  { apply in_or_app; left; apply in_map; exact Hfunction. }
  exact (proj1 (Hpost (SLocal f) Hrow)).
Qed.

Lemma summary_call_bound {S F P A} (cv : calls_view S F P) resolve
    (sp : summary_spec F P A) sigma :
  post_solution (slat sp) (summary_system cv resolve sp) sigma ->
  forall f p g, In f (functions cv) -> In p (sites_of cv f) -> In g (resolve p) ->
    leb (slat sp) (via_call sp p g (sigma g)) (sigma (caller_of cv p)) = true.
Proof.
  intros Hpost f p g Hfunction Hsite Htarget.
  assert (Hrow : In (SCall p g) (System.constraints (summary_system cv resolve sp))).
  { apply in_or_app; right; apply in_flat_map; exists f; split; [exact Hfunction|].
    apply in_flat_map; exists p; split; [exact Hsite|apply in_map; exact Htarget]. }
  exact (proj1 (Hpost (SCall p g) Hrow)).
Qed.

(** Lifting along linked suspended frames bounds the same concrete transition at each caller. *)
Lemma summary_frames_cover {S O F P A} (m : semantics S O) (cv : calls_view S F P)
    resolve (sp : summary_spec F P A) (sc : step_cover S O A) sigma s l s' :
  summary_laws m cv sp sc ->
  post_solution (slat sp) (summary_system cv resolve sp) sigma -> reachable_state m s ->
  forall stack g, frames_linked cv resolve g stack -> incl stack (frames cv s) ->
    (forall f, In f (map fst stack) -> In f (functions cv)) ->
    step_covers sc (sigma g) s l s' ->
    forall f, In f (g :: map fst stack) -> step_covers sc (sigma f) s l s'.
Proof.
  intros Hlaws Hpost Hreachable stack; induction stack as [|[caller p] rest IH];
    intros g Hlinked Hstack Hlisted Hcover f Hin.
  - destruct Hin as [<-|[]]; exact Hcover.
  - destruct Hin as [<-|Hin]; [exact Hcover|].
    destruct Hlinked as [Hcaller [Hsite [Htarget Hlinked]]].
    apply (IH caller Hlinked) with (f := f).
    + intros frame Hframe; apply Hstack; right; exact Hframe.
    + intros h Hh; apply Hlisted; right; exact Hh.
    + eapply (covers_monotone Hlaws).
      * rewrite <- Hcaller.
        eapply summary_call_bound; [exact Hpost| |exact Hsite|exact Htarget].
        apply Hlisted; left; reflexivity.
      * apply (call_covers Hlaws p g (sigma g) s l s' Hreachable).
        -- rewrite Hcaller; apply Hstack; left; reflexivity.
        -- exact Hcover.
    + exact Hin.
Qed.

(** Every active function's post-solution covers the step, including all its callee activity. *)
Theorem summary_sound {S O F P A} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (sp : summary_spec F P A) (sc : step_cover S O A) (sigma : F -> A) :
  calls_view_laws m cv resolve -> summary_laws m cv sp sc ->
  post_solution (slat sp) (summary_system cv resolve sp) sigma ->
  forall s l s' f, reachable_state m s -> step m s l s' -> In f (active cv s) ->
    step_covers sc (sigma f) s l s'.
Proof.
  intros Hcalls Hsummary Hpost s l s' f Hreachable Hstep Hin.
  eapply summary_frames_cover with (stack := frames cv s) (g := here cv s).
  - exact Hsummary.
  - exact Hpost.
  - exact Hreachable.
  - eapply reachable_frames_linked; eassumption.
  - apply incl_refl.
  - intros g Hg; apply (frames_listed Hcalls s Hreachable g); right; exact Hg.
  - eapply (covers_monotone Hsummary).
    + eapply summary_local_bound; [exact Hpost|].
      apply (frames_listed Hcalls s Hreachable); left; reflexivity.
    + apply (local_covers Hsummary s l s' Hreachable Hstep).
  - exact Hin.
Qed.
