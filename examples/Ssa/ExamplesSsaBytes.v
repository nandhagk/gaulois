(** * SSA historical bytes and conservative write summaries

    The byte view reads integer bytes of live allocations and retains sites after free.
    For example, a freed block has no readable byte but still has its original allocation site.
    Builds on: ExamplesSsaMemory, ExamplesSsaPointers and AnalysesMemoryBase. *)

From Stdlib Require Import List Bool ZArith Lia.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemory.
From Gaulois.Analyses Require Import AnalysesMemoryBase.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaViews ExamplesSsaMemory ExamplesSsaEffects ExamplesSsaPointers.
Import List.ListNotations.

(** Write nodes conservatively cover every allocation site over the full 64-bit address range. *)
Definition ssa_bytes_view (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
    bytes_view state event full_node full_edge vid nat :=
  let actions := ssa_pointer_action P in
  let ranges := map (fun site => Footprint site 0%Z (2 ^ 64)%Z) (ssa_allocation_sites P) in
  BytesView (ssa_full_view ext P lim)
    (fun n => if ssa_pointer_writes (actions n) then ranges else [])
    (fun s b => option_map msite (mem s b))
    (fun s b o => ssa_pointer_byte s (VPtr b o)).

Lemma ssa_bytes_readable_bounds ext P lim s b o n :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  ssa_pointer_byte s (VPtr b o) = Some n -> (0 <= o < 2 ^ 64)%Z.
Proof.
  intros Hwf Hreach Hbyte.
  destruct (ssa_pointer_readable s b o n Hbyte) as [mb [Hblock Hbounds]].
  destruct (ssa_pointer_memory_reachable ext P lim s Hwf Hreach b mb Hblock)
    as [Hsite Hsize]; lia.
Qed.

Lemma ssa_bytes_changed_bounds ext P lim s tr t b o :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  step_s ext P lim s tr t ->
  ssa_pointer_byte t (VPtr b o) <> ssa_pointer_byte s (VPtr b o) ->
  (0 <= o < 2 ^ 64)%Z.
Proof.
  intros Hwf Hreach Hstep Hchanged.
  destruct (ssa_pointer_byte t (VPtr b o)) as [n|] eqn:Hafter.
  - eapply ssa_bytes_readable_bounds; [exact Hwf| |exact Hafter].
    eapply reachable_state_step; eassumption.
  - destruct (ssa_pointer_byte s (VPtr b o)) as [n|] eqn:Hbefore.
    + eapply ssa_bytes_readable_bounds; eassumption.
    + contradiction.
Qed.

Lemma ssa_bytes_frame ext P lim s tr t b site o :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  step_s ext P lim s tr t ->
  bsite (ssa_bytes_view ext P lim) s b = Some site ->
  byte (ssa_bytes_view ext P lim) t b o <> byte (ssa_bytes_view ext P lim) s b o ->
  covered (writes_at (ssa_bytes_view ext P lim)
    (point (ssa_full_view ext P lim) s)) site o 1.
Proof.
  intros Hwf Hreach Hstep Hsite Hchanged.
  change (option_map msite (mem s b) = Some site) in Hsite.
  change (ssa_pointer_byte t (VPtr b o) <> ssa_pointer_byte s (VPtr b o)) in Hchanged.
  assert (Hbounds : (0 <= o < 2 ^ 64)%Z).
  { eapply ssa_bytes_changed_bounds; eassumption. }
  destruct (mem s b) as [mb|] eqn:Hblock; [|discriminate].
  injection Hsite as Hsite.
  destruct (ssa_pointer_memory_reachable ext P lim s Hwf Hreach b mb Hblock)
    as [Hlisted Hsize].
  rewrite Hsite in Hlisted.
  destruct Hstep; try solve [exfalso; apply Hchanged; reflexivity];
    cbn [ssa_bytes_view writes_at ssa_full_view point full_point stack];
    lazymatch goal with Hat : at_instr P ?frame ?i |- _ =>
      rewrite (ssa_pointer_action_current P frame [] (fun _ => None) 0 (AnInstr i)
        (ssa_current_instr P frame [] (fun _ => None) 0 i Hat))
    end;
    apply ssa_pointer_full_range; assumption.
Qed.

(** The actual SSA transitions preserve historical sites and cover all changed existing bytes. *)
Theorem ssa_bytes_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P -> bytes_laws (ssa_semantics ext P lim) (ssa_bytes_view ext P lim).
Proof.
  intro Hwf; constructor.
  - apply ssa_full_view_laws; exact Hwf.
  - intros s tr t Hstay; exact Hstay.
  - intros s tr t b site Hreach Hstep Hsite.
    eapply full_site_step; [eapply full_memory_fresh_reachable; exact Hreach|exact Hstep|].
    exact Hsite.
  - intros s tr t b site o Hreach Hstep Hsite Hchanged.
    eapply ssa_bytes_frame; eassumption.
Qed.
