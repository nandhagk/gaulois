(** * Memory footprint and historical site examples

    These examples exercise signed offsets, inclusive pointer starts and half-open access bytes.
    For example, freeing storage removes its pointer lookup while retaining its allocation site.
    Builds on: ViewsMemory, ViewsSemantics, DomainsFootprint and OrderBasic. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Order Require Import OrderBasic OrderConcrete.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsMemory.
Import List.ListNotations.

Local Open Scope Z_scope.

Inductive memory_phase : Type :=
  | Loading
  | Storing
  | Freeing
  | Freed.

Definition memory_next (s : memory_phase) : option memory_phase :=
  match s with
  | Loading => Some Storing
  | Storing => Some Freeing
  | Freeing => Some Freed
  | Freed => None
  end.

Definition memory_semantics : semantics memory_phase unit :=
  {| initial := fun s => s = Loading;
     step := fun s events s' => events = [] /\ memory_next s = Some s' |}.

Definition memory_view : mem_view memory_phase bool Z unit nat :=
  {| mem_instr := fun s =>
       match s with
       | Loading => Some (MemLoad false (-3) 2)
       | Storing => Some (MemStore true 4 3 false)
       | Freeing => Some (MemFree false)
       | Freed => None
       end;
     loc_of := fun s _ =>
       match s with
       | Freed => None
       | _ => Some tt
       end;
     loc_site := fun _ _ => Some 7%nat;
     loc_offset := fun _ c => c |}.

Definition memory_pointers : pointer_domain bool Z nat :=
  {| ptr_lat := bool_lattice;
     ptr_conc := {| gamma := fun p c => p = true /\ -1 <= c <= 2 |};
     ptr_reach := fun p =>
       if p then [Footprint 7%nat (-1) 2; Footprint 9%nat 4 4] else [] |}.

Definition memory_values (_ : memory_phase) (x : bool) : option Z :=
  Some (if x then -1 else 2).

Example memory_sites_stable : mem_view_laws memory_semantics memory_view.
Proof.
  constructor; intros s events s' l t Hreachable Hstep Hsite; exact Hsite.
Qed.

Example memory_pointer_laws : pointer_domain_laws memory_semantics memory_view memory_pointers.
Proof.
  constructor; intros s p c l t Hreachable [Hp Hoffset] Hlocation Hsite.
  subst p; cbn in Hsite; inversion Hsite; subst t.
  exists (Footprint 7%nat (-1) 2); cbn; auto.
Qed.

Example memory_value_facts : forall s x c, reachable_state memory_semantics s ->
  memory_values s x = Some c -> gamma (ptr_conc memory_pointers) true c.
Proof.
  intros s x c Hreachable Hvalue.
  destruct x; cbn in Hvalue; inversion Hvalue; subst c; cbn; split; try reflexivity; lia.
Qed.

Example memory_loading_reachable : reachable_state memory_semantics Loading.
Proof.
  exists Loading, []; split; [reflexivity|constructor].
Qed.

Example memory_storing_reachable : reachable_state memory_semantics Storing.
Proof.
  eapply reachable_state_step; [exact memory_loading_reachable|].
  cbn; auto.
Qed.

Example memory_free_run : exec memory_semantics Loading [] Freed.
Proof.
  eapply exec_step with (s' := Storing) (l := []) (tr := []); [cbn; auto|].
  eapply exec_step with (s' := Freeing) (l := []) (tr := []); [cbn; auto|].
  eapply exec_step with (s' := Freed) (l := []) (tr := []); [cbn; auto|constructor].
Qed.

Example load_footprint_computes : access_footprint memory_pointers true (-3) 2 =
  [Footprint 7%nat (-4) 1; Footprint 9%nat 1 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example store_footprint_computes : access_footprint memory_pointers true 4 3 =
  [Footprint 7%nat 3 9; Footprint 9%nat 8 11].
Proof.
  vm_compute; reflexivity.
Qed.

Example load_upper_start_covered :
  covered (access_footprint memory_pointers true (-3) 2) 7%nat (-1) 2.
Proof.
  eapply (access_footprint_sound memory_semantics memory_view memory_pointers
    memory_values (fun _ => true) memory_pointer_laws memory_value_facts Loading false
    (-3) 2 2 tt 7%nat).
  - exact memory_loading_reachable.
  - left; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example store_lower_start_covered :
  covered (access_footprint memory_pointers true 4 3) 7%nat 3 3.
Proof.
  eapply (access_footprint_sound memory_semantics memory_view memory_pointers
    memory_values (fun _ => true) memory_pointer_laws memory_value_facts Storing true
    4 3 (-1) tt 7%nat).
  - exact memory_storing_reachable.
  - right; exists false; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example load_excludes_adjacent_byte :
  ~ covered (access_footprint memory_pointers true (-3) 2) 7%nat 1 1.
Proof.
  intro Hcovered.
  destruct (Hcovered 1 ltac:(lia)) as [f [Hin [Hsite Hbyte]]].
  cbn in Hin; destruct Hin as [Heq|[Heq|Hfalse]].
  - subst f; cbn in Hbyte; lia.
  - subst f; discriminate Hsite.
  - exact Hfalse.
Qed.

Example adjacent_footprints_cover_two_bytes :
  covered [Footprint 7%nat 0 1; Footprint 7%nat 1 2] 7%nat 0 2.
Proof.
  intros k Hbyte; cbn in Hbyte.
  destruct (Z_lt_ge_dec k 1) as [Hfirst|Hsecond].
  - exists (Footprint 7%nat 0 1); cbn; intuition lia.
  - exists (Footprint 7%nat 1 2); cbn; intuition lia.
Qed.

Example zero_width_footprint_computes : access_footprint memory_pointers true 0 0 =
  [Footprint 7%nat (-1) 2; Footprint 9%nat 4 4].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_pointer_footprint_computes : access_footprint memory_pointers false 5 8 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example zero_width_covered_without_pointer :
  covered (access_footprint memory_pointers false 5 0) 7%nat 100 0.
Proof.
  intros k Hbyte; cbn in Hbyte; lia.
Qed.

Example empty_pointer_does_not_cover_byte :
  ~ covered (access_footprint memory_pointers false 5 1) 7%nat 100 1.
Proof.
  intro Hcovered.
  destruct (Hcovered 100 ltac:(lia)) as [f [Hfalse _]]; exact Hfalse.
Qed.

Example free_removes_pointer_but_retains_site :
  loc_of memory_view Freed 2 = None /\ loc_site memory_view Freed tt = Some 7%nat.
Proof.
  vm_compute; auto.
Qed.

Example historical_site_persists_through_free : loc_site memory_view Freed tt = Some 7%nat.
Proof.
  eapply (loc_site_preserved memory_semantics memory_view memory_sites_stable
    Loading [] Freed tt 7%nat).
  - exact memory_loading_reachable.
  - exact memory_free_run.
  - reflexivity.
Qed.
