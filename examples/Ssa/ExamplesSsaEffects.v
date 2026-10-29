(** * Full-machine SSA effects and calls

    These adapters describe the actual heap and the innermost-first machine stack.
    For example, a direct call pushes a resolved function and preserves the heap image.
    Builds on: ExamplesSsaViews, ExamplesSsaTypingProofs, ViewsEffects and ViewsCalls. *)

From Stdlib Require Import List Arith ZArith Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Views Require Import ViewsSemantics ViewsEffects ViewsCalls.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaActivation ExamplesSsaBridge
  ExamplesSsaViews.
Import List.ListNotations.
Local Open Scope nat_scope.

(** Each instruction position, including the terminator, has one prepared action. *)
Definition ssa_action_index (b : ssa_block) : Map.t nat instr_or_term :=
  first_index (ssa_enumerate 0 (map AnInstr (bbody b) ++ [ATerm (bterm b)])).

(** Function, block and instruction indexes are prepared before any state query. *)
Definition ssa_current (P : program) : state -> option instr_or_term :=
  let index := Map.map (fun fd => Map.map ssa_action_index (first_index (blocks fd)))
    (first_index (funcs P)) in
  fun s =>
    match stack s with
    | [] =>
      None
    | fr :: _ =>
      match Map.get nat_encoding (ffunc fr) index with
      | None =>
        None
      | Some bs =>
        match Map.get nat_encoding (flabel fr) bs with
        | None =>
          None
        | Some code =>
          Map.get nat_encoding (fpc fr) code
        end
      end
    end.

(** The heap image includes the fresh-identity counter, and heap agreement fixes the stack. *)
Definition ssa_effects_view (ext : nat -> list cval -> option cval) (P : program)
    (lim : limits) : effects_view state instr_or_term ((nat -> option mblock) * nat) :=
  {| instr_at := ssa_current P;
     heap := fun s => (mem s, next_block s);
     heap_agree := fun s t => stack s = stack t;
     depth := fun s => length (stack s) |}.

Lemma ssa_enumerated_get {A} (xs : list A) start n :
  Map.get nat_encoding (start + n) (first_index (ssa_enumerate start xs)) = nth_error xs n.
Proof.
  revert start n; induction xs as [|x xs IH]; intros start [|n];
    cbn [ssa_enumerate first_index nth_error].
  - apply Map.get_empty.
  - apply Map.get_empty.
  - rewrite Nat.add_0_r; apply Map.get_set_same.
  - rewrite Map.get_set_other by lia.
    replace (start + S n) with (S start + n) by lia; apply IH.
Qed.

Lemma ssa_current_at P fr rest m nb fd b :
  find_func P (ffunc fr) = Some fd -> find_block fd (flabel fr) = Some b ->
  ssa_current P (State (fr :: rest) m nb) =
    nth_error (map AnInstr (bbody b) ++ [ATerm (bterm b)]) (fpc fr).
Proof.
  intros Hf Hb; unfold ssa_current; cbn [stack].
  rewrite Map.get_map; change (Map.get nat_encoding (ffunc fr) (first_index (funcs P)))
    with (find_func P (ffunc fr)); rewrite Hf; cbn [option_map].
  rewrite Map.get_map; change (Map.get nat_encoding (flabel fr) (first_index (blocks fd)))
    with (find_block fd (flabel fr)); rewrite Hb; cbn [option_map].
  unfold ssa_action_index; exact (ssa_enumerated_get _ 0 (fpc fr)).
Qed.

Lemma ssa_current_instr P fr rest m nb i :
  at_instr P fr i -> ssa_current P (State (fr :: rest) m nb) = Some (AnInstr i).
Proof.
  intros [fd [b [Hf [Hb Hnth]]]]; rewrite (ssa_current_at _ _ _ _ _ _ _ Hf Hb).
  rewrite nth_error_app1 by (rewrite length_map; apply nth_error_Some; rewrite Hnth; discriminate).
  rewrite nth_error_map, Hnth; reflexivity.
Qed.

Lemma ssa_current_term P fr rest m nb t :
  at_term P fr t -> ssa_current P (State (fr :: rest) m nb) = Some (ATerm t).
Proof.
  intros [fd [b [Hf [Hb [Hpc Hterm]]]]].
  rewrite (ssa_current_at _ _ _ _ _ _ _ Hf Hb), Hpc, nth_error_app2 by
    (rewrite length_map; lia).
  rewrite length_map, Nat.sub_diag; cbn; rewrite Hterm; reflexivity.
Qed.

(** A present action identifies the actual next instruction or terminator. *)
Lemma ssa_current_sound P fr rest m nb it :
  ssa_current P (State (fr :: rest) m nb) = Some it ->
  match it with
  | AnInstr i =>
    at_instr P fr i
  | ATerm t =>
    at_term P fr t
  end.
Proof.
  unfold ssa_current; cbn [stack]; rewrite Map.get_map.
  change (Map.get nat_encoding (ffunc fr) (first_index (funcs P)))
    with (find_func P (ffunc fr)).
  destruct (find_func P (ffunc fr)) as [fd|] eqn:Hf; cbn [option_map]; [|discriminate].
  rewrite Map.get_map.
  change (Map.get nat_encoding (flabel fr) (first_index (blocks fd)))
    with (find_block fd (flabel fr)).
  destruct (find_block fd (flabel fr)) as [b|] eqn:Hb; cbn [option_map]; [|discriminate].
  unfold ssa_action_index; rewrite (ssa_enumerated_get _ 0 (fpc fr)).
  destruct (lt_dec (fpc fr) (length (bbody b))) as [Hbefore|Hend].
  - rewrite nth_error_app1 by (rewrite length_map; exact Hbefore).
    rewrite nth_error_map; destruct (nth_error (bbody b) (fpc fr)) as [i|] eqn:Hnth;
      cbn [option_map]; [|discriminate].
    intro Heq; injection Heq as <-; exists fd, b; repeat split; assumption.
  - rewrite nth_error_app2 by (rewrite length_map; lia); rewrite length_map.
    destruct (fpc fr - length (bbody b)) as [|offset] eqn:Hoffset;
      cbn [nth_error]; [|destruct offset; discriminate].
    intro Heq; injection Heq as <-; exists fd, b; repeat split; try assumption; lia.
Qed.

(** Suspended callers retain the function and label of the call they are executing. *)
Definition ssa_suspended (s : state) : list (func * call_site) :=
  map (fun fr => (ffunc fr, (ffunc fr, flabel fr))) (tl (stack s)).

Lemma ssa_first_index_map_key {A B} (h : nat -> A -> B) xs key :
  Map.get nat_encoding key
    (first_index (map (fun ka => (fst ka, h (fst ka) (snd ka))) xs)) =
  option_map (h key) (Map.get nat_encoding key (first_index xs)).
Proof.
  induction xs as [|[k a] rest IH]; cbn [map fst snd first_index].
  - rewrite !Map.get_empty; reflexivity.
  - destruct (Nat.eq_dec key k) as [Heq|Hne].
    + subst k; rewrite !Map.get_set_same; reflexivity.
    + rewrite !Map.get_set_other by exact Hne; exact IH.
Qed.

(** Call sites retain their caller tag while filtering blocks in source order. *)
Definition ssa_function_sites (f : func) (fd : fdef) : list call_site :=
  map (fun l => (f, l)) (map fst (filter (fun lb =>
    match bterm (snd lb) with
    | TCall _ _ _ =>
      true
    | _ =>
      false
    end) (blocks fd))).

(** Each function's complete call-site list is indexed once before queries. *)
Definition ssa_calls (ext : nat -> list cval -> option cval) (P : program)
    : calls_view state func call_site :=
  let sites := first_index (map (fun ff =>
    (fst ff, ssa_function_sites (fst ff) (snd ff))) (funcs P)) in
  {| functions := map fst (funcs P);
     roots := [main P];
     sites_of := fun f =>
       match Map.get nat_encoding f sites with
       | Some ls =>
         ls
       | None =>
         []
       end;
     caller_of := fst;
     here := fun s =>
       match stack s with
       | fr :: _ =>
         ffunc fr
       | [] =>
         main P
       end;
     frames := ssa_suspended |}.

(** Type tags give a constructive finite encoding of complete call signatures. *)
Definition ssa_ty_encoding : encoding ty.
Proof.
  refine (Encoding _ (fun t => encode nat_encoding
    (match t with
    | TyI32 =>
      0
    | TyI64 =>
      1
    | TyPtr =>
      2
    | TyFun =>
      3
    | TyF32 =>
      4
    | TyF64 =>
      5
    end)) _).
  intros a b Heq; apply (encode_injective nat_encoding) in Heq;
    destruct a, b; congruence.
Defined.

Definition ssa_signature_encoding : encoding (list ty * ty) :=
  pair_encoding (list_encoding ssa_ty_encoding) ssa_ty_encoding.

(** Right-to-left insertion retains the original function order within each signature. *)
Fixpoint ssa_signature_groups (fs : list (func * fdef)) :
    Map.t (list ty * ty) (list func) :=
  match fs with
  | [] =>
    Map.empty
  | (f, fd) :: rest =>
    let groups := ssa_signature_groups rest in
    match entry_signature fd with
    | None =>
      groups
    | Some sig =>
      let targets :=
        match Map.get ssa_signature_encoding sig groups with
        | Some targets =>
          targets
        | None =>
          []
        end in
      Map.set ssa_signature_encoding sig (f :: targets) groups
    end
  end.

(** Direct targets are exact; indirect targets are indexed by their full entry signature. *)
Definition ssa_resolver (P : program) : call_site -> list func :=
  let signatures := ssa_signature_groups (funcs P) in
  let targets := Map.map (fun fd => Map.map (fun b =>
    match bterm b with
    | TCall (CDirect f) _ _ =>
      [f]
    | TCall (CIndirect _ ps r) _ _ =>
      match Map.get ssa_signature_encoding (ps, r) signatures with
      | Some fs =>
        fs
      | None =>
        []
      end
    | _ =>
      []
    end) (first_index (blocks fd))) (first_index (funcs P)) in
  fun site =>
    match Map.get nat_encoding (fst site) targets with
    | None =>
      []
    | Some bs =>
      match Map.get nat_encoding (snd site) bs with
      | Some fs =>
        fs
      | None =>
        []
      end
    end.

(** This list predicate is the independent reference for signature grouping. *)
Definition ssa_signature_matches (sig : list ty * ty) (fd : fdef) : bool :=
  match entry_signature fd with
  | Some actual =>
    Pos.eqb (encode ssa_signature_encoding sig)
      (encode ssa_signature_encoding actual)
  | None =>
    false
  end.

(** A signature bucket is exactly the compatible functions in original source order. *)
Lemma ssa_signature_groups_agrees fs sig :
  (match Map.get ssa_signature_encoding sig (ssa_signature_groups fs) with
   | Some targets =>
     targets
   | None =>
     []
   end) =
  map fst (filter (fun ff => ssa_signature_matches sig (snd ff)) fs).
Proof.
  induction fs as [|[f fd] rest IH].
  - cbn [ssa_signature_groups]; rewrite Map.get_empty; reflexivity.
  - cbn [ssa_signature_groups filter snd].
    unfold ssa_signature_matches at 1.
    destruct (entry_signature fd) as [actual|] eqn:Hsig; [|exact IH].
    destruct (Pos.eqb_spec (encode ssa_signature_encoding sig)
      (encode ssa_signature_encoding actual)) as [Heq|Hne].
    + apply (encode_injective ssa_signature_encoding) in Heq; subst actual.
      rewrite Map.get_set_same; cbn [map fst]; f_equal; exact IH.
    + rewrite Map.get_set_other; [exact IH|intro Heq; apply Hne; now rewrite Heq].
Qed.

Lemma ssa_signature_matches_iff sig fd :
  ssa_signature_matches sig fd = true <-> entry_signature fd = Some sig.
Proof.
  unfold ssa_signature_matches; destruct (entry_signature fd) as [actual|] eqn:Hsig.
  - rewrite Pos.eqb_eq; split.
    + intro Heq; apply (encode_injective ssa_signature_encoding) in Heq; now subst actual.
    + intro Heq; injection Heq as <-; reflexivity.
  - split; discriminate.
Qed.

Lemma ssa_signature_group_member fs f fd sig :
  In (f, fd) fs -> entry_signature fd = Some sig ->
  In f (match Map.get ssa_signature_encoding sig (ssa_signature_groups fs) with
        | Some targets =>
          targets
        | None =>
          []
        end).
Proof.
  intros Hin Hsig; rewrite ssa_signature_groups_agrees.
  apply in_map_iff; exists (f, fd); split; [reflexivity|].
  apply filter_In; split; [exact Hin|apply ssa_signature_matches_iff; exact Hsig].
Qed.

Lemma ssa_resolver_at P fr c args cont :
  at_term P fr (TCall c args cont) ->
  ssa_resolver P (ffunc fr, flabel fr) =
    match c with
    | CDirect f =>
      [f]
    | CIndirect _ ps r =>
      match Map.get ssa_signature_encoding (ps, r) (ssa_signature_groups (funcs P)) with
      | Some fs =>
        fs
      | None =>
        []
      end
    end.
Proof.
  intros [fd [b [Hf [Hb [Hpc Hterm]]]]].
  unfold ssa_resolver; cbn [fst snd]; rewrite Map.get_map.
  change (Map.get nat_encoding (ffunc fr) (first_index (funcs P)))
    with (find_func P (ffunc fr)); rewrite Hf; cbn [option_map]; rewrite Map.get_map.
  change (Map.get nat_encoding (flabel fr) (first_index (blocks fd)))
    with (find_block fd (flabel fr)); rewrite Hb; cbn [option_map]; rewrite Hterm; reflexivity.
Qed.

Lemma ssa_call_resolved P fr c args cont f fd b :
  at_term P fr (TCall c args cont) -> callee_def P (fenv fr) c = Some (f, fd, b) ->
  In f (ssa_resolver P (ffunc fr, flabel fr)).
Proof.
  intros Hat Hcall; rewrite (ssa_resolver_at _ _ _ _ _ Hat).
  destruct c as [g|x ps r].
  - cbn [callee_def] in Hcall.
    destruct (find_func P g) as [gd|]; [|discriminate].
    destruct (find_block gd (fentry gd)) as [gb|]; [|discriminate].
    injection Hcall as <-; left; reflexivity.
  - unfold callee_def in Hcall; cbn in Hcall.
    destruct (fenv fr x) as [v|]; [|discriminate].
    destruct v as [w z|block offset|target|bits|bits]; try discriminate.
    destruct (find_func P target) as [gd|] eqn:Hf; [|discriminate].
    destruct (find_block gd (fentry gd)) as [gb|] eqn:Hb; [|discriminate].
    destruct (list_eq_dec ty_eq_dec ps (map snd (bparams gb))) as [Hps|Hps];
      [|discriminate]; destruct (ty_eq_dec r (fresult gd)) as [Hr|Hr]; [|discriminate].
    injection Hcall as <- <- <-; apply (ssa_signature_group_member _ target gd).
    + apply first_index_sound; exact Hf.
    + unfold entry_signature; rewrite Hb; cbn [option_map]; now rewrite Hps, Hr.
Qed.

Lemma ssa_call_site ext P fr c args cont :
  at_term P fr (TCall c args cont) ->
  In (ffunc fr, flabel fr) (sites_of (ssa_calls ext P) (ffunc fr)).
Proof.
  intros [fd [b [Hf [Hb [Hpc Hterm]]]]].
  cbn [ssa_calls sites_of]; rewrite ssa_first_index_map_key.
  change (Map.get nat_encoding (ffunc fr) (first_index (funcs P)))
    with (find_func P (ffunc fr)); rewrite Hf; cbn [option_map ssa_function_sites].
  apply in_map; apply in_map_iff; exists (flabel fr, b); split; [reflexivity|].
  apply filter_In; split; [apply first_index_sound; exact Hb|cbn; rewrite Hterm; reflexivity].
Qed.

Lemma ssa_stack_listed_step ext P lim s tr t :
  Forall (fun fr => In (ffunc fr) (map fst (funcs P))) (stack s) ->
  step_s ext P lim s tr t ->
  Forall (fun fr => In (ffunc fr) (map fst (funcs P))) (stack t).
Proof.
  intros Hlisted Hstep; destruct Hstep; cbn [stack] in *;
    inversion Hlisted as [|top rest Htop Hrest]; subst;
    try (constructor; [exact Htop|exact Hrest]).
  - constructor.
    + match goal with
      | Hcall : callee_def _ _ _ = Some _ |- _ =>
        destruct (callee_def_target _ _ _ _ _ _ Hcall) as [Hf _]
      end.
      apply in_map_iff; exists (f, fd); split; [reflexivity|apply first_index_sound; exact Hf].
    + constructor; assumption.
  - inversion Hrest as [|top' rest' Hcaller Htail]; subst; constructor; assumption.
Qed.

Lemma ssa_stack_listed ext P lim s :
  reachable_state (ssa_semantics ext P lim) s ->
  Forall (fun fr => In (ffunc fr) (map fst (funcs P))) (stack s).
Proof.
  intros [s0 [tr [Hinitial Hrun]]].
  destruct Hinitial as [fd [b [vs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]].
  assert (Hlisted : Forall (fun fr => In (ffunc fr) (map fst (funcs P)))
    (stack (State [SFrame (main P) (fentry fd) 0 env 0] (fun _ => None) 0))).
  { constructor; [|constructor]; cbn; apply in_map_iff; exists (main P, fd).
    split; [reflexivity|apply first_index_sound; exact Hf]. }
  clear Hf Hb Htypes Hvalid Hbind.
  revert Hlisted; induction Hrun as [s|s events u tr t Hstep Hrun IH];
    intro Hlisted; [exact Hlisted|].
  apply IH; exact (ssa_stack_listed_step ext P lim s events u Hlisted Hstep).
Qed.

Lemma ssa_stack_nonempty ext P lim s :
  reachable_state (ssa_semantics ext P lim) s -> stack s <> [].
Proof.
  intros [s0 [tr [Hinitial Hrun]]].
  assert (Hnonempty : stack s0 <> []).
  { destruct Hinitial as [fd [b [vs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]];
      discriminate. }
  clear Hinitial; revert Hnonempty;
    induction Hrun as [s|s events u tr t Hstep Hrun IH]; intro Hnonempty.
  - exact Hnonempty.
  - apply IH; destruct Hstep; discriminate.
Qed.

(** The call adapter covers every reachable frame and every actual push or pop. *)
Theorem ssa_calls_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P ->
  calls_view_laws (ssa_semantics ext P lim) (ssa_calls ext P) (ssa_resolver P).
Proof.
  intro Hwf; constructor.
  - intros f p Hin; cbn [ssa_calls sites_of] in Hin.
    rewrite ssa_first_index_map_key in Hin.
    change (Map.get nat_encoding f (first_index (funcs P))) with (find_func P f) in Hin.
    destruct (find_func P f) as [fd|]; cbn [option_map ssa_function_sites] in Hin;
      [|contradiction].
    apply in_map_iff in Hin.
    destruct Hin as [l [<- Hin]]; reflexivity.
  - intros s [fd [b [vs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]].
    split; [left; reflexivity|reflexivity].
  - intros [stk m nb] Hreachable f Hin.
    pose proof (ssa_stack_listed ext P lim _ Hreachable) as Hlisted.
    destruct stk as [|fr rest].
    + exfalso; exact (ssa_stack_nonempty _ _ _ _ Hreachable eq_refl).
    + cbn [active ssa_calls here frames ssa_suspended stack tl] in Hin.
      destruct Hin as [<-|Hin].
      * inversion Hlisted; assumption.
      * apply in_map_iff in Hin; destruct Hin as [[g site] [Hf Hin]].
        apply in_map_iff in Hin; destruct Hin as [frame [Heq Hin]].
        injection Heq as Hfunction Hsite; cbn in Hf; subst g f.
        exact (proj1 (Forall_forall _ _) Hlisted frame (or_intror Hin)).
  - intros s tr t Hreachable Hstep; destruct Hstep;
      try (left; split; reflexivity).
    + right; left; exists (ffunc fr, flabel fr); split.
      * eapply ssa_call_site; eassumption.
      * split; [eapply ssa_call_resolved; eassumption|reflexivity].
    + right; right; exists (ffunc caller), (ffunc caller, flabel caller);
        split; reflexivity.
Qed.

(** Every suspended caller is linked to the actual callee above it by the resolver. *)
Lemma ssa_frame_chain ext P lim s :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  frames_linked (ssa_calls ext P) (ssa_resolver P)
    (here (ssa_calls ext P) s) (frames (ssa_calls ext P) s).
Proof.
  intros Hwf Hreachable; eapply reachable_frames_linked;
    [apply ssa_calls_laws; exact Hwf|exact Hreachable].
Qed.

(** * Local effect equations *)

(* Identify the action of one explicit full-machine transition. *)
Local Ltac ssa_identify_current Hcurrent :=
  match goal with
  | Hat : at_instr _ _ _ |- _ =>
    rewrite (ssa_current_instr _ _ _ _ _ _ Hat) in Hcurrent;
    injection Hcurrent as <-
  | Hat : at_term _ _ _ |- _ =>
    rewrite (ssa_current_term _ _ _ _ _ _ Hat) in Hcurrent;
    injection Hcurrent as <-
  end.

Lemma ssa_step_silent ext P lim s tr t it :
  ssa_current P s = Some it -> step_s ext P lim s tr t ->
  observes ssa_effects it = false -> tr = [].
Proof.
  intros Hcurrent Hstep; destruct Hstep; ssa_identify_current Hcurrent;
    cbn [ssa_effects observes]; intro Hflag; try discriminate; reflexivity.
Qed.

Lemma ssa_step_heap ext P lim s tr t it :
  ssa_current P s = Some it -> step_s ext P lim s tr t ->
  writes ssa_effects it = false -> allocates ssa_effects it = false ->
  frees ssa_effects it = false -> (mem t, next_block t) = (mem s, next_block s).
Proof.
  intros Hcurrent Hstep; destruct Hstep; ssa_identify_current Hcurrent;
    cbn [ssa_effects writes allocates frees]; intros; try discriminate; reflexivity.
Qed.

Lemma ssa_step_depth ext P lim s tr t it :
  ssa_current P s = Some it -> step_s ext P lim s tr t ->
  calls ssa_effects it = false -> length (stack t) = length (stack s).
Proof.
  intros Hcurrent Hstep; destruct Hstep; ssa_identify_current Hcurrent;
    cbn [ssa_effects calls]; intro Hflag; try discriminate; reflexivity.
Qed.

Lemma ssa_nodiverge_push ext P lim s tr t it :
  ssa_current P s = Some it -> step_s ext P lim s tr t ->
  calls ssa_effects it = true -> may_diverge ssa_effects it = false ->
  length (stack t) <> S (length (stack s)).
Proof.
  intros Hcurrent Hstep; destruct Hstep; ssa_identify_current Hcurrent;
    cbn [ssa_effects calls may_diverge stack length]; intros; try discriminate; lia.
Qed.

(** Nonreading transitions can be replayed on any heap with the identical stack. *)
Lemma ssa_step_heap_independent ext P lim s tr s' t it :
  ssa_current P s = Some it -> step_s ext P lim s tr s' ->
  reads ssa_effects it = false -> stack s = stack t ->
  exists t', step_s ext P lim t tr t' /\ stack s' = stack t'.
Proof.
  intros Hcurrent Hstep Hreads Hagree; destruct Hstep; ssa_identify_current Hcurrent;
    cbn [ssa_effects reads] in Hreads; try discriminate;
    destruct t as [stk tm tnb]; cbn [stack] in Hagree; subst stk.
  - eexists; split; [eapply SOp; eassumption|reflexivity].
  - eexists; split; [eapply SOutput; eassumption|reflexivity].
  - eexists; split; [eapply SJump; eassumption|reflexivity].
  - eexists; split; [eapply SBr; eassumption|reflexivity].
  - eexists; split; [eapply SSwitch; eassumption|reflexivity].
  - eexists; split; [eapply SCall; eassumption|reflexivity].
  - eexists; split; [eapply SReturn; eassumption|reflexivity].
  - eexists; split; [eapply SReturnMain; eassumption|reflexivity].
Qed.

Lemma ssa_current_stack P s t : stack s = stack t -> ssa_current P s = ssa_current P t.
Proof.
  intro Heq; unfold ssa_current; rewrite Heq; reflexivity.
Qed.

Lemma ssa_final_stack P s t : stack s = stack t -> (ssa_final P s <-> ssa_final P t).
Proof.
  intro Heq; unfold ssa_final; rewrite Heq; reflexivity.
Qed.

(** Stops of a nonreading action depend only on the fixed stack and frame limit. *)
Lemma ssa_stop_heap_independent P lim s t it :
  ssa_current P s = Some it -> reads ssa_effects it = false -> stack s = stack t ->
  (ssa_stopped P lim s <-> ssa_stopped P lim t).
Proof.
  intros Hcurrent Hreads Hagree; unfold ssa_stopped; rewrite <- Hagree.
  assert (Hnotalloc : forall fr rest x n,
    stack s = fr :: rest -> ~ at_instr P fr (IAlloc x n)).
  { intros fr rest x n Hstack Hat; destruct s as [stk m nb]; cbn in Hstack; subst stk.
    rewrite (ssa_current_instr _ _ _ _ _ _ Hat) in Hcurrent.
    injection Hcurrent as <-; discriminate Hreads. }
  split; intros [fr [rest [Hstack [Hcall|Halloc]]]];
    exists fr, rest; split; try assumption; try (left; exact Hcall);
    destruct Halloc as [x [n [z [Hat Hrest]]]];
    exfalso; exact (Hnotalloc fr rest x n Hstack Hat).
Qed.

Lemma ssa_stop_flag P lim s it :
  ssa_current P s = Some it -> ssa_stopped P lim s -> may_stop ssa_effects it = true.
Proof.
  intros Hcurrent [fr [rest [Hstack [Hcall|Halloc]]]];
    destruct s as [stk m nb]; cbn in Hstack; subst stk.
  - destruct Hcall as [c [args [cont [cs [f [fd [b [env [Hat Hrest]]]]]]]]].
    rewrite (ssa_current_term _ _ _ _ _ _ Hat) in Hcurrent; injection Hcurrent as <-;
      reflexivity.
  - destruct Halloc as [x [n [z [Hat Hrest]]]].
    rewrite (ssa_current_instr _ _ _ _ _ _ Hat) in Hcurrent; injection Hcurrent as <-;
      reflexivity.
Qed.

(** * Reachable progress for unflagged actions *)

Lemma ssa_full_operation_progress ext P lim fr rest m nb x o args :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  at_instr P fr (IOp x o args) ->
  may_trap ssa_effects (AnInstr (IOp x o args)) = false ->
  exists cs v, read_args (fenv fr) args = Some cs /\ op_eval ext o cs = Some v.
Proof.
  intros Hwf Hreachable [fd [b [Hf [Hb Hnth]]]] Hflag.
  destruct (typed_operands ext P lim _ fr fd b x o args Hwf Hreachable
    (or_introl eq_refl) Hf Hb Hnth) as
    [cs [ps [r [Hvalues [Hsig [Htypes Hvalid]]]]]].
  destruct (op_eval ext o cs) as [v|] eqn:Heval.
  - exists cs, v; split; [apply ssa_read_args_complete; exact Hvalues|exact Heval].
  - destruct (proj2 (op_eval_typed ext P o cs ps r
      (proj2 (proj2 (proj2 (proj2 Hwf)))) Hsig Htypes Hvalid) Heval)
      as [[w ->]|[tag ->]]; discriminate Hflag.
Qed.

(** Typed, available operands of integer control instructions have the required shape. *)
Lemma ssa_full_i32_operand P fr x :
  frame_good P fr -> env_bound (fenv fr) [x] -> static_ty P (ffunc fr) x = Some TyI32 ->
  exists z, fenv fr x = Some (VInt W32 z).
Proof.
  intros [Htyped Havailable] Hbound Htype.
  destruct (Hbound x (or_introl eq_refl)) as [v Hv].
  destruct (Htyped x v Hv) as [Hactual Hvalid]; rewrite Htype in Hactual.
  destruct v as [[|] z|b off|f|z|z]; try discriminate; exists z; exact Hv.
Qed.

(** A selected well-typed jump always has an arity-correct parallel binding. *)
Lemma ssa_full_jump_ready ext P fr term fd dst args :
  wf_program ext P -> frame_good P fr -> at_term P fr term ->
  find_func P (ffunc fr) = Some fd -> In (dst, args) (term_edges term) ->
  typed_jump (find_block fd) (static_ty P (ffunc fr)) (dst, args) ->
  exists cs env, read_args (fenv fr) args = Some cs /\ jump_env P fr dst cs = Some env.
Proof.
  intros Hwf Hgood Hat Hf Hedge Htyped.
  destruct (read_args_exists (fenv fr) args) as [cs Hread].
  { intros x Hx; exact (ssa_term_operands_bound ext P fr term Hwf (proj2 Hgood) Hat x
      (ssa_edge_argument_use term dst args x Hedge Hx)). }
  change (match find_block fd dst with
    | Some b =>
      types_of (static_ty P (ffunc fr)) args = Some (map snd (bparams b))
    | None =>
      False
    end) in Htyped.
  destruct (find_block fd dst) as [b|] eqn:Hb; [|contradiction].
  destruct (ssa_bind_exists (fenv fr) (bparams b) cs) as [env Hbind].
  { pose proof (ssa_types_length _ _ _ Htyped) as Htypes.
    pose proof (ssa_read_length _ _ _ Hread) as Hvalues; rewrite length_map in Htypes; lia. }
  exists cs, env; split; [exact Hread|unfold jump_env; rewrite Hf, Hb; exact Hbind].
Qed.

(** A returning frame can always bind its caller's single continuation parameter. *)
Lemma ssa_full_return_ready ext P child caller :
  wf_program ext P -> return_link P child caller ->
  forall v, exists env, jump_env P caller (fret caller) [v] = Some env.
Proof.
  intros Hwf [fd [c [args [cont [ps [Hf [Hat [Hret Hsig]]]]]]]] v.
  destruct (call_typed ext P caller c args cont Hwf Hat) as
    [callerfd [actualps [r [b [Hcaller [Hactual [Hb [Hargs Hparams]]]]]]]].
  destruct (ssa_bind_exists (fenv caller) (bparams b) [v]) as [env Hbind].
  { pose proof (f_equal (@length ty) Hparams) as Hlength; rewrite length_map in Hlength;
      exact Hlength. }
  exists env; unfold jump_env; rewrite Hcaller, Hret, Hb; exact Hbind.
Qed.

Lemma ssa_unflagged_instruction_progress ext P lim fr rest m nb i :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  at_instr P fr i -> may_trap ssa_effects (AnInstr i) = false ->
  running (ssa_semantics ext P lim) (State (fr :: rest) m nb) \/
  ssa_stopped P lim (State (fr :: rest) m nb).
Proof.
  intros Hwf Hreachable Hat Hflag.
  destruct i as [x o args|x n|p|x ty sz p|sz p x|x]; try discriminate Hflag.
  - destruct (ssa_full_operation_progress ext P lim fr rest m nb x o args
      Hwf Hreachable Hat Hflag) as [cs [v [Hread Heval]]].
    left; exists [], (State (advance fr (env_set (fenv fr) x v) :: rest) m nb).
    eapply SOp; eassumption.
  - destruct Hat as [fd [b [Hf [Hb Hnth]]]].
    destruct (allocation_size_in_range ext P lim _ fr fd b x n Hwf Hreachable
      (or_introl eq_refl) Hf Hb Hnth) as [z [Hsize Hrange]].
    assert (Hat : at_instr P fr (IAlloc x n)) by (exists fd, b; repeat split; assumption).
    destruct (lt_dec nb (max_blocks lim)) as [Hroom|Hfull].
    + left; eexists [], _; eapply SAlloc; eassumption.
    + right; exists fr, rest; split; [reflexivity|right].
      exists x, n, z; repeat split; try assumption; cbn; lia.
  - destruct (reachable_good _ _ _ _ Hwf Hreachable) as [Hframes Hlinks].
    inversion Hframes as [|top tail Hgood Hrest]; subst.
    destruct (frame_operands_bound ext P fr (IOutput x) Hwf (proj2 Hgood) Hat x
      (or_introl eq_refl)) as [v Hv].
    left; eexists [EvOut v], _; eapply SOutput; eassumption.
Qed.

Lemma ssa_unflagged_term_progress ext P lim fr rest m nb term :
  wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) (State (fr :: rest) m nb) ->
  at_term P fr term -> may_trap ssa_effects (ATerm term) = false ->
  running (ssa_semantics ext P lim) (State (fr :: rest) m nb).
Proof.
  intros Hwf Hreachable Hat Hflag.
  destruct (reachable_good _ _ _ _ Hwf Hreachable) as [Hframes Hlinks].
  inversion Hframes as [|top tail Hgood Hrest]; subst.
  destruct (wf_terminator ext P fr term Hwf Hat) as [fd [Hf Htyped]].
  pose proof (ssa_term_operands_bound ext P fr term Hwf (proj2 Hgood) Hat) as Hbound.
  destruct term as [dst args|c l1 a1 l2 a2|c cases d da|c args cont|x];
    try discriminate Hflag.
  - destruct (ssa_full_jump_ready ext P fr _ fd dst args Hwf Hgood Hat Hf
      (or_introl eq_refl) (proj1 (Forall_forall _ _) Htyped _ (or_introl eq_refl)))
      as [cs [env [Hread Hjump]]].
    eexists [], _; eapply SJump; eassumption.
  - destruct Htyped as [Hcondition Hedges].
    destruct (ssa_full_i32_operand P fr c Hgood) as [z Hz].
    { intros y [<-|[]]; apply Hbound; left; reflexivity. }
    { exact Hcondition. }
    destruct (Z.eqb z 0) eqn:Hchoice.
    + destruct (ssa_full_jump_ready ext P fr _ fd l2 a2 Hwf Hgood Hat Hf
        (or_intror (or_introl eq_refl))
        (proj1 (Forall_forall _ _) Hedges _ (or_intror (or_introl eq_refl))))
        as [cs [env [Hread Hjump]]].
      eexists [], _; eapply SBr; try eassumption; rewrite Hchoice; reflexivity.
    + destruct (ssa_full_jump_ready ext P fr _ fd l1 a1 Hwf Hgood Hat Hf
        (or_introl eq_refl) (proj1 (Forall_forall _ _) Hedges _ (or_introl eq_refl)))
        as [cs [env [Hread Hjump]]].
      eexists [], _; eapply SBr; try eassumption; rewrite Hchoice; reflexivity.
  - destruct Htyped as [Hcondition Hedges].
    destruct (ssa_full_i32_operand P fr c Hgood) as [z Hz].
    { intros y [<-|[]]; apply Hbound; left; reflexivity. }
    { exact Hcondition. }
    destruct (switch_target z cases d da) as [dst args] eqn:Hchoice.
    pose proof (switch_target_edge _ _ _ _ _ _ Hchoice) as Hedge.
    destruct (ssa_full_jump_ready ext P fr _ fd dst args Hwf Hgood Hat Hf Hedge
      (proj1 (Forall_forall _ _) Hedges _ Hedge)) as [cs [env [Hread Hjump]]].
    eexists [], _; eapply SSwitch; eassumption.
  - destruct (Hbound x (or_introl eq_refl)) as [v Hv].
    destruct rest as [|caller tail].
    + eexists [EvRet v], _; eapply SReturnMain; eassumption.
    + destruct Hlinks as [Hlink Hlinks].
      destruct (ssa_full_return_ready ext P fr caller Hwf Hlink v) as [env Hjump].
      eexists [], _; eapply SReturn; eassumption.
Qed.

(** Reachable traps are confined to the operations marked by the effects table. *)
Lemma ssa_trap_flag ext P lim s it :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  ssa_current P s = Some it -> trapped (ssa_endings ext P lim) s ->
  may_trap ssa_effects it = true.
Proof.
  intros Hwf Hreachable Hcurrent [Hnorun [Hnofinal Hnostop]].
  destruct (may_trap ssa_effects it) eqn:Hflag; [reflexivity|exfalso].
  destruct s as [[|fr rest] m nb]; [discriminate Hcurrent|].
  pose proof (ssa_current_sound P fr rest m nb it Hcurrent) as Hat.
  destruct it as [i|term].
  - destruct (ssa_unflagged_instruction_progress _ _ _ _ _ _ _ _
      Hwf Hreachable Hat Hflag) as [Hrun|Hstop]; contradiction.
  - apply Hnorun; eapply ssa_unflagged_term_progress; eassumption.
Qed.

(** Nonreading instructions have the same running and trap observations on equal stacks. *)
Lemma ssa_trap_heap_independent ext P lim s t it :
  ssa_current P s = Some it -> reads ssa_effects it = false -> stack s = stack t ->
  (trapped (ssa_endings ext P lim) s <-> trapped (ssa_endings ext P lim) t).
Proof.
  intros Hcurrent Hreads Hagree.
  assert (Hother : ssa_current P t = Some it).
  { rewrite <- (ssa_current_stack P s t Hagree); exact Hcurrent. }
  assert (Hrunning : running (ssa_semantics ext P lim) s <->
    running (ssa_semantics ext P lim) t).
  { split; intros [tr [u Hstep]].
    - destruct (ssa_step_heap_independent _ _ _ _ _ _ _ _ Hcurrent Hstep Hreads Hagree)
        as [v [Hcopy Hstack]]; exists tr, v; exact Hcopy.
    - destruct (ssa_step_heap_independent _ _ _ _ _ _ _ _ Hother Hstep Hreads
        (eq_sym Hagree)) as [v [Hcopy Hstack]]; exists tr, v; exact Hcopy. }
  cbn [ssa_endings trapped].
  rewrite Hrunning, (ssa_final_stack P s t Hagree),
    (ssa_stop_heap_independent P lim s t it Hcurrent Hreads Hagree); reflexivity.
Qed.

(** All effect flags soundly cover the full machine, with exact heap and frame agreement. *)
Theorem ssa_effects_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P ->
  effects_laws (ssa_semantics ext P lim) (ssa_endings ext P lim) ssa_effects
    (ssa_effects_view ext P lim).
Proof.
  intro Hwf; constructor.
  - intros s tr t it Hreachable Hcurrent Hstep Hflag.
    exact (ssa_step_silent ext P lim s tr t it Hcurrent Hstep Hflag).
  - intros s it Hreachable Hcurrent Htrap.
    exact (ssa_trap_flag ext P lim s it Hwf Hreachable Hcurrent Htrap).
  - intros s it Hreachable Hcurrent Hstop.
    exact (ssa_stop_flag P lim s it Hcurrent Hstop).
  - intros s tr t it Hreachable Hcurrent Hstep Hwrite Halloc Hfree.
    exact (ssa_step_heap ext P lim s tr t it Hcurrent Hstep Hwrite Halloc Hfree).
  - intros s tr s' t it Hreachable Hcurrent Hstep Hreads Hagree.
    exact (ssa_step_heap_independent ext P lim s tr s' t it
      Hcurrent Hstep Hreads Hagree).
  - intros s t it Hreachable Hother Hcurrent Hnext Hreads Hagree.
    exact (ssa_trap_heap_independent ext P lim s t it Hcurrent Hreads Hagree).
  - intros s t it Hreachable Hother Hcurrent Hnext Hreads Hagree.
    exact (ssa_stop_heap_independent P lim s t it Hcurrent Hreads Hagree).
  - intros s tr t it Hreachable Hcurrent Hstep Hflag.
    exact (ssa_step_depth ext P lim s tr t it Hcurrent Hstep Hflag).
  - intros s tr t it Hreachable Hcurrent Hstep Hcalls Hdiverge Hdepth.
    exfalso; exact (ssa_nodiverge_push ext P lim s tr t it
      Hcurrent Hstep Hcalls Hdiverge Hdepth).
Qed.

(** * Fixture for reachable allocation and memory traps *)

(** The load after a free is well typed but traps on the retained dead allocation. *)
Definition ssa_effects_fixture : program :=
  Program [(0, FDef 0 [(0, SBlock [(0, TyI64)]
    [IAlloc 1 0; IFree 1; ILoad 2 TyI32 M1 1] (TRet 2))] TyI32)] 0 [].

Definition ssa_effects_initial_env : vid -> option cval :=
  env_set (fun _ => None) 0 (VInt W64 8%Z).

Definition ssa_effects_allocated_env : vid -> option cval :=
  env_set ssa_effects_initial_env 1 (VPtr 0 0%Z).

Definition ssa_effects_initial_state : state :=
  State [SFrame 0 0 0 ssa_effects_initial_env 0] (fun _ => None) 0.

Definition ssa_effects_allocated_state : state :=
  State [SFrame 0 0 1 ssa_effects_allocated_env 0]
    (memory_set (fun _ => None) 0 (MBlock 8 (fun _ => MInt 0%Z) true 1)) 1.

Definition ssa_effects_trap_state : state :=
  State [SFrame 0 0 2 ssa_effects_allocated_env 0]
    (memory_set (mem ssa_effects_allocated_state) 0
      (MBlock 8 (fun _ => MInt 0%Z) false 1)) 1.
