(** * Intraprocedural SSA activations

    An activation retains one function's source environment and abstracts memory and calls.
    For example, a load may return any valid value of its declared type.
    Builds on: ExamplesSsaSemantics, ExamplesSsaTypingProofs and ViewsSemantics. *)

From Stdlib Require Import List ZArith Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Views Require Import ViewsSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaBridge.
Import List.ListNotations.
Local Open Scope nat_scope.

(** An activation stores one function's current block, instruction position and environment. *)
Record astate : Type := AState {
  alabel : label;
  apc : nat;
  aenv : vid -> option cval
}.

Definition activation_frame (f : func) (a : astate) : sframe :=
  SFrame f (alabel a) (apc a) (aenv a) 0.

Definition activation_advance (a : astate) (env : vid -> option cval) : astate :=
  AState (alabel a) (S (apc a)) env.

Definition activation_enter (l : label) (env : vid -> option cval) : astate :=
  AState l 0 env.

(** Initial activations bind exactly the function entry's arbitrary valid typed arguments. *)
Definition activation_initial (P : program) (f : func) (a : astate) : Prop :=
  exists fd b cs env,
    find_func P f = Some fd /\ find_block fd (fentry fd) = Some b /\
    map ty_of cs = map snd (bparams b) /\ Forall valid_cval cs /\
    bind_params (fun _ => None) (bparams b) cs = Some env /\
    a = AState (fentry fd) 0 env.

(** Activation steps execute source operations while abstracting memory and callee results. *)
Inductive activation_step (ext : nat -> list cval -> option cval) (P : program) (f : func)
    : astate -> list event -> astate -> Prop :=
  | AOp : forall a x o args cs v,
      at_instr P (activation_frame f a) (IOp x o args) ->
      read_args (aenv a) args = Some cs -> op_eval ext o cs = Some v ->
      activation_step ext P f a [] (activation_advance a (env_set (aenv a) x v))
  | AAlloc : forall a x n block offset,
      at_instr P (activation_frame f a) (IAlloc x n) ->
      activation_step ext P f a []
        (activation_advance a (env_set (aenv a) x (VPtr block offset)))
  | AFree : forall a p,
      at_instr P (activation_frame f a) (IFree p) ->
      activation_step ext P f a [] (activation_advance a (aenv a))
  | ALoad : forall a x t sz p v,
      at_instr P (activation_frame f a) (ILoad x t sz p) ->
      ty_of v = t -> valid_cval v ->
      activation_step ext P f a [] (activation_advance a (env_set (aenv a) x v))
  | AStore : forall a sz p x,
      at_instr P (activation_frame f a) (IStore sz p x) ->
      activation_step ext P f a [] (activation_advance a (aenv a))
  | AOutput : forall a x v,
      at_instr P (activation_frame f a) (IOutput x) -> aenv a x = Some v ->
      activation_step ext P f a [EvOut v] (activation_advance a (aenv a))
  | AJump : forall a l args cs env,
      at_term P (activation_frame f a) (TJump l args) ->
      read_args (aenv a) args = Some cs ->
      jump_env P (activation_frame f a) l cs = Some env ->
      activation_step ext P f a [] (activation_enter l env)
  | ABranch : forall a c l1 a1 l2 a2 z l args cs env,
      at_term P (activation_frame f a) (TBr c l1 a1 l2 a2) ->
      aenv a c = Some (VInt W32 z) ->
      (l, args) = (if Z.eqb z 0 then (l2, a2) else (l1, a1)) ->
      read_args (aenv a) args = Some cs ->
      jump_env P (activation_frame f a) l cs = Some env ->
      activation_step ext P f a [] (activation_enter l env)
  | ASwitch : forall a c cases d da z l args cs env,
      at_term P (activation_frame f a) (TSwitch c cases d da) ->
      aenv a c = Some (VInt W32 z) -> switch_target z cases d da = (l, args) ->
      read_args (aenv a) args = Some cs ->
      jump_env P (activation_frame f a) l cs = Some env ->
      activation_step ext P f a [] (activation_enter l env)
  | ACall : forall a c args k ps r cs v env,
      at_term P (activation_frame f a) (TCall c args k) ->
      callee_sig P (static_ty P f) c = Some (ps, r) ->
      read_args (aenv a) (term_uses (TCall c args k)) = Some cs ->
      ty_of v = r -> valid_cval v ->
      jump_env P (activation_frame f a) k [v] = Some env ->
      activation_step ext P f a [] (activation_enter k env)
  | AReturn : forall a x v,
      at_term P (activation_frame f a) (TRet x) -> aenv a x = Some v ->
      activation_step ext P f a [EvRet v] (activation_advance a (aenv a)).

(** The activation semantics retains the independent source operator evaluator. *)
Definition activation (ext : nat -> list cval -> option cval) (P : program) (f : func)
    : semantics astate event := Semantics (activation_initial P f) (activation_step ext P f).

Definition activation_final (P : program) (f : func) (a : astate) : Prop :=
  ssa_frame_final P (activation_frame f a).

Definition activation_trapped (ext : nat -> list cval -> option cval)
    (P : program) (f : func) (a : astate) : Prop :=
  ssa_frame_trapped ext P (activation_frame f a).

(** Activations stop only at a return endpoint or an operation trap, without resource stops. *)
Definition activation_endings (ext : nat -> list cval -> option cval)
    (P : program) (f : func) : endings astate :=
  Endings (activation_final P f) (activation_trapped ext P f) (fun _ => False).

(** * Typing and availability *)

Definition activation_good (P : program) (f : func) (a : astate) : Prop :=
  frame_good P (activation_frame f a).

Lemma activation_initial_good ext P f a :
  wf_program ext P -> initial (activation ext P f) a -> activation_good P f a.
Proof.
  intros Hwf [fd [b [cs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]].
  split.
  - eapply bind_params_typed; try eassumption.
    + intros x v Hnone; discriminate.
    + exact (proj1 (wf_block ext P f fd (fentry fd) b Hwf Hf Hb)).
  - apply (entry_available P f fd b env 0 Hf Hb).
    exact (proj2 (bind_params_support _ _ _ _ Hbind)).
Qed.

Lemma activation_transfer_good ext P f a t l args cs env :
  wf_program ext P -> activation_good P f a ->
  at_term P (activation_frame f a) t ->
  (forall fd, find_func P f = Some fd ->
    Forall (typed_jump (find_block fd) (static_ty P f)) (term_edges t)) ->
  In (l, args) (term_edges t) -> read_args (aenv a) args = Some cs ->
  jump_env P (activation_frame f a) l cs = Some env ->
  activation_good P f (activation_enter l env).
Proof.
  intros Hwf Hgood Hat Htyped Hedge Hread Hbind.
  destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]].
  change (frame_good P (enter (activation_frame f a) l env)).
  eapply ordinary_jump_good; [exact Hwf|exact Hgood| |exact Hf| |exact Hedge|exact Hread|
    exact Hbind].
  - exists fd, b; repeat split; assumption.
  - apply Htyped; exact Hf.
Qed.

Lemma activation_load_good ext P f a x t sz p v :
  wf_program ext P -> activation_good P f a ->
  at_instr P (activation_frame f a) (ILoad x t sz p) ->
  ty_of v = t -> valid_cval v ->
  activation_good P f (activation_advance a (env_set (aenv a) x v)).
Proof.
  intros Hwf Hgood Hat Htype Hvalid.
  pose proof (wf_instruction ext P _ _ Hwf Hat) as Hlocal.
  unfold instr_typed, instr_sig, instr_sig_with in Hlocal; cbn beta iota zeta in Hlocal.
  destruct (load_ok t sz); [|contradiction].
  destruct Hlocal as [_ Hresult]; cbn [result_has_type] in Hresult.
  change (frame_good P (advance (activation_frame f a) (env_set (aenv a) x v))).
  eapply assign_advance_good; try eassumption; [reflexivity|].
  cbn [activation_frame ffunc] in *; rewrite Htype; exact Hresult.
Qed.

Lemma activation_call_good ext P f a c args k ps r cs v env :
  wf_program ext P -> activation_good P f a ->
  at_term P (activation_frame f a) (TCall c args k) ->
  callee_sig P (static_ty P f) c = Some (ps, r) ->
  read_args (aenv a) (term_uses (TCall c args k)) = Some cs ->
  ty_of v = r -> valid_cval v ->
  jump_env P (activation_frame f a) k [v] = Some env ->
  activation_good P f (activation_enter k env).
Proof.
  intros Hwf Hgood Hat Hsig Hread Htype Hvalid Hbind.
  destruct (call_typed ext P _ _ _ _ Hwf Hat) as
    [fd [ps' [r' [b [Hf [Hsig' [Hb [Hargs Hparams]]]]]]]].
  cbn [activation_frame ffunc] in Hsig', Hf; rewrite Hsig in Hsig'.
  injection Hsig' as <- <-.
  change (frame_good P (enter (activation_frame f a) k env)).
  eapply jump_good; [exact Hgood|exact Hat| |exact Hbind|].
  - change (In k [k]); left; reflexivity.
  - eapply jump_env_typed; [exact Hwf|exact (proj1 Hgood)|exact Hbind| |].
    + intros fd' b' Hf' Hb'; cbn [activation_frame ffunc] in Hf'.
      rewrite Hf in Hf'; injection Hf' as <-; rewrite Hb in Hb'; injection Hb' as <-.
      cbn; rewrite Htype; symmetry; exact Hparams.
    + constructor; [exact Hvalid|constructor].
Qed.

Lemma activation_step_good ext P f a tr a' :
  wf_program ext P -> activation_good P f a ->
  step (activation ext P f) a tr a' -> activation_good P f a'.
Proof.
  intros Hwf Hgood Hstep.
  destruct Hstep as
    [a x o args cs v Hat Hread Heval
    |a x n block offset Hat
    |a p Hat
    |a x t sz p v Hat Htype Hvalid
    |a sz p x Hat
    |a x v Hat Hvalue
    |a l args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z l args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases d da z l args cs env Hat Hcond Hchoice Hread Hbind
    |a c args k ps r cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a x v Hat Hvalue].
  - change (frame_good P (advance (activation_frame f a) (env_set (aenv a) x v))).
    eapply operation_good; eassumption.
  - change (frame_good P
      (advance (activation_frame f a) (env_set (aenv a) x (VPtr block offset)))).
    eapply assign_advance_good; [exact Hgood|exact Hat|reflexivity| |exact I].
    pose proof (wf_instruction ext P _ _ Hwf Hat) as [_ Hresult].
    exact Hresult.
  - change (frame_good P (advance (activation_frame f a) (aenv a))).
    eapply unchanged_advance_good; [exact Hgood|exact Hat|reflexivity].
  - eapply activation_load_good; eassumption.
  - change (frame_good P (advance (activation_frame f a) (aenv a))).
    eapply unchanged_advance_good; [exact Hgood|exact Hat|reflexivity].
  - change (frame_good P (advance (activation_frame f a) (aenv a))).
    eapply unchanged_advance_good; [exact Hgood|exact Hat|reflexivity].
  - eapply activation_transfer_good; try eassumption.
    + intros fd Hf; destruct (wf_terminator ext P _ _ Hwf Hat) as [fd' [Hf' Htyped]].
      change (find_func P f = Some fd') in Hf'; rewrite Hf in Hf'; injection Hf' as <-.
      exact Htyped.
    + left; reflexivity.
  - eapply activation_transfer_good; try eassumption.
    + intros fd Hf; destruct (wf_terminator ext P _ _ Hwf Hat) as [fd' [Hf' Htyped]].
      change (find_func P f = Some fd') in Hf'; rewrite Hf in Hf'; injection Hf' as <-.
      exact (proj2 Htyped).
    + cbn [term_edges]; destruct (Z.eqb z 0); injection Hchoice as <- <-.
      * right; left; reflexivity.
      * left; reflexivity.
  - eapply activation_transfer_good; try eassumption.
    + intros fd Hf; destruct (wf_terminator ext P _ _ Hwf Hat) as [fd' [Hf' Htyped]].
      change (find_func P f = Some fd') in Hf'; rewrite Hf in Hf'; injection Hf' as <-.
      exact (proj2 Htyped).
    + exact (switch_target_edge z cases d da l args Hchoice).
  - eapply activation_call_good; eassumption.
  - split; [exact (proj1 Hgood)|].
    change (frame_available P (advance (activation_frame f a) (aenv a))).
    eapply past_end_available; [exact Hat|exact (proj2 Hgood)].
Qed.

(** Every reachable activation has a typed environment and its certified available operands. *)
Lemma activation_reachable_good ext P f a :
  wf_program ext P -> reachable_state (activation ext P f) a -> activation_good P f a.
Proof.
  intros Hwf [a0 [tr [Hinitial Hrun]]].
  pose proof (activation_initial_good ext P f a0 Hwf Hinitial) as Hgood.
  clear Hinitial; revert Hgood.
  induction Hrun as [a|a tr a' rest a'' Hstep Hrun IH]; intro Hgood.
  - exact Hgood.
  - apply IH; eapply activation_step_good; eassumption.
Qed.

(** Reachable operation operands are bound, valid and have their declared signature. *)
Lemma activation_typed_operands ext P f a x o args :
  wf_program ext P -> reachable_state (activation ext P f) a ->
  at_instr P (activation_frame f a) (IOp x o args) ->
  exists cs ps r, read_args (aenv a) args = Some cs /\ op_sig P o = Some (ps, r) /\
    map ty_of cs = ps /\ Forall valid_cval cs.
Proof.
  intros Hwf Hreachable Hat.
  destruct (activation_reachable_good ext P f a Hwf Hreachable) as [Htyped Havailable].
  destruct (read_args_exists (aenv a) args
    (frame_operands_bound ext P _ _ Hwf Havailable Hat)) as [cs Hread].
  pose proof (wf_instruction ext P _ _ Hwf Hat) as Hlocal.
  unfold instr_typed, instr_sig, instr_sig_with in Hlocal; cbn beta iota zeta in Hlocal.
  destruct (op_sig P o) as [[ps r]|] eqn:Hsig; [|contradiction].
  destruct Hlocal as [Hargs Hresult].
  destruct (read_args_typed P f (aenv a) args cs ps Htyped Hread Hargs) as [Htypes Hvalid].
  exists cs, ps, r; repeat split; assumption.
Qed.

(** * Refined point identities *)

(** Source values and fresh per-call result temporaries have disjoint identities. *)
Inductive ssa_refined_value : Type :=
  | SsaSourceValue (x : vid)
  | SsaCallResult (l : label).

(** Refined points distinguish parameter binding, stable execution and call administration. *)
Inductive ssa_refined_point : Type :=
  | SsaBeforeParams (l : label)
  | SsaExecPoint (l : label) (pc : nat)
  | SsaCallReady (l : label)
  | SsaAfterReturn (l : label)
  | SsaDeadPoint (l : label).

(** Refined edges retain block-edge occurrences and separate all administrative actions. *)
Inductive ssa_refined_edge : Type :=
  | SsaBindParams (l : label)
  | SsaInstruction (l : label) (pc : nat)
  | SsaMakeCallResult (l : label)
  | SsaTransfer (src dst : label) (slot : nat)
  | SsaReturn (l : label).

Definition ssa_refined_value_code (v : ssa_refined_value) : (nat + nat)%type :=
  match v with
  | SsaSourceValue x => inl x
  | SsaCallResult l => inr l
  end.

(** The sum encoding prevents a call temporary from aliasing a source value. *)
Definition ssa_refined_value_encoding : encoding ssa_refined_value.
Proof.
  pose (E := sum_encoding nat_encoding nat_encoding).
  refine (Encoding _ (fun v => encode E (ssa_refined_value_code v)) _).
  intros [x|l] [y|k] Hcode; apply (encode_injective E) in Hcode;
    cbn [ssa_refined_value_code] in Hcode; inversion Hcode; reflexivity.
Defined.

Definition ssa_refined_point_code (n : ssa_refined_point) : nat * (label * nat) :=
  match n with
  | SsaBeforeParams l => (0, (l, 0))
  | SsaExecPoint l pc => (1, (l, pc))
  | SsaCallReady l => (2, (l, 0))
  | SsaAfterReturn l => (3, (l, 0))
  | SsaDeadPoint l => (4, (l, 0))
  end.

(** Each point constructor has its own tag and retains all its coordinates. *)
Definition ssa_refined_point_encoding : encoding ssa_refined_point.
Proof.
  pose (E := pair_encoding nat_encoding (pair_encoding nat_encoding nat_encoding)).
  refine (Encoding _ (fun n => encode E (ssa_refined_point_code n)) _).
  intros [l|l pc|l|l|l] [k|k qc|k|k|k] Hcode;
    apply (encode_injective E) in Hcode; cbn [ssa_refined_point_code] in Hcode;
    inversion Hcode; reflexivity.
Defined.

Definition ssa_refined_edge_code (e : ssa_refined_edge) : nat * (label * (label * nat)) :=
  match e with
  | SsaBindParams l => (0, (l, (0, 0)))
  | SsaInstruction l pc => (1, (l, (0, pc)))
  | SsaMakeCallResult l => (2, (l, (0, 0)))
  | SsaTransfer src dst slot => (3, (src, (dst, slot)))
  | SsaReturn l => (4, (l, (0, 0)))
  end.

(** Edge encodings distinguish parallel slots as well as administrative constructors. *)
Definition ssa_refined_edge_encoding : encoding ssa_refined_edge.
Proof.
  pose (E := pair_encoding nat_encoding
    (pair_encoding nat_encoding (pair_encoding nat_encoding nat_encoding))).
  refine (Encoding _ (fun e => encode E (ssa_refined_edge_code e)) _).
  intros [l|l pc|l|l k slot|l] [a|a qc|a|a b j|a] Hcode;
    apply (encode_injective E) in Hcode; cbn [ssa_refined_edge_code] in Hcode;
    inversion Hcode; reflexivity.
Defined.

(** A refined state explicitly stores the selected incoming values before parallel binding. *)
Record ssa_refined_state : Type := SsaRefinedState {
  srs_point : ssa_refined_point;
  srs_env : vid -> option cval;
  srs_call_results : label -> option cval;
  srs_pending : nat -> option cval
}.

(** Semantic variables include pending slots, which may have several incoming definitions. *)
Inductive ssa_refined_semantic_var : Type :=
  | SsaSourceVar (x : vid)
  | SsaCallVar (l : label)
  | SsaPendingVar (i : nat).

Definition ssa_refined_semantic_var_code (x : ssa_refined_semantic_var) : nat * nat :=
  match x with
  | SsaSourceVar x => (0, x)
  | SsaCallVar l => (1, l)
  | SsaPendingVar i => (2, i)
  end.

(** Semantic-variable tags preserve source, call and pending-slot distinctions. *)
Definition ssa_refined_semantic_var_encoding : encoding ssa_refined_semantic_var.
Proof.
  pose (E := pair_encoding nat_encoding nat_encoding).
  refine (Encoding _ (fun x => encode E (ssa_refined_semantic_var_code x)) _).
  intros [x|l|i] [y|k|j] Hcode; apply (encode_injective E) in Hcode;
    cbn [ssa_refined_semantic_var_code] in Hcode; inversion Hcode; reflexivity.
Defined.

(** * Refined activation transitions *)

Definition ssa_pending_write (old : nat -> option cval) (cs : list cval)
    : nat -> option cval :=
  let index := first_index (combine (seq 0 (length cs)) cs) in
  fun i => match Map.get nat_encoding i index with
  | Some c => Some c
  | None => old i
  end.

Definition ssa_refined_set_point (r : ssa_refined_state) (n : ssa_refined_point)
    : ssa_refined_state :=
  SsaRefinedState n (srs_env r) (srs_call_results r) (srs_pending r).

Definition ssa_refined_raw (r : ssa_refined_state) (l : label) (pc : nat) : astate :=
  AState l pc (srs_env r).

(** Refined initial states retain exactly the typed external entry arguments in pending slots. *)
Definition ssa_refined_initial_state (P : program) (f : func) (r : ssa_refined_state) : Prop :=
  exists fd b cs,
    find_func P f = Some fd /\ find_block fd (fentry fd) = Some b /\
    map ty_of cs = map snd (bparams b) /\ Forall valid_cval cs /\
    r = SsaRefinedState (SsaBeforeParams (fentry fd)) (fun _ => None) (fun _ => None)
      (ssa_pending_write (fun _ => None) cs).

(** Each transfer reads the selected source list once, before any parameter is written. *)
Inductive ssa_refined_step (ext : nat -> list cval -> option cval)
    (P : program) (f : func) : ssa_refined_state -> list event -> ssa_refined_state -> Prop :=
  | SsaStepBind : forall r l fd b cs env,
      srs_point r = SsaBeforeParams l ->
      find_func P f = Some fd -> find_block fd l = Some b ->
      read_args (srs_pending r) (seq 0 (length (bparams b))) = Some cs ->
      bind_params (srs_env r) (bparams b) cs = Some env ->
      ssa_refined_step ext P f r []
        (SsaRefinedState (SsaExecPoint l 0) env (srs_call_results r) (srs_pending r))
  | SsaStepInstruction : forall r l pc i tr env,
      srs_point r = SsaExecPoint l pc ->
      at_instr P (activation_frame f (ssa_refined_raw r l pc)) i ->
      activation_step ext P f (ssa_refined_raw r l pc) tr (AState l (S pc) env) ->
      ssa_refined_step ext P f r tr
        (SsaRefinedState (SsaExecPoint l (S pc)) env (srs_call_results r) (srs_pending r))
  | SsaStepTransfer : forall r l pc t dst args slot cs env,
      srs_point r = SsaExecPoint l pc ->
      at_term P (activation_frame f (ssa_refined_raw r l pc)) t ->
      (match t with TCall _ _ _ | TRet _ => False | _ => True end) ->
      ssa_term_slot (srs_env r) t = Some slot ->
      nth_error (term_edges t) slot = Some (dst, args) ->
      read_args (srs_env r) args = Some cs ->
      jump_env P (activation_frame f (ssa_refined_raw r l pc)) dst cs = Some env ->
      ssa_refined_step ext P f r []
        (SsaRefinedState (SsaBeforeParams dst) (srs_env r) (srs_call_results r)
          (ssa_pending_write (srs_pending r) cs))
  | SsaStepMakeCall : forall r l pc c args k ps result cs v env,
      srs_point r = SsaExecPoint l pc ->
      at_term P (activation_frame f (ssa_refined_raw r l pc)) (TCall c args k) ->
      callee_sig P (static_ty P f) c = Some (ps, result) ->
      read_args (srs_env r) (term_uses (TCall c args k)) = Some cs ->
      ty_of v = result -> valid_cval v ->
      jump_env P (activation_frame f (ssa_refined_raw r l pc)) k [v] = Some env ->
      ssa_refined_step ext P f r []
        (SsaRefinedState (SsaCallReady l) (srs_env r)
          (env_set (srs_call_results r) l v) (srs_pending r))
  | SsaStepCallTransfer : forall r l fd b c args k v env,
      srs_point r = SsaCallReady l ->
      find_func P f = Some fd -> find_block fd l = Some b -> bterm b = TCall c args k ->
      srs_call_results r l = Some v ->
      jump_env P (activation_frame f (ssa_refined_raw r l (length (bbody b)))) k [v] =
        Some env ->
      ssa_refined_step ext P f r []
        (SsaRefinedState (SsaBeforeParams k) (srs_env r) (srs_call_results r)
          (ssa_pending_write (srs_pending r) [v]))
  | SsaStepReturn : forall r l pc x v,
      srs_point r = SsaExecPoint l pc ->
      at_term P (activation_frame f (ssa_refined_raw r l pc)) (TRet x) ->
      srs_env r x = Some v ->
      ssa_refined_step ext P f r [EvRet v] (ssa_refined_set_point r (SsaAfterReturn l)).

(** The refined activation uses silent administrative parameter and call-result steps. *)
Definition ssa_refined_activation (ext : nat -> list cval -> option cval)
    (P : program) (f : func) : semantics ssa_refined_state event :=
  Semantics (ssa_refined_initial_state P f) (ssa_refined_step ext P f).

(** Stable states are original execution points or completed returns. *)
Definition ssa_refined_stable (r : ssa_refined_state) : Prop :=
  match srs_point r with
  | SsaExecPoint _ _ | SsaAfterReturn _ => True
  | _ => False
  end.

Definition ssa_refined_final (r : ssa_refined_state) : Prop :=
  exists l, srs_point r = SsaAfterReturn l.

Definition ssa_refined_trapped (ext : nat -> list cval -> option cval)
    (P : program) (f : func) (r : ssa_refined_state) : Prop :=
  exists l pc, srs_point r = SsaExecPoint l pc /\
    activation_trapped ext P f (ssa_refined_raw r l pc).

(** Only stable source traps and completed returns are declared endings. *)
Definition ssa_refined_endings (ext : nat -> list cval -> option cval)
    (P : program) (f : func) : endings ssa_refined_state :=
  Endings ssa_refined_final (ssa_refined_trapped ext P f) (fun _ => False).

(** The stable relation equates source environments pointwise and ignores ghost call slots. *)
Definition ssa_refined_rel (P : program) (f : func) (a : astate)
    (r : ssa_refined_state) : Prop :=
  (exists fd b, find_func P f = Some fd /\ find_block fd (alabel a) = Some b /\
    ((apc a <= length (bbody b) /\ srs_point r = SsaExecPoint (alabel a) (apc a)) \/
     (exists x, bterm b = TRet x /\ apc a = S (length (bbody b)) /\
       srs_point r = SsaAfterReturn (alabel a)))) /\
  (forall x, aenv a x = srs_env r x).

(** A macro executes at least one step and has no stable intermediate state. *)
Inductive ssa_refined_macro (m : semantics ssa_refined_state event)
    : ssa_refined_state -> list event -> ssa_refined_state -> Prop :=
  | SsaMacroLast : forall r tr t,
      step m r tr t -> ssa_refined_stable t -> ssa_refined_macro m r tr t
  | SsaMacroMore : forall r tr1 u tr2 t,
      step m r tr1 u -> ~ ssa_refined_stable u -> ssa_refined_macro m u tr2 t ->
      ssa_refined_macro m r (tr1 ++ tr2) t.

Definition ssa_administrative_rank (r : ssa_refined_state) : nat :=
  match srs_point r with
  | SsaBeforeParams _ => 1
  | SsaCallReady _ => 2
  | _ => 0
  end.

(** Every step from an intermediate state is silent and strictly reduces its remaining phase. *)
Lemma ssa_administrative_step ext P f r tr r' :
  step (ssa_refined_activation ext P f) r tr r' -> ~ ssa_refined_stable r ->
  tr = [] /\ ssa_administrative_rank r' < ssa_administrative_rank r.
Proof.
  intros Hstep Hunstable.
  destruct Hstep as
    [r l fd b cs env Hpoint Hf Hb Hread Hbind
    |r l pc i tr env Hpoint Hat Hstep
    |r l pc t dst args slot cs env Hpoint Hat Hkind Hslot Hedge Hread Hbind
    |r l pc c args k ps result cs v env Hpoint Hat Hsig Hread Htype Hvalid Hbind
    |r l fd b c args k v env Hpoint Hf Hb Hterm Hvalue Hbind
    |r l pc x v Hpoint Hat Hvalue].
  all: try (exfalso; apply Hunstable; unfold ssa_refined_stable; rewrite Hpoint; exact I).
  all: split; [reflexivity|]; unfold ssa_administrative_rank; rewrite Hpoint; cbn; lia.
Qed.

Definition ssa_administrative_steps (m : semantics ssa_refined_state event) :=
  ssa_admin_steps m ssa_refined_stable.

(** At most two consecutive administrative steps occur, including the initial parameter bind. *)
Lemma ssa_administrative_bound ext P f r n t :
  ssa_administrative_steps (ssa_refined_activation ext P f) r n t -> n <= 2.
Proof.
  intro Hsteps.
  assert (Hrank : n <= ssa_administrative_rank r).
  { induction Hsteps as [r|r u n t Hunstable Hstep Hsteps IH]; [lia|].
    destruct (ssa_administrative_step ext P f r [] u Hstep Hunstable) as [_ Hdecrease].
    lia. }
  unfold ssa_administrative_rank in Hrank; destruct (srs_point r); lia.
Qed.

(** * Pending-slot and environment equations *)

Local Lemma ssa_numbered_index {A} (xs : list A) start i a :
  nth_error xs i = Some a ->
  Map.get nat_encoding (start + i)
    (first_index (combine (seq start (length xs)) xs)) = Some a.
Proof.
  revert start i; induction xs as [|x xs IH]; intros start [|i] Hnth;
    cbn in Hnth; try discriminate.
  - injection Hnth as <-; cbn [length seq combine first_index].
    rewrite Nat.add_0_r; apply Map.get_set_same.
  - cbn [length seq combine first_index].
    rewrite Map.get_set_other by lia.
    replace (start + S i) with (S start + i) by lia.
    apply IH; exact Hnth.
Qed.

Local Lemma ssa_numbered_index_out {A} (xs : list A) start i :
  i < start \/ start + length xs <= i ->
  Map.get nat_encoding i (first_index (combine (seq start (length xs)) xs)) = None.
Proof.
  revert start; induction xs as [|x xs IH]; intros start Houtside.
  - apply Map.get_empty.
  - cbn [length seq combine first_index].
    rewrite Map.get_set_other by (cbn [length] in Houtside; lia).
    apply IH; cbn [length] in Houtside; lia.
Qed.

(** Written slots contain exactly the already-read incoming values. *)
Lemma ssa_pending_write_lookup old cs i :
  i < length cs -> ssa_pending_write old cs i = nth_error cs i.
Proof.
  intro Hin; unfold ssa_pending_write.
  destruct (nth_error cs i) as [c|] eqn:Hnth.
  - rewrite <- (Nat.add_0_l i) at 1.
    rewrite (ssa_numbered_index cs 0 i c Hnth); reflexivity.
  - apply nth_error_None in Hnth; lia.
Qed.

(** Slots beyond the selected argument list retain their old values. *)
Lemma ssa_pending_write_frame old cs i :
  length cs <= i -> ssa_pending_write old cs i = old i.
Proof.
  intro Houtside; unfold ssa_pending_write.
  rewrite ssa_numbered_index_out by (right; lia); reflexivity.
Qed.

Local Lemma ssa_numbered_values (env : nat -> option cval) (cs : list cval) start :
  (forall i c, nth_error cs i = Some c -> env (start + i) = Some c) ->
  Forall2 (fun i c => env i = Some c) (seq start (length cs)) cs.
Proof.
  revert start; induction cs as [|c cs IH]; intros start Hvalues; [constructor|].
  cbn [length seq]; constructor.
  - replace start with (start + 0) by lia; apply Hvalues; reflexivity.
  - apply IH; intros i value Hnth.
    replace (S start + i) with (start + S i) by lia.
    apply Hvalues; exact Hnth.
Qed.

(** Reading a freshly written pending prefix recovers the same ordered argument list. *)
Lemma ssa_pending_write_read old cs :
  read_args (ssa_pending_write old cs) (seq 0 (length cs)) = Some cs.
Proof.
  apply ssa_read_args_complete, ssa_numbered_values; intros i c Hnth.
  rewrite Nat.add_0_l, ssa_pending_write_lookup.
  - exact Hnth.
  - apply nth_error_Some; rewrite Hnth; discriminate.
Qed.

Local Lemma ssa_initial_bind_run ext P f fd b cs env :
  find_func P f = Some fd -> find_block fd (fentry fd) = Some b ->
  bind_params (fun _ => None) (bparams b) cs = Some env ->
  let r := SsaRefinedState (SsaBeforeParams (fentry fd)) (fun _ => None) (fun _ => None)
    (ssa_pending_write (fun _ => None) cs) in
  let r' := SsaRefinedState (SsaExecPoint (fentry fd) 0) env (fun _ => None)
    (ssa_pending_write (fun _ => None) cs) in
  exec (ssa_refined_activation ext P f) r [] r' /\
    ssa_refined_rel P f (AState (fentry fd) 0 env) r'.
Proof.
  intros Hf Hb Hbind; cbn zeta; split.
  - apply exec_one; eapply SsaStepBind; try reflexivity; try eassumption.
    cbn [srs_pending]; rewrite (ssa_bind_length _ _ _ _ Hbind).
    apply ssa_pending_write_read.
  - split; [exists fd, b|intro x; reflexivity].
    split; [exact Hf|]; split; [exact Hb|]; left; split; [cbn; lia|reflexivity].
Qed.

(** Both initial-state directions bind the same external values before reaching a stable point. *)
Theorem ssa_refined_initial (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  (forall a, initial (activation ext P f) a ->
    exists r r', initial (ssa_refined_activation ext P f) r /\
      exec (ssa_refined_activation ext P f) r [] r' /\ ssa_refined_rel P f a r') /\
  (forall r, initial (ssa_refined_activation ext P f) r ->
    exists a r', initial (activation ext P f) a /\
      exec (ssa_refined_activation ext P f) r [] r' /\ ssa_refined_rel P f a r').
Proof.
  intros Hwf Hfunction; split.
  - intros a [fd [b [cs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]].
    exists (SsaRefinedState (SsaBeforeParams (fentry fd)) (fun _ => None) (fun _ => None)
      (ssa_pending_write (fun _ => None) cs)),
      (SsaRefinedState (SsaExecPoint (fentry fd) 0) env (fun _ => None)
        (ssa_pending_write (fun _ => None) cs)).
    split.
    + exists fd, b, cs; repeat split; try assumption; reflexivity.
    + exact (ssa_initial_bind_run ext P f fd b cs env Hf Hb Hbind).
  - intros r [fd [b [cs [Hf [Hb [Htypes [Hvalid ->]]]]]]].
    assert (Hlength : length (bparams b) = length cs).
    { apply (f_equal (@length ty)) in Htypes; rewrite !length_map in Htypes; lia. }
    destruct (ssa_bind_exists (fun _ => None) (bparams b) cs Hlength) as [env Hbind].
    exists (AState (fentry fd) 0 env),
      (SsaRefinedState (SsaExecPoint (fentry fd) 0) env (fun _ => None)
        (ssa_pending_write (fun _ => None) cs)).
    split.
    + exists fd, b, cs, env; repeat split; try assumption; reflexivity.
    + exact (ssa_initial_bind_run ext P f fd b cs env Hf Hb Hbind).
Qed.

(** * Pointwise source-environment transport *)

Definition ssa_activation_agrees (a b : astate) : Prop :=
  alabel a = alabel b /\ apc a = apc b /\ ssa_env_agrees (aenv a) (aenv b).

Local Lemma ssa_at_instr_env P f a env i :
  at_instr P (activation_frame f a) i ->
  at_instr P (activation_frame f (AState (alabel a) (apc a) env)) i.
Proof.
  intros [fd [b [Hf [Hb Hnth]]]]; exists fd, b; repeat split; assumption.
Qed.

Local Lemma ssa_at_term_env P f a env t :
  at_term P (activation_frame f a) t ->
  at_term P (activation_frame f (AState (alabel a) (apc a) env)) t.
Proof.
  intros [fd [b [Hf [Hb [Hpc Hterm]]]]]; exists fd, b; repeat split; assumption.
Qed.

Local Lemma ssa_jump_agrees P f a env dst cs target :
  ssa_env_agrees (aenv a) env ->
  jump_env P (activation_frame f a) dst cs = Some target ->
  exists target',
    jump_env P (activation_frame f (AState (alabel a) (apc a) env)) dst cs = Some target' /\
    ssa_env_agrees target target'.
Proof.
  intros Hagree; unfold jump_env; cbn [activation_frame ffunc fenv].
  destruct (find_func P f) as [fd|]; [|discriminate].
  destruct (find_block fd dst) as [b|]; [|discriminate].
  apply ssa_bind_agrees; exact Hagree.
Qed.

(** Pointwise equal environments can execute the same source step and preserve equality. *)
Lemma ssa_activation_step_agrees ext P f a tr a' env :
  step (activation ext P f) a tr a' -> ssa_env_agrees (aenv a) env ->
  exists b', step (activation ext P f) (AState (alabel a) (apc a) env) tr b' /\
    ssa_activation_agrees a' b'.
Proof.
  intros Hstep Hagree.
  cbn [activation step].
  destruct Hstep as
    [a x o args cs v Hat Hread Heval
    |a x n block offset Hat
    |a p Hat
    |a x t sz p v Hat Htype Hvalid
    |a sz p x Hat
    |a x v Hat Hvalue
    |a l args cs target Hat Hread Hbind
    |a c l1 a1 l2 a2 z l args cs target Hat Hcond Hchoice Hread Hbind
    |a c cases d da z l args cs target Hat Hcond Hchoice Hread Hbind
    |a c args k ps result cs v target Hat Hsig Hread Htype Hvalid Hbind
    |a x v Hat Hvalue].
  - exists (AState (alabel a) (S (apc a)) (env_set env x v)); split.
    + eapply AOp with (a := AState (alabel a) (apc a) env);
        [apply ssa_at_instr_env; exact Hat| |exact Heval].
      cbn [aenv]; rewrite <- (ssa_read_agrees _ _ args Hagree); exact Hread.
    + split; [reflexivity|]; split; [reflexivity|apply ssa_set_agrees; exact Hagree].
  - exists (AState (alabel a) (S (apc a)) (env_set env x (VPtr block offset))); split.
    + apply AAlloc with (a := AState (alabel a) (apc a) env) (n := n);
        apply ssa_at_instr_env; exact Hat.
    + split; [reflexivity|]; split; [reflexivity|apply ssa_set_agrees; exact Hagree].
  - exists (AState (alabel a) (S (apc a)) env); split.
    + apply AFree with (a := AState (alabel a) (apc a) env) (p := p);
        apply ssa_at_instr_env; exact Hat.
    + split; [reflexivity|]; split; [reflexivity|exact Hagree].
  - exists (AState (alabel a) (S (apc a)) (env_set env x v)); split.
    + eapply ALoad with (a := AState (alabel a) (apc a) env);
        [apply ssa_at_instr_env; exact Hat|exact Htype|exact Hvalid].
    + split; [reflexivity|]; split; [reflexivity|apply ssa_set_agrees; exact Hagree].
  - exists (AState (alabel a) (S (apc a)) env); split.
    + eapply AStore with (a := AState (alabel a) (apc a) env);
        apply ssa_at_instr_env; exact Hat.
    + split; [reflexivity|]; split; [reflexivity|exact Hagree].
  - exists (AState (alabel a) (S (apc a)) env); split.
    + eapply AOutput with (a := AState (alabel a) (apc a) env);
        [apply ssa_at_instr_env; exact Hat|].
      cbn [aenv]; rewrite <- (Hagree x); exact Hvalue.
    + split; [reflexivity|]; split; [reflexivity|exact Hagree].
  - destruct (ssa_jump_agrees P f a env l cs target Hagree Hbind)
      as [target' [Hbind' Htarget]].
    exists (AState l 0 target'); split.
    + eapply AJump with (a := AState (alabel a) (apc a) env);
        [apply ssa_at_term_env; exact Hat| |exact Hbind'].
      cbn [aenv]; rewrite <- (ssa_read_agrees _ _ args Hagree); exact Hread.
    + split; [reflexivity|]; split; [reflexivity|exact Htarget].
  - destruct (ssa_jump_agrees P f a env l cs target Hagree Hbind)
      as [target' [Hbind' Htarget]].
    exists (AState l 0 target'); split.
    + eapply ABranch with (a := AState (alabel a) (apc a) env);
        [apply ssa_at_term_env; exact Hat| |exact Hchoice| |exact Hbind'].
      * cbn [aenv]; rewrite <- (Hagree c); exact Hcond.
      * cbn [aenv]; rewrite <- (ssa_read_agrees _ _ args Hagree); exact Hread.
    + split; [reflexivity|]; split; [reflexivity|exact Htarget].
  - destruct (ssa_jump_agrees P f a env l cs target Hagree Hbind)
      as [target' [Hbind' Htarget]].
    exists (AState l 0 target'); split.
    + eapply ASwitch with (a := AState (alabel a) (apc a) env);
        [apply ssa_at_term_env; exact Hat| |exact Hchoice| |exact Hbind'].
      * cbn [aenv]; rewrite <- (Hagree c); exact Hcond.
      * cbn [aenv]; rewrite <- (ssa_read_agrees _ _ args Hagree); exact Hread.
    + split; [reflexivity|]; split; [reflexivity|exact Htarget].
  - destruct (ssa_jump_agrees P f a env k [v] target Hagree Hbind)
      as [target' [Hbind' Htarget]].
    exists (AState k 0 target'); split.
    + eapply ACall with (a := AState (alabel a) (apc a) env);
        [apply ssa_at_term_env; exact Hat|exact Hsig| |exact Htype|
        exact Hvalid|exact Hbind'].
      cbn [aenv].
      rewrite <- (ssa_read_agrees _ _ (term_uses (TCall c args k)) Hagree); exact Hread.
    + split; [reflexivity|]; split; [reflexivity|exact Htarget].
  - exists (AState (alabel a) (S (apc a)) env); split.
    + eapply AReturn with (a := AState (alabel a) (apc a) env);
        [apply ssa_at_term_env; exact Hat|].
      cbn [aenv]; rewrite <- (Hagree x); exact Hvalue.
    + split; [reflexivity|]; split; [reflexivity|exact Hagree].
Qed.

Local Lemma ssa_refined_rel_transport P f a b r :
  ssa_activation_agrees a b -> ssa_refined_rel P f a r -> ssa_refined_rel P f b r.
Proof.
  destruct a as [l pc env], b as [l' pc' env'];
    intros [Hlabel [Hpc Hagree]] [Hcontrol Hvalues].
  cbn in Hlabel, Hpc; subst l' pc'; split; [exact Hcontrol|].
  intro x; rewrite <- (Hagree x); exact (Hvalues x).
Qed.

Local Lemma ssa_administrative_exec ext P f r n t :
  ssa_administrative_steps (ssa_refined_activation ext P f) r n t ->
  exec (ssa_refined_activation ext P f) r [] t.
Proof.
  intro Hsteps; induction Hsteps as [r|r u n t Hunstable Hstep Hsteps IH].
  - constructor.
  - eapply exec_step with (l := []) (tr := []); [exact Hstep|exact IH].
Qed.

Local Lemma ssa_unstable_macro ext P f r tr t :
  ssa_refined_macro (ssa_refined_activation ext P f) r tr t ->
  ~ ssa_refined_stable r ->
  tr = [] /\ exists n, ssa_administrative_steps (ssa_refined_activation ext P f) r n t /\
    ssa_refined_stable t.
Proof.
  intro Hmacro; induction Hmacro as
    [r tr t Hstep Hstable|r tr1 u tr2 t Hstep Hmiddle Htail IH]; intro Hunstable.
  - destruct (ssa_administrative_step ext P f r tr t Hstep Hunstable) as [-> Hrank].
    split; [reflexivity|]; exists 1; split; [|exact Hstable].
    eapply SsaAdminStep; [exact Hunstable|exact Hstep|constructor].
  - destruct (ssa_administrative_step ext P f r tr1 u Hstep Hunstable) as [-> Hrank].
    destruct (IH Hmiddle) as [-> [n [Hsteps Hstable]]].
    split; [reflexivity|]; exists (S n); split; [|exact Hstable].
    eapply SsaAdminStep; eassumption.
Qed.

(** Every macro's first edge carries its entire trace; the remaining administration is silent. *)
Lemma ssa_macro_head ext P f r tr t :
  ssa_refined_macro (ssa_refined_activation ext P f) r tr t ->
  exists u n, step (ssa_refined_activation ext P f) r tr u /\
    ssa_administrative_steps (ssa_refined_activation ext P f) u n t /\
    ssa_refined_stable t.
Proof.
  intro Hmacro; destruct Hmacro as
    [r tr t Hstep Hstable|r tr1 u tr2 t Hstep Hmiddle Htail].
  - exists t, 0; split; [exact Hstep|]; split; [constructor|exact Hstable].
  - destruct (ssa_unstable_macro ext P f u tr2 t Htail Hmiddle)
      as [-> [n [Hsteps Hstable]]].
    rewrite app_nil_r; exists u, n; repeat split; assumption.
Qed.

Local Lemma ssa_stable_administrative ext P f r n t :
  ssa_refined_stable r ->
  ssa_administrative_steps (ssa_refined_activation ext P f) r n t -> n = 0 /\ t = r.
Proof.
  intros Hstable Hsteps; destruct Hsteps as [r|r u n t Hunstable Hstep Hsteps].
  - split; reflexivity.
  - contradiction.
Qed.

Local Lemma ssa_transfer_bind ext P f r l pc dst cs env :
  jump_env P (activation_frame f (ssa_refined_raw r l pc)) dst cs = Some env ->
  let u := SsaRefinedState (SsaBeforeParams dst) (srs_env r) (srs_call_results r)
    (ssa_pending_write (srs_pending r) cs) in
  let t := SsaRefinedState (SsaExecPoint dst 0) env (srs_call_results r)
    (ssa_pending_write (srs_pending r) cs) in
  step (ssa_refined_activation ext P f) u [] t /\
    ssa_refined_rel P f (AState dst 0 env) t.
Proof.
  unfold jump_env; cbn [activation_frame ssa_refined_raw ffunc fenv].
  destruct (find_func P f) as [fd|] eqn:Hf; [|discriminate].
  destruct (find_block fd dst) as [b|] eqn:Hb; [|discriminate].
  intro Hbind; cbn zeta; split.
  - eapply SsaStepBind with (r := SsaRefinedState (SsaBeforeParams dst) (srs_env r)
      (srs_call_results r) (ssa_pending_write (srs_pending r) cs));
      try reflexivity; try eassumption.
    cbn [srs_pending]; rewrite (ssa_bind_length _ _ _ _ Hbind).
    apply ssa_pending_write_read.
  - split; [exists fd, b|intro x; reflexivity].
    split; [exact Hf|]; split; [exact Hb|]; left; split; [cbn; lia|reflexivity].
Qed.

Definition ssa_completed_head ext P f r tr a : Prop :=
  exists u n t, step (ssa_refined_activation ext P f) r tr u /\
    ssa_administrative_steps (ssa_refined_activation ext P f) u n t /\
    ssa_refined_stable t /\ ssa_refined_rel P f a t.

Local Lemma ssa_instruction_head ext P f r l pc i tr env :
  srs_point r = SsaExecPoint l pc ->
  at_instr P (activation_frame f (ssa_refined_raw r l pc)) i ->
  step (activation ext P f) (ssa_refined_raw r l pc) tr (AState l (S pc) env) ->
  ssa_completed_head ext P f r tr (AState l (S pc) env).
Proof.
  intros Hpoint Hat Hstep.
  exists (SsaRefinedState (SsaExecPoint l (S pc)) env (srs_call_results r) (srs_pending r)),
    0, (SsaRefinedState (SsaExecPoint l (S pc)) env (srs_call_results r) (srs_pending r)).
  split; [eapply SsaStepInstruction with (r := r); eassumption|];
    split; [constructor|].
  split; [exact I|]; split; [|intro x; reflexivity].
  destruct Hat as [fd [b [Hf [Hb Hnth]]]]; exists fd, b.
  split; [exact Hf|]; split; [exact Hb|]; left; split; [|reflexivity].
  change (nth_error (bbody b) pc = Some i) in Hnth.
  assert (Hbound : pc < length (bbody b)).
  { apply nth_error_Some; rewrite Hnth; discriminate. }
  cbn in *; lia.
Qed.

Local Lemma ssa_return_head ext P f r l pc x v :
  srs_point r = SsaExecPoint l pc ->
  at_term P (activation_frame f (ssa_refined_raw r l pc)) (TRet x) ->
  srs_env r x = Some v ->
  ssa_completed_head ext P f r [EvRet v] (AState l (S pc) (srs_env r)).
Proof.
  intros Hpoint Hat Hvalue.
  exists (ssa_refined_set_point r (SsaAfterReturn l)), 0,
    (ssa_refined_set_point r (SsaAfterReturn l)).
  split; [eapply SsaStepReturn with (r := r); eassumption|]; split; [constructor|].
  split; [exact I|]; split; [|intro y; reflexivity].
  destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]]; exists fd, b.
  split; [exact Hf|]; split; [exact Hb|]; right; exists x.
  split; [exact Hterm|]; split; [cbn in *; lia|reflexivity].
Qed.

Local Lemma ssa_transfer_head ext P f r l pc t dst args slot cs env :
  srs_point r = SsaExecPoint l pc ->
  at_term P (activation_frame f (ssa_refined_raw r l pc)) t ->
  (match t with TCall _ _ _ | TRet _ => False | _ => True end) ->
  ssa_term_slot (srs_env r) t = Some slot ->
  nth_error (term_edges t) slot = Some (dst, args) ->
  read_args (srs_env r) args = Some cs ->
  jump_env P (activation_frame f (ssa_refined_raw r l pc)) dst cs = Some env ->
  ssa_completed_head ext P f r [] (AState dst 0 env).
Proof.
  intros Hpoint Hat Hkind Hslot Hedge Hread Hbind.
  destruct (ssa_transfer_bind ext P f r l pc dst cs env Hbind) as [Hstep Hrel].
  exists (SsaRefinedState (SsaBeforeParams dst) (srs_env r) (srs_call_results r)
    (ssa_pending_write (srs_pending r) cs)), 1,
    (SsaRefinedState (SsaExecPoint dst 0) env (srs_call_results r)
      (ssa_pending_write (srs_pending r) cs)).
  split; [eapply SsaStepTransfer with (r := r); eassumption|]; split.
  - eapply SsaAdminStep; [cbn [ssa_refined_stable srs_point]; tauto|exact Hstep|constructor].
  - split; [exact I|exact Hrel].
Qed.

Local Lemma ssa_call_completion ext P f r l pc c args k v env :
  at_term P (activation_frame f (ssa_refined_raw r l pc)) (TCall c args k) ->
  jump_env P (activation_frame f (ssa_refined_raw r l pc)) k [v] = Some env ->
  let u := SsaRefinedState (SsaCallReady l) (srs_env r)
    (env_set (srs_call_results r) l v) (srs_pending r) in
  exists t, ssa_administrative_steps (ssa_refined_activation ext P f) u 2 t /\
    ssa_refined_stable t /\ ssa_refined_rel P f (AState k 0 env) t.
Proof.
  intros Hat Hbind; cbn zeta.
  pose (u := SsaRefinedState (SsaCallReady l) (srs_env r)
    (env_set (srs_call_results r) l v) (srs_pending r)).
  destruct (ssa_transfer_bind ext P f u l pc k [v] env Hbind) as [Hstep Hrel].
  exists (SsaRefinedState (SsaExecPoint k 0) env (srs_call_results u)
    (ssa_pending_write (srs_pending u) [v])); split.
  - eapply SsaAdminStep with (u := SsaRefinedState (SsaBeforeParams k)
      (srs_env u) (srs_call_results u) (ssa_pending_write (srs_pending u) [v])).
    + cbn [ssa_refined_stable srs_point u]; tauto.
    + destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]].
      cbn [activation_frame ssa_refined_raw ffunc flabel fpc alabel apc] in Hf, Hb, Hpc.
      eapply SsaStepCallTransfer with (r := u); try eassumption; try reflexivity.
      change (env_set (srs_call_results r) l v l = Some v).
      unfold env_set; destruct (Nat.eq_dec l l); [reflexivity|contradiction].
    + eapply SsaAdminStep; [cbn [ssa_refined_stable srs_point]; tauto|
        exact Hstep|constructor].
  - split; [exact I|exact Hrel].
Qed.

Local Lemma ssa_call_head ext P f r l pc c args k ps result cs v env :
  srs_point r = SsaExecPoint l pc ->
  at_term P (activation_frame f (ssa_refined_raw r l pc)) (TCall c args k) ->
  callee_sig P (static_ty P f) c = Some (ps, result) ->
  read_args (srs_env r) (term_uses (TCall c args k)) = Some cs ->
  ty_of v = result -> valid_cval v ->
  jump_env P (activation_frame f (ssa_refined_raw r l pc)) k [v] = Some env ->
  ssa_completed_head ext P f r [] (AState k 0 env).
Proof.
  intros Hpoint Hat Hsig Hread Htype Hvalid Hbind.
  destruct (ssa_call_completion ext P f r l pc c args k v env Hat Hbind)
    as [t [Htail [Hstable Hrel]]].
  exists (SsaRefinedState (SsaCallReady l) (srs_env r)
    (env_set (srs_call_results r) l v) (srs_pending r)), 2, t.
  split; [eapply SsaStepMakeCall with (r := r); eassumption|].
  split; [exact Htail|]; split; assumption.
Qed.

Local Lemma ssa_refined_raw_eq r a :
  srs_env r = aenv a -> ssa_refined_raw r (alabel a) (apc a) = a.
Proof.
  destruct a as [l pc env]; cbn [alabel apc aenv].
  intro Henv; unfold ssa_refined_raw; rewrite Henv; reflexivity.
Qed.

Local Lemma ssa_raw_head ext P f a tr a' r :
  step (activation ext P f) a tr a' ->
  srs_point r = SsaExecPoint (alabel a) (apc a) -> srs_env r = aenv a ->
  ssa_completed_head ext P f r tr a'.
Proof.
  intros Hstep Hpoint Henv; pose proof Hstep as Hsource.
  destruct Hstep as
    [a x o args cs v Hat Hread Heval
    |a x n block offset Hat
    |a p Hat
    |a x t sz p v Hat Htype Hvalid
    |a sz p x Hat
    |a x v Hat Hvalue
    |a dst args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases d da z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c args k ps result cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a x v Hat Hvalue].
  all: try (eapply ssa_instruction_head with (l := alabel a) (pc := apc a);
    [exact Hpoint|rewrite (ssa_refined_raw_eq r a Henv); eassumption|
      rewrite (ssa_refined_raw_eq r a Henv); exact Hsource]).
  - eapply ssa_transfer_head with (l := alabel a) (pc := apc a) (t := TJump dst args)
      (args := args) (slot := 0) (cs := cs); try reflexivity.
    + exact Hpoint.
    + rewrite (ssa_refined_raw_eq r a Henv); exact Hat.
    + rewrite Henv; exact Hread.
    + rewrite (ssa_refined_raw_eq r a Henv); exact Hbind.
  - eapply ssa_transfer_head with (l := alabel a) (pc := apc a)
      (t := TBr c l1 a1 l2 a2) (args := args)
      (slot := if Z.eqb z 0 then 1 else 0) (cs := cs).
    + exact Hpoint.
    + rewrite (ssa_refined_raw_eq r a Henv); exact Hat.
    + exact I.
    + rewrite Henv; cbn [ssa_term_slot]; rewrite Hcond; reflexivity.
    + cbn [term_edges]; destruct (Z.eqb z 0); injection Hchoice as <- <-; reflexivity.
    + rewrite Henv; exact Hread.
    + rewrite (ssa_refined_raw_eq r a Henv); exact Hbind.
  - eapply ssa_transfer_head with (l := alabel a) (pc := apc a)
      (t := TSwitch c cases d da) (args := args) (slot := ssa_switch_slot z cases) (cs := cs).
    + exact Hpoint.
    + rewrite (ssa_refined_raw_eq r a Henv); exact Hat.
    + exact I.
    + rewrite Henv; cbn [ssa_term_slot]; rewrite Hcond; reflexivity.
    + rewrite <- Hchoice; exact (ssa_switch_slot_target z cases d da).
    + rewrite Henv; exact Hread.
    + rewrite (ssa_refined_raw_eq r a Henv); exact Hbind.
  - eapply ssa_call_head with (l := alabel a) (pc := apc a) (c := c) (args := args)
      (ps := ps) (result := result) (cs := cs) (v := v).
    + exact Hpoint.
    + rewrite (ssa_refined_raw_eq r a Henv); exact Hat.
    + exact Hsig.
    + rewrite Henv; exact Hread.
    + exact Htype.
    + exact Hvalid.
    + rewrite (ssa_refined_raw_eq r a Henv); exact Hbind.
  - change (ssa_completed_head ext P f r [EvRet v]
      (AState (alabel a) (S (apc a)) (aenv a))).
    rewrite <- Henv; eapply ssa_return_head.
    + exact Hpoint.
    + rewrite (ssa_refined_raw_eq r a Henv); exact Hat.
    + rewrite Henv; exact Hvalue.
Qed.

Local Lemma ssa_head_macro ext P f r tr u n t :
  step (ssa_refined_activation ext P f) r tr u ->
  ssa_administrative_steps (ssa_refined_activation ext P f) u n t ->
  ssa_refined_stable t -> ssa_refined_macro (ssa_refined_activation ext P f) r tr t.
Proof.
  intros Hhead Hsteps; revert r tr Hhead.
  induction Hsteps as [u|u v n t Hunstable Hstep Hsteps IH];
    intros r tr Hhead Hstable.
  - eapply SsaMacroLast; eassumption.
  - rewrite <- (app_nil_r tr).
    eapply SsaMacroMore; [exact Hhead|exact Hunstable|].
    apply IH; assumption.
Qed.

Definition ssa_administrative_next (P : program) (f : func) (r : ssa_refined_state)
    : option ssa_refined_state :=
  match srs_point r with
  | SsaBeforeParams l =>
    match find_func P f with
    | Some fd =>
      match find_block fd l with
      | Some b =>
        match read_args (srs_pending r) (seq 0 (length (bparams b))) with
        | Some cs =>
          match bind_params (srs_env r) (bparams b) cs with
          | Some env => Some (SsaRefinedState (SsaExecPoint l 0) env
              (srs_call_results r) (srs_pending r))
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | SsaCallReady l =>
    match find_func P f with
    | Some fd =>
      match find_block fd l with
      | Some b =>
        match bterm b, srs_call_results r l with
        | TCall _ _ k, Some v => Some (SsaRefinedState (SsaBeforeParams k) (srs_env r)
            (srs_call_results r) (ssa_pending_write (srs_pending r) [v]))
        | _, _ => None
        end
      | None => None
      end
    | None => None
    end
  | _ => None
  end.

Local Lemma ssa_administrative_next_agrees ext P f r tr r' :
  step (ssa_refined_activation ext P f) r tr r' -> ~ ssa_refined_stable r ->
  tr = [] /\ ssa_administrative_next P f r = Some r'.
Proof.
  intros Hstep Hunstable.
  destruct Hstep as
    [r l fd b cs env Hpoint Hf Hb Hread Hbind
    |r l pc i tr env Hpoint Hat Hstep
    |r l pc t dst args slot cs env Hpoint Hat Hkind Hslot Hedge Hread Hbind
    |r l pc c args k ps result cs v env Hpoint Hat Hsig Hread Htype Hvalid Hbind
    |r l fd b c args k v env Hpoint Hf Hb Hterm Hvalue Hbind
    |r l pc x v Hpoint Hat Hvalue].
  all: try (exfalso; apply Hunstable; unfold ssa_refined_stable; rewrite Hpoint; exact I).
  - split; [reflexivity|]; unfold ssa_administrative_next.
    rewrite Hpoint, Hf, Hb, Hread, Hbind; reflexivity.
  - split; [reflexivity|]; unfold ssa_administrative_next.
    rewrite Hpoint, Hf, Hb, Hterm, Hvalue; reflexivity.
Qed.

Local Lemma ssa_administrative_deterministic ext P f r tr u tr' v :
  ~ ssa_refined_stable r -> step (ssa_refined_activation ext P f) r tr u ->
  step (ssa_refined_activation ext P f) r tr' v -> u = v.
Proof.
  intros Hunstable Hstep Hstep'.
  destruct (ssa_administrative_next_agrees ext P f r tr u Hstep Hunstable) as [_ Hu].
  destruct (ssa_administrative_next_agrees ext P f r tr' v Hstep' Hunstable) as [_ Hv].
  congruence.
Qed.

Local Lemma ssa_administrative_completion_unique ext P f r n t n' t' :
  ssa_administrative_steps (ssa_refined_activation ext P f) r n t ->
  ssa_administrative_steps (ssa_refined_activation ext P f) r n' t' ->
  ssa_refined_stable t -> ssa_refined_stable t' -> t = t'.
Proof.
  intro Hsteps; revert n' t'.
  induction Hsteps as [r|r u n t Hunstable Hstep Htail IH];
    intros n' t' Hother Hstable Hstable'.
  - destruct (ssa_stable_administrative ext P f r n' t' Hstable Hother) as [_ ->].
    reflexivity.
  - destruct Hother as [r|r v n' t' Hunstable' Hstep' Htail'].
    + contradiction.
    + assert (Heq : u = v) by
        (eapply ssa_administrative_deterministic; eassumption).
      subst v; eapply IH; eassumption.
Qed.

Local Lemma ssa_activation_final_no_step ext P f a :
  activation_final P f a -> forall tr a', ~ step (activation ext P f) a tr a'.
Proof.
  intros [fd [b [Hf [Hb Hpast]]]] tr a' Hstep; destruct Hstep.
  all: match goal with
  | Hat : at_instr ?source_program ?fr ?i |- _ =>
    pose proof (ssa_at_instr_before source_program fr i fd b Hat Hf Hb) as Hbefore;
    cbn [activation_frame fpc] in Hbefore, Hpast; lia
  | Hat : at_term ?source_program ?fr ?t |- _ =>
    pose proof (ssa_at_term_end source_program fr t fd b Hat Hf Hb) as Hend;
    cbn [activation_frame fpc] in Hend, Hpast; lia
  end.
Qed.

Local Lemma ssa_activation_agrees_sym a b :
  ssa_activation_agrees a b -> ssa_activation_agrees b a.
Proof.
  intros [Hlabel [Hpc Henv]]; split; [symmetry; exact Hlabel|].
  split; [symmetry; exact Hpc|intro x; symmetry; exact (Henv x)].
Qed.

Local Lemma ssa_refined_forward ext P f a r tr a' :
  ssa_refined_rel P f a r -> step (activation ext P f) a tr a' ->
  exists r', ssa_refined_macro (ssa_refined_activation ext P f) r tr r' /\
    ssa_refined_rel P f a' r'.
Proof.
  intros [[fd [b [Hf [Hb [Hexec|[x [Hterm [Hpc Hpoint]]]]]]]] Henv] Hstep.
  - destruct Hexec as [Hbound Hpoint].
    destruct (ssa_activation_step_agrees ext P f a tr a' (srs_env r) Hstep Henv)
      as [b' [Hstep' Hagrees]].
    destruct (ssa_raw_head ext P f (AState (alabel a) (apc a) (srs_env r)) tr b' r
      Hstep' Hpoint eq_refl) as [u [n [r' [Hhead [Htail [Hstable Hrel]]]]]].
    exists r'; split; [eapply ssa_head_macro; eassumption|].
    eapply ssa_refined_rel_transport; [apply ssa_activation_agrees_sym; exact Hagrees|exact Hrel].
  - exfalso; apply (ssa_activation_final_no_step ext P f a) with (tr := tr) (a' := a').
    + exists fd, b; split; [exact Hf|]; split; [exact Hb|].
      change (length (bbody b) < apc a); lia.
    + exact Hstep.
Qed.

Local Lemma ssa_refined_rel_stable P f a r :
  ssa_refined_rel P f a r -> ssa_refined_stable r.
Proof.
  intros [Hcontrol Henv].
  destruct Hcontrol as [fd [b [Hf [Hb [[Hbound Hpoint]|[x [Hterm [Hpc Hpoint]]]]]]]].
  all: unfold ssa_refined_stable; rewrite Hpoint; exact I.
Qed.

Local Lemma ssa_refined_rel_agrees P f a b r :
  ssa_refined_rel P f a r -> ssa_refined_rel P f b r -> ssa_activation_agrees a b.
Proof.
  intros [HcontrolA HenvA] [HcontrolB HenvB].
  assert (Hvalues : ssa_env_agrees (aenv a) (aenv b)).
  { intro x; rewrite (HenvA x), (HenvB x); reflexivity. }
  destruct HcontrolA as [fdA [blockA [HfA [HbA HcaseA]]]].
  destruct HcontrolB as [fdB [blockB [HfB [HbB HcaseB]]]].
  destruct HcaseA as [[HboundA HpointA]|[xA [HtermA [HpcA HpointA]]]];
    destruct HcaseB as [[HboundB HpointB]|[xB [HtermB [HpcB HpointB]]]];
    try (exfalso; congruence).
  - assert (Hlabel : alabel a = alabel b) by congruence.
    assert (Hpc : apc a = apc b) by congruence.
    split; [exact Hlabel|]; split; assumption.
  - assert (Hlabel : alabel a = alabel b) by congruence.
    assert (Hfd : fdA = fdB) by congruence; subst fdB.
    rewrite <- Hlabel in HbB.
    assert (Hblock : blockA = blockB) by congruence; subst blockB.
    split; [exact Hlabel|]; split; [congruence|exact Hvalues].
Qed.

Local Lemma ssa_exec_source_rel P f r l pc fd b :
  srs_point r = SsaExecPoint l pc -> find_func P f = Some fd ->
  find_block fd l = Some b -> pc <= length (bbody b) ->
  ssa_refined_rel P f (ssa_refined_raw r l pc) r.
Proof.
  intros Hpoint Hf Hb Hbound; split; [exists fd, b|intro x; reflexivity].
  split; [exact Hf|]; split; [exact Hb|]; left; split; assumption.
Qed.

Local Lemma ssa_instr_source_rel P f r l pc i :
  srs_point r = SsaExecPoint l pc ->
  at_instr P (activation_frame f (ssa_refined_raw r l pc)) i ->
  ssa_refined_rel P f (ssa_refined_raw r l pc) r.
Proof.
  intros Hpoint [fd [b [Hf [Hb Hnth]]]].
  change (nth_error (bbody b) pc = Some i) in Hnth.
  eapply ssa_exec_source_rel; try eassumption.
  assert (Hbound : pc < length (bbody b)) by
    (apply nth_error_Some; rewrite Hnth; discriminate).
  lia.
Qed.

Local Lemma ssa_term_source_rel P f r l pc t :
  srs_point r = SsaExecPoint l pc ->
  at_term P (activation_frame f (ssa_refined_raw r l pc)) t ->
  ssa_refined_rel P f (ssa_refined_raw r l pc) r.
Proof.
  intros Hpoint [fd [b [Hf [Hb [Hpc Hterm]]]]].
  eapply ssa_exec_source_rel; try eassumption.
  change (pc = length (bbody b)) in Hpc; lia.
Qed.

Local Lemma ssa_transfer_source_step ext P f r l pc t dst args slot cs env :
  at_term P (activation_frame f (ssa_refined_raw r l pc)) t ->
  (match t with TCall _ _ _ | TRet _ => False | _ => True end) ->
  ssa_term_slot (srs_env r) t = Some slot ->
  nth_error (term_edges t) slot = Some (dst, args) ->
  read_args (srs_env r) args = Some cs ->
  jump_env P (activation_frame f (ssa_refined_raw r l pc)) dst cs = Some env ->
  step (activation ext P f) (ssa_refined_raw r l pc) [] (AState dst 0 env).
Proof.
  intros Hat Hkind Hslot Hedge Hread Hbind.
  destruct t as [target actual|c l1 a1 l2 a2|c cases d da|c actual k|x];
    try contradiction.
  - cbn [ssa_term_slot] in Hslot; injection Hslot as <-.
    cbn [term_edges] in Hedge; injection Hedge as <- <-.
    eapply AJump with (a := ssa_refined_raw r l pc); eassumption.
  - cbn [ssa_term_slot] in Hslot.
    destruct (srs_env r c) as [value|] eqn:Hcond; [|discriminate].
    destruct value as [[|] z|block off|callee|bits|bits]; try discriminate.
    injection Hslot as <-.
    assert (Hchoice : (dst, args) = if Z.eqb z 0 then (l2, a2) else (l1, a1)).
    { destruct (Z.eqb z 0); cbn [term_edges] in Hedge; injection Hedge as Heq; congruence. }
    eapply ABranch with (a := ssa_refined_raw r l pc) (z := z);
      [exact Hat|exact Hcond|exact Hchoice|exact Hread|exact Hbind].
  - cbn [ssa_term_slot] in Hslot.
    destruct (srs_env r c) as [value|] eqn:Hcond; [|discriminate].
    destruct value as [[|] z|block off|callee|bits|bits]; try discriminate.
    injection Hslot as <-.
    change (nth_error (term_edges (TSwitch 0 cases d da)) (ssa_switch_slot z cases) =
      Some (dst, args)) in Hedge.
    rewrite ssa_switch_slot_target in Hedge; injection Hedge as Hchoice.
    eapply ASwitch with (a := ssa_refined_raw r l pc) (z := z);
      [exact Hat|exact Hcond|exact Hchoice|exact Hread|exact Hbind].
Qed.

Local Lemma ssa_refined_head_back ext P f r tr u :
  ssa_refined_stable r -> step (ssa_refined_activation ext P f) r tr u ->
  exists a a' n t, ssa_refined_rel P f a r /\ step (activation ext P f) a tr a' /\
    ssa_administrative_steps (ssa_refined_activation ext P f) u n t /\
    ssa_refined_stable t /\ ssa_refined_rel P f a' t.
Proof.
  intros Hstable Hstep.
  destruct Hstep as
    [r l fd b cs env Hpoint Hf Hb Hread Hbind
    |r l pc i tr env Hpoint Hat Hstep
    |r l pc t dst args slot cs env Hpoint Hat Hkind Hslot Hedge Hread Hbind
    |r l pc c args k ps result cs v env Hpoint Hat Hsig Hread Htype Hvalid Hbind
    |r l fd b c args k v env Hpoint Hf Hb Hterm Hvalue Hbind
    |r l pc x v Hpoint Hat Hvalue].
  all: try (unfold ssa_refined_stable in Hstable; rewrite Hpoint in Hstable; contradiction).
  - exists (ssa_refined_raw r l pc), (AState l (S pc) env), 0,
      (SsaRefinedState (SsaExecPoint l (S pc)) env (srs_call_results r) (srs_pending r)).
    split; [eapply ssa_instr_source_rel; eassumption|]; split; [exact Hstep|].
    split; [constructor|]; split; [exact I|].
    destruct Hat as [fd [b [Hf [Hb Hnth]]]].
    eapply ssa_exec_source_rel with (fd := fd) (b := b); try reflexivity; try eassumption.
    change (nth_error (bbody b) pc = Some i) in Hnth.
    assert (Hbound : pc < length (bbody b)) by
      (apply nth_error_Some; rewrite Hnth; discriminate).
    lia.
  - destruct (ssa_transfer_bind ext P f r l pc dst cs env Hbind) as [Hnext Hrel].
    exists (ssa_refined_raw r l pc), (AState dst 0 env), 1,
      (SsaRefinedState (SsaExecPoint dst 0) env (srs_call_results r)
        (ssa_pending_write (srs_pending r) cs)).
    split; [eapply ssa_term_source_rel; eassumption|].
    split; [eapply ssa_transfer_source_step; eassumption|]; split.
    + eapply SsaAdminStep; [cbn [ssa_refined_stable srs_point]; tauto|exact Hnext|constructor].
    + split; [exact I|exact Hrel].
  - destruct (ssa_call_completion ext P f r l pc c args k v env Hat Hbind)
      as [t [Htail [Hend Hrel]]].
    exists (ssa_refined_raw r l pc), (AState k 0 env), 2, t.
    split; [eapply ssa_term_source_rel; eassumption|]; split.
    + eapply ACall with (a := ssa_refined_raw r l pc); eassumption.
    + split; [exact Htail|]; split; assumption.
  - exists (ssa_refined_raw r l pc), (AState l (S pc) (srs_env r)), 0,
      (ssa_refined_set_point r (SsaAfterReturn l)).
    split; [eapply ssa_term_source_rel; eassumption|]; split.
    + eapply AReturn with (a := ssa_refined_raw r l pc); eassumption.
    + split; [constructor|]; split; [exact I|]; split; [|intro y; reflexivity].
      destruct Hat as [fd [b [Hf [Hb [Hpc Hterm]]]]]; exists fd, b.
      split; [exact Hf|]; split; [exact Hb|]; right; exists x.
      split; [exact Hterm|]; split; [|reflexivity].
      change (pc = length (bbody b)) in Hpc; cbn; lia.
Qed.

Local Lemma ssa_refined_back_head ext P f a r tr u :
  ssa_refined_rel P f a r -> step (ssa_refined_activation ext P f) r tr u ->
  exists a' n t, step (activation ext P f) a tr a' /\
    ssa_administrative_steps (ssa_refined_activation ext P f) u n t /\
    ssa_refined_stable t /\ ssa_refined_rel P f a' t.
Proof.
  intros Hrel Hstep.
  destruct (ssa_refined_head_back ext P f r tr u (ssa_refined_rel_stable P f a r Hrel) Hstep)
    as [a0 [a0' [n [t [Hrel0 [Hraw [Htail [Hstable Hrel']]]]]]]].
  destruct (ssa_refined_rel_agrees P f a0 a r Hrel0 Hrel) as [Hlabel [Hpc Henv]].
  destruct (ssa_activation_step_agrees ext P f a0 tr a0' (aenv a) Hraw Henv)
    as [a' [Hraw' Hagrees]].
  assert (Hsource : AState (alabel a0) (apc a0) (aenv a) = a).
  { rewrite Hlabel, Hpc; destruct a; reflexivity. }
  rewrite Hsource in Hraw'; exists a', n, t; split; [exact Hraw'|].
  split; [exact Htail|]; split; [exact Hstable|].
  eapply ssa_refined_rel_transport; eassumption.
Qed.

Local Lemma ssa_refined_backward ext P f a r tr r' :
  ssa_refined_rel P f a r -> ssa_refined_macro (ssa_refined_activation ext P f) r tr r' ->
  exists a', step (activation ext P f) a tr a' /\ ssa_refined_rel P f a' r'.
Proof.
  intros Hrel Hmacro.
  destruct (ssa_macro_head ext P f r tr r' Hmacro) as [u [n [Hhead [Htail Hstable]]]].
  destruct (ssa_refined_back_head ext P f a r tr u Hrel Hhead)
    as [a' [n' [t [Hraw [Hcompletion [Hstable' Hrel']]]]]].
  assert (Heq : r' = t).
  { exact (ssa_administrative_completion_unique ext P f u n r' n' t Htail
      Hcompletion Hstable Hstable'). }
  exists a'; split; [exact Hraw|rewrite Heq; exact Hrel'].
Qed.

(** Raw steps and complete refined macros match the same concrete results and events. *)
Theorem ssa_refined_step_correspondence (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  forall a r, reachable_state (activation ext P f) a ->
    reachable_state (ssa_refined_activation ext P f) r -> ssa_refined_rel P f a r ->
    (forall tr a', step (activation ext P f) a tr a' ->
      exists r', ssa_refined_macro (ssa_refined_activation ext P f) r tr r' /\
        ssa_refined_rel P f a' r') /\
    (forall tr r', ssa_refined_macro (ssa_refined_activation ext P f) r tr r' ->
      exists a', step (activation ext P f) a tr a' /\ ssa_refined_rel P f a' r').
Proof.
  intros Hwf Hfunction a r Ha Hr Hrel; split; intros tr target Hstep.
  - eapply ssa_refined_forward; eassumption.
  - eapply ssa_refined_backward; eassumption.
Qed.

Local Lemma ssa_refined_declared_ends ext P f a r k :
  ssa_refined_rel P f a r -> k <> EndStuck ->
  (ends_as (activation ext P f) (activation_endings ext P f) k a <->
   ends_as (ssa_refined_activation ext P f) (ssa_refined_endings ext P f) k r).
Proof.
  intros [Hcontrol Henv] Hkind.
  assert (Htraps : activation_trapped ext P f a <->
    activation_trapped ext P f (ssa_refined_raw r (alabel a) (apc a))).
  { unfold activation_trapped; apply ssa_frame_trapped_agrees; try reflexivity; exact Henv. }
  destruct Hcontrol as [fd [b [Hf [Hb [[Hbound Hpoint]|[x [Hterm [Hpc Hpoint]]]]]]]].
  - destruct k.
    + split.
      * intro Hend; exfalso.
        apply (proj1 (ssa_frame_final_at P (activation_frame f a) fd b Hf Hb)) in Hend.
        change (length (bbody b) < apc a) in Hend; lia.
      * intros [l Hafter]; rewrite Hpoint in Hafter; discriminate.
    + split.
      * intro Htrap; exists (alabel a), (apc a); split; [exact Hpoint|].
        apply Htraps; exact Htrap.
      * intros [l [pc [Hpoint' Htrap]]].
        assert (Hl : l = alabel a) by congruence.
        assert (Hp : pc = apc a) by congruence; subst l pc.
        apply Htraps; exact Htrap.
    + reflexivity.
    + contradiction.
  - destruct k.
    + split.
      * intro Hend; exists (alabel a); exact Hpoint.
      * intro Hend.
        apply (proj2 (ssa_frame_final_at P (activation_frame f a) fd b Hf Hb)).
        change (length (bbody b) < apc a); lia.
    + split.
      * intro Htrap; exfalso.
        pose proof (ssa_frame_trapped_before ext P (activation_frame f a) fd b
          Htrap Hf Hb) as Hbefore.
        change (apc a < length (bbody b)) in Hbefore; lia.
      * intros [l [pc [Hexec Htrap]]]; rewrite Hpoint in Hexec; discriminate.
    + reflexivity.
    + contradiction.
Qed.

Local Lemma ssa_refined_no_intermediate_end ext P f r k :
  ~ ssa_refined_stable r -> k <> EndStuck ->
  ~ ends_as (ssa_refined_activation ext P f) (ssa_refined_endings ext P f) k r.
Proof.
  intros Hunstable Hkind Hend; destruct k.
  - destruct Hend as [l Hpoint]; apply Hunstable.
    unfold ssa_refined_stable; rewrite Hpoint; exact I.
  - destruct Hend as [l [pc [Hpoint Htrap]]]; apply Hunstable.
    unfold ssa_refined_stable; rewrite Hpoint; exact I.
  - exact Hend.
  - contradiction.
Qed.

Local Lemma ssa_refined_completion_laws ext P f :
  SsaCompletion.laws (activation ext P f) (activation_endings ext P f)
    (ssa_refined_activation ext P f) (ssa_refined_endings ext P f)
    ssa_refined_stable ssa_administrative_rank (ssa_refined_rel P f).
Proof.
  constructor.
  - exact (ssa_refined_rel_stable P f).
  - exact (ssa_refined_declared_ends ext P f).
  - intros r tr r' Hunstable Hstep; exact (ssa_administrative_step ext P f r tr r' Hstep Hunstable).
  - intros r u v Hunstable Hstep Hstep'; eapply ssa_administrative_deterministic; eassumption.
  - exact (ssa_refined_no_intermediate_end ext P f).
  - intros a r tr a' Hrel Hstep.
    destruct (ssa_refined_forward ext P f a r tr a' Hrel Hstep) as [r' [Hmacro Hrel']].
    destruct (ssa_macro_head ext P f r tr r' Hmacro) as [u [n [Hhead [Htail Hstable]]]].
    exists u, n, r'; split; [exact Hhead|]; split; [exact Htail|]; split; assumption.
  - exact (ssa_refined_back_head ext P f).
Qed.

(** Stable raw and refined states preserve every ending, finite event prefix and divergence. *)
Theorem ssa_refined_behaviour (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  forall a r, reachable_state (activation ext P f) a ->
    reachable_state (ssa_refined_activation ext P f) r -> ssa_refined_rel P f a r ->
  same_behaviour (activation ext P f) (activation_endings ext P f) a
    (ssa_refined_activation ext P f) (ssa_refined_endings ext P f) r.
Proof.
  intros Hwf Hfunction a r Ha Hr Hrel; eapply SsaCompletion.behaviour.
  - exact (ssa_refined_completion_laws ext P f).
  - exact Hrel.
Qed.

(** Every reachable stable refined state has a reachable source counterpart. *)
Lemma ssa_refined_reachable_relation ext P f r :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_state (ssa_refined_activation ext P f) r -> ssa_refined_stable r ->
  exists a, reachable_state (activation ext P f) a /\ ssa_refined_rel P f a r.
Proof.
  intros Hwf Hfunction [r0 [tr [Hinitial Hrun]]] Hstable.
  destruct Hinitial as [fd [b [cs [Hf [Hb [Htypes [Hvalid ->]]]]]]].
  assert (Hlength : length (bparams b) = length cs).
  { pose proof (f_equal (@length ty) Htypes) as Hlen; rewrite !length_map in Hlen; lia. }
  destruct (ssa_bind_exists (fun _ => None) (bparams b) cs Hlength) as [env Hbind].
  pose (a0 := AState (fentry fd) 0 env).
  pose (u0 := SsaRefinedState (SsaExecPoint (fentry fd) 0) env (fun _ => None)
    (ssa_pending_write (fun _ => None) cs)).
  assert (Hclosure : SsaCompletion.closure (ssa_refined_activation ext P f) ssa_refined_stable
    (ssa_refined_rel P f) a0 (SsaRefinedState (SsaBeforeParams (fentry fd))
      (fun _ => None) (fun _ => None) (ssa_pending_write (fun _ => None) cs))).
  { exists 1, u0; split.
    - eapply SsaAdminStep with (u := u0); [cbn [ssa_refined_stable srs_point]; tauto| |constructor].
      eapply SsaStepBind; try reflexivity; try eassumption.
      cbn [srs_pending]; rewrite Hlength; apply ssa_pending_write_read.
    - split; [exact I|].
      exact (proj2 (ssa_initial_bind_run ext P f fd b cs env Hf Hb Hbind)). }
  pose proof (SsaCompletion.stutters _ _ _ _ _ _ _ (ssa_refined_completion_laws ext P f))
    as Hstutter.
  pose proof (stuttering_swap _ _ _ _ _ _ _ Hstutter) as Hswap.
  destruct (stuttering_exec _ _ _ _ _ _ _ Hswap _ tr r Hrun a0 Hclosure)
    as [a [Hsource [n [u [Hsteps [Hstable' Hrel]]]]]].
  pose proof (proj2 (ssa_admin_stable _ _ r n u Hstable Hsteps)) as ->.
  exists a; split; [|exact Hrel].
  exists a0, tr; split; [|exact Hsource].
  exists fd, b, cs, env; repeat split; try assumption; reflexivity.
Qed.
