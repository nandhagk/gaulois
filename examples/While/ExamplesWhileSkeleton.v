(** * While control as a structured skeleton

    Each While loop is a block containing a repeating loop, with paired exit labels.
    For example, break zero jumps past the loop to its enclosing block exit.
    Builds on: While semantics, ViewsSkeleton and ViewsSemantics. *)

From Stdlib Require Import List Bool Arith Lia ZArith.
From Gaulois.Views Require Import ViewsSemantics ViewsSkeleton.
From Gaulois.Examples.While Require Import ExamplesWhileSyntax ExamplesWhileSemantics.
Import List.ListNotations.

(** While primitive actions distinguish no-ops, assignments and output. *)
Inductive atom : Type :=
  | ANop
  | AAssign (x : var) (e : expr)
  | AOutput (e : expr).

(** Breaks and continues must name an enclosing While loop. *)
Fixpoint loops_ok (d : nat) (s : stmt) : bool :=
  match s with
  | SSeq s1 s2 | SIf _ s1 s2 => loops_ok d s1 && loops_ok d s2
  | SLoop body => loops_ok (S d) body
  | SBreak n | SContinue n => Nat.ltb n d
  | _ => true
  end.

(** Paired block and loop labels implement the two forms of While jump. *)
Fixpoint to_skeleton (s : stmt) : Skeleton.stmt atom expr :=
  match s with
  | SSkip => Skeleton.Atom ANop
  | SAssign x e => Skeleton.Atom (AAssign x e)
  | SOutput e => Skeleton.Atom (AOutput e)
  | SSeq s1 s2 => Skeleton.Seq (to_skeleton s1) (to_skeleton s2)
  | SIf g s1 s2 => Skeleton.If g (to_skeleton s1) (to_skeleton s2)
  | SLoop body => Skeleton.Block (Skeleton.Loop (to_skeleton body))
  | SBreak n => Skeleton.Jump (2 * n + 1)%nat
  | SContinue n => Skeleton.Jump (2 * n)%nat
  end.

(** The client preserves the independent arithmetic, observations and jump store. *)
Definition while_client (init : store -> Prop) : skeleton_client atom expr store Z :=
  {| init_store := init;
     atom_step := fun a st l st' =>
       match a with
       | ANop => l = [] /\ st' = st
       | AAssign x e => l = [] /\ st' = update st x (eval_expr st e)
       | AOutput e => l = [eval_expr st e] /\ st' = st
       end;
     atom_trap := fun _ _ => False;
     atom_stop := fun _ _ => False;
     guard_bool := fun e st => Some (negb (Z.eqb (eval_expr st e) 0));
     guard_index := fun _ _ => None;
     jump_effect := fun _ _ st st' => st' = st |}.

(** A source occurrence carries the corresponding continuation in both machines. *)
Inductive while_context (prog : stmt) : stmt -> position -> list wframe -> list frame -> Prop :=
  | wc_root : while_context prog prog [] [] []
  | wc_seq_first : forall s1 s2 p k fs,
      while_context prog (SSeq s1 s2) p k fs ->
      while_context prog s1 (p ++ [DFirst]) (KSeq s2 :: k) (FSeq p :: fs)
  | wc_seq_second : forall s1 s2 p k fs,
      while_context prog (SSeq s1 s2) p k fs ->
      while_context prog s2 (p ++ [DSecond]) (KJoin :: k) (FJoin p :: fs)
  | wc_if_first : forall g s1 s2 p k fs,
      while_context prog (SIf g s1 s2) p k fs ->
      while_context prog s1 (p ++ [DFirst]) (KJoin :: k) (FJoin p :: fs)
  | wc_if_second : forall g s1 s2 p k fs,
      while_context prog (SIf g s1 s2) p k fs ->
      while_context prog s2 (p ++ [DSecond]) (KJoin :: k) (FJoin p :: fs)
  | wc_loop_body : forall body p k fs,
      while_context prog (SLoop body) p k fs ->
      while_context prog body ((p ++ [DBody]) ++ [DBody])
        (KLoop body :: KExit :: k) (FLoop (p ++ [DBody]) :: FBlock p :: fs).

(** Context lookup agrees with the translated subtree. *)
Lemma while_context_sub prog s p k fs :
  while_context prog s p k fs -> sub (to_skeleton prog) p = Some (to_skeleton s).
Proof.
  intro Hctx; induction Hctx; [reflexivity| | | | |].
  all: rewrite !sub_app, IHHctx; cbn [sub child to_skeleton]; reflexivity.
Qed.

(** An even label depth restarts the same source loop body in both machines. *)
Lemma while_continue_match prog s p k fs :
  while_context prog s p k fs -> forall n (st : store),
  (jump_cont (2 * n)%nat k = None /\ resume (2 * n)%nat fs st = None) \/
  exists body k' q fs', jump_cont (2 * n)%nat k = Some (JRun body k') /\
    resume (2 * n)%nat fs st = Some (Go q fs' st) /\
    while_context prog body q k' fs'.
Proof.
  intro Hctx; induction Hctx; intros n st; try exact (IHHctx n st).
  - left; split; reflexivity.
  - destruct n as [|n].
    + right; eexists; eexists; eexists; eexists; split; [reflexivity|].
      split; [reflexivity|apply wc_loop_body; exact Hctx].
    + replace (2 * S n)%nat with (S (S (2 * n))) by lia.
      exact (IHHctx n st).
Qed.

(** An odd label depth leaves the same source loop in both machines. *)
Lemma while_break_match prog s p k fs :
  while_context prog s p k fs -> forall n (st : store),
  (jump_cont (2 * n + 1)%nat k = None /\ resume (2 * n + 1)%nat fs st = None) \/
  exists body k' q fs', jump_cont (2 * n + 1)%nat k = Some (JFin k') /\
    resume (2 * n + 1)%nat fs st = Some (Ret q fs' st) /\
    while_context prog (SLoop body) q k' fs'.
Proof.
  intro Hctx; induction Hctx; intros n st; try exact (IHHctx n st).
  - left; split; reflexivity.
  - destruct n as [|n].
    + right; eexists; eexists; eexists; eexists; split; [reflexivity|].
      split; [reflexivity|exact Hctx].
    + replace (2 * S n + 1)%nat with (S (S (2 * n + 1))) by lia.
      exact (IHHctx n st).
Qed.

(** Both machines share stores and the same syntactic continuation at each phase. *)
Inductive match_state (prog : stmt) : config -> mstate store -> Prop :=
  | match_run : forall s p k fs st, while_context prog s p k fs ->
      match_state prog (Run s k st) (Go p fs st)
  | match_enter : forall body p k fs st, while_context prog (SLoop body) p k fs ->
      match_state prog (Enter body (KExit :: k) st) (Go (p ++ [DBody]) (FBlock p :: fs) st)
  | match_fin : forall s p k fs st, while_context prog s p k fs ->
      match_state prog (WhileFin k st) (Ret p fs st).

(** Every initial While configuration has the corresponding skeleton root. *)
Theorem match_state_initial (prog : stmt) (init : store -> Prop) (c : config) :
  initial (while_semantics prog init) c ->
  exists m, initial (skeleton_semantics (to_skeleton prog) (while_client init)) m /\
    match_state prog c m.
Proof.
  intros [st [Hinit ->]].
  exists (Go [] [] st); split.
  - exists st; split; [reflexivity|exact Hinit].
  - apply match_run, wc_root.
Qed.

(** A running source statement matches the corresponding skeleton entry transition. *)
Lemma while_run_forth prog init s p k fs st l c' :
  while_context prog s p k fs -> step_w (Run s k st) l c' ->
  exists m', skel_step (to_skeleton prog) (while_client init) (Go p fs st) l m' /\
    match_state prog c' m'.
Proof.
  intros Hctx Hstep.
  pose proof (while_context_sub _ _ _ _ _ Hctx) as Hsub.
  destruct s as [|x e|s1 s2|g s1 s2|body|n|n|e]; inversion Hstep; subst.
  + eexists; split; [eapply step_atom; [exact Hsub|split; reflexivity]|].
    eapply match_fin; exact Hctx.
  + eexists; split; [eapply step_atom; [exact Hsub|split; reflexivity]|].
    eapply match_fin; exact Hctx.
  + eexists; split; [eapply step_seq; exact Hsub|].
    apply match_run, wc_seq_first; exact Hctx.
  + destruct (Z.eqb (eval_expr st g) 0) eqn:Hguard.
    * eexists; split.
      -- eapply step_if with (b := false); [exact Hsub|cbn; rewrite Hguard; reflexivity].
      -- apply match_run; eapply wc_if_second; exact Hctx.
    * eexists; split.
      -- eapply step_if with (b := true); [exact Hsub|cbn; rewrite Hguard; reflexivity].
      -- apply match_run; eapply wc_if_first; exact Hctx.
  + eexists; split; [eapply step_block; exact Hsub|apply match_enter; exact Hctx].
  + match goal with H : jump_cont _ _ = Some _ |- _ => rename H into Hsource end.
    destruct (while_break_match _ _ _ _ _ Hctx n st) as
      [[Hnone _]|[body [ktgt [q [fs' [Hjump [Hresume Htarget]]]]]]];
      [congruence|].
    rewrite Hjump in Hsource; inversion Hsource; subst.
    eexists; split; [eapply step_jump; [exact Hsub|reflexivity|exact Hresume]|].
    eapply match_fin; exact Htarget.
  + match goal with H : jump_cont _ _ = Some _ |- _ => rename H into Hsource end.
    destruct (while_continue_match _ _ _ _ _ Hctx n st) as
      [[Hnone _]|[body [ktgt [q [fs' [Hjump [Hresume Htarget]]]]]]];
      [congruence|].
    rewrite Hjump in Hsource; inversion Hsource; subst.
    eexists; split; [eapply step_jump; [exact Hsub|reflexivity|exact Hresume]|].
    apply match_run; exact Htarget.
  + eexists; split; [eapply step_atom; [exact Hsub|split; reflexivity]|].
    eapply match_fin; exact Hctx.
Qed.

(** Source transitions preserve the occurrence and continuation matching. *)
Lemma while_match_forth prog init c m l c' :
  match_state prog c m -> step_w c l c' ->
  exists m', skel_step (to_skeleton prog) (while_client init) m l m' /\
    match_state prog c' m'.
Proof.
  intros Hmatch Hstep; destruct Hmatch as
    [s p k fs st Hctx|body p k fs st Hctx|s p k fs st Hctx].
  - eapply while_run_forth; eassumption.
  - inversion Hstep; subst.
    eexists; split.
    + eapply step_loop; rewrite sub_app, (while_context_sub _ _ _ _ _ Hctx); reflexivity.
    + apply match_run, wc_loop_body; exact Hctx.
  - inversion Hstep; subst; inversion Hctx; subst.
    + eexists; split; [apply step_ret_seq|apply match_run; eapply wc_seq_second; eassumption].
    + eexists; split; [apply step_ret_join|eapply match_fin; eassumption].
    + eexists; split; [apply step_ret_join|eapply match_fin; eassumption].
    + eexists; split; [apply step_ret_join|eapply match_fin; eassumption].
    + eexists; split; [apply step_ret_loop|apply match_run; exact Hctx].
Qed.

(** A running skeleton entry matches the corresponding source statement transition. *)
Lemma while_run_back prog init s p k fs st l m' :
  while_context prog s p k fs ->
  skel_step (to_skeleton prog) (while_client init) (Go p fs st) l m' ->
  exists c', step_w (Run s k st) l c' /\ match_state prog c' m'.
Proof.
  intros Hctx Hstep.
  pose proof (while_context_sub _ _ _ _ _ Hctx) as Hsub.
  destruct s as [|x e|s1 s2|g s1 s2|body|n|n|e]; cbn [to_skeleton] in Hsub;
    inversion Hstep; subst; try congruence.
  + assert (a = ANop) by congruence; subst a.
    match goal with H : atom_step _ _ _ _ _ |- _ =>
      cbn [while_client] in H; destruct H as [-> ->]
    end.
    eexists; split; [apply w_skip|eapply match_fin; exact Hctx].
  + assert (a = AAssign x e) by congruence; subst a.
    match goal with H : atom_step _ _ _ _ _ |- _ =>
      cbn [while_client] in H; destruct H as [-> ->]
    end.
    eexists; split; [apply w_assign|eapply match_fin; exact Hctx].
  + eexists; split; [apply w_seq|apply match_run, wc_seq_first; exact Hctx].
  + assert (g0 = g) by congruence; subst g0.
    match goal with H : guard_bool _ _ _ = _ |- _ =>
      cbn [while_client] in H; injection H as <-
    end.
    destruct (Z.eqb (eval_expr st g) 0) eqn:Hguard; cbn.
    * eexists; split.
      -- pose proof (w_if g s1 s2 k st) as Hsource; rewrite Hguard in Hsource; exact Hsource.
      -- apply match_run; eapply wc_if_second; exact Hctx.
    * eexists; split.
      -- pose proof (w_if g s1 s2 k st) as Hsource; rewrite Hguard in Hsource; exact Hsource.
      -- apply match_run; eapply wc_if_first; exact Hctx.
  + eexists; split; [apply w_loop|apply match_enter; exact Hctx].
  + assert (n0 = (2 * n + 1)%nat) by congruence; subst n0.
    match goal with H : jump_effect _ _ _ _ _ |- _ =>
      change (st' = st) in H; subst st'
    end.
    match goal with H : resume _ _ _ = Some _ |- _ => rename H into Hmachine end.
    destruct (while_break_match _ _ _ _ _ Hctx n st) as
      [[_ Hnone]|[body [ktgt [q [fs' [Hjump [Hresume Htarget]]]]]]]; [congruence|].
    rewrite Hresume in Hmachine; injection Hmachine as <-.
    eexists; split; [apply w_break; exact Hjump|eapply match_fin; exact Htarget].
  + assert (n0 = (2 * n)%nat) by congruence; subst n0.
    match goal with H : jump_effect _ _ _ _ _ |- _ =>
      change (st' = st) in H; subst st'
    end.
    match goal with H : resume _ _ _ = Some _ |- _ => rename H into Hmachine end.
    destruct (while_continue_match _ _ _ _ _ Hctx n st) as
      [[_ Hnone]|[body [ktgt [q [fs' [Hjump [Hresume Htarget]]]]]]]; [congruence|].
    rewrite Hresume in Hmachine; injection Hmachine as <-.
    eexists; split; [apply w_continue; exact Hjump|apply match_run; exact Htarget].
  + assert (a = AOutput e) by congruence; subst a.
    match goal with H : atom_step _ _ _ _ _ |- _ =>
      cbn [while_client] in H; destruct H as [-> ->]
    end.
    eexists; split; [apply w_output|eapply match_fin; exact Hctx].
Qed.

(** Skeleton transitions preserve the same source occurrence and continuation. *)
Lemma while_match_back prog init c m l m' :
  match_state prog c m -> skel_step (to_skeleton prog) (while_client init) m l m' ->
  exists c', step_w c l c' /\ match_state prog c' m'.
Proof.
  intros Hmatch Hstep; destruct Hmatch as
    [s p k fs st Hctx|body p k fs st Hctx|s p k fs st Hctx].
  - eapply while_run_back; eassumption.
  - pose proof (while_context_sub _ _ _ _ _ Hctx) as Hsub.
    assert (Hloop : sub (to_skeleton prog) (p ++ [DBody]) =
      Some (Skeleton.Loop (to_skeleton body))) by (rewrite sub_app, Hsub; reflexivity).
    inversion Hstep; subst; try congruence.
    eexists; split; [apply w_enter|apply match_run, wc_loop_body; exact Hctx].
  - inversion Hctx; subst; inversion Hstep; subst.
    + eexists; split; [apply w_fin_seq|apply match_run; eapply wc_seq_second; eassumption].
    + eexists; split; [apply w_fin_join|eapply match_fin; eassumption].
    + eexists; split; [apply w_fin_join|eapply match_fin; eassumption].
    + eexists; split; [apply w_fin_join|eapply match_fin; eassumption].
    + eexists; split; [apply w_fin_loop|apply match_run; exact Hctx].
Qed.

(** A context with no source continuation is the root occurrence. *)
Lemma while_context_root prog s p k fs :
  while_context prog s p k fs -> (k = [] <-> p = [] /\ fs = []).
Proof.
  intro Hctx; destruct Hctx; cbn; split; intro Hempty; try discriminate.
  all: try (split; reflexivity); try reflexivity.
  all: destruct Hempty as [_ Hempty]; discriminate.
Qed.

(** Matched states agree on normal completion. *)
Lemma while_match_final prog init c m :
  match_state prog c m ->
  (final while_endings c <-> final (skeleton_endings (to_skeleton prog) (while_client init)) m).
Proof.
  intro Hmatch; destruct Hmatch as
    [s p k fs st Hctx|body p k fs st Hctx|s p k fs st Hctx]; cbn.
  - split; [intros [st' Hbad]; discriminate|contradiction].
  - split; [intros [st' Hbad]; discriminate|contradiction].
  - pose proof (while_context_root _ _ _ _ _ Hctx) as Hroot.
    split.
    + intros [st' Heq]; inversion Heq; subst.
      destruct (proj1 Hroot eq_refl) as [-> ->]; exact I.
    + destruct p as [|d p], fs as [|f fs]; try contradiction.
      intro Hend; destruct (proj2 Hroot (conj eq_refl eq_refl)).
      exists st; reflexivity.
Qed.

(** A matched skeleton state cannot trap or stop. *)
Lemma while_match_no_failure prog init c m :
  match_state prog c m ->
  ~ trapped (skeleton_endings (to_skeleton prog) (while_client init)) m /\
  ~ stopped (skeleton_endings (to_skeleton prog) (while_client init)) m.
Proof.
  intro Hmatch; destruct Hmatch as
    [s p k fs st Hctx|body p k fs st Hctx|s p k fs st Hctx]; cbn.
  - rewrite (while_context_sub _ _ _ _ _ Hctx); destruct s; cbn [to_skeleton while_client];
      split; intros Hbad; discriminate || contradiction.
  - rewrite sub_app, (while_context_sub _ _ _ _ _ Hctx); cbn; tauto.
  - tauto.
Qed.

(** Both matching directions preserve running, including malformed-jump failures. *)
Lemma while_match_running prog init c m :
  match_state prog c m ->
  (running (while_semantics prog init) c <->
   running (skeleton_semantics (to_skeleton prog) (while_client init)) m).
Proof.
  intro Hmatch; split; intros [l [next Hstep]].
  - destruct (while_match_forth _ init _ _ _ _ Hmatch Hstep) as [next' [Hnext _]].
    exists l, next'; exact Hnext.
  - destruct (while_match_back _ init _ _ _ _ Hmatch Hstep) as [next' [Hnext _]].
    exists l, next'; exact Hnext.
Qed.

(** Every ending and individual step is preserved by the continuation translation. *)
Theorem while_skeleton_bisimulation (prog : stmt) (init : store -> Prop) :
  bisimulation (while_semantics prog init) while_endings
    (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) (match_state prog).
Proof.
  constructor.
  - intros c m tag Hmatch.
    pose proof (while_match_final _ init _ _ Hmatch) as Hfinal.
    destruct (while_match_no_failure _ init _ _ Hmatch) as [Htrap Hstop].
    pose proof (while_match_running _ init _ _ Hmatch) as Hrun.
    destruct tag; cbn [ends_as]; try exact Hfinal; cbn [while_endings trapped stopped].
    + tauto.
    + tauto.
    + unfold stuck; cbn [while_endings trapped stopped]; tauto.
  - intros c m l c' Hmatch Hstep; exact (while_match_forth prog init c m l c' Hmatch Hstep).
  - intros c m l m' Hmatch Hstep; exact (while_match_back prog init c m l m' Hmatch Hstep).
Qed.

(** Skeleton behaviour equality transports back along both matched endpoints. *)
Theorem while_behaviour_transport (prog : stmt) (init : store -> Prop) (c0 c1 : config)
    (m0 m1 : mstate store) :
  match_state prog c0 m0 -> match_state prog c1 m1 ->
  same_behaviour (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) m0
    (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) m1 ->
  same_behaviour (while_semantics prog init) while_endings c0
    (while_semantics prog init) while_endings c1.
Proof.
  intros Hmatch0 Hmatch1 Hsame.
  eapply same_behaviour_trans.
  - eapply bisimilar_same_behaviour; [apply while_skeleton_bisimulation|exact Hmatch0].
  - eapply same_behaviour_trans; [exact Hsame|].
    apply same_behaviour_sym.
    eapply bisimilar_same_behaviour; [apply while_skeleton_bisimulation|exact Hmatch1].
Qed.
