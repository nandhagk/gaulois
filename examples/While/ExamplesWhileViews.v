(** * While variable, effect and region adapters

    Explicit adapters connect the While client to the generic analysis interfaces.
    For example, an output reads its operand and is the only observing atom.
    Builds on: While skeleton, structured views, region summaries and dense analyses. *)

From Stdlib Require Import List Bool Arith Lia ZArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderPowerset OrderLift
  OrderPointwise OrderBasic.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSkeleton ViewsStructured
  ViewsRegion ViewsEffects ViewsAgreement.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesAvailable AnalysesDemand
  AnalysesStructured.
From Gaulois.Examples.While Require Import ExamplesWhileSyntax ExamplesWhileSemantics
  ExamplesWhileSkeleton.
Import List.ListNotations.

(** Expression inventories retain operand occurrences in evaluation order. *)
Fixpoint expr_vars (e : expr) : list var :=
  match e with
  | EConst _ => []
  | EVar x => [x]
  | EUn _ e => expr_vars e
  | EBin _ e1 e2 => expr_vars e1 ++ expr_vars e2
  end.

(** Operand agreement determines the independently evaluated expression. *)
Lemma eval_expr_agrees e st1 st2 :
  (forall x, In x (expr_vars e) -> st1 x = st2 x) -> eval_expr st1 e = eval_expr st2 e.
Proof.
  induction e as [w|x|o e IH|o e1 IH1 e2 IH2]; cbn [expr_vars eval_expr]; intro Hagree.
  - reflexivity.
  - apply Hagree; now left.
  - rewrite IH by exact Hagree; reflexivity.
  - rewrite IH1, IH2; [reflexivity| |]; intros x Hin; apply Hagree; apply in_or_app; auto.
Qed.

(** The primitive variable inventory is independent of the enclosing program. *)
Definition while_skel_vars : skel_vars atom expr var :=
  {| atom_uses := fun a => match a with
       | ANop => []
       | AAssign _ e | AOutput e => expr_vars e
       end;
     atom_defs := fun a => match a with
       | AAssign x _ => [x]
       | _ => []
       end;
     atom_trap_uses := fun _ => [];
     guard_uses := expr_vars |}.

(** Input variables include conditions and output operands, but exclude assignment destinations. *)
Definition while_action_uses (a : action atom expr) : list var :=
  match a with
  | AAtom a => atom_uses while_skel_vars a
  | AGuard e _ | AIndexIs e _ | AIndexAtLeast e _ => expr_vars e
  | AJump _ _ => []
  end.

(** Only assignment actions define variables. *)
Definition while_action_defs (a : action atom expr) : list var :=
  match a with
  | AAtom a => atom_defs while_skel_vars a
  | _ => []
  end.

(** Dense variable analysis reads the prepared skeleton actions. *)
Definition while_var_view (prog : stmt) (init : store -> Prop) :
    var_view (mstate store) Z skel_point (skel_edge atom expr) var Z :=
  let acts := skel_acts (to_skeleton prog) in
  {| gview := skeleton_view (to_skeleton prog) (while_client init);
     uses := fun e => flat_map while_action_uses (acts e);
     defs := fun e => flat_map while_action_defs (acts e);
     exit_uses := fun _ => [];
     vget := fun m x => store_of m x |}.

(** Each node combines its already computed child summaries exactly once.
    Concatenation, zero scans and lowering are charged to the materialised inventories,
    which may be larger than the syntax; no source subtree is traversed here. *)
Definition while_region_alg (prog : stmt) : summary_algebra atom expr (bool * list nat) :=
  {| on_atom := fun _ => (true, []);
     on_seq := fun r1 r2 => (fst r1 && fst r2, snd r1 ++ snd r2);
     on_if := fun _ r1 r2 => (fst r1 || fst r2, snd r1 ++ snd r2);
     on_block := fun r => (fst r || existsb (Nat.eqb 0) (snd r), lower (snd r));
     on_loop := fun r => (false, lower (snd r));
     on_jump := fun n => (false, [n]);
     on_jump_if := fun _ n => (true, [n]);
     on_jump_table := fun _ ns n => (false, n :: ns) |}.

(** The fold preserves completion and the ordered escape inventory on every skeleton. *)
Theorem while_region_alg_agrees (prog : stmt) (s : Skeleton.stmt atom expr) :
  summarise (while_region_alg prog) s = (falls (fun _ => true) s, escapes s).
Proof.
  induction s; cbn [summarise while_region_alg falls escapes];
    rewrite ?IHs, ?IHs1, ?IHs2; reflexivity.
Qed.

(** Only output observes, and every atom is heap-free, total and frame-neutral. *)
Definition while_effects : effects atom :=
  {| reads := fun _ => false;
     writes := fun _ => false;
     may_trap := fun _ => false;
     may_diverge := fun _ => false;
     may_stop := fun _ => false;
     allocates := fun _ => false;
     frees := fun _ => false;
     calls := fun _ => false;
     observes := fun a => match a with AOutput _ => true | _ => false end |}.

(** Whole-state equality supplies heap agreement for this heap-free language. *)
Definition while_effects_view (prog : stmt) : effects_view (mstate store) atom unit :=
  {| instr_at := fun m => match m with
       | Go p _ _ => match sub (to_skeleton prog) p with
         | Some (Skeleton.Atom a) => Some a
         | _ => None
         end
       | Ret _ _ _ => None
       end;
     heap := fun _ => tt;
     heap_agree := eq;
     depth := fun _ => 0%nat |}.

(** The primitive client has an available transition for every atom and jump. *)
Theorem while_client_laws (init : store -> Prop) : skeleton_client_laws (while_client init).
Proof.
  constructor; cbn [while_client].
  - intros p n st; exists st; reflexivity.
  - intros [|x e|e] st; left; eexists; eexists; split; reflexivity.
  - intros a st Hfalse; contradiction.
  - intros a st Hfalse; contradiction.
  - intros a st [Hfalse _]; contradiction.
Qed.

(** The primitive variable inventory frames writes and determines all observations. *)
Theorem while_skel_vars_laws (init : store -> Prop) :
  skel_vars_laws (while_client init) while_skel_vars (fun sigma x => sigma x).
Proof.
  constructor; cbn [while_client while_skel_vars].
  - intros [|y e|e] st l st' x [Hl ->] Houtside; try reflexivity.
    unfold update; destruct (Nat.eqb y x) eqn:Heq; [|reflexivity].
    apply Nat.eqb_eq in Heq; subst; exfalso; apply Houtside; now left.
  - intros [|y e|e] st1 l st1' st2 [-> ->] Hagree.
    + exists st2; split; [split; reflexivity|intros x Hfalse; contradiction].
    + exists (update st2 y (eval_expr st2 e)); split; [split; reflexivity|].
      intros x [<-|Hfalse]; [|contradiction].
      unfold update; rewrite Nat.eqb_refl; apply eval_expr_agrees; exact Hagree.
    + exists st2; cbn; split; [|intros x Hfalse; contradiction].
      split; [rewrite (eval_expr_agrees e st1 st2 Hagree); reflexivity|reflexivity].
  - intros e st1 st2 Hagree; cbn.
    rewrite (eval_expr_agrees e st1 st2 Hagree); split; reflexivity.
  - intros a st1 st2 Hagree; tauto.
  - intros p n st st' x ->; reflexivity.
Qed.

(** The translation introduces two valid relative labels per enclosing While loop. *)
Lemma to_skeleton_labels_at s : forall d,
  loops_ok d s = true -> labels_ok (2 * d)%nat (to_skeleton s) = true.
Proof.
  induction s; intros d Hlabels; cbn [loops_ok to_skeleton labels_ok] in *; try reflexivity.
  - apply andb_true_iff in Hlabels; destruct Hlabels as [Hfirst Hsecond].
    apply andb_true_iff; split; [apply IHs1|apply IHs2]; assumption.
  - apply andb_true_iff in Hlabels; destruct Hlabels as [Hfirst Hsecond].
    apply andb_true_iff; split; [apply IHs1|apply IHs2]; assumption.
  - replace (S (S (2 * d))) with (2 * S d)%nat by lia; apply IHs; exact Hlabels.
  - apply Nat.ltb_lt in Hlabels; apply Nat.ltb_lt; lia.
  - apply Nat.ltb_lt in Hlabels; apply Nat.ltb_lt; lia.
Qed.

(** Well-nested source jumps translate to well-nested skeleton labels. *)
Theorem to_skeleton_labels_ok (s : stmt) :
  loops_ok 0 s = true -> labels_ok 0 (to_skeleton s) = true.
Proof.
  apply (to_skeleton_labels_at s 0).
Qed.

(** While translations use ordinary guards and unconditional jumps only. *)
Fixpoint while_tree (s : Skeleton.stmt atom expr) : Prop :=
  match s with
  | Skeleton.Seq s1 s2 | Skeleton.If _ s1 s2 => while_tree s1 /\ while_tree s2
  | Skeleton.Block s | Skeleton.Loop s => while_tree s
  | Skeleton.JumpIf _ _ | Skeleton.JumpTable _ _ _ => False
  | _ => True
  end.

(** Every source translation has the restricted While control shape. *)
Lemma to_skeleton_tree prog : while_tree (to_skeleton prog).
Proof.
  induction prog; cbn [to_skeleton while_tree]; tauto.
Qed.

(** Every translated subtree retains the same restricted control shape. *)
Lemma while_tree_sub s p t : while_tree s -> sub s p = Some t -> while_tree t.
Proof.
  revert s; induction p as [|d p IH]; intros s Htree Hsub.
  - cbn in Hsub; inversion Hsub; subst; exact Htree.
  - destruct s; destruct d; cbn [sub child] in Hsub; try discriminate.
    all: eapply IH; [|exact Hsub]; cbn [while_tree] in Htree; tauto.
Qed.

(** No raw machine state in a translated While program can trap or stop. *)
Lemma while_no_failure prog init m :
  ~ trapped (skeleton_endings (to_skeleton prog) (while_client init)) m /\
  ~ stopped (skeleton_endings (to_skeleton prog) (while_client init)) m.
Proof.
  destruct m as [p fs st|p fs st]; cbn [skeleton_endings trapped stopped]; [|tauto].
  destruct (sub (to_skeleton prog) p) as [s|] eqn:Hsub; [|tauto].
  pose proof (while_tree_sub _ _ _ (to_skeleton_tree prog) Hsub) as Htree.
  destruct s; cbn [while_tree] in Htree; try contradiction;
    cbn [while_client]; split; intro Hbad; discriminate || contradiction.
Qed.

(** Instructions occur precisely at atom entries in the actual program. *)
Lemma while_instr_entry prog m i : instr_at (while_effects_view prog) m = Some i ->
  exists p fs st, m = Go p fs st /\ sub (to_skeleton prog) p = Some (Skeleton.Atom i).
Proof.
  destruct m as [p fs st|p fs st]; cbn [while_effects_view instr_at]; [|discriminate].
  destruct (sub (to_skeleton prog) p) as [s|] eqn:Hsub; [|discriminate].
  destruct s; try discriminate; intro Heq; injection Heq as <-.
  exists p, fs, st; split; [reflexivity|exact Hsub].
Qed.

(** All nine generic effects laws hold with the required whole-state equality relation. *)
Theorem while_effects_laws (prog : stmt) (init : store -> Prop) :
  effects_laws (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) while_effects
    (while_effects_view prog).
Proof.
  constructor.
  - intros m l m' i Hreach Hinstr Hstep Hquiet.
    destruct (while_instr_entry _ _ _ Hinstr) as [p [fs [st [-> Hsub]]]].
    inversion Hstep; subst; try congruence.
    assert (a = i) by congruence; subst a; destruct i; try discriminate.
    all: match goal with H : atom_step _ _ _ _ _ |- _ => exact (proj1 H) end.
  - intros m i Hreach Hinstr Htrap; exfalso; exact (proj1 (while_no_failure prog init m) Htrap).
  - intros m i Hreach Hinstr Hstop; exfalso; exact (proj2 (while_no_failure prog init m) Hstop).
  - intros; reflexivity.
  - intros m l m' t i Hreach Hinstr Hstep Hread Heq.
    change (m = t) in Heq; subst t; exists m'; split; [exact Hstep|reflexivity].
  - intros m t i Hm Ht Hinstr Hinstr' Hread Heq; change (m = t) in Heq; subst t; tauto.
  - intros m t i Hm Ht Hinstr Hinstr' Hread Heq; change (m = t) in Heq; subst t; tauto.
  - intros; reflexivity.
  - intros m l m' i Hreach Hinstr Hstep Hcalls; discriminate Hcalls.
Qed.

(** While never traps along a run from any allowed initial store. *)
Theorem while_never_traps (prog : stmt) (init : store -> Prop) (m : mstate store) :
  initial (skeleton_semantics (to_skeleton prog) (while_client init)) m ->
  never_traps (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) m.
Proof.
  intros Hinit tr t Hrun; exact (proj1 (while_no_failure prog init t)).
Qed.

(** One primitive action leaves every undeclared destination unchanged. *)
Lemma while_action_frame init a st l st' x :
  act_hold (while_client init) a st l st' -> ~ In x (while_action_defs a) -> st' x = st x.
Proof.
  destruct a as [a|g b|g i|g n|p n]; cbn [act_hold while_action_defs while_client].
  - destruct a as [|y e|e]; intros [Hl ->] Houtside; try reflexivity.
    unfold update; destruct (Nat.eqb y x) eqn:Heq; [|reflexivity].
    apply Nat.eqb_eq in Heq; subst; exfalso; apply Houtside; now left.
  - intros [_ [_ ->]] Houtside; reflexivity.
  - intros [_ [_ ->]] Houtside; reflexivity.
  - intros [_ [_ ->]] Houtside; reflexivity.
  - intros [-> _] Houtside; reflexivity.
Qed.

(** A list of actions frames every variable outside its complete destination inventory. *)
Lemma while_actions_frame init xs st l st' x :
  acts_hold (while_client init) xs st l st' ->
  ~ In x (flat_map while_action_defs xs) -> st' x = st x.
Proof.
  intros Hacts; induction Hacts as [st|a xs st l1 mid l2 last Hfirst Htail IH];
    intro Houtside; [reflexivity|].
  cbn in Houtside; rewrite in_app_iff in Houtside.
  rewrite IH by tauto; eapply while_action_frame; [exact Hfirst|tauto].
Qed.

(** Input and framed-value agreement gives a matching primitive and arbitrary output agreement. *)
Lemma while_action_match init a st1 l st1' st2 (P : var -> Prop) :
  act_hold (while_client init) a st1 l st1' ->
  (forall x, In x (while_action_uses a) \/
    (P x /\ ~ In x (while_action_defs a)) -> st1 x = st2 x) ->
  exists st2', act_hold (while_client init) a st2 l st2' /\
    forall x, P x -> st1' x = st2' x.
Proof.
  destruct a as [a|e b|e i|e n|p n]; cbn [act_hold while_action_uses while_action_defs].
  - destruct a as [|y e|e]; cbn [while_client while_skel_vars]; intros [-> ->] Hagree.
    + exists st2; split; [split; reflexivity|].
      intros x Hx; apply Hagree; right; tauto.
    + assert (Heval : eval_expr st1 e = eval_expr st2 e).
      { apply eval_expr_agrees; intros x Hx; apply Hagree; now left. }
      exists (update st2 y (eval_expr st2 e)); split; [split; reflexivity|].
      intros x Hx; unfold update; destruct (Nat.eqb y x) eqn:Heq; [exact Heval|].
      apply Hagree; right; split; [exact Hx|].
      cbn; intros [Hy|Hfalse]; [subst x; rewrite Nat.eqb_refl in Heq; discriminate|contradiction].
    + assert (Heval : eval_expr st1 e = eval_expr st2 e).
      { apply eval_expr_agrees; intros x Hx; apply Hagree; now left. }
      exists st2; split; [split; [rewrite Heval; reflexivity|reflexivity]|].
      intros x Hx; apply Hagree; right; tauto.
  - cbn [while_client]; intros [Hguard [-> ->]] Hagree.
    assert (Heval : eval_expr st1 e = eval_expr st2 e).
    { apply eval_expr_agrees; intros x Hx; apply Hagree; now left. }
    exists st2; split.
    + split; [|split; reflexivity].
      change (Some (negb (Z.eqb (eval_expr st2 e) 0)) = Some b).
      rewrite <- Heval; exact Hguard.
    + intros x Hx; apply Hagree; right; tauto.
  - cbn [while_client]; intros [Hbad _]; discriminate.
  - cbn [while_client]; intros [[j [Hbad _]] _]; discriminate.
  - cbn [while_client]; intros [-> ->] Hagree; exists st2; split.
    + split; reflexivity.
    + intros x Hx; apply Hagree; right; tauto.
Qed.

(** Sequence agreement composes without requiring equality on dead or unwritten values. *)
Lemma while_actions_match init xs st1 l st1' st2 (P : var -> Prop) :
  acts_hold (while_client init) xs st1 l st1' ->
  (forall x, In x (flat_map while_action_uses xs) \/
    (P x /\ ~ In x (flat_map while_action_defs xs)) -> st1 x = st2 x) ->
  exists st2', acts_hold (while_client init) xs st2 l st2' /\
    forall x, P x -> st1' x = st2' x.
Proof.
  intro Hacts; revert st2.
  induction Hacts as [st|a xs st l1 mid l2 last Hfirst Htail IH]; intros st2 Hagree.
  - exists st2; split; [constructor|].
    intros x Hx; apply Hagree; right; tauto.
  - destruct (while_action_match init a st l1 mid st2
      (fun x => In x (flat_map while_action_uses xs) \/
        (P x /\ ~ In x (flat_map while_action_defs xs))) Hfirst) as [mid2 [Hfirst2 Hmid]].
    + intros x [Huse|[[Huse|[Hx Htaildef]] Hfirstdef]]; apply Hagree; cbn;
        rewrite !in_app_iff; tauto.
    + destruct (IH mid2 Hmid) as [last2 [Htail2 Hlast]].
      exists last2; split; [econstructor; eassumption|exact Hlast].
Qed.

(** A taken edge carries its exact indexed payload in the reference outgoing list. *)
Lemma while_taken_payload prog init s l s' e :
  taken (gview (while_var_view prog init)) s l s' e ->
  In (skel_to (to_skeleton prog) e, skel_acts (to_skeleton prog) e)
    (skel_out (to_skeleton prog) (machine_point s)) /\
  acts_hold (while_client init) (skel_acts (to_skeleton prog) e)
    (store_of s) l (store_of s').
Proof.
  intros [Hin [Hpoint Hacts]]; split; [|exact Hacts].
  apply skeleton_out_slot in Hin; destruct Hin as [Hfrom Hbound].
  rewrite skel_to_agrees, skel_acts_agrees.
  destruct (nth_error (skel_out (to_skeleton prog) (from e)) (slot e))
    as [[dest xs]|] eqn:Hrow.
  - rewrite <- Hfrom; eapply nth_error_In; exact Hrow.
  - apply nth_error_None in Hrow; rewrite Hfrom in Hrow; lia.
Qed.

(** The dense variable view satisfies all graph, framing and observation laws. *)
Theorem while_var_view_laws (prog : stmt) (init : store -> Prop) :
  var_view_laws (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) (while_var_view prog init).
Proof.
  constructor.
  - apply skeleton_view_laws_hold.
  - intros s l s' Hfalse; exact Hfalse.
  - intros s l s' e x Hreach Hstep [_ [_ Hacts]] Houtside.
    eapply while_actions_frame; [exact Hacts|exact Houtside].
  - intros s l s' t e Hs Ht Hpoint Hstep Htaken Hagree.
    destruct (while_taken_payload _ _ _ _ _ _ Htaken) as [Hrow Hacts].
    destruct (while_actions_match init _ _ _ _ (store_of t)
      (fun x => In x (defs (while_var_view prog init) e)) Hacts) as [st' [Hacts' Hdefs]].
    + intros x [Huse|[Hdef Hnot]]; [apply Hagree; exact Huse|contradiction].
    + destruct (out_realise (to_skeleton prog) (while_client init) t
        (skel_to (to_skeleton prog) e) (skel_acts (to_skeleton prog) e) l st')
        as [t' [Hstep' [Hpoint' Hstore]]].
      * exact (reachable_machine_valid _ (while_client init) t Ht).
      * change (machine_point t = machine_point s) in Hpoint; rewrite Hpoint; exact Hrow.
      * exact Hacts'.
      * exists t'; split; [exact Hstep'|split].
        2: { intros x Hx; change (store_of s' x = store_of t' x).
             rewrite Hstore; apply Hdefs; exact Hx. }
        destruct Htaken as [Hin _]; split.
        -- change (machine_point t = machine_point s) in Hpoint; cbn.
           rewrite Hpoint; exact Hin.
        -- split; [exact Hpoint'|rewrite Hstore; exact Hacts'].
  - intros s t Hs Ht Hpoint Hagree.
    pose proof (machine_point_same_control (to_skeleton prog) s t
      (reachable_machine_valid _ _ _ Hs) (reachable_machine_valid _ _ _ Ht) Hpoint) as Hcontrol.
    destruct (while_no_failure prog init s), (while_no_failure prog init t).
    destruct s as [p fs st|p fs st], t as [q gs st'|q gs st']; cbn in Hcontrol; try contradiction;
      destruct Hcontrol as [-> ->]; repeat split; cbn; tauto.
Qed.

(** A While edge performs at most one atom, Boolean guard or store-preserving jump. *)
Definition while_action_list (xs : list (action atom expr)) : Prop :=
  xs = [] \/ (exists a, xs = [AAtom a]) \/
  (exists g b, xs = [AGuard g b]) \/ (exists p n, xs = [AJump p n]).

(** Every outgoing payload in the While control subset has the primitive action shape. *)
Lemma while_out_actions prog n v xs :
  while_tree prog -> In (v, xs) (skel_out prog n) -> while_action_list xs.
Proof.
  intros Htree Hin; destruct n as [p|p]; cbn [skel_out] in Hin.
  - destruct (sub prog p) as [s|] eqn:Hsub; [|contradiction].
    pose proof (while_tree_sub _ _ _ Htree Hsub) as Hlocal.
    destruct s; cbn [while_tree] in Hlocal; try contradiction; cbn in Hin.
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst; right; left; eauto|contradiction].
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst; left; reflexivity|contradiction].
    + destruct Hin as [Heq|[Heq|Hfalse]]; try contradiction;
        inversion Heq; subst; right; right; left; eauto.
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst; left; reflexivity|contradiction].
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst; left; reflexivity|contradiction].
    + apply jump_out_inv in Hin; destruct Hin as [Hlabel ->]; right; right; right; eauto.
  - destruct (locate prog p) as [[s fs]|] eqn:Hloc; [|contradiction].
    destruct fs as [|f fs]; [contradiction|].
    destruct Hin as [Heq|Hfalse]; [|contradiction].
    inversion Heq; subst; left; reflexivity.
Qed.

(** The indexed selector preserves the primitive shape even for arbitrary edge keys. *)
Lemma while_edge_actions prog e : while_action_list (skel_acts (to_skeleton prog) e).
Proof.
  rewrite skel_acts_agrees.
  destruct (nth_error (skel_out (to_skeleton prog) (from e)) (slot e))
    as [[v xs]|] eqn:Hrow.
  - eapply while_out_actions; [apply to_skeleton_tree|eapply nth_error_In; exact Hrow].
  - left; reflexivity.
Qed.

(** Any edge with a materialised action is listed in the graph, including disconnected code. *)
Lemma while_action_edge_listed prog e a : In a (skel_acts (to_skeleton prog) e) ->
  In e (edges_of (skeleton_graph (to_skeleton prog))).
Proof.
  rewrite skel_acts_agrees.
  destruct (nth_error (skel_out (to_skeleton prog) (from e)) (slot e))
    as [[v xs]|] eqn:Hrow; [|contradiction].
  intro Hin; unfold edges_of; apply in_flat_map; exists (from e); split.
  - eapply outgoing_source_node; exact Hrow.
  - apply skeleton_out_slot; split; [reflexivity|].
    apply nth_error_Some; rewrite Hrow; discriminate.
Qed.

(** The dense universe covers every primitive variable named by an arbitrary edge key. *)
Lemma while_edge_vars_cover prog init e x :
  In x (uses (while_var_view prog init) e ++ defs (while_var_view prog init) e) ->
  In x (var_universe var_encoding (while_var_view prog init)).
Proof.
  intro Hvar; destruct (var_universe_covers var_encoding (while_var_view prog init))
    as [_ [Hcover _]]; apply (Hcover e x); [|exact Hvar].
  cbn [while_var_view uses defs] in Hvar; apply in_app_iff in Hvar.
  destruct Hvar as [Hvar|Hvar]; apply in_flat_map in Hvar;
    destruct Hvar as [a [Ha Hx]]; eapply while_action_edge_listed; exact Ha.
Qed.

(** Output and control operands force a full Boolean demand. *)
Definition while_action_nec (a : action atom expr) : list (var * bool) :=
  match a with
  | AAtom (AOutput e) | AGuard e _ | AIndexIs e _ | AIndexAtLeast e _ =>
    map (fun x => (x, true)) (expr_vars e)
  | _ => []
  end.

(** Only a needed assignment destination propagates demand to its operand. *)
Definition while_action_back (a : action atom expr) (x : var) (b : bool) :
    list (var * bool) :=
  match a with
  | AAtom (AAssign y e) =>
    if b && Nat.eqb y x then map (fun z => (z, true)) (expr_vars e) else []
  | _ => []
  end.

(** The Boolean demand view retains equality only on needed variable values. *)
Definition while_demand_view (prog : stmt) (init : store -> Prop) :
    demand_view (mstate store) Z skel_point (skel_edge atom expr) var Z bool :=
  let acts := skel_acts (to_skeleton prog) in
  {| dgraph := gview (while_var_view prog init);
     ddefs := defs (while_var_view prog init);
     dnec := fun e => flat_map while_action_nec (acts e);
     dback := fun e x b => flat_map (fun a => while_action_back a x b) (acts e);
     dexit := fun _ => [];
     dlookup := fun m x => store_of m x;
     dvars := var_universe var_encoding (while_var_view prog init) |}.

(** False demand propagates no operands, on every edge and variable. *)
Lemma while_back_false prog init e x : dback (while_demand_view prog init) e x false = [].
Proof.
  change (flat_map (fun a => while_action_back a x false) (skel_acts (to_skeleton prog) e) = []).
  induction (skel_acts (to_skeleton prog) e) as [|a xs IH]; [reflexivity|].
  destruct a as [[|y rhs|rhs]|g b|g i|g n|p n]; cbn [while_action_back]; exact IH.
Qed.

(** Every forced or backward operand belongs to the action's declared inputs. *)
Lemma while_action_demand_vars a x b y m :
  In (y, m) (while_action_nec a ++ while_action_back a x b) ->
  In y (while_action_uses a).
Proof.
  destruct a as [[|z e|e]|g c|g i|g n|p n];
    cbn [while_action_nec while_action_back while_action_uses while_skel_vars];
    try (intro Hfalse; contradiction).
  all: try destruct (b && Nat.eqb z x); cbn; try (intro Hfalse; contradiction).
  all: rewrite ?app_nil_r; intro Hin; apply in_map_iff in Hin; destruct Hin as [v [Heq Hv]];
    inversion Heq; subst; exact Hv.
Qed.

(** Every named demand and destination is supported in the duplicate-free universe. *)
Lemma while_demand_vars prog init : demand_vars_ok (while_demand_view prog init).
Proof.
  split; [exact (proj1 (var_universe_covers var_encoding (while_var_view prog init)))|].
  split.
  - intros e x b y m Hin; apply while_edge_vars_cover with (e := e).
    apply in_or_app; left.
    change (In y (flat_map while_action_uses (skel_acts (to_skeleton prog) e))).
    apply in_app_iff in Hin; destruct Hin as [Hin|Hin]; apply in_flat_map in Hin;
      destruct Hin as [a [Ha Hy]].
    + apply in_flat_map; exists a; split; [exact Ha|].
      eapply (while_action_demand_vars a x b y m); apply in_or_app; left; exact Hy.
    + apply in_flat_map; exists a; split; [exact Ha|].
      eapply (while_action_demand_vars a x b y m); apply in_or_app; right; exact Hy.
  - split.
    + intros n y m Hfalse; contradiction.
    + intros e x Hdef; apply while_edge_vars_cover with (e := e); apply in_or_app; now right.
Qed.

(** A true finite-map demand is necessarily supported in the variable universe. *)
Lemma while_demand_supported prog init
    (d : finite_map var_encoding (dvars (while_demand_view prog init)) bool) x :
  dget var_encoding bool_lattice d x = true -> In x (dvars (while_demand_view prog init)).
Proof.
  intro Htrue; destruct (in_dec Nat.eq_dec x (dvars (while_demand_view prog init)))
    as [Hin|Hout]; [exact Hin|].
  unfold dget, pointwise_lookup in Htrue.
  rewrite finite_map_out in Htrue by exact Hout; discriminate.
Qed.

(** Transfer preserves a needed variable that the edge does not define. *)
Lemma while_transfer_retain prog init e d x :
  ~ In x (ddefs (while_demand_view prog init) e) -> dget var_encoding bool_lattice d x = true ->
  dget var_encoding bool_lattice
    (demand_transfer var_encoding bool_demand (while_demand_view prog init) e d) x = true.
Proof.
  intros Houtside Htrue; apply demand_bool_transfer_true; split.
  - eapply while_demand_supported; exact Htrue.
  - left; split; [|exact Htrue].
    destruct (FinSet.mem var_encoding x (FinSet.of_list var_encoding
      (ddefs (while_demand_view prog init) e))) eqn:Hmem; [|reflexivity].
    apply FinSet.of_list_spec in Hmem; contradiction.
Qed.

(** A forced operand is demanded at the input of its edge. *)
Lemma while_transfer_forced prog init e d x :
  In (x, true) (dnec (while_demand_view prog init) e) ->
  dget var_encoding bool_lattice
    (demand_transfer var_encoding bool_demand (while_demand_view prog init) e d) x = true.
Proof.
  intro Hin; apply demand_bool_transfer_true; split.
  - destruct (while_demand_vars prog init) as [_ [Hcover _]].
    eapply (Hcover e x false x true); apply in_or_app; left; exact Hin.
  - right; left; exact Hin.
Qed.

(** Backward operands of a needed destination are demanded before the edge. *)
Lemma while_transfer_back prog init e d x y :
  In y (ddefs (while_demand_view prog init) e) ->
  In (x, true) (dback (while_demand_view prog init) e y (dget var_encoding bool_lattice d y)) ->
  dget var_encoding bool_lattice
    (demand_transfer var_encoding bool_demand (while_demand_view prog init) e d) x = true.
Proof.
  intros Hdef Hin; apply demand_bool_transfer_true; split.
  - destruct (while_demand_vars prog init) as [_ [Hcover _]].
    eapply (Hcover e y (dget var_encoding bool_lattice d y) x true).
    apply in_or_app; right; exact Hin.
  - right; right; exists y; split; assumption.
Qed.

(** A needed assignment result agrees when the input states agree on its backward demand. *)
Lemma while_demand_assignment prog init e y rhs st t d :
  skel_acts (to_skeleton prog) e = [AAtom (AAssign y rhs)] ->
  (forall x, dget var_encoding bool_lattice
    (demand_transfer var_encoding bool_demand (while_demand_view prog init) e d) x = true ->
    st x = t x) ->
  forall x, dget var_encoding bool_lattice d x = true ->
    update st y (eval_expr st rhs) x = update t y (eval_expr t rhs) x.
Proof.
  intros Hxs Hagree x Hneed; unfold update; destruct (Nat.eqb y x) eqn:Heq.
  - apply Nat.eqb_eq in Heq; subst x; apply eval_expr_agrees; intros x Hvar.
    apply Hagree; eapply while_transfer_back with (y := y).
    + change (In y (flat_map while_action_defs (skel_acts (to_skeleton prog) e))).
      rewrite Hxs; cbn; auto.
    + change (In (x, true) (flat_map
        (fun a => while_action_back a y (dget var_encoding bool_lattice d y))
        (skel_acts (to_skeleton prog) e))).
      rewrite Hxs, Hneed; cbn [flat_map while_action_back Nat.eqb].
      rewrite Nat.eqb_refl, app_nil_r; apply in_map_iff; exists x.
      split; [reflexivity|exact Hvar].
  - apply Hagree; apply while_transfer_retain; [|exact Hneed].
    change (~ In x (flat_map while_action_defs (skel_acts (to_skeleton prog) e))).
    rewrite Hxs; cbn; intros [Hequal|Hfalse]; [|contradiction].
    subst x; rewrite Nat.eqb_refl in Heq; discriminate.
Qed.

(** A primitive edge matches at its input demand while permitting dead-value differences. *)
Lemma while_demand_actions_match prog init e st l st' t d :
  acts_hold (while_client init) (skel_acts (to_skeleton prog) e) st l st' ->
  (forall x, dget var_encoding bool_lattice
      (demand_transfer var_encoding bool_demand (while_demand_view prog init) e d) x = true ->
    st x = t x) ->
  exists t', acts_hold (while_client init) (skel_acts (to_skeleton prog) e) t l t' /\
    forall x, dget var_encoding bool_lattice d x = true -> st' x = t' x.
Proof.
  intros Hacts Hagree.
  assert (Hkeep : forall x, ~ In x (ddefs (while_demand_view prog init) e) ->
      dget var_encoding bool_lattice d x = true -> st x = t x).
  { intros x Houtside Hneed; apply Hagree; apply while_transfer_retain; assumption. }
  assert (Hforced : forall x, In (x, true) (dnec (while_demand_view prog init) e) -> st x = t x).
  { intros x Hin; apply Hagree; apply while_transfer_forced; exact Hin. }
  destruct (while_edge_actions prog e) as [Hxs|[[a Hxs]|[[g [b Hxs]]|[p [n Hxs]]]]];
    rewrite Hxs in Hacts.
  - apply holds_nil_inv in Hacts; destruct Hacts as [-> ->].
    exists t; split; [rewrite Hxs; constructor|].
    intros x Hneed; apply Hkeep; [|exact Hneed].
    change (~ In x (flat_map while_action_defs (skel_acts (to_skeleton prog) e))).
    rewrite Hxs; cbn; tauto.
  - apply holds_single_inv in Hacts; destruct a as [|y rhs|rhs]; destruct Hacts as [-> ->].
    + exists t; split; [rewrite Hxs; apply holds_single; split; reflexivity|].
      intros x Hneed; apply Hkeep; [|exact Hneed].
      change (~ In x (flat_map while_action_defs (skel_acts (to_skeleton prog) e))).
      rewrite Hxs; cbn; tauto.
    + exists (update t y (eval_expr t rhs)); split.
      * rewrite Hxs; apply holds_single; split; reflexivity.
      * exact (while_demand_assignment prog init e y rhs st t d Hxs Hagree).
    + assert (Heval : eval_expr st rhs = eval_expr t rhs).
      { apply eval_expr_agrees; intros x Hvar; apply Hforced.
        change (In (x, true) (flat_map while_action_nec (skel_acts (to_skeleton prog) e))).
        rewrite Hxs; cbn [flat_map while_action_nec]; rewrite app_nil_r.
        apply in_map_iff; exists x; split; [reflexivity|exact Hvar]. }
      exists t; split.
      * rewrite Hxs; apply holds_single; split; [rewrite Heval; reflexivity|reflexivity].
      * intros x Hneed; apply Hkeep; [|exact Hneed].
        change (~ In x (flat_map while_action_defs (skel_acts (to_skeleton prog) e))).
        rewrite Hxs; cbn; tauto.
  - apply holds_single_inv in Hacts; destruct Hacts as [Hguard [-> ->]].
    assert (Heval : eval_expr st g = eval_expr t g).
    { apply eval_expr_agrees; intros x Hvar; apply Hforced.
      change (In (x, true) (flat_map while_action_nec (skel_acts (to_skeleton prog) e))).
      rewrite Hxs; cbn [flat_map while_action_nec]; rewrite app_nil_r.
      apply in_map_iff; exists x; split; [reflexivity|exact Hvar]. }
    exists t; split.
    + rewrite Hxs; apply holds_single; split; [|split; reflexivity].
      change (Some (negb (Z.eqb (eval_expr t g) 0)) = Some b); rewrite <- Heval; exact Hguard.
    + intros x Hneed; apply Hkeep; [|exact Hneed].
      change (~ In x (flat_map while_action_defs (skel_acts (to_skeleton prog) e))).
      rewrite Hxs; cbn; tauto.
  - apply holds_single_inv in Hacts; destruct Hacts as [-> ->].
    exists t; split; [rewrite Hxs; apply holds_single; split; reflexivity|].
    intros x Hneed; apply Hkeep; [|exact Hneed].
    change (~ In x (flat_map while_action_defs (skel_acts (to_skeleton prog) e))).
    rewrite Hxs; cbn; tauto.
Qed.

(** The Boolean demand adapter satisfies the complete generic demand laws. *)
Theorem while_demand_laws (prog : stmt) (init : store -> Prop) :
  demand_laws (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init))
    (reachable_state (skeleton_semantics (to_skeleton prog) (while_client init)))
    var_encoding bool_demand (while_demand_view prog init).
Proof.
  constructor.
  - apply skeleton_view_laws_hold.
  - intros s l s' Hfalse; exact Hfalse.
  - intros s l s' e x Hreach Hstep Htaken Houtside.
    exact (defs_frame (while_var_view_laws prog init) s l s' e x Hreach Hstep Htaken Houtside).
  - split.
    + pose proof (finite_pointwise_agree_laws var_encoding
        (dvars (while_demand_view prog init)) bool_lattice (@bool_agree Z)
        bool_laws bool_agree_laws) as Hlaws.
      constructor.
      * intros d s; exact (agree_refl Hlaws d (store_of s)).
      * intros a b s t Hle Hagree; exact (agree_antitone Hlaws a b
          (store_of s) (store_of t) Hle Hagree).
    + intros d s t Hagree x Hneed; symmetry; apply Hagree; exact Hneed.
  - intros u v Hfalse; discriminate.
  - apply while_back_false.
  - apply while_demand_vars.
  - intros s l s' t e d Hs Ht Hpoint Hstep Htaken Hagree.
    destruct (while_taken_payload _ _ _ _ _ _ Htaken) as [Hrow Hacts].
    destruct (while_demand_actions_match prog init e (store_of s) l (store_of s') (store_of t) d
      Hacts Hagree) as [st' [Hacts' Hpost]].
    destruct (out_realise (to_skeleton prog) (while_client init) t
      (skel_to (to_skeleton prog) e) (skel_acts (to_skeleton prog) e) l st')
      as [t' [Hstep' [Hpoint' Hstore]]].
    + exact (reachable_machine_valid _ (while_client init) t Ht).
    + change (machine_point t = machine_point s) in Hpoint; rewrite Hpoint; exact Hrow.
    + exact Hacts'.
    + exists t'; split; [exact Hstep'|split].
      * destruct Htaken as [Hin _]; split.
        -- change (machine_point t = machine_point s) in Hpoint; cbn; rewrite Hpoint; exact Hin.
        -- split; [exact Hpoint'|rewrite Hstore; exact Hacts'].
      * intros x Hneed; change (store_of s' x = store_of t' x).
        rewrite Hstore; apply Hpost; exact Hneed.
  - intros s t Hs Ht Hpoint Hagree.
    exact (exits_determine (while_var_view_laws prog init) s t Hs Ht Hpoint
      (fun x Hfalse => False_rect _ Hfalse)).
Qed.

(** Binary subexpressions are inventoried in preorder, with operand order retained. *)
Fixpoint binary_exprs (e : expr) : list expr :=
  match e with
  | EConst _ | EVar _ => []
  | EUn _ e => binary_exprs e
  | EBin o e1 e2 => EBin o e1 e2 :: binary_exprs e1 ++ binary_exprs e2
  end.

(** Primitive computations include assignment, output and guard expressions. *)
Definition while_action_exprs (a : action atom expr) : list expr :=
  match a with
  | AAtom (AAssign _ e) | AAtom (AOutput e) | AGuard e _ |
    AIndexIs e _ | AIndexAtLeast e _ => binary_exprs e
  | _ => []
  end.

(** An expression is killed exactly when an edge defines one of its operand variables. *)
Definition while_expr_killed (defined : list var) (u : expr) : bool :=
  let operands := FinSet.of_list var_encoding (expr_vars u) in
  existsb (fun x => FinSet.mem var_encoding x operands) defined.

(** Generated expressions survive every action of the edge. *)
Definition while_genkill_view (prog : stmt) (init : store -> Prop) :
    genkill_view (mstate store) Z skel_point (skel_edge atom expr) expr Z :=
  let acts := skel_acts (to_skeleton prog) in
  let killed := fun e => while_expr_killed (flat_map while_action_defs (acts e)) in
  {| gkview := gview (while_var_view prog init);
     gen := fun e => filter (fun u => negb (killed e u)) (flat_map while_action_exprs (acts e));
     kill := killed;
     uval := fun m u => Some (eval_expr (store_of m) u) |}.

(** A non-killed expression has no operand among an edge's definitions. *)
Lemma while_kill_frame prog init s l s' e u :
  taken (gview (while_var_view prog init)) s l s' e ->
  kill (while_genkill_view prog init) e u = false ->
  eval_expr (store_of s') u = eval_expr (store_of s) u.
Proof.
  intros [_ [_ Hacts]] Hkill; apply eval_expr_agrees; intros x Hvar.
  eapply while_actions_frame; [exact Hacts|].
  intro Hdef; assert (Htrue : kill (while_genkill_view prog init) e u = true).
  { change (existsb (fun x => FinSet.mem var_encoding x
      (FinSet.of_list var_encoding (expr_vars u)))
      (flat_map while_action_defs (skel_acts (to_skeleton prog) e)) = true).
    apply existsb_exists; exists x; split; [exact Hdef|apply FinSet.of_list_spec; exact Hvar]. }
  congruence.
Qed.

(** Available and busy expression reasoning respects all actual While transitions. *)
Theorem while_genkill_laws (prog : stmt) (init : store -> Prop) :
  genkill_laws (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) (while_genkill_view prog init).
Proof.
  constructor.
  - apply skeleton_view_laws_hold.
  - intros s l s' Hfalse; exact Hfalse.
  - intros s l s' e u Hreach Hstep Htaken Hgen.
    apply filter_In in Hgen; destruct Hgen as [_ Hkill]; apply negb_true_iff in Hkill.
    change (Some (eval_expr (store_of s') u) = Some (eval_expr (store_of s) u)).
    f_equal; exact (while_kill_frame prog init s l s' e u Htaken Hkill).
  - intros s l s' e u Hreach Hstep Htaken Hkill.
    change (Some (eval_expr (store_of s') u) = Some (eval_expr (store_of s) u)).
    f_equal; exact (while_kill_frame prog init s l s' e u Htaken Hkill).
  - intros s Hreach Hfinal; destruct s as [p fs st|p fs st]; [contradiction|].
    destruct p as [|d p], fs as [|f fs]; try contradiction.
    change (Graph.out (skeleton_graph (to_skeleton prog)) (PExit []) = []).
    rewrite skeleton_graph_out_agrees; reflexivity.
Qed.

(** A variable operand assignment contributes precisely its destination-source pair. *)
Definition while_action_copies (a : action atom expr) : list (var * var) :=
  match a with
  | AAtom (AAssign x (EVar y)) => [(x, y)]
  | _ => []
  end.

(** Copy analysis uses the same variable view and prepared action index. *)
Definition while_copy_view (prog : stmt) (init : store -> Prop) :
    copy_view (mstate store) Z skel_point (skel_edge atom expr) var Z :=
  let acts := skel_acts (to_skeleton prog) in
  {| cvars := while_var_view prog init;
     copies := fun e => flat_map while_action_copies (acts e) |}.

(** Each declared copy holds in the actual post-state, including self-copies. *)
Theorem while_copy_sound (prog : stmt) (init : store -> Prop) :
  forall s l s' e x y,
    reachable_state (skeleton_semantics (to_skeleton prog) (while_client init)) s ->
    step (skeleton_semantics (to_skeleton prog) (while_client init)) s l s' ->
    taken (gview (while_var_view prog init)) s l s' e ->
    In (x, y) (copies (while_copy_view prog init) e) ->
    vget (while_var_view prog init) s' x = vget (while_var_view prog init) s' y.
Proof.
  intros s l s' e x y Hreach Hstep [_ [_ Hacts]] Hcopy.
  change (In (x, y) (flat_map while_action_copies (skel_acts (to_skeleton prog) e))) in Hcopy.
  destruct (while_edge_actions prog e) as [Hxs|[[a Hxs]|[[g [b Hxs]]|[p [n Hxs]]]]];
    rewrite Hxs in Hcopy, Hacts; try contradiction.
  - destruct a as [|z rhs|rhs]; cbn [flat_map while_action_copies] in Hcopy; try contradiction.
    destruct rhs as [w|v|o rhs|o lhs rhs]; cbn [while_action_copies] in Hcopy; try contradiction.
    destruct Hcopy as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
    apply holds_single_inv in Hacts; destruct Hacts as [Hl Hstore].
    change (store_of s' x = store_of s' y); change (store_of s' = update (store_of s) x
      (store_of s y)) in Hstore; rewrite Hstore.
    unfold update; rewrite Nat.eqb_refl; destruct (Nat.eqb x y); reflexivity.
Qed.

(** Erasure preserves the source tree and replaces precisely selected assignments by skips. *)
Fixpoint erase_dead (dead : var -> bool) (s : stmt) : stmt :=
  match s with
  | SAssign x e => if dead x then SSkip else SAssign x e
  | SSeq s1 s2 => SSeq (erase_dead dead s1) (erase_dead dead s2)
  | SIf g s1 s2 => SIf g (erase_dead dead s1) (erase_dead dead s2)
  | SLoop body => SLoop (erase_dead dead body)
  | _ => s
  end.

(** A false closed-demand flag selects the corresponding assignment for erasure. *)
Definition while_dce (prog : stmt) (init : store -> Prop)
    (d : finite_map var_encoding (dvars (while_demand_view prog init)) bool) : stmt :=
  erase_dead (fun x => negb (dget var_encoding bool_lattice d x)) prog.

(** The erased primitive has the same control shape as the original atom. *)
Definition erase_atom (dead : var -> bool) (a : atom) : atom :=
  match a with
  | AAssign x e => if dead x then ANop else AAssign x e
  | _ => a
  end.

(** Mapping primitives preserves every skeleton constructor, guard and relative jump. *)
Fixpoint erase_skeleton (dead : var -> bool) (s : Skeleton.stmt atom expr) :
    Skeleton.stmt atom expr :=
  match s with
  | Skeleton.Atom a => Skeleton.Atom (erase_atom dead a)
  | Skeleton.Seq s1 s2 => Skeleton.Seq (erase_skeleton dead s1) (erase_skeleton dead s2)
  | Skeleton.If g s1 s2 => Skeleton.If g (erase_skeleton dead s1) (erase_skeleton dead s2)
  | Skeleton.Block body => Skeleton.Block (erase_skeleton dead body)
  | Skeleton.Loop body => Skeleton.Loop (erase_skeleton dead body)
  | _ => s
  end.

(** Source erasure and skeleton translation commute exactly. *)
Lemma erase_dead_skeleton dead prog :
  to_skeleton (erase_dead dead prog) = erase_skeleton dead (to_skeleton prog).
Proof.
  induction prog; cbn [erase_dead to_skeleton erase_skeleton erase_atom];
    rewrite ?IHprog, ?IHprog1, ?IHprog2; try reflexivity.
  destruct (dead x); reflexivity.
Qed.

(** Erasing a child preserves its direction and changes only its primitive contents. *)
Lemma erase_child dead s dir :
  child (erase_skeleton dead s) dir = option_map (erase_skeleton dead) (child s dir).
Proof.
  destruct s, dir; reflexivity.
Qed.

(** Subtree lookup commutes with erasure at valid and invalid positions. *)
Lemma erase_sub dead s p :
  sub (erase_skeleton dead s) p = option_map (erase_skeleton dead) (sub s p).
Proof.
  revert s; induction p as [|d p IH]; intro s; [reflexivity|].
  cbn [sub]; rewrite erase_child; destruct (child s d); [apply IH|reflexivity].
Qed.

(** Continuation frame tags and owners are unchanged by primitive erasure. *)
Lemma erase_child_frame dead s d p : child_frame (erase_skeleton dead s) d p = child_frame s d p.
Proof.
  destruct s, d; reflexivity.
Qed.

(** Canonical lookup retains the original continuation stack. *)
Lemma erase_locate_from dead s base p fs :
  locate_from (erase_skeleton dead s) base p fs =
  option_map (fun row => (erase_skeleton dead (fst row), snd row)) (locate_from s base p fs).
Proof.
  revert s base fs; induction p as [|d p IH]; intros s base fs; [reflexivity|].
  cbn [locate_from]; rewrite erase_child, erase_child_frame.
  destruct (child s d); [apply IH|reflexivity].
Qed.

(** Label lookup retains the original prefix frames, including invalid suffixes. *)
Lemma erase_enclosing dead s base p fs :
  enclosing_from (erase_skeleton dead s) base p fs = enclosing_from s base p fs.
Proof.
  revert s base fs; induction p as [|d p IH]; intros s base fs; [reflexivity|].
  cbn [enclosing_from]; rewrite erase_child, erase_child_frame.
  destruct (child s d); [apply IH|destruct s; reflexivity].
Qed.

(** Erasure changes only atom actions within an edge payload. *)
Definition erase_action dead (a : action atom expr) : action atom expr :=
  match a with
  | AAtom a => AAtom (erase_atom dead a)
  | _ => a
  end.

(** Row mapping preserves each destination and the order of its actions. *)
Definition erase_row dead (r : skel_point * list (action atom expr)) :=
  (fst r, map (erase_action dead) (snd r)).

(** Unconditional jump rows preserve their exact label destination. *)
Lemma erase_jump_out dead s p n xs :
  jump_out (erase_skeleton dead s) p n (map (erase_action dead) xs) =
  map (erase_row dead) (jump_out s p n xs).
Proof.
  unfold jump_out, label_point; rewrite erase_enclosing.
  destruct (resume_target n (enclosing_from s [] p [])); reflexivity.
Qed.

(** Jump-table rows preserve order, multiplicity and invalid-label omission. *)
Lemma erase_table_out dead s p g ns i :
  table_out (erase_skeleton dead s) p g ns i = map (erase_row dead) (table_out s p g ns i).
Proof.
  revert i; induction ns as [|n ns IH]; intro i; [reflexivity|].
  cbn [table_out]; rewrite map_app, <- IH, <- erase_jump_out; reflexivity.
Qed.

(** Every outgoing table is the original table with primitive actions mapped in place. *)
Lemma erase_out dead s v :
  skel_out (erase_skeleton dead s) v = map (erase_row dead) (skel_out s v).
Proof.
  destruct v as [p|p]; cbn [skel_out].
  - rewrite erase_sub; destruct (sub s p) as [t|]; [|reflexivity].
    destruct t; cbn [erase_skeleton option_map]; try reflexivity.
    + exact (erase_jump_out dead s p n [AJump p n]).
    + rewrite map_app.
      pose proof (erase_jump_out dead s p n [AGuard g true; AJump p n]) as Hjump.
      cbn [map erase_action] in Hjump; rewrite Hjump; reflexivity.
    + rewrite map_app, erase_table_out.
      pose proof (erase_jump_out dead s p n [AIndexAtLeast g (length ns); AJump p n]) as Hjump.
      cbn [map erase_action] in Hjump; rewrite Hjump; reflexivity.
  - unfold locate; rewrite erase_locate_from.
    destruct (locate_from s [] p []) as [[t fs]|]; [|reflexivity].
    destruct fs; reflexivity.
Qed.

(** Outgoing keys are identical in the source and erased graphs. *)
Lemma erase_graph_out dead s v :
  Graph.out (skeleton_graph (erase_skeleton dead s)) v = Graph.out (skeleton_graph s) v.
Proof.
  rewrite !skeleton_graph_out_agrees, erase_out, length_map; reflexivity.
Qed.

(** Every indexed destination is unchanged, including absent edge keys. *)
Lemma erase_to dead s e : skel_to (erase_skeleton dead s) e = skel_to s e.
Proof.
  rewrite !skel_to_agrees, erase_out, nth_error_map.
  destruct (nth_error (skel_out s (from e)) (slot e)) as [[v xs]|]; reflexivity.
Qed.

(** Every indexed payload is mapped exactly, including absent edge keys. *)
Lemma erase_acts dead s e :
  skel_acts (erase_skeleton dead s) e = map (erase_action dead) (skel_acts s e).
Proof.
  rewrite !skel_acts_agrees, erase_out, nth_error_map.
  destruct (nth_error (skel_out s (from e)) (slot e)) as [[v xs]|]; reflexivity.
Qed.

(** The target runs the erased program over literally the original graph dictionary. *)
Definition while_erased_graph prog init dead :
    graph_view (mstate store) Z skel_point (skel_edge atom expr) :=
  let target := skeleton_view (to_skeleton (erase_dead dead prog)) (while_client init) in
  {| cfg := cfg (gview (while_var_view prog init));
     point := point target;
     taken := taken target;
     stays := stays target |}.

(** Erasure retains genuine target transitions while reusing the unchanged source graph. *)
Lemma while_erased_graph_laws prog init dead :
  graph_view_laws (skeleton_semantics (to_skeleton (erase_dead dead prog)) (while_client init))
    (while_erased_graph prog init dead).
Proof.
  pose proof (skeleton_view_laws_hold (to_skeleton (erase_dead dead prog)) (while_client init))
    as Htarget; constructor.
  - apply skeleton_graph_wf.
  - intros m Hinit; exact (entry_points Htarget m Hinit).
  - intros s l s' Hreach Hstep; exact (edge_covers Htarget s l s' Hreach Hstep).
  - intros s l s' e Hreach Hstep Htaken.
    destruct (taken_edge Htarget s l s' e Hreach Hstep Htaken) as [Hin Hto].
    split.
    + change (In e (Graph.out (skeleton_graph (to_skeleton prog)) (machine_point s))).
      change (In e (Graph.out (skeleton_graph (to_skeleton (erase_dead dead prog)))
        (machine_point s))) in Hin.
      rewrite erase_dead_skeleton, erase_graph_out in Hin; exact Hin.
    + change (skel_to (to_skeleton prog) e = machine_point s').
      change (skel_to (to_skeleton (erase_dead dead prog)) e = machine_point s') in Hto.
      rewrite erase_dead_skeleton, erase_to in Hto; exact Hto.
  - intros s l s' Hreach Hstep Hfalse; contradiction.
Qed.

(** Only a singleton assignment action can be erased. *)
Definition while_edge_erased dead (xs : list (action atom expr)) : bool :=
  match xs with
  | [AAtom (AAssign x _)] => dead x
  | _ => false
  end.

(** Atom edges expose their source primitive for the generic effects theorem. *)
Definition while_edge_instr (xs : list (action atom expr)) : option atom :=
  match xs with
  | [AAtom a] => Some a
  | _ => None
  end.

(** The two-program erasure adapter uses separate demand and target-state agreements. *)
Definition while_erasure (prog : stmt) (init : store -> Prop)
    (d : finite_map var_encoding (dvars (while_demand_view prog init)) bool) :
    erasure (mstate store) Z skel_point (skel_edge atom expr) var Z atom :=
  let dead := fun x => negb (dget var_encoding bool_lattice d x) in
  let acts := skel_acts (to_skeleton prog) in
  {| er_demand := while_demand_view prog init;
     er_graph := while_erased_graph prog init dead;
     er_erased := fun e => while_edge_erased dead (acts e);
     er_instr := fun e => while_edge_instr (acts e) |}.

(** A listed edge can be realized from any reachable state whose store executes its payload. *)
Lemma while_edge_realise tree init m e l st' :
  reachable_state (skeleton_semantics tree (while_client init)) m ->
  In e (Graph.out (skeleton_graph tree) (machine_point m)) ->
  acts_hold (while_client init) (skel_acts tree e) (store_of m) l st' ->
  exists m', skel_step tree (while_client init) m l m' /\
    taken (skeleton_view tree (while_client init)) m l m' e /\ store_of m' = st'.
Proof.
  intros Hreach Hout Hacts.
  assert (Hrow : In (skel_to tree e, skel_acts tree e) (skel_out tree (machine_point m))).
  { apply skeleton_out_slot in Hout; destruct Hout as [Hfrom Hbound].
    rewrite skel_to_agrees, skel_acts_agrees.
    destruct (nth_error (skel_out tree (from e)) (slot e)) as [[v xs]|] eqn:Hnth.
    - rewrite <- Hfrom; eapply nth_error_In; exact Hnth.
    - apply nth_error_None in Hnth; rewrite Hfrom in Hnth; lia. }
  destruct (out_realise tree (while_client init) m (skel_to tree e) (skel_acts tree e) l st'
    (reachable_machine_valid tree (while_client init) m Hreach) Hrow Hacts)
    as [m' [Hstep [Hpoint Hstore]]].
  exists m'; split; [exact Hstep|split; [|exact Hstore]].
  split; [exact Hout|split; [exact Hpoint|rewrite Hstore; exact Hacts]].
Qed.

(** At a reachable state, normal completion depends only on being at the root exit. *)
Lemma while_final_point tree init m :
  reachable_state (skeleton_semantics tree (while_client init)) m ->
  (final (skeleton_endings tree (while_client init)) m <-> machine_point m = PExit []).
Proof.
  intro Hreach; pose proof (reachable_machine_valid tree (while_client init) m Hreach) as Hvalid.
  destruct m as [p fs st|p fs st]; cbn [machine_point skeleton_endings final]; [split;
    [contradiction|discriminate]|].
  split.
  - destruct p, fs; try contradiction; reflexivity.
  - intro Heq; injection Heq as ->.
    assert (fs = []) by (eapply context_unique; [exact Hvalid|apply context_root]).
    subst fs; exact I.
Qed.

(** A kept edge's mapped payload is exactly its original payload. *)
Lemma while_kept_actions dead xs : while_action_list xs ->
  while_edge_erased dead xs = false -> map (erase_action dead) xs = xs.
Proof.
  intros [->|[[a ->]|[[g [b ->]]|[p [n ->]]]]]; try reflexivity.
  destruct a as [|x rhs|rhs]; cbn [while_edge_erased map erase_action erase_atom]; try reflexivity.
  intro Hdead; rewrite Hdead; reflexivity.
Qed.

(** Erased edges are exactly singleton assignments to selected destinations. *)
Lemma while_erased_action dead xs : while_edge_erased dead xs = true ->
  exists x rhs, xs = [AAtom (AAssign x rhs)] /\ dead x = true.
Proof.
  destruct xs as [|a xs]; [discriminate|].
  destruct a as [[|x rhs|rhs]|g b|g i|g n|p n]; try discriminate.
  destruct xs; [|discriminate]; intro Hdead; exists x, rhs; split; [reflexivity|exact Hdead].
Qed.

(** Target and source outgoing key observations agree pointwise. *)
Lemma while_erased_out prog dead v :
  Graph.out (skeleton_graph (to_skeleton (erase_dead dead prog))) v =
  Graph.out (skeleton_graph (to_skeleton prog)) v.
Proof.
  rewrite erase_dead_skeleton; apply erase_graph_out.
Qed.

(** Target payloads are the mapped source payloads on every edge key. *)
Lemma while_erased_acts prog dead e :
  skel_acts (to_skeleton (erase_dead dead prog)) e =
  map (erase_action dead) (skel_acts (to_skeleton prog) e).
Proof.
  rewrite erase_dead_skeleton; apply erase_acts.
Qed.

(** Kept primitives match from the original machine to the actual erased machine. *)
Lemma while_kept_forth prog init d e s l s1 t :
  reachable_state (skeleton_semantics (to_skeleton prog) (while_client init)) s ->
  reachable_state
    (skeleton_semantics (to_skeleton (while_dce prog init d)) (while_client init)) t ->
  machine_point t = machine_point s ->
  taken (gview (while_var_view prog init)) s l s1 e ->
  er_erased (while_erasure prog init d) e = false ->
  agree (demand_agreement var_encoding bool_demand (while_demand_view prog init))
    (demand_transfer var_encoding bool_demand (while_demand_view prog init) e d) s t ->
  exists t', skel_step (to_skeleton (while_dce prog init d)) (while_client init) t l t' /\
    taken (er_graph (while_erasure prog init d)) t l t' e /\
    er_agree var_encoding (while_erasure prog init d) d s1 t'.
Proof.
  intros Hs Ht Hpoint [Hout [_ Hacts]] Hkept Hagree.
  destruct (while_demand_actions_match prog init e (store_of s) l (store_of s1) (store_of t) d
    Hacts Hagree) as [st' [Hacts' Hpost]].
  pose proof (while_kept_actions _ _ (while_edge_actions prog e) Hkept) as Hmap.
  destruct (while_edge_realise (to_skeleton (while_dce prog init d)) init t e l st' Ht)
    as [t' [Hstep' [Htaken' Hstore]]].
  - unfold while_dce; rewrite while_erased_out, Hpoint; exact Hout.
  - unfold while_dce; rewrite while_erased_acts, Hmap; exact Hacts'.
  - exists t'; split; [exact Hstep'|split; [exact Htaken'|]].
    intros x Hneed; change (store_of s1 x = store_of t' x).
    rewrite Hstore; apply Hpost; exact Hneed.
Qed.

(** Kept primitives match back from the actual erased machine to the source machine. *)
Lemma while_kept_back prog init d e s t l t1 :
  reachable_state (skeleton_semantics (to_skeleton prog) (while_client init)) s ->
  reachable_state
    (skeleton_semantics (to_skeleton (while_dce prog init d)) (while_client init)) t ->
  machine_point t = machine_point s ->
  taken (er_graph (while_erasure prog init d)) t l t1 e ->
  er_erased (while_erasure prog init d) e = false ->
  agree (demand_agreement var_encoding bool_demand (while_demand_view prog init))
    (demand_transfer var_encoding bool_demand (while_demand_view prog init) e d) s t ->
  exists s1, skel_step (to_skeleton prog) (while_client init) s l s1 /\
    taken (gview (while_var_view prog init)) s l s1 e /\
    er_agree var_encoding (while_erasure prog init d) d s1 t1.
Proof.
  intros Hs Ht Hpoint [Hout [_ Hacts]] Hkept Hagree.
  pose proof (while_kept_actions _ _ (while_edge_actions prog e) Hkept) as Hmap.
  change (acts_hold (while_client init) (skel_acts (to_skeleton (while_dce prog init d)) e)
    (store_of t) l (store_of t1)) in Hacts.
  unfold while_dce in Hacts; rewrite while_erased_acts, Hmap in Hacts.
  destruct (while_demand_actions_match prog init e (store_of t) l (store_of t1) (store_of s) d
    Hacts) as [st' [Hacts' Hpost]].
  - intros x Hneed; symmetry; apply Hagree; exact Hneed.
  - destruct (while_edge_realise (to_skeleton prog) init s e l st' Hs) as
      [s1 [Hstep' [Htaken' Hstore]]].
    + change (In e (Graph.out (skeleton_graph (to_skeleton (while_dce prog init d)))
        (machine_point t))) in Hout.
      unfold while_dce in Hout; rewrite while_erased_out, Hpoint in Hout; exact Hout.
    + exact Hacts'.
    + exists s1; split; [exact Hstep'|split; [exact Htaken'|]].
      intros x Hneed; change (store_of s1 x = store_of t1 x).
      rewrite Hstore; symmetry; apply Hpost; exact Hneed.
Qed.

(** An erased assignment is realized by an actual silent no-op in the target machine. *)
Lemma while_nop_forth prog init d e s l s1 t :
  reachable_state (skeleton_semantics (to_skeleton prog) (while_client init)) s ->
  reachable_state
    (skeleton_semantics (to_skeleton (while_dce prog init d)) (while_client init)) t ->
  machine_point t = machine_point s ->
  taken (gview (while_var_view prog init)) s l s1 e ->
  er_erased (while_erasure prog init d) e = true ->
  exists t', skel_step (to_skeleton (while_dce prog init d)) (while_client init) t [] t' /\
    taken (er_graph (while_erasure prog init d)) t [] t' e /\ store_of t' = store_of t.
Proof.
  intros Hs Ht Hpoint [Hout _] Herased.
  destruct (while_erased_action _ _ Herased) as [x [rhs [Hxs Hdead]]].
  destruct (while_edge_realise (to_skeleton (while_dce prog init d)) init t e [] (store_of t) Ht)
    as [t' [Hstep [Htaken Hstore]]].
  - unfold while_dce; rewrite while_erased_out, Hpoint; exact Hout.
  - unfold while_dce; rewrite while_erased_acts, Hxs; cbn [map erase_action erase_atom].
    rewrite Hdead; apply holds_single; split; reflexivity.
  - exists t'; split; [exact Hstep|split; assumption].
Qed.

(** A target no-op corresponds to a total source assignment on the same edge. *)
Lemma while_nop_back prog init d e s t l t1 :
  reachable_state (skeleton_semantics (to_skeleton prog) (while_client init)) s ->
  reachable_state
    (skeleton_semantics (to_skeleton (while_dce prog init d)) (while_client init)) t ->
  machine_point t = machine_point s ->
  taken (er_graph (while_erasure prog init d)) t l t1 e ->
  er_erased (while_erasure prog init d) e = true ->
  l = [] /\ store_of t1 = store_of t /\
    exists s1 l0, skel_step (to_skeleton prog) (while_client init) s l0 s1 /\
      taken (gview (while_var_view prog init)) s l0 s1 e.
Proof.
  intros Hs Ht Hpoint [Hout [_ Hacts]] Herased.
  destruct (while_erased_action _ _ Herased) as [x [rhs [Hxs Hdead]]].
  change (acts_hold (while_client init) (skel_acts (to_skeleton (while_dce prog init d)) e)
    (store_of t) l (store_of t1)) in Hacts.
  unfold while_dce in Hacts; rewrite while_erased_acts, Hxs in Hacts.
  cbn [map erase_action erase_atom] in Hacts; rewrite Hdead in Hacts.
  apply holds_single_inv in Hacts; destruct Hacts as [Hl Hstore]; split; [exact Hl|].
  split; [exact Hstore|].
  destruct (while_edge_realise (to_skeleton prog) init s e []
    (update (store_of s) x (eval_expr (store_of s) rhs)) Hs) as [s1 [Hstep [Htaken _]]].
  - change (In e (Graph.out (skeleton_graph (to_skeleton (while_dce prog init d)))
      (machine_point t))) in Hout.
    unfold while_dce in Hout; rewrite while_erased_out, Hpoint in Hout; exact Hout.
  - rewrite Hxs; apply holds_single; split; reflexivity.
  - exists s1, []; split; assumption.
Qed.

(** The erased and original machines satisfy the full two-program erasure contract. *)
Theorem while_erasure_laws (prog : stmt) (init : store -> Prop)
    (d : finite_map var_encoding (dvars (while_demand_view prog init)) bool) :
  loops_ok 0 prog = true ->
  erasure_laws KeepTraps (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init))
    (skeleton_semantics (to_skeleton (while_dce prog init d)) (while_client init))
    (skeleton_endings (to_skeleton (while_dce prog init d)) (while_client init))
    var_encoding (while_erasure prog init d) d.
Proof.
  intro Hlabels; constructor.
  - reflexivity.
  - apply while_erased_graph_laws.
  - intros t l t' Hfalse; exact Hfalse.
  - intros e s l s1 t [Hs _] Ht Hpoint Hstep Htaken Hkept Hagree.
    exact (while_kept_forth prog init d e s l s1 t Hs Ht Hpoint Htaken Hkept Hagree).
  - intros e s t l t1 [Hs _] Ht Hpoint Hstep Htaken Hkept Hagree.
    exact (while_kept_back prog init d e s t l t1 Hs Ht Hpoint Htaken Hkept Hagree).
  - intros e s l s1 t [Hs _] Ht Hpoint Hstep Htaken Herased.
    destruct (while_nop_forth prog init d e s l s1 t Hs Ht Hpoint Htaken Herased)
      as [t' [Hnext [Hedge Hstore]]].
    exists t'; split; [exact Hnext|split; [exact Hedge|intros x; change (store_of t' x =
      store_of t x); rewrite Hstore; reflexivity]].
  - intros e s t l t1 [Hs _] Ht Hpoint Hstep Htaken Herased.
    destruct (while_nop_back prog init d e s t l t1 Hs Ht Hpoint Htaken Herased)
      as [Hl [Hstore Hsource]].
    split; [exact Hl|split; [intros x; change (store_of t1 x = store_of t x);
      rewrite Hstore; reflexivity|exact Hsource]].
  - intros s t tag Htag [Hs _] Ht Hpoint Hagree.
    pose proof (while_final_point (to_skeleton prog) init s Hs) as Hfinal.
    pose proof (while_final_point (to_skeleton (while_dce prog init d)) init t Ht) as Hfinal'.
    destruct (while_no_failure prog init s) as [Htrap Hstop].
    destruct (while_no_failure (while_dce prog init d) init t) as [Htrap' Hstop'].
    change (machine_point t = machine_point s) in Hpoint.
    rewrite Hpoint in Hfinal'.
    destruct tag; cbn [ends_as]; tauto.
Qed.

(** Every erased destination has false demand and its assignment has no observable effects. *)
Lemma while_erased_dead prog init d e : er_erased (while_erasure prog init d) e = true ->
  (forall x, In x (ddefs (while_demand_view prog init) e) ->
    dget var_encoding bool_lattice d x = false) /\
  exists a, er_instr (while_erasure prog init d) e = Some a /\
    effectful while_effects KeepTraps a = false.
Proof.
  intro Herased; destruct (while_erased_action _ _ Herased) as [x [rhs [Hxs Hdead]]].
  apply negb_true_iff in Hdead; split.
  - intros y Hy; change (In y (flat_map while_action_defs (skel_acts (to_skeleton prog) e))) in Hy.
    rewrite Hxs in Hy; cbn in Hy; destruct Hy as [<-|Hfalse]; [exact Hdead|contradiction].
  - exists (AAssign x rhs); split; [|reflexivity].
    change (while_edge_instr (skel_acts (to_skeleton prog) e) = Some (AAssign x rhs)).
    rewrite Hxs; reflexivity.
Qed.

(** Every taken source edge exposes precisely the atom at its actual source position. *)
Lemma while_taken_instr prog init s l s' e :
  taken (gview (while_var_view prog init)) s l s' e ->
  instr_at (while_effects_view prog) s = er_instr (while_erasure prog init
    (needed_values var_encoding (while_demand_view prog init))) e.
Proof.
  intro Htaken; destruct (while_taken_payload _ _ _ _ _ _ Htaken) as [Hin Hacts].
  change (instr_at (while_effects_view prog) s =
    while_edge_instr (skel_acts (to_skeleton prog) e)).
  destruct s as [p fs st|p fs st]; cbn [while_effects_view instr_at skel_out machine_point] in *.
  - destruct (sub (to_skeleton prog) p) as [tree|] eqn:Hsub; [|contradiction].
    pose proof (while_tree_sub _ _ _ (to_skeleton_tree prog) Hsub) as Htree.
    destruct tree; cbn [while_tree] in Htree; try contradiction; cbn in Hin.
    all: try (destruct Hin as [Heq|Hfalse]; [inversion Heq; reflexivity|contradiction]).
    + destruct Hin as [Heq|[Heq|Hfalse]]; try contradiction; inversion Heq; reflexivity.
    + apply jump_out_inv in Hin; destruct Hin as [_ Heq]; rewrite Heq; reflexivity.
  - destruct (locate (to_skeleton prog) p) as [[tree gs]|] eqn:Hloc; [|contradiction].
    destruct gs as [|g gs]; [contradiction|].
    destruct Hin as [Heq|Hfalse]; [inversion Heq; reflexivity|contradiction].
Qed.

(** Removing assignments to unneeded variables preserves every While behaviour. *)
Theorem while_dce_sound (prog : stmt) (init : store -> Prop)
    (d : finite_map var_encoding (dvars (while_demand_view prog init)) bool) (sigma : store) :
  loops_ok 0 prog = true ->
  demand_closed var_encoding bool_demand (while_demand_view prog init) d -> init sigma ->
  same_behaviour (while_semantics prog init) while_endings (Run prog [] sigma)
    (while_semantics (while_dce prog init d) init) while_endings
    (Run (while_dce prog init d) [] sigma).
Proof.
  intros Hlabels Hclosed Hinit.
  assert (Hsame : same_behaviour
    (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) (Go [] [] sigma)
    (skeleton_semantics (to_skeleton (while_dce prog init d)) (while_client init))
    (skeleton_endings (to_skeleton (while_dce prog init d)) (while_client init)) (Go [] [] sigma)).
  { apply (dce_sound KeepTraps _ _ _ _
      (reachable_state (skeleton_semantics (to_skeleton prog) (while_client init)))
      var_encoding (while_erasure prog init d) d
      while_effects (while_effects_view prog) (Go [] [] sigma) (Go [] [] sigma)).
    - apply while_demand_laws.
    - apply reachable_invariant.
    - exact Hclosed.
    - apply while_effects_laws.
    - apply while_erasure_laws; exact Hlabels.
    - intros e x Herased Hdef; exact (proj1 (while_erased_dead prog init d e Herased) x Hdef).
    - intros e Herased; exact (proj2 (while_erased_dead prog init d e Herased)).
    - intros s l s' e Hreach Hstep Htaken; exact (while_taken_instr prog init s l s' e Htaken).
    - exists sigma; split; [reflexivity|exact Hinit].
    - exists sigma; split; [reflexivity|exact Hinit].
    - reflexivity.
    - intros x Hneed; reflexivity. }
  eapply same_behaviour_trans.
  - eapply bisimilar_same_behaviour; [apply while_skeleton_bisimulation|apply match_run, wc_root].
  - eapply same_behaviour_trans; [exact Hsame|].
    apply same_behaviour_sym.
    eapply bisimilar_same_behaviour; [apply while_skeleton_bisimulation|apply match_run, wc_root].
Qed.
