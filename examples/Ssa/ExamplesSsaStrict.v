(** * Strict SSA and frame histories

    Source definitions constrain changes within one activation, and full-machine frames retain
    their own activation histories. For example, a suspended caller skips its callee's output.
    Builds on: ExamplesSsaViews, ExamplesSsaTypingProofs and ViewsDominated. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphDominance GraphEdgeDominance.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsSsaPoints ViewsDominated
  ViewsEffects.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaBridge ExamplesSsaActivation
  ExamplesSsaViews.
Import List.ListNotations.
Local Open Scope nat_scope.

Definition frame_state (fr : sframe) : astate := AState (flabel fr) (fpc fr) (fenv fr).

(** Frame positions count from the innermost frame, retaining its function and environment. *)
Definition frame_activation (P : program) (s : state) (i : nat) : option (astate * func) :=
  option_map (fun fr => (frame_state fr, ffunc fr)) (nth_error (stack s) i).

(** A subtrace keeps some events in their original order. *)
Inductive subtrace {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, subtrace [] l
  | sub_keep : forall a l1 l2, subtrace l1 l2 -> subtrace (a :: l1) (a :: l2)
  | sub_skip : forall a l1 l2, subtrace l1 l2 -> subtrace l1 (a :: l2).

Local Lemma subtrace_refl {A} (xs : list A) : subtrace xs xs.
Proof.
  induction xs as [|x xs IH]; [apply sub_nil|apply sub_keep; exact IH].
Qed.

(** * Static refined definition sites *)

(** Definition witnesses retain the source occurrence, with a separate constructor for calls. *)
Inductive strict_definition_site (P : program) (f : func)
    : ssa_refined_value -> ssa_refined_point -> Prop :=
  | StrictParam : forall fd l b x,
      find_func P f = Some fd -> find_block fd l = Some b ->
      In x (map fst (bparams b)) ->
      strict_definition_site P f (SsaSourceValue x) (SsaBeforeParams l)
  | StrictInstruction : forall fd l b pc i x,
      find_func P f = Some fd -> find_block fd l = Some b ->
      nth_error (bbody b) pc = Some i -> In x (instr_def i) ->
      strict_definition_site P f (SsaSourceValue x) (SsaExecPoint l pc)
  | StrictCall : forall fd l b c args k,
      find_func P f = Some fd -> find_block fd l = Some b -> bterm b = TCall c args k ->
      strict_definition_site P f (SsaCallResult l) (SsaExecPoint l (length (bbody b))).

Local Lemma strict_site_source P f x d :
  strict_definition_site P f (SsaSourceValue x) d ->
  exists home origin,
    In (x, (home, origin))
      (flat_map ExamplesSsaViews.ssa_source_occurrences (ssa_blocks P f)) /\
    d = match origin with
      | None => SsaBeforeParams (fst home)
      | Some _ => SsaExecPoint (fst home) (snd home)
      end.
Proof.
  intro Hsite; inversion Hsite as [fd l b y Hf Hb Hparam|
    fd l b pc i y Hf Hb Hnth Hdef|]; subst.
  - exists (l, 0), None; split; [|reflexivity].
    eapply ExamplesSsaViews.ssa_source_parameter_occurrence; eassumption.
  - exists (l, pc), (Some i); split; [|reflexivity].
    eapply ExamplesSsaViews.ssa_source_instruction_occurrence; eassumption.
Qed.

Local Lemma strict_site_unique ext P f x d d' :
  wf_program ext P -> strict_definition_site P f x d ->
  strict_definition_site P f x d' -> d = d'.
Proof.
  intros Hwf Hsite Hsite'; destruct x as [x|l].
  - destruct (strict_site_source P f x d Hsite) as [home [origin [Hin ->]]].
    destruct (strict_site_source P f x d' Hsite') as [home' [origin' [Hin' ->]]].
    pose proof (ExamplesSsaViews.ssa_source_occurrence_unique ext P f x
      (home, origin) (home', origin') Hwf Hin Hin') as Heq.
    injection Heq as <- <-; reflexivity.
  - inversion Hsite as [| |fd label b c args k Hf Hb Hterm]; subst.
    inversion Hsite' as [| |fd' label b' c' args' k' Hf' Hb' Hterm']; subst.
    rewrite Hf in Hf'; injection Hf' as <-.
    rewrite Hb in Hb'; injection Hb' as <-; reflexivity.
Qed.

Local Lemma strict_site_rows ext P f x d :
  wf_program ext P ->
  (In (x, d) (flat_map ssa_refined_definition_rows (ssa_blocks P f)) <->
    strict_definition_site P f x d).
Proof.
  intro Hwf; split.
  - intro Hin; apply in_flat_map in Hin; destruct Hin as [[l b] [Hblock Hrow]].
    unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf;
      [|contradiction].
    assert (Hb : find_block fd l = Some b).
    { apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
        exact Hblock]. }
    unfold ssa_refined_definition_rows in Hrow; cbn [fst snd] in Hrow.
    rewrite !in_app_iff in Hrow; destruct Hrow as [Hparam|[Hbody|Hcall]].
    + apply in_map_iff in Hparam; destruct Hparam as [[y ty] [Heq Hin]].
      injection Heq as <- <-; eapply StrictParam; try eassumption.
      apply in_map_iff; exists (y, ty); split; [reflexivity|exact Hin].
    + apply in_flat_map in Hbody; destruct Hbody as [[pc i] [Henum Hrow]].
      apply in_map_iff in Hrow; destruct Hrow as [y [Heq Hdef]].
      injection Heq as <- <-; eapply StrictInstruction; try eassumption.
      apply ExamplesSsaViews.ssa_enumerate_nth in Henum.
      destruct Henum as [offset [Heq Hnth]]; cbn in Heq; subst pc; exact Hnth.
    + destruct (bterm b) eqn:Hterm; try contradiction.
      destruct Hcall as [Heq|Hfalse]; [injection Heq as <- <-|contradiction].
      eapply StrictCall; eassumption.
  - intro Hsite; destruct Hsite as [fd l b x Hf Hb Hparam|
      fd l b pc i x Hf Hb Hnth Hdef|fd l b c args k Hf Hb Hterm];
      apply in_flat_map; exists (l, b); split;
      try solve [unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb].
    + unfold ssa_refined_definition_rows; cbn [fst snd]; apply in_or_app; left.
      apply in_map_iff in Hparam; destruct Hparam as [[y ty] [Heq Hin]].
      cbn in Heq; subst y; apply in_map_iff; exists (x, ty); split; [reflexivity|exact Hin].
    + unfold ssa_refined_definition_rows; cbn [fst snd]; apply in_or_app; right.
      apply in_or_app; left; apply in_flat_map; exists (pc, i); split.
      * apply ExamplesSsaViews.ssa_enumerate_nth; exists pc; split; [lia|exact Hnth].
      * apply in_map_iff; exists x; split; [reflexivity|exact Hdef].
    + unfold ssa_refined_definition_rows; cbn [fst snd]; apply in_or_app; right.
      apply in_or_app; right; rewrite Hterm; left; reflexivity.
Qed.

Local Lemma strict_definition_lookup ext P f x d :
  wf_program ext P ->
  (point_definition (ssa_refined_points P f) x = Some d <->
    strict_definition_site P f x d).
Proof.
  intro Hwf; split.
  - intro Hget; apply (proj1 (strict_site_rows ext P f x d Hwf)).
    exact (ssa_map_get_sound ssa_refined_value_encoding _ _ _ Hget).
  - intro Hsite; apply ssa_map_get_complete.
    + apply (proj2 (strict_site_rows ext P f x d Hwf)); exact Hsite.
    + intros d' Hin; apply (strict_site_unique ext P f x d' d Hwf); [|exact Hsite].
      apply (proj1 (strict_site_rows ext P f x d' Hwf)); exact Hin.
Qed.

Local Lemma strict_outgoing_definition ext P f n e x :
  wf_program ext P -> In e (Graph.out (ssa_refined_graph P f) n) ->
  In x (edge_def (point_model (ssa_refined_points P f)) e) ->
  strict_definition_site P f x n.
Proof.
  intros Hwf Hout Hdef.
  destruct (ExamplesSsaViews.ssa_refined_out_local ext P f n e Hwf Hout)
    as [fd [l [b [p [Hf [Hb [Hlocal Hsource]]]]]]].
  change (In x (match Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) with
    | Some p => srp_defs p | None => [] end)) in Hdef.
  rewrite (ExamplesSsaViews.ssa_refined_index_complete ext P f fd l b e p
    Hwf Hf Hb Hlocal) in Hdef.
  rewrite <- Hsource.
  destruct Hlocal as [|pc i Hnth|c args k Hterm|slot dst args Hedge|y Hterm].
  - cbn [srp_defs] in Hdef; apply in_map_iff in Hdef.
    destruct Hdef as [y [<- Hin]]; eapply StrictParam; eassumption.
  - cbn [ssa_refined_instruction_row srp_defs fst snd] in Hdef |- *.
    apply in_map_iff in Hdef; destruct Hdef as [y [<- Hin]].
    eapply StrictInstruction; eassumption.
  - destruct Hdef as [<-|Hfalse]; [eapply StrictCall; eassumption|contradiction].
  - unfold ssa_refined_transfer_row in Hdef; cbn [fst snd] in Hdef.
    destruct (bterm b); contradiction.
  - contradiction.
Qed.

Local Lemma strict_home_kills ext P f x d e :
  wf_program ext P -> strict_definition_site P f x d ->
  In e (Graph.out (ssa_refined_graph P f) d) ->
  In x (edge_def (point_model (ssa_refined_points P f)) e).
Proof.
  intros Hwf Hsite Hout.
  destruct (ExamplesSsaViews.ssa_refined_out_local ext P f d e Hwf Hout)
    as [fd' [l' [b' [p [Hf' [Hb' [Hlocal Hsource]]]]]]].
  change (In x (match Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) with
    | Some p => srp_defs p | None => [] end)).
  rewrite (ExamplesSsaViews.ssa_refined_index_complete ext P f fd' l' b' e p
    Hwf Hf' Hb' Hlocal).
  pose proof (ExamplesSsaViews.ssa_refined_local_source _ _ _ _ _ Hlocal) as Howner.
  rewrite Hsource in Howner.
  destruct Hsite as [fd l b x Hf Hb Hparam|
    fd l b pc i x Hf Hb Hnth Hdef|fd l b c args k Hf Hb Hterm];
    cbn [ssa_refined_point_owner] in Howner; subst l';
    rewrite Hf in Hf'; injection Hf' as <-;
    rewrite Hb in Hb'; injection Hb' as <-.
  - destruct Hlocal as [|pc i Hnth|c args k Hterm|slot dst args Hedge|y Hterm];
      try discriminate Hsource.
    + apply in_map; exact Hparam.
    + unfold ssa_refined_transfer_row in Hsource; cbn [fst snd] in Hsource.
      destruct (bterm b); discriminate.
  - assert (Hpc : pc < length (bbody b)) by
      (apply nth_error_Some; rewrite Hnth; discriminate).
    destruct Hlocal as [|pc' i' Hnth'|c args k Hterm|slot dst args Hedge|y Hterm];
      cbn [ssa_refined_instruction_row srp_source fst snd] in Hsource;
      try discriminate Hsource.
    + injection Hsource as Heq; subst pc'; rewrite Hnth in Hnth'; injection Hnth' as <-.
      apply in_map; exact Hdef.
    + injection Hsource as Heq; lia.
    + unfold ssa_refined_transfer_row in Hsource; cbn [fst snd] in Hsource.
      destruct (bterm b); try discriminate; injection Hsource as Heq; lia.
    + injection Hsource as Heq; lia.
  - destruct Hlocal as [|pc i Hnth|c' args' k' Hterm'|slot dst actual Hedge|y Hterm'];
      cbn [ssa_refined_instruction_row srp_source fst snd] in Hsource;
      try discriminate Hsource.
    + injection Hsource as Heq; subst pc.
      assert (Hbound : length (bbody b) < length (bbody b)) by
        (apply nth_error_Some; rewrite Hnth; discriminate).
      lia.
    + left; reflexivity.
    + unfold ssa_refined_transfer_row in Hsource; cbn [fst snd] in Hsource.
      rewrite Hterm in Hsource; discriminate.
    + congruence.
Qed.

(** * Certified availability in the refined graph *)

Definition strict_available (fd : fdef) (R : requirements) (n : ssa_refined_point)
    : list ssa_refined_value :=
  let source l pc := match find_block fd l with
    | Some b => map SsaSourceValue (available_at b R l pc)
    | None => []
    end in
  match n with
  | SsaBeforeParams l => map SsaSourceValue (required R l)
  | SsaExecPoint l pc => source l pc
  | SsaCallReady l =>
    SsaCallResult l :: match find_block fd l with
      | Some b => source l (length (bbody b))
      | None => []
      end
  | SsaAfterReturn l => match find_block fd l with
      | Some b => source l (length (bbody b))
      | None => []
      end
  | SsaDeadPoint _ => []
  end.

Local Lemma strict_available_exec fd R l b pc :
  find_block fd l = Some b ->
  strict_available fd R (SsaExecPoint l pc) = map SsaSourceValue (available_at b R l pc).
Proof.
  intro Hb; cbn [strict_available]; rewrite Hb; reflexivity.
Qed.

Local Lemma strict_available_transfer ext P f fd R l b slot dst args x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  availability_certificate fd R -> nth_error (term_edges (bterm b)) slot = Some (dst, args) ->
  In x (strict_available fd R (SsaBeforeParams dst)) ->
  In x (strict_available fd R
    (if match bterm b with TCall _ _ _ => true | _ => false end
      then SsaCallReady l else SsaExecPoint l (length (bbody b)))).
Proof.
  intros Hwf Hf Hb Hcert Hedge Havailable.
  cbn [strict_available] in Havailable; apply in_map_iff in Havailable.
  destruct Havailable as [y [<- Hy]].
  pose proof (proj2 (proj2 (certificate_block fd R l b Hcert Hb))) as Hedges.
  pose proof (proj1 (Forall_forall _ _)
    (proj1 (Forall_forall _ _) Hedges (dst, args) (nth_error_In _ slot Hedge)) y Hy)
    as Hfinish.
  assert (Hin : In (SsaSourceValue y)
    (map SsaSourceValue (available_at b R l (length (bbody b))))).
  { apply in_map; unfold available_at, prefix_defs; rewrite firstn_all; exact Hfinish. }
  destruct (bterm b); cbn [strict_available]; rewrite Hb; try exact Hin.
  right; exact Hin.
Qed.

Local Lemma strict_available_local ext P f fd R l b e p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  availability_certificate fd R ->
  ssa_refined_local (first_index (ssa_blocks P f)) l b e p ->
  forall x, In x (strict_available fd R (srp_target p)) ->
    In x (strict_available fd R (srp_source p)) \/ In x (srp_defs p).
Proof.
  intros Hwf Hf Hb Hcert Hlocal x Havailable.
  destruct Hlocal as [|pc i Hnth|c args k Hterm|slot dst args Hedge|y Hterm].
  - cbn [srp_target] in Havailable.
    rewrite (strict_available_exec fd R l b 0 Hb) in Havailable.
    unfold available_at, prefix_defs in Havailable; cbn in Havailable.
    rewrite map_app, in_app_iff in Havailable; destruct Havailable as [Hparam|Hrequired];
      [right; exact Hparam|left; exact Hrequired].
  - cbn [ssa_refined_instruction_row srp_target srp_source srp_defs fst snd] in *.
    rewrite (strict_available_exec fd R l b (S pc) Hb) in Havailable.
    rewrite (strict_available_exec fd R l b pc Hb).
    apply in_map_iff in Havailable; destruct Havailable as [y [<- Hy]].
    unfold available_at, prefix_defs in Hy.
    rewrite (firstn_step _ _ _ Hnth), flat_map_app in Hy.
    cbn [flat_map] in Hy; rewrite app_nil_r, !in_app_iff in Hy.
    destruct (in_dec Nat.eq_dec y (instr_def i)) as [Hdef|Hnot].
    + right; apply in_map; exact Hdef.
    + left; apply in_map; unfold available_at, prefix_defs; rewrite !in_app_iff; tauto.
  - cbn [srp_target strict_available] in Havailable; rewrite Hb in Havailable.
    cbn [srp_source srp_defs]; destruct Havailable as [<-|Hin];
      [right; left; reflexivity|left].
    rewrite (strict_available_exec fd R l b _ Hb); exact Hin.
  - left; unfold ssa_refined_transfer_row in *; cbn [fst snd srp_target] in *.
    assert (Hbefore : In x (strict_available fd R (SsaBeforeParams dst))) by
      (destruct (bterm b); exact Havailable).
    pose proof (strict_available_transfer ext P f fd R l b slot dst args x
      Hwf Hf Hb Hcert Hedge Hbefore) as Hin.
    destruct (bterm b); exact Hin.
  - left; cbn [srp_target strict_available] in Havailable; rewrite Hb in Havailable.
    cbn [srp_source]; rewrite (strict_available_exec fd R l b _ Hb); exact Havailable.
Qed.

Local Lemma strict_instruction_available fd R l b pc i x :
  availability_certificate fd R -> find_block fd l = Some b ->
  nth_error (bbody b) pc = Some i -> In x (instr_uses i) ->
  In (SsaSourceValue x) (strict_available fd R (SsaExecPoint l pc)).
Proof.
  intros Hcert Hb Hnth Huse; rewrite (strict_available_exec fd R l b pc Hb).
  apply in_map; exact (proj1 (Forall_forall _ _)
    (body_available_use _ _ _ _ (proj1 (certificate_block fd R l b Hcert Hb)) Hnth)
    x Huse).
Qed.

Local Lemma strict_terminal_available fd R l b x :
  availability_certificate fd R -> find_block fd l = Some b ->
  In x (term_uses (bterm b)) ->
  In (SsaSourceValue x) (strict_available fd R (SsaExecPoint l (length (bbody b)))).
Proof.
  intros Hcert Hb Huse; rewrite (strict_available_exec fd R l b _ Hb).
  apply in_map; unfold available_at, prefix_defs; rewrite firstn_all.
  exact (proj1 (Forall_forall _ _) (proj1 (proj2 (certificate_block fd R l b Hcert Hb)))
    x Huse).
Qed.

Local Lemma strict_selected_use t dst args x :
  In (dst, args) (term_edges t) -> In x (ssa_selected_uses t args) -> In x (term_uses t).
Proof.
  intros Hedge Huse; destruct t as [l actual|c l1 a1 l2 a2|c cases d da|c actual k|y];
    cbn [ssa_selected_uses] in Huse; try exact Huse.
  - exact (ssa_edge_argument_use _ dst args x Hedge Huse).
  - destruct Huse as [<-|Hin]; [left; reflexivity|].
    exact (ssa_edge_argument_use _ dst args x Hedge Hin).
  - destruct Huse as [<-|Hin]; [left; reflexivity|].
    exact (ssa_edge_argument_use _ dst args x Hedge Hin).
Qed.

Local Lemma strict_local_uses ext P f fd R l b e p :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  availability_certificate fd R ->
  ssa_refined_local (first_index (ssa_blocks P f)) l b e p ->
  forall x, In x (srp_uses p) -> In x (strict_available fd R (srp_source p)).
Proof.
  intros Hwf Hf Hb Hcert Hlocal x Huse.
  destruct Hlocal as [|pc i Hnth|c args k Hterm|slot dst args Hedge|y Hterm].
  - contradiction.
  - apply in_map_iff in Huse; destruct Huse as [y [<- Hin]].
    eapply strict_instruction_available; eassumption.
  - apply in_map_iff in Huse; destruct Huse as [y [<- Hin]].
    apply (strict_terminal_available fd R l b y Hcert Hb); rewrite Hterm; exact Hin.
  - unfold ssa_refined_transfer_row in *; cbn [fst snd] in *.
    destruct (bterm b) eqn:Hterm; cbn [srp_uses srp_source] in Huse |- *;
      try solve [apply in_map_iff in Huse; destruct Huse as [y [<- Hin]];
        apply (strict_terminal_available fd R l b y Hcert Hb);
        rewrite Hterm; eapply strict_selected_use;
        [exact (nth_error_In _ slot Hedge)|exact Hin]].
    cbn [srp_uses] in Huse; destruct Huse as [<-|Hfalse]; [|contradiction].
    left; reflexivity.
  - destruct Huse as [<-|Hfalse]; [|contradiction].
    apply (strict_terminal_available fd R l b y Hcert Hb); rewrite Hterm; left; reflexivity.
Qed.

Local Lemma strict_edge_available ext P f fd R e x :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  In e (Graph.out (ssa_refined_graph P f) (Graph.source (ssa_refined_graph P f) e)) ->
  In x (strict_available fd R (Graph.target (ssa_refined_graph P f) e)) ->
  In x (strict_available fd R (Graph.source (ssa_refined_graph P f) e)) \/
    In x (edge_def (point_model (ssa_refined_points P f)) e).
Proof.
  intros Hwf Hf Hcert Hout Havailable.
  destruct (ExamplesSsaViews.ssa_refined_out_local ext P f _ e Hwf Hout)
    as [fd' [l [b [p [Hf' [Hb [Hlocal Hsource]]]]]]].
  rewrite Hf in Hf'; injection Hf' as <-.
  rewrite (proj2 (ExamplesSsaViews.ssa_refined_local_edge ext P f fd l b e p
    Hwf Hf Hb Hlocal)) in Havailable.
  destruct (strict_available_local ext P f fd R l b e p Hwf Hf Hb Hcert Hlocal x
    Havailable) as [Hin|Hin].
  - left; rewrite <- Hsource; exact Hin.
  - right; change (In x (match Map.get ssa_refined_edge_encoding e
      (ssa_refined_index P f) with | Some p => srp_defs p | None => [] end)).
    rewrite (ExamplesSsaViews.ssa_refined_index_complete ext P f fd l b e p
      Hwf Hf Hb Hlocal); exact Hin.
Qed.

Local Lemma strict_path_available ext P f fd R n es m :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  path (ssa_refined_graph P f) n es m ->
  forall x, In x (strict_available fd R m) ->
  In x (strict_available fd R n) \/
    exists e, In e es /\ In x (edge_def (point_model (ssa_refined_points P f)) e).
Proof.
  intros Hwf Hf Hcert Hpath; induction Hpath as [n|e es m Hout Hpath IH]; intros x Hx.
  - left; exact Hx.
  - destruct (IH x Hx) as [Hin|[a [Hin Hdef]]].
    + destruct (strict_edge_available ext P f fd R e x Hwf Hf Hcert Hout Hin)
        as [Hbefore|Hdef].
      * left; exact Hbefore.
      * right; exists e; split; [left; reflexivity|exact Hdef].
    + right; exists a; split; [right; exact Hin|exact Hdef].
Qed.

Local Lemma strict_entry_empty P f fd R n :
  find_func P f = Some fd -> availability_certificate fd R ->
  In n (Graph.entries (ssa_refined_graph P f)) -> strict_available fd R n = [].
Proof.
  intros Hf Hcert Hentry.
  change (In n (map SsaBeforeParams (ssa_entries P f))) in Hentry.
  unfold ssa_entries in Hentry; rewrite Hf in Hentry.
  destruct Hentry as [<-|Hfalse]; [|contradiction].
  cbn [strict_available]; rewrite (proj1 Hcert); reflexivity.
Qed.

Local Lemma strict_point_uses ext P f fd R n x :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  point_use_at (point_model (ssa_refined_points P f)) n x ->
  In x (strict_available fd R n).
Proof.
  intros Hwf Hf Hcert [Hexit|[e [Hout Huse]]].
  - destruct n as [l|l pc|l|l|l]; try contradiction.
    rewrite (proj1 (ssa_refined_exit_agrees ext P f l pc)) in Hexit.
    apply in_map_iff in Hexit; destruct Hexit as [y [<- Huse]].
    destruct (ExamplesSsaViews.ssa_raw_exit_location ext P f (l, pc) y Hwf Huse)
      as [fd' [l' [b [pc' [Hf' [Hb [Heq Hbound]]]]]]].
    injection Heq as <- <-; rewrite Hf in Hf'; injection Hf' as <-.
    destruct (nth_error (bbody b) pc) as [i|] eqn:Hnth;
      [|apply nth_error_None in Hnth; lia].
    assert (Hat : at_instr P (activation_frame f (AState l pc (fun _ => None))) i).
    { exists fd, b; repeat split; assumption. }
    change (In y (ssa_get (pair_encoding nat_encoding nat_encoding) (ssa_exit_index P f)
      [] (l, pc))) in Huse.
    unfold ssa_get in Huse.
    pose proof (ExamplesSsaViews.ssa_exit_instruction ext P f _ i Hwf Hat) as Hexit.
    cbn [alabel apc] in Hexit; rewrite Hexit in Huse.
    destruct (may_trap ssa_effects (AnInstr i)); [|contradiction].
    eapply strict_instruction_available; eassumption.
  - destruct (ExamplesSsaViews.ssa_refined_out_local ext P f n e Hwf Hout)
      as [fd' [l [b [p [Hf' [Hb [Hlocal Hsource]]]]]]].
    rewrite Hf in Hf'; injection Hf' as <-.
    change (In x (match Map.get ssa_refined_edge_encoding e (ssa_refined_index P f) with
      | Some p => srp_uses p | None => [] end)) in Huse.
    rewrite (ExamplesSsaViews.ssa_refined_index_complete ext P f fd l b e p
      Hwf Hf Hb Hlocal) in Huse.
    rewrite <- Hsource; eapply strict_local_uses; eassumption.
Qed.

Local Lemma strict_path_member_out {N E} (g : Graph.t N E) s es n e :
  path g s es n -> In e es -> In e (Graph.out g (Graph.source g e)).
Proof.
  intro Hpath; induction Hpath as [s|a es n Hout Hpath IH]; intro Hin;
    [contradiction|].
  destruct Hin as [<-|Hin]; [exact Hout|apply IH; exact Hin].
Qed.

Local Lemma strict_source_dominance {N E} (g : Graph.t N E) d n :
  reachable g n ->
  (forall s es, In s (Graph.entries g) -> path g s es n ->
    exists e, In e es /\ Graph.source g e = d) ->
  reachable g d /\ strictly_dominates g d n.
Proof.
  intros Hreachable Hsource.
  apply reachable_iff_path in Hreachable; destruct Hreachable as [s [es [Hentry Hpath]]].
  destruct (Hsource s es Hentry Hpath) as [e [Hin Heq]].
  destruct (edge_path_prefix g s es n e Hpath Hin) as [pre [Hpre Hshort]].
  split.
  - apply reachable_iff_path; exists s, pre; split; [exact Hentry|].
    rewrite <- Heq; exact Hpre.
  - split.
    + intros root edges Hroot Hrun.
      destruct (Hsource root edges Hroot Hrun) as [a [Ha Hhome]].
      destruct (ExamplesSsaViews.ssa_path_source_occurs g root edges n a Hrun Ha)
        as [Hstart|[b [Hb Htarget]]].
      * left; rewrite <- Hhome; exact Hstart.
      * right; exists b; split; [exact Hb|rewrite <- Hhome; exact Htarget].
    + intro Hequal; rewrite Hequal in Hsource.
      clear e Hin Heq pre Hpre Hshort.
      remember (length es) as count eqn:Hcount; revert es Hpath Hcount.
      induction count using lt_wf_ind; intros edges Hrun Hcount.
      destruct (Hsource s edges Hentry Hrun) as [a [Ha Hhome]].
      destruct (edge_path_prefix g s edges n a Hrun Ha) as [prefix [Hprefix Hlength]].
      rewrite Hhome in Hprefix.
      exact (H (length prefix) ltac:(lia) prefix Hprefix eq_refl).
Qed.

Local Lemma strict_path_definition ext P f fd R n x root es :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  In x (strict_available fd R n) -> In root (Graph.entries (ssa_refined_graph P f)) ->
  path (ssa_refined_graph P f) root es n ->
  exists e, In e es /\ In x (edge_def (point_model (ssa_refined_points P f)) e).
Proof.
  intros Hwf Hf Hcert Huse Hentry Hpath.
  destruct (strict_path_available ext P f fd R root es n Hwf Hf Hcert Hpath x Huse)
    as [Hstart|Hdef]; [|exact Hdef].
  rewrite (strict_entry_empty P f fd R root Hf Hcert Hentry) in Hstart; contradiction.
Qed.

Local Lemma strict_available_dominates ext P f fd R n x :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  reachable (ssa_refined_graph P f) n -> In x (strict_available fd R n) ->
  exists d, point_definition (ssa_refined_points P f) x = Some d /\
    reachable (ssa_refined_graph P f) d /\ strictly_dominates (ssa_refined_graph P f) d n.
Proof.
  intros Hwf Hf Hcert Hreachable Huse.
  destruct (proj1 (reachable_iff_path _ _) Hreachable) as [root [es [Hentry Hpath]]].
  destruct (strict_path_definition ext P f fd R n x root es Hwf Hf Hcert Huse Hentry Hpath)
    as [e [Hin Hdef]].
  pose proof (strict_outgoing_definition ext P f _ e x Hwf
    (strict_path_member_out _ _ _ _ _ Hpath Hin) Hdef) as Hsite.
  pose proof (proj2 (strict_definition_lookup ext P f x _ Hwf) Hsite) as Hhome.
  exists (Graph.source (ssa_refined_graph P f) e); split; [exact Hhome|].
  apply strict_source_dominance; [exact Hreachable|].
  intros s edges Hstart Hrun.
  destruct (strict_path_definition ext P f fd R n x s edges Hwf Hf Hcert Huse Hstart Hrun)
    as [a [Ha Hdefined]].
  exists a; split; [exact Ha|].
  pose proof (strict_outgoing_definition ext P f _ a x Hwf
    (strict_path_member_out _ _ _ _ _ Hrun Ha) Hdefined) as Hsite'.
  pose proof (proj2 (strict_definition_lookup ext P f x _ Hwf) Hsite') as Hhome'.
  congruence.
Qed.

(** Certified availability and unique static definitions give strict dominance at reachable uses. *)
Theorem ssa_refined_reachable_strict (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_point_ssa (ssa_refined_points P f).
Proof.
  intros Hwf Hfunction; apply in_map_iff in Hfunction.
  destruct Hfunction as [[key fd] [Heq Hmember]]; cbn in Heq; subst key.
  assert (Hf : find_func P f = Some fd) by
    (apply first_index_complete; [exact (proj1 (proj2 Hwf))|exact Hmember]).
  destruct (proj2 (proj2 (proj2 (wf_function ext P f fd Hwf Hf)))) as [R Hcert].
  constructor.
  - exists (SsaBeforeParams (fentry fd)).
    change (map SsaBeforeParams (ssa_entries P f) = [SsaBeforeParams (fentry fd)]).
    unfold ssa_entries; rewrite Hf; reflexivity.
  - intros n x Hreachable Huse.
    apply (strict_available_dominates ext P f fd R n x Hwf Hf Hcert Hreachable).
    exact (strict_point_uses ext P f fd R n x Hwf Hf Hcert Huse).
  - intros n e x Hreachable Hout Hdef.
    apply (proj2 (strict_definition_lookup ext P f x n Hwf)).
    exact (strict_outgoing_definition ext P f n e x Hwf Hout Hdef).
  - intros x d e Hdefinition Hreachable Hout.
    apply (strict_home_kills ext P f x d e Hwf).
    + exact (proj1 (strict_definition_lookup ext P f x d Hwf) Hdefinition).
    + exact Hout.
Qed.

(** * Block homes and constructive frames *)

Local Lemma strict_definition_row_home targets l b x h definition :
  In (x, (h, definition)) (ExamplesSsaViews.ssa_definition_rows targets (l, b)) -> h = l.
Proof.
  unfold ExamplesSsaViews.ssa_definition_rows; cbn [fst snd]; rewrite in_app_iff.
  intros [Hparam|Hbody].
  - apply in_map_iff in Hparam; destruct Hparam as [[slot [y ty]] [Heq Hin]].
    injection Heq as Hx Hhome Hdef; symmetry; exact Hhome.
  - apply in_flat_map in Hbody; destruct Hbody as [i [Hi Hrow]].
    destruct i; cbn [ssa_instruction_rows] in Hrow; try contradiction;
      destruct Hrow as [Heq|Hfalse]; try contradiction; congruence.
Qed.

Local Lemma strict_block_home ext P f fd l b x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  In x (block_defs b) -> home (ssa_block_view ext P f) x = l.
Proof.
  intros Hwf Hf Hb Hdef.
  pose proof (ExamplesSsaViews.ssa_definition_row_keys
    (ExamplesSsaViews.ssa_call_targets P f) (l, b)) as Hkeys.
  cbn [snd] in Hkeys; rewrite <- Hkeys in Hdef.
  apply in_map_iff in Hdef; destruct Hdef as [[y [h definition]] [Heq Hrow]].
  cbn in Heq; subst y.
  pose proof (strict_definition_row_home _ _ _ _ _ _ Hrow) as Hhome; subst h.
  change (fst (ssa_get nat_encoding (ssa_definitions P f) (0, Arbitrary) x) = l).
  unfold ssa_get; rewrite (ExamplesSsaViews.ssa_definition_lookup ext P f x
    (l, definition) Hwf); [reflexivity|].
  apply in_flat_map; exists (l, b); split; [|exact Hrow].
  unfold ssa_blocks; rewrite Hf; apply first_index_sound; exact Hb.
Qed.

Definition strict_block_available (fd : fdef) (R : requirements) (l : label) : list vid :=
  match find_block fd l with
  | Some b => block_defs b ++ required R l
  | None => []
  end.

Local Lemma strict_block_edge_available ext P f fd R e x :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  In e (Graph.out (ssa_block_graph P f) (esrc e)) ->
  In x (strict_block_available fd R (edst e)) ->
  In x (strict_block_available fd R (esrc e)) \/ home (ssa_block_view ext P f) x = edst e.
Proof.
  intros Hwf Hf Hcert Hout Havailable.
  destruct (ExamplesSsaViews.ssa_block_out_member P f (esrc e) e Hout)
    as [b [Hmember Hlocal]].
  unfold ssa_blocks in Hmember; rewrite Hf in Hmember.
  assert (Hb : find_block fd (esrc e) = Some b) by
    (apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
      exact Hmember]).
  destruct (ExamplesSsaViews.ssa_block_edge_target (esrc e) b e Hlocal) as [args Hedge].
  destruct (ExamplesSsaViews.ssa_term_target ext P f fd (esrc e) b (edst e) args
    Hwf Hf Hb Hedge) as [target Htarget].
  unfold strict_block_available in Havailable |- *; rewrite Htarget in Havailable.
  apply in_app_iff in Havailable; destruct Havailable as [Hdef|Hrequired].
  - right; exact (strict_block_home ext P f fd (edst e) target x Hwf Hf Htarget Hdef).
  - left; rewrite Hb; unfold block_defs.
    pose proof (proj2 (proj2 (certificate_block fd R (esrc e) b Hcert Hb))) as Hedges.
    pose proof (proj1 (Forall_forall _ _)
      (proj1 (Forall_forall _ _) Hedges (edst e, args) Hedge) x Hrequired) as Hfinish.
    rewrite !in_app_iff in Hfinish |- *; tauto.
Qed.

Local Lemma strict_block_path_available ext P f fd R n es m x :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  path (ssa_block_graph P f) n es m -> In x (strict_block_available fd R m) ->
  In x (strict_block_available fd R n) \/
    exists e, In e es /\ edst e = home (ssa_block_view ext P f) x.
Proof.
  intros Hwf Hf Hcert Hpath; induction Hpath as [n|e es m Hout Hpath IH]; intro Huse.
  - left; exact Huse.
  - destruct (IH Huse) as [Hin|[a [Ha Hhome]]].
    + destruct (strict_block_edge_available ext P f fd R e x Hwf Hf Hcert Hout Hin)
        as [Hbefore|Hhome].
      * left; exact Hbefore.
      * right; exists e; split; [left; reflexivity|symmetry; exact Hhome].
    + right; exists a; split; [right; exact Ha|exact Hhome].
Qed.

Local Lemma strict_block_available_dominates ext P f fd R l x :
  wf_program ext P -> find_func P f = Some fd -> availability_certificate fd R ->
  In x (strict_block_available fd R l) ->
  dominates (ssa_block_graph P f) (home (ssa_block_view ext P f) x) l.
Proof.
  intros Hwf Hf Hcert Huse root es Hentry Hpath.
  destruct (strict_block_path_available ext P f fd R root es l x Hwf Hf Hcert Hpath Huse)
    as [Hstart|Hdef]; [|right; exact Hdef].
  change (In root (ssa_entries P f)) in Hentry; unfold ssa_entries in Hentry.
  rewrite Hf in Hentry; destruct Hentry as [<-|Hfalse]; [|contradiction].
  destruct (proj1 (wf_function ext P f fd Hwf Hf)) as [b Hb].
  unfold strict_block_available in Hstart; rewrite Hb, (proj1 Hcert), app_nil_r in Hstart.
  left; exact (strict_block_home ext P f fd (fentry fd) b x Hwf Hf Hb Hstart).
Qed.

Local Lemma strict_block_operand ext P f fd R l b pc i x :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  availability_certificate fd R -> nth_error (bbody b) pc = Some i -> In x (instr_uses i) ->
  dominates (ssa_block_graph P f) (home (ssa_block_view ext P f) x) l.
Proof.
  intros Hwf Hf Hb Hcert Hnth Huse.
  apply (strict_block_available_dominates ext P f fd R l x Hwf Hf Hcert).
  unfold strict_block_available; rewrite Hb; unfold block_defs.
  pose proof (proj1 (Forall_forall _ _)
    (body_available_use _ _ _ _ (proj1 (certificate_block fd R l b Hcert Hb)) Hnth)
    x Huse) as Havailable.
  rewrite !in_app_iff in Havailable |- *; destruct Havailable as [Hprefix|Hrest]; [|tauto].
  assert (Hbody : In x (body_defs b)); [|tauto].
  unfold prefix_defs in Hprefix; unfold body_defs.
  apply in_flat_map in Hprefix; destruct Hprefix as [j [Hj Hdef]].
  apply in_flat_map; exists j; split; [|exact Hdef].
  rewrite <- (firstn_skipn pc (bbody b)); apply in_or_app; left; exact Hj.
Qed.

Local Lemma strict_assignment_frame ext P f a i result value x :
  wf_program ext P -> at_instr P (activation_frame f a) i -> In result (instr_def i) ->
  alabel a <> home (ssa_block_view ext P f) x ->
  env_set (aenv a) result value x = aenv a x.
Proof.
  intros Hwf [fd [b [Hf [Hb Hnth]]]] Hdef Haway.
  unfold env_set; destruct (Nat.eq_dec x result) as [->|Hdifferent]; [|reflexivity].
  exfalso; apply Haway; symmetry; apply (strict_block_home ext P f fd (alabel a) b
    result Hwf Hf Hb).
  unfold block_defs, body_defs; apply in_or_app; right; apply in_flat_map.
  exists i; split; [eapply nth_error_In; exact Hnth|exact Hdef].
Qed.

Local Lemma strict_jump_frame ext P f a dst cs env x :
  wf_program ext P -> jump_env P (activation_frame f a) dst cs = Some env ->
  home (ssa_block_view ext P f) x <> dst -> env x = aenv a x.
Proof.
  intros Hwf Hjump Haway; unfold jump_env in Hjump; cbn [activation_frame ffunc] in Hjump.
  destruct (find_func P f) as [fd|] eqn:Hf; [|discriminate].
  destruct (find_block fd dst) as [b|] eqn:Hb; [|discriminate].
  apply (ssa_bind_frame _ _ _ _ _ Hjump); intro Hparam; apply Haway.
  apply (strict_block_home ext P f fd dst b x Hwf Hf Hb).
  unfold block_defs; apply in_or_app; left; exact Hparam.
Qed.

Local Lemma strict_stay_frame ext P f a tr a' x :
  wf_program ext P -> step (activation ext P f) a tr a' ->
  stays (base (ssa_block_view ext P f)) a tr a' ->
  point (base (ssa_block_view ext P f)) a <> home (ssa_block_view ext P f) x ->
  val (ssa_block_view ext P f) a' x = val (ssa_block_view ext P f) a x.
Proof.
  intros Hwf Hstep [Hlabel Hpc] Haway.
  destruct Hstep as
    [a y o args cs v Hat Hread Heval
    |a y n block offset Hat
    |a p Hat
    |a y ty sz p v Hat Htype Hvalid
    |a sz p y Hat
    |a y v Hat Hvalue
    |a dst args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases d da z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c args dst ps r cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a y v Hat Hvalue];
    cbn [ssa_block_view val activation_advance activation_enter aenv apc] in *;
    try reflexivity; try discriminate Hpc.
  all: eapply strict_assignment_frame; [exact Hwf|exact Hat|left; reflexivity|exact Haway].
Qed.

Local Lemma strict_taken_frame ext P f a tr a' e x :
  wf_program ext P -> step (activation ext P f) a tr a' ->
  taken (base (ssa_block_view ext P f)) a tr a' e ->
  home (ssa_block_view ext P f) x <> point (base (ssa_block_view ext P f)) a' ->
  val (ssa_block_view ext P f) a' x = val (ssa_block_view ext P f) a x.
Proof.
  intros Hwf Hstep [fd [b [Hf [Hb [Hpc [Hsource [Htarget [Hzero Hrest]]]]]]]] Haway.
  destruct Hstep as
    [a y o args cs v Hat Hread Heval
    |a y n block offset Hat
    |a p Hat
    |a y ty sz p v Hat Htype Hvalid
    |a sz p y Hat
    |a y v Hat Hvalue
    |a dst args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases d da z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c args dst ps r cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a y v Hat Hvalue];
    cbn [activation_advance activation_enter apc] in Hzero; try discriminate.
  all: eapply strict_jump_frame; [exact Hwf|exact Hbind|exact Haway].
Qed.

Local Lemma strict_guard_home ext P f e cd :
  wf_program ext P -> In e (edges_of (ssa_block_graph P f)) ->
  In cd (edge_guard (ssa_block_view ext P f) e) ->
  dominates (ssa_block_graph P f) (home (ssa_block_view ext P f) (subject cd)) (esrc e).
Proof.
  intros Hwf Hedge Hguard.
  destruct (ExamplesSsaViews.ssa_block_edge_local ext P f e Hwf Hedge)
    as [fd [b [args [Hf [Hb Hnth]]]]].
  destruct e as [src dst slot]; cbn [esrc edst eslot] in *.
  change (In cd (sbp_guard (ssa_get ssa_edge_encoding (ssa_block_payloads P f)
    (SsaBlockPayload [] []) (SsaEdge src dst slot)))) in Hguard.
  rewrite (ExamplesSsaViews.ssa_block_payload_at ext P f fd src b slot dst args
    Hwf Hf Hb Hnth) in Hguard.
  pose proof (ExamplesSsaViews.ssa_guard_subject_used (bterm b) slot cd Hguard) as Huse.
  destruct (proj2 (proj2 (proj2 (wf_function ext P f fd Hwf Hf)))) as [R Hcert].
  apply (strict_block_available_dominates ext P f fd R src (subject cd) Hwf Hf Hcert).
  unfold strict_block_available; rewrite Hb; unfold block_defs.
  pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (certificate_block fd R src b Hcert Hb)))
    (subject cd) Huse) as Hfinish.
  rewrite !in_app_iff in Hfinish |- *; tauto.
Qed.

Local Lemma strict_operation_homes ext P f x o args y :
  wf_program ext P -> def (ssa_block_view ext P f) x = Op o args -> In y args ->
  dominates (ssa_block_graph P f) (home (ssa_block_view ext P f) y)
    (home (ssa_block_view ext P f) x).
Proof.
  intros Hwf Hdef Huse.
  destruct (ExamplesSsaViews.ssa_operation_location ext P f x o args Hwf Hdef)
    as [fd [l [b [pc [Hf [Hb Hnth]]]]]].
  assert (Hhome : home (ssa_block_view ext P f) x = l).
  { apply (strict_block_home ext P f fd l b x Hwf Hf Hb).
    unfold block_defs, body_defs; apply in_or_app; right; apply in_flat_map.
    exists (IOp x o args); split; [exact (nth_error_In _ pc Hnth)|left; reflexivity]. }
  rewrite Hhome.
  destruct (proj2 (proj2 (proj2 (wf_function ext P f fd Hwf Hf)))) as [R Hcert].
  exact (strict_block_operand ext P f fd R l b pc (IOp x o args) y
    Hwf Hf Hb Hcert Hnth Huse).
Qed.

(** A checked source function has constructive frames and operand dominance at block granularity. *)
Theorem ssa_strict_laws (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  strict_ssa_laws (activation ext P f) (ssa_block_view ext P f).
Proof.
  intros Hwf Hfunction; constructor.
  - intros a tr a' x Hreachable Hstep Hstay Hchanged.
    destruct (Nat.eq_dec (alabel a) (home (ssa_block_view ext P f) x)) as [Heq|Haway];
      [exact Heq|exfalso; apply Hchanged].
    exact (strict_stay_frame ext P f a tr a' x Hwf Hstep Hstay Haway).
  - intros a tr a' e x Hreachable Hstep Htaken Hchanged.
    destruct (Nat.eq_dec (home (ssa_block_view ext P f) x) (alabel a')) as [Heq|Haway];
      [exact Heq|exfalso; apply Hchanged].
    exact (strict_taken_frame ext P f a tr a' e x Hwf Hstep Htaken Haway).
  - intros a tr a' x Hreachable Hstep Hstay Haway.
    exact (strict_stay_frame ext P f a tr a' x Hwf Hstep Hstay Haway).
  - intros a tr a' e x Hreachable Hstep Htaken Haway.
    exact (strict_taken_frame ext P f a tr a' e x Hwf Hstep Htaken Haway).
  - intros e cd Hedge Hguard; exact (strict_guard_home ext P f e cd Hwf Hedge Hguard).
  - intros x o args y Hdef Huse; exact (strict_operation_homes ext P f x o args y Hwf Hdef Huse).
Qed.

Local Lemma subtrace_append {A} (xs ys zs ws : list A) :
  subtrace xs ys -> subtrace zs ws -> subtrace (xs ++ zs) (ys ++ ws).
Proof.
  intros Hxy Hzw; induction Hxy as [ys|a xs ys Hxy IH|a xs ys Hxy IH]; cbn.
  - induction ys as [|y ys IH]; [exact Hzw|apply sub_skip; exact IH].
  - apply sub_keep; exact IH.
  - apply sub_skip; exact IH.
Qed.

Definition frame_history ext P (tr : list event) (fr : sframe) : Prop :=
  exists a0 trf, initial (activation ext P (ffunc fr)) a0 /\
    exec (activation ext P (ffunc fr)) a0 trf (frame_state fr) /\ subtrace trf tr.

Local Lemma frame_history_extend ext P tr tail fr :
  frame_history ext P tr fr -> frame_history ext P (tr ++ tail) fr.
Proof.
  intros [a0 [trf [Hinitial [Hrun Hsub]]]]; exists a0, trf; split; [exact Hinitial|].
  split; [exact Hrun|].
  rewrite <- (app_nil_r trf); apply subtrace_append; [exact Hsub|apply sub_nil].
Qed.

Local Lemma frame_history_step ext P tr fr events fr' :
  ffunc fr' = ffunc fr ->
  step (activation ext P (ffunc fr)) (frame_state fr) events (frame_state fr') ->
  frame_history ext P tr fr -> frame_history ext P (tr ++ events) fr'.
Proof.
  intros Hfunction Hstep [a0 [trf [Hinitial [Hrun Hsub]]]].
  unfold frame_history; rewrite Hfunction; exists a0, (trf ++ events).
  split; [exact Hinitial|]; split.
  - eapply exec_app; [exact Hrun|].
    rewrite <- (app_nil_r events); econstructor; [exact Hstep|constructor].
  - apply subtrace_append; [exact Hsub|apply subtrace_refl].
Qed.

Local Lemma frame_return_step ext P fr caller x v env :
  wf_program ext P -> frame_good P fr -> frame_good P caller -> return_link P fr caller ->
  at_term P fr (TRet x) -> fenv fr x = Some v ->
  jump_env P caller (fret caller) [v] = Some env ->
  step (activation ext P (ffunc caller)) (frame_state caller) []
    (frame_state (enter caller (fret caller) env)).
Proof.
  intros Hwf Hfr Hcaller [fd [c [args [cont [ps [Hf [Hcall [Hret Hsig]]]]]]]]
    Hat Hvalue Hbind.
  destruct (wf_terminator ext P fr _ Hwf Hat) as [fd' [Hf' Htyped]].
  rewrite Hf in Hf'; injection Hf' as <-.
  destruct (proj1 Hfr x v Hvalue) as [Htype Hvalid].
  cbn [term_typed] in Htyped; rewrite Htype in Htyped; injection Htyped as Hresult.
  destruct (read_args_exists (fenv caller) (term_uses (TCall c args cont))
    (ssa_term_operands_bound ext P caller _ Hwf (proj2 Hcaller) Hcall)) as [cs Hread].
  rewrite Hret in Hbind |- *.
  eapply ACall; [exact Hcall|exact Hsig|exact Hread| |exact Hvalid|
    exact Hbind].
  exact Hresult.
Qed.

Local Lemma frame_call_initial ext P fr c args cont cs f fd b env :
  wf_program ext P -> frame_good P fr -> at_term P fr (TCall c args cont) ->
  read_args (fenv fr) args = Some cs -> callee_def P (fenv fr) c = Some (f, fd, b) ->
  bind_params (fun _ => None) (bparams b) cs = Some env ->
  initial (activation ext P f) (AState (fentry fd) 0 env).
Proof.
  intros Hwf Hgood Hat Hread Hcall Hbind.
  destruct (call_typed ext P fr c args cont Hwf Hat) as
    [callerfd [ps [r [contb [Hcaller [Hsig [Hcont [Hargs Hparam]]]]]]]].
  destruct (callee_def_target _ _ _ _ _ _ Hcall) as [Hf [Hb Hmatches]].
  destruct (Hmatches _ _ _ Hsig) as [Hps Hr].
  destruct (read_args_typed P _ _ _ _ _ (proj1 Hgood) Hread Hargs) as [Htypes Hvalid].
  exists fd, b, cs, env; repeat split; try assumption; congruence.
Qed.

Local Lemma frame_histories_step ext P lim s events t tr :
  wf_program ext P -> state_good P s -> step (ssa_semantics ext P lim) s events t ->
  Forall (frame_history ext P tr) (stack s) ->
  Forall (frame_history ext P (tr ++ events)) (stack t).
Proof.
  intros Hwf [Hgood Hlinks] Hstep Hhistories.
  destruct Hstep as
    [fr rest m nb x o args cs v Hat Hread Heval
    |fr rest m nb x n z Hat Hvalue Hlimit
    |fr rest m nb p block mb Hat Hpointer Hmemory Hlive
    |fr rest m nb x ty sz p block off mb v Hat Hpointer Hmemory Hload
    |fr rest m nb sz p x block off mb v mb' Hat Hpointer Hvalue Hmemory Hstore
    |fr rest m nb x v Hat Hvalue
    |fr rest m nb dst args cs env Hat Hread Hbind
    |fr rest m nb c l1 a1 l2 a2 z dst args cs env Hat Hcond Hchoice Hread Hbind
    |fr rest m nb c cases d da z dst args cs env Hat Hcond Hchoice Hread Hbind
    |fr rest m nb c args cont cs f fd b env Hat Hread Hcall Hbind Hlimit
    |fr caller rest m nb x v env Hat Hvalue Hbind
    |fr m nb x v Hat Hvalue]; cbn [stack] in *.
  all: inversion Hhistories as [|head tail Hhead Htail]; subst head tail.
  all: inversion Hgood as [|head tail Hfr Hrest]; subst head tail.
  all: try solve [constructor;
    [eapply (frame_history_step ext P tr fr); [reflexivity| |exact Hhead];
      first [solve [eapply AOp; eassumption] |solve [eapply AAlloc; exact Hat] |
        solve [eapply AFree; exact Hat] |
        solve [eapply ALoad; [exact Hat|exact (proj1 (memory_load_typed _ _ _ _ _ Hload))|
          exact (proj2 (memory_load_typed _ _ _ _ _ Hload))]] |
        solve [eapply AStore; exact Hat] |solve [eapply AOutput; eassumption] |
        solve [eapply AJump; eassumption] |solve [eapply ABranch; eassumption] |
        solve [eapply ASwitch; eassumption] |solve [eapply AReturn; eassumption]]
    |apply Forall_forall; intros suspended Hin; apply frame_history_extend;
      exact (proj1 (Forall_forall _ _) Htail suspended Hin)]].
  - constructor.
    + exists (AState (fentry fd) 0 env), []; split.
      * eapply frame_call_initial; eassumption.
      * split; [constructor|apply sub_nil].
    + constructor; [exact (frame_history_extend ext P tr [] fr Hhead)|].
      apply Forall_forall; intros suspended Hin; apply frame_history_extend.
      exact (proj1 (Forall_forall _ _) Htail suspended Hin).
  - inversion Htail as [|head tail Hcaller Hsuspended]; subst head tail.
    inversion Hrest as [|head tail Hcaller_good Hsuspended_good]; subst head tail.
    constructor.
    + eapply (frame_history_step ext P tr caller); [reflexivity| |exact Hcaller].
      eapply (frame_return_step ext P fr caller x v env); try eassumption.
      exact (proj1 Hlinks).
    + apply Forall_forall; intros suspended Hin; apply frame_history_extend.
      exact (proj1 (Forall_forall _ _) Hsuspended suspended Hin).
Qed.

Local Lemma frame_histories_run ext P lim s tr t prefix :
  wf_program ext P -> state_good P s -> exec (ssa_semantics ext P lim) s tr t ->
  Forall (frame_history ext P prefix) (stack s) ->
  Forall (frame_history ext P (prefix ++ tr)) (stack t).
Proof.
  intros Hwf Hgood Hrun; revert prefix Hgood.
  induction Hrun as [s|s events u tail t Hstep Hrun IH]; intros prefix Hgood Hhistories.
  - rewrite app_nil_r; exact Hhistories.
  - rewrite app_assoc; apply IH.
    + exact (step_good ext P lim s events u Hwf Hgood Hstep).
    + exact (frame_histories_step ext P lim s events u prefix Hwf Hgood Hstep Hhistories).
Qed.

(** Every live frame has a reachable activation history whose own events occur in the full run. *)
Theorem activation_lifting (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (s0 s : state) (tr : list event) (i : nat) :
  wf_program ext P -> initial (ssa_semantics ext P lim) s0 ->
  exec (ssa_semantics ext P lim) s0 tr s ->
  forall a f, frame_activation P s i = Some (a, f) ->
    exists a0 trf, initial (activation ext P f) a0 /\ exec (activation ext P f) a0 trf a /\
      subtrace trf tr.
Proof.
  intros Hwf Hinitial Hrun a f Hframe.
  assert (Hhistories : Forall (frame_history ext P []) (stack s0)).
  { destruct Hinitial as [fd [b [cs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]].
    constructor; [|constructor].
    exists (AState (fentry fd) 0 env), []; split.
    - exists fd, b, cs, env; repeat split; assumption.
    - split; [constructor|apply sub_nil]. }
  pose proof (frame_histories_run ext P lim s0 tr s [] Hwf
    (initial_good ext P s0 Hwf Hinitial) Hrun Hhistories) as Hfinal.
  unfold frame_activation in Hframe.
  destruct (nth_error (stack s) i) as [fr|] eqn:Hnth; [|discriminate].
  injection Hframe as <- <-.
  exact (proj1 (Forall_forall _ _) Hfinal fr (nth_error_In _ i Hnth)).
Qed.
