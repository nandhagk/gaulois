(** * Region summaries over structured skeletons

    Bottom-up summaries describe escaping labels, possible completion and tree depth.
    For example, a block containing a jump to depth zero can complete normally.
    Builds on: ViewsSkeleton and ViewsSemantics. *)

From Stdlib Require Import List Bool Arith Lia PeanoNat Recdef.
From Gaulois.Views Require Import ViewsSkeleton ViewsSemantics.
Import List.ListNotations Skeleton.

(** An algebra supplies one summary operation for each statement constructor. *)
Record summary_algebra (A G R : Type) : Type := SummaryAlgebra {
  on_atom : A -> R;
  on_seq : R -> R -> R;
  on_if : G -> R -> R -> R;
  on_block : R -> R;
  on_loop : R -> R;
  on_jump : nat -> R;
  on_jump_if : G -> nat -> R;
  on_jump_table : G -> list nat -> nat -> R
}.

Arguments on_atom {A G R}.
Arguments on_seq {A G R}.
Arguments on_if {A G R}.
Arguments on_block {A G R}.
Arguments on_loop {A G R}.
Arguments on_jump {A G R}.
Arguments on_jump_if {A G R}.
Arguments on_jump_table {A G R}.

(** The fold combines child summaries without changing relative jump depths. *)
Fixpoint summarise {A G R} (alg : summary_algebra A G R) (s : stmt A G) : R :=
  match s with
  | Atom a => on_atom alg a
  | Seq s1 s2 => on_seq alg (summarise alg s1) (summarise alg s2)
  | If g s1 s2 => on_if alg g (summarise alg s1) (summarise alg s2)
  | Block s => on_block alg (summarise alg s)
  | Loop s => on_loop alg (summarise alg s)
  | Jump n => on_jump alg n
  | JumpIf g n => on_jump_if alg g n
  | JumpTable g ns n => on_jump_table alg g ns n
  end.

(** Sound operations preserve the client's chosen meaning at each constructor. *)
Record algebra_sound {A G R} (alg : summary_algebra A G R)
    (meaning : stmt A G -> R -> Prop) : Prop := {
  sound_atom : forall a, meaning (Atom a) (on_atom alg a);
  sound_seq : forall s1 s2 r1 r2,
    meaning s1 r1 -> meaning s2 r2 -> meaning (Seq s1 s2) (on_seq alg r1 r2);
  sound_if : forall g s1 s2 r1 r2,
    meaning s1 r1 -> meaning s2 r2 -> meaning (If g s1 s2) (on_if alg g r1 r2);
  sound_block : forall s r, meaning s r -> meaning (Block s) (on_block alg r);
  sound_loop : forall s r, meaning s r -> meaning (Loop s) (on_loop alg r);
  sound_jump : forall n, meaning (Jump n) (on_jump alg n);
  sound_jump_if : forall g n, meaning (JumpIf g n) (on_jump_if alg g n);
  sound_jump_table : forall g ns n, meaning (JumpTable g ns n) (on_jump_table alg g ns n)
}.

(** An algebra whose rules preserve a meaning has that meaning on every statement. *)
Theorem summarise_sound {A G R} (alg : summary_algebra A G R)
    (meaning : stmt A G -> R -> Prop) :
  algebra_sound alg meaning -> forall s, meaning s (summarise alg s).
Proof.
  intros Hsound s; destruct Hsound; induction s; cbn [summarise]; eauto.
Qed.

(** Crossing a label discards its own jumps and decreases outer relative depths. *)
Fixpoint lower (ns : list nat) : list nat :=
  match ns with
  | [] => []
  | 0 :: ns => lower ns
  | S n :: ns => n :: lower ns
  end.

(** The inventory retains the ordered occurrences of jumps leaving a region. *)
Fixpoint escapes {A G} (s : stmt A G) : list nat :=
  match s with
  | Atom _ => []
  | Seq s1 s2 | If _ s1 s2 => escapes s1 ++ escapes s2
  | Block s | Loop s => lower (escapes s)
  | Jump n | JumpIf _ n => [n]
  | JumpTable _ ns n => n :: ns
  end.

(** Completion conservatively combines atoms, branches and exits from blocks. *)
Fixpoint falls {A G} (ok : A -> bool) (s : stmt A G) : bool :=
  match s with
  | Atom a => ok a
  | Seq s1 s2 => falls ok s1 && falls ok s2
  | If _ s1 s2 => falls ok s1 || falls ok s2
  | Block s => falls ok s || existsb (Nat.eqb 0) (escapes s)
  | Loop _ | Jump _ | JumpTable _ _ _ => false
  | JumpIf _ _ => true
  end.

(** Invalid positions cannot complete. *)
Definition falls_at {A G} (ok : A -> bool) (prog : stmt A G) (p : position) : bool :=
  match sub prog p with
  | Some s => falls ok s
  | None => false
  end.

(** Label depth counts blocks and loops but ignores binary sequencing. *)
Fixpoint nesting {A G} (s : stmt A G) : nat :=
  match s with
  | Seq s1 s2 | If _ s1 s2 => Nat.max (nesting s1) (nesting s2)
  | Block s | Loop s => S (nesting s)
  | _ => 0
  end.

(** Tree depth counts every enclosing structured statement. *)
Fixpoint skel_depth {A G} (s : stmt A G) : nat :=
  match s with
  | Seq s1 s2 | If _ s1 s2 => S (Nat.max (skel_depth s1) (skel_depth s2))
  | Block s | Loop s => S (skel_depth s)
  | _ => 0
  end.

(** Flattening preserves the left-to-right order of all sequence leaves. *)
Fixpoint seq_flat {A G} (s : stmt A G) : list (stmt A G) :=
  match s with
  | Seq s1 s2 => seq_flat s1 ++ seq_flat s2
  | _ => [s]
  end.

Lemma in_lower ns n : In n (lower ns) <-> In (S n) ns.
Proof.
  induction ns as [|[|m] ns IH]; cbn; [tauto|rewrite IH; intuition discriminate|].
  rewrite IH; split; intros [Heq|Hin]; [left; congruence|right; exact Hin|
    left; congruence|right; exact Hin].
Qed.

(** The inventory bounds characterize exactly the syntactic label check. *)
Theorem escapes_labels_ok {A G} (d : nat) (s : stmt A G) :
  labels_ok d s = true <-> (forall n, In n (escapes s) -> n < d).
Proof.
  revert d; induction s as [a|s1 IH1 s2 IH2|g s1 IH1 s2 IH2|s IH|s IH|
    n|g n|g ns n]; intro d; cbn [labels_ok escapes].
  - split; [intros _ n Hin; contradiction|reflexivity].
  - rewrite andb_true_iff, IH1, IH2; setoid_rewrite in_app_iff; firstorder.
  - rewrite andb_true_iff, IH1, IH2; setoid_rewrite in_app_iff; firstorder.
  - rewrite IH; split.
    + intros H n Hin; apply in_lower in Hin; specialize (H (S n) Hin); lia.
    + intros H [|n] Hin; [lia|]; apply in_lower in Hin; specialize (H n Hin); lia.
  - rewrite IH; split.
    + intros H n Hin; apply in_lower in Hin; specialize (H (S n) Hin); lia.
    + intros H [|n] Hin; [lia|]; apply in_lower in Hin; specialize (H n Hin); lia.
  - rewrite Nat.ltb_lt; split;
      [intros H m [<-|[]]; exact H|intros H; apply H; cbn; auto].
  - rewrite Nat.ltb_lt; split;
      [intros H m [<-|[]]; exact H|intros H; apply H; cbn; auto].
  - rewrite andb_true_iff, forallb_forall, Nat.ltb_lt.
    split.
    + intros [Hall Hn] m [<-|Hin]; [exact Hn|apply Nat.ltb_lt; apply Hall; exact Hin].
    + intro H; split;
        [intros m Hin; apply Nat.ltb_lt; apply H; cbn; auto|apply H; cbn; auto].
Qed.

(** Every enclosing label is also an enclosing statement. *)
Theorem nesting_le_skel_depth {A G} (s : stmt A G) : nesting s <= skel_depth s.
Proof.
  induction s; cbn [nesting skel_depth]; lia.
Qed.

Lemma child_depth {A G} (s t : stmt A G) d :
  child s d = Some t -> S (skel_depth t) <= skel_depth s.
Proof.
  destruct s; destruct d; cbn [child skel_depth]; intro Hchild;
    try discriminate; inversion Hchild; subst; cbn [skel_depth]; lia.
Qed.

Lemma sub_length_depth {A G} (s t : stmt A G) p :
  sub s p = Some t -> length p + skel_depth t <= skel_depth s.
Proof.
  revert s; induction p as [|d p IH]; intros s Hsub; cbn [sub] in Hsub.
  - inversion Hsub; subst; cbn; lia.
  - destruct (child s d) as [u|] eqn:Hchild; [|discriminate].
    specialize (IH u Hsub); pose proof (child_depth s u d Hchild); cbn; lia.
Qed.

(** Valid positions have at most one direction per level of tree depth. *)
Theorem position_length_le_depth {A G} (s : stmt A G) (p : position) :
  In p (positions s) -> length p <= skel_depth s.
Proof.
  intro Hin; apply (proj1 (proj2 (positions_exact s) p)) in Hin.
  destruct Hin as [t Hsub]; pose proof (sub_length_depth s t p Hsub); lia.
Qed.

Lemma context_length {A G} (prog : stmt A G) p k :
  context prog p k -> length k = length p.
Proof.
  intro Hctx; induction Hctx; [reflexivity|].
  rewrite length_app; cbn; lia.
Qed.

(** The frame stack never grows past the depth of the program. *)
Theorem frames_bounded {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
  forall m, reachable_state (skeleton_semantics prog C) m ->
    length (stack_of m) <= skel_depth prog.
Proof.
  intros m Hreach; pose proof (reachable_machine_valid prog C m Hreach) as Hctx.
  destruct m as [p k st|p k st]; cbn [machine_valid stack_of] in *;
    rewrite (context_length prog p k Hctx);
    destruct (context_sub prog p k Hctx) as [s Hsub];
    pose proof (sub_length_depth prog s p Hsub); lia.
Qed.

(** * Balanced sequence construction *)

Lemma half_positive n : 2 <= n -> 0 < n / 2.
Proof.
  intro Hn; apply Nat.div_str_pos; lia.
Qed.

Lemma half_smaller n : 0 < n -> n / 2 < n.
Proof.
  intro Hn; apply Nat.div_lt; lia.
Qed.

(** The fallback is used only on empty input; recursive halves of a long list are nonempty. *)
Function balanced {A G} (fallback : stmt A G) (xs : list (stmt A G))
    {measure length xs} : stmt A G :=
  match xs with
  | [] => fallback
  | s :: [] => s
  | s :: t :: rest =>
    Seq (balanced fallback (firstn (length xs / 2) xs))
      (balanced fallback (skipn (length xs / 2) xs))
  end.
Proof.
  - intros; rewrite length_skipn.
    pose proof (half_positive (length (s :: t :: rest)) ltac:(cbn; lia)).
    apply Nat.sub_lt; [apply Nat.lt_le_incl; apply half_smaller; cbn; lia|assumption].
  - intros; rewrite length_firstn.
    eapply Nat.le_lt_trans; [apply Nat.le_min_l|apply half_smaller; cbn; lia].
Defined.

Arguments balanced {A G}.

(** A nonempty list is split into its floor and ceiling halves at every sequence node. *)
Definition seq_of_list {A G} (s : stmt A G) (ss : list (stmt A G)) : stmt A G :=
  balanced s (s :: ss).

Lemma halves_nonempty {T} (xs : list T) :
  2 <= length xs -> firstn (length xs / 2) xs <> [] /\ skipn (length xs / 2) xs <> [].
Proof.
  intro Hlen; pose proof (half_positive (length xs) Hlen) as Hpos.
  pose proof (half_smaller (length xs) ltac:(lia)) as Hlt.
  split; intro Hnil; apply (f_equal (@length T)) in Hnil.
  - rewrite length_firstn in Hnil.
    change (Nat.min (length xs / 2) (length xs) = 0) in Hnil.
    rewrite Nat.min_l in Hnil by lia; lia.
  - rewrite length_skipn in Hnil.
    change (length xs - length xs / 2 = 0) in Hnil; lia.
Qed.

Lemma balanced_flat {A G} (fallback : stmt A G) xs :
  xs <> [] -> seq_flat (balanced fallback xs) = flat_map seq_flat xs.
Proof.
  remember (length xs) as n eqn:Hlen; revert xs Hlen.
  induction n using lt_wf_ind; intros xs Hlen Hnonempty.
  rewrite balanced_equation; destruct xs as [|s [|t rest]].
  - contradiction.
  - cbn [flat_map]; rewrite app_nil_r; reflexivity.
  - change (seq_flat (balanced fallback (firstn (length (s :: t :: rest) / 2)
        (s :: t :: rest))) ++
      seq_flat (balanced fallback (skipn (length (s :: t :: rest) / 2)
        (s :: t :: rest))) = flat_map seq_flat (s :: t :: rest)).
    destruct (halves_nonempty (s :: t :: rest) ltac:(cbn; lia)) as [Hleft Hright].
    rewrite (H (length (firstn (length (s :: t :: rest) / 2) (s :: t :: rest)))).
    2: { rewrite length_firstn; eapply Nat.le_lt_trans;
         [apply Nat.le_min_l|subst n; apply half_smaller; cbn; lia]. }
    2: reflexivity.
    2: exact Hleft.
    rewrite (H (length (skipn (length (s :: t :: rest) / 2) (s :: t :: rest)))).
    2: { rewrite length_skipn; subst n; apply Nat.sub_lt;
         [apply Nat.lt_le_incl; apply half_smaller; cbn; lia|
          apply half_positive; cbn; lia]. }
    2: reflexivity.
    2: exact Hright.
    rewrite <- flat_map_app, firstn_skipn; reflexivity.
Qed.

(** Balanced sequencing keeps every flattened statement in its original order. *)
Theorem seq_of_list_flat {A G} (s : stmt A G) (ss : list (stmt A G)) :
  seq_flat (seq_of_list s ss) = flat_map seq_flat (s :: ss).
Proof.
  apply balanced_flat; discriminate.
Qed.

Lemma half_log_depth n : 2 <= n ->
  S (Nat.log2_up (n / 2)) <= Nat.log2_up n /\
  S (Nat.log2_up (n - n / 2)) <= Nat.log2_up n.
Proof.
  intro Hn; pose proof (half_positive n Hn) as Hhalf.
  pose proof (half_smaller n ltac:(lia)) as Hlt.
  pose proof (Nat.div_mod n 2 ltac:(lia)) as Hdiv.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hmod.
  pose proof (Nat.log2_up_pos n ltac:(lia)) as Hlog.
  pose proof (proj2 (Nat.log2_up_le_pow2 n (Nat.log2_up n) ltac:(lia))
    (Nat.le_refl _)) as Hpow.
  replace (Nat.log2_up n) with (S (Nat.pred (Nat.log2_up n))) in Hpow by lia.
  rewrite Nat.pow_succ_r in Hpow by lia.
  assert (Hceil : n - n / 2 <= 2 ^ Nat.pred (Nat.log2_up n)) by lia.
  apply (proj1 (Nat.log2_up_le_pow2 (n - n / 2) (Nat.pred (Nat.log2_up n))
    ltac:(lia))) in Hceil.
  pose proof (Nat.log2_up_le_mono (n / 2) (n - n / 2) ltac:(lia)).
  lia.
Qed.

Lemma in_halves {T} (xs : list T) n x :
  In x (firstn n xs) \/ In x (skipn n xs) -> In x xs.
Proof.
  intro Hin; rewrite <- (firstn_skipn n xs); apply in_or_app; exact Hin.
Qed.

Lemma maximum_depth_member {A G} (xs : list (stmt A G)) s :
  In s xs -> skel_depth s <= fold_right Nat.max 0 (map skel_depth xs).
Proof.
  induction xs as [|t xs IH]; cbn; [tauto|].
  intros [<-|Hin]; [lia|specialize (IH Hin); lia].
Qed.

Lemma balanced_depth {A G} (fallback : stmt A G) xs :
  xs <> [] -> forall b,
  (forall s, In s xs -> skel_depth s <= b) ->
  skel_depth (balanced fallback xs) <= Nat.log2_up (length xs) + b.
Proof.
  remember (length xs) as n eqn:Hlen; revert xs Hlen.
  induction n using lt_wf_ind; intros xs Hlen Hnonempty b Hbound.
  rewrite balanced_equation; destruct xs as [|s [|t rest]].
  - contradiction.
  - specialize (Hbound s (or_introl eq_refl)); cbn [length Nat.log2_up]; lia.
  - set (xs := s :: t :: rest) in *.
    destruct (halves_nonempty xs ltac:(unfold xs; cbn; lia)) as [Hleft Hright].
    assert (Hfirst : length (firstn (length xs / 2) xs) < n).
    { rewrite length_firstn; eapply Nat.le_lt_trans; [apply Nat.le_min_l|].
      subst n; apply half_smaller; unfold xs; cbn; lia. }
    assert (Hrest : length (skipn (length xs / 2) xs) < n).
    { rewrite length_skipn; subst n; apply Nat.sub_lt;
        [apply Nat.lt_le_incl; apply half_smaller; unfold xs; cbn; lia|
         apply half_positive; unfold xs; cbn; lia]. }
    pose proof (H _ Hfirst _ eq_refl Hleft b
      (fun u Hin => Hbound u (in_halves xs _ u (or_introl Hin)))) as Hdepth1.
    pose proof (H _ Hrest _ eq_refl Hright b
      (fun u Hin => Hbound u (in_halves xs _ u (or_intror Hin)))) as Hdepth2.
    rewrite length_firstn, Nat.min_l in Hdepth1 by
      (apply Nat.lt_le_incl; apply half_smaller; unfold xs; cbn; lia).
    rewrite length_skipn in Hdepth2.
    destruct (half_log_depth (length xs) ltac:(unfold xs; cbn; lia)) as [Hlog1 Hlog2].
    rewrite Hlen.
    change (S (Nat.max (skel_depth (balanced fallback (firstn (length xs / 2) xs)))
      (skel_depth (balanced fallback (skipn (length xs / 2) xs)))) <=
      Nat.log2_up (length xs) + b).
    lia.
Qed.

(** Balanced sequencing adds at most the ceiling logarithm of its length to leaf depth. *)
Theorem seq_of_list_depth {A G} (s : stmt A G) (ss : list (stmt A G)) :
  skel_depth (seq_of_list s ss) <=
  Nat.log2_up (S (length ss)) + fold_right Nat.max 0 (map skel_depth (s :: ss)).
Proof.
  unfold seq_of_list.
  change (skel_depth (balanced s (s :: ss)) <= Nat.log2_up (length (s :: ss)) +
    fold_right Nat.max 0 (map skel_depth (s :: ss))).
  apply balanced_depth; [discriminate|].
  intros t Hin; apply maximum_depth_member; exact Hin.
Qed.

(** * Completion along reachable continuations *)

Lemma zero_escape_block {A G} (ok : A -> bool) (s : stmt A G) :
  In 0 (escapes s) -> falls ok (Block s) = true.
Proof.
  intro Hin; apply orb_true_iff; right; apply existsb_exists.
  exists 0; split; [exact Hin|reflexivity].
Qed.

Lemma resume_completion {A G St} (ok : A -> bool) (prog : stmt A G) p k :
  context prog p k -> forall s n (st : St) m,
  sub prog p = Some s -> In n (escapes s) -> resume n k st = Some m ->
  match m with
  | Go _ _ _ => True
  | Ret q _ _ => falls_at ok prog q = true
  end.
Proof.
  intro Hctx; induction Hctx as [|p k owner d t Hctx IH Howner Hchild];
    intros s n st m Hsub Hin Hresume; [discriminate|].
  rewrite (sub_child prog p owner d Howner), Hchild in Hsub.
  inversion Hsub; subst s.
  destruct owner; destruct d; cbn [child] in Hchild; try discriminate;
    inversion Hchild; subst t; cbn [child_frame resume] in Hresume.
  - eapply IH; [exact Howner|apply in_or_app; left; exact Hin|exact Hresume].
  - eapply IH; [exact Howner|apply in_or_app; right; exact Hin|exact Hresume].
  - eapply IH; [exact Howner|apply in_or_app; left; exact Hin|exact Hresume].
  - eapply IH; [exact Howner|apply in_or_app; right; exact Hin|exact Hresume].
  - destruct n as [|n].
    + inversion Hresume; subst m; unfold falls_at; rewrite Howner.
      apply zero_escape_block; exact Hin.
    + eapply IH; [exact Howner|apply in_lower; exact Hin|exact Hresume].
  - destruct n as [|n].
    + inversion Hresume; exact I.
    + eapply IH; [exact Howner|apply in_lower; exact Hin|exact Hresume].
Qed.

(** A join for the second half of a sequence remembers completion of its first half. *)
Definition frame_ready {A G} (ok : A -> bool) (prog : stmt A G) (f : frame) : Prop :=
  match f with
  | FJoin p => forall s1 s2, sub prog p = Some (Seq s1 s2) -> falls ok s1 = true
  | _ => True
  end.

(** All suspended joins retain the completion history needed when their children return. *)
Definition stack_ready {A G} (ok : A -> bool) (prog : stmt A G) (k : list frame) : Prop :=
  Forall (frame_ready ok prog) k.

(** Returned regions satisfy their completion summary and suspended frames retain their history. *)
Definition completion_valid {A G St} (ok : A -> bool) (prog : stmt A G)
    (m : mstate St) : Prop :=
  stack_ready ok prog (stack_of m) /\
  match m with
  | Go _ _ _ => True
  | Ret p _ _ => falls_at ok prog p = true
  end.

Lemma resume_ready {A G St} (ok : A -> bool) (prog : stmt A G) k n (st : St) m :
  stack_ready ok prog k -> resume n k st = Some m ->
  stack_ready ok prog (stack_of m).
Proof.
  revert n; induction k as [|f k IH]; intros n Hready Hresume; [discriminate|].
  inversion Hready as [|f' k' Hhead Htail]; subst f' k'.
  destruct f; cbn [resume] in Hresume.
  - eapply IH; eassumption.
  - eapply IH; eassumption.
  - destruct n; [inversion Hresume; subst; exact Htail|eapply IH; eassumption].
  - destruct n; [inversion Hresume; subst; exact Hready|eapply IH; eassumption].
Qed.

Lemma return_seq_ready {A G} (ok : A -> bool) (prog : stmt A G) c p k :
  context prog c (FSeq p :: k) -> falls_at ok prog c = true ->
  frame_ready ok prog (FJoin p).
Proof.
  intros Hctx Hfalls s1 s2 Hsub.
  destruct (context_return prog c (FSeq p) k Hctx)
    as [q [d [owner [t [Hpos [Howner [Hchild [Hframe Hparent]]]]]]]].
  destruct owner; destruct d; cbn [child child_frame] in *; try discriminate.
  inversion Hframe; subst q; rewrite Hsub in Howner; inversion Howner; subst.
  unfold falls_at in Hfalls; rewrite (sub_child prog p _ DFirst Hsub) in Hfalls.
  exact Hfalls.
Qed.

Lemma return_join_falls {A G} (ok : A -> bool) (prog : stmt A G) c p k :
  context prog c (FJoin p :: k) -> frame_ready ok prog (FJoin p) ->
  falls_at ok prog c = true -> falls_at ok prog p = true.
Proof.
  intros Hctx Hready Hfalls.
  destruct (context_return prog c (FJoin p) k Hctx)
    as [q [d [owner [t [Hpos [Howner [Hchild [Hframe Hparent]]]]]]]].
  destruct owner; destruct d; cbn [child child_frame] in *; try discriminate;
    inversion Hframe; subst q; subst c; unfold falls_at in *;
    rewrite (sub_child prog p _ _ Howner) in Hfalls;
    cbn [child] in Hfalls;
    rewrite Howner; cbn [falls].
  - apply andb_true_iff; split; [eapply Hready; exact Howner|exact Hfalls].
  - apply orb_true_iff; left; exact Hfalls.
  - apply orb_true_iff; right; exact Hfalls.
Qed.

Lemma return_block_falls {A G} (ok : A -> bool) (prog : stmt A G) c p k :
  context prog c (FBlock p :: k) -> falls_at ok prog c = true ->
  falls_at ok prog p = true.
Proof.
  intros Hctx Hfalls.
  destruct (context_return prog c (FBlock p) k Hctx)
    as [q [d [owner [t [Hpos [Howner [Hchild [Hframe Hparent]]]]]]]].
  destruct owner; destruct d; cbn [child child_frame] in *; try discriminate.
  inversion Hframe; subst q; subst c; unfold falls_at in *.
  rewrite (sub_child prog p _ _ Howner) in Hfalls; cbn [child] in Hfalls.
  rewrite Howner; apply orb_true_iff; left; exact Hfalls.
Qed.

Lemma nth_inventory (ns : list nat) n i : In (nth i ns n) (n :: ns).
Proof.
  revert i; induction ns as [|m ns IH]; intros [|i]; cbn; auto.
  destruct (IH i) as [Heq|Hin]; [left; exact Heq|right; right; exact Hin].
Qed.

Lemma jump_completion_valid {A G St} (ok : A -> bool) (prog : stmt A G) p k s n
    (st : St) m :
  context prog p k -> stack_ready ok prog k -> sub prog p = Some s ->
  In n (escapes s) -> resume n k st = Some m -> completion_valid ok prog m.
Proof.
  intros Hctx Hready Hsub Hin Hresume; split.
  - eapply resume_ready; eassumption.
  - eapply resume_completion; eassumption.
Qed.

Lemma completion_valid_step {A G St O} (ok : A -> bool) (prog : stmt A G)
    (C : skeleton_client A G St O) m l m' :
  (forall a st l st', atom_step C a st l st' -> ok a = true) ->
  machine_valid prog m -> completion_valid ok prog m ->
  skel_step prog C m l m' -> completion_valid ok prog m'.
Proof.
  intros Hatom Hctx [Hready Hcomplete] Hstep.
  destruct Hstep as [p k st a l st' Hsub Hrun|p k st s1 s2 Hsub|
    p k st g s1 s2 b Hsub Hguard|p k st s Hsub|p k st s Hsub|
    p k st n st' m Hsub Heffect Hresume|p k st g n st' m Hsub Hguard Heffect Hresume|
    p k st g n Hsub Hguard|p k st g ns n i st' m Hsub Hguard Heffect Hresume|
    c p k st|c p k st|c p k st|c p k st];
    cbn [machine_valid stack_of] in Hctx, Hready, Hcomplete.
  - split; [exact Hready|unfold falls_at; rewrite Hsub; eapply Hatom; exact Hrun].
  - split; [constructor; [exact I|exact Hready]|exact I].
  - split; [|exact I]; constructor; [|exact Hready].
    intros t1 t2 Hseq; congruence.
  - split; [constructor; [exact I|exact Hready]|exact I].
  - split; [constructor; [exact I|exact Hready]|exact I].
  - eapply jump_completion_valid; eassumption || (cbn; auto).
  - eapply jump_completion_valid; eassumption || (cbn; auto).
  - split; [exact Hready|unfold falls_at; rewrite Hsub; reflexivity].
  - eapply jump_completion_valid; eassumption || apply nth_inventory.
  - inversion Hready as [|f k' Hhead Htail]; subst.
    split; [constructor; [eapply return_seq_ready; eassumption|exact Htail]|exact I].
  - inversion Hready as [|f k' Hhead Htail]; subst.
    split; [exact Htail|eapply return_join_falls; eassumption].
  - inversion Hready as [|f k' Hhead Htail]; subst.
    split; [exact Htail|eapply return_block_falls; eassumption].
  - split; [exact Hready|exact I].
Qed.

Lemma completion_valid_exec {A G St O} (ok : A -> bool) (prog : stmt A G)
    (C : skeleton_client A G St O) m tr m' :
  (forall a st l st', atom_step C a st l st' -> ok a = true) ->
  exec (skeleton_semantics prog C) m tr m' ->
  machine_valid prog m -> completion_valid ok prog m -> completion_valid ok prog m'.
Proof.
  intros Hatom Hrun; induction Hrun as [m|m l m' tr t Hstep Hrun IH];
    intros Hctx Hcomplete.
  - exact Hcomplete.
  - apply IH.
    + exact (machine_valid_step prog C m l m' Hctx Hstep).
    + exact (completion_valid_step ok prog C m l m' Hatom Hctx Hcomplete Hstep).
Qed.

(** Normal completion: a reachable completion of the statement at p implies falls_at. *)
Theorem falls_sound {A G St O} (ok : A -> bool) (prog : stmt A G)
    (C : skeleton_client A G St O) :
  (forall a st l st', atom_step C a st l st' -> ok a = true) ->
  forall p k st, reachable_state (skeleton_semantics prog C) (Ret p k st) ->
    falls_at ok prog p = true.
Proof.
  intros Hatom p k st [m0 [tr [[initial_st [-> Hinit]] Hrun]]].
  assert (Hctx : machine_valid prog (Go [] [] initial_st)) by constructor.
  assert (Hcomplete : completion_valid ok prog (Go [] [] initial_st)).
  { split; [constructor|exact I]. }
  exact (proj2 (completion_valid_exec ok prog C _ _ _ Hatom Hrun Hctx Hcomplete)).
Qed.
