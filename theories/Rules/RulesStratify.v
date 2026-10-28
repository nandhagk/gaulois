(** * Predicate levels for stratified negation

    A finite map raises head levels until all positive and negative dependencies hold.
    For example, a rule [p :- !q] requires p to have a level strictly above q.
    Builds on: RulesSyntax, CollectionsMap and CollectionsFinSet. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Rules Require Import RulesSyntax.
Import List.ListNotations.

(** A stratification supplies a level for every predicate and a strict global bound. *)
Record stratification (P : Type) : Type := Stratification {
  level : P -> nat;
  count : nat
}.

Arguments Stratification {P}.
Arguments level {P}.
Arguments count {P}.

(** Positive dependencies do not rise and negative dependencies strictly descend from the head. *)
Definition stratified {P} (prog : program P) (st : stratification P) : Prop :=
  (forall p, level st p < count st) /\
  forall r l, In r (rules prog) -> In l (body r) ->
    match l with
    | LPos a => level st (pred a) <= level st (pred (head r))
    | LNeg a => level st (pred a) < level st (pred (head r))
    end.

(** Dependency edges carry zero for a positive literal and one for a negative literal. *)
Definition rule_edges {P} (r : rule P) : list (P * (P * nat)) :=
  map (fun l => (pred (head r), (pred (lit_atom l),
    match l with LPos _ => 0 | LNeg _ => 1 end))) (body r).

Definition program_edges {P} (prog : program P) : list (P * (P * nat)) :=
  flat_map rule_edges (rules prog).

Definition rule_predicates {P} (r : rule P) : list P :=
  pred (head r) :: map (fun l => pred (lit_atom l)) (body r).

Definition rule_nodes {P} (prog : program P) : list P :=
  FinSet.elements (FinSet.of_list (penc prog) (flat_map rule_predicates (rules prog))).

Lemma rule_nodes_spec {P} (prog : program P) p :
  In p (rule_nodes prog) <-> exists r, In r (rules prog) /\ In p (rule_predicates r).
Proof.
  unfold rule_nodes; rewrite FinSet.elements_spec.
  - rewrite FinSet.of_list_spec, in_flat_map; reflexivity.
  - apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

Lemma edge_nodes {P} (prog : program P) h b w :
  In (h, (b, w)) (program_edges prog) ->
  In h (rule_nodes prog) /\ In b (rule_nodes prog).
Proof.
  unfold program_edges; rewrite in_flat_map.
  intros [r [Hr He]]; unfold rule_edges in He; apply in_map_iff in He.
  destruct He as [l [He Hl]]; injection He as Hh Hb Hw; subst h b.
  split; apply rule_nodes_spec; exists r; split; try exact Hr.
  - now left.
  - right; apply in_map_iff; exists l; auto.
Qed.

Definition level_at {P} (E : encoding P) (m : Map.t P nat) (p : P) : nat :=
  match Map.get E p m with Some n => n | None => 0 end.

Definition edge_ok {P} (E : encoding P) (m : Map.t P nat) (e : P * (P * nat)) :=
  Nat.leb (level_at E m (fst (snd e)) + snd (snd e)) (level_at E m (fst e)).

Definition levels_ok {P} (prog : program P) (m : Map.t P nat) :=
  forallb (edge_ok (penc prog) m) (program_edges prog).

Lemma levels_ok_spec {P} (prog : program P) m :
  levels_ok prog m = true <-> forall h b w,
    In (h, (b, w)) (program_edges prog) ->
    level_at (penc prog) m b + w <= level_at (penc prog) m h.
Proof.
  unfold levels_ok; rewrite forallb_forall; split.
  - intros H h b w Hin; specialize (H _ Hin); apply Nat.leb_le; exact H.
  - intros H [h [b w]] Hin; apply Nat.leb_le; apply H; exact Hin.
Qed.

Definition raise_edge {P} (E : encoding P) (m : Map.t P nat) (e : P * (P * nat)) :=
  Map.set E (fst e)
    (Nat.max (level_at E m (fst e)) (level_at E m (fst (snd e)) + snd (snd e))) m.

Definition raise_pass {P} (E : encoding P) (es : list (P * (P * nat))) m :=
  fold_left (raise_edge E) es m.

Lemma level_set {P} (E : encoding P) m h v p :
  level_at E (Map.set E h v m) p =
    if Pos.eqb (encode E p) (encode E h) then v else level_at E m p.
Proof.
  destruct (Pos.eqb (encode E p) (encode E h)) eqn:Heq.
  - apply Pos.eqb_eq in Heq; apply (encode_injective E) in Heq; subst p.
    unfold level_at; rewrite Map.get_set_same; reflexivity.
  - unfold level_at; rewrite Map.get_set_other; [reflexivity |].
    intro Hsame; subst p; rewrite Pos.eqb_refl in Heq; discriminate.
Qed.

Lemma raise_edge_grows {P} (E : encoding P) m e p :
  level_at E m p <= level_at E (raise_edge E m e) p.
Proof.
  unfold raise_edge; rewrite level_set.
  destruct (Pos.eqb (encode E p) (encode E (fst e))) eqn:Heq; try lia.
  apply Pos.eqb_eq in Heq; apply (encode_injective E) in Heq; subst p; apply Nat.le_max_l.
Qed.

Lemma raise_pass_grows {P} (E : encoding P) es m p :
  level_at E m p <= level_at E (raise_pass E es m) p.
Proof.
  revert m; induction es as [|e es IH]; intro m; cbn [raise_pass fold_left].
  - lia.
  - eapply Nat.le_trans; [apply raise_edge_grows | apply IH].
Qed.

Lemma raise_pass_edge {P} (E : encoding P) es m h b w :
  In (h, (b, w)) es ->
  level_at E m b + w <= level_at E (raise_pass E es m) h.
Proof.
  revert m; induction es as [|[h' [b' w']] es IH]; intros m Hin; cbn in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + injection Heq as Heqh Heqb Heqw; subst h' b' w'.
      change (level_at E m b + w <=
        level_at E (raise_pass E es (raise_edge E m (h, (b, w)))) h).
      eapply Nat.le_trans with (m := level_at E (raise_edge E m (h, (b, w))) h).
      2: apply raise_pass_grows.
      change (level_at E m b + w <= level_at E
        (Map.set E h (Nat.max (level_at E m h) (level_at E m b + w)) m) h).
      rewrite level_set, Pos.eqb_refl.
      apply Nat.le_max_r.
    + specialize (IH (raise_edge E m (h', (b', w'))) Hin).
      change (level_at E m b + w <=
        level_at E (raise_pass E es (raise_edge E m (h', (b', w')))) h).
      pose proof (raise_edge_grows E m (h', (b', w')) b); lia.
Qed.

Lemma raise_pass_bound {P} (E : encoding P) es m (bound : P -> nat) :
  (forall p, level_at E m p <= bound p) ->
  (forall h b w, In (h, (b, w)) es -> bound b + w <= bound h) ->
  forall p, level_at E (raise_pass E es m) p <= bound p.
Proof.
  revert m; induction es as [|[h [b w]] es IH]; intros m Hbound Hedges p.
  - apply Hbound.
  - apply IH.
    + intro q; change (level_at E (Map.set E h
        (Nat.max (level_at E m h) (level_at E m b + w)) m) q <= bound q).
      rewrite level_set.
      destruct (Pos.eqb (encode E q) (encode E h)) eqn:Heq.
      * apply Pos.eqb_eq in Heq; apply (encode_injective E) in Heq; subst q.
        apply Nat.max_lub; [apply Hbound |].
        specialize (Hedges h b w (or_introl eq_refl)); specialize (Hbound b); lia.
      * apply Hbound.
    + intros h' b' w' Hin; apply Hedges; now right.
Qed.

Definition levels_sum {P} (E : encoding P) (ps : list P) m :=
  fold_right (fun p n => level_at E m p + n) 0 ps.

Lemma levels_sum_mono {P} (E : encoding P) ps m m' :
  (forall p, level_at E m p <= level_at E m' p) ->
  levels_sum E ps m <= levels_sum E ps m'.
Proof.
  intro Hle; unfold levels_sum; induction ps as [|p ps IH]; cbn; [lia |].
  specialize (Hle p); lia.
Qed.

Lemma levels_sum_strict {P} (E : encoding P) ps m m' p :
  (forall q, level_at E m q <= level_at E m' q) ->
  In p ps -> level_at E m p < level_at E m' p ->
  levels_sum E ps m < levels_sum E ps m'.
Proof.
  intros Hle Hin Hstrict; induction ps as [|q ps IH]; cbn in Hin; try contradiction.
  change (level_at E m q + levels_sum E ps m < level_at E m' q + levels_sum E ps m').
  destruct Hin as [Heq | Hin].
  - subst q; pose proof (levels_sum_mono E ps m m' Hle); lia.
  - specialize (IH Hin); specialize (Hle q); lia.
Qed.

Lemma forallb_failed {A} (f : A -> bool) xs :
  forallb f xs = false -> exists x, In x xs /\ f x = false.
Proof.
  induction xs as [|x xs IH]; cbn; [discriminate |].
  destruct (f x) eqn:Hx; cbn.
  - intro Hrest; destruct (IH Hrest) as [y [Hin Hy]]; exists y; auto.
  - intros _; exists x; auto.
Qed.

Lemma failed_pass_grows {P} (prog : program P) m : levels_ok prog m = false ->
  levels_sum (penc prog) (rule_nodes prog) m <
  levels_sum (penc prog) (rule_nodes prog) (raise_pass (penc prog) (program_edges prog) m).
Proof.
  intro Hfalse; unfold levels_ok in Hfalse; apply forallb_failed in Hfalse.
  destruct Hfalse as [[h [b w]] [Hin Hbad]].
  apply Nat.leb_gt in Hbad.
  eapply levels_sum_strict with (p := h).
  - apply raise_pass_grows.
  - exact (proj1 (edge_nodes prog h b w Hin)).
  - pose proof (raise_pass_edge (penc prog) (program_edges prog) m h b w Hin); cbn in Hbad; lia.
Qed.

(** Compressing a witness counts occurring predicates at smaller witness levels. *)
Definition level_rank {P} (ps : list P) (f : P -> nat) p :=
  length (filter (fun q => Nat.ltb (f q) (f p)) ps).

Lemma level_rank_mono {P} ps (f : P -> nat) p q :
  f p <= f q -> level_rank ps f p <= level_rank ps f q.
Proof.
  intro Hpq; unfold level_rank; induction ps as [|x ps IH]; cbn [filter length]; [lia |].
  destruct (Nat.ltb (f x) (f p)) eqn:Hp;
    destruct (Nat.ltb (f x) (f q)) eqn:Hq; cbn [length]; try lia.
  apply Nat.ltb_lt in Hp; apply Nat.ltb_ge in Hq; lia.
Qed.

Lemma level_rank_strict {P} ps (f : P -> nat) p q :
  In p ps -> f p < f q -> level_rank ps f p < level_rank ps f q.
Proof.
  intros Hin Hpq; unfold level_rank; induction ps as [|x ps IH]; cbn in Hin; try contradiction.
  destruct Hin as [Heq | Hin].
  - subst x; cbn [filter length]; rewrite Nat.ltb_irrefl.
    assert (Hlt : Nat.ltb (f p) (f q) = true) by (apply Nat.ltb_lt; exact Hpq).
    rewrite Hlt; cbn [length].
    pose proof (level_rank_mono ps f p q (Nat.lt_le_incl _ _ Hpq)) as Hmono.
    unfold level_rank in Hmono; lia.
  - cbn [filter length]; specialize (IH Hin).
    destruct (Nat.ltb (f x) (f p)) eqn:Hp;
      destruct (Nat.ltb (f x) (f q)) eqn:Hq; cbn [length]; try lia.
    apply Nat.ltb_lt in Hp; apply Nat.ltb_ge in Hq; lia.
Qed.

Lemma level_rank_bound {P} ps (f : P -> nat) p :
  In p ps -> level_rank ps f p < length ps.
Proof.
  intro Hin; unfold level_rank.
  assert (Hfilter : forall xs : list P,
    length (filter (fun q => Nat.ltb (f q) (f p)) xs) <= length xs).
  { intro xs; induction xs as [|x xs IH]; cbn [filter length]; [lia |].
    destruct (Nat.ltb (f x) (f p)); cbn [length]; lia. }
  induction ps as [|x ps IH]; cbn in Hin; try contradiction.
  destruct Hin as [Heq | Hin].
  - subst x; cbn [filter length]; rewrite Nat.ltb_irrefl; specialize (Hfilter ps); lia.
  - cbn [filter length]; destruct (Nat.ltb (f x) (f p)); cbn [length];
      specialize (IH Hin); lia.
Qed.

Lemma ranked_edges {P} (prog : program P) st : stratified prog st ->
  forall h b w, In (h, (b, w)) (program_edges prog) ->
  level_rank (rule_nodes prog) (level st) b + w <=
  level_rank (rule_nodes prog) (level st) h.
Proof.
  intros [_ Hstrat] h b w Hin.
  pose proof (proj2 (edge_nodes prog h b w Hin)) as Hb.
  unfold program_edges in Hin; apply in_flat_map in Hin; destruct Hin as [r [Hr He]].
  unfold rule_edges in He; apply in_map_iff in He; destruct He as [l [He Hl]].
  specialize (Hstrat r l Hr Hl); destruct l as [a | a]; injection He as Hh Hb' Hw;
    subst h b w; cbn in Hstrat |- *.
  - rewrite Nat.add_0_r; apply level_rank_mono; exact Hstrat.
  - pose proof (level_rank_strict (rule_nodes prog) (level st) (pred a)
      (pred (head r)) Hb Hstrat); lia.
Qed.

Definition stratify_step {P} (prog : program P) (s : Map.t P nat * bool) :=
  let '(m, done) := s in
  if done then s else if levels_ok prog m then (m, true)
  else (raise_pass (penc prog) (program_edges prog) m, false).

Definition stratify_state {P} (prog : program P) :=
  let n := N.of_nat (length (rule_nodes prog)) in
  N.iter (N.succ (n * n)) (stratify_step prog) (Map.empty, false).

(** The binary iteration budget bounds the total possible strict level increases. *)
Definition stratify {P} (prog : program P) : option (stratification P) :=
  let '(m, done) := stratify_state prog in
  if done then Some (Stratification (level_at (penc prog) m)
    (S (fold_right Nat.max 0 (map (level_at (penc prog) m) (rule_nodes prog)))))
  else None.

Lemma raise_pass_outside {P} (E : encoding P) es m p :
  (forall h b w, In (h, (b, w)) es -> h <> p) ->
  level_at E (raise_pass E es m) p = level_at E m p.
Proof.
  revert m; induction es as [|[h [b w]] es IH]; intros m Hout.
  - reflexivity.
  - change (level_at E (raise_pass E es (raise_edge E m (h, (b, w)))) p = level_at E m p).
    rewrite IH by (intros h' b' w' Hin; apply Hout with b' w'; now right).
    change (level_at E (Map.set E h
      (Nat.max (level_at E m h) (level_at E m b + w)) m) p = level_at E m p).
    rewrite level_set.
    destruct (Pos.eqb (encode E p) (encode E h)) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq; apply (encode_injective E) in Heq.
    exfalso; apply (Hout h b w (or_introl eq_refl)); symmetry; exact Heq.
Qed.

Lemma stratify_state_sound {P} (prog : program P) :
  let '(m, done) := stratify_state prog in
  (done = true -> levels_ok prog m = true) /\
  (forall p, ~ In p (rule_nodes prog) -> level_at (penc prog) m p = 0).
Proof.
  unfold stratify_state; apply N.iter_invariant.
  - intros [m done] [Hdone Hsupport]; unfold stratify_step; destruct done.
    + split; assumption.
    + destruct (levels_ok prog m) eqn:Hok.
      * split; [intros _; exact Hok | exact Hsupport].
      * split; [discriminate |].
        intros p Hout; rewrite raise_pass_outside.
        -- apply Hsupport; exact Hout.
        -- intros h b w Hin Heq; subst h; apply Hout; exact (proj1 (edge_nodes prog p b w Hin)).
  - split; [discriminate | intros p _; unfold level_at; rewrite Map.get_empty; reflexivity].
Qed.

Lemma maximum_member (ns : list nat) n : In n ns -> n <= fold_right Nat.max 0 ns.
Proof.
  induction ns as [|x ns IH]; cbn; intros Hin; [contradiction |].
  destruct Hin as [Heq | Hin].
  - subst x; apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

(** Every successful run returns bounded levels satisfying all rule dependencies. *)
Theorem stratify_sound {P} (prog : program P) (st : stratification P) :
  stratify prog = Some st -> stratified prog st.
Proof.
  unfold stratify; pose proof (stratify_state_sound prog) as Hstate.
  destruct (stratify_state prog) as [m done]; destruct Hstate as [Hdone Hsupport].
  destruct done; [|discriminate]; intro Hsome; injection Hsome as Hst; subst st.
  split.
  - intro p; cbn; destruct (in_dec
      (fun p q => match Pos.eq_dec (encode (penc prog) p) (encode (penc prog) q) with
        | left Heq => left (encode_injective (penc prog) p q Heq)
        | right Hne => right (fun Heq => Hne (f_equal (encode (penc prog)) Heq))
        end) p (rule_nodes prog)) as [Hin | Hout].
    + pose proof (maximum_member (map (level_at (penc prog) m) (rule_nodes prog))
        (level_at (penc prog) m p) (in_map _ _ _ Hin)); lia.
    + rewrite Hsupport by exact Hout; lia.
  - intros r l Hr Hl; specialize (Hdone eq_refl).
    pose proof (proj1 (levels_ok_spec prog m) Hdone) as Hedges.
    assert (Hin : In (pred (head r), (pred (lit_atom l),
      match l with LPos _ => 0 | LNeg _ => 1 end)) (program_edges prog)).
    { apply in_flat_map; exists r; split; [exact Hr |].
      apply in_map_iff; exists l; auto. }
    specialize (Hedges _ _ _ Hin); destruct l; cbn in *; lia.
Qed.

Lemma levels_sum_bound {P} (E : encoding P) ps m B :
  (forall p, In p ps -> level_at E m p <= B) -> levels_sum E ps m <= length ps * B.
Proof.
  intro Hbound; induction ps as [|p ps IH].
  - change (0 <= 0); lia.
  - change (level_at E m p + levels_sum E ps m <= B + length ps * B).
    assert (Hp := Hbound p (or_introl eq_refl)).
    assert (Hrest : levels_sum E ps m <= length ps * B).
    { apply IH; intros q Hin; apply Hbound; now right. }
    lia.
Qed.

Lemma stratify_progress {P} (prog : program P) st : stratified prog st ->
  forall n,
  let '(m, done) := N.iter n (stratify_step prog) (Map.empty, false) in
  (forall p, level_at (penc prog) m p <= level_rank (rule_nodes prog) (level st) p) /\
  (done = false -> N.to_nat n <= levels_sum (penc prog) (rule_nodes prog) m).
Proof.
  intro Hst; apply (N.iter_ind _ (stratify_step prog) (Map.empty, false)
    (fun n s => let '(m, done) := s in
      (forall p, level_at (penc prog) m p <= level_rank (rule_nodes prog) (level st) p) /\
      (done = false -> N.to_nat n <= levels_sum (penc prog) (rule_nodes prog) m))).
  - split.
    + intro p; unfold level_at; rewrite Map.get_empty; lia.
    + cbn; lia.
  - intros n [m done] [Hbound Hprogress]; unfold stratify_step.
    destruct done.
    + split; [exact Hbound | discriminate].
    + destruct (levels_ok prog m) eqn:Hok.
      * split; [exact Hbound | discriminate].
      * split.
        -- apply raise_pass_bound; [exact Hbound | apply ranked_edges; exact Hst].
        -- intros _; specialize (Hprogress eq_refl).
           pose proof (failed_pass_grows prog m Hok); rewrite N2Nat.inj_succ; lia.
Qed.

(** Every stratifiable program reaches a fixpoint within the binary round budget. *)
Theorem stratify_complete {P} (prog : program P) :
  (exists st', stratified prog st') -> exists st'', stratify prog = Some st''.
Proof.
  intros [st Hst]; pose proof (stratify_progress prog st Hst
    (N.succ (N.of_nat (length (rule_nodes prog)) *
      N.of_nat (length (rule_nodes prog))))) as Hprogress.
  change (let '(m, done) := stratify_state prog in
    (forall p, level_at (penc prog) m p <= level_rank (rule_nodes prog) (level st) p) /\
    (done = false -> N.to_nat (N.succ (N.of_nat (length (rule_nodes prog)) *
      N.of_nat (length (rule_nodes prog)))) <=
      levels_sum (penc prog) (rule_nodes prog) m)) in Hprogress.
  unfold stratify; destruct (stratify_state prog) as [m done].
  destruct done.
  - eexists; reflexivity.
  - destruct Hprogress as [Hbound Hprogress]; specialize (Hprogress eq_refl).
    rewrite N2Nat.inj_succ, N2Nat.inj_mul, !Nat2N.id in Hprogress.
    assert (Hsum : levels_sum (penc prog) (rule_nodes prog) m <=
      length (rule_nodes prog) * length (rule_nodes prog)).
    { apply levels_sum_bound; intros p Hin.
      specialize (Hbound p).
      pose proof (level_rank_bound (rule_nodes prog) (level st) p Hin); lia. }
    lia.
Qed.
