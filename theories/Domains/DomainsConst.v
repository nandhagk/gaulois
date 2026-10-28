(** * Constant word payloads

    Flat constants evaluate known operands and solve invertible constant equations.
    For example, knowing that x + 3 is 7 refines x to 4 modulo its word width.
    Builds on: DomainsNumeric, OrderFlat and Bits word arithmetic. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice OrderFlat.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit.
From Gaulois.Domains Require Import DomainsNumeric.
Import List.ListNotations.

Open Scope Z_scope.

(** Flat constants denote equality, while bottom is empty and top is unrestricted. *)
Definition const_gamma (w : width) (p : flat Z) (z : Z) : Prop :=
  match p with
  | FBot => False
  | FVal c => z = c
  | FTop => True
  end.

(** Flat intersection detects inconsistent known constants. *)
Definition const_meet (a b : flat Z) : flat Z :=
  match a, b with
  | FBot, _ => FBot
  | _, FBot => FBot
  | FTop, _ => b
  | _, FTop => a
  | FVal x, FVal y => if Z.eqb x y then FVal x else FBot
  end.

Lemma const_meet_sound : forall w a b z,
  const_gamma w a z -> const_gamma w b z -> const_gamma w (const_meet a b) z.
Proof.
  intros w [|x|] [|y|] z Ha Hb; cbn in *; try contradiction; try assumption.
  subst x y. now rewrite Z.eqb_refl.
Qed.

Lemma const_meet_lower : forall a b,
  leb (flat_lattice Z.eqb) (const_meet a b) a = true.
Proof.
  intros [|x|] [|y|]; cbn; try reflexivity; try apply Z.eqb_refl.
  destruct (Z.eqb x y); cbn; auto using Z.eqb_refl.
Qed.

Fixpoint const_values (wps : list (width * flat Z)) : option (list word) :=
  match wps with
  | [] => Some []
  | (w, FVal z) :: rest =>
    match const_values rest with
    | Some xs => Some ((w, z) :: xs)
    | None => None
    end
  | _ => None
  end.

Definition const_empty (wp : width * flat Z) : bool :=
  match snd wp with
  | FBot => true
  | _ => false
  end.

Definition const_is (p : flat Z) (z : Z) : bool :=
  match p with
  | FVal c => Z.eqb c z
  | _ => false
  end.

(** Annihilators remain useful even when the other operand is unknown. *)
Definition const_shortcut (o : op) (wps : list (width * flat Z)) : option Z :=
  match wps with
  | [(w, p); (_, q)] =>
    match o with
    | bvmul | bvand => if const_is p 0 || const_is q 0 then Some 0 else None
    | bvor =>
      if const_is p (modulus w - 1) || const_is q (modulus w - 1)
      then Some (modulus w - 1) else None
    | bvshl | bvlshr | bvashr | bvurem => if const_is p 0 then Some 0 else None
    | _ => None
    end
  | _ => None
  end.

(** Known operand lists use the concrete evaluator; unknown operands retain annihilator rules. *)
Definition const_forward (o : op) (wps : list (width * flat Z)) (rw : width) : flat Z :=
  if existsb const_empty wps then FBot else
  match const_values wps with
  | Some ys =>
    match eval_op o ys with
    | Some (_, z) => FVal z
    | None => FBot
    end
  | None =>
    match const_shortcut o wps with
    | Some z => FVal z
    | None => FTop
    end
  end.

(** An unknown inverse operand imposes no additional constant constraint. *)
Definition const_inverse (f : Z -> Z) (p : flat Z) : flat Z :=
  match p with
  | FVal z => FVal (f z)
  | _ => FTop
  end.

(** Every inverse fact is intersected with the old operand fact. *)
Definition const_assume (o : op) (wps : list (width * flat Z)) (rw : width)
  (q : flat Z) : list (flat Z) :=
  match o, wps, q with
  | bveq, [(_, a); (_, b)], FVal r =>
    if Z.eqb r 1 then [const_meet a b; const_meet b a] else map snd wps
  | bvne, [(_, a); (_, b)], FVal r =>
    if Z.eqb r 0 then [const_meet a b; const_meet b a] else map snd wps
  | bvadd, [(w, a); (_, b)], FVal r =>
    [const_meet a (const_inverse (wsub w r) b);
     const_meet b (const_inverse (wsub w r) a)]
  | bvsub, [(w, a); (_, b)], FVal r =>
    [const_meet a (const_inverse (wadd w r) b);
     const_meet b (const_inverse (fun c => wsub w c r) a)]
  | bvxor, [(w, a); (_, b)], FVal r =>
    [const_meet a (const_inverse (wxor w r) b);
     const_meet b (const_inverse (wxor w r) a)]
  | bvnot, [(_, a)], FVal r => [const_meet a (FVal (wnot rw r))]
  | bvneg, [(_, a)], FVal r => [const_meet a (FVal (wneg rw r))]
  | _, _, _ => map snd wps
  end.

(** Constants are width-indexed payloads with the flat integer lattice. *)
Definition const_domain : word_domain (flat Z) :=
  {| plat _ := flat_lattice Z.eqb;
     ptop _ := FTop;
     pconst w z := FVal (wrap w z);
     pforward := const_forward;
     passume := const_assume;
     pmeet _ := const_meet |}.

Lemma const_values_sound : forall wps ys xs,
  Forall2 (payload_sound const_gamma) wps ys -> const_values wps = Some xs -> xs = ys.
Proof.
  intros wps ys xs Hgamma. revert xs.
  induction Hgamma as [|[w [|c|]] [v z] rest tail Hhead Htail IH];
    intros xs Hvalues; cbn in Hvalues; try discriminate.
  - inversion Hvalues. reflexivity.
  - destruct (const_values rest) as [zs|] eqn:Hrest; [|discriminate].
    inversion Hvalues; subst xs. destruct Hhead as [Hwv [Hword Hz]].
    cbn in Hwv, Hz. subst v z. rewrite (IH zs eq_refl). reflexivity.
Qed.

Lemma const_no_empty : forall wps ys, Forall2 (payload_sound const_gamma) wps ys ->
  existsb const_empty wps = false.
Proof.
  intros wps ys Hgamma.
  induction Hgamma as [|[w [|c|]] [v z] rest tail Hhead Htail IH]; cbn; auto.
  destruct Hhead as [_ [_ Hbad]]. exact (False_ind _ Hbad).
Qed.

Lemma const_is_sound : forall w p z c, const_gamma w p z -> const_is p c = true -> z = c.
Proof.
  intros w [|a|] z c Hgamma His; cbn in *; try contradiction; try discriminate.
  apply Z.eqb_eq in His. congruence.
Qed.

Lemma word_zero_ops : forall w y, is_word w y ->
  wmul w 0 y = 0 /\ wand w 0 y = 0 /\ wshl w 0 y = 0 /\
  wlshr w 0 y = 0 /\ washr w 0 y = 0 /\ wurem w 0 y = 0.
Proof.
  intros w y Hword.
  assert (Hmsb : msb w 0 = false) by (unfold msb; rewrite wrap_0; apply Z.bits_0).
  assert (Hsigned : signed w 0 = 0).
  { unfold signed. rewrite wrap_0.
    assert (Hhalf : (0 <? half w) = true) by (apply Z.ltb_lt; apply half_pos).
    now rewrite Hhalf. }
  assert (Hpow : 2 ^ wrap w y <> 0).
  { pose proof (wrap_is_word w y) as [Hnonneg Hupper]. apply Z.pow_nonzero; lia. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - unfold wmul. rewrite Z.mul_0_l. apply wrap_0.
  - unfold wand. rewrite wrap_0. apply Z.land_0_l.
  - unfold wshl. rewrite ?wrap_0, ?Z.mul_0_l, ?wrap_0.
    destruct (Zpos w <=? wrap w y); reflexivity.
  - unfold wlshr. rewrite wrap_0, Z.div_0_l by exact Hpow.
    destruct (Zpos w <=? wrap w y); reflexivity.
  - unfold washr. rewrite Hmsb, Hsigned, Z.div_0_l by exact Hpow.
    rewrite wrap_0. destruct (Zpos w <=? wrap w y); reflexivity.
  - unfold wurem. rewrite wrap_0. destruct (wrap w y =? 0) eqn:Hy; [reflexivity|].
    apply Z.eqb_neq in Hy. now apply Z.mod_0_l.
Qed.

Lemma wor_ones : forall w x, wor w (modulus w - 1) x = modulus w - 1.
Proof.
  intros w x. apply (word_ext w); [apply wor_is_word|apply ones_is_word|].
  intros i Hi. unfold wor. rewrite Z.lor_spec, (wrap_id _ _ (ones_is_word w)).
  rewrite all_ones_bits by exact Hi.
  destruct (i <? Zpos w) eqn:Hlt; cbn; [reflexivity|].
  apply Z.ltb_ge in Hlt. apply (word_bits_high w); [apply wrap_is_word|exact Hlt].
Qed.

Lemma const_either_sound : forall w p q x y c,
  const_gamma w p x -> const_gamma w q y ->
  const_is p c || const_is q c = true -> x = c \/ y = c.
Proof.
  intros w p q x y c Hp Hq Htest. apply orb_true_iff in Htest as [Htest|Htest].
  - left. exact (const_is_sound w p x c Hp Htest).
  - right. exact (const_is_sound w q y c Hq Htest).
Qed.

Lemma word_zero_binary : forall o w x y rw z,
  (o = bvmul \/ o = bvand) -> is_word w x -> is_word w y ->
  (x = 0 \/ y = 0) -> eval_op o [(w, x); (w, y)] = Some (rw, z) -> z = 0.
Proof.
  intros o w x y rw z [-> | ->] Hx Hy Hzero Heval.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvmul w x y wmul eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. destruct Hzero as [-> | ->].
    + exact (proj1 (word_zero_ops w y Hy)).
    + rewrite wmul_comm. exact (proj1 (word_zero_ops w x Hx)).
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvand w x y wand eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. destruct Hzero as [-> | ->].
    + exact (proj1 (proj2 (word_zero_ops w y Hy))).
    + rewrite wand_comm. exact (proj1 (proj2 (word_zero_ops w x Hx))).
Qed.

Lemma word_zero_first : forall o w y rw z,
  (o = bvurem \/ o = bvshl \/ o = bvlshr \/ o = bvashr) -> is_word w y ->
  eval_op o [(w, 0); (w, y)] = Some (rw, z) -> z = 0.
Proof.
  intros o w y rw z Ho Hy Heval.
  destruct (word_zero_ops w y Hy) as [Hmul [Hand [Hshl [Hlshr [Hashr Hrem]]]]].
  destruct Ho as [-> | [-> | [-> | ->]]].
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvurem w 0 y wurem eq_refl)) Heval) as Hr.
    now rewrite Hrem in Hr; inversion Hr.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvshl w 0 y wshl eq_refl)) Heval) as Hr.
    now rewrite Hshl in Hr; inversion Hr.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvlshr w 0 y wlshr eq_refl)) Heval) as Hr.
    now rewrite Hlshr in Hr; inversion Hr.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvashr w 0 y washr eq_refl)) Heval) as Hr.
    now rewrite Hashr in Hr; inversion Hr.
Qed.

Lemma const_shortcut_same_width : forall o w p q x y rw z c,
  is_word w x -> is_word w y -> const_gamma w p x -> const_gamma w q y ->
  eval_op o [(w, x); (w, y)] = Some (rw, z) ->
  const_shortcut o [(w, p); (w, q)] = Some c -> z = c.
Proof.
  intros o w p q x y rw z c Hx Hy Hp Hq Heval Hshortcut.
  destruct o; cbn [const_shortcut] in Hshortcut; try discriminate.
  - destruct (const_is p 0 || const_is q 0) eqn:Htest; [|discriminate].
    inversion Hshortcut; subst c.
    exact (word_zero_binary bvmul w x y rw z ltac:(tauto) Hx Hy
      (const_either_sound w p q x y 0 Hp Hq Htest) Heval).
  - destruct (const_is p 0) eqn:Htest; [|discriminate]. inversion Hshortcut; subst c.
    apply (const_is_sound w p x 0 Hp) in Htest. subst x.
    exact (word_zero_first bvurem w y rw z ltac:(tauto) Hy Heval).
  - destruct (const_is p 0 || const_is q 0) eqn:Htest; [|discriminate].
    inversion Hshortcut; subst c.
    exact (word_zero_binary bvand w x y rw z ltac:(tauto) Hx Hy
      (const_either_sound w p q x y 0 Hp Hq Htest) Heval).
  - destruct (const_is p (modulus w - 1) || const_is q (modulus w - 1)) eqn:Htest;
      [|discriminate]. inversion Hshortcut; subst c.
    pose proof (eq_trans (eq_sym (eval_op_fun2 bvor w x y wor eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z.
    destruct (const_either_sound w p q x y _ Hp Hq Htest) as [-> | ->].
    + apply wor_ones.
    + rewrite wor_comm. apply wor_ones.
  - destruct (const_is p 0) eqn:Htest; [|discriminate]. inversion Hshortcut; subst c.
    apply (const_is_sound w p x 0 Hp) in Htest. subst x.
    exact (word_zero_first bvshl w y rw z ltac:(tauto) Hy Heval).
  - destruct (const_is p 0) eqn:Htest; [|discriminate]. inversion Hshortcut; subst c.
    apply (const_is_sound w p x 0 Hp) in Htest. subst x.
    exact (word_zero_first bvlshr w y rw z ltac:(tauto) Hy Heval).
  - destruct (const_is p 0) eqn:Htest; [|discriminate]. inversion Hshortcut; subst c.
    apply (const_is_sound w p x 0 Hp) in Htest. subst x.
    exact (word_zero_first bvashr w y rw z ltac:(tauto) Hy Heval).
Qed.

Lemma const_shortcut_sound : forall o wps ys rw z c,
  Forall2 (payload_sound const_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  const_shortcut o wps = Some c -> z = c.
Proof.
  intros o wps ys rw z c Hgamma Heval Hshortcut.
  destruct wps as [|[w p] [|[v q] rest]]; try discriminate.
  destruct rest; try discriminate. inversion Hgamma as [|wp y wps' ys' Hp Htail]; subst.
  inversion Htail as [|wp y' wps' ys'' Hq Hnil]; subst. inversion Hnil; subst.
  destruct y as [wy x], y' as [vy y].
  destruct Hp as [Hwx [Hx Hp]], Hq as [Hvy [Hy Hq]]. cbn in Hwx, Hvy, Hp, Hq.
  subst wy vy.
  assert (Hw : w = v).
  { pose proof (eval_op_width o [(w, x); (v, y)] (rw, z) Heval) as Hwidth.
    destruct o; cbn in Hshortcut, Hwidth; try discriminate;
      destruct (Pos.eqb w v) eqn:Hwv; try discriminate; now apply Pos.eqb_eq. }
  subst v. exact (const_shortcut_same_width o w p q x y rw z c Hx Hy Hp Hq Heval Hshortcut).
Qed.

Lemma const_forward_sound : forall o wps ys rw z,
  Forall2 (payload_sound const_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  const_gamma rw (const_forward o wps rw) z.
Proof.
  intros o wps ys rw z Hgamma Heval. unfold const_forward.
  rewrite (const_no_empty wps ys Hgamma).
  destruct (const_values wps) as [xs|] eqn:Hvalues.
  - apply (const_values_sound wps ys xs Hgamma) in Hvalues. subst xs.
    rewrite Heval. reflexivity.
  - destruct (const_shortcut o wps) as [c|] eqn:Hshortcut; [|exact I].
    exact (const_shortcut_sound o wps ys rw z c Hgamma Heval Hshortcut).
Qed.

Lemma wrap_add_left : forall w x y, wrap w (wrap w x + y) = wrap w (x + y).
Proof.
  intros w x y. rewrite (wrap_add w (wrap w x) y), wrap_wrap.
  symmetry. apply wrap_add.
Qed.

Lemma wrap_sub_left : forall w x y, wrap w (wrap w x - y) = wrap w (x - y).
Proof.
  intros w x y. rewrite (wrap_sub w (wrap w x) y), wrap_wrap.
  symmetry. apply wrap_sub.
Qed.

Lemma wrap_sub_right : forall w x y, wrap w (x - wrap w y) = wrap w (x - y).
Proof.
  intros w x y. rewrite (wrap_sub w x (wrap w y)), wrap_wrap.
  symmetry. apply wrap_sub.
Qed.

Lemma const_add_inverse : forall w x y, is_word w x ->
  wsub w (wadd w x y) y = x.
Proof.
  intros w x y Hx. unfold wsub, wadd. rewrite wrap_sub_left.
  replace (x + y - y) with x by ring. now apply wrap_id.
Qed.

Lemma const_sub_inverse_left : forall w x y, is_word w x ->
  wadd w (wsub w x y) y = x.
Proof.
  intros w x y Hx. unfold wsub, wadd. rewrite wrap_add_left.
  replace (x - y + y) with x by ring. now apply wrap_id.
Qed.

Lemma const_sub_inverse_right : forall w x y, is_word w y ->
  wsub w x (wsub w x y) = y.
Proof.
  intros w x y Hy. unfold wsub. rewrite wrap_sub_right.
  replace (x - (x - y)) with y by ring. now apply wrap_id.
Qed.

Lemma const_xor_inverse : forall w x y, is_word w x ->
  wxor w (wxor w x y) y = x.
Proof.
  intros w x y Hx. rewrite <- wxor_assoc, wxor_self.
  unfold wxor. rewrite wrap_0, Z.lxor_0_r. now apply wrap_id.
Qed.

Lemma const_neg_inverse : forall w x, is_word w x -> wneg w (wneg w x) = x.
Proof.
  intros w x Hx. unfold wneg. rewrite wrap_opp.
  replace (- - x) with x by ring. now apply wrap_id.
Qed.

Lemma const_inverse_sound : forall w f p x y,
  const_gamma w p y -> x = f y -> const_gamma w (const_inverse f p) x.
Proof.
  intros w f [|c|] x y Hp Hxy; cbn in *; try contradiction; try exact I.
  now subst y.
Qed.

Lemma const_old_sound : forall wps ys, Forall2 (payload_sound const_gamma) wps ys ->
  Forall2 (fun p y => const_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (map snd wps)) ys.
Proof.
  intros wps ys Hgamma.
  induction Hgamma as [|[w p] y rest tail Hhead Htail IH]; cbn; constructor; [|exact IH].
  exact (proj2 (proj2 Hhead)).
Qed.

Lemma const_old_lower : forall wps : list (width * flat Z),
  Forall2 (fun wp p' => leb (flat_lattice Z.eqb) p' (snd wp) = true) wps (map snd wps).
Proof.
  intro wps. induction wps as [|[w p] rest IH]; cbn; constructor; [|exact IH].
  apply (leb_refl (flat_laws Z.eqb Z.eqb_eq)).
Qed.

Lemma const_assume_lower : forall o wps rw q,
  Forall2 (fun wp p' => leb (flat_lattice Z.eqb) p' (snd wp) = true)
    wps (const_assume o wps rw q).
Proof.
  intros o wps rw q. destruct q as [|r|]; destruct o;
    try solve [apply const_old_lower].
  all: destruct wps as [|[w a] [|[v b] [|wp rest]]];
    cbn [const_assume]; try solve [apply const_old_lower].
  all: try (destruct (r =? 1)); try (destruct (r =? 0));
    try solve [apply const_old_lower].
  all: constructor; [apply const_meet_lower|];
    try (constructor; [apply const_meet_lower|]); constructor.
Qed.

Lemma const_assume_unary_sound : forall o w a x rw z r,
  (o = bvnot \/ o = bvneg) -> is_word w x -> const_gamma w a x ->
  eval_op o [(w, x)] = Some (rw, z) -> z = r ->
  Forall2 (fun p y => const_gamma (fst p) (snd p) (snd y))
    (combine [w] (const_assume o [(w, a)] rw (FVal r))) [(w, x)].
Proof.
  intros o w a x rw z r [-> | ->] Hx Ha Heval <-.
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvnot w x wnot eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. cbn [const_assume combine]. constructor; [|constructor].
    apply const_meet_sound; [exact Ha|]. cbn. symmetry. now apply wnot_involutive.
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvneg w x wneg eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. cbn [const_assume combine]. constructor; [|constructor].
    apply const_meet_sound; [exact Ha|]. cbn. symmetry. now apply const_neg_inverse.
Qed.

Lemma const_assume_binary_sound : forall o w a b x y rw z r,
  (o = bvadd \/ o = bvsub \/ o = bvxor \/ o = bveq \/ o = bvne) ->
  is_word w x -> is_word w y -> const_gamma w a x -> const_gamma w b y ->
  eval_op o [(w, x); (w, y)] = Some (rw, z) -> z = r ->
  Forall2 (fun p y => const_gamma (fst p) (snd p) (snd y))
    (combine [w; w] (const_assume o [(w, a); (w, b)] rw (FVal r))) [(w, x); (w, y)].
Proof.
  intros o w a b x y rw z r Ho Hx Hy Ha Hb Heval <-.
  assert (Hpair : forall a' b', const_gamma w a' x -> const_gamma w b' y ->
    Forall2 (fun p y => const_gamma (fst p) (snd p) (snd y))
      [(w, a'); (w, b')] [(w, x); (w, y)]).
  { intros a' b' Hx' Hy'. constructor; [exact Hx'|]. constructor; [exact Hy'|constructor]. }
  destruct Ho as [-> | [-> | [-> | [-> | ->]]]].
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvadd w x y wadd eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply Hpair; apply const_meet_sound; try assumption.
    + apply (const_inverse_sound w _ b x y Hb). symmetry. now apply const_add_inverse.
    + apply (const_inverse_sound w _ a y x Ha). rewrite wadd_comm.
      symmetry. now apply const_add_inverse.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsub w x y wsub eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply Hpair; apply const_meet_sound; try assumption.
    + apply (const_inverse_sound w _ b x y Hb). symmetry. now apply const_sub_inverse_left.
    + apply (const_inverse_sound w _ a y x Ha). symmetry. now apply const_sub_inverse_right.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvxor w x y wxor eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply Hpair; apply const_meet_sound; try assumption.
    + apply (const_inverse_sound w _ b x y Hb). symmetry. now apply const_xor_inverse.
    + apply (const_inverse_sound w _ a y x Ha). rewrite (wxor_comm w x y).
      symmetry. now apply const_xor_inverse.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bveq w x y _ eq_refl)) Heval) as Hr.
    cbn beta in Hr.
    rewrite (wrap_id w x Hx), (wrap_id w y Hy) in Hr.
    destruct (x =? y) eqn:Hxy; inversion Hr; subst rw z; cbn [const_assume].
    + apply Z.eqb_eq in Hxy. subst y. apply Hpair; apply const_meet_sound; assumption.
    + apply Hpair; assumption.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvne w x y _ eq_refl)) Heval) as Hr.
    cbn beta in Hr.
    rewrite (wrap_id w x Hx), (wrap_id w y Hy) in Hr.
    destruct (x =? y) eqn:Hxy; inversion Hr; subst rw z; cbn [const_assume].
    + apply Z.eqb_eq in Hxy. subst y. apply Hpair; apply const_meet_sound; assumption.
    + apply Hpair; assumption.
Qed.

Lemma const_assume_unary_payload : forall o wps ys rw z r,
  (o = bvnot \/ o = bvneg) -> Forall2 (payload_sound const_gamma) wps ys ->
  eval_op o ys = Some (rw, z) -> z = r ->
  Forall2 (fun p y => const_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (const_assume o wps rw (FVal r))) ys.
Proof.
  intros o wps ys rw z r Ho Hgamma Heval Hr.
  assert (Hlen : length wps = 1%nat).
  { rewrite (Forall2_length Hgamma), (eval_op_arity o ys (rw, z) Heval).
    destruct Ho as [-> | ->]; reflexivity. }
  destruct wps as [|[w a] [|wp rest]]; cbn in Hlen; try discriminate.
  inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
  inversion Htail; subst. destruct y as [v x].
  destruct Hhead as [Hwv [Hx Ha]]. cbn in Hwv, Hx, Ha. subst v.
  exact (const_assume_unary_sound o w a x rw r r Ho Hx Ha Heval eq_refl).
Qed.

Lemma const_assume_binary_payload : forall o wps ys rw z r,
  (o = bvadd \/ o = bvsub \/ o = bvxor \/ o = bveq \/ o = bvne) ->
  Forall2 (payload_sound const_gamma) wps ys -> eval_op o ys = Some (rw, z) -> z = r ->
  Forall2 (fun p y => const_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (const_assume o wps rw (FVal r))) ys.
Proof.
  intros o wps ys rw z r Ho Hgamma Heval Hr.
  assert (Hlen : length wps = 2%nat).
  { rewrite (Forall2_length Hgamma), (eval_op_arity o ys (rw, z) Heval).
    destruct Ho as [-> | [-> | [-> | [-> | ->]]]]; reflexivity. }
  destruct wps as [|[w a] [|[v b] [|wp rest]]]; cbn in Hlen; try discriminate.
  inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
  inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
  destruct y as [wy x], y' as [vy y].
  destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
  cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
  assert (Hwv : w = v).
  { pose proof (eval_op_width o [(w, x); (v, y)] (rw, r) Heval) as Hwidth.
    destruct Ho as [-> | [-> | [-> | [-> | ->]]]]; cbn in Hwidth;
      destruct (Pos.eqb w v) eqn:Hwv; try discriminate; now apply Pos.eqb_eq. }
  subst v. exact (const_assume_binary_sound o w a b x y rw r r Ho Hx Hy Ha Hb Heval eq_refl).
Qed.

Lemma const_assume_sound : forall o wps ys rw z q,
  Forall2 (payload_sound const_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  const_gamma rw q z ->
  Forall2 (fun p y => const_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (const_assume o wps rw q)) ys.
Proof.
  intros o wps ys rw z [|r|] Hgamma Heval Hq; [contradiction| |].
  - destruct o; try solve [apply const_old_sound; exact Hgamma].
    all: first
      [eapply const_assume_unary_payload; [tauto|exact Hgamma|exact Heval|exact Hq]
      |eapply const_assume_binary_payload; [tauto|exact Hgamma|exact Heval|exact Hq]].
  - destruct o; destruct wps as [|[w a] [|[v b] [|wp rest]]];
      apply const_old_sound; exact Hgamma.
Qed.

(** Constants satisfy the complete payload-domain contract. *)
Theorem const_word_laws : word_laws const_domain const_gamma.
Proof.
  constructor.
  - intros w. apply flat_laws. exact Z.eqb_eq.
  - intros w [|a|] [|b|] z Hle Ha; cbn in *;
      try contradiction; try discriminate; try exact I.
    apply Z.eqb_eq in Hle. congruence.
  - intros w z Hgamma. exact Hgamma.
  - intros w z Hword. exact I.
  - intros w z. reflexivity.
  - apply const_forward_sound.
  - apply const_assume_sound.
  - apply const_assume_lower.
  - apply const_meet_sound.
  - intros w. apply const_meet_lower.
Qed.
