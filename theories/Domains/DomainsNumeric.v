(** * Numeric domains and width tags

    Numeric dictionaries describe words and refine expression environments.
    For example, a tagged eight-bit constant retains its width through addition.
    Builds on: Order lattices and concretisations, and Bits expressions. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Bits Require Import BitsWord BitsOp BitsExpr.
Import List.ListNotations Bits.

Local Open Scope nat_scope.

(** Numeric operations share one lattice and one representation of words. *)
Record numeric_domain (A : Type) : Type := NumericDomain {
  lat : lattice A;
  top_at : width -> A;
  of_const : width -> Z -> A;
  forward : op -> list A -> A;
  assume : op -> A -> list A -> list A;
  meet : A -> A -> A
}.

Arguments lat {A}.
Arguments top_at {A}.
Arguments of_const {A}.
Arguments forward {A}.
Arguments assume {A}.
Arguments meet {A}.

(** Numeric laws connect transfers and operand refinement to concrete evaluation. *)
Record numeric_laws {A} (D : numeric_domain A) (G : concretisation A word) : Prop := {
  lat_laws : lattice_laws (lat D);
  gamma_laws : concretisation_laws (lat D) G;
  bot_empty : bottom_empty (lat D) G;
  top_at_sound : forall w z, is_word w z -> gamma G (top_at D w) (w, z);
  of_const_sound : forall w z, gamma G (of_const D w z) (w, wrap w z);
  forward_sound : forall o xs ys r, Forall2 (gamma G) xs ys ->
    eval_op o ys = Some r -> gamma G (forward D o xs) r;
  assume_sound : forall o a xs ys r, Forall2 (gamma G) xs ys ->
    eval_op o ys = Some r -> gamma G a r -> Forall2 (gamma G) (assume D o a xs) ys;
  assume_length : forall o a xs, length (assume D o a xs) = length xs;
  assume_refines : forall o a xs,
    Forall2 (fun x' x => leb (lat D) x' x = true) (assume D o a xs) xs;
  meet_sound : forall a b c, gamma G a c -> gamma G b c -> gamma G (meet D a b) c;
  meet_lower_left : forall a b, leb (lat D) (meet D a b) a = true
}.

Arguments lat_laws {A D G}.
Arguments gamma_laws {A D G}.
Arguments bot_empty {A D G}.
Arguments top_at_sound {A D G}.
Arguments of_const_sound {A D G}.
Arguments forward_sound {A D G}.
Arguments assume_sound {A D G}.
Arguments assume_length {A D G}.
Arguments assume_refines {A D G}.
Arguments meet_sound {A D G}.
Arguments meet_lower_left {A D G}.

(** Abstract evaluation follows the syntax, including nested operand lists. *)
Fixpoint abs_eval {A} (D : numeric_domain A) (env : nat -> A) (e : expr) : A :=
  match e with
  | Var i => env i
  | Const w z => of_const D w z
  | App o args =>
    forward D o ((fix go (es : list expr) : list A :=
      match es with
      | [] => []
      | e :: rest => abs_eval D env e :: go rest
      end) args)
  end.

(** Assumptions refine arguments in order, threading the refined environment. *)
Fixpoint abs_assume {A} (D : numeric_domain A) (env : nat -> A) (e : expr) (a : A) :
  nat -> A :=
  match e with
  | Var i => fun j => if Nat.eqb j i then meet D (env i) a else env j
  | Const _ _ => env
  | App o args =>
    let xs := (fix values (es : list expr) : list A :=
      match es with
      | [] => []
      | e :: rest => abs_eval D env e :: values rest
      end) args in
    (fix go (es : list expr) (qs : list A) (current : nat -> A) : nat -> A :=
      match es, qs with
      | e :: rest, q :: tail => go rest tail (abs_assume D current e q)
      | _, _ => current
      end) args (assume D o a xs) env
  end.

(** Concrete environments contain normalized words. *)
Definition env_ok (cenv : nat -> word) : Prop :=
  forall i, is_word (fst (cenv i)) (snd (cenv i)).

(** Every abstract environment entry describes its concrete counterpart. *)
Definition env_sound {A} (G : concretisation A word) (aenv : nat -> A)
  (cenv : nat -> word) : Prop := forall i, gamma G (aenv i) (cenv i).

(** A variable reads its abstract environment entry. *)
Theorem abs_eval_var : forall {A} (D : numeric_domain A) env i,
  abs_eval D env (Var i) = env i.
Proof.
  reflexivity.
Qed.

(** A constant uses the dictionary's constant abstraction. *)
Theorem abs_eval_const : forall {A} (D : numeric_domain A) env w z,
  abs_eval D env (Const w z) = of_const D w z.
Proof.
  reflexivity.
Qed.

(** An application passes abstract argument values to its forward transfer. *)
Theorem abs_eval_app : forall {A} (D : numeric_domain A) env o args,
  abs_eval D env (App o args) = forward D o (map (abs_eval D env) args).
Proof.
  reflexivity.
Qed.

(** Abstract evaluation describes every successful concrete evaluation. *)
Theorem abs_eval_sound : forall {A} (D : numeric_domain A) G env cenv e r,
  numeric_laws D G -> env_ok cenv -> env_sound G env cenv ->
  eval cenv e = Some r -> gamma G (abs_eval D env e) r.
Proof.
  intros A D G env cenv e. induction e as [i|w z|o args IH];
    intros r laws Hok Henv Heval.
  - cbn in Heval. inversion Heval; subst r.
    rewrite (wrap_id _ _ (Hok i)). rewrite <- surjective_pairing. apply Henv.
  - cbn in Heval. inversion Heval; subst r. apply (of_const_sound laws).
  - rewrite abs_eval_app. rewrite eval_app in Heval.
    destruct (eval_args cenv args) as [ys|] eqn:Hargs; [|discriminate].
    apply (forward_sound laws o _ ys r); [|exact Heval].
    clear Heval. revert ys Hargs. induction IH as [|e He rest Hrest IHrest];
      intros ys Hargs.
    + inversion Hargs. constructor.
    + rewrite eval_args_cons in Hargs.
      destruct (eval cenv e) as [y|] eqn:Heval; [|discriminate].
      destruct (eval_args cenv rest) as [tail|] eqn:Htail; [|discriminate].
      inversion Hargs; subst ys. constructor.
      * exact (He y laws Hok Henv eq_refl).
      * exact (IHrest tail eq_refl).
Qed.

(** Guard refinement preserves the concrete environment satisfying the guard. *)
Theorem abs_assume_sound : forall {A} (D : numeric_domain A) G env cenv e a r,
  numeric_laws D G -> env_ok cenv -> env_sound G env cenv ->
  eval cenv e = Some r -> gamma G a r -> env_sound G (abs_assume D env e a) cenv.
Proof.
  intros A D G env cenv e. revert env.
  induction e as [i|w z|o args IH]; intros env a r laws Hok Henv Heval Ha.
  - cbn in Heval. inversion Heval; subst r.
    rewrite (wrap_id _ _ (Hok i)) in Ha. unfold env_sound. intro j.
    cbn. destruct (Nat.eqb j i) eqn:Hji.
    + apply Nat.eqb_eq in Hji. subst j. apply (meet_sound laws); [apply Henv|].
      rewrite <- surjective_pairing in Ha. exact Ha.
    + apply Henv.
  - exact Henv.
  - change (env_sound G
      ((fix go (es : list expr) (qs : list A) (current : nat -> A) : nat -> A :=
        match es, qs with
        | e :: rest, q :: tail => go rest tail (abs_assume D current e q)
        | _, _ => current
        end) args (assume D o a (map (abs_eval D env) args)) env) cenv).
    rewrite eval_app in Heval.
    destruct (eval_args cenv args) as [ys|] eqn:Hargs; [|discriminate].
    assert (Hvalues : Forall2 (gamma G) (map (abs_eval D env) args) ys).
    { clear IH Ha Heval. revert ys Hargs. induction args as [|e rest IHrest];
        intros ys Hargs.
      - inversion Hargs. constructor.
      - rewrite eval_args_cons in Hargs.
        destruct (eval cenv e) as [y|] eqn:He; [|discriminate].
        destruct (eval_args cenv rest) as [tail|] eqn:Htail; [|discriminate].
        inversion Hargs; subst ys. constructor.
        + eapply abs_eval_sound; eassumption.
        + exact (IHrest tail eq_refl). }
    pose proof (assume_sound laws o a _ ys r Hvalues Heval Ha) as Hqs.
    clear Hvalues Heval Ha.
    remember (assume D o a (map (abs_eval D env) args)) as qs eqn:Hdefinition.
    clear Hdefinition. generalize dependent env. generalize dependent ys. revert qs.
    induction IH as [|e He rest Hrest IHrest]; intros qs ys Hargs Hqs current Hcurrent.
    + exact Hcurrent.
    + rewrite eval_args_cons in Hargs.
      destruct (eval cenv e) as [y|] eqn:Heval; [|discriminate].
      destruct (eval_args cenv rest) as [tail|] eqn:Htail; [|discriminate].
      inversion Hargs; subst ys. inversion Hqs as [|q y' tailq tail' Hq Htailq]; subst.
      cbn. apply (IHrest tailq tail eq_refl Htailq).
      exact (He current q y laws Hok Hcurrent eq_refl Hq).
Qed.

(** Every guard refinement lies below the original environment pointwise. *)
Theorem abs_assume_refines : forall {A} (D : numeric_domain A) G env e a i,
  numeric_laws D G -> leb (lat D) (abs_assume D env e a i) (env i) = true.
Proof.
  intros A D G env e. revert env.
  induction e as [j|w z|o args IH]; intros env a i laws.
  - cbn. destruct (Nat.eqb i j) eqn:Hij.
    + apply Nat.eqb_eq in Hij. subst j. apply (meet_lower_left laws).
    + apply (leb_refl (lat_laws laws)).
  - apply (leb_refl (lat_laws laws)).
  - cbn. generalize (assume D o a
      ((fix values (es : list expr) : list A :=
        match es with
        | [] => []
        | e :: rest => abs_eval D env e :: values rest
        end) args)) as qs.
    generalize dependent env.
    induction IH as [|e He rest Hrest IHrest]; intros env qs.
    + apply (leb_refl (lat_laws laws)).
    + destruct qs as [|q tail].
      * apply (leb_refl (lat_laws laws)).
      * cbn. eapply (leb_trans (lat_laws laws)).
        -- apply (IHrest (abs_assume D env e q) tail).
        -- apply (He env q i laws).
Qed.

(** Payload operations receive widths explicitly and leave width tags to the builder. *)
Record word_domain (P : Type) : Type := WordDomain {
  plat : width -> lattice P;
  ptop : width -> P;
  pconst : width -> Z -> P;
  pforward : op -> list (width * P) -> width -> P;
  passume : op -> list (width * P) -> width -> P -> list P;
  pmeet : width -> P -> P -> P
}.

Arguments plat {P}.
Arguments ptop {P}.
Arguments pconst {P}.
Arguments pforward {P}.
Arguments passume {P}.
Arguments pmeet {P}.

(** A tagged payload describes a normalized concrete word of the same width. *)
Definition payload_sound {P} (G : width -> P -> Z -> Prop) (wp : width * P)
  (y : word) : Prop :=
  fst wp = fst y /\ is_word (fst y) (snd y) /\ G (fst wp) (snd wp) (snd y).

(** Payload laws provide the semantic obligations needed by width tagging. *)
Record word_laws {P} (D : word_domain P) (G : width -> P -> Z -> Prop) : Prop := {
  plat_laws : forall w, lattice_laws (plat D w);
  pgamma_monotone : forall w a b z, leb (plat D w) a b = true -> G w a z -> G w b z;
  pgamma_bot_empty : forall w z, ~ G w (bot (plat D w)) z;
  ptop_sound : forall w z, is_word w z -> G w (ptop D w) z;
  pconst_sound : forall w z, G w (pconst D w z) (wrap w z);
  pforward_sound : forall o wps ys rw z, Forall2 (payload_sound G) wps ys ->
    eval_op o ys = Some (rw, z) -> G rw (pforward D o wps rw) z;
  passume_sound : forall o wps ys rw z q, Forall2 (payload_sound G) wps ys ->
    eval_op o ys = Some (rw, z) -> G rw q z ->
    Forall2 (fun p y => G (fst p) (snd p) (snd y))
      (combine (map fst wps) (passume D o wps rw q)) ys;
  passume_refines : forall o wps rw q,
    Forall2 (fun wp p' => leb (plat D (fst wp)) p' (snd wp) = true)
      wps (passume D o wps rw q);
  pmeet_sound : forall w a b z, G w a z -> G w b z -> G w (pmeet D w a b) z;
  pmeet_lower_left : forall w a b, leb (plat D w) (pmeet D w a b) a = true
}.

Arguments plat_laws {P D G}.
Arguments pgamma_monotone {P D G}.
Arguments pgamma_bot_empty {P D G}.
Arguments ptop_sound {P D G}.
Arguments pconst_sound {P D G}.
Arguments pforward_sound {P D G}.
Arguments passume_sound {P D G}.
Arguments passume_refines {P D G}.
Arguments pmeet_sound {P D G}.
Arguments pmeet_lower_left {P D G}.

(** Tags distinguish impossible values, one known width, and arbitrary words. *)
Inductive tagged (P : Type) : Type :=
  | TBot
  | TVal (w : width) (p : P)
  | TAny.

Arguments TBot {P}.
Arguments TVal {P}.
Arguments TAny {P}.

(** Tagged order never compares payloads at different widths. *)
Definition tagged_lattice {P} (plat : width -> lattice P) : lattice (tagged P) :=
  {| leb a b :=
       match a, b with
       | TBot, _ => true
       | _, TAny => true
       | TVal w p, TVal v q => Pos.eqb w v && leb (plat w) p q
       | _, _ => false
       end;
     bot := TBot;
     join a b :=
       match a, b with
       | TBot, _ => b
       | _, TBot => a
       | TVal w p, TVal v q =>
         if Pos.eqb w v then TVal w (join (plat w) p q) else TAny
       | _, _ => TAny
       end;
     widen a b :=
       match a, b with
       | TBot, _ => b
       | _, TBot => a
       | TVal w p, TVal v q =>
         if Pos.eqb w v then TVal w (widen (plat w) p q) else TAny
       | _, _ => TAny
       end;
     narrow a b :=
       match a, b with
       | TVal w p, TVal v q =>
         if Pos.eqb w v then TVal w (narrow (plat w) p q) else a
       | _, _ => a
       end |}.

(** Payloads ordered below bottom are normalized to the unique tagged bottom. *)
Definition tagged_val {P} (D : word_domain P) (w : width) (p : P) : tagged P :=
  if leb (plat D w) p (bot (plat D w)) then TBot else TVal w p.

(** Tagged meanings require normalized words, except at the unrestricted top. *)
Definition tagged_gamma {P} (G : width -> P -> Z -> Prop) :
  concretisation (tagged P) word :=
  {| gamma t c :=
       match t with
       | TBot => False
       | TVal w p => fst c = w /\ is_word w (snd c) /\ G w p (snd c)
       | TAny => True
       end |}.

(** Tagging preserves the payload lattice laws. *)
Theorem tagged_laws : forall {P} (D : word_domain P),
  (forall w, lattice_laws (plat D w)) -> lattice_laws (tagged_lattice (plat D)).
Proof.
  intros P D laws. constructor.
  - intros [|w p|]; cbn; try reflexivity.
    rewrite Pos.eqb_refl. apply (leb_refl (laws w)).
  - intros [|w p|] [|v q|] [|u r|]; cbn; intros Hab Hbc;
      try discriminate; try reflexivity.
    apply andb_true_iff in Hab as [Hwv Hpq].
    apply andb_true_iff in Hbc as [Hvu Hqr].
    apply Pos.eqb_eq in Hwv. apply Pos.eqb_eq in Hvu. subst v u.
    rewrite Pos.eqb_refl. exact (leb_trans (laws w) p q r Hpq Hqr).
  - intros [|w p|]; reflexivity.
  - intros [|w p|] [|v q|]; cbn; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (laws w)).
    + destruct (Pos.eqb_spec w v); subst; cbn; [|reflexivity].
      rewrite Pos.eqb_refl. apply (join_upper_l (laws v)).
  - intros [|w p|] [|v q|]; cbn; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (laws v)).
    + destruct (Pos.eqb_spec w v); subst; cbn; [|reflexivity].
      rewrite Pos.eqb_refl. apply (join_upper_r (laws v)).
  - intros [|w p|] [|v q|]; cbn; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (laws w)).
    + destruct (Pos.eqb_spec w v); subst; cbn; [|reflexivity].
      rewrite Pos.eqb_refl. apply (widen_upper_l (laws v)).
  - intros [|w p|] [|v q|]; cbn; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (laws v)).
    + destruct (Pos.eqb_spec w v); subst; cbn; [|reflexivity].
      rewrite Pos.eqb_refl. apply (widen_upper_r (laws v)).
  - intros [|w p|] [|v q|]; cbn; intro Hba; try discriminate; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (laws w)).
    + apply andb_true_iff in Hba as [Hvw Hqp].
      apply Pos.eqb_eq in Hvw. subst v. rewrite Pos.eqb_refl. cbn.
      rewrite Pos.eqb_refl. apply (narrow_lower (laws w)). exact Hqp.
  - intros [|w p|] [|v q|]; cbn; intro Hba; try discriminate; try reflexivity.
    apply andb_true_iff in Hba as [Hvw Hqp].
    apply Pos.eqb_eq in Hvw. subst v. rewrite Pos.eqb_refl. cbn.
    rewrite Pos.eqb_refl. apply (narrow_upper (laws w)). exact Hqp.
Qed.

(** A tagged bottom test also detects empty payloads. *)
Definition tagged_empty {P} (D : word_domain P) (t : tagged P) : bool :=
  match t with
  | TBot => true
  | TVal w p => leb (plat D w) p (bot (plat D w))
  | TAny => false
  end.

(** Collecting operands succeeds exactly when every operand has a width tag. *)
Fixpoint tagged_values {P} (xs : list (tagged P)) : option (list (width * P)) :=
  match xs with
  | [] => Some []
  | TVal w p :: rest =>
    match tagged_values rest with
    | Some wps => Some ((w, p) :: wps)
    | None => None
    end
  | _ => None
  end.

(** Refinement retains the original operand when a malformed dictionary omits an entry. *)
Fixpoint tagged_refine {P} (D : word_domain P) (wps : list (width * P)) (qs : list P) :
  list (tagged P) :=
  match wps, qs with
  | (w, p) :: rest, q :: tail => tagged_val D w q :: tagged_refine D rest tail
  | (w, p) :: rest, [] => TVal w p :: tagged_refine D rest []
  | [], _ => []
  end.

(** Forward transfer checks empty operands before collecting their widths. *)
Definition tagged_forward {P} (D : word_domain P) (o : op) (xs : list (tagged P)) :
  tagged P :=
  if existsb (tagged_empty D) xs then TBot else
  match tagged_values xs with
  | Some wps =>
    match result_width o (map fst wps) with
    | Some rw => tagged_val D rw (pforward D o wps rw)
    | None => TBot
    end
  | None => TAny
  end.

(** Backward transfer rejects impossible results and incompatible operand widths. *)
Definition tagged_assume {P} (D : word_domain P) (o : op) (a : tagged P)
  (xs : list (tagged P)) : list (tagged P) :=
  if tagged_empty D a then map (fun _ => TBot) xs else
  match a, tagged_values xs with
  | TVal rw q, Some wps =>
    match result_width o (map fst wps) with
    | Some rw' =>
      if Pos.eqb rw rw' then tagged_refine D wps (passume D o wps rw q)
      else map (fun _ => TBot) xs
    | None => map (fun _ => TBot) xs
    end
  | _, _ => xs
  end.

(** Tagged intersection respects width incompatibility and normalizes empty payloads. *)
Definition tagged_meet {P} (D : word_domain P) (a b : tagged P) : tagged P :=
  match a, b with
  | TBot, _ => TBot
  | _, TBot => TBot
  | TAny, TAny => TAny
  | TAny, TVal w p => tagged_val D w p
  | TVal w p, TAny => tagged_val D w p
  | TVal w p, TVal v q =>
    if Pos.eqb w v then tagged_val D w (pmeet D w p q) else TBot
  end.

(** The builder attaches word widths to every payload operation. *)
Definition tagged_domain {P} (D : word_domain P) : numeric_domain (tagged P) :=
  {| lat := tagged_lattice (plat D);
     top_at w := TVal w (ptop D w);
     of_const w z := TVal w (pconst D w z);
     forward := tagged_forward D;
     assume := tagged_assume D;
     meet := tagged_meet D |}.

Lemma tagged_val_sound : forall {P} (D : word_domain P) G,
  word_laws D G -> forall w p z, is_word w z -> G w p z ->
  gamma (tagged_gamma G) (tagged_val D w p) (w, z).
Proof.
  intros P D G laws w p z Hword Hp. unfold tagged_val.
  destruct (leb (plat D w) p (bot (plat D w))) eqn:Hbot; cbn.
  - exfalso. apply (pgamma_bot_empty laws w z).
    exact (pgamma_monotone laws w p _ z Hbot Hp).
  - auto.
Qed.

Lemma tagged_val_lower : forall {P} (D : word_domain P) w p q,
  leb (plat D w) p q = true ->
  leb (tagged_lattice (plat D)) (tagged_val D w p) (TVal w q) = true.
Proof.
  intros P D w p q Hpq. unfold tagged_val.
  destruct (leb (plat D w) p (bot (plat D w))); cbn; [reflexivity|].
  now rewrite Pos.eqb_refl.
Qed.

Lemma tagged_empty_false : forall {P} (D : word_domain P) G,
  word_laws D G -> forall t c, gamma (tagged_gamma G) t c -> tagged_empty D t = false.
Proof.
  intros P D G laws [|w p|] [v z] Hgamma; cbn in *; try contradiction; [|reflexivity].
  destruct Hgamma as [Hvw [Hword Hp]]. subst v.
  destruct (leb (plat D w) p (bot (plat D w))) eqn:Hbot; [|reflexivity].
  exfalso. apply (pgamma_bot_empty laws w z).
  exact (pgamma_monotone laws w p _ z Hbot Hp).
Qed.

Lemma tagged_values_rebuild : forall {P} (xs : list (tagged P)) wps,
  tagged_values xs = Some wps -> xs = map (fun wp => TVal (fst wp) (snd wp)) wps.
Proof.
  intros P xs. induction xs as [|[|w p|] rest IH]; intros wps Hvalues;
    cbn in Hvalues; try discriminate.
  - inversion Hvalues. reflexivity.
  - destruct (tagged_values rest) as [tail|] eqn:Htail; [|discriminate].
    inversion Hvalues; subst wps. cbn. f_equal. apply IH. reflexivity.
Qed.

Lemma tagged_values_sound : forall {P} G xs ys wps,
  Forall2 (gamma (tagged_gamma G)) xs ys -> tagged_values xs = Some wps ->
  Forall2 (@payload_sound P G) wps ys.
Proof.
  intros P G xs ys wps Hgamma. revert wps.
  induction Hgamma as [|[|w p|] [v z] rest tail Hhead Htail IH];
    intros wps Hvalues; cbn in Hvalues; try discriminate.
  - inversion Hvalues. constructor.
  - destruct (tagged_values rest) as [wps'|] eqn:Hrest; [|discriminate].
    inversion Hvalues; subst wps. constructor; [|apply IH; reflexivity].
    cbn in Hhead. destruct Hhead as [Hvw Hmeaning]. cbn.
    split; [symmetry; exact Hvw|]. now subst v.
Qed.

Lemma payload_widths : forall {P} G wps ys,
  Forall2 (@payload_sound P G) wps ys -> map fst wps = map fst ys.
Proof.
  intros P G wps ys Hgamma. induction Hgamma as [|wp y rest tail Hhead Htail IH].
  - reflexivity.
  - cbn. destruct Hhead as [Hwidth _]. now rewrite Hwidth, IH.
Qed.

Lemma tagged_no_empty : forall {P} (D : word_domain P) G,
  word_laws D G -> forall xs ys, Forall2 (gamma (tagged_gamma G)) xs ys ->
  existsb (tagged_empty D) xs = false.
Proof.
  intros P D G laws xs ys Hgamma.
  induction Hgamma as [|x y rest tail Hhead Htail IH]; cbn; [reflexivity|].
  rewrite (tagged_empty_false D G laws x y Hhead), IH. reflexivity.
Qed.

Lemma tagged_forward_sound : forall {P} (D : word_domain P) G,
  word_laws D G -> forall o xs ys r, Forall2 (gamma (tagged_gamma G)) xs ys ->
  eval_op o ys = Some r -> gamma (tagged_gamma G) (tagged_forward D o xs) r.
Proof.
  intros P D G laws o xs ys [rw z] Hgamma Heval.
  unfold tagged_forward. rewrite (tagged_no_empty D G laws xs ys Hgamma).
  destruct (tagged_values xs) as [wps|] eqn:Hvalues; [|exact I].
  pose proof (tagged_values_sound G xs ys wps Hgamma Hvalues) as Hpayload.
  rewrite (payload_widths G wps ys Hpayload).
  rewrite (eval_op_width o ys (rw, z) Heval). cbn.
  apply (tagged_val_sound D G laws).
  - exact (eval_op_is_word o ys (rw, z) Heval).
  - exact (pforward_sound laws o wps ys rw z Hpayload Heval).
Qed.

Lemma tagged_refine_sound : forall {P} (D : word_domain P) G,
  word_laws D G -> forall wps ys qs, Forall2 (payload_sound G) wps ys ->
  Forall2 (fun p y => G (fst p) (snd p) (snd y)) (combine (map fst wps) qs) ys ->
  Forall2 (gamma (tagged_gamma G)) (tagged_refine D wps qs) ys.
Proof.
  intros P D G laws wps ys qs Hpayload. revert qs.
  induction Hpayload as [|[w p] [v z] rest tail Hhead Htail IH]; intros qs Hqs.
  - destruct qs; constructor.
  - destruct qs as [|q qs]; cbn in Hqs; [inversion Hqs|].
    inversion Hqs as [|wp y rest' tail' Hq Hrest]; subst.
    cbn. constructor; [|now apply IH].
    destruct Hhead as [Hwv [Hword Hp]]. cbn in Hwv, Hword, Hq. subst v.
    now apply (tagged_val_sound D G laws).
Qed.

Lemma tagged_refine_lower : forall {P} (D : word_domain P) wps qs,
  Forall2 (fun wp p' => leb (plat D (fst wp)) p' (snd wp) = true) wps qs ->
  Forall2 (fun x' x => leb (tagged_lattice (plat D)) x' x = true)
    (tagged_refine D wps qs) (map (fun wp => TVal (fst wp) (snd wp)) wps).
Proof.
  intros P D wps qs Hrefine.
  induction Hrefine as [|[w p] q rest tail Hhead Htail IH]; cbn; constructor.
  - now apply tagged_val_lower.
  - exact IH.
Qed.

Lemma tagged_refine_length : forall {P} (D : word_domain P) wps qs,
  length (tagged_refine D wps qs) = length wps.
Proof.
  intros P D wps. induction wps as [|[w p] rest IH]; intros [|q qs]; cbn; auto.
Qed.

Lemma tagged_assume_sound : forall {P} (D : word_domain P) G,
  word_laws D G -> forall o a xs ys r, Forall2 (gamma (tagged_gamma G)) xs ys ->
  eval_op o ys = Some r -> gamma (tagged_gamma G) a r ->
  Forall2 (gamma (tagged_gamma G)) (tagged_assume D o a xs) ys.
Proof.
  intros P D G laws o a xs ys [rw z] Hgamma Heval Ha.
  unfold tagged_assume. rewrite (tagged_empty_false D G laws a (rw, z) Ha).
  destruct a as [|aw q|]; [contradiction| |exact Hgamma].
  destruct (tagged_values xs) as [wps|] eqn:Hvalues; [|exact Hgamma].
  pose proof (tagged_values_sound G xs ys wps Hgamma Hvalues) as Hpayload.
  rewrite (payload_widths G wps ys Hpayload), (eval_op_width o ys (rw, z) Heval).
  cbn in Ha. destruct Ha as [Hwidth [Hword Hq]]. subst aw.
  rewrite Pos.eqb_refl. apply (tagged_refine_sound D G laws wps ys _ Hpayload).
  exact (passume_sound laws o wps ys rw z q Hpayload Heval Hq).
Qed.

Lemma tagged_assume_lower : forall {P} (D : word_domain P) G,
  word_laws D G -> forall o a xs,
  Forall2 (fun x' x => leb (tagged_lattice (plat D)) x' x = true)
    (tagged_assume D o a xs) xs.
Proof.
  intros P D G laws o a xs.
  assert (Hbottom : Forall2 (fun x' x => leb (tagged_lattice (plat D)) x' x = true)
    (map (fun _ => TBot) xs) xs).
  { induction xs; cbn; constructor; auto. }
  assert (Hsame : Forall2 (fun x' x => leb (tagged_lattice (plat D)) x' x = true) xs xs).
  { clear Hbottom. induction xs; constructor;
      [apply (leb_refl (tagged_laws D (plat_laws laws)))|auto]. }
  unfold tagged_assume. destruct (tagged_empty D a); [exact Hbottom|].
  destruct a as [|rw q|]; try exact Hsame.
  destruct (tagged_values xs) as [wps|] eqn:Hvalues; [|exact Hsame].
  destruct (result_width o (map fst wps)) as [rw'|]; [|exact Hbottom].
  destruct (Pos.eqb rw rw'); [|exact Hbottom].
  rewrite (tagged_values_rebuild xs wps Hvalues).
  apply tagged_refine_lower. apply (passume_refines laws).
Qed.

Lemma tagged_assume_length : forall {P} (D : word_domain P) o a xs,
  length (tagged_assume D o a xs) = length xs.
Proof.
  intros P D o a xs. unfold tagged_assume.
  destruct (tagged_empty D a); [apply length_map|].
  destruct a as [|rw q|]; try reflexivity.
  destruct (tagged_values xs) as [wps|] eqn:Hvalues; [|reflexivity].
  destruct (result_width o (map fst wps)) as [rw'|]; [|apply length_map].
  destruct (Pos.eqb rw rw'); [|apply length_map].
  rewrite tagged_refine_length, (tagged_values_rebuild xs wps Hvalues), length_map.
  reflexivity.
Qed.

Lemma tagged_meet_sound : forall {P} (D : word_domain P) G,
  word_laws D G -> forall a b c, gamma (tagged_gamma G) a c ->
  gamma (tagged_gamma G) b c -> gamma (tagged_gamma G) (tagged_meet D a b) c.
Proof.
  intros P D G laws [|w p|] [|v q|] [u z] Ha Hb;
    cbn in Ha, Hb; try contradiction; cbn [tagged_meet]; try exact I.
  - destruct Ha as [Huw [Hword Hp]]. destruct Hb as [Huv [_ Hq]]. subst u v.
    rewrite Pos.eqb_refl. apply (tagged_val_sound D G laws); [exact Hword|].
    now apply (pmeet_sound laws).
  - destruct Ha as [Huw [Hword Hp]]. subst u. now apply (tagged_val_sound D G laws).
  - destruct Hb as [Huv [Hword Hq]]. subst u. now apply (tagged_val_sound D G laws).
Qed.

Lemma tagged_meet_lower : forall {P} (D : word_domain P) G,
  word_laws D G -> forall a b,
  leb (tagged_lattice (plat D)) (tagged_meet D a b) a = true.
Proof.
  intros P D G laws [|w p|] [|v q|]; cbn [tagged_meet]; try reflexivity.
  - destruct (Pos.eqb w v); [|reflexivity].
    apply tagged_val_lower. apply (pmeet_lower_left laws).
  - apply tagged_val_lower. apply (leb_refl (plat_laws laws w)).
  - unfold tagged_val. destruct (leb (plat D v) q (bot (plat D v))); reflexivity.
Qed.

(** Every sound payload dictionary lifts to a sound numeric dictionary. *)
Theorem tagged_numeric_laws : forall {P} (D : word_domain P) G,
  word_laws D G -> numeric_laws (tagged_domain D) (tagged_gamma G).
Proof.
  intros P D G laws. constructor.
  - apply tagged_laws. apply (plat_laws laws).
  - constructor. intros [|w p|] [|v q|] [u z] Hle Ha;
      cbn in Hle, Ha |- *; try contradiction; try discriminate; try exact I.
    apply andb_true_iff in Hle as [Hwv Hpq]. apply Pos.eqb_eq in Hwv. subst v.
    destruct Ha as [Huw [Hword Hp]]. split; [exact Huw|]. split; [exact Hword|].
    exact (pgamma_monotone laws w p q z Hpq Hp).
  - constructor. intros c Hgamma. exact Hgamma.
  - intros w z Hword. cbn. split; [reflexivity|]. split; [exact Hword|].
    now apply (ptop_sound laws).
  - intros w z. cbn. split; [reflexivity|].
    split; [apply wrap_is_word|apply (pconst_sound laws)].
  - apply (tagged_forward_sound D G laws).
  - apply (tagged_assume_sound D G laws).
  - apply tagged_assume_length.
  - apply (tagged_assume_lower D G laws).
  - apply (tagged_meet_sound D G laws).
  - apply (tagged_meet_lower D G laws).
Qed.

(** A cap constrains only values that carry a specific width. *)
Definition width_ok {P} (maxw : width) (t : tagged P) : Prop :=
  match t with
  | TVal w _ => (w <= maxw)%positive
  | _ => True
  end.

(** Capped values carry an erased proof of their width bound. *)
Definition capped {P} (maxw : width) : Type := { t : tagged P | width_ok maxw t }.

Lemma tagged_join_width : forall {P} (L : width -> lattice P) maxw a b,
  width_ok maxw a -> width_ok maxw b -> width_ok maxw (join (tagged_lattice L) a b).
Proof.
  intros P L maxw [|w p|] [|v q|] Ha Hb; cbn in *; try exact I; try assumption.
  destruct (Pos.eqb w v); cbn; auto.
Qed.

Lemma tagged_widen_width : forall {P} (L : width -> lattice P) maxw a b,
  width_ok maxw a -> width_ok maxw b -> width_ok maxw (widen (tagged_lattice L) a b).
Proof.
  intros P L maxw [|w p|] [|v q|] Ha Hb; cbn in *; try exact I; try assumption.
  destruct (Pos.eqb w v); cbn; auto.
Qed.

Lemma tagged_narrow_width : forall {P} (L : width -> lattice P) maxw a b,
  width_ok maxw a -> width_ok maxw (narrow (tagged_lattice L) a b).
Proof.
  intros P L maxw [|w p|] [|v q|] Ha; cbn in *; try exact I; try assumption.
  destruct (Pos.eqb w v); exact Ha.
Qed.

(** Lattice operations preserve the cap without changing their underlying tags. *)
Definition capped_lattice {P} (maxw : width) (plat : width -> lattice P) :
  lattice (@capped P maxw) :=
  {| leb a b := leb (tagged_lattice plat) (proj1_sig a) (proj1_sig b);
     bot := exist _ TBot I;
     join a b := exist _ (join (tagged_lattice plat) (proj1_sig a) (proj1_sig b))
       (tagged_join_width plat maxw _ _ (proj2_sig a) (proj2_sig b));
     widen a b := exist _ (widen (tagged_lattice plat) (proj1_sig a) (proj1_sig b))
       (tagged_widen_width plat maxw _ _ (proj2_sig a) (proj2_sig b));
     narrow a b := exist _ (narrow (tagged_lattice plat) (proj1_sig a) (proj1_sig b))
       (tagged_narrow_width plat maxw _ _ (proj2_sig a)) |}.

(** Restricting the tagged carrier preserves all weak lattice laws. *)
Theorem capped_laws : forall {P} (D : word_domain P),
  (forall w, lattice_laws (plat D w)) -> forall maxw : width,
  lattice_laws (capped_lattice maxw (plat D)).
Proof.
  intros P D laws maxw. pose proof (tagged_laws D laws) as taggedlaws. constructor; cbn.
  - intros a. apply (leb_refl taggedlaws).
  - intros a b c. apply (leb_trans taggedlaws).
  - intros a. reflexivity.
  - intros a b. apply (join_upper_l taggedlaws).
  - intros a b. apply (join_upper_r taggedlaws).
  - intros a b. apply (widen_upper_l taggedlaws).
  - intros a b. apply (widen_upper_r taggedlaws).
  - intros a b. apply (narrow_lower taggedlaws).
  - intros a b. apply (narrow_upper taggedlaws).
Qed.

(** The finite maximum is used only by erased termination proofs. *)
Definition width_max (f : width -> nat) (maxw : width) : nat :=
  fold_right Nat.max 0 (map (fun n => f (Pos.of_nat n)) (seq 1 (Pos.to_nat maxw))).

Lemma fold_max_member : forall xs x, In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  intros xs x Hin. induction xs as [|y rest IH]; cbn in *; [contradiction|].
  destruct Hin as [<-|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma width_max_bound : forall f maxw w, (w <= maxw)%positive -> f w <= width_max f maxw.
Proof.
  intros f maxw w Hwidth. apply fold_max_member. apply in_map_iff.
  exists (Pos.to_nat w). split; [now rewrite Pos2Nat.id|].
  apply in_seq. split.
  - pose proof (Pos2Nat.is_pos w). lia.
  - apply Pos2Nat.inj_le in Hwidth. lia.
Qed.

(** Capped height counts bottom, the payload height, and the unrestricted top separately. *)
Definition capped_height {P} (D : word_domain P) (maxw : width)
  (laws : forall w, lattice_laws (plat D w))
  (H : forall w, monotone_height (plat D w)) : monotone_height (capped_lattice maxw (plat D)).
Proof.
  set (M := width_max (fun w => bound (base_height (H w))) maxw).
  set (r := fun t : @capped P maxw =>
    match proj1_sig t with
    | TBot => 0
    | TVal w p => S (rank (base_height (H w)) p)
    | TAny => S (S M)
    end).
  assert (Hbound : forall w p, (w <= maxw)%positive ->
    rank (base_height (H w)) p <= M).
  { intros w p Hwidth. eapply Nat.le_trans; [apply rank_bounded|].
    exact (width_max_bound (fun v => bound (base_height (H v))) maxw w Hwidth). }
  unshelve refine (@MonotoneHeight _ _ (@Height _ _ r (S (S M)) _ _) _).
  - unfold r. intros [[|w p|] Hwidth]; cbn [proj1_sig]; try lia.
    specialize (Hbound w p Hwidth). lia.
  - unfold r. intros [[|w p|] Hwidth] [[|v q|] Hwidth'];
      cbn [capped_lattice tagged_lattice proj1_sig leb join]; try discriminate.
    + lia.
    + lia.
    + rewrite Pos.eqb_refl, (leb_refl (laws w)). discriminate.
    + destruct (Pos.eqb_spec w v); subst; cbn [proj1_sig].
      * rewrite Pos.eqb_refl. intro Hstrict.
        exact (proj1 (Nat.succ_lt_mono _ _) (join_rank_grows (base_height (H v)) p q Hstrict)).
      * intros _. specialize (Hbound w p Hwidth). lia.
    + intros _. specialize (Hbound w p Hwidth). lia.
  - cbn [rank]. unfold r. intros [[|w p|] Hwidth] [[|v q|] Hwidth'];
      cbn [capped_lattice tagged_lattice proj1_sig leb]; try discriminate; try lia.
    + rewrite andb_true_iff. intros [Hwv Hpq]. apply Pos.eqb_eq in Hwv. subst v.
      pose proof (rank_monotone (H w) p q Hpq). lia.
    + intros _. specialize (Hbound w p Hwidth). lia.
Defined.

(** Capped widening ranks add one level at a payload and two above the finite maximum at bottom. *)
Definition capped_wrank {P} (D : word_domain P) (maxw : width)
  (W : forall w, bounded_widening_rank (plat D w)) :
  bounded_widening_rank (capped_lattice maxw (plat D)).
Proof.
  set (M := width_max (fun w => wbound (W w)) maxw).
  set (r := fun t : @capped P maxw =>
    match proj1_sig t with
    | TBot => S (S M)
    | TVal w p => S (wrank (base_wrank (W w)) p)
    | TAny => 0
    end).
  assert (Hbound : forall w p, (w <= maxw)%positive ->
    wrank (base_wrank (W w)) p <= M).
  { intros w p Hwidth. eapply Nat.le_trans; [apply wrank_bounded|].
    exact (width_max_bound (fun v => wbound (W v)) maxw w Hwidth). }
  unshelve refine (@BoundedWideningRank _ _ (@WideningRank _ _ r _ _) (S (S M)) _).
  - unfold r. intros [[|w p|] Hwidth] [[|v q|] Hwidth'];
      cbn [capped_lattice tagged_lattice proj1_sig leb widen];
      try discriminate; try lia.
    destruct (Pos.eqb_spec v w); subst; cbn [proj1_sig]; [|discriminate].
    rewrite Pos.eqb_refl. intro Hpq.
    pose proof (widen_rank_stable (base_wrank (W w)) p q Hpq). lia.
  - unfold r. intros [[|w p|] Hwidth] [[|v q|] Hwidth'];
      cbn [capped_lattice tagged_lattice proj1_sig leb widen];
      try discriminate; try lia.
    + intros _. specialize (Hbound v q Hwidth'). lia.
    + destruct (Pos.eqb_spec v w); subst; cbn [proj1_sig].
      * rewrite Pos.eqb_refl. intro Hpq.
        pose proof (widen_rank_progress (base_wrank (W w)) p q Hpq). lia.
      * assert (Hwv : Pos.eqb w v = false) by (apply Pos.eqb_neq; congruence).
        rewrite Hwv. cbn. lia.
  - cbn [wrank]. unfold r. intros [[|w p|] Hwidth]; cbn [proj1_sig]; try lia.
    specialize (Hbound w p Hwidth). lia.
Defined.

Lemma width_le_dec : forall w v : width, {(w <= v)%positive} + {~ (w <= v)%positive}.
Proof.
  intros w v. destruct (Pos.leb w v) eqn:Hle.
  - left. now apply Pos.leb_le.
  - right. intro Hwidth. apply Pos.leb_le in Hwidth. congruence.
Defined.

(** Clamping preserves in-range tags and widens an excessive width to the unrestricted top. *)
Definition clamp {P} (maxw : width) (t : tagged P) : @capped P maxw.
Proof.
  destruct t as [|w p|].
  - exact (exist _ TBot I).
  - destruct (width_le_dec w maxw) as [Hwidth|Hwidth].
    + exact (exist _ (TVal w p) Hwidth).
    + exact (exist _ TAny I).
  - exact (exist _ TAny I).
Defined.

(** The capped meaning observes only the underlying tagged value. *)
Definition capped_gamma {P} (G : width -> P -> Z -> Prop) (maxw : width) :
  concretisation (@capped P maxw) word := comap_gamma (@proj1_sig _ _) (tagged_gamma G).

Lemma clamp_within : forall {P} maxw (t : tagged P),
  width_ok maxw t -> proj1_sig (clamp maxw t) = t.
Proof.
  intros P maxw [|w p|] Hwidth; cbn; try reflexivity.
  destruct (width_le_dec w maxw) as [Hle|Hle]; [reflexivity|].
  exfalso. exact (Hle Hwidth).
Qed.

Lemma clamp_lower : forall {P} L maxw (a : tagged P) (b : @capped P maxw),
  leb (tagged_lattice L) a (proj1_sig b) = true ->
  leb (capped_lattice maxw L) (clamp maxw a) b = true.
Proof.
  intros P L maxw [|w p|] [[|v q|] Hwidth] Hle;
    cbn in Hle; try discriminate; try reflexivity.
  - apply andb_true_iff in Hle as [Hwv Hpq]. apply Pos.eqb_eq in Hwv. subst v.
    change (leb (tagged_lattice L) (proj1_sig (clamp maxw (TVal w p))) (TVal w q) = true).
    rewrite clamp_within; [cbn; now rewrite Pos.eqb_refl|exact Hwidth].
  - cbn. destruct (width_le_dec w maxw); reflexivity.
Qed.

(** Clamping only adds concrete words. *)
Theorem clamp_gamma : forall {P} (G : width -> P -> Z -> Prop)
  (maxw : width) (t : tagged P) (c : word),
  gamma (tagged_gamma G) t c -> gamma (capped_gamma G maxw) (clamp maxw t) c.
Proof.
  intros P G maxw [|w p|] c Hgamma; cbn; try assumption.
  destruct (width_le_dec w maxw); cbn; auto.
Qed.

(** Every numeric result is clamped, including the operands returned by backward transfer. *)
Definition capped_domain {P} (D : word_domain P) (maxw : width) :
  numeric_domain (@capped P maxw) :=
  {| lat := capped_lattice maxw (plat D);
     top_at w := clamp maxw (top_at (tagged_domain D) w);
     of_const w z := clamp maxw (of_const (tagged_domain D) w z);
     forward o xs := clamp maxw (forward (tagged_domain D) o (map (@proj1_sig _ _) xs));
     assume o a xs := map (clamp maxw)
       (assume (tagged_domain D) o (proj1_sig a) (map (@proj1_sig _ _) xs));
     meet a b := clamp maxw (meet (tagged_domain D) (proj1_sig a) (proj1_sig b)) |}.

Lemma capped_arguments : forall {P} G maxw xs ys,
  Forall2 (gamma (@capped_gamma P G maxw)) xs ys ->
  Forall2 (gamma (tagged_gamma G)) (map (@proj1_sig _ _) xs) ys.
Proof.
  intros P G maxw xs ys Hgamma. induction Hgamma; cbn; constructor; auto.
Qed.

Lemma clamp_list_sound : forall {P} G maxw xs ys,
  Forall2 (gamma (@tagged_gamma P G)) xs ys ->
  Forall2 (gamma (capped_gamma G maxw)) (map (clamp maxw) xs) ys.
Proof.
  intros P G maxw xs ys Hgamma. induction Hgamma; cbn; constructor; auto.
  now apply clamp_gamma.
Qed.

Lemma clamp_list_lower : forall {P} L maxw xs (ys : list (@capped P maxw)),
  Forall2 (fun x y => leb (tagged_lattice L) x y = true) xs (map (@proj1_sig _ _) ys) ->
  Forall2 (fun x y => leb (capped_lattice maxw L) x y = true) (map (clamp maxw) xs) ys.
Proof.
  intros P L maxw xs ys. revert xs.
  induction ys as [|y rest IH]; intros xs Hle; inversion Hle as [|x y' tail rest' Hxy Htail];
    subst; cbn; constructor.
  - now apply clamp_lower.
  - now apply IH.
Qed.

(** A cap preserves numeric soundness and pointwise refinement. *)
Theorem capped_numeric_laws : forall {P} (D : word_domain P) G,
  word_laws D G -> forall maxw : width,
  numeric_laws (capped_domain D maxw) (capped_gamma G maxw).
Proof.
  intros P D G laws maxw. pose proof (tagged_numeric_laws D G laws) as taggedlaws.
  constructor.
  - apply capped_laws. apply (plat_laws laws).
  - constructor. intros a b c Hle Ha.
    exact (gamma_monotone (gamma_laws taggedlaws) _ _ c Hle Ha).
  - constructor. intros c Hgamma. exact Hgamma.
  - intros w z Hword. apply clamp_gamma. exact (top_at_sound taggedlaws w z Hword).
  - intros w z. apply clamp_gamma. exact (of_const_sound taggedlaws w z).
  - intros o xs ys r Hgamma Heval. apply clamp_gamma.
    apply (forward_sound taggedlaws o _ ys r); [|exact Heval].
    now apply (capped_arguments G maxw).
  - intros o a xs ys r Hgamma Heval Ha. apply clamp_list_sound.
    apply (assume_sound taggedlaws o (proj1_sig a) _ ys r); try assumption.
    now apply (capped_arguments G maxw).
  - intros o a xs. cbn. rewrite length_map, tagged_assume_length, length_map. reflexivity.
  - intros o a xs. apply clamp_list_lower. apply (assume_refines taggedlaws).
  - intros a b c Ha Hb. apply clamp_gamma. apply (meet_sound taggedlaws); assumption.
  - intros a b. apply clamp_lower. apply (meet_lower_left taggedlaws).
Qed.
