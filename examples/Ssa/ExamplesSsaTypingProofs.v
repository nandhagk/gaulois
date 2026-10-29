(** * SSA typing and checker correctness

    Operators preserve their signatures and valid words. The structural checker verifies
    local signatures and finite certificates for availability along all control-flow paths.
    For example, a valid 64-bit allocation operand is necessarily below [2^64].
    Builds on: ExamplesSsaSyntax, ExamplesSsaTyping and ExamplesSsaSemantics. *)

From Stdlib Require Import List ZArith Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Views Require Import ViewsSemantics.
From Gaulois.Examples.Ssa Require Import
  ExamplesSsaSyntax ExamplesSsaTyping ExamplesSsaSemantics.
Import List.ListNotations.

Lemma first_index_sound {A : Type} (xs : list (nat * A)) x a :
  Map.get nat_encoding x (first_index xs) = Some a -> In (x, a) xs.
Proof.
  induction xs as [|[y b] rest IH]; cbn [first_index].
  - rewrite Map.get_empty; discriminate.
  - destruct (Nat.eq_dec x y) as [Heq|Hne].
    + subst y; rewrite Map.get_set_same; intros Heq; inversion Heq; left; reflexivity.
    + rewrite Map.get_set_other by exact Hne; intro Hget; right; apply IH; exact Hget.
Qed.

Lemma first_index_complete {A : Type} (xs : list (nat * A)) x a :
  NoDup (map fst xs) -> In (x, a) xs -> Map.get nat_encoding x (first_index xs) = Some a.
Proof.
  induction xs as [|[y b] rest IH]; cbn [first_index]; intros Hunique Hin.
  - contradiction.
  - inversion Hunique as [|? ? Hfresh Hrest]; subst.
    destruct Hin as [Heq|Hin].
    + inversion Heq; subst; apply Map.get_set_same.
    + rewrite Map.get_set_other.
      * apply IH; assumption.
      * intro Heq; subst y; apply Hfresh; exact (in_map fst rest (x, a) Hin).
Qed.

Lemma word_ok_valid w z : word_ok w z = true <-> valid_cval (VInt w z).
Proof.
  unfold word_ok; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt.
  destruct w; reflexivity.
Qed.

Lemma word_wrap_valid w z : valid_cval (VInt w (word_wrap w z)).
Proof.
  destruct w; unfold valid_cval, word_wrap, iw_modulus, iw_bits;
    apply Z.mod_pos_bound; reflexivity.
Qed.

Lemma normalize_const_typed c : ty_of (normalize_const c) = ty_of c.
Proof.
  destruct c as [w z|b off|f|z|z]; try reflexivity; destruct w; reflexivity.
Qed.

Lemma normalize_const_valid c : valid_cval (normalize_const c).
Proof.
  destruct c as [w z|b off|f|z|z]; try exact I; apply word_wrap_valid.
Qed.

Lemma bool_value_valid b : valid_cval (bool_value b).
Proof.
  destruct b; cbn [bool_value valid_cval]; lia.
Qed.

Lemma bin_eval_type w o a b v :
  bin_eval w o a b = Some v -> ty_of v = bin_result w o.
Proof.
  destruct o; cbn [bin_eval bin_result];
    try (intro Heq; inversion Heq; destruct w; reflexivity).
  destruct (b =? 0)%Z; intro Heq; try discriminate;
    inversion Heq; destruct w; reflexivity.
Qed.

Lemma bin_eval_valid w o a b v : bin_eval w o a b = Some v -> valid_cval v.
Proof.
  destruct o; cbn [bin_eval];
    try (intro Heq; inversion Heq; apply word_wrap_valid);
    try (intro Heq; inversion Heq; apply bool_value_valid).
  destruct (b =? 0)%Z; intro Heq; try discriminate;
    inversion Heq; apply word_wrap_valid.
Qed.

Lemma bin_eval_failure w o a b : bin_eval w o a b = None -> o = BDivU.
Proof.
  destruct o; cbn [bin_eval]; try discriminate; reflexivity.
Qed.

Lemma typed_single_i32 cs : map ty_of cs = [TyI32] ->
  exists z, cs = [VInt W32 z].
Proof.
  destruct cs as [|c [|d rest]]; cbn; try discriminate.
  destruct c as [[|] z|b off|f|z|z]; intro Heq; try discriminate; eexists; reflexivity.
Qed.

Lemma typed_single_i64 cs : map ty_of cs = [TyI64] ->
  exists z, cs = [VInt W64 z].
Proof.
  destruct cs as [|c [|d rest]]; cbn; try discriminate.
  destruct c as [[|] z|b off|f|z|z]; intro Heq; try discriminate; eexists; reflexivity.
Qed.

Lemma typed_integer_pair w cs : map ty_of cs = [iw_ty w; iw_ty w] ->
  exists a b, cs = [VInt w a; VInt w b].
Proof.
  destruct cs as [|c [|d [|e rest]]]; cbn; try discriminate.
  destruct w, c as [[|] a|bc oc|fc|zc|zc], d as [[|] b|bd od|fd|zd|zd];
    cbn; intro Heq; try discriminate; eexists; eexists; reflexivity.
Qed.

Lemma typed_pointer_pair cs : map ty_of cs = [TyPtr; TyI64] ->
  exists b off z, cs = [VPtr b off; VInt W64 z].
Proof.
  destruct cs as [|c [|d [|e rest]]]; cbn; try discriminate.
  destruct c as [[|] a|bc oc|fc|zc|zc], d as [[|] z|bd od|fd|zd|zd];
    cbn; intro Heq; try discriminate; eexists; eexists; eexists; reflexivity.
Qed.

(** Well-typed valid operands produce a value of the declared result type or a permitted trap. *)
Theorem op_eval_typed (ext : nat -> list cval -> option cval) (P : program) (o : sop)
    (cs : list cval) (ps : list ty) (r : ty) :
  ext_respects ext P -> op_sig P o = Some (ps, r) -> map ty_of cs = ps ->
  Forall valid_cval cs ->
  (forall v, op_eval ext o cs = Some v -> ty_of v = r) /\
  (op_eval ext o cs = None -> (exists w, o = OBin w BDivU) \/ exists tag, o = OExt tag).
Proof.
  intros Hext Hsig Htypes Hvalid; destruct o as [c|w o| | | |tag].
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct cs; cbn in Htypes; try discriminate; split; cbn [op_eval].
    + intros v Heq; inversion Heq; apply normalize_const_typed.
    + discriminate.
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct (typed_integer_pair w cs Htypes) as [a [b ->]].
    inversion Hvalid as [|? ? Ha Htail]; subst.
    inversion Htail as [|? ? Hb Hnil]; subst.
    apply word_ok_valid in Ha; apply word_ok_valid in Hb.
    cbn [op_eval]; destruct (iw_eq_dec w w) as [Heq|Hne]; [|contradiction].
    rewrite Ha, Hb; cbn; split.
    + intros v Heval; eapply bin_eval_type; exact Heval.
    + intro Hnone; apply bin_eval_failure in Hnone; subst o; left; exists w; reflexivity.
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct (typed_single_i32 cs Htypes) as [z ->].
    inversion Hvalid as [|? ? Hz Htail]; subst; apply word_ok_valid in Hz.
    cbn [op_eval]; rewrite Hz; split; [intros v Heq; inversion Heq; reflexivity|discriminate].
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct (typed_single_i64 cs Htypes) as [z ->].
    inversion Hvalid as [|? ? Hz Htail]; subst; apply word_ok_valid in Hz.
    cbn [op_eval]; rewrite Hz; split; [intros v Heq; inversion Heq; reflexivity|discriminate].
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct (typed_pointer_pair cs Htypes) as [b [off [z ->]]].
    split; cbn [op_eval]; [intros v Heq; inversion Heq; reflexivity|discriminate].
  - split.
    + intros v Heval; exact (proj1 (Hext tag ps r cs v
        (first_index_sound _ _ _ Hsig) Htypes Hvalid Heval)).
    + intro Hnone; right; exists tag; reflexivity.
Qed.

(** Successful operator results retain canonical integer payloads. *)
Theorem op_eval_valid (ext : nat -> list cval -> option cval) (P : program) (o : sop)
    (cs : list cval) (ps : list ty) (r : ty) (v : cval) :
  ext_respects ext P -> op_sig P o = Some (ps, r) -> map ty_of cs = ps ->
  Forall valid_cval cs -> op_eval ext o cs = Some v -> valid_cval v.
Proof.
  intros Hext Hsig Htypes Hvalid Heval; destruct o as [c|w o| | | |tag].
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct cs; cbn in Htypes; try discriminate.
    inversion Heval; apply normalize_const_valid.
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct (typed_integer_pair w cs Htypes) as [a [b ->]].
    inversion Hvalid as [|? ? Ha Htail]; subst.
    inversion Htail as [|? ? Hb Hnil]; subst.
    apply word_ok_valid in Ha; apply word_ok_valid in Hb.
    cbn [op_eval] in Heval; destruct (iw_eq_dec w w) as [Heq|Hne]; [|contradiction].
    rewrite Ha, Hb in Heval; cbn in Heval; eapply bin_eval_valid; exact Heval.
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct (typed_single_i32 cs Htypes) as [z ->].
    inversion Hvalid as [|? ? Hz Htail]; subst.
    pose proof Hz as Hrange; apply word_ok_valid in Hz.
    cbn [op_eval] in Heval; rewrite Hz in Heval; inversion Heval; subst v.
    cbn [valid_cval] in *; lia.
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct (typed_single_i64 cs Htypes) as [z ->].
    inversion Hvalid as [|? ? Hz Htail]; subst; apply word_ok_valid in Hz.
    cbn [op_eval] in Heval; rewrite Hz in Heval; inversion Heval; apply word_wrap_valid.
  - cbn [op_sig] in Hsig; injection Hsig as <- <-.
    destruct (typed_pointer_pair cs Htypes) as [b [off [z ->]]].
    inversion Heval; exact I.
  - exact (proj2 (Hext tag ps r cs v
      (first_index_sound _ _ _ Hsig) Htypes Hvalid Heval)).
Qed.

(** Empty extension declarations impose no requirements on the host evaluator. *)
Theorem ext_respects_nil (ext : nat -> list cval -> option cval) (P : program) :
  ext_sigs P = nil -> ext_respects ext P.
Proof.
  intros Hnil tag ps r cs v Hin; rewrite Hnil in Hin; contradiction.
Qed.

(** * Certificate and checker soundness *)

Lemma mem_set x y (a : idset) :
  Map.mem nat_encoding x (Map.set nat_encoding y tt a) =
    if Nat.eq_dec x y then true else Map.mem nat_encoding x a.
Proof.
  unfold Map.mem; destruct (Nat.eq_dec x y) as [->|Hne].
  - rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Definition represents (a : idset) (xs : list vid) : Prop :=
  forall x, Map.mem nat_encoding x a = true <-> In x xs.

Lemma represents_empty : represents Map.empty [].
Proof.
  intro x; unfold Map.mem; rewrite Map.get_empty; cbn; split; discriminate || contradiction.
Qed.

Lemma represents_set a xs x : represents a xs ->
  represents (Map.set nat_encoding x tt a) (x :: xs).
Proof.
  intros Ha y; rewrite mem_set; destruct (Nat.eq_dec y x) as [->|Hne]; cbn.
  - tauto.
  - rewrite (Ha y); split; [tauto|intros [Heq|Hin]; [congruence|exact Hin]].
Qed.

Lemma represents_index xs : represents (ids_index xs) xs.
Proof.
  induction xs as [|x xs IH]; cbn [ids_index first_index map].
  - apply represents_empty.
  - apply represents_set; exact IH.
Qed.

Lemma represents_add xs a ys : represents a ys -> represents (add_ids xs a) (xs ++ ys).
Proof.
  revert a ys; induction xs as [|x xs IH]; intros a ys Ha; cbn [add_ids fold_left].
  - exact Ha.
  - specialize (IH (Map.set nat_encoding x tt a) (x :: ys) (represents_set a ys x Ha)).
    intro y; rewrite (IH y), !in_app_iff; cbn; tauto.
Qed.

Lemma unique_check_sound seen xs : unique_check seen xs = true ->
  NoDup xs /\ forall x, In x xs -> Map.mem nat_encoding x seen = false.
Proof.
  revert seen; induction xs as [|x xs IH]; intros seen Hcheck; cbn [unique_check] in Hcheck.
  - split; [constructor|intros y Hin; contradiction].
  - apply andb_true_iff in Hcheck as [Hfresh Hrest]; apply negb_true_iff in Hfresh.
    destruct (IH _ Hrest) as [Hunique Habsent]; split.
    + constructor; [|exact Hunique].
      intro Hin; specialize (Habsent x Hin); rewrite mem_set in Habsent.
      destruct (Nat.eq_dec x x); discriminate || contradiction.
    + intros y [->|Hin]; [exact Hfresh|].
      specialize (Habsent y Hin); rewrite mem_set in Habsent.
      destruct (Nat.eq_dec y x); discriminate || assumption.
Qed.

Lemma forallb_sound {A : Type} (p : A -> bool) (Q : A -> Prop) xs :
  (forall x, p x = true -> Q x) -> forallb p xs = true -> Forall Q xs.
Proof.
  intros Hpoint Hall; apply Forall_forall; intros x Hin.
  apply Hpoint; apply (proj1 (forallb_forall p xs) Hall x Hin).
Qed.

Lemma indexed_forall a available xs : represents a available ->
  forallb (fun x => Map.mem nat_encoding x a) xs = true ->
  Forall (fun x => In x available) xs.
Proof.
  intros Ha; apply forallb_sound; intros x Hmem; apply Ha; exact Hmem.
Qed.

Lemma body_available_check_sound code a available : represents a available ->
  body_available_check a code = true -> body_available available code.
Proof.
  revert a available; induction code as [|i code IH]; intros a available Ha Hcheck.
  - exact I.
  - apply andb_true_iff in Hcheck as [Huses Hrest]; split.
    + eapply indexed_forall; eassumption.
    + eapply IH; [apply represents_add; exact Ha|exact Hrest].
Qed.

Lemma certificate_check_sound fd R : certificate_check fd R = true ->
  availability_certificate fd R.
Proof.
  unfold certificate_check, availability_certificate.
  intros Hcheck; apply andb_true_iff in Hcheck as [Hentry Hall]; split.
  - destruct (required R (fentry fd)); reflexivity || discriminate.
  - eapply forallb_sound; [|exact Hall]; intros [l b] Hblock; cbn in *.
    apply andb_true_iff in Hblock as [Hprefix Hedges].
    apply andb_true_iff in Hprefix as [Hbody Hterm].
    pose proof (represents_index (map fst (bparams b) ++ required R l)) as Hstart.
    pose proof (represents_add (body_defs b) _ _ Hstart) as Hfinish.
    split; [eapply body_available_check_sound; eassumption|].
    split; [eapply indexed_forall; eassumption|].
    eapply forallb_sound; [|exact Hedges]; intros edge Hedge.
    eapply indexed_forall; eassumption.
Qed.

Lemma result_type_check_sound T dst : result_type_check T dst = true -> result_has_type T dst.
Proof.
  destruct dst as [[x t]|]; cbn [result_type_check result_has_type]; [|tauto].
  destruct (option_eq_dec ty_eq_dec (T x) (Some t)); congruence.
Qed.

Lemma instr_type_check_sound P T i : instr_type_check P T i = true -> instr_typed P T i.
Proof.
  unfold instr_type_check, instr_type_check_with, instr_typed; fold (instr_sig P T).
  destruct (instr_sig P T i) as [[ps dst]|];
    [|discriminate].
  rewrite andb_true_iff; intros [Hargs Hdst]; split.
  - destruct (option_eq_dec (list_eq_dec ty_eq_dec) (types_of T (instr_uses i)) (Some ps));
      congruence.
  - apply result_type_check_sound; exact Hdst.
Qed.

Lemma jump_type_check_sound B T edge : jump_type_check B T edge = true -> typed_jump B T edge.
Proof.
  unfold jump_type_check, typed_jump; destruct (B (fst edge)) as [b|]; [|discriminate].
  destruct (option_eq_dec (list_eq_dec ty_eq_dec) (types_of T (snd edge))
    (Some (map snd (bparams b)))); congruence.
Qed.

Lemma term_type_check_sound P fd T B t :
  term_type_check P fd T B t = true -> term_typed P fd T B t.
Proof.
  destruct t as [l args|c l1 a1 l2 a2|c cases d da|c args k|x];
    cbn [term_type_check term_type_check_with term_typed].
  - apply forallb_sound; apply jump_type_check_sound.
  - rewrite andb_true_iff; intros [Hc Hjumps]; split.
    + destruct (option_eq_dec ty_eq_dec (T c) (Some TyI32)); congruence.
    + eapply forallb_sound; [apply jump_type_check_sound|exact Hjumps].
  - rewrite andb_true_iff; intros [Hc Hjumps]; split.
    + destruct (option_eq_dec ty_eq_dec (T c) (Some TyI32)); congruence.
    + eapply forallb_sound; [apply jump_type_check_sound|exact Hjumps].
  - fold (callee_sig P T).
    destruct (callee_sig P T c) as [[ps r]|], (B k) as [b|]; try discriminate.
    rewrite andb_true_iff; intros [Hargs Hcont]; split.
    + destruct (option_eq_dec (list_eq_dec ty_eq_dec) (types_of T args) (Some ps));
        congruence.
    + destruct (list_eq_dec ty_eq_dec (map snd (bparams b)) [r]); congruence.
  - destruct (option_eq_dec ty_eq_dec (T x) (Some (fresult fd))); congruence.
Qed.

Lemma continuation_check_sound counts t :
  continuation_check counts t = true -> continuation_ok counts t.
Proof.
  destruct t; cbn [continuation_check continuation_ok]; try tauto.
  destruct (Map.get nat_encoding k counts) as [[|[|n]]|]; congruence.
Qed.

Lemma function_check_sound P ffd : function_check P ffd = true ->
  function_wf P (fst ffd) (snd ffd).
Proof.
  destruct ffd as [f fd]; unfold function_check, function_check_with, function_wf; cbn.
  rewrite !andb_true_iff; intros [[[Hentry Hunique] Hblocks] Hcert].
  split; [destruct (find_block fd (fentry fd)) as [b|]; [eauto|discriminate]|].
  split; [exact (proj1 (unique_check_sound _ _ Hunique))|].
  split; [|exists (propose_requirements fd); apply certificate_check_sound; exact Hcert].
  eapply forallb_sound; [|exact Hblocks]; intros [l b] Hblock; cbn in *.
  rewrite !andb_true_iff in Hblock; destruct Hblock as [[[Hparams Hbody] Hterm] Hcont].
  split.
  - eapply forallb_sound; [|exact Hparams]; intros [x t] Hparam; cbn in *.
    destruct (option_eq_dec ty_eq_dec (static_ty P f x) (Some t)); congruence.
  - split; [eapply forallb_sound; [apply instr_type_check_sound|exact Hbody]|].
    split; [apply term_type_check_sound; exact Hterm|].
    apply continuation_check_sound; exact Hcont.
Qed.

(** * Prepared checker lookup agreement *)

Lemma first_index_wf {A : Type} (xs : list (nat * A)) :
  Map.wf nat_encoding (first_index xs).
Proof.
  induction xs as [|[x a] rest IH]; cbn [first_index].
  - apply Map.wf_empty.
  - apply Map.wf_set; exact IH.
Qed.

(** Cached entry signatures preserve the public lookup, including first bindings. *)
Lemma prepared_entry_index_agrees operators (xs : list (func * fdef)) :
  Map.map prepared_signature (Map.map (prepare_function operators) (first_index xs)) =
    Map.map entry_signature (first_index xs).
Proof.
  apply (Map.extensionality nat_encoding).
  - apply Map.wf_map; apply Map.wf_map; apply first_index_wf.
  - apply Map.wf_map; apply first_index_wf.
  - intro f; rewrite !Map.get_map.
    destruct (Map.get nat_encoding f (first_index xs)); reflexivity.
Qed.

Lemma prepared_entry_sig_agrees P operators :
  prepared_entry_sig (Map.map (prepare_function operators) (first_index (funcs P))) =
    entry_sig P.
Proof.
  unfold prepared_entry_sig, entry_sig; rewrite prepared_entry_index_agrees; reflexivity.
Qed.

(** A function's prepared block lookup is the public first-binding block lookup. *)
Lemma prepared_blocks_agree operators fd :
  (fun l => Map.get nat_encoding l (prepared_block_index (prepare_function operators fd))) =
    find_block fd.
Proof.
  reflexivity.
Qed.

(** Prepared types agree with static lookup for the function selected by its name. *)
Lemma prepared_types_agree P f fd : find_func P f = Some fd ->
  (fun x => Map.get nat_encoding x (prepared_type_index (prepare_function (op_sig P) fd))) =
    static_ty P f.
Proof.
  intro Hfind; unfold static_ty; rewrite Hfind; reflexivity.
Qed.

(** Function checking through prepared tables retains the public checking conditions. *)
Lemma prepared_function_check_agrees P f fd : find_func P f = Some fd ->
  function_check_prepared (op_sig P)
    (prepared_entry_sig (Map.map (prepare_function (op_sig P)) (first_index (funcs P))))
    (Map.map (prepare_function (op_sig P)) (first_index (funcs P))) (f, fd) =
    function_check P (f, fd).
Proof.
  intro Hfind; rewrite prepared_entry_sig_agrees.
  unfold function_check_prepared; cbn [fst]; rewrite Map.get_map.
  change (Map.get nat_encoding f (first_index (funcs P)) = Some fd) in Hfind.
  rewrite Hfind; cbn [option_map].
  unfold function_check, static_ty; cbn [fst snd].
  change (find_func P f = Some fd) in Hfind; rewrite Hfind; reflexivity.
Qed.

Lemma prepared_checks_agree P : NoDup (map fst (funcs P)) ->
  forallb
    (function_check_prepared (op_sig P)
      (prepared_entry_sig (Map.map (prepare_function (op_sig P)) (first_index (funcs P))))
      (Map.map (prepare_function (op_sig P)) (first_index (funcs P)))) (funcs P) =
    forallb (function_check P) (funcs P).
Proof.
  intro Hunique; apply Bool.eq_true_iff_eq; rewrite !forallb_forall.
  split; intros Hall [f fd] Hin; specialize (Hall (f, fd) Hin);
    assert (Hfind : find_func P f = Some fd) by
      (apply first_index_complete; assumption).
  - rewrite (prepared_function_check_agrees P f fd Hfind) in Hall; exact Hall.
  - rewrite (prepared_function_check_agrees P f fd Hfind); exact Hall.
Qed.

(** Preparation preserves the entire original checker result, including malformed programs. *)
Lemma wf_check_agrees P :
  wf_check P =
    (match find_func P (main P) with Some _ => true | None => false end) &&
    unique_check Map.empty (map fst (funcs P)) &&
    unique_check Map.empty (all_definitions P) && forallb (function_check P) (funcs P).
Proof.
  unfold wf_check.
  destruct (unique_check Map.empty (map fst (funcs P))) eqn:Hunique.
  - rewrite (prepared_checks_agree P (proj1 (unique_check_sound _ _ Hunique))); reflexivity.
  - rewrite !andb_false_r; reflexivity.
Qed.

(** Checker acceptance and a respecting host establish all program well-formedness conditions. *)
Theorem wf_check_sound (ext : nat -> list cval -> option cval) (P : program) :
  ext_respects ext P -> wf_check P = true -> wf_program ext P.
Proof.
  intros Hext Hcheck; rewrite wf_check_agrees, !andb_true_iff in Hcheck.
  destruct Hcheck as [[[Hmain Hfunctions] Hvalues] Hlocal].
  pose proof (proj1 (unique_check_sound _ _ Hfunctions)) as Hunique.
  split; [destruct (find_func P (main P)) as [fd|]; [eauto|discriminate]|].
  split; [exact Hunique|].
  split; [exact (proj1 (unique_check_sound _ _ Hvalues))|].
  split; [eapply forallb_sound; [apply function_check_sound|exact Hlocal]|exact Hext].
Qed.

(** * Environment support and local typing *)

Definition env_bound (env : vid -> option cval) (xs : list vid) : Prop :=
  forall x, In x xs -> exists v, env x = Some v.

Definition support_le (env env' : vid -> option cval) : Prop :=
  forall x v, env x = Some v -> exists v', env' x = Some v'.

Lemma env_set_support env x v : support_le env (env_set env x v).
Proof.
  intros y c Hget; unfold env_set; destruct (Nat.eq_dec y x); eauto.
Qed.

Lemma env_set_bound env x v : env_bound (env_set env x v) [x].
Proof.
  intros y [Heq|Hin]; [subst y|contradiction]; exists v; unfold env_set.
  destruct (Nat.eq_dec x x); congruence.
Qed.

Lemma env_set_typed P f env x v : typed_env P f env ->
  static_ty P f x = Some (ty_of v) -> valid_cval v -> typed_env P f (env_set env x v).
Proof.
  intros Henv Htype Hvalid y c; unfold env_set; destruct (Nat.eq_dec y x) as [->|Hne].
  - intro Heq; injection Heq as <-; split; assumption.
  - apply Henv.
Qed.

Lemma read_args_sound env xs cs : read_args env xs = Some cs ->
  Forall2 (fun x c => env x = Some c) xs cs.
Proof.
  revert cs; induction xs as [|x xs IH]; intros cs Hread; cbn [read_args] in Hread.
  - injection Hread as <-; constructor.
  - destruct (env x) as [c|] eqn:Hx, (read_args env xs) as [rest|] eqn:Hrest;
      try discriminate; injection Hread as <-; constructor; [exact Hx|apply IH; reflexivity].
Qed.

Lemma read_args_typed P f env xs cs ps : typed_env P f env ->
  read_args env xs = Some cs -> types_of (static_ty P f) xs = Some ps ->
  map ty_of cs = ps /\ Forall valid_cval cs.
Proof.
  intros Henv Hread; apply read_args_sound in Hread; revert ps.
  induction Hread as [|x c xs cs Hx Hrest IH]; intros ps Htypes; cbn [types_of] in Htypes.
  - injection Htypes as <-; split; [reflexivity|constructor].
  - destruct (Henv x c Hx) as [Htype Hvalid]; rewrite Htype in Htypes.
    destruct (types_of (static_ty P f) xs) as [ts|] eqn:Hts; try discriminate.
    injection Htypes as <-; destruct (IH ts eq_refl) as [Hmap Hvals]; split; cbn.
    + rewrite Hmap; reflexivity.
    + constructor; assumption.
Qed.

Lemma bind_params_support env ps vs env' : bind_params env ps vs = Some env' ->
  support_le env env' /\ env_bound env' (map fst ps).
Proof.
  revert env vs env'; induction ps as [|[x t] ps IH]; intros env vs env' Hbind;
    destruct vs as [|v vs]; cbn [bind_params] in Hbind; try discriminate.
  - injection Hbind as <-; split; [intros y c Hget; eauto|intros y Hin; contradiction].
  - destruct (IH _ _ _ Hbind) as [Hsupport Hparams]; split.
    + intros y c Hget; destruct (env_set_support env x v y c Hget) as [d Hd].
      exact (Hsupport y d Hd).
    + intros y [Heq|Hin].
      * subst y; apply (Hsupport x v); unfold env_set.
        destruct (Nat.eq_dec x x); congruence.
      * apply Hparams; exact Hin.
Qed.

Lemma bind_params_typed P f env ps vs env' : typed_env P f env ->
  Forall (fun xt => static_ty P f (fst xt) = Some (snd xt)) ps ->
  map ty_of vs = map snd ps -> Forall valid_cval vs ->
  bind_params env ps vs = Some env' -> typed_env P f env'.
Proof.
  revert env vs env'; induction ps as [|[x t] ps IH];
    intros env vs env' Henv Hparams Htypes Hvalid Hbind;
    destruct vs as [|v vs]; cbn [bind_params] in Hbind; try discriminate.
  - injection Hbind as <-; exact Henv.
  - inversion Hparams as [|? ? Hx Hps]; subst.
    inversion Hvalid as [|? ? Hv Hvs]; subst.
    cbn in Htypes; injection Htypes as Hvt Htypes.
    eapply (IH (env_set env x v) vs env'); try eassumption.
    apply env_set_typed; [exact Henv|cbn in Hx; rewrite Hvt; exact Hx|exact Hv].
Qed.

Lemma wf_function ext P f fd : wf_program ext P -> find_func P f = Some fd ->
  function_wf P f fd.
Proof.
  intros [_ [_ [_ [Hfunctions _]]]] Hfind.
  apply first_index_sound in Hfind; exact (proj1 (Forall_forall _ _) Hfunctions (f, fd) Hfind).
Qed.

Lemma wf_block ext P f fd l b : wf_program ext P -> find_func P f = Some fd ->
  find_block fd l = Some b ->
  Forall (fun xt => static_ty P f (fst xt) = Some (snd xt)) (bparams b) /\
  Forall (instr_typed P (static_ty P f)) (bbody b) /\
  term_typed P fd (static_ty P f) (find_block fd) (bterm b) /\
  continuation_ok (incoming_index fd) (bterm b).
Proof.
  intros Hwf Hf Hb; destruct (wf_function ext P f fd Hwf Hf) as [_ [_ [Hall _]]].
  apply first_index_sound in Hb; exact (proj1 (Forall_forall _ _) Hall (l, b) Hb).
Qed.

Lemma wf_instruction ext P fr i : wf_program ext P -> at_instr P fr i ->
  instr_typed P (static_ty P (ffunc fr)) i.
Proof.
  intros Hwf [fd [b [Hf [Hb Hi]]]].
  destruct (wf_block ext P _ _ _ _ Hwf Hf Hb) as [_ [Hbody _]].
  exact (proj1 (Forall_forall _ _) Hbody i (nth_error_In _ _ Hi)).
Qed.

Lemma wf_terminator ext P fr t : wf_program ext P -> at_term P fr t ->
  exists fd, find_func P (ffunc fr) = Some fd /\
    term_typed P fd (static_ty P (ffunc fr)) (find_block fd) t.
Proof.
  intros Hwf [fd [b [Hf [Hb [Hpc Hterm]]]]].
  destruct (wf_block ext P _ _ _ _ Hwf Hf Hb) as [_ [_ [Htyped _]]].
  exists fd; split; [exact Hf|rewrite <- Hterm; exact Htyped].
Qed.

Definition prefix_defs (b : ssa_block) (pc : nat) : list vid :=
  flat_map instr_def (firstn pc (bbody b)).

Definition available_at (b : ssa_block) (R : requirements) (l : label) (pc : nat) : list vid :=
  prefix_defs b pc ++ map fst (bparams b) ++ required R l.

Definition frame_available (P : program) (fr : sframe) : Prop :=
  forall fd b R, find_func P (ffunc fr) = Some fd ->
    find_block fd (flabel fr) = Some b -> availability_certificate fd R ->
    env_bound (fenv fr) (available_at b R (flabel fr) (fpc fr)).

Definition frame_good (P : program) (fr : sframe) : Prop :=
  typed_env P (ffunc fr) (fenv fr) /\ frame_available P fr.

Lemma firstn_step {A : Type} (xs : list A) n x : nth_error xs n = Some x ->
  firstn (S n) xs = firstn n xs ++ [x].
Proof.
  revert xs; induction n as [|n IH]; intros [|y xs] Hnth; cbn in *; try discriminate.
  - injection Hnth as ->; reflexivity.
  - rewrite (IH xs Hnth); reflexivity.
Qed.

Lemma certificate_block fd R l b : availability_certificate fd R ->
  find_block fd l = Some b ->
  body_available (map fst (bparams b) ++ required R l) (bbody b) /\
  Forall (fun x => In x (body_defs b ++ map fst (bparams b) ++ required R l))
    (term_uses (bterm b)) /\
  Forall (fun edge => Forall
    (fun x => In x (body_defs b ++ map fst (bparams b) ++ required R l))
    (required R (fst edge))) (term_edges (bterm b)).
Proof.
  intros [_ Hall] Hb; apply first_index_sound in Hb.
  exact (proj1 (Forall_forall _ _) Hall (l, b) Hb).
Qed.

Lemma body_available_use code start pc i : body_available start code ->
  nth_error code pc = Some i ->
  Forall (fun x => In x (flat_map instr_def (firstn pc code) ++ start)) (instr_uses i).
Proof.
  revert start pc; induction code as [|j code IH]; intros start [|pc] Hbody Hnth;
    cbn in Hnth; try discriminate; destruct Hbody as [Huses Hrest].
  - injection Hnth as <-; exact Huses.
  - specialize (IH _ pc Hrest Hnth).
    eapply Forall_impl; [|exact IH]; intros x Hin.
    cbn; rewrite !in_app_iff in *; tauto.
Qed.

Lemma frame_operands_bound ext P fr i : wf_program ext P -> frame_available P fr ->
  at_instr P fr i -> env_bound (fenv fr) (instr_uses i).
Proof.
  intros Hwf Havailable [fd [b [Hf [Hb Hnth]]]].
  destruct (wf_function ext P _ _ Hwf Hf) as [_ [_ [_ [R Hcert]]]].
  pose proof (proj1 (certificate_block fd R _ _ Hcert Hb)) as Hbody.
  pose proof (body_available_use _ _ _ _ Hbody Hnth) as Huses.
  intros x Hin; apply (Havailable fd b R Hf Hb Hcert x).
  exact (proj1 (Forall_forall _ _) Huses x Hin).
Qed.

Lemma advance_available P fr i env' : at_instr P fr i -> frame_available P fr ->
  support_le (fenv fr) env' -> env_bound env' (instr_def i) ->
  frame_available P (advance fr env').
Proof.
  intros [fd0 [b0 [Hf0 [Hb0 Hnth]]]] Hav Hsupport Hdefs fd b R Hf Hb Hcert.
  cbn in Hf, Hb; rewrite Hf0 in Hf; injection Hf as <-.
  rewrite Hb0 in Hb; injection Hb as <-.
  intros x Hin; change (In x (flat_map instr_def (firstn (S (fpc fr)) (bbody b0)) ++
    map fst (bparams b0) ++ required R (flabel fr))) in Hin.
  rewrite (firstn_step _ _ _ Hnth), flat_map_app in Hin; cbn in Hin.
  rewrite app_nil_r, !in_app_iff in Hin.
  destruct Hin as [[Hin|Hin]|Hin].
  - destruct (Hav _ _ R Hf0 Hb0 Hcert x) as [v Hv].
    + unfold available_at, prefix_defs; rewrite in_app_iff; left; exact Hin.
    + exact (Hsupport x v Hv).
  - exact (Hdefs x Hin).
  - destruct (Hav _ _ R Hf0 Hb0 Hcert x) as [v Hv].
    + unfold available_at; rewrite in_app_iff; right; apply in_app_iff; exact Hin.
    + exact (Hsupport x v Hv).
Qed.

Lemma entry_available P f fd b env ret : find_func P f = Some fd ->
  find_block fd (fentry fd) = Some b -> env_bound env (map fst (bparams b)) ->
  frame_available P (SFrame f (fentry fd) 0 env ret).
Proof.
  intros Hf Hb Hbound fd' b' R Hf' Hb' [Hentry Hcert]; cbn in Hf', Hb'.
  rewrite Hf in Hf'; injection Hf' as <-; rewrite Hb in Hb'; injection Hb' as <-.
  unfold available_at, prefix_defs; cbn; rewrite Hentry, app_nil_r; exact Hbound.
Qed.

Lemma jump_available P fr t l env' : at_term P fr t -> frame_available P fr ->
  In l (map fst (term_edges t)) -> support_le (fenv fr) env' ->
  (forall fd b, find_func P (ffunc fr) = Some fd -> find_block fd l = Some b ->
    env_bound env' (map fst (bparams b))) -> frame_available P (enter fr l env').
Proof.
  intros [fd0 [b0 [Hf0 [Hb0 [Hpc Hterm]]]]] Hav Hedge Hsupport Hparams.
  intros fd b R Hf Hb Hcert; cbn in Hf, Hb.
  unfold available_at, prefix_defs; cbn; intros x Hin; apply in_app_iff in Hin.
  destruct Hin as [Hin|Hin]; [exact (Hparams fd b Hf Hb x Hin)|].
  rewrite Hf0 in Hf; injection Hf as <-.
  destruct (certificate_block fd0 R _ _ Hcert Hb0) as [_ [_ Hedges]].
  apply in_map_iff in Hedge; destruct Hedge as [[target args] [Heq Hedge]]; cbn in Heq.
  subst target; rewrite <- Hterm in Hedge.
  pose proof (proj1 (Forall_forall _ _) Hedges (l, args) Hedge) as Hrequired.
  pose proof (proj1 (Forall_forall _ _) Hrequired x Hin) as Hfinish.
  destruct (Hav fd0 b0 R Hf0 Hb0 Hcert x) as [v Hv].
  - unfold available_at, prefix_defs; rewrite Hpc, firstn_all; exact Hfinish.
  - exact (Hsupport x v Hv).
Qed.

Lemma jump_env_support P fr l vs env : jump_env P fr l vs = Some env ->
  support_le (fenv fr) env /\
  forall fd b, find_func P (ffunc fr) = Some fd -> find_block fd l = Some b ->
    env_bound env (map fst (bparams b)).
Proof.
  unfold jump_env; destruct (find_func P (ffunc fr)) as [fd|] eqn:Hf;
    [|discriminate]; destruct (find_block fd l) as [b|] eqn:Hb; [|discriminate].
  intro Hbind; destruct (bind_params_support _ _ _ _ Hbind) as [Hsupport Hbound].
  split; [exact Hsupport|].
  intros fd' b' Hf' Hb'; injection Hf' as <-.
  rewrite Hb in Hb'; injection Hb' as <-; exact Hbound.
Qed.

Lemma memory_load_typed t sz mb off v : memory_load t sz mb off = Some v ->
  ty_of v = t /\ valid_cval v.
Proof.
  unfold memory_load; destruct (access_ok mb off sz); [|discriminate].
  destruct t, sz; try discriminate;
    try (destruct (integer_bytes _ _ _) as [z|]; cbn; [|discriminate];
      intro Heq; injection Heq as <-; split; [reflexivity|apply word_wrap_valid]).
  destruct (mbytes mb off) as [z|p i]; [discriminate|].
  destruct p, i; try discriminate.
  destruct (fragments_ok 8 (mbytes mb) off (VPtr b o) 0); [|discriminate].
  intro Heq; injection Heq as <-; split; [reflexivity|exact I].
Qed.

Lemma jump_env_typed ext P fr l cs env : wf_program ext P -> typed_env P (ffunc fr) (fenv fr) ->
  jump_env P fr l cs = Some env ->
  (forall fd b, find_func P (ffunc fr) = Some fd -> find_block fd l = Some b ->
    map ty_of cs = map snd (bparams b)) -> Forall valid_cval cs ->
  typed_env P (ffunc fr) env.
Proof.
  intros Hwf Henv; unfold jump_env.
  destruct (find_func P (ffunc fr)) as [fd|] eqn:Hf; [|discriminate].
  destruct (find_block fd l) as [b|] eqn:Hb; [|discriminate].
  intros Hbind Htypes Hvalid; eapply bind_params_typed; try eassumption.
  - exact (proj1 (wf_block ext P _ _ _ _ Hwf Hf Hb)).
  - exact (Htypes fd b eq_refl Hb).
Qed.

Lemma entry_sig_find P f fd b : find_func P f = Some fd ->
  find_block fd (fentry fd) = Some b -> entry_sig P f = Some (map snd (bparams b), fresult fd).
Proof.
  intros Hf Hb; unfold entry_sig; rewrite Map.get_map.
  change (match option_map entry_signature (find_func P f) with
    | Some sig => sig
    | None => None
    end = Some (map snd (bparams b), fresult fd)).
  rewrite Hf; cbn [option_map]; unfold entry_signature; rewrite Hb; reflexivity.
Qed.

Lemma callee_def_target P env c f fd b : callee_def P env c = Some (f, fd, b) ->
  find_func P f = Some fd /\ find_block fd (fentry fd) = Some b /\
  forall T ps r, callee_sig P T c = Some (ps, r) ->
    ps = map snd (bparams b) /\ r = fresult fd.
Proof.
  destruct c as [g|x ps0 r0].
  - unfold callee_def; cbn -[find_func find_block].
    destruct (find_func P g) as [gd|] eqn:Hf; [|discriminate].
    destruct (find_block gd (fentry gd)) as [gb|] eqn:Hb; [|discriminate].
    intro Heq; injection Heq as <- <- <-; split; [exact Hf|]; split; [exact Hb|].
    intros T ps r; change (entry_sig P g = Some (ps, r) ->
      ps = map snd (bparams gb) /\ r = fresult gd).
    rewrite (entry_sig_find P g gd gb Hf Hb).
    intro Heq; injection Heq as <- <-; split; reflexivity.
  - unfold callee_def; cbn -[find_func find_block].
    destruct (env x) as [v|]; cbn -[find_func find_block]; [|discriminate].
    destruct v as [w z|bb off|g|z|z]; try discriminate.
    destruct (find_func P g) as [gd|] eqn:Hf; [|discriminate].
    destruct (find_block gd (fentry gd)) as [gb|] eqn:Hb; [|discriminate].
    destruct (list_eq_dec ty_eq_dec ps0 (map snd (bparams gb))) as [Hps|Hne];
      [|discriminate].
    destruct (ty_eq_dec r0 (fresult gd)) as [Hr|Hne]; [|discriminate].
    intro Heq; injection Heq as <- <- <-; split; [exact Hf|]; split; [exact Hb|].
    intros T ps r; cbn [callee_sig callee_sig_with]; destruct (T x) as [t|];
      [|discriminate].
    destruct t; try discriminate; intro Heq; injection Heq as <- <-; split; assumption.
Qed.

Lemma call_typed ext P fr c args cont : wf_program ext P -> at_term P fr (TCall c args cont) ->
  exists fd ps r b, find_func P (ffunc fr) = Some fd /\
    callee_sig P (static_ty P (ffunc fr)) c = Some (ps, r) /\
    find_block fd cont = Some b /\ types_of (static_ty P (ffunc fr)) args = Some ps /\
    map snd (bparams b) = [r].
Proof.
  intros Hwf Hat; destruct (wf_terminator ext P fr _ Hwf Hat) as [fd [Hf Htyped]].
  cbn [term_typed] in Htyped.
  destruct (callee_sig P (static_ty P (ffunc fr)) c) as [[ps r]|] eqn:Hsig;
    [|contradiction]; destruct (find_block fd cont) as [b|] eqn:Hb; [|contradiction].
  destruct Htyped as [Hargs Hcont]; exists fd, ps, r, b; repeat split; assumption.
Qed.

Lemma typed_jump_env ext P fr l args cs env fd : wf_program ext P ->
  typed_env P (ffunc fr) (fenv fr) -> find_func P (ffunc fr) = Some fd ->
  typed_jump (find_block fd) (static_ty P (ffunc fr)) (l, args) ->
  read_args (fenv fr) args = Some cs -> jump_env P fr l cs = Some env ->
  typed_env P (ffunc fr) env.
Proof.
  intros Hwf Henv Hf Hjump Hread Hbind; unfold typed_jump in Hjump; cbn in Hjump.
  destruct (find_block fd l) as [b|] eqn:Hb; [|contradiction].
  destruct (read_args_typed P _ _ _ _ _ Henv Hread Hjump) as [Htypes Hvalid].
  eapply jump_env_typed; try eassumption.
  intros fd' b' Hf' Hb'; rewrite Hf in Hf'; injection Hf' as <-.
  rewrite Hb in Hb'; injection Hb' as <-; exact Htypes.
Qed.

Lemma switch_target_edge z cases d da l args : switch_target z cases d da = (l, args) ->
  In (l, args) (term_edges (TSwitch 0%nat cases d da)).
Proof.
  induction cases as [|[[key target] actual] rest IH]; cbn [switch_target term_edges map].
  - intro Heq; injection Heq as <- <-; left; reflexivity.
  - destruct (word_wrap W32 key =? z)%Z.
    + intro Heq; injection Heq as <- <-; left; reflexivity.
    + intro Heq; right; apply IH; exact Heq.
Qed.

Definition return_link (P : program) (child caller : sframe) : Prop :=
  exists fd c args cont ps, find_func P (ffunc child) = Some fd /\
    at_term P caller (TCall c args cont) /\ fret caller = cont /\
    callee_sig P (static_ty P (ffunc caller)) c = Some (ps, fresult fd).

Fixpoint stack_links (P : program) (frames : list sframe) : Prop :=
  match frames with
  | [] => True
  | fr :: rest =>
    match rest with
    | [] => True
    | caller :: _ => return_link P fr caller /\ stack_links P rest
    end
  end.

Definition state_good (P : program) (s : state) : Prop :=
  Forall (frame_good P) (stack s) /\ stack_links P (stack s).

Lemma return_link_child P child caller child' :
  ffunc child' = ffunc child -> return_link P child caller -> return_link P child' caller.
Proof.
  intros Heq Hlink; unfold return_link in *; rewrite Heq; exact Hlink.
Qed.

Lemma past_end_available P fr env : at_term P fr (TRet env) -> frame_available P fr ->
  frame_available P (advance fr (fenv fr)).
Proof.
  intros [fd0 [b0 [Hf0 [Hb0 [Hpc Hterm]]]]] Hav fd b R Hf Hb Hcert.
  cbn in Hf, Hb; rewrite Hf0 in Hf; injection Hf as <-.
  rewrite Hb0 in Hb; injection Hb as <-.
  specialize (Hav fd0 b0 R Hf0 Hb0 Hcert).
  unfold available_at, prefix_defs in *; cbn [fpc flabel advance] in *.
  rewrite Hpc, firstn_all in Hav.
  change (env_bound (fenv fr)
    (flat_map instr_def (firstn (S (fpc fr)) (bbody b0)) ++
      map fst (bparams b0) ++ required R (flabel fr))).
  rewrite Hpc, firstn_all2 by lia; exact Hav.
Qed.

Lemma advance_good P fr i env' : frame_good P fr -> at_instr P fr i ->
  typed_env P (ffunc fr) env' -> support_le (fenv fr) env' ->
  env_bound env' (instr_def i) -> frame_good P (advance fr env').
Proof.
  intros [_ Hav] Hat Htyped Hsupport Hdefs; split; [exact Htyped|].
  eapply advance_available; eassumption.
Qed.

Lemma unchanged_advance_good P fr i : frame_good P fr -> at_instr P fr i ->
  instr_def i = [] -> frame_good P (advance fr (fenv fr)).
Proof.
  intros [Htyped Hav] Hat Hdefs; eapply advance_good; try eassumption.
  - split; assumption.
  - intros x v Hv; eauto.
  - rewrite Hdefs; intros x Hin; contradiction.
Qed.

Lemma assign_advance_good P fr i x v : frame_good P fr -> at_instr P fr i ->
  instr_def i = [x] -> static_ty P (ffunc fr) x = Some (ty_of v) -> valid_cval v ->
  frame_good P (advance fr (env_set (fenv fr) x v)).
Proof.
  intros [Htyped Hav] Hat Hdefs Htype Hvalid; eapply advance_good.
  - split; assumption.
  - exact Hat.
  - apply env_set_typed; assumption.
  - apply env_set_support.
  - rewrite Hdefs; apply env_set_bound.
Qed.

Lemma jump_good P fr t l vs env : frame_good P fr -> at_term P fr t ->
  In l (map fst (term_edges t)) -> jump_env P fr l vs = Some env ->
  typed_env P (ffunc fr) env -> frame_good P (enter fr l env).
Proof.
  intros [_ Hav] Hat Hedge Hbind Htyped.
  destruct (jump_env_support _ _ _ _ _ Hbind) as [Hsupport Hparams].
  split; [exact Htyped|]; eapply jump_available; eassumption.
Qed.

Lemma top_replace P fr rest fr' : Forall (frame_good P) (fr :: rest) ->
  stack_links P (fr :: rest) -> frame_good P fr' -> ffunc fr' = ffunc fr ->
  Forall (frame_good P) (fr' :: rest) /\ stack_links P (fr' :: rest).
Proof.
  intros Hframes Hlinks Hgood Hfunc; inversion Hframes as [|? ? Hfr Hrest]; subst.
  split; [constructor; assumption|]; destruct rest as [|caller rest]; [exact I|].
  destruct Hlinks as [Hlink Hlinks]; split; [|exact Hlinks].
  eapply return_link_child; eassumption.
Qed.

Lemma initial_good ext P s : wf_program ext P -> ssa_initial P s -> state_good P s.
Proof.
  intros Hwf [fd [b [vs [env [Hf [Hb [Htypes [Hvalid [Hbind ->]]]]]]]]].
  cbn [state_good stack stack_links]; split; [|exact I]; constructor; [|constructor].
  split.
  - eapply bind_params_typed; try eassumption.
    + intros x v Hnone; discriminate.
    + exact (proj1 (wf_block ext P _ _ _ _ Hwf Hf Hb)).
  - apply (entry_available P (main P) fd b env 0%nat Hf Hb).
    exact (proj2 (bind_params_support _ _ _ _ Hbind)).
Qed.

Lemma operation_good ext P fr x o args cs v : wf_program ext P -> frame_good P fr ->
  at_instr P fr (IOp x o args) -> read_args (fenv fr) args = Some cs ->
  op_eval ext o cs = Some v -> frame_good P (advance fr (env_set (fenv fr) x v)).
Proof.
  intros Hwf Hgood Hat Hread Heval.
  pose proof (wf_instruction ext P fr _ Hwf Hat) as Hlocal.
  unfold instr_typed, instr_sig, instr_sig_with in Hlocal; cbn beta iota zeta in Hlocal.
  destruct (op_sig P o) as [[ps r]|] eqn:Hsig; [|contradiction].
  destruct Hlocal as [Htypes Hresult]; cbn [instr_uses result_has_type] in *.
  destruct (read_args_typed P _ _ _ _ _ (proj1 Hgood) Hread Htypes) as [Hcs Hvalid].
  destruct Hwf as [Hmain [Hnames [Hdefs [Hfunctions Hext]]]].
  pose proof (proj1 (op_eval_typed ext P o cs ps r Hext Hsig Hcs Hvalid) v Heval) as Hv.
  eapply assign_advance_good; try eassumption; [reflexivity| |].
  - rewrite Hv; exact Hresult.
  - eapply op_eval_valid; eassumption.
Qed.

Lemma allocation_good ext P fr x n nb : wf_program ext P -> frame_good P fr ->
  at_instr P fr (IAlloc x n) ->
  frame_good P (advance fr (env_set (fenv fr) x (VPtr nb 0))).
Proof.
  intros Hwf Hgood Hat; pose proof (wf_instruction ext P fr _ Hwf Hat) as Hlocal.
  destruct Hlocal as [_ Hresult]; cbn [result_has_type] in Hresult.
  eapply assign_advance_good; try eassumption; [reflexivity|exact I].
Qed.

Lemma load_good ext P fr x t sz p mb off v : wf_program ext P -> frame_good P fr ->
  at_instr P fr (ILoad x t sz p) -> memory_load t sz mb off = Some v ->
  frame_good P (advance fr (env_set (fenv fr) x v)).
Proof.
  intros Hwf Hgood Hat Hload; pose proof (wf_instruction ext P fr _ Hwf Hat) as Hlocal.
  unfold instr_typed, instr_sig, instr_sig_with in Hlocal; cbn beta iota zeta in Hlocal.
  destruct (load_ok t sz); [|contradiction].
  destruct Hlocal as [_ Hresult]; cbn [result_has_type] in Hresult.
  destruct (memory_load_typed _ _ _ _ _ Hload) as [Htype Hvalid].
  eapply assign_advance_good; try eassumption; [reflexivity|rewrite Htype; exact Hresult].
Qed.

Lemma ordinary_jump_good ext P fr t l args cs env fd : wf_program ext P ->
  frame_good P fr -> at_term P fr t -> find_func P (ffunc fr) = Some fd ->
  Forall (typed_jump (find_block fd) (static_ty P (ffunc fr))) (term_edges t) ->
  In (l, args) (term_edges t) -> read_args (fenv fr) args = Some cs ->
  jump_env P fr l cs = Some env -> frame_good P (enter fr l env).
Proof.
  intros Hwf Hgood Hat Hf Htyped Hedge Hread Hbind.
  eapply jump_good; try eassumption.
  - exact (in_map fst (term_edges t) (l, args) Hedge).
  - eapply typed_jump_env; try eassumption; [exact (proj1 Hgood)|].
    exact (proj1 (Forall_forall _ _) Htyped (l, args) Hedge).
Qed.

Lemma call_good ext P fr c args cont cs f fd b env : wf_program ext P -> frame_good P fr ->
  at_term P fr (TCall c args cont) -> read_args (fenv fr) args = Some cs ->
  callee_def P (fenv fr) c = Some (f, fd, b) ->
  bind_params (fun _ => None) (bparams b) cs = Some env ->
  frame_good P (SFrame f (fentry fd) 0 env 0%nat) /\
  return_link P (SFrame f (fentry fd) 0 env 0%nat)
    (SFrame (ffunc fr) (flabel fr) (fpc fr) (fenv fr) cont).
Proof.
  intros Hwf Hgood Hat Hread Hcall Hbind.
  destruct (call_typed ext P fr c args cont Hwf Hat) as
    [callerfd [ps [r [contb [Hcaller [Hsig [Hcont [Hargs Hparam]]]]]]]].
  destruct (callee_def_target _ _ _ _ _ _ Hcall) as [Hf [Hb Hmatches]].
  destruct (Hmatches _ _ _ Hsig) as [Hps Hr].
  destruct (read_args_typed P _ _ _ _ _ (proj1 Hgood) Hread Hargs) as [Hcs Hvalid].
  split.
  - split.
    + eapply bind_params_typed; try eassumption.
      * intros x v Hnone; discriminate.
      * exact (proj1 (wf_block ext P _ _ _ _ Hwf Hf Hb)).
      * rewrite <- Hps; exact Hcs.
    + apply (entry_available P f fd b env 0%nat Hf Hb).
      exact (proj2 (bind_params_support _ _ _ _ Hbind)).
  - exists fd, c, args, cont, ps; cbn; split; [exact Hf|].
    split; [exact Hat|]; split; [reflexivity|rewrite <- Hr; exact Hsig].
Qed.

Lemma return_good ext P fr caller x v env : wf_program ext P -> frame_good P fr ->
  frame_good P caller -> return_link P fr caller -> at_term P fr (TRet x) ->
  fenv fr x = Some v -> jump_env P caller (fret caller) [v] = Some env ->
  frame_good P (enter caller (fret caller) env).
Proof.
  intros Hwf Hfr Hcaller [childfd [c [args [cont [ps [Hchild [Hcall [Hret Hsig]]]]]]]]
    Hat Hvalue Hbind.
  destruct (wf_terminator ext P fr _ Hwf Hat) as [fd [Hf Htyped]].
  rewrite Hchild in Hf; injection Hf as <-.
  cbn [term_typed] in Htyped.
  destruct (proj1 Hfr x v Hvalue) as [Hv Hvalid]; rewrite Hv in Htyped.
  injection Htyped as Htype.
  destruct (call_typed ext P caller c args cont Hwf Hcall) as
    [callerfd [ps' [r [b [Hf [Hsig' [Hb [Hargs Hparams]]]]]]]].
  rewrite Hsig in Hsig'; injection Hsig' as <- <-.
  eapply jump_good; try eassumption.
  - rewrite Hret; cbn [term_edges map]; left; reflexivity.
  - eapply jump_env_typed; try eassumption; [exact (proj1 Hcaller)| |].
    + intros fd' b' Hf' Hb'; rewrite Hf in Hf'; injection Hf' as <-.
      rewrite Hret, Hb in Hb'; injection Hb' as <-; cbn; rewrite Hparams, Htype; reflexivity.
    + constructor; [exact Hvalid|constructor].
Qed.

Lemma step_good ext P lim s events t : wf_program ext P -> state_good P s ->
  step_s ext P lim s events t -> state_good P t.
Proof.
  intros Hwf Hgood Hstep; destruct Hstep as
    [fr k m nb x o args cs v Hat Hread Heval
    |fr k m nb x n z Hat Hsize Hlimit
    |fr k m nb p b mb Hat Hptr Hblock Hlive
    |fr k m nb x ty sz p b off mb v Hat Hptr Hblock Hload
    |fr k m nb sz p x b off mb v mb' Hat Hptr Hvalue Hblock Hstore
    |fr k m nb x v Hat Hvalue
    |fr k m nb l args cs env Hat Hread Hbind
    |fr k m nb c l1 a1 l2 a2 z l args cs env Hat Hcond Hchoice Hread Hbind
    |fr k m nb c cases d da z l args cs env Hat Hcond Hchoice Hread Hbind
    |fr k m nb c args cont cs f fd b env Hat Hread Hcall Hbind Hlimit
    |fr caller k m nb x v env Hat Hvalue Hbind
    |fr m nb x v Hat Hvalue];
    destruct Hgood as [Hframes Hlinks];
    inversion Hframes as [|? ? Hfr Hrest]; subst;
    cbn [state_good stack].
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    eapply operation_good; eassumption.
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    eapply allocation_good; eassumption.
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    eapply unchanged_advance_good; [exact Hfr|exact Hat|reflexivity].
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    eapply load_good; eassumption.
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    eapply unchanged_advance_good; [exact Hfr|exact Hat|reflexivity].
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    eapply unchanged_advance_good; [exact Hfr|exact Hat|reflexivity].
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    destruct (wf_terminator ext P _ _ Hwf Hat) as [fd [Hf Htyped]].
    eapply (ordinary_jump_good ext P fr (TJump l args) l args cs env fd);
      try eassumption; cbn [term_edges]; left; reflexivity.
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    destruct (wf_terminator ext P _ _ Hwf Hat) as [fd [Hf [_ Htyped]]].
    eapply (ordinary_jump_good ext P fr (TBr c l1 a1 l2 a2) l args cs env fd);
      try eassumption.
    change (In (l, args) [(l1, a1); (l2, a2)]).
    rewrite Hchoice; destruct (z =? 0)%Z; cbn; auto.
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    destruct (wf_terminator ext P _ _ Hwf Hat) as [fd [Hf [_ Htyped]]].
    eapply (ordinary_jump_good ext P fr (TSwitch c cases d da) l args cs env fd);
      try eassumption.
    exact (switch_target_edge _ _ _ _ _ _ Hchoice).
  - destruct (call_good ext P _ _ _ _ _ _ _ _ _ Hwf Hfr Hat Hread Hcall Hbind)
      as [Hchild Hlink].
    assert (Hcaller : frame_good P
      (SFrame (ffunc fr) (flabel fr) (fpc fr) (fenv fr) cont)) by exact Hfr.
    split.
    + constructor; [exact Hchild|constructor; assumption].
    + split; [exact Hlink|].
      exact (proj2 (top_replace P fr k _ Hframes Hlinks Hcaller eq_refl)).
  - inversion Hrest as [|? ? Hcaller Htail]; subst.
    destruct Hlinks as [Hlink Hlinks].
    eapply top_replace; [exact Hrest|exact Hlinks| |reflexivity].
    exact (return_good ext P fr caller x v env Hwf Hfr Hcaller Hlink Hat Hvalue Hbind).
  - eapply top_replace; [exact Hframes|exact Hlinks| |reflexivity].
    split; [exact (proj1 Hfr)|eapply past_end_available; [exact Hat|exact (proj2 Hfr)]].
Qed.

Lemma reachable_good ext P lim s : wf_program ext P ->
  reachable_state (ssa_semantics ext P lim) s -> state_good P s.
Proof.
  intros Hwf [s0 [tr [Hinitial Hrun]]].
  assert (Hstart : state_good P s0) by (eapply initial_good; eassumption).
  clear Hinitial.
  revert Hstart; induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intro Hgood.
  - exact Hgood.
  - apply IH; exact (step_good ext P lim s l s' Hwf Hgood Hstep).
Qed.

(** Every frame of a reachable well-formed execution holds only correctly typed valid values. *)
Theorem typed_state_reachable (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (s : state) :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  forall fr, In fr (stack s) -> typed_env P (ffunc fr) (fenv fr).
Proof.
  intros Hwf Hreach fr Hin; destruct (reachable_good _ _ _ _ Hwf Hreach) as [Hframes _].
  exact (proj1 (proj1 (Forall_forall _ _) Hframes fr Hin)).
Qed.

Lemma read_args_exists env xs : env_bound env xs -> exists cs, read_args env xs = Some cs.
Proof.
  induction xs as [|x xs IH]; intro Hbound.
  - exists []; reflexivity.
  - destruct (Hbound x (or_introl eq_refl)) as [v Hv].
    destruct IH as [cs Hcs]; [intros y Hin; apply Hbound; right; exact Hin|].
    exists (v :: cs); cbn [read_args]; rewrite Hv, Hcs; reflexivity.
Qed.

(** Every next operator in every reachable frame has bound operands of its declared signature. *)
Theorem typed_operands (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (s : state) (fr : sframe) (fd : fdef) (b : ssa_block) (x : vid) (o : sop) (args : list vid) :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s -> In fr (stack s) ->
  find_func P (ffunc fr) = Some fd -> find_block fd (flabel fr) = Some b ->
  nth_error (bbody b) (fpc fr) = Some (IOp x o args) ->
  exists cs ps r, Forall2 (fun y c => fenv fr y = Some c) args cs /\
    op_sig P o = Some (ps, r) /\ map ty_of cs = ps /\ Forall valid_cval cs.
Proof.
  intros Hwf Hreach Hin Hf Hb Hnth.
  destruct (reachable_good _ _ _ _ Hwf Hreach) as [Hframes _].
  destruct (proj1 (Forall_forall _ _) Hframes fr Hin) as [Htyped Hav].
  assert (Hat : at_instr P fr (IOp x o args)) by (exists fd, b; repeat split; assumption).
  pose proof (wf_instruction ext P fr _ Hwf Hat) as Hlocal.
  unfold instr_typed, instr_sig, instr_sig_with in Hlocal; cbn beta iota zeta in Hlocal.
  destruct (op_sig P o) as [[ps r]|] eqn:Hsig; [|contradiction].
  destruct Hlocal as [Htypes Hresult].
  destruct (read_args_exists _ args (frame_operands_bound ext P fr _ Hwf Hav Hat)) as [cs Hcs].
  destruct (read_args_typed P _ _ _ _ _ Htyped Hcs Htypes) as [Hmap Hvalid].
  exists cs, ps, r; repeat split; try assumption; apply read_args_sound; exact Hcs.
Qed.

(** Reachable allocation sizes are unsigned 64-bit values, hence define bounded extents. *)
Theorem allocation_size_in_range (ext : nat -> list cval -> option cval) (P : program)
    (lim : limits) (s : state) (fr : sframe) (fd : fdef) (b : ssa_block) (x n : vid) :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s -> In fr (stack s) ->
  find_func P (ffunc fr) = Some fd -> find_block fd (flabel fr) = Some b ->
  nth_error (bbody b) (fpc fr) = Some (IAlloc x n) ->
  exists z, fenv fr n = Some (VInt W64 z) /\ (0 <= z < 2 ^ 64)%Z.
Proof.
  intros Hwf Hreach Hin Hf Hb Hnth.
  destruct (reachable_good _ _ _ _ Hwf Hreach) as [Hframes _].
  destruct (proj1 (Forall_forall _ _) Hframes fr Hin) as [Htyped Hav].
  assert (Hat : at_instr P fr (IAlloc x n)) by (exists fd, b; repeat split; assumption).
  destruct (frame_operands_bound ext P fr _ Hwf Hav Hat n (or_introl eq_refl)) as [v Hv].
  pose proof (wf_instruction ext P fr _ Hwf Hat) as [Htypes Hresult].
  destruct (Htyped n v Hv) as [Htype Hvalid].
  cbn [instr_uses types_of] in Htypes; rewrite Htype in Htypes.
  injection Htypes as Hty; destruct v as [[|] z|bb off|f|z|z];
    cbn in Hty; try discriminate; exists z; split; assumption.
Qed.
