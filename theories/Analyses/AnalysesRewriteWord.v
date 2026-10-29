(** * A word-language Rewrite client

    This client registers word identities and a fact-justified ground division rule.
    For example, a validated singleton fact for seven permits rewriting seven divided by itself.
    Builds on: BitsWord, BitsFun, BitsTestbit, BitsArith and the standalone Rewrite engine. *)

From Stdlib Require Import List Bool ZArith Lia PeanoNat.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteAnalysis RewriteRun RewriteExtract.
Import List.ListNotations.

(** Word operators are ordinary client syntax, including an independently registered rotation. *)
Inductive rw_word_op : Type :=
  | WordLit (z : Z)
  | WordAdd
  | WordMul
  | WordDiv
  | WordRotl.

(** Literal codes are even and the four remaining constructors have distinct odd codes. *)
Definition rw_word_encoding : encoding rw_word_op.
Proof.
  refine (Encoding rw_word_op (fun op =>
    match op with
    | WordLit z => xO (encode Z_encoding z)
    | WordAdd => 1%positive
    | WordMul => 3%positive
    | WordDiv => 5%positive
    | WordRotl => 7%positive
    end) _).
  intros a b; destruct a, b; cbn; intro Hcode; try discriminate; try reflexivity.
  f_equal; apply (encode_injective Z_encoding); now injection Hcode.
Defined.

(** The single-sort signature checks literal and binary-operation arities. *)
Definition rw_word_sig : rw_signature rw_word_op unit nat :=
  RwSignature rw_word_op unit nat (fun _ => Some tt)
    (fun op args _ =>
      match op, args with
      | WordLit _, [] => true
      | WordAdd, [_; _] | WordMul, [_; _] | WordDiv, [_; _] | WordRotl, [_; _] => true
      | _, _ => false
      end).

(** Word evaluation uses Bits at width 32, including its total division-by-zero convention. *)
Definition rw_word_eval (op : rw_word_op) (args : list Z) : option Z :=
  match op, args with
  | WordLit z, [] => Some (wrap 32%positive z)
  | WordAdd, [x; y] => Some (wadd 32%positive x y)
  | WordMul, [x; y] => Some (wmul 32%positive x y)
  | WordDiv, [x; y] => Some (wudiv 32%positive x y)
  | WordRotl, [x; y] => Some (wrotl 32%positive x y)
  | _, _ => None
  end.

(** Admissible interpretations use the word evaluator and bind present variables to words. *)
Definition rw_word_admissible (sem : rw_semantics rw_word_op unit nat Z) : Prop :=
  rw_eval_op sem = rw_word_eval /\
  forall v z, rw_var_value sem v = Some z -> is_word 32%positive z.

(** A ground pattern preserves literal free variables and introduces no substitution holes. *)
Fixpoint rw_ground_pattern {K Sort V H} (t : rw_term K Sort V) : rw_pattern K Sort V H :=
  match t with
  | RWVar s v => RWPVar s v
  | RWApp s op args => RWPApp s op (map rw_ground_pattern args)
  end.

Lemma rw_ground_pattern_sort {K Sort V H} (t : rw_term K Sort V) :
  rwp_sort (@rw_ground_pattern K Sort V H t) = rw_sort t.
Proof.
  destruct t; reflexivity.
Qed.

Lemma rw_ground_pattern_instantiate {K Sort V H} (sub : rw_substitution K Sort V H)
    (t : rw_term K Sort V) : rw_instantiate sub (rw_ground_pattern t) = Some t.
Proof.
  revert t; fix IH 1; intros [s v|s op args]; [reflexivity|].
  change (match rw_instantiate_args sub (map rw_ground_pattern args) with
          | Some ts => Some (RWApp s op ts)
          | None => None
          end = Some (RWApp s op args)).
  assert (Hargs : rw_instantiate_args sub (map rw_ground_pattern args) = Some args).
  { induction args as [|t rest IHrest]; [reflexivity|].
    change (match rw_instantiate sub (rw_ground_pattern t) with
            | None => None
            | Some child =>
              match rw_instantiate_args sub (map rw_ground_pattern rest) with
              | None => None
              | Some children => Some (child :: children)
              end
            end = Some (t :: rest)).
    rewrite IH, IHrest; reflexivity. }
  now rewrite Hargs.
Qed.

Lemma rw_ground_pattern_typed {K Sort V H} (sig : rw_signature K Sort V)
    (hs : H -> option Sort) (t : rw_term K Sort V) :
  rw_typed sig t -> rwp_typed sig hs (rw_ground_pattern t).
Proof.
  revert t; fix IH 2; intros t Htyped; destruct Htyped as [s v Hsort|s op args Hargs Hshape].
  - constructor; exact Hsort.
  - apply rwp_typed_app.
    + clear Hshape; induction Hargs as [|child rest Hchild Hrest IHrest]; cbn [map].
      * constructor.
      * constructor; [exact (IH child Hchild)|exact IHrest].
    + now rewrite map_map, (map_ext _ _ (@rw_ground_pattern_sort K Sort V H)).
Qed.

(** A binary right-identity rule uses one checked hole and an unconditional Boolean condition. *)
Definition rw_word_identity_rule (op : rw_word_op) (z : Z) :
    rw_rule rw_word_op unit nat nat :=
  RwRule rw_word_op unit nat nat [0%nat]
    (fun h => if Nat.eqb h 0 then Some tt else None)
    (RWPApp tt op [RWHole tt 0%nat; RWPApp tt (WordLit z) []]) (RWHole tt 0%nat)
    (fun _ => true).

(** Adding the zero literal preserves the complete option result. *)
Definition rw_word_add_zero : rw_rule rw_word_op unit nat nat :=
  rw_word_identity_rule WordAdd 0%Z.

(** Multiplying by the one literal preserves the complete option result. *)
Definition rw_word_mul_one : rw_rule rw_word_op unit nat nat :=
  rw_word_identity_rule WordMul 1%Z.

(** Rotating left by the zero literal preserves the complete option result. *)
Definition rw_word_rotate_zero : rw_rule rw_word_op unit nat nat :=
  rw_word_identity_rule WordRotl 0%Z.

(** Self-division is registered as a ground rule for the exact fact-validated witness. *)
Definition rw_word_div_self (t : rw_term rw_word_op unit nat) :
    rw_rule rw_word_op unit nat nat :=
  RwRule rw_word_op unit nat nat [] (fun _ => None)
    (RWPApp tt WordDiv [rw_ground_pattern t; rw_ground_pattern t])
    (RWPApp tt (WordLit 1%Z) []) (fun _ => true).

(** A nonzero fact excludes undefined evaluation and guarantees a canonical nonzero word. *)
Definition rw_word_nonzero {F} (an : rw_analysis rw_word_op unit nat Z F) (f : F) : Prop :=
  ~ rw_fact_holds an f None /\
  forall z, rw_fact_holds an f (Some z) -> is_word 32%positive z /\ z <> 0%Z.

(** Singleton facts specify the exact wrapped result, while unknown permits every outcome. *)
Definition rw_word_analysis : rw_analysis rw_word_op unit nat Z (option Z) :=
  RwAnalysis rw_word_op unit nat Z (option Z)
    (fun fact result =>
      match fact with
      | None => True
      | Some z => result = Some (wrap 32%positive z)
      end)
    None (fun a _ => a) (fun _ _ _ => None).

(** The executable nonzero check inspects the canonical word represented by a singleton fact. *)
Definition rw_word_nonzero_check (z : Z) : bool := negb (Z.eqb (wrap 32%positive z) 0%Z).

(** Unknown transfer and left-preserving combination satisfy the fact-validity laws. *)
Theorem rw_word_analysis_laws : rw_analysis_laws rw_word_sig rw_word_admissible rw_word_analysis.
Proof.
  constructor.
  - intro result; exact I.
  - intros f h result Hf Hh; exact Hf.
  - intros g facts c Hwf Hfacts t sem Hrepr Hsem; exact I.
Qed.

(** An accepted singleton check supplies both definedness and a nonzero canonical value. *)
Theorem rw_word_singleton_nonzero (z : Z) : rw_word_nonzero_check z = true ->
  rw_word_nonzero rw_word_analysis (Some z).
Proof.
  unfold rw_word_nonzero_check; rewrite Bool.negb_true_iff, Z.eqb_neq; intro Hnonzero.
  split; [discriminate|].
  intros value Hvalue; cbn [rw_word_analysis] in Hvalue; injection Hvalue as ->.
  split; [apply wrap_is_word|exact Hnonzero].
Qed.

(** A represented literal determines a valid singleton fact for its entire sound class. *)
Theorem rw_word_literal_fact {H} (rules : list (rw_rule rw_word_op unit nat H))
    (g : rw_graph rw_word_op unit nat) (c : rw_id) (z : Z) :
  Forall (rw_rule_sound rw_word_sig rw_word_admissible) rules ->
  rw_graph_sound rw_word_sig rw_word_admissible rules g ->
  rw_represents g c (RWApp tt (WordLit z) []) ->
  rw_fact_valid rw_word_admissible rw_word_analysis g c (Some z).
Proof.
  intros Hrules Hgraph Hliteral t sem Hrepr Hsem.
  pose proof (rw_equal_sound rw_word_sig rw_word_admissible rules Hrules t
    (RWApp tt (WordLit z) []) (Hgraph c t _ Hrepr Hliteral) sem Hsem) as Hequal.
  change (rw_denote sem t = Some (wrap 32%positive z)); rewrite Hequal.
  cbn [rw_denote]; now rewrite (proj1 Hsem).
Qed.

Lemma rw_word_eval_is_word (op : rw_word_op) (args : list Z) (value : Z) :
  rw_word_eval op args = Some value -> is_word 32%positive value.
Proof.
  destruct op; destruct args as [|x [|y [|extra rest]]]; cbn [rw_word_eval];
    intro Hvalue; try discriminate; injection Hvalue as <-;
    first [apply wrap_is_word|apply wudiv_is_word|
      unfold wadd, wmul, wrotl; apply wrap_is_word].
Qed.

Lemma rw_word_denote_is_word (sem : rw_semantics rw_word_op unit nat Z)
    (t : rw_term rw_word_op unit nat) (value : Z) :
  rw_word_admissible sem -> rw_denote sem t = Some value -> is_word 32%positive value.
Proof.
  intros [Heval Hvars]; destruct t as [s v|s op args].
  - apply Hvars.
  - rewrite rw_denote_app; destruct (rw_denote_args sem args) as [values|]; [|discriminate].
    rewrite Heval; apply rw_word_eval_is_word.
Qed.

Lemma rw_word_identity_sound (op : rw_word_op) (z : Z) :
  (forall value, is_word 32%positive value ->
    rw_word_eval op [value; wrap 32%positive z] = Some value) ->
  rw_rule_sound rw_word_sig rw_word_admissible (rw_word_identity_rule op z).
Proof.
  intros Hidentity sub lhs rhs Hsub Hguard Hlhs Hrhs.
  cbn [rw_word_identity_rule rw_lhs rw_rhs rw_instantiate] in Hlhs, Hrhs.
  destruct (sub 0%nat) as [t|] eqn:Hbinding; [|discriminate].
  injection Hlhs as <-; injection Hrhs as <-; intros sem Hsem.
  rewrite rw_denote_app; cbn [rw_denote_args].
  destruct (rw_denote sem t) as [value|] eqn:Hvalue; [|reflexivity].
  cbn [rw_denote]; rewrite (proj1 Hsem); cbn [rw_word_eval].
  apply Hidentity; exact (rw_word_denote_is_word sem t value Hsem Hvalue).
Qed.

(** The add-zero rule follows Bits' right identity on canonical successful results. *)
Theorem rw_word_add_zero_sound : rw_rule_sound rw_word_sig rw_word_admissible rw_word_add_zero.
Proof.
  apply rw_word_identity_sound; intros value Hword; rewrite wrap_0; cbn [rw_word_eval].
  now rewrite wadd_0_r.
Qed.

(** The multiply-one rule follows Bits' right identity on canonical successful results. *)
Theorem rw_word_mul_one_sound : rw_rule_sound rw_word_sig rw_word_admissible rw_word_mul_one.
Proof.
  apply rw_word_identity_sound; intros value Hword; rewrite wrap_1; cbn [rw_word_eval].
  now rewrite wmul_1_r.
Qed.

Lemma rw_word_rotl_zero (value : Z) : is_word 32%positive value ->
  wrotl 32%positive value 0 = value.
Proof.
  intro Hword; unfold wrotl; rewrite wrap_0; cbn.
  rewrite (wrap_id 32%positive value Hword).
  change (wrap 32%positive (value * 1 + value / modulus 32%positive) = value).
  rewrite Z.mul_1_r, Z.div_small by exact Hword.
  rewrite Z.add_0_r; now apply wrap_id.
Qed.

(** The rotation rule follows the zero-amount equation, including partial child failures. *)
Theorem rw_word_rotate_zero_sound :
  rw_rule_sound rw_word_sig rw_word_admissible rw_word_rotate_zero.
Proof.
  apply rw_word_identity_sound; intros value Hword; rewrite wrap_0; cbn [rw_word_eval].
  now rewrite rw_word_rotl_zero.
Qed.

Lemma rw_word_identity_wf (op : rw_word_op) (z : Z) :
  rw_operator_shape rw_word_sig op [tt; tt] tt = true ->
  rw_rule_wf rw_word_sig (rw_word_identity_rule op z).
Proof.
  intro Hshape; split.
  - constructor; [intro Hin; inversion Hin|constructor].
  - split.
    + intro h; cbn [rw_word_identity_rule rw_holes rw_hole_sort].
      destruct h as [|h]; cbn; split; intro Hdomain.
      * exists tt; reflexivity.
      * now left.
      * destruct Hdomain as [Hbad|Hbad]; [discriminate|contradiction].
      * destruct Hdomain as [s Hbad]; discriminate.
    + split.
      * apply rwp_typed_app; [|exact Hshape].
        constructor; [constructor; reflexivity|].
        constructor; [apply rwp_typed_app; [constructor|reflexivity]|constructor].
      * split; [constructor; reflexivity|reflexivity].
Qed.

(** The add-zero rule declares exactly its single hole and preserves its sort. *)
Theorem rw_word_add_zero_wf : rw_rule_wf rw_word_sig rw_word_add_zero.
Proof.
  apply rw_word_identity_wf; reflexivity.
Qed.

(** The multiply-one rule declares exactly its single hole and preserves its sort. *)
Theorem rw_word_mul_one_wf : rw_rule_wf rw_word_sig rw_word_mul_one.
Proof.
  apply rw_word_identity_wf; reflexivity.
Qed.

(** The rotation rule declares exactly its single hole and preserves its sort. *)
Theorem rw_word_rotate_zero_wf : rw_rule_wf rw_word_sig rw_word_rotate_zero.
Proof.
  apply rw_word_identity_wf; reflexivity.
Qed.

(** A typed exact witness gives a well-formed ground self-division rule. *)
Theorem rw_word_div_self_wf (t : rw_term rw_word_op unit nat) :
  rw_typed rw_word_sig t -> rw_rule_wf rw_word_sig (rw_word_div_self t).
Proof.
  intro Htyped; split; [constructor|]; split.
  - intro h; split; [contradiction|intros [s Hbad]; discriminate].
  - split.
    + apply rwp_typed_app.
      * constructor; [now apply rw_ground_pattern_typed|].
        constructor; [now apply rw_ground_pattern_typed|constructor].
      * destruct (rwp_sort (@rw_ground_pattern rw_word_op unit nat nat t)); reflexivity.
    + split; [apply rwp_typed_app; [constructor|reflexivity]|reflexivity].
Qed.

(** A valid nonzero fact for the exact represented witness justifies its ground division rule. *)
Theorem rw_word_div_self_sound {F} (an : rw_analysis rw_word_op unit nat Z F) (f : F)
    (g : rw_graph rw_word_op unit nat) (c : rw_id) (t : rw_term rw_word_op unit nat) :
  rw_word_nonzero an f -> rw_fact_valid rw_word_admissible an g c f -> rw_represents g c t ->
  rw_rule_sound rw_word_sig rw_word_admissible (rw_word_div_self t).
Proof.
  intros [Hdefined Hnonzero] Hvalid Hrepr sub lhs rhs Hsub Hguard Hlhs Hrhs.
  change (rw_instantiate sub (RWPApp tt WordDiv [rw_ground_pattern t; rw_ground_pattern t]) =
    Some lhs) in Hlhs.
  rewrite rw_instantiate_app in Hlhs.
  cbn [rw_instantiate_args] in Hlhs; rewrite rw_ground_pattern_instantiate in Hlhs.
  cbn in Hlhs; injection Hlhs as <-.
  change (Some (RWApp tt (WordLit 1%Z) []) = Some rhs) in Hrhs; injection Hrhs as <-.
  intros sem Hsem; pose proof (Hvalid t sem Hrepr Hsem) as Hfact.
  rewrite rw_denote_app; cbn [rw_denote_args].
  destruct (rw_denote sem t) as [value|] eqn:Hvalue.
  - destruct (Hnonzero value Hfact) as [Hword Hnotzero].
    rewrite (proj1 Hsem); cbn [rw_word_eval rw_denote]; rewrite (proj1 Hsem).
    cbn [rw_word_eval]; rewrite wrap_1, wudiv_spec by assumption.
    now rewrite Z.div_same by exact Hnotzero.
  - exact (False_rect _ (Hdefined Hfact)).
Qed.

(** * Direct one-attempt demonstrations *)

(** Literals cost one and the other word constructors cost two. *)
Definition rw_word_cost (op : rw_word_op) : nat :=
  match op with
  | WordLit _ => 1
  | _ => 2
  end.

(** A demo interns its source, runs one binary-fuel attempt and extracts at the original root. *)
Definition rw_word_demo_run (rule : rw_rule rw_word_op unit nat nat)
    (input : rw_term rw_word_op unit nat) (bindings : Map.t nat (rw_term rw_word_op unit nat)) :
    option (rw_term rw_word_op unit nat) :=
  let '(g, root) := rw_add rw_word_encoding unit_encoding nat_encoding rw_empty input in
  let attempt := RwAttempt 0%nat root bindings in
  let result := rw_run rw_word_encoding unit_encoding nat_encoding nat_encoding rw_word_sig
    [rule] (fun _ => Some attempt) 1%N g in
  rw_extract_tree rw_word_encoding unit_encoding nat_encoding (fun _ => 1%nat) rw_word_cost
    (rw_run_graph result) root.

(** The add demo directly rewrites seven plus zero to the represented literal seven. *)
Definition rw_word_demo_add : option (rw_term rw_word_op unit nat) :=
  let seven := RWApp tt (WordLit 7%Z) [] in
  rw_word_demo_run rw_word_add_zero (RWApp tt WordAdd [seven; RWApp tt (WordLit 0%Z) []])
    (Map.set nat_encoding 0%nat seven Map.empty).

(** The multiplication demo directly rewrites seven times one to the represented literal seven. *)
Definition rw_word_demo_mul : option (rw_term rw_word_op unit nat) :=
  let seven := RWApp tt (WordLit 7%Z) [] in
  rw_word_demo_run rw_word_mul_one (RWApp tt WordMul [seven; RWApp tt (WordLit 1%Z) []])
    (Map.set nat_encoding 0%nat seven Map.empty).

(** The extension demo directly rewrites rotation of seven by zero to the literal seven. *)
Definition rw_word_demo_rotate : option (rw_term rw_word_op unit nat) :=
  let seven := RWApp tt (WordLit 7%Z) [] in
  rw_word_demo_run rw_word_rotate_zero (RWApp tt WordRotl [seven; RWApp tt (WordLit 0%Z) []])
    (Map.set nat_encoding 0%nat seven Map.empty).

(** Division registration tests the singleton fact before constructing a ground rule. *)
Definition rw_word_register_division (z : Z) : option (rw_rule rw_word_op unit nat nat) :=
  if rw_word_nonzero_check z then Some (rw_word_div_self (RWApp tt (WordLit z) [])) else None.

(** The division producer attempts only a rule that passed the singleton's nonzero check. *)
Definition rw_word_demo_division (z : Z) : option (rw_term rw_word_op unit nat) :=
  match rw_word_register_division z with
  | None => None
  | Some rule =>
    let value := RWApp tt (WordLit z) [] in
    rw_word_demo_run rule (RWApp tt WordDiv [value; value]) Map.empty
  end.

(** Seven's validated nonzero singleton enables the direct self-division demo. *)
Definition rw_word_demo_div : option (rw_term rw_word_op unit nat) := rw_word_demo_division 7%Z.

(** Zero fails registration, so the rejected demo runs no division attempt. *)
Definition rw_word_demo_zero : option (rw_term rw_word_op unit nat) := rw_word_demo_division 0%Z.

(** Registered division rules are justified by a valid literal fact, not an arbitrary guard. *)
Lemma rw_word_register_division_sound (z : Z) (rule : rw_rule rw_word_op unit nat nat) :
  rw_word_register_division z = Some rule -> rw_rule_sound rw_word_sig rw_word_admissible rule.
Proof.
  unfold rw_word_register_division; destruct (rw_word_nonzero_check z) eqn:Hcheck;
    intro Hregistered; [injection Hregistered as <-|discriminate].
  assert (Htyped : rw_typed rw_word_sig (RWApp tt (WordLit z) [])).
  { apply rw_typed_app; [constructor|reflexivity]. }
  pose proof (rw_add_correct rw_word_encoding unit_encoding nat_encoding rw_word_sig
    rw_word_admissible ([] : list (rw_rule rw_word_op unit nat nat)) rw_empty
    (RWApp tt (WordLit z) []) (rw_empty_wf rw_word_sig)
    (rw_empty_sound rw_word_sig rw_word_admissible []) rw_empty_productive Htyped) as Hadded.
  destruct (rw_add rw_word_encoding unit_encoding nat_encoding rw_empty (RWApp tt (WordLit z) []))
    as [g root].
  destruct Hadded as [Hwf [Hsound [Hproductive [Hextends Hrepr]]]].
  apply (rw_word_div_self_sound rw_word_analysis (Some z) g root).
  - now apply rw_word_singleton_nonzero.
  - apply (@rw_word_literal_fact nat [] g root z); [constructor|exact Hsound|exact Hrepr].
  - exact Hrepr.
Qed.

(** Registered division rules also retain the exact ground rule's typing. *)
Lemma rw_word_register_division_wf (z : Z) (rule : rw_rule rw_word_op unit nat nat) :
  rw_word_register_division z = Some rule -> rw_rule_wf rw_word_sig rule.
Proof.
  unfold rw_word_register_division; destruct (rw_word_nonzero_check z); intro Hregistered;
    [injection Hregistered as <-|discriminate].
  apply rw_word_div_self_wf; apply rw_typed_app; [constructor|reflexivity].
Qed.

(** The direct demo runner preserves semantics and the original root's additive tree cost. *)
Lemma rw_word_demo_run_sound (rule : rw_rule rw_word_op unit nat nat)
    (input output : rw_term rw_word_op unit nat)
    (bindings : Map.t nat (rw_term rw_word_op unit nat)) :
  rw_rule_wf rw_word_sig rule -> rw_rule_sound rw_word_sig rw_word_admissible rule ->
  rw_typed rw_word_sig input -> rw_word_demo_run rule input bindings = Some output ->
  rw_equiv rw_word_admissible input output /\
  (rw_tree_cost (fun _ => 1%nat) rw_word_cost output <=
    rw_tree_cost (fun _ => 1%nat) rw_word_cost input)%nat.
Proof.
  intros Hrulewf Hrulesound Htyped Houtput.
  assert (Hrules : Forall (rw_rule_sound rw_word_sig rw_word_admissible) [rule]).
  { constructor; [exact Hrulesound|constructor]. }
  assert (Hruleswf : Forall (rw_rule_wf rw_word_sig) [rule]).
  { constructor; [exact Hrulewf|constructor]. }
  pose proof (rw_add_correct rw_word_encoding unit_encoding nat_encoding rw_word_sig
    rw_word_admissible [rule] rw_empty input (rw_empty_wf rw_word_sig)
    (rw_empty_sound rw_word_sig rw_word_admissible [rule]) rw_empty_productive Htyped) as Hadded.
  unfold rw_word_demo_run in Houtput.
  destruct (rw_add rw_word_encoding unit_encoding nat_encoding rw_empty input) as [g root].
  destruct Hadded as [Hwf [Hsound [Hproductive [Hextends Hrepr]]]].
  pose proof (rw_run_correct rw_word_encoding unit_encoding nat_encoding nat_encoding rw_word_sig
    rw_word_admissible [rule] (fun _ => Some (RwAttempt 0%nat root bindings)) 1%N g
    Hruleswf Hrules Hwf Hsound Hproductive) as Hrun.
  destruct Hrun as [Hrunwf [Hrunsound [Hrunproductive Hrunextends]]].
  eapply (rw_extract_tree_equiv rw_word_encoding unit_encoding nat_encoding rw_word_sig
    rw_word_admissible [rule] (fun _ => 1%nat) rw_word_cost).
  - exact Hrules.
  - exact Hrunwf.
  - exact Hrunsound.
  - exact (Hrunextends root input Hrepr).
  - exact Houtput.
Qed.
