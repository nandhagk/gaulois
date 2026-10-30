(** * NaN observability

    Five demands distinguish unused values, NaN identity, sign, payload and complete patterns.
    For example, less-than ignores both the sign and the payload of every NaN operand.
    Builds on: FloatOps, demand dictionaries and checked SSA continuation structure. *)

From Stdlib Require Import Bool List ZArith Lia.
From Flocq Require Import Core IEEE754.BinarySingleNaN IEEE754.Binary.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Views Require Import ViewsAgreement.
From Gaulois.Analyses Require Import AnalysesDemand.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaTypingProofs ExamplesSsaBridge ExamplesSsaViews.
From Gaulois.Float Require Import FloatOps.
Import List.ListNotations.
Local Open Scope nat_scope.

(** Bottom needs no value; every other demand observes non-NaN values exactly. *)
Inductive nan_demand : Type :=
  | NotDemanded
  | Demanded (sign payload : bool).

(** NaN fields are compared only when selected, while non-NaNs are compared exactly. *)
Definition ff_agree (sg pl : bool) (a b : full_float) : Prop :=
  match a, b with
  | F754_nan s1 p1, F754_nan s2 p2 =>
    (sg = true -> s1 = s2) /\ (pl = true -> p1 = p2)
  | F754_nan _ _, _ => False
  | _, F754_nan _ _ => False
  | _, _ => a = b
  end.

Definition nan_leb (a b : nan_demand) : bool :=
  match a, b with
  | NotDemanded, _ => true
  | Demanded _ _, NotDemanded => false
  | Demanded sg pl, Demanded sg' pl' => implb sg sg' && implb pl pl'
  end.

Definition nan_join (a b : nan_demand) : nan_demand :=
  match a, b with
  | NotDemanded, _ => b
  | _, NotDemanded => a
  | Demanded sg pl, Demanded sg' pl' => Demanded (sg || sg') (pl || pl')
  end.

Definition nan_lattice : lattice nan_demand :=
  {| leb := nan_leb;
     bot := NotDemanded;
     join := nan_join;
     widen := nan_join;
     narrow := fun a _ => a |}.

(** Bottom contributes no raw operand demand; sign or payload demand needs both operands fully. *)
Definition nan_back (o : fbop) (d : nan_demand) : nan_demand * nan_demand :=
  match d with
  | NotDemanded => (NotDemanded, NotDemanded)
  | Demanded sg pl =>
    let input := match o with
      | FLt => Demanded false false
      | FArith _ => if sg || pl then Demanded true true else Demanded false false
      end in
    (input, input)
  end.

Lemma ff_agree_refl sg pl a : ff_agree sg pl a a.
Proof.
  destruct a; cbn; auto.
Qed.

Lemma ff_agree_sym sg pl a b : ff_agree sg pl a b -> ff_agree sg pl b a.
Proof.
  destruct a, b; cbn; intuition congruence.
Qed.

Lemma ff_agree_weaken sg pl sg' pl' a b :
  (sg = true -> sg' = true) -> (pl = true -> pl' = true) ->
  ff_agree sg' pl' a b -> ff_agree sg pl a b.
Proof.
  destruct a, b; cbn; intuition congruence.
Qed.

Lemma ff_agree_full a b : ff_agree true true a b <-> a = b.
Proof.
  destruct a, b; cbn; intuition congruence.
Qed.

Lemma ff_agree_shape a b : ff_agree false false a b <-> FF2SF a = FF2SF b.
Proof.
  destruct a, b; cbn; intuition congruence.
Qed.

Section Float.
Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}.
Local Abbreviation fl := (binary_float prec emax).

(** The float agreement exposes the selected fields of Flocq's full representation. *)
Definition nan_agree (d : nan_demand) (x y : fl) : Prop :=
  match d with
  | NotDemanded => True
  | Demanded sg pl => ff_agree sg pl (B2FF prec emax x) (B2FF prec emax y)
  end.

(** The five-point demand lattice is paired with its full-float agreement. *)
Definition nan_domain : demand_domain nan_demand fl :=
  DemandDomain nan_lattice (Agreement _ _ nan_agree).

(** The five demands form a lattice with disjunction as join and widening. *)
Theorem nan_lattice_laws : lattice_laws (dlat nan_domain).
Proof.
  constructor; intros;
    repeat match goal with
    | d : nan_demand |- _ => destruct d as [| [] []]
    end; cbn [nan_domain dlat nan_lattice nan_leb nan_join leb bot join widen narrow] in *;
    cbn in *; congruence.
Qed.

(** Agreement is reflexive, antitone, symmetric, and universal at bottom. *)
Theorem nan_domain_laws :
  agreement_laws (dlat nan_domain) (dagree nan_domain) /\
  agreement_symmetric (dagree nan_domain) /\
  (forall u v, agree (dagree nan_domain) (bot (dlat nan_domain)) u v).
Proof.
  split.
  - constructor.
    + intros [|sg pl] x; [exact I|apply ff_agree_refl].
    + intros [|sg pl] [|sg' pl'] x y Hle Hagree; try exact I; try discriminate.
      apply (ff_agree_weaken sg pl sg' pl' _ _); [| |exact Hagree].
      * cbn in Hle; apply andb_true_iff in Hle as [Hsg _].
        exact (proj1 (implb_true_iff sg sg') Hsg).
      * cbn in Hle; apply andb_true_iff in Hle as [_ Hpl].
        exact (proj1 (implb_true_iff pl pl') Hpl).
  - split.
    + intros [|sg pl] x y Hagree; [exact I|apply ff_agree_sym; exact Hagree].
    + intros u v; exact I.
Qed.

Lemma nan_agree_full x y : nan_agree (Demanded true true) x y -> x = y.
Proof.
  intro Hagree; apply B2FF_inj, ff_agree_full; exact Hagree.
Qed.

Lemma nan_agree_refl d x : nan_agree d x x.
Proof.
  destruct d; [exact I|apply ff_agree_refl].
Qed.

Lemma nan_agree_sym d x y : nan_agree d x y -> nan_agree d y x.
Proof.
  destruct d; [intros _; exact I|apply ff_agree_sym].
Qed.

Lemma nan_agree_weaken sg pl sg' pl' x y :
  (sg = true -> sg' = true) -> (pl = true -> pl' = true) ->
  nan_agree (Demanded sg' pl') x y -> nan_agree (Demanded sg pl) x y.
Proof.
  apply ff_agree_weaken.
Qed.

Lemma nan_agree_shape x y : nan_agree (Demanded false false) x y <->
  B2BSN prec emax x = B2BSN prec emax y.
Proof.
  unfold nan_agree; rewrite ff_agree_shape, !FF2SF_B2FF.
  split.
  - intro Heq; apply B2SF_inj; rewrite !B2SF_B2BSN; exact Heq.
  - intro Heq; rewrite <- !B2SF_B2BSN, Heq; reflexivity.
Qed.

Lemma fl_eval_bin_shape (nm : @nan_model prec emax) o x y x' y' :
  B2BSN prec emax x = B2BSN prec emax x' ->
  B2BSN prec emax y = B2BSN prec emax y' ->
  B2BSN prec emax (fl_eval_bin nm o x y) =
  B2BSN prec emax (fl_eval_bin nm o x' y').
Proof.
  intros Hx Hy; unfold fl_eval_bin, Bplus, Bminus, Bmult, Bdiv.
  destruct o; rewrite !B2BSN_BSN2B, Hx, Hy; reflexivity.
Qed.

(** Computed backward demands suffice for every arithmetic NaN model and result demand. *)
Theorem nan_back_sound (nm : @nan_model prec emax) (o : farith) (d : nan_demand)
    (x y x' y' : fl) :
  nan_agree (fst (nan_back (FArith o) d)) x x' ->
  nan_agree (snd (nan_back (FArith o) d)) y y' ->
  nan_agree d (fl_eval_bin nm o x y) (fl_eval_bin nm o x' y').
Proof.
  destruct d as [| [] []]; cbn [nan_back fst snd orb]; intros Hx Hy; try exact I.
  all: try solve [apply nan_agree_full in Hx; apply nan_agree_full in Hy;
    subst x' y'; apply nan_agree_refl].
  apply nan_agree_shape; apply fl_eval_bin_shape; apply nan_agree_shape; assumption.
Qed.

(** Comparison ignores NaN sign and payload while retaining every non-NaN value exactly. *)
Theorem fl_lt_agrees (x y x' y' : fl) :
  nan_agree (Demanded false false) x x' ->
  nan_agree (Demanded false false) y y' -> fl_lt x y = fl_lt x' y'.
Proof.
  intros Hx Hy; apply nan_agree_shape in Hx; apply nan_agree_shape in Hy.
  unfold fl_lt, Bcompare; rewrite Hx, Hy; reflexivity.
Qed.

End Float.

(** * Parameter demand and checked call continuations *)

Definition float_incoming_value (counts : Map.t nat nat) (target : nat) : nat :=
  match Map.get nat_encoding target counts with
  | Some n => n
  | None => 0
  end.

Definition float_count_edge (counts : Map.t nat nat) (edge : label * list vid) :
    Map.t nat nat :=
  Map.set nat_encoding (fst edge) (S (float_incoming_value counts (fst edge))) counts.

Definition float_count_block (counts : Map.t nat nat) (lb : label * ssa_block) :
    Map.t nat nat := fold_left float_count_edge (term_edges (bterm (snd lb))) counts.

Definition float_edge_weight (target : nat) (edges : list (label * list vid)) : nat :=
  fold_right (fun edge n => if Nat.eqb (fst edge) target then S n else n) 0 edges.

Definition float_block_weight (target : nat) (lb : label * ssa_block) : nat :=
  float_edge_weight target (term_edges (bterm (snd lb))).

Definition float_total_incoming (target : nat) (bs : list (label * ssa_block)) : nat :=
  fold_right (fun lb n => float_block_weight target lb + n) 0 bs.

Lemma float_incoming_step counts edge target :
  float_incoming_value (float_count_edge counts edge) target =
    float_incoming_value counts target + (if Nat.eqb (fst edge) target then 1 else 0).
Proof.
  destruct edge as [dst args]; unfold float_count_edge; cbn [fst].
  destruct (Nat.eq_dec target dst) as [->|Hdifferent].
  - unfold float_incoming_value at 1; rewrite Map.get_set_same, Nat.eqb_refl; lia.
  - unfold float_incoming_value at 1; rewrite Map.get_set_other by exact Hdifferent.
    rewrite (proj2 (Nat.eqb_neq dst target) ltac:(congruence)).
    unfold float_incoming_value; lia.
Qed.

Lemma float_incoming_edges counts edges target :
  float_incoming_value (fold_left float_count_edge edges counts) target =
    float_incoming_value counts target + float_edge_weight target edges.
Proof.
  unfold float_edge_weight; revert counts;
    induction edges as [|[dst actual] edges IH]; intro counts;
    cbn [fold_left fold_right fst]; [lia|].
  rewrite IH, float_incoming_step; cbn [fst].
  destruct (Nat.eqb dst target); lia.
Qed.

Lemma float_incoming_blocks counts bs target :
  float_incoming_value (fold_left float_count_block bs counts) target =
    float_incoming_value counts target + float_total_incoming target bs.
Proof.
  unfold float_total_incoming, float_block_weight.
  revert counts; induction bs as [|[l b] bs IH]; intro counts;
    cbn [fold_left float_total_incoming fold_right snd]; [lia|].
  rewrite IH; unfold float_count_block; rewrite float_incoming_edges.
  change (float_incoming_value counts target +
    float_edge_weight target (term_edges (bterm b)) + float_total_incoming target bs =
      float_incoming_value counts target +
        (float_edge_weight target (term_edges (bterm b)) + float_total_incoming target bs)).
  lia.
Qed.

Lemma float_incoming_index fd target :
  float_incoming_value (incoming_index fd) target = float_total_incoming target (blocks fd).
Proof.
  change (float_incoming_value (fold_left float_count_block (blocks fd) Map.empty) target =
    float_total_incoming target (blocks fd)).
  rewrite float_incoming_blocks; unfold float_incoming_value at 1.
  rewrite Map.get_empty; reflexivity.
Qed.

Lemma float_weight_member {A} (weight : A -> nat) rows x : In x rows ->
  weight x <= fold_right (fun y n => weight y + n) 0 rows.
Proof.
  induction rows as [|y rows IH]; cbn; [contradiction|].
  intros [<-|Hin]; [lia|specialize (IH Hin); lia].
Qed.

Lemma float_weight_two {A} (weight : A -> nat) rows x y :
  x <> y -> In x rows -> In y rows -> 1 <= weight x -> 1 <= weight y ->
  2 <= fold_right (fun z n => weight z + n) 0 rows.
Proof.
  induction rows as [|z rows IH]; cbn; [contradiction|].
  intros Hdifferent [Hx|Hx] [Hy|Hy] Hwx Hwy.
  - congruence.
  - subst z; pose proof (float_weight_member weight rows y Hy); lia.
  - subst z; pose proof (float_weight_member weight rows x Hx); lia.
  - specialize (IH Hdifferent Hx Hy Hwx Hwy); lia.
Qed.

Lemma float_edge_weight_member target edges args :
  In (target, args) edges -> 1 <= float_edge_weight target edges.
Proof.
  unfold float_edge_weight; induction edges as [|[dst actual] edges IH];
    cbn [In fold_right fst];
    [contradiction|].
  intros [Heq|Hin].
  - injection Heq as -> ->; rewrite Nat.eqb_refl; lia.
  - specialize (IH Hin); destruct (Nat.eqb dst target); lia.
Qed.

(** An ordinary incoming edge cannot also target a checked call continuation. *)
Lemma float_ordinary_target ext P f fd l b dst args :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  In (dst, args) (term_edges (bterm b)) ->
  (match bterm b with TCall _ _ _ => False | _ => True end) ->
  FinSet.mem nat_encoding dst (ExamplesSsaViews.ssa_call_targets P f) = false.
Proof.
  intros Hwf Hf Hb Hedge Hordinary.
  destruct (FinSet.mem nat_encoding dst (ExamplesSsaViews.ssa_call_targets P f)) eqn:Hcall;
    [|reflexivity].
  exfalso; unfold ExamplesSsaViews.ssa_call_targets in Hcall.
  apply FinSet.of_list_spec in Hcall; apply in_flat_map in Hcall.
  destruct Hcall as [[cl cb] [Hblock Htarget]].
  cbn [snd] in Htarget.
  destruct (bterm cb) as [d actual|c l1 a1 l2 a2|c cases d da|c actual k|x] eqn:Hterm;
    try contradiction.
  destruct Htarget as [Heq|Hfalse]; [subst k|contradiction].
  unfold ssa_blocks in Hblock; rewrite Hf in Hblock.
  assert (Hcb : find_block fd cl = Some cb).
  { apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
      exact Hblock]. }
  pose proof (proj2 (proj2 (proj2 (wf_block ext P f fd cl cb Hwf Hf Hcb)))) as Hcontinuation.
  unfold continuation_ok in Hcontinuation; rewrite Hterm in Hcontinuation.
  assert (Hcount : float_total_incoming dst (blocks fd) = 1).
  { rewrite <- float_incoming_index; unfold float_incoming_value.
    rewrite Hcontinuation; reflexivity. }
  assert (Hdistinct : (l, b) <> (cl, cb)).
  { intro Heq; injection Heq as Hlabel Hbody; subst cb; rewrite Hterm in Hordinary;
      exact Hordinary. }
  pose proof (float_weight_two (float_block_weight dst) (blocks fd) (l, b) (cl, cb)
    Hdistinct (first_index_sound _ _ _ Hb) Hblock
    (float_edge_weight_member dst _ args Hedge)) as Htwo.
  assert (Hcall_weight : 1 <= float_block_weight dst (cl, cb)).
  { unfold float_block_weight; cbn [snd]; rewrite Hterm.
    cbn [term_edges float_edge_weight fold_right fst]; rewrite Nat.eqb_refl; lia. }
  specialize (Htwo Hcall_weight); change (2 <= float_total_incoming dst (blocks fd)) in Htwo.
  lia.
Qed.
