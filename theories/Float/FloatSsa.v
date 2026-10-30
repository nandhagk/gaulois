(** * Floating-point SSA extensions

    Binary32 and binary64 operations interpret the toy language's opaque float bit patterns.
    For example, extension tags zero and one add binary32 and binary64 operands respectively.
    Builds on: FloatNan, Flocq Bits and the SSA activation and analysis views. *)

From Stdlib Require Import Bool List ZArith Lia.
From Flocq Require Import Core IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderPointwise OrderLift.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsAgreement ViewsSsa.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesDemand.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaTypingProofs ExamplesSsaSemantics ExamplesSsaActivation ExamplesSsaBridge
  ExamplesSsaViews ExamplesSsaAnalyses.
From Gaulois.Float Require Import FloatInterval FloatOps FloatNan.
Import List.ListNotations.
Local Open Scope nat_scope.

(** The float extension supports the two IEEE interchange widths. *)
Inductive fw : Type :=
  | F32
  | F64.

(** Adjacent even and odd tags select the two widths for each operation. *)
Definition float_ext_tag (w : fw) (o : fbop) : nat :=
  (2 * match o with
    | FArith FAdd => 0
    | FArith FSub => 1
    | FArith FMul => 2
    | FArith FDiv => 3
    | FLt => 4
    end + match w with F32 => 0 | F64 => 1 end)%nat.

(** Exactly the ten float tags decode; every tag from ten onward is absent. *)
Definition float_ext_decode (tag : nat) : option (fw * fbop) :=
  match tag with
  | 0 => Some (F32, FArith FAdd)
  | 1 => Some (F64, FArith FAdd)
  | 2 => Some (F32, FArith FSub)
  | 3 => Some (F64, FArith FSub)
  | 4 => Some (F32, FArith FMul)
  | 5 => Some (F64, FArith FMul)
  | 6 => Some (F32, FArith FDiv)
  | 7 => Some (F64, FArith FDiv)
  | 8 => Some (F32, FLt)
  | 9 => Some (F64, FLt)
  | _ => None
  end.

Definition float_bits_in_range (width : Z) (bits : Z) : bool :=
  (0 <=? bits)%Z && (bits <? 2 ^ width)%Z.

Definition float_eval32 (nm : @nan_model 24 128) (o : fbop) (a b : Z) : cval :=
  match o with
  | FArith arith =>
    VF32 (bits_of_b32 (@fl_eval_bin 24 128 eq_refl eq_refl nm arith
      (b32_of_bits a) (b32_of_bits b)))
  | FLt => VInt W32 (if fl_lt (b32_of_bits a) (b32_of_bits b) then 1 else 0)
  end.

Definition float_eval64 (nm : @nan_model 53 1024) (o : fbop) (a b : Z) : cval :=
  match o with
  | FArith arith =>
    VF64 (bits_of_b64 (@fl_eval_bin 53 1024 eq_refl eq_refl nm arith
      (b64_of_bits a) (b64_of_bits b)))
  | FLt => VInt W32 (if fl_lt (b64_of_bits a) (b64_of_bits b) then 1 else 0)
  end.

(** Float extension evaluation rejects wrong tags, arities, widths and out-of-range patterns. *)
Definition float_ext (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024)
    (tag : nat) (args : list cval) : option cval :=
  match float_ext_decode tag, args with
  | Some (F32, o), [VF32 a; VF32 b] =>
    if float_bits_in_range 32 a && float_bits_in_range 32 b
    then Some (float_eval32 nm32 o a b) else None
  | Some (F64, o), [VF64 a; VF64 b] =>
    if float_bits_in_range 64 a && float_bits_in_range 64 b
    then Some (float_eval64 nm64 o a b) else None
  | _, _ => None
  end.

(** Arithmetic preserves its float width, and every comparison returns a 32-bit integer. *)
Definition float_ext_sigs : list (nat * (list ty * ty)) :=
  [(0, ([TyF32; TyF32], TyF32)); (1, ([TyF64; TyF64], TyF64));
   (2, ([TyF32; TyF32], TyF32)); (3, ([TyF64; TyF64], TyF64));
   (4, ([TyF32; TyF32], TyF32)); (5, ([TyF64; TyF64], TyF64));
   (6, ([TyF32; TyF32], TyF32)); (7, ([TyF64; TyF64], TyF64));
   (8, ([TyF32; TyF32], TyI32)); (9, ([TyF64; TyF64], TyI32))].

(** Decoding an encoded operation recovers its width and operation. *)
Theorem float_ext_tag_decode (w : fw) (o : fbop) :
  float_ext_decode (float_ext_tag w o) = Some (w, o).
Proof.
  destruct w, o as [[]|]; reflexivity.
Qed.

(** Every successful decoding has exactly its canonical tag. *)
Theorem float_ext_decode_tag (tag : nat) (w : fw) (o : fbop) :
  float_ext_decode tag = Some (w, o) -> float_ext_tag w o = tag.
Proof.
  destruct tag as [|[|[|[|[|[|[|[|[|[|tag]]]]]]]]]];
    cbn [float_ext_decode]; intro Hdecode; try discriminate;
    injection Hdecode as <- <-; reflexivity.
Qed.

Definition float_width_ty (w : fw) : ty :=
  match w with
  | F32 => TyF32
  | F64 => TyF64
  end.

Definition float_result_ty (w : fw) (o : fbop) : ty :=
  match o with
  | FArith _ => float_width_ty w
  | FLt => TyI32
  end.

Lemma float_signature_decode tag ps r : In (tag, (ps, r)) float_ext_sigs ->
  exists w o, float_ext_decode tag = Some (w, o) /\
    ps = [float_width_ty w; float_width_ty w] /\ r = float_result_ty w o.
Proof.
  unfold float_ext_sigs; cbn; intro Hin.
  repeat (destruct Hin as [Heq|Hin];
    [injection Heq as <- <- <-; eexists; eexists; repeat split; reflexivity|]).
  contradiction.
Qed.

Lemma float_eval32_typed nm o a b :
  ty_of (float_eval32 nm o a b) = float_result_ty F32 o /\
  valid_cval (float_eval32 nm o a b).
Proof.
  destruct o as [arith|]; cbn [float_eval32 float_result_ty float_width_ty ty_of valid_cval].
  - split; [reflexivity|exact I].
  - destruct (fl_lt (b32_of_bits a) (b32_of_bits b)); split; [reflexivity|lia|
      reflexivity|lia].
Qed.

Lemma float_eval64_typed nm o a b :
  ty_of (float_eval64 nm o a b) = float_result_ty F64 o /\
  valid_cval (float_eval64 nm o a b).
Proof.
  destruct o as [arith|]; cbn [float_eval64 float_result_ty float_width_ty ty_of valid_cval].
  - split; [reflexivity|exact I].
  - destruct (fl_lt (b64_of_bits a) (b64_of_bits b)); split; [reflexivity|lia|
      reflexivity|lia].
Qed.

Section FloatSsaTheorems.
Context (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024).
Local Abbreviation fx := (float_ext nm32 nm64).

(** Successful extension evaluation has the declared result type and a valid result value. *)
Theorem float_ext_respects (P : program) :
  ext_sigs P = float_ext_sigs -> ext_respects fx P.
Proof.
  intros Hsigs tag ps r cs v Hin Htypes Hvalid Heval.
  rewrite Hsigs in Hin; apply float_signature_decode in Hin as [w [o [Hdecode [Hps Hr]]]].
  subst ps r; unfold fx, float_ext in Heval; rewrite Hdecode in Heval.
  destruct cs as [|a [|b [|c rest]]]; try discriminate.
  destruct w; destruct a as [wa za|ba oa|fa|a32|a64];
    destruct b as [wb zb|bb ob|fb|b32|b64]; try discriminate.
  - destruct (float_bits_in_range 32 a32 && float_bits_in_range 32 b32);
      try discriminate; injection Heval as <-; apply float_eval32_typed.
  - destruct (float_bits_in_range 64 a64 && float_bits_in_range 64 b64);
      try discriminate; injection Heval as <-; apply float_eval64_typed.
Qed.

End FloatSsaTheorems.

Definition nan_cval_agree (sg pl : bool) (u v : cval) : Prop :=
  match u, v with
  | VF32 a, VF32 b =>
    if float_bits_in_range 32 a && float_bits_in_range 32 b
    then nan_agree (Demanded sg pl) (b32_of_bits a) (b32_of_bits b) else u = v
  | VF64 a, VF64 b =>
    if float_bits_in_range 64 a && float_bits_in_range 64 b
    then nan_agree (Demanded sg pl) (b64_of_bits a) (b64_of_bits b) else u = v
  | _, _ => u = v
  end.

Definition nan_option_agree (d : nan_demand) (u v : option cval) : Prop :=
  match d with
  | NotDemanded => True
  | Demanded sg pl =>
    match u, v with
    | Some a, Some b => nan_cval_agree sg pl a b
    | _, _ => u = v
    end
  end.

(** The SSA boundary agrees universally at bottom and distinguishes missing demanded values. *)
Definition nan_domain_ssa : demand_domain nan_demand (option cval) :=
  DemandDomain nan_lattice (Agreement _ _ nan_option_agree).

Lemma nan_cval_refl sg pl u : nan_cval_agree sg pl u u.
Proof.
  destruct u; cbn [nan_cval_agree]; try reflexivity.
  - destruct (float_bits_in_range 32 bits && float_bits_in_range 32 bits);
      [apply nan_agree_refl|reflexivity].
  - destruct (float_bits_in_range 64 bits && float_bits_in_range 64 bits);
      [apply nan_agree_refl|reflexivity].
Qed.

Lemma nan_cval_sym sg pl u v : nan_cval_agree sg pl u v -> nan_cval_agree sg pl v u.
Proof.
  destruct u as [wu zu|bu ou|fu|a32|a64]; destruct v as [wv zv|bv ov|fv|b32|b64];
    cbn [nan_cval_agree]; try (intro Heq; symmetry; exact Heq).
  - rewrite (andb_comm (float_bits_in_range 32 b32) (float_bits_in_range 32 a32)).
    destruct (float_bits_in_range 32 a32 && float_bits_in_range 32 b32);
      [apply nan_agree_sym|intro Heq; symmetry; exact Heq].
  - rewrite (andb_comm (float_bits_in_range 64 b64) (float_bits_in_range 64 a64)).
    destruct (float_bits_in_range 64 a64 && float_bits_in_range 64 b64);
      [apply nan_agree_sym|intro Heq; symmetry; exact Heq].
Qed.

Lemma nan_cval_weaken sg pl sg' pl' u v :
  (sg = true -> sg' = true) -> (pl = true -> pl' = true) ->
  nan_cval_agree sg' pl' u v -> nan_cval_agree sg pl u v.
Proof.
  intros Hsg Hpl; destruct u as [wu zu|bu ou|fu|a32|a64];
    destruct v as [wv zv|bv ov|fv|b32|b64]; cbn [nan_cval_agree]; try tauto.
  - destruct (float_bits_in_range 32 a32 && float_bits_in_range 32 b32); [|tauto].
    apply nan_agree_weaken; assumption.
  - destruct (float_bits_in_range 64 a64 && float_bits_in_range 64 b64); [|tauto].
    apply nan_agree_weaken; assumption.
Qed.

(** The lifted option agreement has the same lattice and agreement laws as the float domain. *)
Theorem nan_domain_ssa_laws :
  lattice_laws (dlat nan_domain_ssa) /\
  agreement_laws (dlat nan_domain_ssa) (dagree nan_domain_ssa) /\
  agreement_symmetric (dagree nan_domain_ssa) /\
  (forall u v, agree (dagree nan_domain_ssa) (bot (dlat nan_domain_ssa)) u v).
Proof.
  split; [exact (@nan_lattice_laws 24 128)|]; split.
  - constructor.
    + intros [|sg pl] [u|]; cbn [nan_option_agree]; try exact I; try reflexivity.
      apply nan_cval_refl.
    + intros [|sg pl] [|sg' pl'] u v Hle Hagree; try exact I; try discriminate.
      cbn in Hle; apply andb_true_iff in Hle as [Hsg Hpl].
      destruct u as [u|], v as [v|]; cbn [nan_option_agree] in *; try exact Hagree.
      apply (nan_cval_weaken sg pl sg' pl' u v); [| |exact Hagree].
      * exact (proj1 (implb_true_iff sg sg') Hsg).
      * exact (proj1 (implb_true_iff pl pl') Hpl).
  - split.
    + intros [|sg pl] [u|] [v|] Hagree; try exact I;
        cbn [nan_option_agree] in *; try (symmetry; exact Hagree).
      apply nan_cval_sym; exact Hagree.
    + intros u v; exact I.
Qed.

Definition float_trap_shape_index (P : program) (f : func) : Map.t ssa_edge (list vid) :=
  Map.of_list ssa_edge_encoding (flat_map (fun lb =>
    flat_map (fun pi => match snd pi with
      | IOp _ (OExt _) args => [(SsaEdge (fst lb) (fst lb) (fst pi), args)]
      | _ => []
      end) (ssa_enumerate 0 (bbody (snd lb)))) (ssa_blocks P f)).

Definition nan_forward_pairs (d : nan_demand) (pairs : list (vid * bool)) :
    list (vid * nan_demand) := map (fun yd => (fst yd, d)) pairs.

Definition nan_op_back (o : sop) (args : list vid) (d : nan_demand) :
    list (vid * nan_demand) :=
  match d with
  | NotDemanded => []
  | Demanded _ _ => match o, args with
    | OExt tag, [a1; a2] => match float_ext_decode tag with
      | Some (_, b) => let '(d1, d2) := nan_back b d in [(a1, d1); (a2, d2)]
      | None => map (fun y => (y, Demanded true true)) args
      end
    | _, _ => map (fun y => (y, Demanded true true)) args
    end
  end.

(** Parameter demands retain every raw selected input in its original order and multiplicity. *)
Definition ssa_nan_demand_view (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
    demand_view astate event (label * nat) ssa_edge vid (option cval) nan_demand :=
  let raw := ssa_demand_view ext P f in
  let sv := ssa_block_view ext P f in
  let shape := float_trap_shape_index P f in
  let full := Demanded true true in
  {| dgraph := dgraph raw;
     ddefs := ddefs raw;
     dnec := fun e => nan_forward_pairs full (dnec raw e) ++
       map (fun x => (x, Demanded false false)) (ssa_get ssa_edge_encoding shape [] e);
     dback := fun e x d => match d with
       | NotDemanded => []
       | Demanded sg pl => match def sv x with
         | Op o args => nan_op_back o args d
         | Param _ _ => nan_forward_pairs d (dback raw e x true)
         | Arbitrary => []
         end
       end;
     dexit := fun n => nan_forward_pairs full (dexit raw n);
     dlookup := dlookup raw;
     dvars := dvars raw |}.

Lemma ssa_nan_dback_bottom ext P f e x :
  dback (ssa_nan_demand_view ext P f) e x NotDemanded = [].
Proof.
  reflexivity.
Qed.

Lemma ssa_nan_dback_param ext P f e x b i sg pl :
  def (ssa_block_view ext P f) x = Param b i ->
  dback (ssa_nan_demand_view ext P f) e x (Demanded sg pl) =
    map (fun yd => (fst yd, Demanded sg pl)) (dback (ssa_demand_view ext P f) e x true).
Proof.
  intro Hdef; cbn [ssa_nan_demand_view dback].
  rewrite Hdef; reflexivity.
Qed.

Lemma float_bits_range width bits :
  float_bits_in_range width bits = true <-> (0 <= bits < 2 ^ width)%Z.
Proof.
  unfold float_bits_in_range; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; tauto.
Qed.

Lemma float_decode32_injective a b : float_bits_in_range 32 a = true ->
  float_bits_in_range 32 b = true -> b32_of_bits a = b32_of_bits b -> a = b.
Proof.
  intros Ha Hb Heq; apply float_bits_range in Ha; apply float_bits_range in Hb.
  pose proof (f_equal bits_of_b32 Heq) as Hbits.
  unfold bits_of_b32, b32_of_bits in Hbits.
  rewrite !bits_of_binary_float_of_bits in Hbits by assumption; exact Hbits.
Qed.

Lemma float_decode64_injective a b : float_bits_in_range 64 a = true ->
  float_bits_in_range 64 b = true -> b64_of_bits a = b64_of_bits b -> a = b.
Proof.
  intros Ha Hb Heq; apply float_bits_range in Ha; apply float_bits_range in Hb.
  pose proof (f_equal bits_of_b64 Heq) as Hbits.
  unfold bits_of_b64, b64_of_bits in Hbits.
  rewrite !bits_of_binary_float_of_bits in Hbits by assumption; exact Hbits.
Qed.

Lemma nan_cval_full u v : nan_cval_agree true true u v -> u = v.
Proof.
  destruct u as [wu zu|bu ou|fu|a32|a64]; destruct v as [wv zv|bv ov|fv|b32|b64];
    cbn [nan_cval_agree]; try tauto.
  - destruct (float_bits_in_range 32 a32 && float_bits_in_range 32 b32) eqn:Hrange;
      [|tauto].
    apply andb_true_iff in Hrange as [Ha Hb]; intro Hagree.
    apply nan_agree_full in Hagree; apply f_equal; eapply float_decode32_injective; eassumption.
  - destruct (float_bits_in_range 64 a64 && float_bits_in_range 64 b64) eqn:Hrange;
      [|tauto].
    apply andb_true_iff in Hrange as [Ha Hb]; intro Hagree.
    apply nan_agree_full in Hagree; apply f_equal; eapply float_decode64_injective; eassumption.
Qed.

(** Full boundary demand entails exact option equality, including malformed float patterns. *)
Lemma nan_option_full u v : nan_option_agree (Demanded true true) u v -> u = v.
Proof.
  destruct u as [u|], v as [v|]; cbn [nan_option_agree]; try tauto.
  intro Hagree; apply f_equal, nan_cval_full; exact Hagree.
Qed.

(** Deleting bottom pairs preserves their entire semantic contribution for arbitrary lookups. *)
Lemma nan_forward_bottom_agrees pairs (left right : vid -> option cval) :
  (forall x d, In (x, d) (nan_forward_pairs NotDemanded pairs) ->
    agree (dagree nan_domain_ssa) d (left x) (right x)) <->
  (forall x d, In (x, d) [] -> agree (dagree nan_domain_ssa) d (left x) (right x)).
Proof.
  split.
  - intros Hall x d Hnone; contradiction.
  - intros Hempty x d Hin; apply in_map_iff in Hin as [[y needed] [Heq Hin]].
    injection Heq as <- <-; exact I.
Qed.

(** Sparse facts distinguish unreachable values, the two float widths, and arbitrary values. *)
Inductive fl_any : Type :=
  | FlBot
  | FlA32 (I : @fl_interval 24 128)
  | FlA64 (I : @fl_interval 53 1024)
  | FlOther.

Definition fl_any_leb (a b : fl_any) : bool :=
  match a, b with
  | FlBot, _ => true
  | _, FlOther => true
  | FlA32 lhs, FlA32 rhs => leb fl_lattice lhs rhs
  | FlA64 lhs, FlA64 rhs => leb fl_lattice lhs rhs
  | _, _ => false
  end.

Definition fl_any_join (a b : fl_any) : fl_any :=
  match a, b with
  | FlBot, _ => b
  | _, FlBot => a
  | FlA32 lhs, FlA32 rhs => FlA32 (join fl_lattice lhs rhs)
  | FlA64 lhs, FlA64 rhs => FlA64 (join fl_lattice lhs rhs)
  | _, _ => FlOther
  end.

Definition fl_any_widen (a b : fl_any) : fl_any :=
  match a, b with
  | FlBot, _ => b
  | _, FlBot => a
  | FlA32 lhs, FlA32 rhs => FlA32 (widen fl_lattice lhs rhs)
  | FlA64 lhs, FlA64 rhs => FlA64 (widen fl_lattice lhs rhs)
  | _, _ => FlOther
  end.

Definition fl_any_narrow (a b : fl_any) : fl_any :=
  match a, b with
  | FlOther, _ => b
  | FlA32 lhs, FlA32 rhs => FlA32 (narrow fl_lattice lhs rhs)
  | FlA64 lhs, FlA64 rhs => FlA64 (narrow fl_lattice lhs rhs)
  | _, _ => a
  end.

(** Width-specific interval facts are incomparable and have a shared arbitrary-value top. *)
Definition fl_any_lattice : lattice fl_any :=
  {| leb := fl_any_leb;
     bot := FlBot;
     join := fl_any_join;
     widen := fl_any_widen;
     narrow := fl_any_narrow |}.

Definition fl_any_gamma (a : fl_any) (c : cval) : Prop :=
  match a, c with
  | FlBot, _ => False
  | FlOther, _ => True
  | FlA32 interval, VF32 bits => (0 <= bits < 2 ^ 32)%Z /\ fl_gamma interval (b32_of_bits bits)
  | FlA64 interval, VF64 bits => (0 <= bits < 2 ^ 64)%Z /\ fl_gamma interval (b64_of_bits bits)
  | _, _ => False
  end.

(** The numeric concretisation retains the original non-optional SSA concrete-value carrier. *)
Definition fl_any_concretisation : concretisation fl_any cval :=
  Concretisation _ _ fl_any_gamma.

(** The arbitrary-value fact contains every SSA value, including malformed float patterns. *)
Definition fl_any_top : top fl_any_lattice.
Proof.
  refine {| top_value := FlOther |}; intros []; reflexivity.
Defined.

(** * Complete demand support *)

Lemma nan_forward_pair_member d pairs y m :
  In (y, m) (nan_forward_pairs d pairs) -> exists needed, In (y, needed) pairs /\ m = d.
Proof.
  intro Hin; apply in_map_iff in Hin as [[x needed] [Heq Hin]].
  injection Heq as <- <-; exists needed; split; [exact Hin|reflexivity].
Qed.

Lemma nan_op_back_member o args d y m : In (y, m) (nan_op_back o args d) -> In y args.
Proof.
  destruct d as [|sg pl]; [cbn; contradiction|].
  destruct o as [c|w o| | | |tag]; cbn [nan_op_back];
    try solve [intro Hin; apply in_map_iff in Hin as [x [Heq Hin]];
      injection Heq as <- <-; exact Hin].
  destruct args as [|a [|b [|c rest]]].
  - cbn; contradiction.
  - cbn; intros [Heq|Hfalse]; [injection Heq as <- <-; auto|contradiction].
  - cbn; destruct (float_ext_decode tag) as [[w o]|]; cbn.
    + destruct o as [arith|]; cbn [nan_back]; destruct (sg || pl);
        cbn; intros [Heq|[Heq|Hfalse]]; try contradiction;
        injection Heq as <- <-; auto.
    + intros [Heq|[Heq|Hfalse]]; try contradiction; injection Heq as <- <-; auto.
  - change (In (y, m) (map (fun x => (x, Demanded true true)) (a :: b :: c :: rest)) ->
      In y (a :: b :: c :: rest)).
    intro Hin; apply in_map_iff in Hin as [x [Heq Hin]];
      injection Heq as <- <-; exact Hin.
Qed.

Lemma float_operation_values ext P f x o args : wf_program ext P ->
  def (ssa_block_view ext P f) x = Op o args ->
  forall y, In y args -> In y (values_of P f).
Proof.
  intros Hwf Hdef y Hy.
  destruct (ExamplesSsaViews.ssa_operation_location ext P f x o args Hwf Hdef)
    as [fd [l [b [pc [Hf [Hb Hi]]]]]].
  pose proof (ExamplesSsaViews.ssa_instruction_values ext P f fd l b
    (IOp x o args) Hwf Hf Hb (nth_error_In _ pc Hi)) as Hvalues.
  apply Forall_app in Hvalues; exact (proj1 (Forall_forall _ _) (proj1 Hvalues) y Hy).
Qed.

Lemma float_shape_values ext P f e y : wf_program ext P ->
  In y (ssa_get ssa_edge_encoding (float_trap_shape_index P f) [] e) ->
  In y (values_of P f).
Proof.
  intros Hwf; unfold ssa_get, float_trap_shape_index.
  destruct (Map.get ssa_edge_encoding e _) as [args|] eqn:Hget; [|contradiction].
  apply (ssa_map_get_sound ssa_edge_encoding) in Hget.
  apply in_flat_map in Hget; destruct Hget as [[l b] [Hblock Hrow]].
  apply in_flat_map in Hrow; destruct Hrow as [[pc i] [Henum Hrow]].
  destruct i as [result o actual|result n|pointer|result ty size pointer|size pointer value|value];
    try contradiction.
  destruct o as [c|w o| | | |tag]; try contradiction.
  destruct Hrow as [Heq|Hfalse]; [injection Heq as <- <-|contradiction].
  unfold ssa_blocks in Hblock; destruct (find_func P f) as [fd|] eqn:Hf; [|contradiction].
  assert (Hb : find_block fd l = Some b).
  { apply first_index_complete; [exact (proj1 (proj2 (wf_function ext P f fd Hwf Hf)))|
      exact Hblock]. }
  apply ExamplesSsaViews.ssa_enumerate_nth in Henum; destruct Henum as [offset [_ Hi]].
  pose proof (ExamplesSsaViews.ssa_instruction_values ext P f fd l b
    (IOp result (OExt tag) actual) Hwf Hf Hb (nth_error_In _ offset Hi)) as Hvalues.
  apply Forall_app in Hvalues; intro Hy.
  exact (proj1 (Forall_forall _ _) (proj1 Hvalues) y Hy).
Qed.

(** Every forced, backward, defined and exit variable is covered, at all raw points. *)
Lemma ssa_nan_demand_vars ext P f : wf_program ext P ->
  demand_vars_ok (ssa_nan_demand_view ext P f).
Proof.
  intro Hwf; destruct (ssa_demand_vars ext P f Hwf)
    as [Hnodup [Hinputs [Hexits Hdefs]]].
  split; [exact Hnodup|]; split.
  - intros e x d y m Hin; apply in_app_iff in Hin as [Hforced|Hback].
    + apply in_app_iff in Hforced as [Hraw|Hshape].
      * apply nan_forward_pair_member in Hraw as [needed [Hin Heq]].
        apply (Hinputs e x false y needed); apply in_or_app; left; exact Hin.
      * apply in_map_iff in Hshape as [z [Heq Hin]]; injection Heq as <- <-.
        exact (float_shape_values ext P f e z Hwf Hin).
    + destruct d as [|sg pl]; [contradiction|].
      cbn [ssa_nan_demand_view dback] in Hback.
      destruct (def (ssa_block_view ext P f) x) as [o args|b i|] eqn:Hdef;
        [eapply float_operation_values; [exact Hwf|exact Hdef|
          exact (nan_op_back_member o args _ y m Hback)]| |contradiction].
      apply nan_forward_pair_member in Hback as [needed [Hin Heq]].
      apply (Hinputs e x true y needed); apply in_or_app; right; exact Hin.
  - split.
    + intros n y m Hin; apply nan_forward_pair_member in Hin as [needed [Hin Heq]].
      exact (Hexits n y needed Hin).
    + exact Hdefs.
Qed.

Lemma nan_option_refl d u : nan_option_agree d u u.
Proof.
  exact (agree_refl (proj1 (proj2 nan_domain_ssa_laws)) d u).
Qed.

Lemma nan_option_antitone d d' u v : nan_leb d d' = true ->
  nan_option_agree d' u v -> nan_option_agree d u v.
Proof.
  exact (agree_antitone (proj1 (proj2 nan_domain_ssa_laws)) d d' u v).
Qed.

Lemma nan_option_join d d' u v : nan_option_agree (nan_join d d') u v ->
  nan_option_agree d u v /\ nan_option_agree d' u v.
Proof.
  intro Hagree; split; eapply nan_option_antitone; [|exact Hagree| |exact Hagree].
  - exact (join_upper_l (proj1 nan_domain_ssa_laws) d d').
  - exact (join_upper_r (proj1 nan_domain_ssa_laws) d d').
Qed.

Definition nan_lookup (raw : Map.t vid nan_demand) (x : vid) : nan_demand :=
  pointwise_lookup var_encoding NotDemanded raw x.

Lemma nan_lookup_union a b x : nan_lookup (Map.union_with nan_join a b) x =
  nan_join (nan_lookup a x) (nan_lookup b x).
Proof.
  unfold nan_lookup; generalize var_encoding as EX; intro EX.
  change (@pointwise_lookup nat nan_demand EX NotDemanded
    (@Map.union_with nat nan_demand nan_join a b) x =
      nan_join (@pointwise_lookup nat nan_demand EX NotDemanded a x)
        (@pointwise_lookup nat nan_demand EX NotDemanded b x)).
  unfold pointwise_lookup, Map.get; rewrite Map.code_get_union_with.
  destruct (@Map.code_get nat nan_demand (@encode nat EX x) a) as [[|sg pl]|],
    (@Map.code_get nat nan_demand (@encode nat EX x) b) as [[|sg' pl']|]; reflexivity.
Qed.

Lemma nan_exit_member pairs x d : In (x, d) pairs ->
  nan_leb d (nan_lookup (exit_map var_encoding nan_lattice pairs) x) = true.
Proof.
  induction pairs as [|[y m] rest IH]; cbn [In exit_map]; [contradiction|].
  rewrite nan_lookup_union; intros [Heq|Hin].
  - injection Heq as <- <-; unfold nan_lookup, pointwise_lookup at 1.
    rewrite Map.get_set_same; exact (join_upper_l (proj1 nan_domain_ssa_laws) _ _).
  - eapply (leb_trans (proj1 nan_domain_ssa_laws)); [exact (IH Hin)|].
    exact (join_upper_r (proj1 nan_domain_ssa_laws) _ _).
Qed.

Lemma nan_demand_outside U (d : finite_map var_encoding U nan_demand) x :
  ~ In x U -> dget var_encoding nan_lattice d x = NotDemanded.
Proof.
  intro Houtside; unfold dget, pointwise_lookup.
  destruct (Map.get var_encoding x (proj1_sig d)) as [m|] eqn:Hget; [|reflexivity].
  exfalso; apply Houtside, (proj2 (proj2_sig d)); rewrite Hget; discriminate.
Qed.

Lemma nan_demand_agreement (dv :
    demand_view astate event (label * nat) ssa_edge vid (option cval) nan_demand) :
  agreement_laws (demand_lattice var_encoding nan_domain_ssa dv)
    (demand_agreement var_encoding nan_domain_ssa dv) /\
  agreement_symmetric (demand_agreement var_encoding nan_domain_ssa dv).
Proof.
  split.
  - constructor.
    + intros d s x; apply nan_option_refl.
    + intros a b s t Hab Hagree x; eapply nan_option_antitone; [|exact (Hagree x)].
      exact (monotone_pointwise_lookup var_encoding nan_lattice
        (proj1 nan_domain_ssa_laws) x _ _ Hab).
  - intros d s t Hagree x.
    exact (proj1 (proj2 (proj2 nan_domain_ssa_laws)) _ _ _ (Hagree x)).
Qed.

Lemma nan_transfer_get (dv :
    demand_view astate event (label * nat) ssa_edge vid (option cval) nan_demand)
    e d y : In y (dvars dv) ->
  dget var_encoding nan_lattice (demand_transfer var_encoding nan_domain_ssa dv e d) y =
    nan_join (nan_lookup (demand_retain var_encoding
      (FinSet.of_list var_encoding (ddefs dv e)) (proj1_sig d)) y)
      (nan_join (nan_lookup (exit_map var_encoding nan_lattice (dnec dv e)) y)
        (nan_lookup (exit_map var_encoding nan_lattice
          (flat_map (fun x => dback dv e x (dget var_encoding nan_lattice d x))
            (ddefs dv e))) y)).
Proof.
  intro Hin; unfold dget, pointwise_lookup, demand_transfer.
  rewrite demand_index_clamp_get by exact Hin.
  match goal with
  | |- (match Map.get _ _ ?raw with Some m => m | None => _ end) = ?rhs =>
    change (nan_lookup raw y = rhs)
  end.
  rewrite !nan_lookup_union; reflexivity.
Qed.

Lemma nan_transfer_forced_agrees (dv :
    demand_view astate event (label * nat) ssa_edge vid (option cval) nan_demand)
    e d s t y m : In y (dvars dv) -> In (y, m) (dnec dv e) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) s t ->
  nan_option_agree m (dlookup dv s y) (dlookup dv t y).
Proof.
  intros Hy Hin Hagree; specialize (Hagree y).
  change (nan_option_agree (dget var_encoding nan_lattice
    (demand_transfer var_encoding nan_domain_ssa dv e d) y)
      (dlookup dv s y) (dlookup dv t y)) in Hagree.
  rewrite nan_transfer_get in Hagree by exact Hy.
  apply nan_option_join in Hagree as [_ Hagree]; apply nan_option_join in Hagree as [Hagree _].
  eapply nan_option_antitone; [exact (nan_exit_member _ _ _ Hin)|exact Hagree].
Qed.

Lemma nan_transfer_backward_agrees (dv :
    demand_view astate event (label * nat) ssa_edge vid (option cval) nan_demand)
    e d s t x y m : In y (dvars dv) -> In x (ddefs dv e) ->
  In (y, m) (dback dv e x (dget var_encoding nan_lattice d x)) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) s t ->
  nan_option_agree m (dlookup dv s y) (dlookup dv t y).
Proof.
  intros Hy Hx Hin Hagree; specialize (Hagree y).
  change (nan_option_agree (dget var_encoding nan_lattice
    (demand_transfer var_encoding nan_domain_ssa dv e d) y)
      (dlookup dv s y) (dlookup dv t y)) in Hagree.
  rewrite nan_transfer_get in Hagree by exact Hy.
  apply nan_option_join in Hagree as [_ Hagree]; apply nan_option_join in Hagree as [_ Hagree].
  eapply nan_option_antitone; [apply nan_exit_member|exact Hagree].
  apply in_flat_map; exists x; split; assumption.
Qed.

Lemma nan_retain_lookup defined raw x : ~ In x defined ->
  nan_lookup (demand_retain var_encoding (FinSet.of_list var_encoding defined) raw) x =
    nan_lookup raw x.
Proof.
  intro Houtside; unfold nan_lookup, pointwise_lookup, demand_retain.
  rewrite Map.get_combine by reflexivity.
  destruct (Map.get var_encoding x (FinSet.of_list var_encoding defined)) as [[]|]
    eqn:Hget; [|reflexivity].
  exfalso; apply Houtside, (proj1 (FinSet.of_list_spec var_encoding x defined)).
  unfold FinSet.mem, Map.mem; rewrite Hget; reflexivity.
Qed.

Lemma nan_transfer_frame_agrees (dv :
    demand_view astate event (label * nat) ssa_edge vid (option cval) nan_demand)
    e d s t x : ~ In x (ddefs dv e) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) s t ->
  nan_option_agree (dget var_encoding nan_lattice d x) (dlookup dv s x) (dlookup dv t x).
Proof.
  intros Houtside Hagree; destruct (in_dec Nat.eq_dec x (dvars dv)) as [Hin|Hnot].
  - specialize (Hagree x); change (nan_option_agree (dget var_encoding nan_lattice
      (demand_transfer var_encoding nan_domain_ssa dv e d) x)
        (dlookup dv s x) (dlookup dv t x)) in Hagree.
    rewrite nan_transfer_get in Hagree by exact Hin.
    apply nan_option_join in Hagree as [Hagree _].
    rewrite nan_retain_lookup in Hagree by exact Houtside; exact Hagree.
  - rewrite (nan_demand_outside _ d x Hnot); exact I.
Qed.

(** * Agreement along raw SSA steps *)

Section NanSsa.
Context (ext : nat -> list cval -> option cval) (P : program) (f : func)
  (Hwf : wf_program ext P).
Local Abbreviation dv := (ssa_nan_demand_view ext P f).

Lemma ssa_nan_raw_forced_agrees e d a t x needed :
  In (x, needed) (dnec (ssa_demand_view ext P f) e) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) a t ->
  aenv a x = aenv t x.
Proof.
  intros Hin Hagree; destruct (ssa_demand_vars ext P f Hwf)
    as [_ [Hinputs _]].
  assert (Hinside : In x (dvars dv)).
  { apply (Hinputs e x false x needed); apply in_or_app; left; exact Hin. }
  assert (Hforced : In (x, Demanded true true) (dnec dv e)).
  { cbn [ssa_nan_demand_view dnec]; apply in_or_app; left.
    apply in_map_iff; exists (x, needed); split; [reflexivity|exact Hin]. }
  apply nan_option_full.
  exact (nan_transfer_forced_agrees dv e d a t x _ Hinside Hforced Hagree).
Qed.

Lemma ssa_nan_forced_inputs e p d a t :
  Map.get ssa_edge_encoding e (ssa_point_index P f) = Some p ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) a t ->
  forall x, In x (spp_forced p) -> aenv a x = aenv t x.
Proof.
  intros Hindex Hagree x Hx; eapply ssa_nan_raw_forced_agrees; [|exact Hagree].
  rewrite ExamplesSsaViews.ssa_forced_demands, Hindex.
  apply in_map_iff; exists x; split; [reflexivity|exact Hx].
Qed.

Lemma ssa_nan_outputs a tr a' t t' e d :
  step (activation ext P f) a tr a' -> ssa_point_taken P f a tr a' e ->
  step (activation ext P f) t tr t' -> ssa_point_taken P f t tr t' e ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) a t ->
  (forall x, In x (ddefs dv e) ->
    nan_option_agree (dget var_encoding nan_lattice d x) (aenv a' x) (aenv t' x)) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv) d a' t'.
Proof.
  intros Hstep Htaken Hstep' Htaken' Hagree Hwritten x.
  destruct (in_dec Nat.eq_dec x (ddefs dv e)) as [Hdef|Houtside].
  - exact (Hwritten x Hdef).
  - change (nan_option_agree (dget var_encoding nan_lattice d x) (aenv a' x) (aenv t' x)).
    rewrite (ExamplesSsaViews.ssa_raw_defs_frame ext P f a tr a' e x
      Hwf Hstep Htaken Houtside),
      (ExamplesSsaViews.ssa_raw_defs_frame ext P f t tr t' e x
        Hwf Hstep' Htaken' Houtside).
    exact (nan_transfer_frame_agrees dv e d a t x Houtside Hagree).
Qed.

Lemma ssa_nan_all_inputs a tr a' t e d :
  step (activation ext P f) a tr a' -> ssa_point_taken P f a tr a' e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) a t ->
  (forall x, In x (AnalysesLiveness.uses (ssa_var_view ext P f) e) -> aenv a x = aenv t x) ->
  exists t', step (activation ext P f) t tr t' /\ ssa_point_taken P f t tr t' e /\
    agree (demand_agreement var_encoding nan_domain_ssa dv) d a' t'.
Proof.
  intros Hstep Htaken Hpoint Hagree Hinputs.
  destruct (ExamplesSsaViews.ssa_raw_uses_determine ext P f a tr a' t e
    Hwf Hstep Htaken Hpoint Hinputs) as [t' [Hstep' [Htaken' Hwritten]]].
  exists t'; split; [exact Hstep'|]; split; [exact Htaken'|].
  eapply ssa_nan_outputs; try eassumption; intros x Hx.
  rewrite (Hwritten x Hx); apply nan_option_refl.
Qed.

Lemma ssa_nan_effectful_instruction a tr a' t e d i :
  at_instr P (activation_frame f a) i ->
  step (activation ext P f) a tr a' -> ssa_point_taken P f a tr a' e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  effectful ssa_effects KeepTraps (AnInstr i) = true ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) a t ->
  exists t', step (activation ext P f) t tr t' /\ ssa_point_taken P f t tr t' e /\
    agree (demand_agreement var_encoding nan_domain_ssa dv) d a' t'.
Proof.
  intros Hat Hstep Htaken Hpoint Hflag Hagree.
  pose proof (ExamplesSsaViews.ssa_taken_instruction_index ext P f a tr a' e i
    Hwf Hat Htaken) as Hindex.
  eapply ssa_nan_all_inputs; try eassumption.
  cbn [ssa_var_view AnalysesLiveness.uses]; rewrite Hindex; intros x Hx.
  apply (ssa_nan_forced_inputs e _ d a t Hindex Hagree x).
  cbn [ssa_instruction_payload spp_forced]; rewrite Hflag; exact Hx.
Qed.

Lemma nan_op_back_pure x o args sg pl :
  effectful ssa_effects KeepTraps (AnInstr (IOp x o args)) = false ->
  nan_op_back o args (Demanded sg pl) = map (fun y => (y, Demanded true true)) args.
Proof.
  destruct o; try reflexivity; discriminate.
Qed.

Lemma ssa_nan_operation_matches a t e d x o args cs v :
  reachable_state (activation ext P f) t ->
  at_instr P (activation_frame f a) (IOp x o args) ->
  read_args (aenv a) args = Some cs -> op_eval ext o cs = Some v ->
  ssa_point_taken P f a [] (activation_advance a (env_set (aenv a) x v)) e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) a t ->
  exists t', step (activation ext P f) t [] t' /\ ssa_point_taken P f t [] t' e /\
    agree (demand_agreement var_encoding nan_domain_ssa dv) d
      (activation_advance a (env_set (aenv a) x v)) t'.
Proof.
  intros Hreachable Hat Hread Heval Htaken Hpoint Hagree.
  assert (Hstep : step (activation ext P f) a []
      (activation_advance a (env_set (aenv a) x v))) by (eapply AOp; eassumption).
  destruct (effectful ssa_effects KeepTraps (AnInstr (IOp x o args))) eqn:Hflag.
  - eapply ssa_nan_effectful_instruction; eassumption.
  - pose proof (ExamplesSsaViews.ssa_taken_instruction_index ext P f a [] _ e
      (IOp x o args) Hwf Hat Htaken) as Hindex.
    destruct (dget var_encoding nan_lattice d x) as [|sg pl] eqn:Hneeded.
    + assert (Hat' : at_instr P (activation_frame f t) (IOp x o args)).
      { injection Hpoint as Hlabel Hpc.
        apply (proj1 (ssa_at_instr_coordinates P (activation_frame f a)
          (activation_frame f t) _ eq_refl (eq_sym Hlabel) (eq_sym Hpc))); exact Hat. }
      destruct (ExamplesSsaViews.ssa_pure_operation_progress ext P f t x o args Hwf
        Hreachable Hat' (ssa_effectful_false_trap _ _ Hflag)) as [cs' [v' [Hread' Heval']]].
      assert (Hstep' : step (activation ext P f) t []
          (activation_advance t (env_set (aenv t) x v'))) by (eapply AOp; eassumption).
      assert (Htaken' : ssa_point_taken P f t []
          (activation_advance t (env_set (aenv t) x v')) e).
      { eapply ExamplesSsaViews.ssa_taken_same_points; try eassumption.
        - injection Hpoint as Hlabel Hpc; cbn; congruence.
        - intros term Hfalse; discriminate. }
      exists (activation_advance t (env_set (aenv t) x v')); split; [exact Hstep'|].
      split; [exact Htaken'|]; eapply ssa_nan_outputs; try eassumption.
      cbn [ssa_nan_demand_view ddefs ssa_demand_view ssa_var_view AnalysesLiveness.defs].
      rewrite Hindex; intros y [<-|Hfalse]; [rewrite Hneeded; exact I|contradiction].
    + assert (Hdef : def (ssa_block_view ext P f) x = Op o args).
      { exact (ExamplesSsaViews.ssa_at_instruction_definition ext P f a
          (IOp x o args) x (Op o args) Hwf Hat (or_introl eq_refl)). }
      eapply ssa_nan_all_inputs; try eassumption.
      cbn [ssa_var_view AnalysesLiveness.uses]; rewrite Hindex; intros y Hy.
      apply nan_option_full; eapply (nan_transfer_backward_agrees dv e d a t x y
        (Demanded true true)); [| | |exact Hagree].
      * exact (float_operation_values ext P f x o args Hwf Hdef y Hy).
      * cbn [ssa_nan_demand_view ddefs ssa_demand_view ssa_var_view AnalysesLiveness.defs].
        rewrite Hindex; left; reflexivity.
      * cbn [ssa_nan_demand_view dback]; rewrite Hdef, Hneeded, (nan_op_back_pure x o args
          sg pl Hflag); apply in_map_iff; exists y; split; [reflexivity|exact Hy].
Qed.

Lemma ssa_nan_binding_outputs a t e d fd l b dst args cs cs' env env' :
  find_func P f = Some fd -> find_block fd l = Some b ->
  Map.get ssa_edge_encoding e (ssa_point_index P f) =
    Some (ssa_transfer_payload (first_index (ssa_blocks P f)) l b (dst, args)) ->
  In (dst, args) (term_edges (bterm b)) ->
  (match bterm b with TCall _ _ _ => False | _ => True end) ->
  read_args (aenv a) args = Some cs -> read_args (aenv t) args = Some cs' ->
  jump_env P (activation_frame f a) dst cs = Some env ->
  jump_env P (activation_frame f t) dst cs' = Some env' ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) a t ->
  forall x, In x (ddefs dv e) ->
    nan_option_agree (dget var_encoding nan_lattice d x) (env x) (env' x).
Proof.
  intros Hf Hb Hindex Hedge Hordinary Hread Hread' Hjump Hjump' Hagree x Hdefined.
  unfold jump_env in Hjump, Hjump'; cbn [activation_frame ffunc fenv] in Hjump, Hjump'.
  rewrite Hf in Hjump, Hjump'; destruct (find_block fd dst) as [target|] eqn:Htarget;
    [|discriminate].
  assert (Hlookup : Map.get nat_encoding dst (first_index (ssa_blocks P f)) = Some target).
  { unfold ssa_blocks; rewrite Hf; exact Htarget. }
  pose proof (ssa_parameter_nodup ext P f fd dst target Hwf Hf Htarget) as Hunique.
  pose proof Hdefined as Hdef.
  cbn [ssa_nan_demand_view ddefs ssa_demand_view ssa_var_view AnalysesLiveness.defs] in Hdef.
  rewrite Hindex in Hdef; cbn [ssa_transfer_payload spp_defs fst snd] in Hdef.
  unfold ssa_get in Hdef; rewrite Hlookup in Hdef.
  assert (Hlength : length (map fst (bparams target)) = length args).
  { rewrite length_map; pose proof (ssa_bind_length _ _ _ _ Hjump).
    pose proof (ssa_read_length _ _ _ Hread); lia. }
  destruct (ssa_parameter_back_argument _ _ x Hunique Hlength Hdef) as [y [Hback Hpair]].
  assert (Hraw : In (y, true) (dback (ssa_demand_view ext P f) e x true)).
  { rewrite ExamplesSsaViews.ssa_backward_demands, Hindex.
    cbn [ssa_transfer_payload spp_back fst snd]; unfold ssa_get; rewrite Hlookup.
    destruct (bterm b); try contradiction; rewrite Hback; left; reflexivity. }
  apply in_map_iff in Hdef as [[px ty] [Heq Hparam]]; cbn in Heq; subst px.
  apply In_nth_error in Hparam as [i Hi].
  pose proof (ExamplesSsaViews.ssa_parameter_definition_at ext P f fd dst target i x ty
    Hwf Hf Htarget Hi) as Hdefinition.
  rewrite (float_ordinary_target ext P f fd l b dst args Hwf Hf Hb Hedge Hordinary)
    in Hdefinition.
  destruct (dget var_encoding nan_lattice d x) as [|sg pl] eqn:Hneeded; [exact I|].
  rewrite (ssa_bind_argument _ _ _ _ _ _ x y Hunique Hjump Hread Hpair),
    (ssa_bind_argument _ _ _ _ _ _ x y Hunique Hjump' Hread' Hpair).
  eapply (nan_transfer_backward_agrees dv e d a t x y (Demanded sg pl));
    [|exact Hdefined| |exact Hagree].
  - destruct (ssa_demand_vars ext P f Hwf) as [_ [Hinputs _]].
    apply (Hinputs e x true y true); apply in_or_app; right; exact Hraw.
  - rewrite Hneeded, (ssa_nan_dback_param ext P f e x dst i sg pl Hdefinition).
    apply in_map_iff; exists (y, true); split; [reflexivity|exact Hraw].
Qed.

Lemma ssa_nan_ordinary_transfer a t e d term slot dst args cs env :
  reachable_state (activation ext P f) t ->
  at_term P (activation_frame f a) term ->
  (match term with TCall _ _ _ | TRet _ => False | _ => True end) ->
  ssa_term_slot (aenv a) term = Some slot -> ssa_term_slot (aenv t) term = Some slot ->
  nth_error (term_edges term) slot = Some (dst, args) ->
  read_args (aenv a) args = Some cs -> jump_env P (activation_frame f a) dst cs = Some env ->
  step (activation ext P f) a [] (activation_enter dst env) ->
  ssa_point_taken P f a [] (activation_enter dst env) e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) a t ->
  (forall cs' env', read_args (aenv t) args = Some cs' ->
    jump_env P (activation_frame f t) dst cs' = Some env' ->
    step (activation ext P f) t [] (activation_enter dst env')) ->
  exists t', step (activation ext P f) t [] t' /\ ssa_point_taken P f t [] t' e /\
    agree (demand_agreement var_encoding nan_domain_ssa dv) d (activation_enter dst env) t'.
Proof.
  intros Hreachable Hat Hordinary Hslot Hslot' Hedge Hread Hjump Hstep Htaken Hpoint
    Hagree Hconstruct.
  assert (Hnot : forall x, term <> TRet x) by (intros x ->; contradiction).
  destruct (ExamplesSsaViews.ssa_taken_transfer_index ext P f a [] _ e term slot dst args
    Hwf Hat Hnot Hslot Hedge Htaken) as [fd [b [Hf [Hb [Ht Hindex]]]]].
  assert (Hat' : at_term P (activation_frame f t) term).
  { injection Hpoint as Hlabel Hpc.
    apply (proj1 (ssa_at_term_coordinates P (activation_frame f a)
      (activation_frame f t) term eq_refl (eq_sym Hlabel) (eq_sym Hpc))); exact Hat. }
  destruct (ExamplesSsaViews.ssa_selected_arguments_bound ext P f t term dst args Hwf
    Hreachable Hat' (nth_error_In _ slot Hedge)) as [cs' Hread'].
  destruct (ExamplesSsaViews.ssa_jump_reread P f a t dst args cs cs' env Hread Hjump Hread')
    as [env' Hjump'].
  pose proof (Hconstruct cs' env' Hread' Hjump') as Hstep'.
  assert (Htaken' : ssa_point_taken P f t [] (activation_enter dst env') e).
  { eapply ExamplesSsaViews.ssa_taken_same_points; try eassumption; [reflexivity|].
    intros selected Heq; cbn [ssa_transfer_payload spp_action] in Heq.
    rewrite Ht in Heq; injection Heq as <-; rewrite Hslot, Hslot'; reflexivity. }
  exists (activation_enter dst env'); split; [exact Hstep'|]; split; [exact Htaken'|].
  eapply ssa_nan_outputs; try eassumption.
  apply (ssa_nan_binding_outputs a t e d fd (alabel a) b dst args cs cs' env env'
    Hf Hb Hindex); try assumption.
  - rewrite Ht; exact (nth_error_In _ slot Hedge).
  - rewrite Ht; destruct term; try contradiction; exact I.
Qed.

Lemma ssa_nan_steps a tr a' t e d :
  reachable_state (activation ext P f) t ->
  step (activation ext P f) a tr a' -> ssa_point_taken P f a tr a' e ->
  (alabel t, apc t) = (alabel a, apc a) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (demand_transfer var_encoding nan_domain_ssa dv e d) a t ->
  exists t', step (activation ext P f) t tr t' /\ ssa_point_taken P f t tr t' e /\
    agree (demand_agreement var_encoding nan_domain_ssa dv) d a' t'.
Proof.
  intros Hreachable Hstep Htaken Hpoint Hagree; pose proof Hstep as Horiginal.
  assert (Hterm : forall term, at_term P (activation_frame f a) term ->
    at_term P (activation_frame f t) term).
  { intros term Hat; injection Hpoint as Hlabel Hpc.
    apply (proj1 (ssa_at_term_coordinates P (activation_frame f a)
      (activation_frame f t) term eq_refl (eq_sym Hlabel) (eq_sym Hpc))); exact Hat. }
  destruct Hstep as
    [a x o args cs v Hat Hread Heval
    |a x n block offset Hat
    |a p Hat
    |a x ty sz p v Hat Htype Hvalid
    |a sz p x Hat
    |a x v Hat Hvalue
    |a dst args cs env Hat Hread Hbind
    |a c l1 a1 l2 a2 z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c cases def da z dst args cs env Hat Hcond Hchoice Hread Hbind
    |a c args dst ps r cs v env Hat Hsig Hread Htype Hvalid Hbind
    |a x v Hat Hvalue].
  all: try solve [eapply ssa_nan_effectful_instruction; try eassumption; reflexivity].
  - exact (ssa_nan_operation_matches a t e d x o args cs v Hreachable
      Hat Hread Heval Htaken Hpoint Hagree).
  - apply (ssa_nan_ordinary_transfer a t e d (TJump dst args) 0 dst args cs env
      Hreachable Hat I eq_refl eq_refl eq_refl Hread Hbind Horiginal Htaken Hpoint Hagree).
    intros cs' env' Hread' Hbind'; eapply AJump; [apply Hterm; exact Hat|exact Hread'|
      exact Hbind'].
  - assert (Hslot : ssa_term_slot (aenv a) (TBr c l1 a1 l2 a2) =
        Some (if Z.eqb z 0 then 1 else 0)).
    { cbn [ssa_term_slot]; rewrite Hcond; reflexivity. }
    assert (Hedge : nth_error (term_edges (TBr c l1 a1 l2 a2))
        (if Z.eqb z 0 then 1 else 0) = Some (dst, args)).
    { cbn [term_edges]; destruct (Z.eqb z 0); injection Hchoice as <- <-; reflexivity. }
    destruct (ExamplesSsaViews.ssa_taken_transfer_index ext P f a [] _ e _ _ dst args Hwf Hat
      ltac:(intros y Hfalse; discriminate) Hslot Hedge Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    assert (Hcontrol : aenv a c = aenv t c).
    { apply (ssa_nan_forced_inputs e _ d a t Hindex Hagree c).
      cbn [ssa_transfer_payload spp_forced]; rewrite Ht; left; reflexivity. }
    assert (Hslot' : ssa_term_slot (aenv t) (TBr c l1 a1 l2 a2) =
        Some (if Z.eqb z 0 then 1 else 0)).
    { cbn [ssa_term_slot]; rewrite <- Hcontrol, Hcond; reflexivity. }
    apply (ssa_nan_ordinary_transfer a t e d _ _ dst args cs env Hreachable
      Hat I Hslot Hslot' Hedge Hread Hbind Horiginal Htaken Hpoint Hagree).
    intros cs' env' Hread' Hbind'; eapply ABranch; [apply Hterm; exact Hat|
      rewrite <- Hcontrol; exact Hcond|exact Hchoice|exact Hread'|exact Hbind'].
  - assert (Hslot : ssa_term_slot (aenv a) (TSwitch c cases def da) =
        Some (ssa_switch_slot z cases)).
    { cbn [ssa_term_slot]; rewrite Hcond; reflexivity. }
    assert (Hedge : nth_error (term_edges (TSwitch c cases def da))
        (ssa_switch_slot z cases) = Some (dst, args)).
    { rewrite <- Hchoice; exact (ssa_switch_slot_target z cases def da). }
    destruct (ExamplesSsaViews.ssa_taken_transfer_index ext P f a [] _ e _ _ dst args Hwf Hat
      ltac:(intros y Hfalse; discriminate) Hslot Hedge Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    assert (Hcontrol : aenv a c = aenv t c).
    { apply (ssa_nan_forced_inputs e _ d a t Hindex Hagree c).
      cbn [ssa_transfer_payload spp_forced]; rewrite Ht; left; reflexivity. }
    assert (Hslot' : ssa_term_slot (aenv t) (TSwitch c cases def da) =
        Some (ssa_switch_slot z cases)).
    { cbn [ssa_term_slot]; rewrite <- Hcontrol, Hcond; reflexivity. }
    apply (ssa_nan_ordinary_transfer a t e d _ _ dst args cs env Hreachable
      Hat I Hslot Hslot' Hedge Hread Hbind Horiginal Htaken Hpoint Hagree).
    intros cs' env' Hread' Hbind'; eapply ASwitch; [apply Hterm; exact Hat|
      rewrite <- Hcontrol; exact Hcond|exact Hchoice|exact Hread'|exact Hbind'].
  - destruct (ExamplesSsaViews.ssa_taken_transfer_index ext P f a [] _ e (TCall c args dst) 0 dst []
      Hwf Hat ltac:(intros y Hfalse; discriminate) eq_refl eq_refl Htaken)
      as [fd [b [Hf [Hb [Ht Hindex]]]]].
    apply (ssa_nan_all_inputs a [] _ t e d Horiginal Htaken Hpoint Hagree).
    cbn [ssa_var_view AnalysesLiveness.uses]; rewrite Hindex; intros x Hx.
    apply (ssa_nan_forced_inputs e _ d a t Hindex Hagree x).
    cbn [ssa_transfer_payload spp_forced spp_uses] in Hx |- *; rewrite Ht in Hx |- *.
    exact Hx.
  - pose proof (ExamplesSsaViews.ssa_taken_return_index ext P f a [EvRet v] _ e x Hwf Hat Htaken)
      as Hindex.
    apply (ssa_nan_all_inputs a _ _ t e d Horiginal Htaken Hpoint Hagree).
    cbn [ssa_var_view AnalysesLiveness.uses]; rewrite Hindex; intros y Hy.
    apply (ssa_nan_forced_inputs e _ d a t Hindex Hagree y); exact Hy.
Qed.

End NanSsa.

Lemma float_no_function_reachable ext P f a : find_func P f = None ->
  ~ reachable_state (activation ext P f) a.
Proof.
  intros Hmissing [s [tr [Hinitial Hrun]]].
  destruct Hinitial as [fd [b [cs [env [Hf Hrest]]]]]; congruence.
Qed.

Lemma float_point_graph_laws ext P f : wf_program ext P ->
  graph_view_laws (activation ext P f) (ssa_point_view ext P f).
Proof.
  intro Hwf; destruct (find_func P f) as [fd|] eqn:Hf.
  - apply ExamplesSsaViews.ssa_point_graph_laws; [exact Hwf|].
    apply in_map_iff; exists (f, fd); split; [reflexivity|].
    exact (first_index_sound _ _ _ Hf).
  - constructor.
    + change (graph_wf (ssa_point_graph P f)).
      unfold ssa_point_graph; rewrite ExamplesSsaViews.ssa_point_all_rows_agrees.
      unfold ssa_entries, ssa_blocks; rewrite Hf; cbn [map flat_map].
      apply ssa_graph_of_rows_wf; [constructor|intros n Hin; contradiction|
        intros e p q Hin; contradiction|intros e p Hin; contradiction].
    + intros a Hinitial; exfalso; apply (float_no_function_reachable ext P f a Hf).
      exists a, []; split; [exact Hinitial|constructor].
    + intros a tr a' Ha Hstep; exfalso.
      exact (float_no_function_reachable ext P f a Hf Ha).
    + intros a tr a' e Ha Hstep Htaken; exfalso.
      exact (float_no_function_reachable ext P f a Hf Ha).
    + intros a tr a' Ha Hstep Hfalse; contradiction.
Qed.

(** The lifted exit list retains every raw operand in exactly its original order. *)
Lemma ssa_nan_exit_demands ext P f n :
  dexit (ssa_nan_demand_view ext P f) n =
    map (fun x => (x, Demanded true true)) (AnalysesLiveness.exit_uses (ssa_var_view ext P f) n).
Proof.
  cbn [ssa_nan_demand_view dexit]; rewrite ssa_exit_demands.
  unfold nan_forward_pairs; rewrite map_map; reflexivity.
Qed.

Lemma nan_exit_agrees (dv :
    demand_view astate event (label * nat) ssa_edge vid (option cval) nan_demand)
    n s t x m : In x (dvars dv) -> In (x, m) (dexit dv n) ->
  agree (demand_agreement var_encoding nan_domain_ssa dv)
    (finite_map_clamp var_encoding (dvars dv) (exit_map var_encoding nan_lattice (dexit dv n)))
    s t -> nan_option_agree m (dlookup dv s x) (dlookup dv t x).
Proof.
  intros Hinside Hin Hagree; specialize (Hagree x).
  change (nan_option_agree (dget var_encoding nan_lattice
    (finite_map_clamp var_encoding (dvars dv) (exit_map var_encoding nan_lattice (dexit dv n))) x)
      (dlookup dv s x) (dlookup dv t x)) in Hagree.
  unfold dget, pointwise_lookup in Hagree; rewrite finite_map_clamp_get in Hagree by exact Hinside.
  eapply nan_option_antitone; [exact (nan_exit_member _ _ _ Hin)|exact Hagree].
Qed.

Lemma ssa_nan_demand_laws_ext ext P f : wf_program ext P ->
  demand_laws (activation ext P f) (activation_endings ext P f)
    (reachable_state (activation ext P f)) var_encoding nan_domain_ssa
    (ssa_nan_demand_view ext P f).
Proof.
  intro Hwf; constructor.
  - exact (float_point_graph_laws ext P f Hwf).
  - intros a tr a' Hfalse; contradiction.
  - intros a tr a' e x Ha Hstep Htaken Houtside.
    exact (ExamplesSsaViews.ssa_raw_defs_frame ext P f a tr a' e x
      Hwf Hstep Htaken Houtside).
  - apply nan_demand_agreement.
  - intros u v; exact I.
  - intros e x; reflexivity.
  - exact (ssa_nan_demand_vars ext P f Hwf).
  - intros a tr a' t e d Ha Ht Hpoint Hstep Htaken Hagree.
    exact (ssa_nan_steps ext P f Hwf a tr a' t e d Ht Hstep Htaken Hpoint Hagree).
  - intros a t Ha Ht Hpoint Hagree.
    apply (ExamplesSsaViews.ssa_raw_exits_determine ext P f a t Hwf Ha Ht Hpoint).
    intros x Hx; apply nan_option_full.
    assert (Hin : In (x, Demanded true true)
        (dexit (ssa_nan_demand_view ext P f) (alabel a, apc a))).
    { rewrite ssa_nan_exit_demands; apply in_map_iff; exists x; split;
        [reflexivity|exact Hx]. }
    eapply (nan_exit_agrees (ssa_nan_demand_view ext P f) (alabel a, apc a)
      a t x (Demanded true true)); [|exact Hin|exact Hagree].
    destruct (ssa_nan_demand_vars ext P f Hwf) as [_ [_ [Hexits _]]].
    exact (Hexits _ x _ Hin).
Qed.

Section FloatDemandTheorems.
Context (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024).
Local Abbreviation fx := (float_ext nm32 nm64).

(** The NaN view meets every generic demand law on the complete raw SSA graph. *)
Theorem ssa_nan_demand_view_laws (P : program) (f : func) :
  wf_program fx P ->
  demand_laws (activation fx P f) (activation_endings fx P f)
    (reachable_state (activation fx P f)) var_encoding nan_domain_ssa
    (ssa_nan_demand_view fx P f).
Proof.
  apply ssa_nan_demand_laws_ext.
Qed.

(** Initial activations agreeing on a post-solution have identical complete behaviours. *)
Theorem ssa_nan_demand_sound (P : program) (f : func)
    (sigma : (label * nat) ->
      finite_map var_encoding (dvars (ssa_nan_demand_view fx P f)) nan_demand)
    (s0 t0 : astate) :
  wf_program fx P ->
  post_solution
    (demand_lattice var_encoding nan_domain_ssa (ssa_nan_demand_view fx P f))
    (demand_system var_encoding nan_domain_ssa (ssa_nan_demand_view fx P f)) sigma ->
  initial (activation fx P f) s0 -> initial (activation fx P f) t0 ->
  point (dgraph (ssa_nan_demand_view fx P f)) t0 =
    point (dgraph (ssa_nan_demand_view fx P f)) s0 ->
  agree (demand_agreement var_encoding nan_domain_ssa (ssa_nan_demand_view fx P f))
    (sigma (point (dgraph (ssa_nan_demand_view fx P f)) s0)) s0 t0 ->
  same_behaviour (activation fx P f) (activation_endings fx P f) s0
    (activation fx P f) (activation_endings fx P f) t0.
Proof.
  intros Hwf Hpost Hs Ht Hpoint Hagree.
  eapply demand_sound; [apply ssa_nan_demand_view_laws; exact Hwf|
    apply reachable_invariant|exact Hpost|exact Hs|exact Ht|exact Hpoint|exact Hagree].
Qed.

End FloatDemandTheorems.

Lemma fl_any_lattice_laws : lattice_laws fl_any_lattice.
Proof.
  constructor.
  - intros [|I|I|]; try reflexivity; apply (leb_refl (proj1 fl_lattice_laws)).
  - intros [|I|I|] [|J|J|] [|K|K|]; cbn [fl_any_lattice fl_any_leb leb];
      intros Hij Hjk; try discriminate; try reflexivity;
      eapply (leb_trans (proj1 fl_lattice_laws)); eassumption.
  - intros []; reflexivity.
  - intros [|I|I|] [|J|J|]; try reflexivity;
      first [apply (leb_refl (proj1 fl_lattice_laws))|
        apply (join_upper_l (proj1 fl_lattice_laws))].
  - intros [|I|I|] [|J|J|]; try reflexivity;
      first [apply (leb_refl (proj1 fl_lattice_laws))|
        apply (join_upper_r (proj1 fl_lattice_laws))].
  - intros [|I|I|] [|J|J|]; try reflexivity;
      first [apply (leb_refl (proj1 fl_lattice_laws))|
        apply (widen_upper_l (proj1 fl_lattice_laws))].
  - intros [|I|I|] [|J|J|]; try reflexivity;
      first [apply (leb_refl (proj1 fl_lattice_laws))|
        apply (widen_upper_r (proj1 fl_lattice_laws))].
  - intros [|I|I|] [|J|J|] Hle; try discriminate; try reflexivity;
      first [apply (leb_refl (proj1 fl_lattice_laws))|
        apply (narrow_lower (proj1 fl_lattice_laws)); exact Hle].
  - intros [|I|I|] [|J|J|] Hle; try discriminate; try reflexivity;
      first [apply (leb_refl (proj1 fl_lattice_laws))|
        apply (narrow_upper (proj1 fl_lattice_laws)); exact Hle].
Qed.

Lemma fl_any_concretisation_laws : concretisation_laws fl_any_lattice fl_any_concretisation.
Proof.
  constructor; intros [|I|I|] [|J|J|] c Hle Hgamma;
    try discriminate; try contradiction; try solve [constructor].
  - destruct c; try contradiction; destruct Hgamma as [Hrange Hgamma].
    split; [exact Hrange|]; exact (fl_gamma_mono I J _ Hle Hgamma).
  - destruct c; try contradiction; destruct Hgamma as [Hrange Hgamma].
    split; [exact Hrange|]; exact (fl_gamma_mono I J _ Hle Hgamma).
Qed.

Definition fl_any_rank (a : fl_any) : nat :=
  match a with
  | FlBot => 8
  | FlA32 interval => 1 + fl_rank interval
  | FlA64 interval => 1 + fl_rank interval
  | FlOther => 0
  end.

Lemma fl_any_rank_bounded a : fl_any_rank a <= 8.
Proof.
  destruct a as [|I|I|]; cbn [fl_any_rank]; try lia.
  - pose proof (wrank_bounded (@fl_widening_rank 24 128) I) as Hrank;
      change (fl_rank I <= 6) in Hrank; lia.
  - pose proof (wrank_bounded (@fl_widening_rank 53 1024) I) as Hrank;
      change (fl_rank I <= 6) in Hrank; lia.
Qed.

(** Widening can consume at most eight strict rank levels across reachability and float widths. *)
Definition fl_any_widening_rank : bounded_widening_rank fl_any_lattice.
Proof.
  unshelve refine (@BoundedWideningRank _ _ (@WideningRank _ _ fl_any_rank _ _) 8 _).
  - intros [|I|I|] [|J|J|] Hle;
      cbn [fl_any_lattice fl_any_leb fl_any_widen fl_any_rank leb widen] in *;
      try discriminate; try lia.
    + change (1 + fl_rank (fl_widen I J) <= 1 + fl_rank I).
      pose proof (fl_rank_step I J); lia.
    + change (1 + fl_rank (fl_widen I J) <= 1 + fl_rank I).
      pose proof (fl_rank_step I J); lia.
  - intros [|I|I|] [|J|J|] Hle;
      cbn [fl_any_lattice fl_any_leb fl_any_widen fl_any_rank leb widen] in *;
      try discriminate; try lia.
    + pose proof (wrank_bounded (@fl_widening_rank 24 128) J) as Hrank;
        change (fl_rank J <= 6) in Hrank; lia.
    + pose proof (wrank_bounded (@fl_widening_rank 53 1024) J) as Hrank;
        change (fl_rank J <= 6) in Hrank; lia.
    + change (1 + fl_rank (fl_widen I J) < 1 + fl_rank I).
      pose proof (fl_rank_progress I J Hle); lia.
    + change (1 + fl_rank (fl_widen I J) < 1 + fl_rank I).
      pose proof (fl_rank_progress I J Hle); lia.
  - apply fl_any_rank_bounded.
Defined.

(** * Numeric SSA instantiation *)

Definition float_op_abs (o : sop) (fs : list fl_any) : fl_any :=
  match fs with
  | [a; b] =>
    match o, a, b with
    | OExt tag, FlA32 interval1, FlA32 interval2 =>
      match float_ext_decode tag with
      | Some (F32, FArith a) => FlA32 (@fl_bin 24 128 eq_refl eq_refl a interval1 interval2)
      | _ => FlOther
      end
    | OExt tag, FlA64 interval1, FlA64 interval2 =>
      match float_ext_decode tag with
      | Some (F64, FArith a) => FlA64 (@fl_bin 53 1024 eq_refl eq_refl a interval1 interval2)
      | _ => FlOther
      end
    | _, _, _ => FlOther
    end
  | _ => FlOther
  end.

Definition float_assume_args (o : sop) (taken : bool) (fs : list fl_any) : list fl_any :=
  match fs with
  | [a; b] =>
    match o, taken, a, b with
    | OExt tag, true, FlA32 interval1, FlA32 interval2 =>
      match float_ext_decode tag with
      | Some (F32, FLt) =>
        let '(interval1', interval2') := fl_assume_lt interval1 interval2 in
        [FlA32 interval1'; FlA32 interval2']
      | _ => fs
      end
    | OExt tag, true, FlA64 interval1, FlA64 interval2 =>
      match float_ext_decode tag with
      | Some (F64, FLt) =>
        let '(interval1', interval2') := fl_assume_lt interval1 interval2 in
        [FlA64 interval1'; FlA64 interval2']
      | _ => fs
      end
    | _, _, _, _ => fs
    end
  | _ => fs
  end.

(** Arithmetic and successful less-than guards refine facts of their matching float width. *)
Definition float_ssa_domain : sparse_domain fl_any cval sop :=
  SparseDomain fl_any_lattice fl_any_concretisation FlOther float_op_abs
    (fun _ a => a) float_assume_args.

(** The numeric problem uses the checked SSA block view and the caller's entry facts. *)
Definition float_problem (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024)
    (P : program) (f : func) (vals : list vid) (entry : vid -> fl_any) :
    sparse_problem astate event label ssa_edge vid sop cval fl_any :=
  SparseProblem (ssa_block_view (float_ext nm32 nm64) P f) float_ssa_domain vals entry.

Lemma float_op_sound nm32 nm64 o fs cs c : Forall2 fl_any_gamma fs cs ->
  ExamplesSsaSemantics.op_eval (float_ext nm32 nm64) o cs = Some c ->
  fl_any_gamma (float_op_abs o fs) c.
Proof.
  intros Hfacts Heval.
  destruct fs as [|a [|b [|extra rest]]]; cbn [float_op_abs]; try exact I.
  destruct o as [constant|w op| | | |tag]; cbn [float_op_abs]; try exact I.
  destruct a as [|I|I|], b as [|J|J|]; cbn; try exact Logic.I;
    destruct (float_ext_decode tag) as [[w op]|] eqn:Hdecode; cbn; try exact Logic.I;
    destruct w, op as [arith|]; cbn; try exact Logic.I.
  all: inversion Hfacts as [|fa ca fas cas Ha Hrest]; subst;
    inversion Hrest as [|fb cb fbs cbs Hb Hnil]; subst; inversion Hnil; subst;
    destruct ca, cb; cbn [fl_any_gamma] in Ha, Hb; try contradiction;
    destruct Ha as [Hra Hga]; destruct Hb as [Hrb Hgb];
    cbn [ExamplesSsaSemantics.op_eval] in Heval; unfold float_ext in Heval;
    rewrite Hdecode in Heval;
    match type of Heval with (if ?test then _ else _) = _ => destruct test eqn:Hrange end;
    try discriminate; injection Heval as <-; cbn [float_eval32 float_eval64 fl_any_gamma].
  - split; [apply bits_of_binary_float_range; reflexivity|].
    unfold b32_of_bits, bits_of_b32.
    rewrite binary_float_of_bits_of_binary_float.
    apply fl_bin_sound; assumption.
  - split; [apply bits_of_binary_float_range; reflexivity|].
    unfold b64_of_bits, bits_of_b64; rewrite binary_float_of_bits_of_binary_float.
    apply fl_bin_sound; assumption.
Qed.

Lemma float_assume_sound nm32 nm64 truth :
  (forall w z, truth (VInt w z) = negb (Z.eqb z 0)) ->
  forall o taken fs cs c, Forall2 fl_any_gamma fs cs ->
  ExamplesSsaSemantics.op_eval (float_ext nm32 nm64) o cs = Some c -> truth c = taken ->
  Forall2 fl_any_gamma (float_assume_args o taken fs) cs.
Proof.
  intros Htruth o taken fs cs c Hfacts Heval Htaken.
  destruct fs as [|a [|b [|extra rest]]]; cbn [float_assume_args]; try exact Hfacts.
  destruct o as [constant|w op| | | |tag]; cbn [float_assume_args]; try exact Hfacts.
  destruct taken; [|exact Hfacts].
  destruct a as [|I|I|], b as [|J|J|]; cbn; try exact Hfacts;
    destruct (float_ext_decode tag) as [[w op]|] eqn:Hdecode; cbn; try exact Hfacts;
    destruct w, op as [arith|]; cbn; try exact Hfacts.
  all: inversion Hfacts as [|fa ca fas cas Ha Hrest]; subst;
    inversion Hrest as [|fb cb fbs cbs Hb Hnil]; subst; inversion Hnil; subst;
    destruct ca, cb; cbn [fl_any_gamma] in Ha, Hb; try contradiction;
    destruct Ha as [Hra Hga]; destruct Hb as [Hrb Hgb];
    cbn [ExamplesSsaSemantics.op_eval] in Heval; unfold float_ext in Heval;
    rewrite Hdecode in Heval;
    match type of Heval with (if ?test then _ else _) = _ => destruct test eqn:Hrange end;
    try discriminate; injection Heval as <-; cbn [float_eval32 float_eval64] in Htaken;
    rewrite Htruth in Htaken;
    destruct (fl_lt _ _) eqn:Hlt; try discriminate.
  - unfold fl_lt in Hlt; destruct (Bcompare _ _ _ _) as [[]|] eqn:Hcompare;
      try discriminate.
    destruct (fl_assume_lt_sound I J _ _ Hga Hgb Hcompare) as [Ha Hb].
    constructor; [split; assumption|constructor; [split; assumption|constructor]].
  - unfold fl_lt in Hlt; destruct (Bcompare _ _ _ _) as [[]|] eqn:Hcompare;
      try discriminate.
    destruct (fl_assume_lt_sound I J _ _ Hga Hgb Hcompare) as [Ha Hb].
    constructor; [split; assumption|constructor; [split; assumption|constructor]].
Qed.

Section FloatValueTheorems.
Context (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024).
Local Abbreviation fx := (float_ext nm32 nm64).

(** The float fact lattice and transfers satisfy every sparse-domain soundness law. *)
Theorem float_ssa_domain_laws (truth : cval -> bool) :
  (forall w z, truth (VInt w z) = negb (Z.eqb z 0)) ->
  sparse_domain_laws float_ssa_domain truth (ExamplesSsaSemantics.op_eval fx).
Proof.
  intro Htruth; constructor.
  - apply fl_any_lattice_laws.
  - apply fl_any_concretisation_laws.
  - intros c Hfalse; exact Hfalse.
  - intro c; exact I.
  - apply float_op_sound.
  - intros k a c Hgamma Hguard; exact Hgamma.
  - apply float_assume_sound; exact Htruth.
Qed.

(** Every reachable present SSA value belongs to the numeric post-solution fact. *)
Theorem ssa_float_value_sound (P : program) (f : func) (vals : list vid) (entry : vid -> fl_any)
    (sigma : sparse_unknown label ssa_edge vid -> lift_bot fl_any) :
  wf_program fx P ->
  (forall s x c, reachable_state (activation fx P f) s ->
    val (ssa_block_view fx P f) s x = Some c -> In x vals) ->
  (forall s x c, initial (activation fx P f) s -> val (ssa_block_view fx P f) s x = Some c ->
    exists b i, def (ssa_block_view fx P f) x = Param b i /\
      In b (Graph.entries (cfg (base (ssa_block_view fx P f)))) /\
      gamma fl_any_concretisation (entry x) c) ->
  post_solution (lift_bot_lattice fl_any_lattice)
    (sparse_system label_encoding var_encoding (float_problem nm32 nm64 P f vals entry)) sigma ->
  forall s x c, reachable_state (activation fx P f) s ->
    val (ssa_block_view fx P f) s x = Some c ->
    gamma (lift_bot_gamma fl_any_concretisation) (sigma (UVal x)) c.
Proof.
  intros Hwf Hcoverage Hinitial Hpost s x c Hreachable Hval.
  assert (Hfunction : In f (map fst (funcs P))).
  { destruct Hreachable as [s0 [tr [Hstart Hrun]]].
    destruct Hstart as [fd [b [cs [env [Hfind Hrest]]]]].
    apply first_index_sound in Hfind; apply in_map_iff; exists (f, fd); auto. }
  exact (proj2 (proj2 (sparse_sound label_encoding var_encoding (activation fx P f)
    (float_problem nm32 nm64 P f vals entry) sigma
    (ssa_block_view_laws fx P f Hwf Hfunction)
    (float_ssa_domain_laws ssa_truth ltac:(intros; reflexivity))
    Hcoverage Hinitial Hpost)) s x c Hreachable Hval).
Qed.

End FloatValueTheorems.
