(** * Numeric sparse value analysis

    Operator bridges connect independent client evaluators to numeric sparse transfers.
    For example, a true 32-bit addition refines its operands without equating its result to one.
    Builds on: BitsExpr, DomainsNumeric, ViewsSsa and FixpointTotal. *)

From Stdlib Require Import List ZArith Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderLift.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsExpr.
From Gaulois.Domains Require Import DomainsNumeric.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointTotal.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa.
Import List.ListNotations.

(** A bridge supplies expressions for supported operators and partial word conversion. *)
Record op_bridge (K C : Type) : Type := OpBridge {
  op_expr : K -> option Bits.expr;
  to_word : C -> option word
}.

Arguments OpBridge {K C}.
Arguments op_expr {K C}.
Arguments to_word {K C}.

(** Successful client results agree with expression evaluation and nonzero truth. *)
Record op_bridge_laws {K C} (br : op_bridge K C)
    (op_eval : K -> list C -> option C) (truth : C -> bool) : Prop := {
  bridge_word : forall c w, to_word br c = Some w -> is_word (fst w) (snd w);
  bridge_eq : forall o cs r e, op_eval o cs = Some r -> op_expr br o = Some e ->
    exists ws wr, Forall2 (fun c w => to_word br c = Some w) cs ws /\
      Bits.eval (fun i => nth i ws (1%positive, 0%Z)) e = Some wr /\
      to_word br r = Some wr;
  bridge_truth : forall c w, to_word br c = Some w -> truth c = negb (Z.eqb (snd w) 0)
}.

(** A pure expression is true exactly when it differs from its self-xor. *)
Definition numeric_truth_expr (e : Bits.expr) : Bits.expr :=
  Bits.App bvne [e; Bits.App bvxor [e; e]].

(** Numeric facts retain nonword values precisely away from abstract bottom. *)
Definition numeric_conc {A K C} (ND : numeric_domain A) (G : concretisation A word)
    (br : op_bridge K C) : concretisation A C :=
  {| gamma a c :=
       match to_word br c with
       | Some w => gamma G a w
       | None => leb (lat ND) a (bot (lat ND)) = false
       end |}.

(** Numeric evaluation and truth refinement instantiate the sparse transfer interface. *)
Definition sparse_of_numeric {A K C} (ND : numeric_domain A) (G : concretisation A word)
    (br : op_bridge K C) (top : A) : sparse_domain A C K :=
  {| fact_lat := lat ND;
     fact_conc := numeric_conc ND G br;
     top_fact := top;
     op_abs o fs :=
       match op_expr br o with
       | Some e => abs_eval ND (fun i => nth i fs top) e
       | None => top
       end;
     assume_value k a :=
       match k with
       | GConst c =>
         match to_word br c with
         | Some (w, z) => meet ND a (of_const ND w z)
         | None => a
         end
       | _ => a
       end;
     assume_args o b fs :=
       match op_expr br o with
       | Some e =>
         let env := abs_assume ND (fun i => nth i fs top) (numeric_truth_expr e)
           (of_const ND 1%positive (if b then 1%Z else 0%Z)) in
         map env (seq 0 (length fs))
       | None => fs
       end |}.

(** A numeric sparse problem retains the client's value support and entry facts. *)
Definition numeric_problem {S O N E V K C A} (ND : numeric_domain A)
    (G : concretisation A word) (br : op_bridge K C) (top : A)
    (sv : ssa_view S O N E V K C) (vals : list V) (entry : V -> A) :
    sparse_problem S O N E V K C A :=
  @SparseProblem S O N E V K C A sv (sparse_of_numeric ND G br top) vals entry.

(** The total engine returns a checked sparse post-solution. *)
Definition solve_values {S O N E V K C A} (pr : sparse_problem S O N E V K C A)
    (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (HL : lattice_laws (lift_bot_lattice (fact_lat (domain pr))))
    (sch : scheduler (sparse_unknown N E V)) (st : strategy)
    (HT : terminates (lift_bot_lattice (fact_lat (domain pr))) (sparse_static EN EV pr) sch st) :
  {s : sparse_unknown N E V -> lift_bot A |
     post_solution (lift_bot_lattice (fact_lat (domain pr))) (sparse_system EN EV pr) s} :=
  solve_total (sparse_unknown_encoding EN EE EV) (sparse_constraint_encoding EN EE EV)
    (lift_bot_lattice (fact_lat (domain pr))) HL sch st (sparse_system EN EV pr)
    (sparse_static EN EV pr) HT.

Lemma numeric_truth_eval env e w z :
  Bits.eval env e = Some (w, z) ->
  Bits.eval env (numeric_truth_expr e) =
    Some (1%positive, if negb (Z.eqb z 0) then 1%Z else 0%Z).
Proof.
  intro Heval.
  pose proof (eval_is_word (w, z) env e Heval) as Hword.
  unfold numeric_truth_expr. rewrite eval_app, eval_args_cons, Heval.
  rewrite eval_args_cons, eval_app, !eval_args_cons, Heval, eval_args_nil.
  cbn -[eval_op].
  unfold eval_op. cbn [result_width map fst snd]. rewrite Pos.eqb_refl.
  cbn [op_value map normalize_word word_fun2 word_cmp fst snd].
  unfold wxor. rewrite Z.lxor_nilpotent, wrap_0.
  cbn [result_width map fst snd]. rewrite Pos.eqb_refl.
  cbn [op_value map normalize_word word_fun2 word_cmp fst snd].
  rewrite wrap_wrap, (wrap_id w z Hword).
  destruct (negb (Z.eqb z 0)); rewrite ?wrap_1, ?wrap_0; reflexivity.
Qed.

Lemma numeric_words {A K C} (ND : numeric_domain A) G (br : op_bridge K C) fs cs ws :
  Forall2 (gamma (numeric_conc ND G br)) fs cs ->
  Forall2 (fun c w => to_word br c = Some w) cs ws -> Forall2 (gamma G) fs ws.
Proof.
  intros Hfacts Hwords. revert fs Hfacts.
  induction Hwords as [|c w cs ws Hword Hrest IH]; intros fs Hfacts;
    inversion Hfacts as [|a c' fs' cs' Hfact Htail]; subst; constructor.
  - cbn [numeric_conc gamma] in Hfact.
    now rewrite Hword in Hfact.
  - now apply IH.
Qed.

Lemma numeric_nth_words {K C} (br : op_bridge K C) op_eval truth :
  op_bridge_laws br op_eval truth -> forall cs ws,
  Forall2 (fun c w => to_word br c = Some w) cs ws ->
  env_ok (fun i => nth i ws (1%positive, 0%Z)).
Proof.
  intros Hbridge cs ws Hwords.
  induction Hwords as [|c w cs ws Hword Htail IH]; intros [|i]; cbn.
  - apply zero_is_word.
  - apply zero_is_word.
  - exact (bridge_word _ _ _ Hbridge c w Hword).
  - apply IH.
Qed.

Lemma numeric_nth_sound {A} (G : concretisation A word) top fs ws :
  gamma G top (1%positive, 0%Z) -> Forall2 (gamma G) fs ws ->
  env_sound G (fun i => nth i fs top) (fun i => nth i ws (1%positive, 0%Z)).
Proof.
  intros Htop Hfacts.
  induction Hfacts as [|a w fs ws Hfact Htail IH]; intros [|i]; cbn; auto.
Qed.

Lemma numeric_readback {A C} (R : A -> C -> Prop) (f : nat -> A) (cs : list C) start :
  (forall i c, nth_error cs i = Some c -> R (f (start + i)%nat) c) ->
  Forall2 R (map f (seq start (length cs))) cs.
Proof.
  revert start. induction cs as [|c cs IH]; intros start Hsound; cbn; constructor.
  - specialize (Hsound 0%nat c eq_refl). now rewrite Nat.add_0_r in Hsound.
  - apply IH. intros i d Hnth.
    specialize (Hsound (S i) d Hnth).
    now rewrite Nat.add_succ_r, Nat.add_succ_l in *.
Qed.

Lemma numeric_nth_conversion {K C} (br : op_bridge K C) cs ws :
  Forall2 (fun c w => to_word br c = Some w) cs ws ->
  forall i c, nth_error cs i = Some c ->
    to_word br c = Some (nth i ws (1%positive, 0%Z)).
Proof.
  intro Hwords. induction Hwords as [|c w cs ws Hword Htail IH];
    intros [|i] d Hnth; cbn in *; try discriminate.
  - injection Hnth as <-. exact Hword.
  - now apply IH.
Qed.

Lemma numeric_conc_laws {A K C} (ND : numeric_domain A) G (br : op_bridge K C) :
  numeric_laws ND G -> concretisation_laws (lat ND) (numeric_conc ND G br).
Proof.
  intro Hnumeric. constructor. intros a b c Hab Ha.
  cbn in Ha |- *. destruct (to_word br c) as [w|].
  - exact (gamma_monotone (gamma_laws Hnumeric) a b w Hab Ha).
  - destruct (leb (lat ND) b (bot (lat ND))) eqn:Hbot; [|reflexivity].
    pose proof (leb_trans (lat_laws Hnumeric) a b _ Hab Hbot). congruence.
Qed.

Lemma numeric_top_sound {A K C} (ND : numeric_domain A) G (br : op_bridge K C)
    top truth op_eval :
  op_bridge_laws br op_eval truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) ->
  leb (lat ND) top (bot (lat ND)) = false ->
  forall c, gamma (numeric_conc ND G br) top c.
Proof.
  intros Hbridge Htop Hnotbot c. cbn. destruct (to_word br c) as [[w z]|] eqn:Hword.
  - apply Htop. exact (bridge_word _ _ _ Hbridge c (w, z) Hword).
  - exact Hnotbot.
Qed.

Lemma numeric_op_sound {A K C} (ND : numeric_domain A) G (br : op_bridge K C)
    top truth op_eval :
  numeric_laws ND G -> op_bridge_laws br op_eval truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) ->
  leb (lat ND) top (bot (lat ND)) = false ->
  forall o fs cs c, Forall2 (gamma (numeric_conc ND G br)) fs cs ->
    op_eval o cs = Some c ->
    gamma (numeric_conc ND G br) (op_abs (sparse_of_numeric ND G br top) o fs) c.
Proof.
  intros Hnumeric Hbridge Htop Hnotbot o fs cs c Hfacts Heval.
  cbn [sparse_of_numeric op_abs]. destruct (op_expr br o) as [e|] eqn:Hexpr.
  - destruct (bridge_eq _ _ _ Hbridge o cs c e Heval Hexpr)
      as [ws [wr [Hwords [Hresult Hword]]]].
    cbn [numeric_conc gamma].
    rewrite Hword. eapply abs_eval_sound; [exact Hnumeric| | |exact Hresult].
    + exact (numeric_nth_words br op_eval truth Hbridge cs ws Hwords).
    + apply numeric_nth_sound; [apply Htop, zero_is_word|].
      exact (numeric_words ND G br fs cs ws Hfacts Hwords).
  - exact (numeric_top_sound ND G br top truth op_eval Hbridge Htop Hnotbot c).
Qed.

Lemma numeric_assume_value_sound {A K C} (ND : numeric_domain A) G
    (br : op_bridge K C) top truth op_eval :
  numeric_laws ND G -> op_bridge_laws br op_eval truth ->
  forall k a c, gamma (numeric_conc ND G br) a c -> holds_guard truth k c ->
    gamma (numeric_conc ND G br) (assume_value (sparse_of_numeric ND G br top) k a) c.
Proof.
  intros Hnumeric Hbridge [| |d|d] a c Hfact Hguard; try exact Hfact.
  cbn in Hguard. subst c. cbn [sparse_of_numeric assume_value].
  destruct (to_word br d) as [[w z]|] eqn:Hword; [|exact Hfact].
  cbn in Hfact |- *. rewrite Hword in Hfact |- *.
  apply (meet_sound Hnumeric); [exact Hfact|].
  pose proof (of_const_sound Hnumeric w z) as Hconst.
  rewrite (wrap_id w z (bridge_word _ _ _ Hbridge d (w, z) Hword)) in Hconst.
  exact Hconst.
Qed.

Lemma numeric_assume_args_sound {A K C} (ND : numeric_domain A) G
    (br : op_bridge K C) top truth op_eval :
  numeric_laws ND G -> op_bridge_laws br op_eval truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) ->
  forall o b fs cs c, Forall2 (gamma (numeric_conc ND G br)) fs cs ->
    op_eval o cs = Some c -> truth c = b ->
    Forall2 (gamma (numeric_conc ND G br))
      (assume_args (sparse_of_numeric ND G br top) o b fs) cs.
Proof.
  intros Hnumeric Hbridge Htop o b fs cs c Hfacts Heval Htruth.
  cbn [sparse_of_numeric assume_args]. destruct (op_expr br o) as [e|] eqn:Hexpr;
    [|exact Hfacts].
  destruct (bridge_eq _ _ _ Hbridge o cs c e Heval Hexpr)
    as [ws [[w z] [Hwords [Hresult Hword]]]].
  assert (Henv : env_sound G (fun i => nth i fs top)
    (fun i => nth i ws (1%positive, 0%Z))).
  { apply numeric_nth_sound; [apply Htop, zero_is_word|].
    exact (numeric_words ND G br fs cs ws Hfacts Hwords). }
  assert (Hb : negb (Z.eqb z 0) = b).
  { rewrite <- Htruth. symmetry. exact (bridge_truth _ _ _ Hbridge c (w, z) Hword). }
  pose proof (numeric_truth_eval _ _ _ _ Hresult) as Htest. rewrite Hb in Htest.
  assert (Hconstant : gamma G (of_const ND 1%positive (if b then 1%Z else 0%Z))
    (1%positive, if b then 1%Z else 0%Z)).
  { destruct b; apply (of_const_sound Hnumeric). }
  pose proof (abs_assume_sound ND G _ _ _ _ _ Hnumeric
    (numeric_nth_words br op_eval truth Hbridge cs ws Hwords) Henv Htest Hconstant) as Hrefined.
  rewrite (Forall2_length Hfacts). apply numeric_readback.
  intros i d Hnth. cbn [Nat.add] in *.
  cbn [numeric_conc gamma].
  rewrite (numeric_nth_conversion br cs ws Hwords i d Hnth). apply Hrefined.
Qed.

(** Every lawful numeric domain and operator bridge yield lawful sparse transfers. *)
Theorem sparse_of_numeric_laws {A K C} (ND : numeric_domain A)
    (G : concretisation A word) (br : op_bridge K C) (top : A)
    (truth : C -> bool) (op_eval : K -> list C -> option C) :
  numeric_laws ND G -> op_bridge_laws br op_eval truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) -> leb (lat ND) top (bot (lat ND)) = false ->
  sparse_domain_laws (sparse_of_numeric ND G br top) truth op_eval.
Proof.
  intros Hnumeric Hbridge Htop Hnotbot. constructor.
  - exact (lat_laws Hnumeric).
  - exact (numeric_conc_laws ND G br Hnumeric).
  - intro c. cbn. destruct (to_word br c) as [w|].
    + exact (gamma_bot_empty (bot_empty Hnumeric) w).
    + rewrite (leb_refl (lat_laws Hnumeric)). discriminate.
  - exact (numeric_top_sound ND G br top truth op_eval Hbridge Htop Hnotbot).
  - exact (numeric_op_sound ND G br top truth op_eval Hnumeric Hbridge Htop Hnotbot).
  - exact (numeric_assume_value_sound ND G br top truth op_eval Hnumeric Hbridge).
  - exact (numeric_assume_args_sound ND G br top truth op_eval Hnumeric Hbridge Htop).
Qed.

(** Sparse numeric post-solutions describe every present reachable client value. *)
Theorem numeric_value_sound {S O N E V K C A} (EN : encoding N) (EV : encoding V)
    (m : semantics S O) (ND : numeric_domain A)
    (G : concretisation A word) (br : op_bridge K C) (top : A) (sv : ssa_view S O N E V K C)
    (vals : list V) (entry : V -> A) (sigma : sparse_unknown N E V -> lift_bot A) :
  ssa_view_laws m sv -> numeric_laws ND G -> op_bridge_laws br (op_eval sv) (truth sv) ->
  (forall w z, is_word w z -> gamma G top (w, z)) -> leb (lat ND) top (bot (lat ND)) = false ->
  (forall s x c, reachable_state m s -> val sv s x = Some c -> In x vals) ->
  (forall s x c, initial m s -> val sv s x = Some c ->
     exists b i, def sv x = Param b i /\ In b (Graph.entries (cfg (base sv))) /\
       gamma (fact_conc (sparse_of_numeric ND G br top)) (entry x) c) ->
  post_solution (lift_bot_lattice (lat ND))
    (sparse_system EN EV (numeric_problem ND G br top sv vals entry)) sigma ->
  forall s x c, reachable_state m s -> val sv s x = Some c ->
    gamma (lift_bot_gamma (fact_conc (sparse_of_numeric ND G br top))) (sigma (UVal x)) c.
Proof.
  intros Hview Hnumeric Hbridge Htop Hnotbot Hcoverage Hinitial Hpost.
  exact (proj2 (proj2 (sparse_sound EN EV m (numeric_problem ND G br top sv vals entry)
    sigma Hview (sparse_of_numeric_laws ND G br top (truth sv) (op_eval sv)
      Hnumeric Hbridge Htop Hnotbot) Hcoverage Hinitial Hpost))).
Qed.
