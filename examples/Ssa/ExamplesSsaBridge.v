(** * Shared SSA bridges

    These bridges connect source integer operations and selected edges to prepared adapters.
    For example, shifting a 32-bit value by 32 uses the toy's reduced amount zero.
    Builds on: ExamplesSsaSemantics, ExamplesSsaTypingProofs, AnalysesValues and GraphCore. *)

From Stdlib Require Import List ZArith Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderBasic OrderPointwise.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsSemantics ViewsAgreement ViewsEffects ViewsSsaPoints.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsExpr.
From Gaulois.Analyses Require Import AnalysesValues AnalysesDemand.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs.
Import List.ListNotations.
Local Open Scope Z_scope.

(** Integer truth depends only on whether the payload is zero. *)
Definition ssa_truth (c : cval) : bool :=
  match c with
  | VInt _ z => negb (Z.eqb z 0)
  | _ => false
  end.

Definition ssa_width (w : iw) : width :=
  match w with
  | W32 => 32%positive
  | W64 => 64%positive
  end.

Definition ssa_binary_expr (w : iw) (o : bop) : Bits.expr :=
  let args := [Bits.Var 0; Bits.Var 1] in
  let cmp op := Bits.App (bvzext 31) [Bits.App op args] in
  let shift op := Bits.App op
    [Bits.Var 0; Bits.App bvurem [Bits.Var 1; Bits.Const (ssa_width w) (iw_bits w)]] in
  match o with
  | BAdd => Bits.App bvadd args
  | BSub => Bits.App bvsub args
  | BMul => Bits.App bvmul args
  | BDivU => Bits.App bvudiv args
  | BAnd => Bits.App bvand args
  | BOr => Bits.App bvor args
  | BXor => Bits.App bvxor args
  | BShl => shift bvshl
  | BShrU => shift bvlshr
  | BEq => cmp bveq
  | BLtU => cmp bvult
  | BLtS => cmp bvslt
  end.

Definition ssa_op_expr (o : sop) : option Bits.expr :=
  match o with
  | OBin w op => Some (ssa_binary_expr w op)
  | OZext => Some (Bits.App (bvzext 32) [Bits.Var 0])
  | OTrunc => Some (Bits.App (bvextract 31 0) [Bits.Var 0])
  | _ => None
  end.

Definition ssa_to_word (c : cval) : option word :=
  match c with
  | VInt w z => if word_ok w z then Some (ssa_width w, z) else None
  | _ => None
  end.

(** The bridge supports integer binary operations and the two integer width conversions. *)
Definition ssa_bridge : op_bridge sop cval := OpBridge ssa_op_expr ssa_to_word.

Local Lemma ssa_word_valid w z :
  valid_cval (VInt w z) <-> is_word (ssa_width w) z.
Proof.
  destruct w; reflexivity.
Qed.

Local Lemma ssa_word_wrap w z : word_wrap w z = wrap (ssa_width w) z.
Proof.
  destruct w; reflexivity.
Qed.

Local Lemma ssa_word_signed w z :
  word_signed w z =
    if z <? half (ssa_width w) then z else z - modulus (ssa_width w).
Proof.
  destruct w; reflexivity.
Qed.

Local Lemma ssa_to_word_integer w z :
  valid_cval (VInt w z) -> ssa_to_word (VInt w z) = Some (ssa_width w, z).
Proof.
  intro Hvalid; unfold ssa_to_word; rewrite (proj2 (word_ok_valid w z) Hvalid); reflexivity.
Qed.

Local Lemma ssa_bin_eval ext w o a b r :
  op_eval ext (OBin w o) [VInt w a; VInt w b] = Some r ->
  valid_cval (VInt w a) /\ valid_cval (VInt w b) /\ bin_eval w o a b = Some r.
Proof.
  cbn [op_eval]; destruct (iw_eq_dec w w); [|contradiction].
  destruct (word_ok w a && word_ok w b) eqn:Hvalid; [|discriminate].
  apply andb_true_iff in Hvalid; destruct Hvalid as [Ha Hb].
  intro Heval; split; [apply word_ok_valid; exact Ha|].
  split; [apply word_ok_valid; exact Hb|exact Heval].
Qed.

Local Lemma ssa_shift_amount w b :
  wrap (ssa_width w) (iw_bits w) = iw_bits w /\
  wrap (ssa_width w) (b mod iw_bits w) = b mod iw_bits w /\
  (iw_bits w <=? b mod iw_bits w) = false.
Proof.
  destruct w; cbn [ssa_width iw_bits];
    pose proof (Z.mod_pos_bound b 32 ltac:(lia)) as H32;
    pose proof (Z.mod_pos_bound b 64 ltac:(lia)) as H64;
    split; [apply wrap_id; change (0 <= 32 < 4294967296); lia|
      split; [apply wrap_id; change (0 <= b mod 32 < 4294967296); lia|
        apply Z.leb_gt; lia]|
      apply wrap_id; change (0 <= 64 < 18446744073709551616); lia|
      split; [apply wrap_id; change (0 <= b mod 64 < 18446744073709551616); lia|
        apply Z.leb_gt; lia]].
Qed.

Local Lemma ssa_expr_binary w o a b r :
  valid_cval (VInt w a) -> valid_cval (VInt w b) -> bin_eval w o a b = Some r ->
  exists wr,
    Bits.eval (fun i => nth i [(ssa_width w, a); (ssa_width w, b)] (1%positive, 0))
      (ssa_binary_expr w o) = Some wr /\ ssa_to_word r = Some wr.
Proof.
  intros Ha Hb Heval.
  pose proof (bin_eval_valid w o a b r Heval) as Hr.
  apply ssa_word_valid in Ha; apply ssa_word_valid in Hb.
  destruct w; destruct o;
    cbn [bin_eval] in Heval;
    try (destruct (b =? 0) eqn:Hzero; [discriminate|]);
    inversion Heval; subst r.
  all: apply ssa_to_word_integer in Hr; rewrite ?ssa_word_wrap in Hr.
  all: cbn [ssa_width] in Ha, Hb.
  all: eexists; split; [|exact Hr].
  all: cbn [ssa_binary_expr ssa_width iw_bits Bits.eval eval_op result_width op_value
      normalize_word word_fun2 word_cmp nth map fst snd Pos.eqb];
    rewrite ?wrap_wrap, ?(wrap_id _ _ Ha), ?(wrap_id _ _ Hb).
  all: unfold wadd, wsub, wmul, wudiv, wand, wor, wxor, wshl, wlshr, wurem, wult, wslt,
    signed; rewrite ?wrap_wrap, ?(wrap_id _ _ Ha), ?(wrap_id _ _ Hb).
  all: try rewrite Hzero.
  all: try reflexivity.
  all: try (unfold word_signed; cbn [iw_bits half modulus];
    match goal with |- context [if ?test then 1 else 0] =>
      destruct test; rewrite ?wrap_0, ?wrap_1; reflexivity
    end).
  all: try (match goal with |- context [wrap ?width ?bits] =>
    first [let H := fresh "Hamount" in
      pose proof (ssa_shift_amount W32 b) as H; cbn [ssa_width iw_bits] in H;
      destruct H as [Hwidth [Hamount Hlarge]];
      rewrite Hwidth; cbn [Z.eqb]; rewrite Hamount, Hlarge|
      let H := fresh "Hamount" in
      pose proof (ssa_shift_amount W64 b) as H; cbn [ssa_width iw_bits] in H;
      destruct H as [Hwidth [Hamount Hlarge]];
      rewrite Hwidth; cbn [Z.eqb]; rewrite Hamount, Hlarge]
    end;
    rewrite ?wrap_wrap;
    first [rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia)|
      rewrite Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia)]; reflexivity).
  all: rewrite !ssa_word_signed; cbn [ssa_width];
    match goal with |- context [if ?test then 1 else 0] =>
      destruct test; rewrite ?wrap_0, ?wrap_1; reflexivity
    end.
Qed.

(** Every supported successful SSA operation has the same word result and truth as Bits. *)
Theorem ssa_bridge_laws (ext : nat -> list cval -> option cval) :
  op_bridge_laws ssa_bridge (op_eval ext) ssa_truth.
Proof.
  constructor.
  - intros [w z|block offset|f|z|z] wr Hword; try discriminate.
    cbn [ssa_bridge to_word ssa_to_word] in Hword.
    destruct (word_ok w z) eqn:Hvalid; [|discriminate].
    inversion Hword; apply ssa_word_valid, word_ok_valid; exact Hvalid.
  - intros [c|w o| | | |tag] cs r e Heval Hexpr;
      cbn [ssa_bridge op_expr ssa_op_expr] in Hexpr; try discriminate.
    + inversion Hexpr; subst e.
      destruct cs as [|c [|d [|u rest]]];
        try solve [destruct c; discriminate];
        try solve [destruct c, d; discriminate]; try discriminate.
      destruct c as [wa a|block offset|f|z|z]; cbn [op_eval] in Heval;
        try discriminate.
      destruct d as [wb b|block offset|f|z|z]; cbn [op_eval] in Heval;
        try discriminate.
      destruct (iw_eq_dec w wa) as [<-|Hne]; [|discriminate].
      destruct (iw_eq_dec w wb) as [<-|Hne]; [|discriminate].
      destruct (word_ok w a && word_ok w b) eqn:Hvalid; [|discriminate].
      apply andb_true_iff in Hvalid; destruct Hvalid as [Ha Hb].
      apply word_ok_valid in Ha; apply word_ok_valid in Hb.
      destruct (ssa_expr_binary w o a b r Ha Hb Heval) as [wr [Hbits Hword]].
      exists [(ssa_width w, a); (ssa_width w, b)], wr; split.
      * constructor; [apply ssa_to_word_integer; exact Ha|].
        constructor; [apply ssa_to_word_integer; exact Hb|constructor].
      * split; assumption.
    + inversion Hexpr; subst e.
      destruct cs as [|c [|d rest]];
        try solve [destruct c as [[|] a|block offset|f|z|z]; discriminate];
        try discriminate.
      destruct c as [[|] a|block offset|f|z|z]; try discriminate.
      cbn [op_eval] in Heval; destruct (word_ok W32 a) eqn:Hvalid; [|discriminate].
      inversion Heval; subst r.
      exists [(32%positive, a)], (64%positive, a); split.
      * constructor; [apply ssa_to_word_integer, word_ok_valid; exact Hvalid|constructor].
      * split.
        -- cbn [Bits.eval eval_op result_width op_value normalize_word nth map fst snd].
           rewrite !(wrap_id 32%positive a) by
             (apply (proj1 (ssa_word_valid W32 a)), word_ok_valid; exact Hvalid).
           rewrite wrap_id; [reflexivity|].
           apply word_ok_valid in Hvalid; cbn [valid_cval] in Hvalid.
           change (0 <= a < 18446744073709551616); lia.
        -- apply ssa_to_word_integer; apply word_ok_valid in Hvalid.
           cbn [valid_cval] in *; lia.
    + inversion Hexpr; subst e.
      destruct cs as [|c [|d rest]];
        try solve [destruct c as [[|] a|block offset|f|z|z]; discriminate];
        try discriminate.
      destruct c as [[|] a|block offset|f|z|z]; try discriminate.
      cbn [op_eval] in Heval; destruct (word_ok W64 a) eqn:Hvalid; [|discriminate].
      inversion Heval; subst r.
      exists [(64%positive, a)], (32%positive, word_wrap W32 a); split.
      * constructor; [apply ssa_to_word_integer, word_ok_valid; exact Hvalid|constructor].
      * split.
        -- cbn [Bits.eval eval_op result_width op_value normalize_word nth map fst snd].
           rewrite !(wrap_id 64%positive a) by
             (apply (proj1 (ssa_word_valid W64 a)), word_ok_valid; exact Hvalid).
           change (Some (32%positive, wrap 32%positive (wrap 64%positive a / 1)) =
             Some (32%positive, word_wrap W32 a)).
           rewrite Z.div_1_r.
           rewrite (wrap_id 64%positive a) by
             (apply (proj1 (ssa_word_valid W64 a)), word_ok_valid; exact Hvalid).
           reflexivity.
        -- apply ssa_to_word_integer, word_wrap_valid.
  - intros [w z|block offset|f|z|z] wr Hword; try discriminate.
    cbn [ssa_bridge to_word ssa_to_word] in Hword.
    destruct (word_ok w z); [|discriminate]; inversion Hword; reflexivity.
Qed.

(** * Shared prepared graph construction *)

Definition ssa_get {K A} (E : encoding K) (index : Map.t K A) (fallback : A) (k : K) : A :=
  match Map.get E k index with
  | Some a => a
  | None => fallback
  end.

Definition ssa_key_eq_dec {K} (E : encoding K) (x y : K) : {x = y} + {x <> y}.
Proof.
  destruct (Pos.eq_dec (encode E x) (encode E y)) as [Heq|Hdifferent].
  - left; apply (encode_injective E); exact Heq.
  - right; intro Heq; subst y; contradiction.
Defined.

Lemma ssa_map_get_sound {K A} (E : encoding K) (rows : list (K * A)) k a :
  Map.get E k (Map.of_list E rows) = Some a -> In (k, a) rows.
Proof.
  rewrite Map.get_of_list.
  destruct (find (fun row => Pos.eqb (encode E (fst row)) (encode E k)) (rev rows))
    as [[key value]|] eqn:Hfind; [|discriminate].
  cbn; intro Hvalue; injection Hvalue as <-.
  apply find_some in Hfind; destruct Hfind as [Hin Hkey].
  apply Pos.eqb_eq, (encode_injective E) in Hkey; cbn in Hkey; subst key.
  apply in_rev; exact Hin.
Qed.

Lemma ssa_map_get_complete {K A} (E : encoding K) (rows : list (K * A)) k a :
  In (k, a) rows -> (forall other, In (k, other) rows -> other = a) ->
  Map.get E k (Map.of_list E rows) = Some a.
Proof.
  intros Hin Hunique; rewrite Map.get_of_list.
  destruct (find (fun row => Pos.eqb (encode E (fst row)) (encode E k)) (rev rows))
    as [[key value]|] eqn:Hfind.
  - apply find_some in Hfind; destruct Hfind as [Hmember Hkey].
    apply Pos.eqb_eq, (encode_injective E) in Hkey; cbn in Hkey; subst key.
    apply in_rev in Hmember; rewrite (Hunique value Hmember); reflexivity.
  - assert (Hmember : In (k, a) (rev rows)) by
      (apply (proj1 (in_rev rows (k, a))); exact Hin).
    pose proof (find_none _ _ Hfind (k, a) Hmember) as Hnone.
    cbn in Hnone; rewrite Pos.eqb_refl in Hnone; discriminate.
Qed.

Definition ssa_outgoing_index {N E A} (EN : encoding N) (source : A -> N)
    (rows : list (E * A)) : Map.t N (list E) :=
  fold_right (fun ep acc =>
    let n := source (snd ep) in
    Map.set EN n (fst ep :: ssa_get EN acc [] n) acc) Map.empty rows.

Definition ssa_graph_of_rows {N E A} (EN : encoding N) (EE : encoding E)
    (entries nodes : list N) (source target : A -> N) (fallback : N)
    (rows : list (E * A)) : Graph.t N E :=
  let index := Map.of_list EE rows in
  Graph.Make entries nodes (ssa_get EN (ssa_outgoing_index EN source rows) [])
    (fun e => match Map.get EE e index with
     | Some p => source p
     | None => fallback
     end)
    (fun e => match Map.get EE e index with
     | Some p => target p
     | None => fallback
     end).

Lemma ssa_outgoing_member {N E A} (EN : encoding N) (source : A -> N)
    (rows : list (E * A)) n e :
  In e (ssa_get EN (ssa_outgoing_index EN source rows) [] n) <->
    exists p, In (e, p) rows /\ source p = n.
Proof.
  induction rows as [|[edge p] rows IH]; cbn [ssa_outgoing_index fold_right fst snd].
  - unfold ssa_get; rewrite Map.get_empty; cbn; split; [tauto|intros [p [Hfalse _]]; tauto].
  - unfold ssa_get at 1; destruct (ssa_key_eq_dec EN n (source p)) as [->|Hdifferent].
    + rewrite Map.get_set_same; cbn [In].
      rewrite IH; split.
      * intros [<-|[value [Hin Hsource]]].
        -- exists p; split; [left; reflexivity|reflexivity].
        -- exists value; split; [right; exact Hin|exact Hsource].
      * intros [value [[Heq|Hin] Hsource]].
        -- injection Heq as <- <-; left; reflexivity.
        -- right; exists value; split; assumption.
    + rewrite Map.get_set_other by exact Hdifferent.
      change (In e (ssa_get EN (ssa_outgoing_index EN source rows) [] n) <->
        exists value, In (e, value) ((edge, p) :: rows) /\ source value = n).
      rewrite IH; split.
      * intros [value [Hin Hsource]]; exists value; split; [right; exact Hin|exact Hsource].
      * intros [value [[Heq|Hin] Hsource]].
        -- injection Heq as <- <-; exfalso; apply Hdifferent; symmetry; exact Hsource.
        -- exists value; split; assumption.
Qed.

(** Unique row keys give duplicate-free outgoing occurrence lists. *)
Lemma ssa_outgoing_nodup {N E A} (EN : encoding N) (source : A -> N) rows :
  NoDup (map (@fst E A) rows) ->
  forall n, NoDup (ssa_get EN (ssa_outgoing_index EN source rows) [] n).
Proof.
  induction rows as [|[edge p] rows IH]; intros Hunique n.
  - cbn [ssa_outgoing_index fold_right]; unfold ssa_get; rewrite Map.get_empty; constructor.
  - inversion Hunique as [|key keys Hfresh Htail]; subst.
    cbn [ssa_outgoing_index fold_right fst snd]; unfold ssa_get at 1.
    destruct (ssa_key_eq_dec EN n (source p)) as [->|Hdifferent].
    + rewrite Map.get_set_same; constructor; [|exact (IH Htail (source p))].
      intro Hin; apply ssa_outgoing_member in Hin; destruct Hin as [q [Hrow _]].
      apply Hfresh, in_map_iff; exists (edge, q); split; [reflexivity|exact Hrow].
    + rewrite Map.get_set_other by exact Hdifferent; exact (IH Htail n).
Qed.

(** A prepared graph is well formed when its unique payload rows have listed endpoints. *)
Lemma ssa_graph_of_rows_wf {N E A} (EN : encoding N) (EE : encoding E)
    entries nodes (source target : A -> N) fallback rows :
  NoDup nodes -> incl entries nodes ->
  (forall e p q, In (e, p) rows -> In (e, q) rows -> p = q) ->
  (forall e p, In (e, p) rows -> In (target p) nodes) ->
  graph_wf (ssa_graph_of_rows EN EE entries nodes source target fallback rows).
Proof.
  intros Hnodes Hentries Hunique Htarget; constructor; try assumption.
  - intros n e Hedge; apply ssa_outgoing_member in Hedge.
    destruct Hedge as [p [Hin Hsource]].
    cbn [ssa_graph_of_rows Graph.source].
    rewrite (ssa_map_get_complete EE rows e p Hin (fun q Hq => Hunique e q p Hq Hin)).
    exact Hsource.
  - intros n e Hnode Hedge; apply ssa_outgoing_member in Hedge.
    destruct Hedge as [p [Hin Hsource]].
    cbn [ssa_graph_of_rows Graph.target].
    rewrite (ssa_map_get_complete EE rows e p Hin (fun q Hq => Hunique e q p Hq Hin)).
    exact (Htarget e p Hin).
Qed.

(** * Selected source control edges *)

Local Open Scope nat_scope.

Fixpoint ssa_switch_slot (z : Z) (cases : list (Z * label * list vid)) : nat :=
  match cases with
  | [] => 0
  | ((key, _), _) :: rest =>
    if Z.eqb z (word_wrap W32 key) then 0 else S (ssa_switch_slot z rest)
  end.

Definition ssa_term_slot (env : vid -> option cval) (t : terminator) : option nat :=
  match t with
  | TJump _ _ | TCall _ _ _ | TRet _ => Some 0
  | TBr c _ _ _ _ =>
    match env c with
    | Some (VInt W32 z) => Some (if Z.eqb z 0 then 1 else 0)
    | _ => None
    end
  | TSwitch c cases _ _ =>
    match env c with
    | Some (VInt W32 z) => Some (ssa_switch_slot z cases)
    | _ => None
    end
  end.

Lemma ssa_switch_slot_target z cases d da :
  nth_error (term_edges (TSwitch 0 cases d da)) (ssa_switch_slot z cases) =
    Some (switch_target z cases d da).
Proof.
  induction cases as [|[[key l] args] cases IH]; [reflexivity|].
  cbn [term_edges ssa_switch_slot switch_target map app].
  rewrite (Z.eqb_sym z (word_wrap W32 key)).
  destruct (Z.eqb (word_wrap W32 key) z); [reflexivity|exact IH].
Qed.

(** * Source binding equations *)

Lemma ssa_read_args_complete (env : vid -> option cval) xs cs :
  Forall2 (fun x c => env x = Some c) xs cs -> read_args env xs = Some cs.
Proof.
  intro Hvalues; induction Hvalues as [|x c xs cs Hvalue Hvalues IH].
  - reflexivity.
  - cbn [read_args]; rewrite Hvalue, IH; reflexivity.
Qed.

Lemma ssa_bind_length env ps cs env' :
  bind_params env ps cs = Some env' -> length ps = length cs.
Proof.
  revert env cs; induction ps as [|[x t] ps IH]; intros env [|c cs] Hbind;
    cbn [bind_params] in Hbind; try discriminate; [reflexivity|].
  cbn [length]; f_equal; eapply IH; exact Hbind.
Qed.

Lemma ssa_bind_exists env ps cs :
  length ps = length cs -> exists env', bind_params env ps cs = Some env'.
Proof.
  revert env cs; induction ps as [|[x t] ps IH]; intros env [|c cs] Hlength;
    cbn [length] in Hlength; try discriminate.
  - exists env; reflexivity.
  - cbn [bind_params]; apply IH; lia.
Qed.

Definition ssa_env_agrees (env env' : vid -> option cval) : Prop :=
  forall x, env x = env' x.

Lemma ssa_set_agrees env env' x v :
  ssa_env_agrees env env' -> ssa_env_agrees (env_set env x v) (env_set env' x v).
Proof.
  intros Hagree y; unfold env_set; destruct (Nat.eq_dec y x); [reflexivity|apply Hagree].
Qed.

Lemma ssa_read_agrees env env' xs :
  ssa_env_agrees env env' -> read_args env xs = read_args env' xs.
Proof.
  intro Hagree; induction xs as [|x xs IH]; [reflexivity|].
  cbn [read_args]; rewrite Hagree, IH; reflexivity.
Qed.

Lemma ssa_bind_agrees env env' ps cs target :
  ssa_env_agrees env env' -> bind_params env ps cs = Some target ->
  exists target', bind_params env' ps cs = Some target' /\ ssa_env_agrees target target'.
Proof.
  revert env env' cs; induction ps as [|[x t] ps IH];
    intros env env' [|c cs] Hagree Hbind; cbn [bind_params] in Hbind; try discriminate.
  - injection Hbind as <-; exists env'; split; [reflexivity|exact Hagree].
  - eapply IH; [apply ssa_set_agrees; exact Hagree|exact Hbind].
Qed.

(** Reading an operand list depends only on its listed bindings, retaining duplicates. *)
Lemma ssa_read_equal_on env env' xs :
  (forall x, In x xs -> env x = env' x) -> read_args env xs = read_args env' xs.
Proof.
  intro Hagree; induction xs as [|x xs IH]; [reflexivity|].
  cbn [read_args]; rewrite Hagree by (left; reflexivity).
  rewrite IH; [reflexivity|intros y Hin; apply Hagree; right; exact Hin].
Qed.

(** A parallel bind preserves every source variable outside its parameter list. *)
Lemma ssa_bind_frame env ps cs target x :
  bind_params env ps cs = Some target -> ~ In x (map fst ps) -> target x = env x.
Proof.
  revert env cs; induction ps as [|[y t] ps IH];
    intros env [|v cs] Hbind Houtside; cbn [bind_params] in Hbind; try discriminate.
  - injection Hbind as <-; reflexivity.
  - rewrite (IH (env_set env y v) cs Hbind).
    + unfold env_set; destruct (Nat.eq_dec x y) as [->|Hdifferent]; [|reflexivity].
      exfalso; apply Houtside; left; reflexivity.
    + intro Hin; apply Houtside; right; exact Hin.
Qed.

(** Equal incoming values give equal new parameter bindings, even with duplicate parameters. *)
Lemma ssa_bind_written env env' ps cs target target' :
  bind_params env ps cs = Some target -> bind_params env' ps cs = Some target' ->
  forall x, In x (map fst ps) -> target x = target' x.
Proof.
  revert env env' cs; induction ps as [|[y t] ps IH];
    intros env env' [|v cs] Hbind Hbind' x Hin;
    cbn [bind_params] in Hbind, Hbind'; try discriminate; [contradiction|].
  destruct (in_dec Nat.eq_dec x (map fst ps)) as [Htail|Houtside].
  - eapply IH; eassumption.
  - cbn in Hin; destruct Hin as [<-|Hfalse]; [|contradiction].
    rewrite (ssa_bind_frame _ _ _ _ _ Hbind Houtside),
      (ssa_bind_frame _ _ _ _ _ Hbind' Houtside).
    unfold env_set; destruct (Nat.eq_dec y y); [reflexivity|contradiction].
Qed.

(** A typed operand list names only bindings present in the static environment. *)
Lemma ssa_types_defined T xs ps :
  types_of T xs = Some ps -> Forall (fun x => exists ty, T x = Some ty) xs.
Proof.
  revert ps; induction xs as [|x xs IH]; intros ps Htypes; [constructor|].
  cbn [types_of] in Htypes; destruct (T x) as [ty|] eqn:Hx; [|discriminate].
  destruct (types_of T xs) as [rest|] eqn:Hrest; [|discriminate].
  constructor; [exists ty; exact Hx|eapply IH; reflexivity].
Qed.

Lemma ssa_types_length T xs ps : types_of T xs = Some ps -> length xs = length ps.
Proof.
  revert ps; induction xs as [|x xs IH]; intros ps Htypes; cbn [types_of] in Htypes.
  - injection Htypes as <-; reflexivity.
  - destruct (T x) as [ty|]; [|discriminate].
    destruct (types_of T xs) as [rest|] eqn:Hrest; [|discriminate].
    injection Htypes as <-; cbn; f_equal; apply IH; reflexivity.
Qed.

Lemma ssa_typed_jump_arity B T dst args target :
  typed_jump B T (dst, args) -> B dst = Some target ->
  length args = length (bparams target).
Proof.
  unfold typed_jump; cbn; intros Htyped Htarget; rewrite Htarget in Htyped.
  pose proof (ssa_types_length T args _ Htyped) as Hlength.
  rewrite length_map in Hlength; exact Hlength.
Qed.

Lemma ssa_instruction_types_defined P T i :
  instr_typed P T i -> Forall (fun x => exists ty, T x = Some ty) (instr_uses i).
Proof.
  unfold instr_typed; destruct (instr_sig P T i) as [[ps result]|]; [|contradiction].
  intros [Htypes Hresult]; eapply ssa_types_defined; exact Htypes.
Qed.

Lemma ssa_jump_types_defined B T dst args :
  typed_jump B T (dst, args) -> Forall (fun x => exists ty, T x = Some ty) args.
Proof.
  unfold typed_jump; cbn; destruct (B dst); [|contradiction].
  apply ssa_types_defined.
Qed.

Lemma ssa_term_edge_types_defined P fd T B t dst args :
  term_typed P fd T B t -> In (dst, args) (term_edges t) ->
  Forall (fun x => exists ty, T x = Some ty) args.
Proof.
  intros Htyped Hedge; destruct t; cbn [term_typed] in Htyped.
  - eapply ssa_jump_types_defined; exact (proj1 (Forall_forall _ _) Htyped _ Hedge).
  - eapply ssa_jump_types_defined; exact
      (proj1 (Forall_forall _ _) (proj2 Htyped) _ Hedge).
  - eapply ssa_jump_types_defined; exact
      (proj1 (Forall_forall _ _) (proj2 Htyped) _ Hedge).
  - cbn [term_edges] in Hedge; destruct Hedge as [Heq|Hfalse]; [|contradiction].
    injection Heq as <- <-; constructor.
  - contradiction.
Qed.

Lemma ssa_call_types_defined P fd T B c args k :
  term_typed P fd T B (TCall c args k) ->
  Forall (fun x => exists ty, T x = Some ty) (term_uses (TCall c args k)).
Proof.
  cbn [term_typed]; destruct (callee_sig P T c) as [[ps r]|] eqn:Hsig;
    [|contradiction].
  destruct (B k); [|contradiction]; intros [Hargs Hparams].
  pose proof (ssa_types_defined T args ps Hargs) as Hdefined.
  destruct c as [target|x parameters result]; [exact Hdefined|].
  constructor; [|exact Hdefined].
  unfold callee_sig, callee_sig_with in Hsig; destruct (T x) as [ty|] eqn:Hx;
    [|discriminate]; destruct ty; try discriminate; eexists; reflexivity.
Qed.

Lemma ssa_combine_right {A B} (xs : list A) (ys : list B) x y :
  In (x, y) (combine xs ys) -> In y ys.
Proof.
  revert ys; induction xs as [|a xs IH]; intros [|b ys] Hin;
    cbn in Hin; try contradiction.
  destruct Hin as [Heq|Hin]; [injection Heq as <- <-; left; reflexivity|].
  right; eapply IH; exact Hin.
Qed.

Lemma ssa_parameter_back_uses parameters args x ys y :
  Map.get nat_encoding x (Map.of_list nat_encoding
    (map (fun xy : vid * vid => (fst xy, [snd xy])) (combine parameters args))) = Some ys ->
  In y ys -> In y args.
Proof.
  intros Hget Hy; apply (ssa_map_get_sound nat_encoding) in Hget.
  apply in_map_iff in Hget; destruct Hget as [[parameter argument] [Heq Hin]].
  cbn in Heq; injection Heq as <- <-; destruct Hy as [<-|Hfalse]; [|contradiction].
  eapply ssa_combine_right; exact Hin.
Qed.

Lemma ssa_combine_member_left {A B} (xs : list A) (ys : list B) x :
  length xs = length ys -> In x xs -> exists y, In (x, y) (combine xs ys).
Proof.
  revert ys; induction xs as [|a xs IH]; intros [|b ys] Hlength Hin;
    cbn in Hlength, Hin; try discriminate; try contradiction.
  destruct Hin as [<-|Hin]; [exists b; left; reflexivity|].
  destruct (IH ys ltac:(lia) Hin) as [y Hy]; exists y; right; exact Hy.
Qed.

Lemma ssa_combine_unique {A B} (xs : list A) (ys : list B) x y z :
  NoDup xs -> In (x, y) (combine xs ys) -> In (x, z) (combine xs ys) -> y = z.
Proof.
  revert ys; induction xs as [|a xs IH]; intros [|b ys] Hunique Hy Hz;
    cbn in Hy, Hz; try contradiction.
  inversion Hunique as [|head tail Hfresh Htail]; subst.
  destruct Hy as [Heq|Hy], Hz as [Heq'|Hz].
  - congruence.
  - injection Heq as <- <-; exfalso; apply Hfresh; eapply in_combine_l; exact Hz.
  - injection Heq' as <- <-; exfalso; apply Hfresh; eapply in_combine_l; exact Hy.
  - eapply IH; eassumption.
Qed.

Lemma ssa_parameter_back_argument (parameters args : list vid) (x : vid) :
  NoDup parameters -> length parameters = length args -> In x parameters ->
  exists y, Map.get nat_encoding x (Map.of_list nat_encoding
    (map (fun xy : vid * vid => (fst xy, [snd xy])) (combine parameters args))) = Some [y] /\
    In (x, y) (combine parameters args).
Proof.
  intros Hunique Hlength Hx.
  destruct (ssa_combine_member_left parameters args x Hlength Hx) as [y Hy].
  exists y; split; [|exact Hy]; apply ssa_map_get_complete.
  - apply in_map_iff; exists (x, y); split; [reflexivity|exact Hy].
  - intros ys Hrow; apply in_map_iff in Hrow.
    destruct Hrow as [[key value] [Heq Hin]]; cbn in Heq;
      injection Heq as Hkey Hys; subst key ys.
    rewrite (ssa_combine_unique parameters args x value y Hunique Hin Hy); reflexivity.
Qed.

Lemma ssa_flat_map_nodup_member {A B} (f : A -> list B) xs x :
  NoDup (flat_map f xs) -> In x xs -> NoDup (f x).
Proof.
  induction xs as [|a xs IH]; [contradiction|].
  cbn [flat_map]; intros Hunique [<-|Hin].
  - exact (NoDup_app_remove_r _ _ Hunique).
  - apply IH; [exact (NoDup_app_remove_l _ _ Hunique)|exact Hin].
Qed.

Lemma ssa_map_nodup {A B} (f : A -> B) xs :
  (forall x y, f x = f y -> x = y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros Hinjective Hunique; induction Hunique as [|x xs Hfresh Htail IH]; cbn.
  - constructor.
  - constructor; [|exact IH]; intro Hin; apply in_map_iff in Hin.
    destruct Hin as [y [Heq Hy]]; apply Hinjective in Heq; subst y; exact (Hfresh Hy).
Qed.

(** A consecutive instruction prefix attaches to one already-proved terminal chain. *)
Lemma ssa_point_chain_prefix {N E} (g : Graph.t N E) (node : nat -> N) (edge : nat -> E)
    start count ns es :
  (forall pc, start <= pc < start + count ->
    In (edge pc) (Graph.out g (node pc)) /\ Graph.target g (edge pc) = node (S pc)) ->
  point_chain g (node (start + count) :: ns) es ->
  point_chain g (node start :: map node (seq (S start) count) ++ ns)
    (map edge (seq start count) ++ es).
Proof.
  revert start; induction count as [|count IH]; intros start Hedges Htail.
  - cbn; rewrite Nat.add_0_r in Htail; exact Htail.
  - cbn [seq map app].
    destruct (Hedges start ltac:(lia)) as [Hout Htarget].
    eapply point_chain_step; [exact Hout|exact Htarget|].
    apply IH.
    + intros pc Hpc; apply Hedges; lia.
    + replace (S start + count) with (start + S count) by lia; exact Htail.
Qed.

Lemma ssa_no_syntactic_live {N E V} (p : point_uses N E V) n x :
  Graph.out (live_graph p) n = [] -> exit_use p n = [] -> ~ syntactic_live p x n.
Proof.
  intros Hout Hexit Hlive; destruct Hlive as [n Huse|n e Hedge Huse|n e Hedge Hkill Hnext].
  - rewrite Hexit in Huse; contradiction.
  - rewrite Hout in Hedge; contradiction.
  - rewrite Hout in Hedge; contradiction.
Qed.

Lemma ssa_parameter_nodup ext P f fd l b :
  wf_program ext P -> find_func P f = Some fd -> find_block fd l = Some b ->
  NoDup (map fst (bparams b)).
Proof.
  intros [_ [_ [Hunique _]]] Hf Hb.
  pose proof (ssa_flat_map_nodup_member _ _ (f, fd) Hunique
    (first_index_sound _ _ _ Hf)) as Hfunction.
  pose proof (ssa_flat_map_nodup_member _ _ (l, b) Hfunction
    (first_index_sound _ _ _ Hb)) as Hblock.
  exact (NoDup_app_remove_r _ _ Hblock).
Qed.

(** Parameter values come from the already-read incoming operand list. *)
Lemma ssa_bind_argument env input ps args cs target x y :
  NoDup (map fst ps) -> bind_params env ps cs = Some target ->
  read_args input args = Some cs -> In (x, y) (combine (map fst ps) args) ->
  target x = input y.
Proof.
  revert env args cs; induction ps as [|[p ty] ps IH];
    intros env [|a args] [|v cs] Hunique Hbind Hread Hin;
    cbn [bind_params read_args combine map] in Hbind, Hread, Hin;
    try discriminate; try contradiction.
  destruct (input a) as [c|] eqn:Ha; [|discriminate].
  destruct (read_args input args) as [actual|] eqn:Hargs; [|discriminate].
  injection Hread as <- <-; inversion Hunique as [|key keys Hfresh Htail]; subst.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-.
    rewrite (ssa_bind_frame _ _ _ _ _ Hbind Hfresh); unfold env_set.
    destruct (Nat.eq_dec p p); [exact (eq_sym Ha)|contradiction].
  - eapply IH; eassumption.
Qed.

Lemma ssa_read_length env xs cs : read_args env xs = Some cs -> length xs = length cs.
Proof.
  intro Hread; apply read_args_sound in Hread; apply Forall2_length in Hread; exact Hread.
Qed.

(** Terminal availability covers the operands of every selected outgoing occurrence. *)
Lemma ssa_term_operands_bound ext P fr t :
  wf_program ext P -> frame_available P fr -> at_term P fr t ->
  env_bound (fenv fr) (term_uses t).
Proof.
  intros Hwf Havailable [fd [b [Hf [Hb [Hpc Hterm]]]]].
  destruct (wf_function ext P _ _ Hwf Hf) as [_ [_ [_ [R Hcert]]]].
  pose proof (proj1 (proj2 (certificate_block fd R _ _ Hcert Hb))) as Huses.
  intros x Hx; apply (Havailable fd b R Hf Hb Hcert x).
  unfold available_at, prefix_defs; rewrite Hpc, firstn_all.
  rewrite <- Hterm in Hx; exact (proj1 (Forall_forall _ _) Huses x Hx).
Qed.

Lemma ssa_edge_argument_use t dst args x :
  In (dst, args) (term_edges t) -> In x args -> In x (term_uses t).
Proof.
  intros Hedge Hx; destruct t as [l actual|c l1 a1 l2 a2|c cases d da|c actual k|y];
    cbn [term_edges term_uses] in Hedge |- *.
  - destruct Hedge as [Heq|Hfalse]; [injection Heq as <- <-; exact Hx|contradiction].
  - right; destruct Hedge as [Heq|[Heq|Hfalse]];
      [injection Heq as <- <-; apply in_or_app; left; exact Hx|
       injection Heq as <- <-; apply in_or_app; right; exact Hx|contradiction].
  - right; apply in_app_iff in Hedge; apply in_or_app.
    destruct Hedge as [Hcase|Hdefault].
    + left; apply in_map_iff in Hcase; destruct Hcase as [[[key l] actual] [Heq Hin]].
      cbn in Heq; injection Heq as Hdst Hargs; apply in_flat_map.
      exists (key, l, actual); split; [exact Hin|cbn; rewrite Hargs; exact Hx].
    + destruct Hdefault as [Heq|Hfalse]; [injection Heq as <- <-; right; exact Hx|
        contradiction].
  - destruct Hedge as [Heq|Hfalse]; [injection Heq as <- <-; contradiction|contradiction].
  - contradiction.
Qed.

(** * Boolean demand agreement *)

Lemma ssa_bool_demand_member {X} (EX : encoding X) U (d : finite_map EX U bool) x :
  dget EX bool_lattice d x = true -> In x U.
Proof.
  unfold dget, pointwise_lookup; destruct (Map.get EX x (proj1_sig d)) as [value|]
    eqn:Hget; [|discriminate].
  intro Htrue; apply (proj2 (proj2_sig d)); rewrite Hget; discriminate.
Qed.

Lemma ssa_bool_demand_agreement {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) :
  agreement_laws (demand_lattice EX bool_demand dv) (demand_agreement EX bool_demand dv) /\
  agreement_symmetric (demand_agreement EX bool_demand dv).
Proof.
  split.
  - constructor.
    + intros d s x Hneeded; reflexivity.
    + intros a b s t Hab Hagree x Hneeded; apply Hagree.
      exact (proj1 (demand_bool_leb_iff EX _ a b) Hab x Hneeded).
  - intros d s t Hagree x Hneeded; symmetry; apply Hagree; exact Hneeded.
Qed.

Lemma ssa_bool_forced_agrees {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) e d s t x :
  demand_vars_ok dv ->
  agree (demand_agreement EX bool_demand dv) (demand_transfer EX bool_demand dv e d) s t ->
  In (x, true) (dnec dv e) -> dlookup dv s x = dlookup dv t x.
Proof.
  intros [_ [Hinputs _]] Hagree Hforced; apply Hagree.
  apply demand_bool_transfer_true; split.
  - apply (Hinputs e x false x true); apply in_or_app; left; exact Hforced.
  - right; left; exact Hforced.
Qed.

Lemma ssa_bool_backward_agrees {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) e d s t x y :
  demand_vars_ok dv ->
  agree (demand_agreement EX bool_demand dv) (demand_transfer EX bool_demand dv e d) s t ->
  In x (ddefs dv e) -> dget EX bool_lattice d x = true ->
  In (y, true) (dback dv e x true) -> dlookup dv s y = dlookup dv t y.
Proof.
  intros [_ [Hinputs _]] Hagree Hdef Hneeded Hback; apply Hagree.
  apply demand_bool_transfer_true; split.
  - apply (Hinputs e x true y true); apply in_or_app; right; exact Hback.
  - right; right; exists x; split; [exact Hdef|rewrite Hneeded; exact Hback].
Qed.

Lemma ssa_bool_frame_agrees {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) e d s t x :
  agree (demand_agreement EX bool_demand dv) (demand_transfer EX bool_demand dv e d) s t ->
  ~ In x (ddefs dv e) -> dget EX bool_lattice d x = true ->
  dlookup dv s x = dlookup dv t x.
Proof.
  intros Hagree Houtside Hneeded; apply Hagree; apply demand_bool_transfer_true; split.
  - exact (ssa_bool_demand_member EX _ d x Hneeded).
  - left; split; [|exact Hneeded].
    destruct (FinSet.mem EX x (FinSet.of_list EX (ddefs dv e))) eqn:Hmem;
      [|reflexivity].
    apply FinSet.of_list_spec in Hmem; contradiction.
Qed.

Lemma ssa_bool_exit_agrees {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) n s t x :
  demand_vars_ok dv ->
  agree (demand_agreement EX bool_demand dv)
    (finite_map_clamp EX (dvars dv) (exit_map EX bool_lattice (dexit dv n))) s t ->
  In (x, true) (dexit dv n) -> dlookup dv s x = dlookup dv t x.
Proof.
  intros [_ [_ [Hexits _]]] Hagree Hexit; apply Hagree.
  unfold dget, pointwise_lookup; rewrite finite_map_clamp_get by (eapply Hexits; exact Hexit).
  apply demand_bool_exit_true; exact Hexit.
Qed.

Lemma ssa_effectful_false_trap {I} (ef : effects I) i :
  effectful ef KeepTraps i = false -> may_trap ef i = false.
Proof.
  unfold effectful; rewrite !orb_false_iff, andb_true_r; tauto.
Qed.

(** Instruction lookup is strictly before the same block's terminator. *)
Lemma ssa_at_instr_before P fr i fd b :
  at_instr P fr i -> find_func P (ffunc fr) = Some fd ->
  find_block fd (flabel fr) = Some b -> fpc fr < length (bbody b).
Proof.
  intros [fd' [b' [Hf' [Hb' Hnth]]]] Hf Hb.
  rewrite Hf in Hf'; injection Hf' as <-; rewrite Hb in Hb'; injection Hb' as <-.
  apply nth_error_Some; rewrite Hnth; discriminate.
Qed.

(** Terminator lookup fixes the instruction position to the body's length. *)
Lemma ssa_at_term_end P fr t fd b :
  at_term P fr t -> find_func P (ffunc fr) = Some fd ->
  find_block fd (flabel fr) = Some b -> fpc fr = length (bbody b).
Proof.
  intros [fd' [b' [Hf' [Hb' [Hpc Hterm]]]]] Hf Hb.
  rewrite Hf in Hf'; injection Hf' as <-; rewrite Hb in Hb'; injection Hb' as <-.
  exact Hpc.
Qed.

(** One frame selects at most one source instruction or terminator. *)
Lemma ssa_at_instr_unique P fr i j :
  at_instr P fr i -> at_instr P fr j -> i = j.
Proof.
  intros [fd [b [Hf [Hb Hi]]]] [fd' [b' [Hf' [Hb' Hj]]]].
  rewrite Hf in Hf'; injection Hf' as <-; rewrite Hb in Hb'; injection Hb' as <-.
  rewrite Hi in Hj; injection Hj as Heq; exact Heq.
Qed.

Lemma ssa_at_term_unique P fr t u :
  at_term P fr t -> at_term P fr u -> t = u.
Proof.
  intros [fd [b [Hf [Hb [_ Ht]]]]] [fd' [b' [Hf' [Hb' [_ Hu]]]]].
  rewrite Hf in Hf'; injection Hf' as <-; rewrite Hb in Hb'; injection Hb' as <-.
  congruence.
Qed.

Lemma ssa_at_instr_not_term P fr i t : at_instr P fr i -> ~ at_term P fr t.
Proof.
  intros Hi [fd [b [Hf [Hb [Hpc Hterm]]]]].
  pose proof (ssa_at_instr_before P fr i fd b Hi Hf Hb); lia.
Qed.

(** Source-frame finality depends only on the selected block and instruction position. *)
Definition ssa_frame_final (P : program) (fr : sframe) : Prop :=
  exists fd b, find_func P (ffunc fr) = Some fd /\ find_block fd (flabel fr) = Some b /\
    length (bbody b) < fpc fr.

(** A source-frame operation trap records the already-read operands of its failing evaluator. *)
Definition ssa_frame_trapped (ext : nat -> list cval -> option cval)
    (P : program) (fr : sframe) : Prop :=
  exists x o args cs, at_instr P fr (IOp x o args) /\
    read_args (fenv fr) args = Some cs /\ op_eval ext o cs = None.

Lemma ssa_frame_final_at P fr fd b :
  find_func P (ffunc fr) = Some fd -> find_block fd (flabel fr) = Some b ->
  (ssa_frame_final P fr <-> length (bbody b) < fpc fr).
Proof.
  intros Hf Hb; split.
  - intros [fd' [b' [Hf' [Hb' Hpast]]]].
    rewrite Hf in Hf'; injection Hf' as <-; rewrite Hb in Hb'; injection Hb' as <-.
    exact Hpast.
  - intro Hpast; exists fd, b; repeat split; assumption.
Qed.

Lemma ssa_at_instr_coordinates P fr fr' i :
  ffunc fr = ffunc fr' -> flabel fr = flabel fr' -> fpc fr = fpc fr' ->
  (at_instr P fr i <-> at_instr P fr' i).
Proof.
  intros Hfunction Hlabel Hpc; unfold at_instr; rewrite Hfunction, Hlabel, Hpc; reflexivity.
Qed.

Lemma ssa_at_term_coordinates P fr fr' t :
  ffunc fr = ffunc fr' -> flabel fr = flabel fr' -> fpc fr = fpc fr' ->
  (at_term P fr t <-> at_term P fr' t).
Proof.
  intros Hfunction Hlabel Hpc; unfold at_term; rewrite Hfunction, Hlabel, Hpc; reflexivity.
Qed.

Lemma ssa_frame_trapped_agrees ext P fr fr' :
  ffunc fr = ffunc fr' -> flabel fr = flabel fr' -> fpc fr = fpc fr' ->
  ssa_env_agrees (fenv fr) (fenv fr') ->
  (ssa_frame_trapped ext P fr <-> ssa_frame_trapped ext P fr').
Proof.
  intros Hfunction Hlabel Hpc Henv; split;
    intros [x [o [args [cs [Hat [Hread Hfail]]]]]]; exists x, o, args, cs; split.
  - apply (proj1 (ssa_at_instr_coordinates P fr fr' _ Hfunction Hlabel Hpc)); exact Hat.
  - split; [rewrite <- (ssa_read_agrees _ _ args Henv); exact Hread|exact Hfail].
  - apply (proj2 (ssa_at_instr_coordinates P fr fr' _ Hfunction Hlabel Hpc)); exact Hat.
  - split; [rewrite (ssa_read_agrees _ _ args Henv); exact Hread|exact Hfail].
Qed.

Lemma ssa_frame_trapped_before ext P fr fd b :
  ssa_frame_trapped ext P fr -> find_func P (ffunc fr) = Some fd ->
  find_block fd (flabel fr) = Some b -> fpc fr < length (bbody b).
Proof.
  intros [x [o [args [cs [Hat Hother]]]]] Hf Hb; eapply ssa_at_instr_before; eassumption.
Qed.

(** * Bounded administrative completion *)

Inductive ssa_admin_steps {T O} (m : semantics T O) (stable : T -> Prop)
    : T -> nat -> T -> Prop :=
  | SsaAdminRefl : forall r, ssa_admin_steps m stable r 0 r
  | SsaAdminStep : forall r u n t,
      ~ stable r -> step m r [] u -> ssa_admin_steps m stable u n t ->
      ssa_admin_steps m stable r (S n) t.

Arguments SsaAdminRefl {T O m stable}.
Arguments SsaAdminStep {T O m stable}.

Lemma ssa_admin_exec {T O} (m : semantics T O) stable r n t :
  ssa_admin_steps m stable r n t -> exec m r [] t.
Proof.
  intro Hsteps; induction Hsteps as [r|r u n t Hunstable Hstep Htail IH].
  - constructor.
  - eapply exec_step with (l := []) (tr := []); eassumption.
Qed.

Lemma ssa_admin_stable {T O} (m : semantics T O) stable r n t :
  stable r -> ssa_admin_steps m stable r n t -> n = 0 /\ t = r.
Proof.
  intros Hstable Hsteps; destruct Hsteps as [r|r u n t Hunstable Hstep Htail].
  - split; reflexivity.
  - contradiction.
Qed.

Module SsaCompletion.

(** Completion laws pair every visible head with the same silent administrative endpoint. *)
Record laws {S T O} (m1 : semantics S O) (e1 : endings S)
    (m2 : semantics T O) (e2 : endings T) (stable : T -> Prop) (rank : T -> nat)
    (R : S -> T -> Prop) : Prop := Laws {
  relation_stable : forall s t, R s t -> stable t;
  declared_ends : forall s t k, R s t -> k <> EndStuck ->
    (ends_as m1 e1 k s <-> ends_as m2 e2 k t);
  administrative_step : forall t tr t', ~ stable t -> step m2 t tr t' ->
    tr = [] /\ rank t' < rank t;
  administrative_deterministic : forall t u v, ~ stable t ->
    step m2 t [] u -> step m2 t [] v -> u = v;
  no_intermediate_ends : forall t k, ~ stable t -> k <> EndStuck -> ~ ends_as m2 e2 k t;
  forth : forall s t tr s', R s t -> step m1 s tr s' ->
    exists u n v, step m2 t tr u /\ ssa_admin_steps m2 stable u n v /\ stable v /\ R s' v;
  back : forall s t tr u, R s t -> step m2 t tr u ->
    exists s' n v, step m1 s tr s' /\ ssa_admin_steps m2 stable u n v /\ stable v /\ R s' v
}.

Arguments relation_stable {S T O m1 e1 m2 e2 stable rank R}.
Arguments declared_ends {S T O m1 e1 m2 e2 stable rank R}.
Arguments administrative_step {S T O m1 e1 m2 e2 stable rank R}.
Arguments administrative_deterministic {S T O m1 e1 m2 e2 stable rank R}.
Arguments no_intermediate_ends {S T O m1 e1 m2 e2 stable rank R}.
Arguments forth {S T O m1 e1 m2 e2 stable rank R}.
Arguments back {S T O m1 e1 m2 e2 stable rank R}.

Definition closure {S T O} (m : semantics T O) stable (R : S -> T -> Prop) s t : Prop :=
  exists n u, ssa_admin_steps m stable t n u /\ stable u /\ R s u.

Section Completion.

Context {S T O : Type} (m1 : semantics S O) (e1 : endings S)
  (m2 : semantics T O) (e2 : endings T) (stable : T -> Prop) (rank : T -> nat)
  (R : S -> T -> Prop) (H : laws m1 e1 m2 e2 stable rank R).

Local Lemma running_agrees s t : R s t -> (running m1 s <-> running m2 t).
Proof.
  intro HR; split; intros [tr [u Hstep]].
  - destruct (forth H s t tr u HR Hstep) as [v [n [w [Hhead Htail]]]].
    exists tr, v; exact Hhead.
  - destruct (back H s t tr u HR Hstep) as [v [n [w [Hhead Htail]]]].
    exists tr, v; exact Hhead.
Qed.

Local Lemma endings_agree s t k : R s t -> (ends_as m1 e1 k s <-> ends_as m2 e2 k t).
Proof.
  intro HR; destruct k.
  - exact (declared_ends H s t EndFinal HR ltac:(discriminate)).
  - exact (declared_ends H s t EndTrap HR ltac:(discriminate)).
  - exact (declared_ends H s t EndStop HR ltac:(discriminate)).
  - pose proof (running_agrees s t HR) as Hrunning.
    pose proof (declared_ends H s t EndFinal HR ltac:(discriminate)) as Hfinal.
    pose proof (declared_ends H s t EndTrap HR ltac:(discriminate)) as Htrap.
    pose proof (declared_ends H s t EndStop HR ltac:(discriminate)) as Hstop.
    change ((~ running m1 s /\ ~ final e1 s /\ ~ trapped e1 s /\ ~ stopped e1 s) <->
      (~ running m2 t /\ ~ final e2 t /\ ~ trapped e2 t /\ ~ stopped e2 t)).
    cbn [ends_as] in Hfinal, Htrap, Hstop; tauto.
Qed.

Local Lemma administrative_not_ending t u :
  ~ stable t -> step m2 t [] u -> forall k, ~ ends_as m2 e2 k t.
Proof.
  intros Hunstable Hstep k Hend; destruct k.
  - exact (no_intermediate_ends H t EndFinal Hunstable ltac:(discriminate) Hend).
  - exact (no_intermediate_ends H t EndTrap Hunstable ltac:(discriminate) Hend).
  - exact (no_intermediate_ends H t EndStop Hunstable ltac:(discriminate) Hend).
  - destruct Hend as [Hnot_running Hother]; apply Hnot_running; exists [], u; exact Hstep.
Qed.

Local Lemma closure_ending_relation s t k :
  closure m2 stable R s t -> ends_as m2 e2 k t -> R s t.
Proof.
  intros [n [u [Hsteps [Hstable HR]]]] Hend.
  destruct Hsteps as [t|t v n u Hunstable Hstep Htail].
  - exact HR.
  - exfalso; exact (administrative_not_ending t v Hunstable Hstep k Hend).
Qed.

Lemma stutters :
  stuttering m1 e1 m2 e2 (closure m2 stable R) (fun _ _ => 0) (fun _ t => rank t).
Proof.
  constructor.
  - intros s t k [n [u [Hsteps [Hstable HR]]]] Hend; exists u; split.
    + exact (ssa_admin_exec m2 stable t n u Hsteps).
    + exact (proj1 (endings_agree s u k HR) Hend).
  - intros s t k HE Hend; exists s; split; [constructor|].
    exact (proj2 (endings_agree s t k (closure_ending_relation s t k HE Hend)) Hend).
  - intros s t tr s' [n [u [Hsteps [Hstable HR]]]] Hstep.
    destruct (forth H s u tr s' HR Hstep) as [v [n' [w [Hhead [Htail [Hw HR']]]]]].
    right; exists u, v; split; [exact (ssa_admin_exec m2 stable t n u Hsteps)|].
    split; [exact Hhead|]; exists n', w; repeat split; assumption.
  - intros s t tr t' [n [u [Hsteps [Hstable HR]]]] Hstep.
    destruct Hsteps as [t|t v n u Hunstable Hfirst Htail].
    + destruct (back H s t tr t' HR Hstep) as [s' [n' [w [Hhead [Htail [Hw HR']]]]]].
      right; exists s, s'; split; [constructor|]; split; [exact Hhead|].
      exists n', w; repeat split; assumption.
    + destruct (administrative_step H t tr t' Hunstable Hstep) as [-> Hrank].
      assert (Heq : v = t') by
        (eapply administrative_deterministic; [exact H|exact Hunstable|exact Hfirst|
          exact Hstep]).
      subst v; left; split; [reflexivity|]; split; [|exact Hrank].
      exists n, u; repeat split; assumption.
Qed.

(** Bounded silent completion preserves all ending tags, finite prefixes and diverging prefixes. *)
Theorem behaviour s t : R s t -> same_behaviour m1 e1 s m2 e2 t.
Proof.
  intro HR; eapply stuttering_same_behaviour; [exact stutters|].
  exists 0, t; split; [constructor|]; split; [exact (relation_stable H s t HR)|exact HR].
Qed.

End Completion.

End SsaCompletion.
Import SsaCompletion.
