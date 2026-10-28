(** * Injective key encodings

    Encodings map keys to positive numbers with a proof of injectivity.
    For example, a list is represented by a stream of delimited element codes.
    Builds on: Rocq Stdlib binary numbers and lists. *)

From Stdlib Require Import Bool List NArith ZArith.
Import List.ListNotations.

(** * Encoding dictionaries *)

(** An encoding assigns each key a distinct positive code. *)
Record encoding (K : Type) : Type := Encoding {
  encode : K -> positive;
  encode_injective : forall x y, encode x = encode y -> x = y
}.
Arguments encode {K}.
Arguments encode_injective {K}.

(** Positive numbers encode as themselves. *)
Definition positive_encoding : encoding positive.
Proof.
  refine (Encoding positive (fun p => p) _). intros x y H; exact H.
Defined.

(** Binary natural numbers encode as their successor. *)
Definition N_encoding : encoding N.
Proof.
  refine (Encoding N N.succ_pos _).
  intros [|x] [|y] H; simpl in H; try reflexivity.
  - destruct y; discriminate.
  - destruct x; discriminate.
  - f_equal. now apply Pos.succ_inj.
Defined.

(** Unary natural numbers encode as their positive successor. *)
Definition nat_encoding : encoding nat.
Proof.
  refine (Encoding nat Pos.of_succ_nat _).
  intros x y H.
  apply (f_equal Pos.to_nat) in H.
  rewrite !SuccNat2Pos.id_succ in H. now inversion H.
Defined.

(** Signed numbers use the low bit to distinguish signs. *)
Definition Z_encoding : encoding Z.
Proof.
  refine (Encoding Z (fun z => match z with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end) _).
  intros [|x|x] [|y|y] H; simpl in H; try discriminate; try reflexivity;
    inversion H; reflexivity.
Defined.

(** Booleans have the codes one and two. *)
Definition bool_encoding : encoding bool.
Proof.
  refine (Encoding bool (fun b => if b then 2%positive else 1%positive) _).
  intros [] [] H; simpl in H; try discriminate; reflexivity.
Defined.

(** The unique unit value has code one. *)
Definition unit_encoding : encoding unit.
Proof.
  refine (Encoding unit (fun _ => 1%positive) _).
  intros [] [] _. reflexivity.
Defined.

(** Options reserve one for absence and append a zero for presence. *)
Definition option_encoding {A} (EA : encoding A) : encoding (option A).
Proof.
  refine (Encoding (option A) (fun o => match o with
    | None => xH
    | Some a => xO (encode EA a)
    end) _).
  intros [x|] [y|] H; simpl in H; try discriminate; try reflexivity.
  inversion H. f_equal. now apply (encode_injective EA).
Defined.

(** Sum codes append a tag distinguishing the two alternatives. *)
Definition sum_encoding {A B} (EA : encoding A) (EB : encoding B) : encoding (A + B).
Proof.
  refine (Encoding (A + B) (fun s => match s with
    | inl a => xO (encode EA a)
    | inr b => xI (encode EB b)
    end) _).
  intros [x|x] [y|y] H; simpl in H; try discriminate;
    inversion H; f_equal; eauto using encode_injective.
Defined.

(** * Delimited streams *)

(* The least significant bit is emitted first. The suffix is threaded through each
   traversal, avoiding repeated concatenation. *)
Fixpoint emit_code (p : positive) (tail : list bool) : list bool :=
  match p with
  | xH => false :: true :: tail
  | xO q => false :: false :: emit_code q tail
  | xI q => true :: true :: emit_code q tail
  end.

Fixpoint read_code (bits : list bool) : option (positive * list bool) :=
  match bits with
  | false :: true :: tail => Some (xH, tail)
  | false :: false :: tail =>
      match read_code tail with
      | Some (p, rest) => Some (xO p, rest)
      | None => None
      end
  | true :: true :: tail =>
      match read_code tail with
      | Some (p, rest) => Some (xI p, rest)
      | None => None
      end
  | _ => None
  end.

Lemma read_emit_code : forall p tail, read_code (emit_code p tail) = Some (p, tail).
Proof.
  induction p; intros tail; simpl; now rewrite ?IHp.
Qed.

Fixpoint stream_positive (bits : list bool) : positive :=
  match bits with
  | [] => xH
  | false :: rest => xO (stream_positive rest)
  | true :: rest => xI (stream_positive rest)
  end.

Fixpoint positive_stream (p : positive) : list bool :=
  match p with
  | xH => []
  | xO q => false :: positive_stream q
  | xI q => true :: positive_stream q
  end.

Lemma positive_stream_roundtrip : forall bits, positive_stream (stream_positive bits) = bits.
Proof.
  induction bits as [|[] rest IH]; simpl; now rewrite ?IH.
Qed.

Lemma stream_positive_injective : forall xs ys,
  stream_positive xs = stream_positive ys -> xs = ys.
Proof.
  intros xs ys H. apply (f_equal positive_stream) in H.
  now rewrite !positive_stream_roundtrip in H.
Qed.

Fixpoint emit_list {A} (E : encoding A) (xs : list A) : list bool :=
  match xs with
  | [] => []
  | x :: rest => emit_code (encode E x) (emit_list E rest)
  end.

Lemma emit_list_injective : forall A (E : encoding A) xs ys,
  emit_list E xs = emit_list E ys -> xs = ys.
Proof.
  intros A E xs. induction xs as [|x xs IH]; intros [|y ys] H; simpl in H.
  - reflexivity.
  - destruct (encode E y); discriminate.
  - destruct (encode E x); discriminate.
  - apply (f_equal read_code) in H. rewrite !read_emit_code in H.
    inversion H as [[Hcode Hrest]].
    f_equal; [now apply (encode_injective E)|now apply IH].
Qed.

(** A pair concatenates two self-delimiting element codes. *)
Definition pair_encoding {A B} (EA : encoding A) (EB : encoding B) : encoding (A * B).
Proof.
  refine (Encoding (A * B) (fun xy =>
    stream_positive (emit_code (encode EA (fst xy)) (emit_code (encode EB (snd xy)) []))) _).
  intros [a b] [a' b'] H. simpl in H.
  apply stream_positive_injective in H.
  apply (f_equal read_code) in H. rewrite !read_emit_code in H.
  injection H as Ha Htail.
  apply (f_equal read_code) in Htail. rewrite !read_emit_code in Htail.
  injection Htail as Hb.
  f_equal; [now apply (encode_injective EA)|now apply (encode_injective EB)].
Defined.

(** A list concatenates the self-delimiting codes of its elements. *)
Definition list_encoding {A} (EA : encoding A) : encoding (list A).
Proof.
  refine (Encoding (list A) (fun xs => stream_positive (emit_list EA xs)) _).
  intros xs ys H. apply emit_list_injective with (E := EA).
  now apply stream_positive_injective.
Defined.
