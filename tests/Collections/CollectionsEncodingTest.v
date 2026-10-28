(** * Encoding examples

    These examples exercise primitive and composed key codes.
    For example, lists with a shared prefix receive distinct codes.
    Builds on: CollectionsEncoding. *)

From Stdlib Require Import Bool List NArith ZArith.
From Gaulois.Collections Require Import CollectionsEncoding.
Import List.ListNotations.

(** The primitive encodings use their prescribed boundary codes. *)
Example primitive_codes :
  encode positive_encoding 5%positive = 5%positive /\
  encode N_encoding 0%N = 1%positive /\
  encode N_encoding 2%N = 3%positive /\
  encode nat_encoding 0 = 1%positive /\
  encode nat_encoding 4 = 5%positive /\
  encode Z_encoding 0%Z = 1%positive /\
  encode Z_encoding 2%Z = 4%positive /\
  encode Z_encoding (-2)%Z = 5%positive /\
  encode bool_encoding false = 1%positive /\
  encode bool_encoding true = 2%positive /\
  encode unit_encoding tt = 1%positive.
Proof.
  vm_compute. repeat split.
Qed.

(** Option and sum tags distinguish both alternatives. *)
Example tagged_codes :
  encode (option_encoding positive_encoding) None = 1%positive /\
  encode (option_encoding positive_encoding) (Some 3%positive) = 6%positive /\
  encode (sum_encoding positive_encoding positive_encoding) (inl 3%positive) = 6%positive /\
  encode (sum_encoding positive_encoding positive_encoding) (inr 3%positive) = 7%positive.
Proof.
  vm_compute. repeat split.
Qed.

(** Empty and nested lists retain their structure in their codes. *)
Example nested_lists :
  encode (list_encoding positive_encoding) [] = 1%positive /\
  Pos.eqb (encode (list_encoding (list_encoding bool_encoding)) [[]; [true]])
    (encode (list_encoding (list_encoding bool_encoding)) [[true]; []]) = false /\
  Pos.eqb (encode (list_encoding positive_encoding) [1%positive; 2%positive])
    (encode (list_encoding positive_encoding) [1%positive; 2%positive; 1%positive]) = false.
Proof.
  vm_compute. repeat split.
Qed.

(** Pairs with equal first codes and different second codes remain distinct. *)
Example pair_shared_prefix :
  Pos.eqb (encode (pair_encoding positive_encoding positive_encoding) (3%positive, 1%positive))
    (encode (pair_encoding positive_encoding positive_encoding) (3%positive, 2%positive)) = false.
Proof.
  vm_compute. reflexivity.
Qed.
