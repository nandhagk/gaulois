(** * Word and expression examples

    These computations exercise boundary arithmetic, operator validation and expression bridges.
    For example, dividing a positive word by zero returns the all-ones word.
    Builds on: BitsWord, BitsFun, BitsOp, BitsExpr, BitsBridge and BitsTestbit. *)

From Stdlib Require Import ZArith List Bool.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsExpr BitsBridge BitsTestbit.
Import List.ListNotations.
Import Bits.

Open Scope Z_scope.

(** Width one distinguishes sign, complement and the counts of zero. *)
Example width_one :
  wnot 1%positive 1 = 0 /\ wneg 1%positive 1 = 1 /\
  signed 1%positive 1 = -1 /\
  wclz 1%positive 0 = 1 /\ wctz 1%positive 1 = 0 /\ wpopcnt 1%positive 1 = 1.
Proof.
  vm_compute. repeat split.
Qed.

(** Arithmetic wraps at the modulus, including the minimum signed value. *)
Example arithmetic_overflow :
  eval_op bvadd [(8%positive, 200); (8%positive, 100)] = Some (8%positive, 44) /\
  eval_op bvmul [(8%positive, 20); (8%positive, 20)] = Some (8%positive, 144) /\
  eval_op bvsub [(8%positive, 0); (8%positive, 1)] = Some (8%positive, 255) /\
  eval_op bvneg [(8%positive, 128)] = Some (8%positive, 128).
Proof.
  vm_compute. repeat split.
Qed.

(** Unsigned and signed division have their specified zero-divisor results. *)
Example zero_divisor :
  eval_op bvudiv [(8%positive, 7); (8%positive, 0)] = Some (8%positive, 255) /\
  eval_op bvurem [(8%positive, 7); (8%positive, 0)] = Some (8%positive, 7) /\
  eval_op bvsdiv [(8%positive, 249); (8%positive, 0)] = Some (8%positive, 1) /\
  eval_op bvsrem [(8%positive, 249); (8%positive, 0)] = Some (8%positive, 249) /\
  eval_op bvsmod [(8%positive, 249); (8%positive, 0)] = Some (8%positive, 249).
Proof.
  vm_compute. repeat split.
Qed.

(** Signed remainder and modulus discriminate all sign combinations. *)
Example signed_division :
  wsdiv 8%positive 128 255 = 128 /\
  wsdiv 8%positive 249 3 = 254 /\ wsdiv 8%positive 7 253 = 254 /\
  wsdiv 8%positive 249 253 = 2 /\
  wsrem 8%positive 249 3 = 255 /\ wsrem 8%positive 7 253 = 1 /\
  wsrem 8%positive 249 253 = 255 /\
  wsmod 8%positive 249 3 = 2 /\ wsmod 8%positive 7 253 = 254 /\
  wsmod 8%positive 249 253 = 255.
Proof.
  vm_compute. repeat split.
Qed.

(** Large shifts clear logical results and fill arithmetic results with the sign. *)
Example large_shifts :
  wshl 8%positive 129 8 = 0 /\ wlshr 8%positive 129 8 = 0 /\
  washr 8%positive 129 8 = 255 /\ washr 8%positive 127 255 = 0 /\
  washr 8%positive 129 1 = 192 /\ wshl 8%positive 129 256 = 129.
Proof.
  vm_compute. repeat split.
Qed.

(** Rotations keep overflow bits and reduce their amount modulo the width. *)
Example rotations :
  wrotl 8%positive 129 1 = 3 /\ wrotr 8%positive 129 1 = 192 /\
  wrotl 3%positive 5 4 = 3 /\ wrotr 3%positive 5 4 = 6.
Proof.
  vm_compute. repeat split.
Qed.

(** Counts distinguish leading, trailing and total set bits, and define zero. *)
Example counts :
  map (fun o => eval_op o [(8%positive, 40)]) [bvclz; bvctz; bvpopcnt] =
    [Some (8%positive, 2); Some (8%positive, 3); Some (8%positive, 2)] /\
  map (fun o => eval_op o [(8%positive, 0)]) [bvclz; bvctz; bvpopcnt] =
    [Some (8%positive, 8); Some (8%positive, 8); Some (8%positive, 0)].
Proof.
  vm_compute. repeat split.
Qed.

(** The bitwise truth tables act on each bit of normalized words. *)
Example bitwise_operators :
  wand 8%positive 170 204 = 136 /\ wor 8%positive 170 204 = 238 /\
  wxor 8%positive 170 204 = 102 /\ wnot 8%positive 170 = 85 /\
  Z.testbit (washr 8%positive 129 2) 7 = true /\
  Z.testbit (wshl 8%positive 129 2) 8 = false.
Proof.
  vm_compute. repeat split.
Qed.

(** Comparisons distinguish signed from unsigned order and normalize equality inputs. *)
Example comparisons :
  eval_op bvult [(8%positive, 255); (8%positive, 1)] = Some (1%positive, 0) /\
  eval_op bvslt [(8%positive, 255); (8%positive, 1)] = Some (1%positive, 1) /\
  eval_op bveq [(8%positive, -1); (8%positive, 255)] = Some (1%positive, 1) /\
  eval_op bvne [(8%positive, 0); (8%positive, 255)] = Some (1%positive, 1) /\
  eval_op bvule [(8%positive, 5); (8%positive, 5)] = Some (1%positive, 1) /\
  eval_op bvsle [(8%positive, 128); (8%positive, 127)] = Some (1%positive, 1).
Proof.
  vm_compute. repeat split.
Qed.

(** Width-changing operators preserve their intended high and low parts. *)
Example width_changes :
  eval_op (bvzext 8%positive) [(8%positive, 255)] = Some (16%positive, 255) /\
  eval_op (bvsext 8%positive) [(8%positive, 255)] = Some (16%positive, 65535) /\
  eval_op (bvtrunc 4%positive) [(8%positive, 165)] = Some (4%positive, 5) /\
  eval_op (bvextract 7 4) [(8%positive, 165)] = Some (4%positive, 10) /\
  eval_op bvconcat [(4%positive, 10); (4%positive, 5)] = Some (8%positive, 165).
Proof.
  vm_compute. repeat split.
Qed.

(** Width checking rejects bad arities, mismatches and invalid extraction bounds. *)
Example invalid_operands :
  eval_op bvnot [] = None /\ eval_op bvnot [(8%positive, 0); (8%positive, 0)] = None /\
  eval_op bvadd [(8%positive, 0); (4%positive, 0)] = None /\
  eval_op bvite [(2%positive, 1); (8%positive, 1); (8%positive, 2)] = None /\
  eval_op bvite [(1%positive, 1); (8%positive, 1); (4%positive, 2)] = None /\
  eval_op (bvtrunc 9%positive) [(8%positive, 1)] = None /\
  eval_op (bvextract 2 3) [(8%positive, 1)] = None /\
  eval_op (bvextract 8 0) [(8%positive, 1)] = None.
Proof.
  vm_compute. repeat split.
Qed.

(** Nested applications normalize environment entries and select with a wrapped condition. *)
Example expression_evaluation :
  eval (env_of [(8%positive, 200); (8%positive, 100)])
    (App bvite [Const 1%positive 3;
      App bvadd [Var 0; Var 1]; Const 8%positive 17]) = Some (8%positive, 44) /\
  eval (env_of []) (Var 9) = Some (1%positive, 0) /\
  eval_args (env_of []) [Const 8%positive 260; App bvadd []] = None.
Proof.
  vm_compute. repeat split.
Qed.

(** The variable-list expression used by the bridge evaluates the original argument order. *)
Example bridge_application :
  eval (env_of [(8%positive, 200); (8%positive, 100)])
    (App bvadd (vars (arity bvadd))) = Some (8%positive, 44) /\
  eval (env_of [(8%positive, 3); (8%positive, 7)])
    (App bvsub (vars (arity bvsub))) = Some (8%positive, 252).
Proof.
  vm_compute. repeat split.
Qed.

(** Parameterized operator codes retain both extraction bounds and constructor tags. *)
Example operator_codes :
  Pos.eqb (encode op_encoding (bvextract 7 0))
    (encode op_encoding (bvextract 7 1)) = false /\
  Pos.eqb (encode op_encoding (bvzext 4%positive))
    (encode op_encoding (bvsext 4%positive)) = false.
Proof.
  vm_compute. repeat split.
Qed.
