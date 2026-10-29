(** * Typed block-parameter SSA syntax

    Functions contain labelled blocks whose parameters are bound simultaneously.
    For example, [TJump l [b; a]] swaps two parameters without sequential reads.
    Builds on: Stdlib lists and integers, Collections encoded maps. *)

From Stdlib Require Import List ZArith Bool.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
Import List.ListNotations.

(** Function names are program-wide natural-number identifiers. *)
Definition func : Type := nat.

(** Labels identify blocks within one function. *)
Definition label : Type := nat.

(** Value identifiers have one definition in the entire program. *)
Definition vid : Type := nat.

(** Integer operations use either 32 or 64 bits. *)
Inductive iw : Type :=
  | W32
  | W64.

(** Memory accesses have one of four fixed byte widths. *)
Inductive msize : Type :=
  | M1
  | M2
  | M4
  | M8.

(** Static types distinguish integer widths, pointers, function names and floating payloads. *)
Inductive ty : Type :=
  | TyI32
  | TyI64
  | TyPtr
  | TyFun
  | TyF32
  | TyF64.

(** Concrete values retain their type and distinguish data pointers from function names. *)
Inductive cval : Type :=
  | VInt (w : iw) (z : Z)
  | VPtr (b : nat) (o : Z)
  | VFun (f : func)
  | VF32 (bits : Z)
  | VF64 (bits : Z).

(** A value's constructor determines its static type. *)
Definition ty_of (c : cval) : ty :=
  match c with
  | VInt W32 _ => TyI32
  | VInt W64 _ => TyI64
  | VPtr _ _ => TyPtr
  | VFun _ => TyFun
  | VF32 _ => TyF32
  | VF64 _ => TyF64
  end.

(** Integer payloads are canonical unsigned words; other payloads are opaque. *)
Definition valid_cval (c : cval) : Prop :=
  match c with
  | VInt W32 z => (0 <= z < 2 ^ 32)%Z
  | VInt W64 z => (0 <= z < 2 ^ 64)%Z
  | _ => True
  end.

(** Binary integer operators include trapping unsigned division and signed comparison. *)
Inductive bop : Type :=
  | BAdd
  | BSub
  | BMul
  | BDivU
  | BAnd
  | BOr
  | BXor
  | BShl
  | BShrU
  | BEq
  | BLtU
  | BLtS.

(** Pure operation syntax includes typed integers, conversions, pointer offsets and extensions. *)
Inductive sop : Type :=
  | OConst (c : cval)
  | OBin (w : iw) (o : bop)
  | OZext
  | OTrunc
  | OPtrAdd
  | OExt (tag : nat).

(** Instructions bind SSA results or perform explicit memory and output effects. *)
Inductive instr : Type :=
  | IOp (x : vid) (o : sop) (args : list vid)
  | IAlloc (x : vid) (n : vid)
  | IFree (p : vid)
  | ILoad (x : vid) (t : ty) (sz : msize) (p : vid)
  | IStore (sz : msize) (p v : vid)
  | IOutput (v : vid).

(** Indirect calls carry the signature that the runtime target must match. *)
Inductive callee : Type :=
  | CDirect (f : func)
  | CIndirect (v : vid) (ps : list ty) (r : ty).

(** Terminators transfer control using parallel argument binding or return one value. *)
Inductive terminator : Type :=
  | TJump (l : label) (args : list vid)
  | TBr (c : vid) (l1 : label) (a1 : list vid) (l2 : label) (a2 : list vid)
  | TSwitch (c : vid) (cases : list (Z * label * list vid)) (d : label) (da : list vid)
  | TCall (c : callee) (args : list vid) (k : label)
  | TRet (v : vid).

(** A block has typed parameters, an instruction sequence and one terminator. *)
Record ssa_block : Type := SBlock {
  bparams : list (vid * ty);
  bbody : list instr;
  bterm : terminator
}.

(** A function declares its entry, labelled blocks and result type. *)
Record fdef : Type := FDef {
  fentry : label;
  blocks : list (label * ssa_block);
  fresult : ty
}.

(** Programs identify main and declare the signatures of their extension operators. *)
Record program : Type := Program {
  funcs : list (func * fdef);
  main : func;
  ext_sigs : list (nat * (list ty * ty))
}.

(** Index construction retains the first binding, including on malformed input. *)
Fixpoint first_index {A : Type} (xs : list (nat * A)) : Map.t nat A :=
  match xs with
  | [] => Map.empty
  | (k, a) :: rest => Map.set nat_encoding k a (first_index rest)
  end.

(** Function lookup uses the program's name index. *)
Definition find_func (P : program) : func -> option fdef :=
  let index := first_index (funcs P) in
  fun f => Map.get nat_encoding f index.

(** Block lookup uses the function's label index. *)
Definition find_block (fd : fdef) : label -> option ssa_block :=
  let index := first_index (blocks fd) in
  fun l => Map.get nat_encoding l index.

Definition iw_bits (w : iw) : Z :=
  match w with
  | W32 => 32
  | W64 => 64
  end.

Definition iw_modulus (w : iw) : Z := (2 ^ iw_bits w)%Z.

Definition size_bytes (sz : msize) : nat :=
  match sz with
  | M1 => 1
  | M2 => 2
  | M4 => 4
  | M8 => 8
  end.

Definition ty_eq_dec (a b : ty) : {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.

Definition option_eq_dec {A : Type} (eq_dec : forall a b : A, {a = b} + {a <> b})
    (a b : option A) : {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.

Definition iw_eq_dec (a b : iw) : {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.

Definition cval_eq_dec (a b : cval) : {a = b} + {a <> b}.
Proof.
  decide equality; try apply Z.eq_dec; try apply Nat.eq_dec; apply iw_eq_dec.
Defined.
