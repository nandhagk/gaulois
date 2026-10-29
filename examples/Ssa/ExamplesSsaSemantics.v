(** * SSA operators, byte memory and frames

    The machine executes one instruction or terminator at a time and retains dead blocks.
    For example, freeing a block removes its readable bytes but retains its allocation site.
    Builds on: ExamplesSsaSyntax and ViewsSemantics. *)

From Stdlib Require Import List ZArith Bool Lia.
From Gaulois.Views Require Import ViewsSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax.
Import List.ListNotations.
Open Scope Z_scope.

(** A memory cell contains an integer byte or an indexed fragment of one value. *)
Inductive mval : Type :=
  | MInt (n : Z)
  | MFrag (p : cval) (i : nat).

(** Dead blocks retain their extent and historical allocation site. *)
Record mblock : Type := MBlock {
  msz : nat;
  mbytes : Z -> mval;
  mlive : bool;
  msite : vid
}.

(** Each activation has an independent environment and a return continuation label. *)
Record sframe : Type := SFrame {
  ffunc : func;
  flabel : label;
  fpc : nat;
  fenv : vid -> option cval;
  fret : label
}.

(** The stack is innermost first, and allocation identities increase without reuse. *)
Record state : Type := State {
  stack : list sframe;
  mem : nat -> option mblock;
  next_block : nat
}.

(** Output and the program's final result are distinct observable events. *)
Inductive event : Type :=
  | EvOut (v : cval)
  | EvRet (v : cval).

(** Limits bound simultaneous frames and the total number of allocated identities. *)
Record limits : Type := Limits {
  max_frames : nat;
  max_blocks : nat
}.

Definition word_ok (w : iw) (z : Z) : bool := (0 <=? z) && (z <? iw_modulus w).

Definition word_wrap (w : iw) (z : Z) : Z := z mod iw_modulus w.

Definition word_signed (w : iw) (z : Z) : Z :=
  if z <? iw_modulus w / 2 then z else z - iw_modulus w.

Definition bool_value (b : bool) : cval := VInt W32 (if b then 1 else 0).

Definition bin_eval (w : iw) (o : bop) (a b : Z) : option cval :=
  let integer z := Some (VInt w (word_wrap w z)) in
  match o with
  | BAdd => integer (a + b)
  | BSub => integer (a - b)
  | BMul => integer (a * b)
  | BDivU => if b =? 0 then None else integer (a / b)
  | BAnd => integer (Z.land a b)
  | BOr => integer (Z.lor a b)
  | BXor => integer (Z.lxor a b)
  | BShl => integer (Z.shiftl a (b mod iw_bits w))
  | BShrU => integer (Z.shiftr a (b mod iw_bits w))
  | BEq => Some (bool_value (a =? b))
  | BLtU => Some (bool_value (a <? b))
  | BLtS => Some (bool_value (word_signed w a <? word_signed w b))
  end.

Definition normalize_const (c : cval) : cval :=
  match c with
  | VInt w z => VInt w (word_wrap w z)
  | _ => c
  end.

(** Built-ins check operand shapes and integer validity before evaluating. *)
Definition op_eval (ext : nat -> list cval -> option cval)
    (o : sop) (cs : list cval) : option cval :=
  match o, cs with
  | OExt tag, _ => ext tag cs
  | OConst c, [] => Some (normalize_const c)
  | OBin w o, [VInt wa a; VInt wb b] =>
    if iw_eq_dec w wa then
      if iw_eq_dec w wb then
        if word_ok w a && word_ok w b then bin_eval w o a b else None
      else None
    else None
  | OZext, [VInt W32 a] => if word_ok W32 a then Some (VInt W64 a) else None
  | OTrunc, [VInt W64 a] =>
    if word_ok W64 a then Some (VInt W32 (word_wrap W32 a)) else None
  | OPtrAdd, [VPtr b off; VInt W64 k] => Some (VPtr b (off + word_signed W64 k))
  | _, _ => None
  end.

Definition env_set (env : vid -> option cval) (x : vid) (v : cval) : vid -> option cval :=
  fun y => if Nat.eq_dec y x then Some v else env y.

Fixpoint read_args (env : vid -> option cval) (xs : list vid) : option (list cval) :=
  match xs with
  | [] => Some []
  | x :: xs =>
    match env x, read_args env xs with
    | Some v, Some vs => Some (v :: vs)
    | _, _ => None
    end
  end.

(** Values have already been read when parameter binding starts. *)
Fixpoint bind_params (env : vid -> option cval) (ps : list (vid * ty)) (vs : list cval)
    : option (vid -> option cval) :=
  match ps, vs with
  | [], [] => Some env
  | (x, _) :: ps, v :: vs => bind_params (env_set env x v) ps vs
  | _, _ => None
  end.

Definition memory_set (m : nat -> option mblock) (b : nat) (v : mblock)
    : nat -> option mblock :=
  fun a => if Nat.eq_dec a b then Some v else m a.

Definition access_ok (mb : mblock) (off : Z) (sz : msize) : bool :=
  mlive mb && (0 <=? off) && (off + Z.of_nat (size_bytes sz) <=? Z.of_nat (msz mb)).

Fixpoint integer_bytes (n : nat) (get : Z -> mval) (off : Z) : option Z :=
  match n with
  | O => Some 0
  | S n =>
    match get off, integer_bytes n get (off + 1) with
    | MInt b, Some z => if (0 <=? b) && (b <? 256) then Some (b + 256 * z) else None
    | _, _ => None
    end
  end.

Fixpoint fragments_ok (n : nat) (get : Z -> mval) (off : Z) (v : cval) (i : nat) : bool :=
  match n with
  | O => true
  | S n =>
    match get off with
    | MFrag v' j =>
      if cval_eq_dec v v' then Nat.eqb i j && fragments_ok n get (off + 1) v (S i)
      else false
    | _ => false
    end
  end.

Definition memory_load (t : ty) (sz : msize) (mb : mblock) (off : Z) : option cval :=
  if access_ok mb off sz then
    match t, sz with
    | TyI32, M8 => None
    | TyI32, _ =>
      option_map (fun z => VInt W32 (word_wrap W32 z))
        (integer_bytes (size_bytes sz) (mbytes mb) off)
    | TyI64, _ =>
      option_map (fun z => VInt W64 (word_wrap W64 z))
        (integer_bytes (size_bytes sz) (mbytes mb) off)
    | TyPtr, M8 =>
      match mbytes mb off with
      | MFrag (VPtr b o) O =>
        if fragments_ok 8 (mbytes mb) off (VPtr b o) 0 then Some (VPtr b o) else None
      | _ => None
      end
    | _, _ => None
    end
  else None.

Definition value_byte (v : cval) (i : Z) : mval :=
  match v with
  | VInt _ z => MInt ((z / 256 ^ i) mod 256)
  | _ => MFrag v (Z.to_nat i)
  end.

Definition store_shape (sz : msize) (v : cval) : bool :=
  match v, sz with
  | VInt _ _, _ => true
  | VPtr _ _, M8 => true
  | VFun _, M8 => true
  | _, _ => false
  end.

Definition memory_store (sz : msize) (mb : mblock) (off : Z) (v : cval) : option mblock :=
  if access_ok mb off sz && store_shape sz v then
    Some (MBlock (msz mb)
      (fun i => if (off <=? i) && (i <? off + Z.of_nat (size_bytes sz))
                then value_byte v (i - off) else mbytes mb i)
      (mlive mb) (msite mb))
  else None.

Definition advance (fr : sframe) (env : vid -> option cval) : sframe :=
  SFrame (ffunc fr) (flabel fr) (S (fpc fr)) env (fret fr).

Definition enter (fr : sframe) (l : label) (env : vid -> option cval) : sframe :=
  SFrame (ffunc fr) l 0 env (fret fr).

Definition at_instr (P : program) (fr : sframe) (i : instr) : Prop :=
  exists fd b, find_func P (ffunc fr) = Some fd /\
    find_block fd (flabel fr) = Some b /\ nth_error (bbody b) (fpc fr) = Some i.

Definition at_term (P : program) (fr : sframe) (t : terminator) : Prop :=
  exists fd b, find_func P (ffunc fr) = Some fd /\
    find_block fd (flabel fr) = Some b /\ fpc fr = List.length (bbody b) /\ bterm b = t.

Definition jump_env (P : program) (fr : sframe) (l : label) (vs : list cval)
    : option (vid -> option cval) :=
  match find_func P (ffunc fr) with
  | None => None
  | Some fd =>
    match find_block fd l with
    | None => None
    | Some b => bind_params (fenv fr) (bparams b) vs
    end
  end.

Fixpoint switch_target (z : Z) (cases : list (Z * label * list vid))
    (d : label) (da : list vid) : label * list vid :=
  match cases with
  | [] => (d, da)
  | (key, l, args) :: rest =>
    if word_wrap W32 key =? z then (l, args) else switch_target z rest d da
  end.

Definition callee_def (P : program) (env : vid -> option cval) (c : callee)
    : option (func * fdef * ssa_block) :=
  let target :=
    match c with
    | CDirect f => Some f
    | CIndirect x _ _ =>
      match env x with
      | Some (VFun f) => Some f
      | _ => None
      end
    end in
  match target with
  | None => None
  | Some f =>
    match find_func P f with
    | None => None
    | Some fd =>
      match find_block fd (fentry fd) with
      | None => None
      | Some b =>
        match c with
        | CDirect _ => Some (f, fd, b)
        | CIndirect _ ps r =>
          if list_eq_dec ty_eq_dec ps (map snd (bparams b)) then
            if ty_eq_dec r (fresult fd) then Some (f, fd, b) else None
          else None
        end
      end
    end
  end.

(** Each constructor performs one language instruction or terminator. *)
Inductive step_s (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    : state -> list event -> state -> Prop :=
  | SOp : forall fr k m nb x o args cs v,
      at_instr P fr (IOp x o args) -> read_args (fenv fr) args = Some cs ->
      op_eval ext o cs = Some v ->
      step_s ext P lim (State (fr :: k) m nb) []
        (State (advance fr (env_set (fenv fr) x v) :: k) m nb)
  | SAlloc : forall fr k m nb x n z,
      at_instr P fr (IAlloc x n) -> fenv fr n = Some (VInt W64 z) ->
      (nb < max_blocks lim)%nat ->
      step_s ext P lim (State (fr :: k) m nb) []
        (State (advance fr (env_set (fenv fr) x (VPtr nb 0)) :: k)
          (memory_set m nb (MBlock (Z.to_nat z) (fun _ => MInt 0) true x)) (S nb))
  | SFree : forall fr k m nb p b mb,
      at_instr P fr (IFree p) -> fenv fr p = Some (VPtr b 0) ->
      m b = Some mb -> mlive mb = true ->
      step_s ext P lim (State (fr :: k) m nb) []
        (State (advance fr (fenv fr) :: k)
          (memory_set m b (MBlock (msz mb) (mbytes mb) false (msite mb))) nb)
  | SLoad : forall fr k m nb x t sz p b off mb v,
      at_instr P fr (ILoad x t sz p) -> fenv fr p = Some (VPtr b off) ->
      m b = Some mb -> memory_load t sz mb off = Some v ->
      step_s ext P lim (State (fr :: k) m nb) []
        (State (advance fr (env_set (fenv fr) x v) :: k) m nb)
  | SStore : forall fr k m nb sz p x b off mb v mb',
      at_instr P fr (IStore sz p x) -> fenv fr p = Some (VPtr b off) ->
      fenv fr x = Some v -> m b = Some mb -> memory_store sz mb off v = Some mb' ->
      step_s ext P lim (State (fr :: k) m nb) []
        (State (advance fr (fenv fr) :: k) (memory_set m b mb') nb)
  | SOutput : forall fr k m nb x v,
      at_instr P fr (IOutput x) -> fenv fr x = Some v ->
      step_s ext P lim (State (fr :: k) m nb) [EvOut v]
        (State (advance fr (fenv fr) :: k) m nb)
  | SJump : forall fr k m nb l args cs env,
      at_term P fr (TJump l args) -> read_args (fenv fr) args = Some cs ->
      jump_env P fr l cs = Some env ->
      step_s ext P lim (State (fr :: k) m nb) [] (State (enter fr l env :: k) m nb)
  | SBr : forall fr k m nb c l1 a1 l2 a2 z l args cs env,
      at_term P fr (TBr c l1 a1 l2 a2) -> fenv fr c = Some (VInt W32 z) ->
      (l, args) = (if z =? 0 then (l2, a2) else (l1, a1)) ->
      read_args (fenv fr) args = Some cs -> jump_env P fr l cs = Some env ->
      step_s ext P lim (State (fr :: k) m nb) [] (State (enter fr l env :: k) m nb)
  | SSwitch : forall fr k m nb c cases d da z l args cs env,
      at_term P fr (TSwitch c cases d da) -> fenv fr c = Some (VInt W32 z) ->
      switch_target z cases d da = (l, args) ->
      read_args (fenv fr) args = Some cs -> jump_env P fr l cs = Some env ->
      step_s ext P lim (State (fr :: k) m nb) [] (State (enter fr l env :: k) m nb)
  | SCall : forall fr k m nb c args cont cs f fd b env,
      at_term P fr (TCall c args cont) -> read_args (fenv fr) args = Some cs ->
      callee_def P (fenv fr) c = Some (f, fd, b) ->
      bind_params (fun _ => None) (bparams b) cs = Some env ->
      (List.length (fr :: k) < max_frames lim)%nat ->
      step_s ext P lim (State (fr :: k) m nb) []
        (State (SFrame f (fentry fd) 0 env 0%nat ::
          SFrame (ffunc fr) (flabel fr) (fpc fr) (fenv fr) cont :: k) m nb)
  | SReturn : forall fr caller k m nb x v env,
      at_term P fr (TRet x) -> fenv fr x = Some v ->
      jump_env P caller (fret caller) [v] = Some env ->
      step_s ext P lim (State (fr :: caller :: k) m nb) []
        (State (enter caller (fret caller) env :: k) m nb)
  | SReturnMain : forall fr m nb x v,
      at_term P fr (TRet x) -> fenv fr x = Some v ->
      step_s ext P lim (State [fr] m nb) [EvRet v]
        (State [advance fr (fenv fr)] m nb).

(** Initial parameters are the only bindings, and have their declared types and ranges. *)
Definition ssa_initial (P : program) (s : state) : Prop :=
  exists fd b vs env,
    find_func P (main P) = Some fd /\ find_block fd (fentry fd) = Some b /\
    map ty_of vs = map snd (bparams b) /\ Forall valid_cval vs /\
    bind_params (fun _ => None) (bparams b) vs = Some env /\
    s = State [SFrame (main P) (fentry fd) 0 env 0%nat] (fun _ => None) 0.

(** The full semantics starts at main and uses the frame transition rules. *)
Definition ssa_semantics (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    : semantics state event := Semantics (ssa_initial P) (step_s ext P lim).

Definition ssa_final (P : program) (s : state) : Prop :=
  exists fr fd b, stack s = [fr] /\ find_func P (ffunc fr) = Some fd /\
    find_block fd (flabel fr) = Some b /\ (List.length (bbody b) < fpc fr)%nat.

Definition ssa_stopped (P : program) (lim : limits) (s : state) : Prop :=
  exists fr k, stack s = fr :: k /\
    ((exists c args cont cs f fd b env,
        at_term P fr (TCall c args cont) /\ read_args (fenv fr) args = Some cs /\
        callee_def P (fenv fr) c = Some (f, fd, b) /\
        bind_params (fun _ => None) (bparams b) cs = Some env /\
        (max_frames lim <= List.length (fr :: k))%nat) \/
     (exists x n z, at_instr P fr (IAlloc x n) /\ fenv fr n = Some (VInt W64 z) /\
        (max_blocks lim <= next_block s)%nat)).

(** Final states, language traps and resource stops have distinct observations. *)
Definition ssa_endings (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    : endings state :=
  Endings (ssa_final P)
    (fun s => ~ running (ssa_semantics ext P lim) s /\
      ~ ssa_final P s /\ ~ ssa_stopped P lim s)
    (ssa_stopped P lim).

(** * Production fixtures for computed tests

    These reference programs and states support the examples in [ExamplesSsaSyntaxTest].
    The computed assertions remain in the test theory. *)

Local Open Scope nat_scope.

Definition no_ext (_ : nat) (_ : list cval) : option cval := None.

Definition memory_caller : fdef := FDef 0
  [(0, SBlock [(0, TyI64); (1, TyI32)]
    [IAlloc 2 0; IStore M4 2 1; ILoad 3 TyI32 M4 2; IFree 2;
      IOp 4 (OConst (VFun 1)) []]
    (TCall (CIndirect 4 [TyI32] TyI32) [3] 1));
   (1, SBlock [(5, TyI32)] [IOutput 5] (TRet 5))] TyI32.

Definition arithmetic_callee : fdef := FDef 0
  [(0, SBlock [(6, TyI32)]
    [IOp 7 (OConst (VInt W32 1%Z)) []; IOp 8 (OBin W32 BAdd) [6; 7]]
    (TBr 8 1 [8] 2 [6]));
   (1, SBlock [(9, TyI32)] [] (TJump 3 [9]));
   (2, SBlock [(10, TyI32)] [] (TJump 3 [10]));
   (3, SBlock [(11, TyI32)] [] (TRet 11))] TyI32.

Definition memory_calls : program := Program [(0, memory_caller); (1, arithmetic_callee)] 0 [].

Definition bad_operand : program := Program
  [(0, FDef 0 [(0, SBlock [(0, TyI64)] [IOp 1 (OBin W32 BAdd) [0; 0]] (TRet 1))]
    TyI32)] 0 [].

Definition late_definition : program := Program
  [(0, FDef 0 [(0, SBlock []
    [IOp 0 (OBin W32 BAdd) [1; 1]; IOp 1 (OConst (VInt W32 1%Z)) []] (TRet 0))]
    TyI32)] 0 [].

Definition parallel_loop : program := Program
  [(0, FDef 0 [(0, SBlock [(0, TyI32); (1, TyI32)] [] (TJump 0 [1; 0]))] TyI32)] 0 [].

Definition zero_block : mblock := MBlock 8 (fun _ => MInt 0%Z) true 2.

Definition allocation_env : vid -> option cval :=
  env_set (env_set (fun _ => None) 0 (VInt W64 8%Z)) 1 (VInt W32 5%Z).

Definition allocation_start : state :=
  State [SFrame 0 0 0 allocation_env 0] (fun _ => None) 0.

Definition extension_program : program := Program
  [(0, FDef 0 [(0, SBlock [(0, TyI32)] [IOp 1 (OExt 7) [0]] (TRet 1))] TyI32)]
  0 [(7, ([TyI32], TyI32))].

Definition return_program : program := Program
  [(0, FDef 0
    [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
     (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32);
   (1, FDef 0 [(0, SBlock [(2, TyI32)] [] (TRet 2))] TyI32)] 0 [].

Definition caller_env : vid -> option cval := env_set (fun _ => None) 0 (VInt W32 42%Z).

Definition callee_env : vid -> option cval := env_set (fun _ => None) 2 (VInt W32 42%Z).

Definition calling_state : state := State [SFrame 0 0 0 caller_env 0] (fun _ => None) 0.

Definition called_state : state :=
  State [SFrame 1 0 0 callee_env 0; SFrame 0 0 0 caller_env 1] (fun _ => None) 0.

Definition returned_state : state :=
  State [SFrame 0 1 0 (env_set caller_env 1 (VInt W32 42%Z)) 1] (fun _ => None) 0.

Definition identity_ext (tag : nat) (cs : list cval) : option cval :=
  match tag, cs with
  | 7, [v] => Some v
  | _, _ => None
  end.

Definition switch_program : program := Program
  [(0, FDef 0
    [(0, SBlock [(0, TyI32)] []
      (TSwitch 0 [(4294967296%Z, 1, [0]); (1%Z, 2, [0])] 2 [0]));
     (1, SBlock [(1, TyI32)] [] (TRet 1));
     (2, SBlock [(2, TyI32)] [] (TRet 2))] TyI32)] 0 [].

Definition non_dominating_definition : program := Program
  [(0, FDef 0
    [(0, SBlock [(0, TyI32)] [] (TBr 0 1 [] 2 []));
     (1, SBlock [] [IOp 1 (OConst (VInt W32 1%Z)) []] (TJump 3 []));
     (2, SBlock [] [] (TJump 3 []));
     (3, SBlock [] [IOp 2 (OBin W32 BAdd) [1; 1]] (TRet 2))] TyI32)] 0 [].
