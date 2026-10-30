# Gaulois.Examples

Two toy languages, written the way a client would write them and proved against the library: the
structured language `While` and the SSA language `Ssa` with static types, calls and byte memory.
Each has its own operators and its own reference semantics, written without the library; the
library's views are then proved for it once, and every catalogue analysis becomes sound on it. For
example, `While`'s `x + y` is `wrap32 (x + y)` over `Z`; one bridge equation says it equals
`Bits.eval` of the 32-bit addition, so every `Domains` operator transfer works for it.

The theory is `Gaulois.Examples`, with subdirectories `While` and `Ssa`. Nothing here is a model
of the library: a toy never imports a `Bits` operator into its semantics. Every theorem below is
required and proved; every `Example` is small enough for `vm_compute` and is a smoke check, except
those named as the acceptance evidence of a checker, which are required.

The `examples/While` and `examples/Ssa` files are production reference-client modules and use
the `Examples` basename prefix. Computed `Example` declarations belong in `tests/Examples`,
with the same statements and ownership as below. Definitions needed by those examples and the
contracted theorems remain in the production modules. A reference below to an analysis module
for a computed `Example` identifies its client and owner, not its physical test location.
Their qualified names use `Gaulois.Tests.Examples.<owned test module>` instead of the production
`Gaulois.Examples.{While,Ssa}.Examples*` module paths.

## Files

| File | Contents | Card |
|---|---|---|
| `ExamplesWhileSyntax.v` | expressions, operators, statements | EX-1 |
| `ExamplesWhileSemantics.v` | stores, operator semantics, small-step with output events | EX-1 |
| `ExamplesWhileBridge.v` | the bridge equations to `Bits`, one per operator | EX-4 |
| `ExamplesWhileSkeleton.v` | translation to the skeleton, client, bisimulation, behaviour transport | EX-4 |
| `ExamplesWhileViews.v` | skeleton-client laws, variable, demand and effects views, region summaries | EX-4 |
| `ExamplesWhileAnalyses.v` | instantiation theorems and fixtures for computed examples | EX-4, ANA-2 |
| `ExamplesSsaSyntax.v` | types, values, operators, instructions, terminators, functions | EX-2 |
| `ExamplesSsaTyping.v` | operator signatures, well-formedness and typed environments | EX-2 |
| `ExamplesSsaTypingProofs.v` | operator typing, preservation and checker soundness | EX-2 |
| `ExamplesSsaSemantics.v` | memory, small-step semantics with frames, endings | EX-2 |
| `ExamplesSsaActivation.v` | the activation semantics of one function | EX-5a |
| `ExamplesSsaBridge.v` | the bridge to `Bits` for the integer operators | EX-5a |
| `ExamplesSsaViews.v` | block and point graph views, SSA view and its laws, variable and demand views, the effects table | EX-5a |
| `ExamplesSsaStrict.v` | strictness laws of the block view; activation lifting of reachability and traces | EX-5c |
| `ExamplesSsaEffects.v` | effects view and calls view with their laws | EX-5b |
| `ExamplesSsaMemory.v` | the full-program graph and memory views | EX-6 |
| `ExamplesSsaPointers.v` | pointer view, footprints, pointer and zero laws | ANA-9 |
| `ExamplesSsaBytes.v` | byte view and byte laws | ANA-10a |
| `ExamplesSsaAnalyses.v` | instantiation theorems and fixtures, factorial included | EX-5a, ANA-3 to ANA-9, ANA-10a, ANA-10e |

## Definitions

### While (EX-1)

```coq
(* ExamplesWhileSyntax.v. Constructors carry an S prefix so that they never clash with the
   skeleton's. *)
Definition var : Type := nat.
Inductive unop : Type := Neg | BNot | LNot.
Inductive binop : Type :=
  | Add | Sub | Mul | And | Or | Xor | Shl | ShrU | ShrS | Eq | Ne | LtU | LeU | LtS | LeS.
Inductive expr : Type :=
  | EConst (w : Z)                            (* its value is wrap32 w, so a constant is always a word *)
  | EVar (x : var)
  | EUn (o : unop) (e : expr)
  | EBin (o : binop) (e1 e2 : expr).
Inductive stmt : Type :=
  | SSkip
  | SAssign (x : var) (e : expr)
  | SSeq (s1 s2 : stmt)
  | SIf (c : expr) (s1 s2 : stmt)            (* c is true when nonzero *)
  | SLoop (s : stmt)                         (* repeats s; left only by SBreak *)
  | SBreak (n : nat)                         (* leave the n-th enclosing loop, 0 the innermost *)
  | SContinue (n : nat)                      (* restart the body of the n-th enclosing loop *)
  | SOutput (e : expr).
```

```coq
(* ExamplesWhileSemantics.v. Words are the integers in [0, 2^32); every operator is defined by
   Z arithmetic and a final reduction, and none is a Bits operator. *)
Definition wrap32 (z : Z) : Z := z mod 4294967296.
Definition signed32 (z : Z) : Z := if (z <? 2147483648)%Z then z else (z - 4294967296)%Z.
Definition eval_un (o : unop) (a : Z) : Z.
(* Neg: wrap32 (-a); BNot: 4294967295 - a; LNot: 1 if a = 0, else 0 *)
Definition eval_bin (o : binop) (a b : Z) : Z.
(* Add, Sub, Mul: wrap32 of the Z result; And, Or, Xor: Z.land, Z.lor, Z.lxor;
   Shl: wrap32 (Z.shiftl a (b mod 32)); ShrU: Z.shiftr a (b mod 32);
   ShrS: wrap32 (Z.shiftr (signed32 a) (b mod 32));
   Eq, Ne, LtU, LeU: 1 or 0 on the unsigned values; LtS, LeS: 1 or 0 on signed32 of both *)
Definition store : Type := var -> Z.
Definition update (sigma : store) (x : var) (z : Z) : store :=
  fun y => if Nat.eqb x y then z else sigma y.
Fixpoint eval_expr (sigma : store) (e : expr) : Z.
(* the evident recursion; EConst w gives wrap32 w, EVar x gives sigma x *)
Inductive wframe : Type :=
  | KSeq (s : stmt)            (* the second half of a sequence *)
  | KJoin                      (* a branch of an if, or the second half of a sequence, is running *)
  | KLoop (body : stmt)        (* a loop body is running *)
  | KExit.                     (* the loop is left when this frame is reached by a break *)
(* The three forms mirror the skeleton machine's steps one for one, so that the bisimulation of
   EX-4 is lock-step. *)
Inductive config : Type :=
  | Run (s : stmt) (k : list wframe) (sigma : store)      (* about to run s *)
  | Enter (body : stmt) (k : list wframe) (sigma : store) (* a loop was entered; start its body *)
  | WhileFin (k : list wframe) (sigma : store).                (* the current statement completed *)
Inductive target_cont : Type := JRun (s : stmt) (k : list wframe) | JFin (k : list wframe).
Definition jump_cont (d : nat) (k : list wframe) : option target_cont.
(* the d-th label among the KLoop and KExit frames, innermost first, skipping KSeq and KJoin:
   a KLoop s gives JRun s (KLoop s :: the frames below it), a KExit gives JFin (the frames below
   it); None if there are fewer labels. A break n uses d = 2n + 1 and a continue n uses d = 2n *)
Inductive step_w : config -> list Z -> config -> Prop :=
  | w_skip : forall k sigma, step_w (Run SSkip k sigma) nil (WhileFin k sigma)
  | w_assign : forall x e k sigma,
      step_w (Run (SAssign x e) k sigma) nil (WhileFin k (update sigma x (eval_expr sigma e)))
  | w_output : forall e k sigma,
      step_w (Run (SOutput e) k sigma) [eval_expr sigma e] (WhileFin k sigma)
  | w_seq : forall s1 s2 k sigma, step_w (Run (SSeq s1 s2) k sigma) nil (Run s1 (KSeq s2 :: k) sigma)
  | w_if : forall c s1 s2 k sigma,
      step_w (Run (SIf c s1 s2) k sigma) nil
        (Run (if Z.eqb (eval_expr sigma c) 0 then s2 else s1) (KJoin :: k) sigma)
  | w_loop : forall s k sigma, step_w (Run (SLoop s) k sigma) nil (Enter s (KExit :: k) sigma)
  | w_enter : forall s k sigma, step_w (Enter s k sigma) nil (Run s (KLoop s :: k) sigma)
  | w_break : forall n k k' sigma, jump_cont (2 * n + 1) k = Some (JFin k') ->
      step_w (Run (SBreak n) k sigma) nil (WhileFin k' sigma)
  | w_continue : forall n k s k' sigma, jump_cont (2 * n) k = Some (JRun s k') ->
      step_w (Run (SContinue n) k sigma) nil (Run s k' sigma)
  | w_fin_seq : forall s k sigma, step_w (WhileFin (KSeq s :: k) sigma) nil (Run s (KJoin :: k) sigma)
  | w_fin_join : forall k sigma, step_w (WhileFin (KJoin :: k) sigma) nil (WhileFin k sigma)
  | w_fin_exit : forall k sigma, step_w (WhileFin (KExit :: k) sigma) nil (WhileFin k sigma)
  | w_fin_loop : forall s k sigma, step_w (WhileFin (KLoop s :: k) sigma) nil (Run s (KLoop s :: k) sigma).
(* Initial configurations are `Run prog nil sigma` with `init sigma`. Final: `WhileFin nil _`.
   There are no traps and no resource stops. A break or continue with too few loops is stuck. *)
Definition while_semantics (prog : stmt) (init : store -> Prop) : semantics config Z.
Definition while_endings : endings config.
Definition store_of_config (c : config) : store :=
  match c with Run _ _ sigma | Enter _ _ sigma | WhileFin _ sigma => sigma end.
(* Stores whose values are words: the initial stores of every instantiation below. *)
Definition word_stores : store -> Prop := fun sigma => forall x, is_word 32 (sigma x).
Definition var_encoding : encoding var := nat_encoding.
```

### While (EX-4)

```coq
(* ExamplesWhileBridge.v. Each toy operator is one Bits expression over Var 0 and Var 1. *)
Definition un_bits (o : unop) : Bits.expr.
Definition bin_bits (o : binop) : Bits.expr.
(* Add, Sub, Mul, And, Or, Xor: the 32-bit bvadd, bvsub, bvmul, bvand, bvor, bvxor;
   Shl, ShrU, ShrS: bvshl, bvlshr, bvashr of Var 0 by (bvand (Var 1) 31);
   Eq, Ne, LtU, LeU, LtS, LeS: the comparison as a 1-bit result zero-extended to 32 bits;
   Neg: bvneg; BNot: bvnot; LNot: the zero test zero-extended *)
Definition env2 (a b : Z) : nat -> width * Z := fun i => (32%positive, if Nat.eqb i 0 then a else b).
```

```coq
(* ExamplesWhileSkeleton.v. The translation: every loop is a Block around a Loop, so a break n
   is a jump of depth 2n + 1 and a continue n a jump of depth 2n. *)
Inductive atom : Type := ANop | AAssign (x : var) (e : expr) | AOutput (e : expr).
Fixpoint loops_ok (d : nat) (s : stmt) : bool.
(* d counts the enclosing loops: SBreak n and SContinue n need n < d, SLoop s checks s at S d *)
Fixpoint to_skeleton (s : stmt) : Skeleton.stmt atom expr.
(* SSkip: Atom ANop; SAssign x e: Atom (AAssign x e); SOutput e: Atom (AOutput e);
   SSeq, SIf c: Seq, If c; SLoop s: Block (Loop (to_skeleton s));
   SBreak n: Jump (2 * n + 1); SContinue n: Jump (2 * n) *)
Definition while_client (init : store -> Prop) : skeleton_client atom expr store Z.
(* init_store = init; atom_step: ANop silent, AAssign updates, AOutput emits [eval_expr sigma e];
   atom_trap and atom_stop are False; guard_bool e sigma = Some (negb (eval_expr sigma e =? 0));
   guard_index _ _ = None; jump_effect _ _ sigma sigma' := sigma' = sigma (so jump_total holds) *)
Inductive match_state (prog : stmt) : config -> mstate store -> Prop.
(* Run s k sigma matches Go p fs sigma when the subtree at p of to_skeleton prog is to_skeleton s
   and fs is the translation of k (KSeq t: FSeq, KJoin: FJoin, KExit: FBlock, KLoop: FLoop);
   Enter s k sigma matches Go p fs sigma at the Loop node whose body is to_skeleton s; and
   WhileFin k sigma matches Ret p fs sigma for the completed position p. Each step_w rule matches
   the skeleton rule of the same name: w_skip and w_assign and w_output step_atom, w_seq
   step_seq, w_if step_if, w_loop step_block, w_enter step_loop, w_break and w_continue step_jump
   with resume, w_fin_seq step_ret_seq, w_fin_join step_ret_join, w_fin_exit step_ret_block and
   w_fin_loop step_ret_loop *)
```

```coq
(* ExamplesWhileViews.v *)
Definition while_skel_vars : skel_vars atom expr var.
(* atom_uses (AAssign _ e) = vars of e; atom_defs (AAssign x _) = [x]; AOutput e uses vars of e,
   defines nothing; ANop neither; guard_uses e = vars of e; atom_trap_uses = nil *)
Definition while_var_view (prog : stmt) (init : store -> Prop) :
  var_view (mstate store) Z skel_point (skel_edge atom expr) var Z.
(* gview = skeleton_view (to_skeleton prog) (while_client init); uses and defs of an edge from its
   actions (`skel_acts`) through while_skel_vars and act_vars; exit_uses _ = nil;
   vget m x = store_of m x *)
Definition while_region_alg (prog : stmt) : summary_algebra atom expr (bool * list nat).
(* For child summaries (b, e), the fields are:
   on_atom _ = (true, nil);
   on_seq (b1, e1) (b2, e2) = (b1 && b2, e1 ++ e2);
   on_if _ (b1, e1) (b2, e2) = (b1 || b2, e1 ++ e2);
   on_block (b, e) = (b || existsb (Nat.eqb 0) e, lower e);
   on_loop (b, e) = (false, lower e);
   on_jump n = (false, [n]); on_jump_if _ n = (true, [n]);
   on_jump_table _ ns n = (false, n :: ns).
   The program argument does not change the fields. The second component preserves the order and
   duplicates of escapes, including the default before the table entries. *)
(* Each child is summarised once in a bottom-up traversal. Charge list concatenation, lowering and
   zero scans to the sizes of the materialised summaries and their child inventories, in addition
   to traversal and map costs. The total inventory size can exceed the syntax size; do not traverse
   source subtrees again per node or scan these lists inside solver loops. *)
(* The effects of While's atoms: only an output observes; nothing reads or writes a heap, traps,
   stops, allocates, frees or calls. *)
Definition while_effects : effects atom.
Definition while_effects_view (prog : stmt) : effects_view (mstate store) atom unit.
(* instr_at (Go p _ _) = the atom at p of to_skeleton prog, None at other positions or at Ret;
   heap _ = tt; heap_agree s t = (s = t); depth _ = 0.
   While has no heap: this relation requires the same whole nonheap machine state. *)
(* The neededness view: an output demands the variables of its operand, a branch the variables of
   its guard, an assignment x := e defines x and, when x is needed, demands the variables of e. *)
Definition while_demand_view (prog : stmt) (init : store -> Prop) :
  demand_view (mstate store) Z skel_point (skel_edge atom expr) var Z bool.
(* dgraph = gview (while_var_view prog init); ddefs e = the defs of the edge; dnec e = the variables
   of an AOutput operand and of an AGuard guard, each paired with true; dback e x true = the
   variables of e' for the AAssign x e' of the edge, paired with true; dback e x false = nil;
   dexit _ = nil; dlookup m x = store_of m x; dvars = the variables of prog, once each *)
(* The available-expression view: the expressions are While's `expr`, an assignment or an output
   computes the binary subexpressions of its operand, and an assignment to x kills every expression
   that mentions x. *)
Definition while_genkill_view (prog : stmt) (init : store -> Prop) :
  genkill_view (mstate store) Z skel_point (skel_edge atom expr) expr Z.
(* gkview = gview (while_var_view prog init); kill e u = true when an AAssign x _ atom of the edge
   has x among the variables of u. gen e contains the EBin subexpressions of the operands of the
   AAssign or AOutput atoms and of the guards, filtered to those for which kill e u = false.
   The filter accounts for every action of the edge. uval m u = Some (eval_expr (store_of m) u) *)
Definition while_copy_view (prog : stmt) (init : store -> Prop) :
  copy_view (mstate store) Z skel_point (skel_edge atom expr) var Z.
(* cvars is while_var_view prog init. copies e contains (x, y) exactly for an assignment x := y
   among the actions of e; no other action contributes a pair. Card: EX-4. *)
(* Dead-code erasure of While: every assignment to a variable that the demand does not need becomes
   a skip. The skeleton of the result has the shape of the original, with ANop for AAssign. *)
Fixpoint erase_dead (dead : var -> bool) (s : stmt) : stmt.
(* SAssign x e becomes SSkip when dead x = true; the other constructors recurse; SOutput stays *)
Definition while_dce (prog : stmt) (init : store -> Prop)
    (d : finite_map var_encoding (dvars (while_demand_view prog init)) bool) : stmt :=
  erase_dead (fun x => negb (dget var_encoding bool_lattice d x)) prog.
Definition while_erasure (prog : stmt) (init : store -> Prop)
    (d : finite_map var_encoding (dvars (while_demand_view prog init)) bool) :
  erasure (mstate store) Z skel_point (skel_edge atom expr) var Z atom.
(* er_demand = while_demand_view prog init; er_graph = the view of the skeleton machine of
   `to_skeleton (while_dce prog init d)` whose `cfg` is literally that of the original's view (the
   erased program has the shape of the original, so its steps follow the same edges, a fact that the
   laws below prove and that makes `er_cfg` hold by reflexivity); er_erased e = true exactly when
   the actions of e in to_skeleton prog are [AAtom (AAssign x _)] with dead x; er_instr e = the atom *)
```

### Ssa (EX-2)

```coq
(* ExamplesSsaSyntax.v. Every Ssa definition takes `ext : nat -> list cval -> option cval`, the
   evaluation of `OExt tag`, as a first argument that is omitted below; `fun _ _ => None` makes the
   extension operators trap, and Float supplies the float operators. Static types: every value
   has one type, fixed by its definition. *)
Definition func : Type := nat.
Definition label : Type := nat.
Definition vid : Type := nat.          (* unique in the whole program: each value is defined once *)
Inductive iw : Type := W32 | W64.
Inductive msize : Type := M1 | M2 | M4 | M8.
Inductive ty : Type := TyI32 | TyI64 | TyPtr | TyFun | TyF32 | TyF64.
Inductive cval : Type :=
  | VInt (w : iw) (z : Z)              (* z in [0, 2^32) or [0, 2^64) *)
  | VPtr (b : nat) (o : Z)             (* block number and byte offset *)
  | VFun (f : func)
  | VF32 (bits : Z)                    (* IEEE bit patterns: opaque here, used by Float *)
  | VF64 (bits : Z).
Definition ty_of (c : cval) : ty :=
  match c with
  | VInt W32 _ => TyI32 | VInt W64 _ => TyI64 | VPtr _ _ => TyPtr | VFun _ => TyFun
  | VF32 _ => TyF32 | VF64 _ => TyF64
  end.
Definition valid_cval (c : cval) : Prop :=
  match c with
  | VInt W32 z => (0 <= z < 2 ^ 32)%Z
  | VInt W64 z => (0 <= z < 2 ^ 64)%Z
  | _ => True
  end.
Inductive bop : Type := BAdd | BSub | BMul | BDivU | BAnd | BOr | BXor | BShl | BShrU | BEq | BLtU | BLtS.
Inductive sop : Type :=
  | OConst (c : cval)                  (* an integer payload is wrapped to its width: EConst's rule *)
  | OBin (w : iw) (o : bop)            (* comparisons give VInt W32 0 or 1; BDivU traps on 0 *)
  | OZext | OTrunc                     (* I32 to I64 and back *)
  | OPtrAdd                            (* pointer plus an I64 offset, read as a signed 64-bit integer *)
  | OExt (tag : nat).                  (* an extension operator, evaluated by `ext` *)
Inductive instr : Type :=
  | IOp (x : vid) (o : sop) (args : list vid)
  | IAlloc (x : vid) (n : vid)          (* a fresh zeroed block of n bytes, n an I64 value; x is its site *)
  | IFree (p : vid)
  | ILoad (x : vid) (t : ty) (sz : msize) (p : vid)   (* little-endian; t is TyI32, TyI64 or TyPtr *)
  | IStore (sz : msize) (p v : vid)
  | IOutput (v : vid).
(* An indirect callee names the signature it expects, as a call_indirect does. *)
Inductive callee : Type := CDirect (f : func) | CIndirect (v : vid) (ps : list ty) (r : ty).
Inductive terminator : Type :=
  | TJump (l : label) (args : list vid)
  | TBr (c : vid) (l1 : label) (a1 : list vid) (l2 : label) (a2 : list vid)
  | TSwitch (c : vid) (cases : list (Z * label * list vid)) (d : label) (da : list vid)
  | TCall (c : callee) (args : list vid) (k : label)   (* the result is the one parameter of k *)
  | TRet (v : vid).
Record ssa_block : Type := SBlock { bparams : list (vid * ty); bbody : list instr; bterm : terminator }.
Record fdef : Type := FDef { fentry : label; blocks : list (label * ssa_block); fresult : ty }.
(* `ext_sigs` declares the signature of each extension operator the program uses. *)
Record program : Type := Program {
  funcs : list (func * fdef); main : func; ext_sigs : list (nat * (list ty * ty))
}.
Definition find_func (P : program) (f : func) : option fdef.         (* lookup in funcs *)
Definition find_block (fd : fdef) (l : label) : option ssa_block.    (* lookup in blocks *)
```

Specified once, for every rule below:
- **Parallel parameter reads.** A jump, branch, switch or call binds the target's parameters
  simultaneously: every argument is read in the environment before the jump, so `l(b, a)` into
  parameters `(a, b)` swaps them.
- **Switch width.** The scrutinee of `TSwitch` is a 32-bit integer; each case key is wrapped to 32
  bits; the first case whose wrapped key equals the scrutinee wins; otherwise the default.
- **Call continuations.** The continuation `k` of a `TCall` has exactly one parameter, of the
  callee's result type, and is the target of that call alone and of no jump, branch or switch; the
  returned value is bound to that parameter and nothing else changes in the caller's environment.
- **Constants.** `OConst (VInt w z)` evaluates to `VInt w (z mod 2^bits w)`, so a constant is always
  a word, as While's `EConst` is.

```coq
(* ExamplesSsaTyping.v *)
Definition iw_ty (w : iw) : ty := match w with W32 => TyI32 | W64 => TyI64 end.
Definition op_sig (P : program) (o : sop) : option (list ty * ty).
(* OConst c: Some (nil, ty_of c); OBin w o: both operands iw_ty w, the result iw_ty w, but TyI32
   for BEq, BLtU and BLtS; OZext: [TyI32] to TyI64; OTrunc: [TyI64] to TyI32; OPtrAdd: [TyPtr; TyI64]
   to TyPtr; OExt tag: the entry of ext_sigs P for tag, None when the program declares none *)
Definition load_ok (t : ty) (sz : msize) : bool.
(* TyI32: M1, M2 or M4; TyI64: M1, M2, M4 or M8; TyPtr: M8; no other type is loaded *)
Definition static_ty (P : program) (f : func) : vid -> option ty.
(* a block parameter: its declared type; an IOp result: the result of op_sig; IAlloc: TyPtr; ILoad:
   its t; None for a vid that f does not define *)
Definition ext_respects (ext : nat -> list cval -> option cval) (P : program) : Prop :=
  forall tag ps r cs v, In (tag, (ps, r)) (ext_sigs P) -> map ty_of cs = ps ->
    Forall valid_cval cs -> ext tag cs = Some v -> ty_of v = r /\ valid_cval v.
Definition wf_program (ext : nat -> list cval -> option cval) (P : program) : Prop.
(* the conjunction of:
   1. names: main names a function; every function has its entry block; function numbers and block
      labels are unique; every label and function that a terminator names exists;
   2. one definition: every vid is defined once in the whole program, by one instruction or one
      block parameter;
   3. dominance: every operand of an instruction or terminator is defined by a parameter, or by an
      earlier instruction of its block, or in a block that dominates the use (dominance over the
      block graph of the function, defined here without the library);
   4. types: the operands of an instruction have the types of its signature; the condition of a
      branch and the scrutinee of a switch are TyI32; the arguments of a jump, branch or switch have
      the types of the target's parameters; the arguments of a call have the types of the callee's
      entry parameters, and the single parameter of its continuation the callee's result type; an
      indirect callee value is a TyFun; a returned value has the function's result type; a load
      satisfies load_ok; the size operand of IAlloc has type TyI64; the constants of OConst are of
      the type they claim;
   5. continuations: a call continuation has one parameter and is entered by that call only;
   6. ext_respects ext P *)
(* The decidable part of wf_program, for concrete programs: conditions 1 to 5, with `wf_check_sound`
   adding ext_respects. *)
Definition wf_check (P : program) : bool.
(* An environment is typed when every value it binds has the static type of its vid. *)
Definition typed_env (P : program) (f : func) (env : vid -> option cval) : Prop :=
  forall x c, env x = Some c -> static_ty P f x = Some (ty_of c) /\ valid_cval c.
```

```coq
(* ExamplesSsaSemantics.v *)
Inductive mval : Type := MInt (n : Z) | MFrag (p : cval) (i : nat).   (* a byte, or one byte of a pointer *)
Record mblock : Type := MBlock { msz : nat; mbytes : Z -> mval; mlive : bool; msite : vid }.
Record sframe : Type := SFrame {
  ffunc : func; flabel : label; fpc : nat;
  fenv : vid -> option cval;
  fret : label                          (* where the callee's result continues, while it runs *)
}.
Record state : Type := State { stack : list sframe; mem : nat -> option mblock; next_block : nat }.
Inductive event : Type := EvOut (v : cval) | EvRet (v : cval).   (* a run's result is an event *)
Record limits : Type := Limits { max_frames : nat; max_blocks : nat }.
Definition op_eval (ext : nat -> list cval -> option cval) : sop -> list cval -> option cval.
(* None: trap. OConst c: Some c with an integer payload wrapped; OBin w o on two VInt of width w:
   BAdd, BSub, BMul wrapped to w; BDivU None when the divisor is 0, else the quotient; BAnd, BOr,
   BXor; BShl and BShrU by the amount modulo the width; BEq, BLtU, BLtS give VInt W32 0 or 1; any
   other operand shape None (typing makes it unreachable); OZext [VInt W32 a] = VInt W64 a; OTrunc
   [VInt W64 a] = VInt W32 (a mod 2^32); OPtrAdd [VPtr b o; VInt W64 k] = VPtr b (o + signed k);
   OExt tag cs = ext tag cs. OBin, OZext and OTrunc return None when an integer input is outside
   its width; on valid inputs the equations above apply. *)
Inductive step_s (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
    state -> list event -> state -> Prop.
(* One constructor per row; a step executes the instruction at fpc, or the terminator when fpc is
   at the end of the body. Only the innermost frame changes unless stated.
   IOp x o args       env x := the result; trap if op_eval is None (no step)
   IAlloc x n         the block number next_block, Z.to_nat of n zero bytes, live, site x; x :=
                      VPtr next_block 0; next_block + 1
   IFree p            the block of p, at offset 0 and live, becomes dead; else trap
   ILoad x t sz p     p = VPtr b o in a live block with o >= 0 and o + size sz <= msz: for TyI32 and
                      TyI64 all-MInt bytes give the VInt of that type (little-endian, zero-extended);
                      for TyPtr eight MFrag of one pointer in order give it back; anything else, or
                      outside a live block, traps
   IStore sz p v      write the bytes of v (MInt for integers, truncated to sz bytes; MFrag for a
                      pointer or function, with sz = M8) at p in a live block; else trap
   IOutput v          event EvOut (env v)
   TJump, TBr, TSwitch   bind the target's parameters in parallel to the argument values, fpc := 0
   TCall c args k     a new frame at the callee's entry with its parameters bound; the caller's
                      fret := k; trap if an indirect callee is not a VFun of the declared signature
   TRet v             a frame below: pop, the new innermost frame goes to its fret block with the
                      block's one parameter bound to env v; the only frame: fpc := past the end,
                      event EvRet (env v)
   Resource stops: a call beyond max_frames or an allocation beyond max_blocks is not a step; the
   state is `stopped`. Initial: one frame at the entry of main, parameters arbitrary values of their
   declared types and valid_cval, an empty memory, next_block 0. Bytes written by a store are in
   [0, 256); integer loads decode those bytes and produce valid_cval values. *)
Definition ssa_semantics (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  semantics state event.
Definition ssa_endings (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  endings state.
(* final: the only frame is past the end of its block; trapped: the next step would trap;
   stopped: it would exceed a limit *)
```

### Ssa (EX-5a): activation semantics and views

```coq
(* ExamplesSsaActivation.v. One function, one environment. The memory is not modelled; loads and
   allocations produce arbitrary values of their type and stores and frees do nothing, and a call is
   one step that binds an arbitrary result. This is the semantics for which the SSA view is stated. *)
Record astate : Type := AState { alabel : label; apc : nat; aenv : vid -> option cval }.
Definition activation (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  semantics astate event.
(* initial: alabel = fentry f, apc = 0, aenv binds exactly the entry block's parameters, to
   arbitrary values of their declared types satisfying valid_cval; IOp, IOutput, TJump, TBr, TSwitch
   as in step_s, with
   the same parallel binding and the same trap; IAlloc x _: x := any VPtr; ILoad x t _ _: x := any
   value of type t (an integer in range for TyI32 and TyI64, any pointer for TyPtr); IStore, IFree:
   no change; TCall c _ k: the one parameter of k := any valid_cval of the callee's result type;
   TRet v: apc := past the end, event EvRet (aenv v) *)
Definition activation_endings (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  endings astate.
(* final: apc is past the end of the block's terminator; trapped: the next IOp would trap;
   stopped: never *)
```

```coq
(* ExamplesSsaBridge.v *)
Definition ssa_truth (c : cval) : bool :=
  match c with VInt _ z => negb (Z.eqb z 0) | _ => false end.
Definition ssa_bridge : op_bridge sop cval.
(* op_expr: OBin w o by the Bits expression of the width w operation, preserving the toy's shift
   amount reduction modulo 32 or 64, since Bits shifts by at least the width yield zero (BDivU is
   Bits' unsigned division, the trap on zero staying on the toy's side: the bridge speaks only of
   a Some result),
   comparisons as a 1-bit result zero-extended to 32 bits, OZext and OTrunc by extension and
   extract; OConst, OPtrAdd and OExt have none. to_word (VInt w z) = Some (width of w, z) when
   valid_cval (VInt w z), and None for an invalid integer or any other value *)
```

```coq
(* ExamplesSsaViews.v *)
Record ssa_edge : Type := SsaEdge { esrc : label; edst : label; eslot : nat }.
(* eslot tells apart the parallel edges of a switch and the branches of a TBr. In the block view it
   is the branch index of the terminator; in the point view an instruction step at pc has slot pc
   and a terminator branch j has slot (length of the body) + j *)
Definition values_of (P : program) (f : func) : list vid.     (* every vid that f defines, once *)
Definition ssa_block_view (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  ssa_view astate event label ssa_edge vid sop cval.
(* nodes: the labels of f; entries = [fentry f]; an edge per terminator target, from the block to
   the target, with edge_args = the terminator's argument list for that target (a call's
   continuation has none) and edge_guard: TBr gives [Condition c GTrue] and [Condition c GFalse] on
   its two edges, TSwitch gives [Condition c (GConst (VInt W32 key))] on the edge of each case and
   a Condition c (GNotConst (VInt W32 key)) for each case on the default; point = alabel; stays = a
   step within the block (apc moves, alabel does not; a TRet is one); taken = the terminator step
   along its edge; def x = Op o args for an IOp, Param l i for the
   i-th parameter of l, Arbitrary for loads, allocations and the parameter of a call continuation;
   home x = its block; params = the parameters of the block; val s x = aenv s x; op_eval from
   ExamplesSsaSemantics; truth = ssa_truth *)
Definition ssa_point_view (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  graph_view astate event (label * nat) ssa_edge.
(* nodes (l, pc) for pc from 0 to one past the terminator; one edge per step, no stays: the
   instruction-level graph for dense and backward analyses *)
Inductive instr_or_term : Type := AnInstr (i : instr) | ATerm (t : terminator).
Definition call_site : Type := (func * label)%type.   (* the block whose terminator is the call *)
Definition ssa_effects : effects instr_or_term.
(* IOp o: may_trap iff o is OBin _ BDivU or OExt _; IAlloc: reads, allocates, may_stop; IFree:
   reads, writes, frees, may_trap; ILoad: reads, may_trap; IStore: reads, writes, may_trap; IOutput:
   observes; TCall: calls, may_diverge, may_stop, may_trap; TRet: calls, observes; TJump, TBr and
   TSwitch: none. `reads` is true when the step, the trap or the stop may depend on the heap *)
Definition ssa_var_view (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  var_view astate event (label * nat) ssa_edge vid (option cval).
(* uses = the operands of the instruction or terminator edge (a branch edge: the condition and the
   arguments passed along it); defs = its result, or the parameters of the target for a jump, branch
   or switch edge and the one parameter of the continuation for a call; exit_uses at the node of an
   instruction marked may_trap by ssa_effects are its operands, elsewhere nil; vget s x = aenv s x.
   This includes the conservative operands of free, load and store, although activation does not
   model their memory traps. At nodes outside the function's instruction points, exit_uses is nil. *)
Definition ssa_demand_view (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  demand_view astate event (label * nat) ssa_edge vid (option cval) bool.
(* dgraph and ddefs as in ssa_var_view; dnec e: the operands of an effectful instruction (effectful
   ssa_effects KeepTraps), of a branch, a switch, a call and a return; dback e x true: for an edge
   that defines x by an IOp, the operands of the operation, and for a jump edge that defines the
   parameter x, the argument passed for it; dback e x false = nil;
   dexit n = map (fun x => (x, true)) (exit_uses (ssa_var_view ext P f) n);
   dlookup s x = aenv s x; dvars = values_of P f *)
```

### Ssa (EX-5b, EX-5c): effects, calls, lifting; (EX-6): memory

```coq
(* ExamplesSsaEffects.v *)
Definition ssa_effects_view (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  effects_view state instr_or_term ((nat -> option mblock) * nat).
(* instr_at s = the instruction or terminator at fpc of the innermost frame; heap s = (mem s,
   next_block s); heap_agree s t = the two stacks are equal; depth = length of the stack *)
Definition ssa_calls (ext : nat -> list cval -> option cval) (P : program) :
  calls_view state func call_site.
(* functions: the functions of P; roots = [main P]; sites_of f: the (f, l) of the blocks whose
   terminator is a TCall; caller_of (f, l) = f; here s: ffunc of the innermost frame; frames s: the
   suspended frames, innermost first, each with its function and the (function, label) of the call
   at which it is suspended *)
Definition ssa_resolver (P : program) : call_site -> list func.
(* a direct call: [f]; an indirect call of signature (ps, r): every function whose entry
   parameters have the types ps and whose result type is r *)
Definition frame_activation (P : program) (s : state) (i : nat) : option (astate * func).
(* the i-th frame of s, the innermost first, as an activation state of its function *)
(* A trace of the activation semantics is a subsequence of the trace of the run it came from. *)
Inductive subtrace {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, subtrace nil l
  | sub_keep : forall a l1 l2, subtrace l1 l2 -> subtrace (a :: l1) (a :: l2)
  | sub_skip : forall a l1 l2, subtrace l1 l2 -> subtrace l1 (a :: l2).
```

```coq
(* ExamplesSsaMemory.v *)
Definition full_node : Type := (func * label * nat)%type.
Record full_edge : Type := FullEdge { fsrc : full_node; fdst : full_node; fslot : nat }.
Definition ssa_full_view (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  graph_view state event full_node full_edge.
(* the supergraph of the whole program: nodes are the points (function, label, pc) of every function;
   point s = (ffunc, flabel, fpc) of the innermost frame; an edge per step, a call going to the
   callee's entry point and a return to the continuation of the caller; no stays *)
Definition ssa_mem_view (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  mem_view state vid cval nat vid.
(* L = the block number, T = the site, the vid of the IAlloc; loc_of s (VPtr b _) = Some b when the
   block b exists in s, None otherwise and for every other value; loc_site s b = the msite of block
   b; loc_offset s (VPtr _ o) = o; mem_instr: IAlloc x n gives MemAlloc x n, ILoad MemLoad p 0 (size),
   IStore MemStore p 0 (size) v, IFree MemFree p *)
(* ExamplesSsaPointers.v. Card: ANA-9. *)
Definition ssa_ptr_ops (P : program) : list (ptr_op vid vid).
(* every pointer effect that the program can have: PAlloc x x for each IAlloc x _; PCopy x p for each
   OPtrAdd; PLoad and PStore for the pointer-typed loads and stores; PEscape for a pointer output
   and for the pointer arguments of an indirect call; PCopy formal actual for the pointer arguments
   of each call to each function of the resolver; PCopy continuation-parameter value for each
   pointer return to each call site that may call the returning function *)
Definition ssa_ptr_view (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  ptr_view state vid cval nat vid.
(* pval s x = the value of x in the innermost frame of the function that defines x; pop s = the
   pointer effects of the next step, for the frames that the step involves; held s c = the pointer
   value reassembled from the eight fragments at the address that c denotes; pbyte s c = the byte at
   that address, when the block is live and the byte is an MInt *)
Definition ssa_footprints (P : program) : full_edge -> list (footprint vid).
(* for an edge leaving an IAlloc, IStore, IFree or TCall, the range [0, 2^64) of every allocation
   site of P; nil elsewhere. These are the ranges for the zero facts of ANA-9. *)
(* ExamplesSsaBytes.v. Card: ANA-10a. *)
Definition ssa_bytes_view (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  bytes_view state event full_node full_edge vid nat.
(* writes_at n: for an IAlloc, IStore, IFree or TCall at the node, the range [0, 2^64) of every
   allocation site of P (the coarsest sound footprint, and an allocation counts as a write); nil
   elsewhere; bsite s b = the msite of block b; byte s b o = the byte at offset o of the live block b,
   when it is an MInt *)
```

### Wrappers for the computed Examples

```coq
(* ExamplesSsaAnalyses.v and ExamplesWhileAnalyses.v. Encodings for the toys' key types, and small
   wrappers over executable engine results. Each encoding is an injective code: the index of the
   constructor and the codes of its components, paired. Card: EX-5a for label_encoding,
   sop_encoding, const_numeric, const_conc and liveness_at; EX-4 for the While wrappers through
   lcm_avail2; ANA-6 for ok_i32, mul_one_rules, mul_one_term and unit_cost. *)
Definition label_encoding : encoding label := nat_encoding.
Definition sop_encoding : encoding sop.
Definition expr_encoding : encoding expr.            (* While's expressions *)
Definition const_numeric : numeric_domain (tagged (flat Z)) := tagged_domain const_domain.
Definition const_conc : concretisation (tagged (flat Z)) word := tagged_gamma const_gamma.
(* This constant-only client retains const_gamma and tagged_gamma. Product clients use DOM-4's
   word-restricted meaning, which agrees pointwise with the former tagged intersection meaning by
   product_tagged_gamma_equiv. *)
(* liveness_at P pt: the fact at the point pt of solve_liveness on ssa_var_view (fun _ _ => None) P 0;
   while_live_at prog n: the same for while_var_view prog word_stores at the skeleton point n;
   while_needed prog: needed_values var_encoding (while_demand_view prog word_stores);
   while_dead_var prog x: dead_value var_encoding (while_demand_view prog word_stores) x;
   loop_head: the loop head of factorial_while, PEntry [DSecond; DFirst; DBody; DBody];
   lcm_avail, lcm_busy prog: the solutions of solve_total for available_system and busy_system of
   while_genkill_view prog word_stores; lcm_avail2 prog r: the availability solution of the view
   whose gen also lists the expressions that r inserts *)
(* Neededness closure is unconditional; leastness requires empty dback at false. EX-4 and EX-5a
   establish that premise wherever their clients use leastness. The total wrappers remain defined
   on their existing inputs; semantic soundness retains its separate view-law premises. *)
Definition liveness_at (P : program) (pt : label * nat) :
  live_set var_encoding (ssa_var_view (fun _ _ => None) P 0).
Definition while_live_at (prog : stmt) (n : skel_point) :
  live_set var_encoding (while_var_view prog word_stores).
Definition while_needed (prog : stmt) :
  finite_map var_encoding (dvars (while_demand_view prog word_stores)) bool :=
  needed_values var_encoding (while_demand_view prog word_stores).
Definition while_dead_var (prog : stmt) (x : var) : bool :=
  dead_value var_encoding (while_demand_view prog word_stores) x.
Definition loop_head : skel_point := PEntry [DSecond; DFirst; DBody; DBody].
Definition lcm_extended_view (prog : stmt) (r : lcm_result (skel_edge atom expr) skel_point expr) :
  genkill_view (mstate store) Z skel_point (skel_edge atom expr) expr Z.
(* while_genkill_view prog word_stores with gen e extended by insert r e; the rest is unchanged *)
Definition lcm_avail (prog : stmt) :
  skel_point -> avail_set expr_encoding (while_genkill_view prog word_stores).
Definition lcm_busy (prog : stmt) :
  skel_point -> avail_set expr_encoding (while_genkill_view prog word_stores).
Definition lcm_avail2 (prog : stmt) (r : lcm_result (skel_edge atom expr) skel_point expr) :
  skel_point -> avail_set expr_encoding (lcm_extended_view prog r).
(* The integer environments of the e-graph example: every variable holds a 32-bit word. *)
Definition ok_i32 (env : nat -> option cval) : Prop :=
  forall i, exists z, env i = Some (VInt W32 z) /\ (0 <= z < 4294967296)%Z.
Definition mul_one_rules : list (rewrite_rule sop).
(* x * 1 -> x: lhs TApp (OBin W32 BMul) [TVar 0; TApp (OConst (VInt W32 1)) nil], rhs TVar 0, and the
   side condition that the instance of TVar 0 is built from variables, OConst (VInt W32 _) and
   32-bit arithmetic operators only *)
Definition mul_one_term : term sop.      (* the left side of the rule *)
Definition unit_cost : sop -> nat := fun _ => 1.
```

## Theorems

### While

```coq
(** While's expression operators are Bits operators in disguise: one equation per operator. *)
Theorem un_bridge (o : unop) (a : Z) :
  is_word 32 a -> Bits.eval (env2 a 0) (un_bits o) = Some (32%positive, eval_un o a).
Theorem bin_bridge (o : binop) (a b : Z) :
  is_word 32 a -> is_word 32 b ->
  Bits.eval (env2 a b) (bin_bits o) = Some (32%positive, eval_bin o a b).
(** Evaluation stays in range, constants included. *)
Theorem eval_expr_word (sigma : store) (e : expr) :
  (forall x, is_word 32 (sigma x)) -> is_word 32 (eval_expr sigma e).
```
Proof idea: case analysis on the operator, then `Z` arithmetic modulo `2^32` against the
`Bits` semantics (`BIT-1`, `BIT-2`: signed views, shifts, comparisons); `EConst` is `wrap32`, a
word by `Z.mod_pos_bound`. Card: EX-4.

```coq
(** The translation is a lock-step bisimulation of While's reference semantics with the skeleton
    machine, so events, traps, stops and termination are preserved. *)
Theorem while_skeleton_bisimulation (prog : stmt) (init : store -> Prop) :
  bisimulation (while_semantics prog init) while_endings
    (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) (match_state prog).
(** The matching is total on initial configurations. *)
Theorem match_state_initial (prog : stmt) (init : store -> Prop) (c : config) :
  initial (while_semantics prog init) c ->
  exists m, initial (skeleton_semantics (to_skeleton prog) (while_client init)) m /\
    match_state prog c m.
(** Behaviour transport: skeleton-level equality of behaviour is While-level equality. *)
Theorem while_behaviour_transport (prog : stmt) (init : store -> Prop) (c0 c1 : config)
    (m0 m1 : mstate store) :
  match_state prog c0 m0 -> match_state prog c1 m1 ->
  same_behaviour (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) m0
    (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) m1 ->
  same_behaviour (while_semantics prog init) while_endings c0
    (while_semantics prog init) while_endings c1.
```
Proof idea: `match_state` is defined by recursion on the continuation, and each While rule is
matched by the skeleton rule of the same name, with `jump_cont` matched by `resume` at depths
`2n+1` and `2n`; transport is `same_behaviour_trans` and `same_behaviour_sym` with
`bisimilar_same_behaviour`. Card: EX-4.

```coq
(** The skeleton client of While satisfies the laws of a client and the variable-level laws that
    structured liveness needs. *)
Theorem while_client_laws (init : store -> Prop) : skeleton_client_laws (while_client init).
Theorem while_skel_vars_laws (init : store -> Prop) :
  skel_vars_laws (while_client init) while_skel_vars (fun sigma x => sigma x).
(** The fold gives completion and the ordered escape inventory for every skeleton. *)
Theorem while_region_alg_agrees (prog : stmt) (s : Skeleton.stmt atom expr) :
  summarise (while_region_alg prog) s = (falls (fun _ => true) s, escapes s).
(** A While program whose breaks and continues name existing loops has well-nested labels. *)
Theorem to_skeleton_labels_ok (s : stmt) :
  loops_ok 0 s = true -> labels_ok 0 (to_skeleton s) = true.
(** The variable view satisfies the laws of ANA-1. *)
Theorem while_var_view_laws (prog : stmt) (init : store -> Prop) :
  var_view_laws (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) (while_var_view prog init).
(** The effects, demand and gen/kill views satisfy their laws. No While atom reads or writes a
    heap, traps, stops or calls, and the original program never traps. *)
Theorem while_effects_laws (prog : stmt) (init : store -> Prop) :
  effects_laws (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) while_effects
    (while_effects_view prog).
Theorem while_demand_laws (prog : stmt) (init : store -> Prop) :
  demand_laws (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init))
    (reachable_state (skeleton_semantics (to_skeleton prog) (while_client init)))
    var_encoding bool_demand (while_demand_view prog init).
Theorem while_genkill_laws (prog : stmt) (init : store -> Prop) :
  genkill_laws (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) (while_genkill_view prog init).
Theorem while_copy_sound (prog : stmt) (init : store -> Prop) :
  forall s l s' e x y,
    reachable_state (skeleton_semantics (to_skeleton prog) (while_client init)) s ->
    step (skeleton_semantics (to_skeleton prog) (while_client init)) s l s' ->
    taken (gview (while_var_view prog init)) s l s' e ->
    In (x, y) (copies (while_copy_view prog init) e) ->
    vget (while_var_view prog init) s' x = vget (while_var_view prog init) s' y.
(* Proof idea: inspect the skeleton actions and the While assignment semantics. Card: EX-4. *)
Theorem while_never_traps (prog : stmt) (init : store -> Prop) (m : mstate store) :
  initial (skeleton_semantics (to_skeleton prog) (while_client init)) m ->
  never_traps (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init)) m.
```
Proof idea: the first from the shape of the table (`jump_effect` keeps the store, atoms always step
or are the identity); the second by cases on the atoms; the third from `skeleton_view_laws_hold`
and the second; the effects laws by cases on the atom at the position (only `AOutput` emits an
event); for `reads_frame`, substitute the state equality and use the given step and its
successor; the demand laws by the per-atom agreement (an assignment reads the variables of its
operand, a guard the variables of its condition) and `d_vars` from the program's variables; the
gen/kill laws because an assignment changes only its variable; no atom traps, so no state is
trapped. Card: EX-4.

```coq
(** Dead-code erasure on While. Replacing by skips the assignments to the variables that a closed
    demand does not need gives a program with the same behaviour, from every initial store. While
    never traps, so both policies give this conclusion. *)
Theorem while_erasure_laws (prog : stmt) (init : store -> Prop)
    (d : finite_map var_encoding (dvars (while_demand_view prog init)) bool) :
  loops_ok 0 prog = true ->
  erasure_laws KeepTraps (skeleton_semantics (to_skeleton prog) (while_client init))
    (skeleton_endings (to_skeleton prog) (while_client init))
    (skeleton_semantics (to_skeleton (while_dce prog init d)) (while_client init))
    (skeleton_endings (to_skeleton (while_dce prog init d)) (while_client init))
    var_encoding (while_erasure prog init d) d.
Theorem while_dce_sound (prog : stmt) (init : store -> Prop)
    (d : finite_map var_encoding (dvars (while_demand_view prog init)) bool) (sigma : store) :
  loops_ok 0 prog = true ->
  demand_closed var_encoding bool_demand (while_demand_view prog init) d -> init sigma ->
  same_behaviour (while_semantics prog init) while_endings (Run prog nil sigma)
    (while_semantics (while_dce prog init d) init) while_endings
    (Run (while_dce prog init d) nil sigma).
```
Proof idea: `while_erasure_laws` by the shape lemma: the skeleton of `while_dce prog init d` has
the positions, the edges and the targets of the skeleton of `prog` (`erase_dead` changes only the
atom of an assignment), so every kept edge runs the same atom in both machines and an erased edge
is `ANop` in the new one, a silent step that keeps the store, while the original's assignment
changes only a dead variable. `while_dce_sound` is `dce_sound` for `KeepTraps` with
`while_demand_laws`, `reachable_invariant`, `while_effects_laws` (an assignment is not effectful:
no read, write, trap or event) and the dead-variable premise from the definition of `while_dce`,
on the two skeleton machines started at the matched states of `match_state_initial`, which agree
because they are equal; then `while_behaviour_transport` for each program with
`same_behaviour_sym` and `same_behaviour_trans`. This effects-view equality does not replace the
separate `demand_agreement` and `er_agree` relations: the erasure proof still matches states that
may differ on dead variables. Card: EX-4.

```coq
(** Instantiation, dense and structured liveness: two While runs whose stores agree on the live-in
    set behave identically. *)
Theorem while_liveness_sound (prog : stmt)
    (sigma : skel_point -> live_set var_encoding (while_var_view prog word_stores))
    (c0 c1 : config) :
  post_solution (live_lattice var_encoding (while_var_view prog word_stores))
    (liveness_system var_encoding (while_var_view prog word_stores)) sigma ->
  initial (while_semantics prog word_stores) c0 -> initial (while_semantics prog word_stores) c1 ->
  (forall x, fmem var_encoding x (sigma (PEntry nil)) = true ->
     store_of_config c0 x = store_of_config c1 x) ->
  same_behaviour (while_semantics prog word_stores) while_endings c0
    (while_semantics prog word_stores) while_endings c1.
Theorem while_reaching_sound (prog : stmt)
    (sigma : skel_point -> reach_set var_encoding skel_edge_encoding
      (while_var_view prog word_stores)) :
  post_solution (reach_lattice var_encoding skel_edge_encoding (while_var_view prog word_stores))
    (reaching_system var_encoding skel_edge_encoding (while_var_view prog word_stores)) sigma ->
  forall s0 es s x d,
    initial (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s0 ->
    run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
      (gview (while_var_view prog word_stores)) s0 es s ->
    last_writer (fun e y => mentions var_encoding y (defs (while_var_view prog word_stores) e)) es x
      = Some d ->
    fmem (pair_encoding var_encoding skel_edge_encoding) (x, d)
      (sigma (point (gview (while_var_view prog word_stores)) s)) = true.
Theorem while_zero_since_entry_sound (prog : stmt) (locals : list var) (zero : Z)
    (sigma : skel_point -> live_set var_encoding (while_var_view prog word_stores)) :
  (forall s x, initial (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s ->
    In x locals -> vget (while_var_view prog word_stores) s x = zero) ->
  post_solution (zero_lattice var_encoding (while_var_view prog word_stores))
    (zero_since_entry_system var_encoding (while_var_view prog word_stores) locals) sigma ->
  forall s x, reachable_state (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s ->
    fmem var_encoding x (sigma (point (gview (while_var_view prog word_stores)) s)) = true ->
    vget (while_var_view prog word_stores) s x = zero.
Theorem while_equality_sound (prog : stmt) (sigma : skel_point -> partition var_encoding) :
  post_solution (partition_lattice var_encoding)
    (equality_system var_encoding (while_copy_view prog word_stores)) sigma ->
  forall s x y, reachable_state (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s ->
    partition_equiv var_encoding (sigma (point (gview (while_var_view prog word_stores)) s)) x y ->
    vget (while_var_view prog word_stores) s x = vget (while_var_view prog word_stores) s y.
Theorem while_available_sound (prog : stmt)
    (sigma : skel_point -> avail_set expr_encoding (while_genkill_view prog word_stores)) :
  post_solution (avail_lattice expr_encoding (while_genkill_view prog word_stores))
    (available_system expr_encoding (while_genkill_view prog word_stores)) sigma ->
  forall s0 es s u,
    initial (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s0 ->
    run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
      (gkview (while_genkill_view prog word_stores)) s0 es s ->
    fmem expr_encoding u (sigma (point (gkview (while_genkill_view prog word_stores)) s)) = true ->
    exists es1 s1 e es2, es = es1 ++ e :: es2 /\
      run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
        (gkview (while_genkill_view prog word_stores)) s0 es1 s1 /\
      run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
        (gkview (while_genkill_view prog word_stores)) s1 (e :: es2) s /\
      In u (gen (while_genkill_view prog word_stores) e) /\
      uval (while_genkill_view prog word_stores) s u =
        uval (while_genkill_view prog word_stores) s1 u.
Theorem while_busy_sound (prog : stmt)
    (sigma : skel_point -> avail_set expr_encoding (while_genkill_view prog word_stores)) :
  post_solution (avail_lattice expr_encoding (while_genkill_view prog word_stores))
    (busy_system expr_encoding (while_genkill_view prog word_stores)) sigma ->
  forall s es t u,
    reachable_state (skeleton_semantics (to_skeleton prog) (while_client word_stores)) s ->
    run_edges (skeleton_semantics (to_skeleton prog) (while_client word_stores))
      (gkview (while_genkill_view prog word_stores)) s es t ->
    final (skeleton_endings (to_skeleton prog) (while_client word_stores)) t ->
    fmem expr_encoding u (sigma (point (gkview (while_genkill_view prog word_stores)) s)) = true ->
    exists es1 e es2, es = es1 ++ e :: es2 /\
      In u (gen (while_genkill_view prog word_stores) e) /\
      forall e', In e' es1 -> kill (while_genkill_view prog word_stores) e' u = false.
(* Proof idea: instantiate reaching_sound, zero_since_entry_sound and equality_sound with the
   While view laws and while_copy_sound, and available_sound and busy_sound with
   while_genkill_laws. Card: EX-4. *)
Theorem while_structured_liveness_sound (prog : stmt)
    (sigma : skel_point -> skel_set var_encoding while_skel_vars (to_skeleton prog))
    (c0 c1 : config) :
  post_solution (skel_lattice var_encoding while_skel_vars (to_skeleton prog))
    (structured_liveness_system var_encoding while_skel_vars (to_skeleton prog)) sigma ->
  initial (while_semantics prog word_stores) c0 -> initial (while_semantics prog word_stores) c1 ->
  (forall x, fmem var_encoding x (sigma (PEntry nil)) = true ->
     store_of_config c0 x = store_of_config c1 x) ->
  same_behaviour (while_semantics prog word_stores) while_endings c0
    (while_semantics prog word_stores) while_endings c1.
Theorem while_certificate_sound (prog : stmt)
    (cert : certificate var_encoding while_skel_vars (to_skeleton prog)) :
  certificate_check var_encoding while_skel_vars (to_skeleton prog) cert = true ->
  exists sigma,
    post_solution (skel_lattice var_encoding while_skel_vars (to_skeleton prog))
      (structured_liveness_system var_encoding while_skel_vars (to_skeleton prog)) sigma /\
    certificate_of var_encoding while_skel_vars (to_skeleton prog) sigma = cert.
Theorem while_certificate_complete (prog : stmt)
    (sigma : skel_point -> skel_set var_encoding while_skel_vars (to_skeleton prog)) :
  post_solution (skel_lattice var_encoding while_skel_vars (to_skeleton prog))
    (structured_liveness_system var_encoding while_skel_vars (to_skeleton prog)) sigma ->
  certificate_check var_encoding while_skel_vars (to_skeleton prog)
    (certificate_of var_encoding while_skel_vars (to_skeleton prog) sigma) = true.
Theorem while_region_table_agrees {R} (alg : summary_algebra atom expr R) (prog : stmt)
    (p : position) :
  Map.get position_encoding p (region_table alg (to_skeleton prog)) =
  match sub (to_skeleton prog) p with Some s => Some (summarise alg s) | None => None end.
```
Proof idea: `liveness_sound` and `structured_liveness_sound` on the skeleton (with
`while_var_view_laws`, `while_skel_vars_laws` and `while_client_laws`), `match_state_initial` for
the matched initial states, `while_behaviour_transport`. Card: EX-4 for dense liveness and the
other ANA-1 instantiations above; ANA-2 for structured liveness and the ANA-2 instantiations.
The certificate statements instantiate `certificate_sound` and `certificate_complete`; the table
statement instantiates `region_table_agrees`. Card: ANA-2.
For lazy code motion, `lcm_insert_safe` and `lcm_delete_current` apply directly to
`while_genkill_view` and `lcm_extended_view`, with their stated premises; `while_lcm_accepts`
checks a concrete result. The generic theorem names are the public claims.

### Ssa

```coq
(** `ExamplesSsaTypingProofs.v`: typing and checker theorems use the semantics above. *)
(** Static types. A typed operand list never meets an ill-typed operator: for typed operands the
    result of an operator has the type of its signature, and an operator fails only by a division
    by zero or by an extension operator. *)
Theorem op_eval_typed (ext : nat -> list cval -> option cval) (P : program) (o : sop)
    (cs : list cval) (ps : list ty) (r : ty) :
  ext_respects ext P -> op_sig P o = Some (ps, r) -> map ty_of cs = ps -> Forall valid_cval cs ->
  (forall v, op_eval ext o cs = Some v -> ty_of v = r) /\
  (op_eval ext o cs = None -> (exists w, o = OBin w BDivU) \/ exists tag, o = OExt tag).
Theorem op_eval_valid (ext : nat -> list cval -> option cval) (P : program) (o : sop)
    (cs : list cval) (ps : list ty) (r : ty) (v : cval) :
  ext_respects ext P -> op_sig P o = Some (ps, r) -> map ty_of cs = ps ->
  Forall valid_cval cs -> op_eval ext o cs = Some v -> valid_cval v.
(** Typing is preserved: every frame of every reachable state holds a typed environment, and the
    operands of the next operation are bound and have the types of its signature. *)
Theorem typed_state_reachable (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (s : state) :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s ->
  forall fr, In fr (stack s) -> typed_env P (ffunc fr) (fenv fr).
Theorem typed_operands (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (s : state) (fr : sframe) (fd : fdef) (b : ssa_block) (x : vid) (o : sop) (args : list vid) :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s -> In fr (stack s) ->
  find_func P (ffunc fr) = Some fd -> find_block fd (flabel fr) = Some b ->
  nth_error (bbody b) (fpc fr) = Some (IOp x o args) ->
  exists cs ps r, Forall2 (fun y c => fenv fr y = Some c) args cs /\ op_sig P o = Some (ps, r) /\
    map ty_of cs = ps /\ Forall valid_cval cs.
Theorem allocation_size_in_range (ext : nat -> list cval -> option cval) (P : program)
    (lim : limits) (s : state) (fr : sframe) (fd : fdef) (b : ssa_block) (x n : vid) :
  wf_program ext P -> reachable_state (ssa_semantics ext P lim) s -> In fr (stack s) ->
  find_func P (ffunc fr) = Some fd -> find_block fd (flabel fr) = Some b ->
  nth_error (bbody b) (fpc fr) = Some (IAlloc x n) ->
  exists z, fenv fr n = Some (VInt W64 z) /\ (0 <= z < 2 ^ 64)%Z.
```
Proof idea: `op_eval_typed` by cases on the operator and the typed shape of its operands, with
`ext_respects` for an extension; `op_eval_valid` follows by the same cases and the word range of
each built-in result. `typed_state_reachable` follows by induction on the run, one case per rule
(a bound result has the static type and range of its definition by `op_eval_typed` and
`op_eval_valid`, a load by `load_ok` and the byte invariant, a
parameter by the typing of the arguments, a returned value by the function's result type);
`typed_operands` from dominance in `wf_program` (every path to the use defines the operand) and
the previous theorem. `allocation_size_in_range` uses the same dominance argument and typed
environment. Together they make an ill-typed or out-of-range operand unreachable. Card: EX-2.

```coq
(** The checker establishes well-formedness for a concrete program, and a program with no extension
    operator needs no hypothesis about `ext`. *)
Theorem wf_check_sound (ext : nat -> list cval -> option cval) (P : program) :
  ext_respects ext P -> wf_check P = true -> wf_program ext P.
Theorem ext_respects_nil (ext : nat -> list cval -> option cval) (P : program) :
  ext_sigs P = nil -> ext_respects ext P.
(** The rule `x * 1 -> x` is sound over 32-bit environments, with its side condition. *)
Theorem mul_one_rules_sound (ext : nat -> list cval -> option cval) :
  Forall (rule_sound (op_eval ext) ok_i32) mul_one_rules.
```
Proof idea: `wf_check_sound` unfolds the five checked conditions; the rule is `x * 1 = x` for a
word,
and the side condition makes every instance of `x` denote a word or fail where both sides fail.
Card: EX-2 (the checker) and ANA-6 (the rule).

```coq
(** The bridge: each integer operator's result is a Bits result; the toy's truth is nonzero. *)
Theorem ssa_bridge_laws (ext : nat -> list cval -> option cval) :
  op_bridge_laws ssa_bridge (op_eval ext) ssa_truth.
Theorem ssa_truth_nonzero (ext : nat -> list cval -> option cval) (P : program) (f : func)
    (w : iw) (z : Z) :
  truth (ssa_block_view ext P f) (VInt w z) = negb (Z.eqb z 0).
(** The SSA view satisfies its laws, and the variable and demand views theirs, for every
    well-formed function. *)
Theorem ssa_block_view_laws (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  ssa_view_laws (activation ext P f) (ssa_block_view ext P f).
Theorem ssa_var_view_laws (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  var_view_laws (activation ext P f) (activation_endings ext P f) (ssa_var_view ext P f).
Theorem ssa_demand_view_laws (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  demand_laws (activation ext P f) (activation_endings ext P f)
    (reachable_state (activation ext P f)) var_encoding bool_demand (ssa_demand_view ext P f).
```
Proof idea: the views are definitions by cases on the instruction kind. `guard_op_defined`: a block
computes its comparison from the values it holds, so at a taken edge the guard subject holds the
result of its operation on the current values of its arguments (by dominance of the arguments, which
the well-formedness gives, the arguments are bound and unchanged since the comparison ran);
`value_origin` by case analysis on the step: the binding is unchanged or comes from the rule that
bound it, including parallel parameter bindings and arbitrary call results; `ssa_truth_nonzero`
is `reflexivity` on the view.
The demand laws follow the same case analysis as the variable view. Exit demands retain all raw
exit operands, so Boolean demand agreement gives the equality required by `exits_determine`.
Prove `demand_vars_ok` for every node, including unreachable blocks: well-formedness puts each
listed operand in `values_of P f`. At reachable points, bound, valid, well-typed operands rule out
the shape and range failures of other `IOp`s; division and extension traps are covered by their
exit operands. Finality is determined by the point and activation never stops. Full-machine heap
traps and resource stops are separate from activation endings. Card: EX-5a.

```coq
(** Strictness: a value changes only where it is defined; guard subjects and operands are defined in
    blocks that dominate. *)
Theorem ssa_strict_laws (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  strict_ssa_laws (activation ext P f) (ssa_block_view ext P f).
(** Activation lifting: every frame of every state that a run of the full semantics reaches is a
    reachable state of its function's activation semantics, by a run whose trace is a subsequence of
    the full trace; the events of callees appear in the full trace between the frame's own events. *)
Theorem activation_lifting (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (s0 s : state) (tr : list event) (i : nat) :
  wf_program ext P -> initial (ssa_semantics ext P lim) s0 -> exec (ssa_semantics ext P lim) s0 tr s ->
  forall a f, frame_activation P s i = Some (a, f) ->
    exists a0 trf, initial (activation ext P f) a0 /\ exec (activation ext P f) a0 trf a /\
      subtrace trf tr.
```
Proof idea: strictness uses the well-formedness (definitions dominate uses, each value defined once,
so `redefine_in_stay` and `frame_in_stay` hold because only `IOp`, `ILoad` and `IAlloc` bind, at
their own block; `redefine_on_edge` and `frame_on_edge` hold because only a jump binds parameters,
of its target. `op_args_dominate` and
`guard_home` are dominance of operands and of guard subjects). The lifting is by induction on
`exec`, call by call and return by return: a step of the innermost frame is a step of its
activation (loads, allocations and call results are arbitrary there, and the callee's
steps happen above the frame and are not its steps); a call pushes a new frame whose activation
run starts at the callee's entry with the actual arguments, which is an initial activation state
since entry parameters are arbitrary values of their types; a return gives the caller's
continuation parameter the returned value, an arbitrary result for its activation; the trace of a
frame's run is the events of its own steps, which `subtrace` keeps in order inside the full trace
whose other events come from callee frames. Card: EX-5c (it needs EX-5a and VIEW-6).

```coq
(** The effects and calls views satisfy their laws on the full semantics. *)
Theorem ssa_effects_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P ->
  effects_laws (ssa_semantics ext P lim) (ssa_endings ext P lim) ssa_effects
    (ssa_effects_view ext P lim).
Theorem ssa_calls_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P ->
  calls_view_laws (ssa_semantics ext P lim) (ssa_calls ext P) (ssa_resolver P).
```
Proof idea: one case per instruction. `IFree` of a dead block traps; a load of a fragment as an
integer traps; an allocation reads the allocator state (`next_block`, the limit) and a store its
validity check, so `reads` is true for them and `reads_frame`, `trap_frame` and `stop_frame` hold
for
the others (an `IOp` or a branch depends on the environment only, a call's stop on the depth of
the stack, which `heap_agree` fixes); a `TCall` may trap on a signature mismatch, which `may_trap`
covers. `ssa_calls_laws` from the frame-chain invariant: a call pushes a frame of a function of the
resolver, a return pops it. Card: EX-5b.

```coq
(** The full-program graph view, and the memory, pointer, byte and zero-byte views, satisfy their
    laws. The pointer effects need only contain those of the program. *)
Theorem ssa_full_view_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P ->
  graph_view_laws (ssa_semantics ext P lim) (ssa_full_view ext P lim).
Theorem ssa_mem_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P -> mem_view_laws (ssa_semantics ext P lim) (ssa_mem_view ext P lim).
Theorem ssa_ptr_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (ops : list (ptr_op vid vid)) :
  wf_program ext P -> incl (ssa_ptr_ops P) ops ->
  ptr_view_laws (ssa_semantics ext P lim) (ssa_ptr_view ext P lim) ops.
Theorem ssa_bytes_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P -> bytes_laws (ssa_semantics ext P lim) (ssa_bytes_view ext P lim).
Theorem ssa_zero_laws (ext : nat -> list cval -> option cval) (P : program) (lim : limits) :
  wf_program ext P ->
  zero_laws (ssa_semantics ext P lim) (ssa_full_view ext P lim) (ssa_ptr_view ext P lim)
    (ssa_footprints P).
```
Proof idea: a block is never removed and its site never changes (`site_stable`); the pointer effect
of a step is read off the instruction (`PAlloc` for an allocation, `PCopy` for a pointer addition, a
call parameter or a returned pointer, `PLoad` and `PStore` for the pointer-typed loads and stores);
a byte changes only by a store, an allocation or a free, whose `writes_at` covers every site and
offset (`byte_frame`); `allocation_size_in_range` bounds each allocated block below 2^64; an
allocation zero-fills its block and a block that exists is
changed only by a store or a free, whose footprints cover it (`z_fresh`, `z_kept`; a freed block
reads as no byte). For `z_address`, a `VPtr` retains its block number and offset, and an existing
block has a site that `ssa_mem_laws` preserves, including after free. Card: EX-6 for
`ssa_full_view_laws` and `ssa_mem_laws`; ANA-9 for
`ssa_ptr_laws` and `ssa_zero_laws`; ANA-10a for `ssa_bytes_laws`.

```coq
(** Instantiation theorems: each catalogue analysis is sound on Ssa. Every line is the
    Analyses theorem applied to the view and the laws above, for every well-formed function. *)
Theorem ssa_sccp_sound (ext : nat -> list cval -> option cval) (P : program) (f : func)
    (sigma : sparse_unknown label ssa_edge vid -> lift_bot (tagged (flat Z))) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  post_solution (lift_bot_lattice (lat const_numeric))
    (sparse_system label_encoding var_encoding
       (numeric_problem const_numeric const_conc ssa_bridge TAny
         (ssa_block_view ext P f) (values_of P f) (fun _ => TAny))) sigma ->
  forall s x c, reachable_state (activation ext P f) s ->
    val (ssa_block_view ext P f) s x = Some c ->
    gamma (lift_bot_gamma (fact_conc (sparse_of_numeric const_numeric const_conc ssa_bridge TAny)))
      (sigma (UVal x)) c.
Theorem ssa_dead_value_removable (ext : nat -> list cval -> option cval) (P : program) (f : func)
    (d : finite_map var_encoding (dvars (ssa_demand_view ext P f)) bool) (x : vid) (s t : astate) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  demand_closed var_encoding bool_demand (ssa_demand_view ext P f) d ->
  dget var_encoding bool_lattice d x = false ->
  reachable_state (activation ext P f) s -> reachable_state (activation ext P f) t ->
  point (ssa_point_view ext P f) t = point (ssa_point_view ext P f) s ->
  (forall y, y <> x -> aenv s y = aenv t y) ->
  same_behaviour (activation ext P f) (activation_endings ext P f) s
    (activation ext P f) (activation_endings ext P f) t.
Theorem ssa_summary_sound (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (impure_local : func -> bool) (sigma : func -> bool) :
  wf_program ext P ->
  summary_laws (ssa_semantics ext P lim) (ssa_calls ext P)
    (purity_spec (ssa_calls ext P) impure_local) (purity_cover (ssa_effects_view ext P lim)) ->
  post_solution bool_lattice
    (summary_system (ssa_calls ext P) (ssa_resolver P) (purity_spec (ssa_calls ext P) impure_local))
    sigma ->
  forall s l s' g, reachable_state (ssa_semantics ext P lim) s ->
    step (ssa_semantics ext P lim) s l s' -> In g (active (ssa_calls ext P) s) -> sigma g = false ->
    l = nil /\ heap (ssa_effects_view ext P lim) s' = heap (ssa_effects_view ext P lim) s.
```
Proof idea: the first two instantiate `numeric_value_sound` (with `ssa_bridge_laws`,
`ssa_block_view_laws`, the constant domain's `numeric_laws`) and `dead_value_removable` /
`closed_demand_sound` with `ssa_demand_view_laws`; the third `purity_sound` with `ssa_calls_laws`
and
`ssa_effects_laws`, and the explicit `summary_laws` premise. Card: EX-5a for
`ssa_dead_value_removable`, ANA-3 for `ssa_sccp_sound`, and ANA-8 for `ssa_summary_sound`.

Other analyses use their named generic theorem with the applicable view and its laws. In
particular, `numeric_value_sound` takes a numeric domain, `ssa_bridge` and `ssa_block_view`;
`numbering_use_sound` and `loop_invariant_sound` take `ssa_block_view`, `ssa_strict_laws` and
their explicit numbering-specific observation or loop premises;
`optimise_sound` takes an operator evaluator and rewrite laws; `scev_sound` and `loop_trip_sound`
take the corresponding recurrence and loop premises. Call, pointer and byte analyses use
`ssa_calls_laws`, `ssa_ptr_laws` and `ssa_bytes_laws` where their generic theorem requires them.
The generic theorem's other premises remain explicit; these are not additional named theorems.

```coq
Section SsaAnalysisWrappers.
Context (ext : nat -> list cval -> option cval) (P : program) (lim : limits).
Local Notation m := (ssa_semantics ext P lim).
Local Notation cv := (ssa_calls ext P).
Local Notation resolve := (ssa_resolver P).
Local Notation pv := (ssa_ptr_view ext P lim).
Local Notation bv := (ssa_bytes_view ext P lim).

Theorem ssa_guard_chain_sound (f : func) (s : astate) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_state (activation ext P f) s ->
  Forall (cond_holds (ssa_block_view ext P f) s)
    (guard_chain (ssa_block_view ext P f) label_encoding
      (point (base (ssa_block_view ext P f)) s)).
(* guard_chain_holds, ssa_block_view_laws, ssa_strict_laws. Card: ANA-3. *)

Theorem ssa_recursion_sound (s : state) :
  wf_program ext P -> reachable_state m s -> ~ NoDup (active cv s) ->
  exists f, In f (active cv s) /\ recursive (call_graph cv resolve) f.
(* recursive_sound, ssa_calls_laws. Card: ANA-8. *)

Theorem ssa_unreachable_sound (f : func) :
  wf_program ext P -> ~ reachable (call_graph cv resolve) f ->
  forall s, reachable_state m s -> ~ In f (active cv s).
(* unreachable_never_runs, ssa_calls_laws. Card: ANA-8. *)

Theorem ssa_stack_demand_sound (fw : frame_weights func) (f : func) (d : nat) :
  wf_program ext P -> stack_demand cv (call_graph cv resolve) fw f = Some d ->
  forall s, reachable_state m s -> In f (active cv s) -> stack_above cv fw f s <= d.
(* stack_demand_sound, ssa_calls_laws. Card: ANA-8. *)

Theorem ssa_callee_leaf_sound (f : func) :
  wf_program ext P -> callee_leaf cv f = true ->
  forall s l s', reachable_state m s -> here cv s = f -> step m s l s' ->
    frames cv s' = frames cv s \/ exists g p, frames cv s = (g, p) :: frames cv s'.
(* callee_leaf_sound, ssa_calls_laws. Card: ANA-8. *)

Theorem ssa_andersen_sound (sigma : pts_key vid vid -> pts_set var_encoding (ssa_ptr_ops P)) :
  wf_program ext P ->
  post_solution (pts_lattice var_encoding (ssa_ptr_ops P))
    (andersen_system var_encoding var_encoding (ssa_ptr_ops P)) sigma ->
  forall s, reachable_state m s ->
    (forall x t, pts_of pv s x = Some t -> fmem var_encoding t (sigma (PVal x)) = true) /\
    (forall t0 t, heap_pts pv s t0 t -> fmem var_encoding t (sigma (PHeap t0)) = true).
(* andersen_sound, ssa_ptr_laws with incl_refl. Card: ANA-9. *)

Theorem ssa_steensgaard_sound :
  wf_program ext P ->
  forall s x y t, reachable_state m s -> pts_of pv s x = Some t -> pts_of pv s y = Some t ->
    may_alias (steensgaard var_encoding var_encoding (ssa_ptr_ops P)) x y.
(* steensgaard_sound, ssa_ptr_laws with incl_refl. Card: ANA-9. *)

Theorem ssa_escape_sound (sigma : pts_key vid vid -> pts_set var_encoding (ssa_ptr_ops P)) :
  wf_program ext P ->
  post_solution (pts_lattice var_encoding (ssa_ptr_ops P))
    (andersen_system var_encoding var_encoding (ssa_ptr_ops P)) sigma ->
  forall s x t t', reachable_state m s -> In (PEscape x) (pop pv s) ->
    pts_of pv s x = Some t ->
    FinSet.mem var_encoding t (escaped_sites var_encoding (ssa_ptr_ops P) sigma) = true /\
    (heap_pts pv s t t' ->
       FinSet.mem var_encoding t' (escaped_sites var_encoding (ssa_ptr_ops P) sigma) = true).
(* escaped_closed, ssa_ptr_laws with incl_refl. Card: ANA-9. *)

Theorem ssa_immutable_sound (ty : vid) (o : Z) :
  wf_program ext P -> (forall n, covered (writes_at bv n) ty o 1 -> False) ->
  forall s tr t l, reachable_state m s -> exec m s tr t -> bsite bv s l = Some ty ->
    byte bv t l o = byte bv s l o.
(* immutable_sound, ssa_bytes_laws. Card: ANA-10a. *)
End SsaAnalysisWrappers.
```

### Examples that compute

```coq
(** Pfenning's factorial with `z <- z + 1`, as an Ssa function: z is live in the loop and is
    nevertheless not needed. *)
Definition factorial_ssa : program.
(* z' = z + one is an OBin W32 BAdd on typed operands, which cannot trap, so it is not effectful under
   KeepTraps and `factorial_z_dead` holds for that policy.
   main (function 0, result TyI32) has the entry block 0 `e(x)` with p0 = 1 and z0 = 0, jumping to the
   loop block 1 `l(p, x1, z)`: p' = p * x1; one = 1; z' = z + one; x' = x1 - one; zero = 0;
   c = zero <u x'; br c, l(p', x', z'), exit(p'); and the block 2 `exit(r)`: output r; ret r. The
   values are numbered x = 0, p0 = 1, z0 = 2, p = 3, x1 = 4, z = 5, p' = 6, one = 7, z' = 8, x' = 9,
   zero = 10, c = 11, r = 12; there is no extension operator *)
Definition z_value : vid := 5.
Definition p_value : vid := 3.
Definition loop_header_point : label * nat := (1, 0).
Example factorial_wf : wf_check factorial_ssa = true.
Example factorial_z_live :
  fmem var_encoding z_value (liveness_at factorial_ssa loop_header_point) = true.
Example factorial_z_dead :
  dead_value var_encoding (ssa_demand_view (fun _ _ => None) factorial_ssa 0) z_value = true.
Example factorial_p_needed :
  dead_value var_encoding (ssa_demand_view (fun _ _ => None) factorial_ssa 0) p_value = false.
(* Card: EX-5a for factorial_ssa, its values, and the preceding Examples. *)
(** The same program in While: z is live and not needed at the loop head, and the erasure replaces
    its assignment by a skip. *)
Definition factorial_while : stmt.
(* p := 1; loop { p := p * x; z := z + 1; x := x - 1; if x >u 0 then continue 0 else break 0 };
   output p, with x >u 0 written as EBin LtU (EConst 0) (EVar x) *)
Definition factorial_while_dce : stmt.
(* factorial_while with `z := z + 1` replaced by SSkip *)
Definition z_var : var := 2.
Example while_z_live :
  fmem var_encoding z_var (while_live_at factorial_while loop_head) = true.
Example while_z_dead : while_dead_var factorial_while z_var = true.
Example while_dce_factorial :
  while_dce factorial_while word_stores (while_needed factorial_while) = factorial_while_dce.
(* Card: EX-4 for factorial_while, its variants, and the preceding While Examples. *)
```
Each `Example` above is a smoke check (a concrete computation by `vm_compute` on the engine result);
the theorems above are the claims. The following Examples are required: each is the acceptance
evidence of a checker or of a producer of the catalogue, a nontrivial input that the checker
accepts (and, where stated, a nearby one that it rejects).

```coq
(** Lazy code motion: on `if c then x := a + b else skip; y := a + b` the result that inserts
    `a + b` on the empty branch and deletes the recomputation in `y := a + b` passes `lcm_check`,
    with the solutions of the engine for the three systems. *)
Definition lcm_prog : stmt.
Definition lcm_result_ex : lcm_result (skel_edge atom expr) skel_point expr.
Example while_lcm_accepts :
  lcm_check expr_encoding (while_genkill_view lcm_prog word_stores)
    (lcm_avail lcm_prog) (lcm_busy lcm_prog) (lcm_avail2 lcm_prog lcm_result_ex) lcm_result_ex = true.
(* Card: EX-4 for lcm_prog, lcm_result_ex and while_lcm_accepts. *)
(** Numbering: on a function that computes `a + b` in a block and again in a block it dominates, the
    dominator numbering gives the two computations one leader, and the checker accepts it. *)
Definition gvn_prog : program.
(* main (function 0, result TyI32): block 0 `e(a, b)`: s1 = a + b; jump 1; block 1: s2 = a + b; output
   s2; ret s2; the values are a = 0, b = 1, s1 = 2, s2 = 3 *)
Definition gvn_first : vid := 2.
Definition gvn_second : vid := 3.
Definition gvn_problem : numbering_problem astate event label ssa_edge vid sop cval.
(* nsv = ssa_block_view (fun _ _ => None) gvn_prog 0; pure o = false exactly for OExt _;
   nvalues = values_of gvn_prog 0 *)
Definition gvn_binding_state : astate.
Definition gvn_binding_observation : numbering_observation unit astate label ssa_edge vid.
Theorem gvn_binding_observation_laws :
  numbering_observation_laws (activation (fun _ _ => None) gvn_prog 0)
    gvn_problem gvn_binding_observation.
(* The context has the concrete state just after s2 = a + b with both entry arguments zero.
   Its ready values are a, b, s1 and s2; the arguments have rank zero and the Ops rank one. *)
Theorem gvn_binding_witness :
  observation_state gvn_binding_observation tt = gvn_binding_state /\
  observation_ready gvn_binding_observation tt gvn_first /\
  observation_ready gvn_binding_observation tt gvn_second /\
  exists s l c d, reachable_state (activation (fun _ _ => None) gvn_prog 0) s /\
    step (activation (fun _ _ => None) gvn_prog 0) s l gvn_binding_state /\
    val (nsv gvn_problem) gvn_binding_state gvn_second = Some c /\
    val (nsv gvn_problem) s gvn_second <> Some c /\
    val (nsv gvn_problem) gvn_binding_state gvn_first = Some d.
Theorem gvn_binding_home_dominates :
  strictly_dominates (cfg (base (nsv gvn_problem)))
    (home (nsv gvn_problem) gvn_first) (home (nsv gvn_problem) gvn_second).
Theorem gvn_binding_equal :
  exists c d, val (nsv gvn_problem) gvn_binding_state gvn_second = Some c /\
    val (nsv gvn_problem) gvn_binding_state gvn_first = Some d /\ c = d.
(* gvn_binding_equal uses numbering_check_sound and the independent witness. *)
Definition gvn_use_prog : program.
(* The same computations, followed by a distinct block 2 that uses s2. *)
Definition gvn_use_problem : numbering_problem astate event label ssa_edge vid sop cval.
(* nsv is ssa_block_view (fun _ _ => None) gvn_use_prog 0, pure is false exactly for OExt _,
   and nvalues is values_of gvn_use_prog 0. *)
Definition gvn_use_state : astate.
Definition gvn_use_observation : numbering_observation unit astate label ssa_edge vid.
Theorem gvn_use_observation_laws :
  numbering_observation_laws (activation (fun _ _ => None) gvn_use_prog 0)
    gvn_use_problem gvn_use_observation.
Theorem gvn_use_witness :
  reachable_state (activation (fun _ _ => None) gvn_use_prog 0) gvn_use_state /\
  observation_state gvn_use_observation tt = gvn_use_state /\
  observation_ready gvn_use_observation tt gvn_first /\
  observation_ready gvn_use_observation tt gvn_second /\
  strictly_dominates (cfg (base (nsv gvn_use_problem)))
    (home (nsv gvn_use_problem) gvn_first) (point (base (nsv gvn_use_problem)) gvn_use_state) /\
  strictly_dominates (cfg (base (nsv gvn_use_problem)))
    (home (nsv gvn_use_problem) gvn_second) (point (base (nsv gvn_use_problem)) gvn_use_state) /\
  (exists c, val (nsv gvn_use_problem) gvn_use_state gvn_first = Some c) /\
  (exists d, val (nsv gvn_use_problem) gvn_use_state gvn_second = Some d).
Theorem gvn_use_equal :
  exists c, val (nsv gvn_use_problem) gvn_use_state gvn_first = Some c /\
    val (nsv gvn_use_problem) gvn_use_state gvn_second = Some c.
(* ANA-5 proves the independent witness and applies numbering_use_sound for gvn_use_equal. *)
Definition gvn_phi_prog : program.
Definition gvn_phi_problem : numbering_problem astate event label ssa_edge vid sop cval.
Definition gvn_phi_left : vid.
Definition gvn_phi_right : vid.
Definition gvn_phi_observation : numbering_observation nat astate label ssa_edge vid.
(* The entry edge supplies the same seed to both parameters of block 1. The back edge supplies
   those two parameters themselves. A separate condition enters the loop and then exits to a
   distinct dominated use block after a back edge. The adapter uses this program's block view,
   its values_of inventory and the same pure predicate as gvn_problem. *)
Theorem gvn_phi_observation_laws :
  numbering_observation_laws (activation (fun _ _ => None) gvn_phi_prog 0)
    gvn_phi_problem gvn_phi_observation.
Theorem gvn_phi_checked : numbering_check label_encoding var_encoding sop_encoding
  gvn_phi_problem
  (optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem) = true.
Theorem gvn_phi_witness : exists h h' h'' e entry c d,
  def (nsv gvn_phi_problem) gvn_phi_left = Param 1 0 /\
  def (nsv gvn_phi_problem) gvn_phi_right = Param 1 1 /\
  observation_previous gvn_phi_observation h 1 = Some (e, h') /\
  observation_previous gvn_phi_observation h' 1 = Some (entry, h'') /\ e <> entry /\
  (exists seed, nth_error (edge_args (nsv gvn_phi_problem) entry) 0 = Some seed /\
    nth_error (edge_args (nsv gvn_phi_problem) entry) 1 = Some seed) /\
  nth_error (edge_args (nsv gvn_phi_problem) e) 0 = Some gvn_phi_left /\
  nth_error (edge_args (nsv gvn_phi_problem) e) 1 = Some gvn_phi_right /\
  observation_ready gvn_phi_observation h gvn_phi_left /\
  observation_ready gvn_phi_observation h gvn_phi_right /\
  observation_ready gvn_phi_observation h' gvn_phi_left /\
  observation_ready gvn_phi_observation h' gvn_phi_right /\
  observation_rank gvn_phi_observation h' gvn_phi_left <
    observation_rank gvn_phi_observation h gvn_phi_left /\
  observation_rank gvn_phi_observation h' gvn_phi_right <
    observation_rank gvn_phi_observation h gvn_phi_right /\
  reachable_state (activation (fun _ _ => None) gvn_phi_prog 0)
    (observation_state gvn_phi_observation h) /\
  strictly_dominates (cfg (base (nsv gvn_phi_problem))) 1
    (point (base (nsv gvn_phi_problem)) (observation_state gvn_phi_observation h)) /\
  val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_left = Some c /\
  val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_right = Some d /\
  optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem gvn_phi_left =
    optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem gvn_phi_right.
Theorem gvn_phi_equal : forall h c d,
  observation_ready gvn_phi_observation h gvn_phi_left ->
  observation_ready gvn_phi_observation h gvn_phi_right ->
  reachable_state (activation (fun _ _ => None) gvn_phi_prog 0)
    (observation_state gvn_phi_observation h) ->
  strictly_dominates (cfg (base (nsv gvn_phi_problem))) 1
    (point (base (nsv gvn_phi_problem)) (observation_state gvn_phi_observation h)) ->
  val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_left = Some c ->
  val (nsv gvn_phi_problem) (observation_state gvn_phi_observation h) gvn_phi_right = Some d ->
  c = d.
(* ANA-5 proves the independent value witnesses, actual incoming-edge history and checker
   acceptance, then derives equality using the generic theorem. *)
Definition gvn_loop_prog : program.
Definition gvn_loop_problem : numbering_problem astate event label ssa_edge vid sop cval.
Definition gvn_loop_info : loop_info label.
Definition gvn_loop_value : vid.
(* nsv is ssa_block_view (fun _ _ => None) gvn_loop_prog 0, pure is false exactly for OExt _,
   and nvalues is values_of gvn_loop_prog 0. The loop value is its inside-body pure addition,
   not an outside-home value; its arguments are the independently bound entry parameters. *)
Theorem gvn_loop_laws :
  numbering_loop_laws (activation (fun _ _ => None) gvn_loop_prog 0) gvn_loop_problem.
Theorem gvn_loop_wf : loop_info_wf (cfg (base (nsv gvn_loop_problem))) gvn_loop_info.
Theorem gvn_loop_invariant : invariant_in gvn_loop_problem gvn_loop_info gvn_loop_value = true.
Theorem gvn_loop_stability :
  loop_operands_stable (activation (fun _ _ => None) gvn_loop_prog 0)
    gvn_loop_problem gvn_loop_info gvn_loop_value.
Theorem gvn_loop_run : exists s tr t,
  reachable_state (activation (fun _ _ => None) gvn_loop_prog 0) s /\
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) s tr t /\
  s <> t.
Theorem gvn_loop_recomputed : exists a b c d tr o args,
  reachable_state (activation (fun _ _ => None) gvn_loop_prog 0) a /\
  def (nsv gvn_loop_problem) gvn_loop_value = Op o args /\
  at_instr gvn_loop_prog (activation_frame 0 a) (IOp gvn_loop_value o args) /\
  step (activation (fun _ _ => None) gvn_loop_prog 0) a [] b /\
  val (nsv gvn_loop_problem) a gvn_loop_value <>
    val (nsv gvn_loop_problem) b gvn_loop_value /\
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) b tr c /\
  at_instr gvn_loop_prog (activation_frame 0 c) (IOp gvn_loop_value o args) /\
  step (activation (fun _ _ => None) gvn_loop_prog 0) c [] d /\
  body gvn_loop_info (point (base (nsv gvn_loop_problem)) a) = true /\
  body gvn_loop_info (point (base (nsv gvn_loop_problem)) d) = true /\
  val (nsv gvn_loop_problem) c gvn_loop_value = val (nsv gvn_loop_problem) d gvn_loop_value.
Theorem gvn_loop_sound : forall s tr1 u1 tr2 u2 tr3 u3,
  reachable_state (activation (fun _ _ => None) gvn_loop_prog 0) s ->
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) s tr1 u1 ->
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) u1 tr2 u2 ->
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) u2 tr3 u3 ->
  val (nsv gvn_loop_problem) u1 gvn_loop_value <>
    val (nsv gvn_loop_problem) u2 gvn_loop_value ->
  val (nsv gvn_loop_problem) u2 gvn_loop_value =
    val (nsv gvn_loop_problem) u3 gvn_loop_value.
(* A loop recomputes a pure addition of entry arguments on each iteration; those arguments are
   stable throughout the loop. ANA-5 proves its numbering_loop_laws, loop_info_wf,
   invariant_in and loop_operands_stable premises, proves a reachable nonempty loop run, and
   applies loop_invariant_sound to that actual Ssa client as gvn_loop_sound. *)
Example gvn_merges :
  dominator_numbering label_encoding var_encoding sop_encoding gvn_problem gvn_second =
    dominator_numbering label_encoding var_encoding sop_encoding gvn_problem gvn_first /\
  numbering_check label_encoding var_encoding sop_encoding gvn_problem
    (dominator_numbering label_encoding var_encoding sop_encoding gvn_problem) = true.
(* Card: ANA-5 for gvn_prog, its values, gvn_problem and gvn_merges. *)
(** E-graphs: with the rule `x * 1 -> x` for 32-bit integers, the pipeline returns the term `x`, with
    a checked explanation, for `x * 1`, and the term it returns is strictly cheaper. *)
Example egraph_optimise_accepts :
  optimise sop_encoding mul_one_rules unit_cost 100%positive mul_one_term = Some (TVar 0).
(* Card: ANA-6. *)
(** Scalar evolution: the counted loop `for i = 0; i < n; i++` over 32-bit unsigned integers, with
    n = 5, has the recurrence {0,+,1}, the trip count 5 and passes the no-wrap check. *)
Definition count_up : program.
(* main (function 0, result TyI32): block 0 `e(n)`: i0 = 0; one = 1; jump l(i0); block 1 `l(i)`:
   c = i <u n; br c, b(), x(); block 2 `b()`: i' = i + one; jump l(i'); block 3 `x()`: ret i; the
   values are n = 0, i0 = 1, one = 2, i = 3, c = 4, i' = 5; the loop has the header 1, the body
   {1, 2}, the entry edge from block 0 and the back edge from block 2, and tests i against n *)
Definition count_up_n : vid := 0.
Definition count_up_chrec : chrec vid := CRec (CInv (IVar 1)) (CInv (IVar 2)).   (* {i0, +, one} *)
Definition count_up_inv : vid -> Z.
(* the entry state's values of the invariants: i0 = 0, one = 1, n = 5, every other value 0 *)
Example scev_count_up_trip :
  trip_count count_up_inv 32%positive Unsigned CmpLt count_up_chrec (IVar count_up_n) = Some 5%N /\
  nowrap_check 32%positive Unsigned count_up_inv count_up_chrec (IVar count_up_n) 5%N = true.
(* Card: ANA-7 for count_up, its values and scev_count_up_trip. *)
(** MemorySSA: on a chain of three nodes that stores to site A, stores to site B and loads from site
    A, the load's definition is the first store and the checker accepts; when the second store
    writes site A as well, the checker rejects. *)
Definition chain_graph : Graph.t nat nat.
(* entries [0]; nodes [0; 1; 2]; the edge e leaves node e for node e + 1 (edges 0 and 1); no edge
   leaves node 2 *)
Definition chain_writes : nat -> list (footprint nat).
(* node 0: [Footprint 0 0 8] (a store to site A = 0); node 1: [Footprint 1 0 8] (site B = 1);
   node 2: nil *)
Definition chain_writes_clobber : nat -> list (footprint nat).
(* as chain_writes, but node 1 writes [Footprint 0 4 8], which overlaps the load *)
Definition chain_reads : nat -> list (footprint nat).     (* node 2: [Footprint 0 0 8]; else nil *)
Definition chain_ssa : memory_ssa nat nat.                 (* the load at node 2 has def MDef 0 0 *)
Example memoryssa_accepts :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0
    chain_graph chain_writes chain_reads chain_ssa = true.
Example memoryssa_rejects :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0
    chain_graph chain_writes_clobber chain_reads chain_ssa = false.
(* Card: ANA-10e for chain_graph, the chain footprints, chain_ssa and the two Examples. *)
```

## Algorithms and references

- **Structured toy and its translation.** `While`'s `Block` around `Loop` encoding of `break` and
  `continue` follows WebAssembly's `block` and `loop`; its continuation machine is the standard
  small-step presentation (as in CompCert's Cminor), written independently of the library.
- **Operator bridge.** SMT-LIB QF_BV total semantics (`Bits`); the toy's traps stay on its side
  of the equation: `BDivU` traps on zero before the bridge applies, and a constant is wrapped to its
  width before it is a value.
- **SSA with block parameters and static types.** Appel, "SSA is functional programming" (1998);
  the strictness laws follow Cytron et al. (1991): definitions dominate uses. Every value has one
  type fixed by its definition, so that an operator is applied only to operands of its signature;
  an indirect call names the signature it expects, as WebAssembly's `call_indirect` does.
- **Memory.** Byte values with pointer fragments as in CompCert's memory model (design only; the
  development shares no code or definitions with it).
- **Activation lifting.** The intraprocedural view of one function is lifted to the frames of the
  whole program by a simulation of each frame by its activation, as in context-insensitive
  interprocedural analyses; traces are lifted by keeping each frame's own events as a subsequence.
- **Dead-code erasure.** A lock-step simulation between a program and its transform, instantiating
  Views' two-program agreement theorem; the factorial example with `z <- z + 1` is Pfenning,
  Platzer and Simmons, 15-411 Lecture 7 (2015).

## Open questions

1. **Activation semantics.** The SSA view is stated for the activation semantics and lifted to
   frames by `activation_lifting`, which carries reachability and traces. No agreement between
   states of the full semantics is defined, so no behaviour result about activations is claimed to
   transfer; neededness across calls is not covered.
2. **Bits names.** `Bits.eval` and `Bits.expr` are from the Bits expression module; the operator
   constructors behind `bin_bits`, `un_bits` and `ssa_bridge` are those of BIT-1 and BIT-2.
3. **Skeleton match.** `match_state` is specified in prose; its exact form is part of EX-4. The
   skeleton's `stmt` is written `Skeleton.stmt` where While's own `stmt` is in scope, and the
   constants domain is `const_numeric`, the `tagged_domain` of DOM-1's `const_domain`.
4. **Instantiations.** Named specializations are stated above. Other analyses use their generic
   theorem with the relevant toy view, its laws, and the theorem's remaining premises.
5. **Executable engines.** The computed `Example`s need executable results from FIX-2a (a fuel that
   is a closed term, with the proof erased) and the wrappers of the last section of the
   definitions.
6. **Floats.** `Float` adds float values and operators to `Ssa` in a separate theory through
   `ext`; the toys here have none. A program that uses an extension operator declares its signature
   in `ext_sigs`, and `wf_program` then requires that `ext` respects the declaration.
7. **Allocation sizes.** `IAlloc` takes its size as an operand, so a footprint for an allocation
   site is the coarse range `[0, 2^64)` unless an analysis refines it; the memory views are
   sound for every program and as precise as their footprints.

## Requests to other documents

The EX-5b effect and call laws concern the specified Ssa semantics under `wf_program ext P`.
Its resolver covers modeled calls, and `ext` is the extension in that semantics. These proofs do
not cover a host that adds unmodeled callbacks or heap effects. Such a host needs a new view and
local step and effect laws, with unknown effects handled conservatively.

1. **float.md** (FLT-1): `float_ext nm32 nm64` is the `ext` of every Ssa definition, and `Examples`
   now types the extension operators: a program that uses a float tag lists
   `(tag, (argument types, result type))` in `ext_sigs`, with `TyF32` or `TyF64` operands and the
   same result for arithmetic and `TyI32` for a comparison. Float needs a theorem
   `float_ext_respects (P : program) : ext_sigs P = float_ext_sigs -> ext_respects (float_ext nm32
   nm64) P`,
   with `float_ext_sigs : list (nat * (list ty * ty))` the signatures of its five tags per width, so
   that `wf_program (float_ext nm32 nm64) P` can be established. Why: typing makes ill-typed
   `op_eval` unreachable, and a float operation must not be applied to an integer.
2. **float.md** (FLT-1): `ssa_truth_nonzero` is provided by EX-5a with the statement that float.md
   gives; the remaining Ssa names that float.md uses (`program`, `func`, `label`, `vid`, `astate`,
   `event`, `sop`, `cval`, `OExt`, `VF32`, `VF64`, `activation`, `activation_endings`,
   `ssa_block_view`, `ssa_demand_view`, `ssa_edge`, `values_of`, `wf_program`, `var_encoding`) are
   unchanged in meaning, and each takes `ext` first.
## Refined Ssa point graph and activation (EX-5a)

```coq
(* ExamplesSsaActivation.v; each constructor has its own finite encoding. *)
Inductive ssa_refined_value : Type :=
| SsaSourceValue (x : vid)
| SsaCallResult (l : label).

Inductive ssa_refined_point : Type :=
| SsaBeforeParams (l : label)
| SsaExecPoint (l : label) (pc : nat)
| SsaCallReady (l : label)
| SsaAfterReturn (l : label)
| SsaDeadPoint (l : label).

Inductive ssa_refined_edge : Type :=
| SsaBindParams (l : label)
| SsaInstruction (l : label) (pc : nat)
| SsaMakeCallResult (l : label)
| SsaTransfer (src dst : label) (slot : nat)
| SsaReturn (l : label).

Definition ssa_refined_value_encoding : encoding ssa_refined_value.
Definition ssa_refined_point_encoding : encoding ssa_refined_point.
Definition ssa_refined_edge_encoding : encoding ssa_refined_edge.

(* ExamplesSsaViews.v imports ExamplesSsaActivation.v. *)
(* This is an analysis carrier. It is not a semantic view of activation. *)
Definition ssa_refined_var_view (P : program) (f : func) :
  var_view ssa_refined_point event ssa_refined_point ssa_refined_edge
    ssa_refined_value unit.
Definition ssa_refined_points (P : program) (f : func) :
  ssa_points label ssa_edge ssa_refined_point ssa_refined_edge ssa_refined_value.
Definition ssa_refine_point (P : program) (f : func) (n : label * nat) :
  ssa_refined_point.

Theorem ssa_refined_point_model (P : program) (f : func) :
  point_model (ssa_refined_points P f) = var_point_uses (ssa_refined_var_view P f).

Theorem ssa_refined_point_laws (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  ssa_point_laws (ssa_refined_points P f).

Theorem ssa_refined_liveness (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  forall n x, In n (Graph.nodes (cfg (ssa_point_view ext P f))) ->
  (syntactic_live (var_point_uses (ssa_var_view ext P f)) x n <->
   syntactic_live (point_model (ssa_refined_points P f)) (SsaSourceValue x)
     (ssa_refine_point P f n)).
```

Build one shared `point_uses` expression and use it both for the point model and the analysis
carrier, so the record equality is constructive, with no functional extensionality. The carrier
has `point := fun n => n`, `taken` and `stays` constantly false and `vget` constantly `tt`.
It exists to instantiate syntactic ANA-1, ANA-11, ANA-12 and ANA-13 statements; no
`var_view_laws` or semantic soundness is claimed for it. Keep the existing raw semantic variable
view and its actual `var_view_laws`. This distinction is necessary: at a join, two reachable
states can have the same source variables but different selected incoming pending lists; a
deterministic parameter edge can therefore write different values despite equality of its
syntactic use list. Neither inventing hidden equality nor adding a non-dominating phi input as a
use establishes `uses_determine`.

The refined block graph is exactly `cfg (base (ssa_block_view ext P f))`; graph construction
does not depend on `ext`. Include all original blocks, even unreachable ones. The graph entry
is `SsaBeforeParams` of the function entry. Within each block place `SsaBeforeParams l`, then
`SsaExecPoint l 0` through the terminator point, with the return endpoint after a return and a
`SsaCallReady l` after a call. The first internal edge `SsaBindParams l` defines exactly
`map SsaSourceValue` of the block parameters and has no syntactic uses. Entry arguments are
external concrete initial values, not SSA variables or invented uses; the first parameter edge
defines them before the first instruction reads them. Every ordinary instruction edge reads and
defines the injected source variables in the original syntax; retain original operand order and
duplicates. Return and trap exit uses match the raw view.

Each jump, branch or switch `SsaTransfer src dst slot` preserves its corresponding
`SsaEdge src dst slot` block-edge occurrence, including
parallel slots, reads its actual selected arguments and guard operands before any target
parameter definition, and defines no source value. Its `block_edge_args` is the injected
selected argument list in the original order. A call's internal `SsaMakeCallResult l` reads the
call operands and defines only `SsaCallResult l`; its following `SsaTransfer` reads that value,
and its block edge has `block_edge_args = [SsaCallResult l]`. The continuation parameter is
defined on its common parameter edge. Thus the refined arity is one without asserting equality
with the old empty call `edge_args`. Distinct constructors give a fresh value per call site and
prevent aliasing source values. Empty parameter edges remain present; no source block or entry
restriction is added.

The point definition of a parameter is `SsaBeforeParams` of its block, of an instruction result
the source of its instruction edge, and of a call result `SsaExecPoint l` at its terminator;
unmentioned values have `None`. Define the function from one prepared definition index, not by
scanning definitions at each query. `ssa_refine_point` maps a raw `(l, pc)` to
`SsaExecPoint l pc` up to the terminator and maps a raw return endpoint to `SsaAfterReturn l`.
The raw graph also lists a one-past-terminator node for non-returning terminators; these are
isolated dead endpoints, mapped to `SsaDeadPoint l`, which is not in the refined graph and has
empty outgoing and exit-use lists. This does not discard an unreachable source block. State the
mapping for all raw graph nodes, including unreachable components. The liveness theorem
is an equivalence for injected source variables at these stable points, not an equation between
sets over different carriers and not a claim about intermediate points. Prove it by mapping
finite use-before-kill paths in both directions. At a raw call edge the new temporary is defined
and used strictly between stable points; it cannot become a source-variable use or kill.

### Refined activation correspondence

```coq
(* ExamplesSsaActivation.v owns state, activation and macro definitions. ExamplesSsaViews.v
   imports it and owns both variable views and their graph agreement. *)
Record ssa_refined_state : Type := SsaRefinedState {
  srs_point : ssa_refined_point;
  srs_env : vid -> option cval;
  srs_call_results : label -> option cval;
  srs_pending : nat -> option cval
}.
Inductive ssa_refined_semantic_var : Type :=
| SsaSourceVar (x : vid)
| SsaCallVar (l : label)
| SsaPendingVar (i : nat).
Definition ssa_refined_semantic_var_encoding : encoding ssa_refined_semantic_var.
Definition ssa_refined_activation (ext : nat -> list cval -> option cval)
    (P : program) (f : func) : semantics ssa_refined_state event.
Definition ssa_refined_endings (ext : nat -> list cval -> option cval)
    (P : program) (f : func) : endings ssa_refined_state.
(* ExamplesSsaViews.v owns this view, graph agreement and semantic view laws. *)
Definition ssa_refined_semantic_var_view (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  var_view ssa_refined_state event ssa_refined_point ssa_refined_edge
    ssa_refined_semantic_var (option cval).
Theorem ssa_refined_graph_agrees (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  cfg (gview (ssa_refined_semantic_var_view ext P f)) =
    live_graph (point_model (ssa_refined_points P f)).
(* ExamplesSsaActivation.v owns the stable relation and macro correspondence. *)
Definition ssa_refined_stable (r : ssa_refined_state) : Prop.
Definition ssa_refined_rel (P : program) (f : func) (a : astate)
    (r : ssa_refined_state) : Prop.

(* ExamplesSsaViews.v. *)
Theorem ssa_refined_semantic_var_laws (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  var_view_laws (ssa_refined_activation ext P f) (ssa_refined_endings ext P f)
    (ssa_refined_semantic_var_view ext P f).

(* ExamplesSsaActivation.v. A macro has one or more steps with no stable intermediate state. *)
Inductive ssa_refined_macro (m : semantics ssa_refined_state event) :
    ssa_refined_state -> list event -> ssa_refined_state -> Prop :=
| SsaMacroLast : forall r tr t,
    step m r tr t -> ssa_refined_stable t -> ssa_refined_macro m r tr t
| SsaMacroMore : forall r tr1 u tr2 t,
    step m r tr1 u -> ~ ssa_refined_stable u -> ssa_refined_macro m u tr2 t ->
    ssa_refined_macro m r (tr1 ++ tr2) t.

Theorem ssa_refined_initial (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  (forall a, initial (activation ext P f) a ->
    exists r r', initial (ssa_refined_activation ext P f) r /\
      exec (ssa_refined_activation ext P f) r [] r' /\ ssa_refined_rel P f a r') /\
  (forall r, initial (ssa_refined_activation ext P f) r ->
    exists a r', initial (activation ext P f) a /\
      exec (ssa_refined_activation ext P f) r [] r' /\ ssa_refined_rel P f a r').

Theorem ssa_refined_step_correspondence (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  forall a r, reachable_state (activation ext P f) a ->
    reachable_state (ssa_refined_activation ext P f) r -> ssa_refined_rel P f a r ->
    (forall tr a', step (activation ext P f) a tr a' ->
      exists r', ssa_refined_macro (ssa_refined_activation ext P f) r tr r' /\
        ssa_refined_rel P f a' r') /\
    (forall tr r', ssa_refined_macro (ssa_refined_activation ext P f) r tr r' ->
      exists a', step (activation ext P f) a tr a' /\ ssa_refined_rel P f a' r').

Theorem ssa_refined_behaviour (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  forall a r, reachable_state (activation ext P f) a ->
    reachable_state (ssa_refined_activation ext P f) r -> ssa_refined_rel P f a r ->
  same_behaviour (activation ext P f) (activation_endings ext P f) a
    (ssa_refined_activation ext P f) (ssa_refined_endings ext P f) r.
```

The refined initial state is before entry binding and stores exactly the arbitrary valid typed
entry arguments in pending slots 0 through arity minus one. A transfer evaluates the chosen
argument list in the old environment once and writes these slots simultaneously;
`SsaBindParams` reads them and performs one parallel bind. Never evaluate sequentially in the
updated environment. Slots persist after binding; an edge overwrites exactly the slots for its
target arity and leaves every other slot unchanged. Slots beyond the largest block-parameter arity
are never used or defined. Initial unused slots and call-result slots are `None`. On calls, evaluate
operands and choose the same arbitrary typed result as activation on `SsaMakeCallResult`, then
pass the stored result on the projected edge. Preserve the original event on the corresponding
macro, with all administrative steps silent. The point relation identifies stable execution or
return points with raw `(alabel, apc)` and requires pointwise equality of source environments;
it does not require equality of ghost call-result slots. Endings at stable points agree, including
traps, final, stop and stuck; intermediate states cannot be endings or stuck. Prove a fixed bound
of at most two consecutive administrative steps, including initial binding, so no infinite silent
administrative run is introduced. `same_behaviour` covers finite event prefixes, all four ending
tags and diverging prefixes. No entry-result or incoming-argument choice is left uncorrelated.
In particular, when a call emits an event before its administrative continuation edges, the
reverse finite-prefix direction matches that intermediate prefix by the raw call step.

The semantic variable view uses the same actual refined graph and classifies each step by its
edge. Its `vget` returns `srs_env r x` for `SsaSourceVar x`, `srs_call_results r l` for
`SsaCallVar l`, and `srs_pending r i` for `SsaPendingVar i`, including unused slots. For every
transfer into arity `k`, its defs are precisely `SsaPendingVar 0` through `k-1`, and its uses
are the selected source arguments and guards, or the call-result slot for a call continuation.
The parameter edge uses those `k` pending variables and defines the `k` source parameters. The
call-result edge defines its `SsaCallVar`; other instruction uses, definitions and exit uses
are the source variables read or written by the actual operation. Include guard, trap, return
and indirect-call operands. Event and edge selection is determined by the listed uses; for
arbitrary loads, allocations and call results, choose the same result as the witnessed step.
Prove `defs_frame`, same-label `uses_determine` and `exits_determine` by cases, including the
zero-arity and unused-slot cases. This semantic view has a different variable universe and
different edge uses/defs from the strict syntactic point model: pending slots can be defined on
several incoming edges, and are not strict SSA values. It supports semantic dense analyses via
its own laws. It is not the argument to `ssa_live_query_dense`; the exact source-variable bridge
above connects the latter to the original semantic view. No equality of the two variable-view
records or liveness sets is asserted.

### Refined reachable strictness (EX-5c)

```coq
Theorem ssa_refined_reachable_strict (ext : nat -> list cval -> option cval)
    (P : program) (f : func) :
  wf_program ext P -> In f (map fst (funcs P)) ->
  reachable_point_ssa (ssa_refined_points P f).
```

Prove strict point dominance from the actual EX-2 availability certificate and unique source
definitions. Include entry parameter use at the first instruction, same-block instruction order,
phi reads at the predecessor's projected edge, self-loops, parallel edges and the call-result
definition before its use. The proof applies to reachable points only and does not assume every
block is reachable or the entry has no incoming edges. Preserve the existing block-view origin
and strictness proofs and activation lifting.
