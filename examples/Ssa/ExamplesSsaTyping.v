(** * Static typing and SSA availability certificates

    Local signatures fix types independently of evaluation. Availability certificates check
    that every path from the entry defines each operand before its use.
    For example, a loop parameter is available at the start of every visit to its block.
    Builds on: ExamplesSsaSyntax and Collections maps. *)

From Stdlib Require Import List ZArith Bool NArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax.
Import List.ListNotations.

(** Integer widths have distinct static types. *)
Definition iw_ty (w : iw) : ty :=
  match w with
  | W32 => TyI32
  | W64 => TyI64
  end.

Definition bin_result (w : iw) (o : bop) : ty :=
  match o with
  | BEq | BLtU | BLtS => TyI32
  | _ => iw_ty w
  end.

(** An operation's signature depends only on syntax and declared extension signatures. *)
Definition op_sig (P : program) : sop -> option (list ty * ty) :=
  let extensions := first_index (ext_sigs P) in
  fun o =>
  match o with
  | OConst c => Some ([], ty_of c)
  | OBin w o => Some ([iw_ty w; iw_ty w], bin_result w o)
  | OZext => Some ([TyI32], TyI64)
  | OTrunc => Some ([TyI64], TyI32)
  | OPtrAdd => Some ([TyPtr; TyI64], TyPtr)
  | OExt tag => Map.get nat_encoding tag extensions
  end.

(** Only integers and complete data pointers can be loaded. *)
Definition load_ok (t : ty) (sz : msize) : bool :=
  match t, sz with
  | TyI32, M8 => false
  | TyI32, _ => true
  | TyI64, _ => true
  | TyPtr, M8 => true
  | _, _ => false
  end.

Definition instr_uses (i : instr) : list vid :=
  match i with
  | IOp _ _ args => args
  | IAlloc _ n => [n]
  | IFree p => [p]
  | ILoad _ _ _ p => [p]
  | IStore _ p v => [p; v]
  | IOutput v => [v]
  end.

Definition instr_def (i : instr) : list vid :=
  match i with
  | IOp x _ _ | IAlloc x _ | ILoad x _ _ _ => [x]
  | _ => []
  end.

Definition instr_binding_with (signature : sop -> option (list ty * ty))
    : instr -> list (vid * ty) :=
  fun i =>
  match i with
  | IOp x o _ =>
    match signature o with
    | Some (_, r) => [(x, r)]
    | None => []
    end
  | IAlloc x _ => [(x, TyPtr)]
  | ILoad x t _ _ => [(x, t)]
  | _ => []
  end.

Definition instr_binding (P : program) : instr -> list (vid * ty) :=
  instr_binding_with (op_sig P).

Definition block_bindings (P : program) (b : ssa_block) : list (vid * ty) :=
  bparams b ++ flat_map (instr_binding P) (bbody b).

Definition function_bindings_with (signature : sop -> option (list ty * ty)) (fd : fdef)
    : list (vid * ty) :=
  let binding := instr_binding_with signature in
  flat_map (fun lb => bparams (snd lb) ++ flat_map binding (bbody (snd lb))) (blocks fd).

Definition function_bindings (P : program) (fd : fdef) : list (vid * ty) :=
  function_bindings_with (op_sig P) fd.

(** Static lookup is indexed once over the definitions of the selected function. *)
Definition static_ty (P : program) (f : func) : vid -> option ty :=
  match find_func P f with
  | None => fun _ => None
  | Some fd =>
    let index := first_index (function_bindings P fd) in
    fun x => Map.get nat_encoding x index
  end.

(** Extensions preserve both the declared types and integer word validity. *)
Definition ext_respects (ext : nat -> list cval -> option cval) (P : program) : Prop :=
  forall tag ps r cs v, In (tag, (ps, r)) (ext_sigs P) -> map ty_of cs = ps ->
    Forall valid_cval cs -> ext tag cs = Some v -> ty_of v = r /\ valid_cval v.

(** Every present environment binding agrees with the unique static definition. *)
Definition typed_env (P : program) (f : func) (env : vid -> option cval) : Prop :=
  forall x c, env x = Some c -> static_ty P f x = Some (ty_of c) /\ valid_cval c.

Fixpoint types_of (T : vid -> option ty) (xs : list vid) : option (list ty) :=
  match xs with
  | [] => Some []
  | x :: xs =>
    match T x, types_of T xs with
    | Some t, Some ts => Some (t :: ts)
    | _, _ => None
    end
  end.

Definition result_has_type (T : vid -> option ty) (dst : option (vid * ty)) : Prop :=
  match dst with
  | None => True
  | Some (x, t) => T x = Some t
  end.

Definition result_type_check (T : vid -> option ty) (dst : option (vid * ty)) : bool :=
  match dst with
  | None => true
  | Some (x, t) => if option_eq_dec ty_eq_dec (T x) (Some t) then true else false
  end.

Definition store_type_ok (t : ty) (sz : msize) : bool :=
  match t, sz with
  | TyI32, _ | TyI64, _ => true
  | TyPtr, M8 | TyFun, M8 => true
  | _, _ => false
  end.

Definition instr_sig_with (signature : sop -> option (list ty * ty)) (T : vid -> option ty)
    : instr -> option (list ty * option (vid * ty)) :=
  fun i =>
  match i with
  | IOp x o _ => option_map (fun pr => (fst pr, Some (x, snd pr))) (signature o)
  | IAlloc x _ => Some ([TyI64], Some (x, TyPtr))
  | IFree _ => Some ([TyPtr], None)
  | ILoad x t sz _ => if load_ok t sz then Some ([TyPtr], Some (x, t)) else None
  | IStore sz _ v =>
    match T v with
    | Some t => if store_type_ok t sz then Some ([TyPtr; t], None) else None
    | None => None
    end
  | IOutput v => option_map (fun t => ([t], None)) (T v)
  end.

Definition instr_sig (P : program) (T : vid -> option ty)
    : instr -> option (list ty * option (vid * ty)) :=
  instr_sig_with (op_sig P) T.

(** Local instruction typing checks operands and the result's unique definition. *)
Definition instr_typed (P : program) (T : vid -> option ty) (i : instr) : Prop :=
  match instr_sig P T i with
  | None => False
  | Some (ps, dst) => types_of T (instr_uses i) = Some ps /\ result_has_type T dst
  end.

Definition instr_type_check_with (operators : sop -> option (list ty * ty))
    (T : vid -> option ty) : instr -> bool :=
  let signature := instr_sig_with operators T in
  fun i => match signature i with
  | None => false
  | Some (ps, dst) =>
    (if option_eq_dec (list_eq_dec ty_eq_dec) (types_of T (instr_uses i)) (Some ps)
     then true else false) && result_type_check T dst
  end.

Definition instr_type_check (P : program) (T : vid -> option ty) : instr -> bool :=
  instr_type_check_with (op_sig P) T.

Definition term_edges (t : terminator) : list (label * list vid) :=
  match t with
  | TJump l args => [(l, args)]
  | TBr _ l1 a1 l2 a2 => [(l1, a1); (l2, a2)]
  | TSwitch _ cs d da => map (fun p => (snd (fst p), snd p)) cs ++ [(d, da)]
  | TCall _ _ k => [(k, [])]
  | TRet _ => []
  end.

Definition term_uses (t : terminator) : list vid :=
  match t with
  | TJump _ args => args
  | TBr c _ a1 _ a2 => c :: a1 ++ a2
  | TSwitch c cs _ da => c :: flat_map snd cs ++ da
  | TCall (CDirect _) args _ => args
  | TCall (CIndirect x _ _) args _ => x :: args
  | TRet x => [x]
  end.

Definition entry_signature (fd : fdef) : option (list ty * ty) :=
  option_map (fun b => (map snd (bparams b), fresult fd)) (find_block fd (fentry fd)).

Definition entry_sig (P : program) : func -> option (list ty * ty) :=
  let signatures := Map.map entry_signature (first_index (funcs P)) in
  fun f => match Map.get nat_encoding f signatures with
  | None => None
  | Some sig => sig
  end.

Definition callee_sig_with (entry : func -> option (list ty * ty)) (T : vid -> option ty)
    : callee -> option (list ty * ty) :=
  fun c =>
  match c with
  | CDirect f => entry f
  | CIndirect x ps r =>
    match T x with
    | Some TyFun => Some (ps, r)
    | _ => None
    end
  end.

Definition callee_sig (P : program) (T : vid -> option ty)
    : callee -> option (list ty * ty) :=
  callee_sig_with (entry_sig P) T.

Definition typed_jump (B : label -> option ssa_block) (T : vid -> option ty)
    (edge : label * list vid) : Prop :=
  match B (fst edge) with
  | None => False
  | Some b => types_of T (snd edge) = Some (map snd (bparams b))
  end.

Definition jump_type_check (B : label -> option ssa_block) (T : vid -> option ty)
    (edge : label * list vid) : bool :=
  match B (fst edge) with
  | None => false
  | Some b =>
    if option_eq_dec (list_eq_dec ty_eq_dec) (types_of T (snd edge))
        (Some (map snd (bparams b))) then true else false
  end.

(** Terminator typing includes exact call and continuation signatures. *)
Definition term_typed (P : program) (fd : fdef) (T : vid -> option ty)
    (B : label -> option ssa_block) (t : terminator) : Prop :=
  match t with
  | TCall c args k =>
    match callee_sig P T c, B k with
    | Some (ps, r), Some b =>
      types_of T args = Some ps /\ map snd (bparams b) = [r]
    | _, _ => False
    end
  | TRet x => T x = Some (fresult fd)
  | TBr c _ _ _ _ | TSwitch c _ _ _ =>
    T c = Some TyI32 /\ Forall (typed_jump B T) (term_edges t)
  | TJump _ _ => Forall (typed_jump B T) (term_edges t)
  end.

Definition term_type_check_with (entry : func -> option (list ty * ty))
    (fd : fdef) (T : vid -> option ty)
    (B : label -> option ssa_block) : terminator -> bool :=
  let signature := callee_sig_with entry T in
  fun t =>
  match t with
  | TCall c args k =>
    match signature c, B k with
    | Some (ps, r), Some b =>
      (if option_eq_dec (list_eq_dec ty_eq_dec) (types_of T args) (Some ps)
       then true else false) &&
      (if list_eq_dec ty_eq_dec (map snd (bparams b)) [r] then true else false)
    | _, _ => false
    end
  | TRet x => if option_eq_dec ty_eq_dec (T x) (Some (fresult fd)) then true else false
  | TBr c _ _ _ _ | TSwitch c _ _ _ =>
    (if option_eq_dec ty_eq_dec (T c) (Some TyI32) then true else false) &&
      forallb (jump_type_check B T) (term_edges t)
  | TJump _ _ => forallb (jump_type_check B T) (term_edges t)
  end.

Definition term_type_check (P : program) (fd : fdef) (T : vid -> option ty)
    (B : label -> option ssa_block) : terminator -> bool :=
  term_type_check_with (entry_sig P) fd T B.

Definition idset : Type := Map.t nat unit.

Definition ids_index (xs : list nat) : idset := first_index (map (fun x => (x, tt)) xs).

Definition set_ids (a : idset) : list nat := map fst (Map.elements a).

Definition add_ids (xs : list nat) (a : idset) : idset :=
  fold_left (fun s x => Map.set nat_encoding x tt s) xs a.

Definition remove_ids (xs : list nat) (a : idset) : idset :=
  fold_left (fun s x => Map.remove nat_encoding x s) xs a.

Definition requirements : Type := Map.t label (list vid).

Definition required (R : requirements) (l : label) : list vid :=
  match Map.get nat_encoding l R with
  | Some xs => xs
  | None => []
  end.

Definition terminal_need (R : requirements) (t : terminator) : idset :=
  add_ids (term_uses t)
    (fold_left (fun a edge => add_ids (required R (fst edge)) a) (term_edges t) Map.empty).

Definition instruction_need (i : instr) (after : idset) : idset :=
  add_ids (instr_uses i) (remove_ids (instr_def i) after).

Definition block_need (R : requirements) (b : ssa_block) : list vid :=
  set_ids (remove_ids (map fst (bparams b))
    (fold_right instruction_need (terminal_need R (bterm b)) (bbody b))).

Definition requirement_round (fd : fdef) (R : requirements) : requirements :=
  first_index (map (fun lb => (fst lb, block_need R (snd lb))) (blocks fd)).

(** Binary iteration proposes a certificate; acceptance independently checks its closure. *)
Definition propose_requirements (fd : fdef) : requirements :=
  N.iter (N.of_nat (S (List.length (blocks fd)))) (requirement_round fd) Map.empty.

Fixpoint body_available (a : list vid) (code : list instr) : Prop :=
  match code with
  | [] => True
  | i :: rest =>
    Forall (fun x => In x a) (instr_uses i) /\ body_available (instr_def i ++ a) rest
  end.

Definition body_defs (b : ssa_block) : list vid := flat_map instr_def (bbody b).

(** A certificate propagates availability along every edge, including calls' returns. *)
Definition availability_certificate (fd : fdef) (R : requirements) : Prop :=
  required R (fentry fd) = [] /\
  Forall (fun lb =>
    let l := fst lb in
    let b := snd lb in
    let start := map fst (bparams b) ++ required R l in
    let finish := body_defs b ++ start in
    body_available start (bbody b) /\
    Forall (fun x => In x finish) (term_uses (bterm b)) /\
    Forall (fun edge => Forall (fun x => In x finish) (required R (fst edge)))
      (term_edges (bterm b))) (blocks fd).

Fixpoint body_available_check (a : idset) (code : list instr) : bool :=
  match code with
  | [] => true
  | i :: rest => forallb (fun x => Map.mem nat_encoding x a) (instr_uses i) &&
    body_available_check (add_ids (instr_def i) a) rest
  end.

Definition certificate_check (fd : fdef) (R : requirements) : bool :=
  (match required R (fentry fd) with [] => true | _ => false end) &&
  forallb (fun lb =>
    let b := snd lb in
    let start := ids_index (map fst (bparams b) ++ required R (fst lb)) in
    let finish := add_ids (body_defs b) start in
    body_available_check start (bbody b) &&
    forallb (fun x => Map.mem nat_encoding x finish) (term_uses (bterm b)) &&
    forallb (fun edge => forallb (fun x => Map.mem nat_encoding x finish)
      (required R (fst edge))) (term_edges (bterm b))) (blocks fd).

Fixpoint unique_check (seen : idset) (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (Map.mem nat_encoding x seen) &&
    unique_check (Map.set nat_encoding x tt seen) rest
  end.

Definition block_defs (b : ssa_block) : list vid := map fst (bparams b) ++ body_defs b.

Definition all_definitions (P : program) : list vid :=
  flat_map (fun ffd => flat_map (fun lb => block_defs (snd lb)) (blocks (snd ffd))) (funcs P).

Definition incoming_index (fd : fdef) : Map.t label nat :=
  fold_left (fun counts lb => fold_left (fun counts edge =>
    let l := fst edge in
    let n := match Map.get nat_encoding l counts with Some n => n | None => 0 end in
    Map.set nat_encoding l (S n) counts) (term_edges (bterm (snd lb))) counts)
    (blocks fd) Map.empty.

Definition continuation_ok (counts : Map.t label nat) (t : terminator) : Prop :=
  match t with
  | TCall _ _ k => Map.get nat_encoding k counts = Some 1
  | _ => True
  end.

Definition continuation_check (counts : Map.t label nat) (t : terminator) : bool :=
  match t with
  | TCall _ _ k =>
    match Map.get nat_encoding k counts with Some 1 => true | _ => false end
  | _ => true
  end.

(** Function well-formedness comprises names, local types, continuations and dominance. *)
Definition function_wf (P : program) (f : func) (fd : fdef) : Prop :=
  (exists b, find_block fd (fentry fd) = Some b) /\
  NoDup (map fst (blocks fd)) /\
  Forall (fun lb =>
    Forall (fun xt => static_ty P f (fst xt) = Some (snd xt)) (bparams (snd lb)) /\
    Forall (instr_typed P (static_ty P f)) (bbody (snd lb)) /\
    term_typed P fd (static_ty P f) (find_block fd) (bterm (snd lb)) /\
    continuation_ok (incoming_index fd) (bterm (snd lb))) (blocks fd) /\
  exists R, availability_certificate fd R.

(** The declarative program conditions are independent of the checker's proposed certificate. *)
Definition wf_program (ext : nat -> list cval -> option cval) (P : program) : Prop :=
  (exists fd, find_func P (main P) = Some fd) /\
  NoDup (map fst (funcs P)) /\ NoDup (all_definitions P) /\
  Forall (fun ffd => function_wf P (fst ffd) (snd ffd)) (funcs P) /\ ext_respects ext P.

Definition function_check_with (operators : sop -> option (list ty * ty))
    (entry : func -> option (list ty * ty)) (fd : fdef)
    (T : vid -> option ty) (B : label -> option ssa_block) : bool :=
  let counts := incoming_index fd in
  let instruction_check := instr_type_check_with operators T in
  let terminator_check := term_type_check_with entry fd T B in
  (match B (fentry fd) with Some _ => true | None => false end) &&
  unique_check Map.empty (map fst (blocks fd)) &&
  forallb (fun lb =>
    forallb (fun xt =>
      if option_eq_dec ty_eq_dec (T (fst xt)) (Some (snd xt)) then true else false)
      (bparams (snd lb)) &&
    forallb instruction_check (bbody (snd lb)) &&
    terminator_check (bterm (snd lb)) &&
    continuation_check counts (bterm (snd lb))) (blocks fd) &&
  certificate_check fd (propose_requirements fd).

Definition function_check (P : program) (ffd : func * fdef) : bool :=
  function_check_with (op_sig P) (entry_sig P) (snd ffd)
    (static_ty P (fst ffd)) (find_block (snd ffd)).

(** A prepared function shares its block index with its cached entry signature. *)
Record prepared_function : Type := PreparedFunction {
  prepared_def : fdef;
  prepared_block_index : Map.t label ssa_block;
  prepared_type_index : Map.t vid ty;
  prepared_signature : option (list ty * ty)
}.

Definition prepare_function (operators : sop -> option (list ty * ty)) (fd : fdef)
    : prepared_function :=
  let block_index := first_index (blocks fd) in
  let type_index := first_index (function_bindings_with operators fd) in
  let signature := option_map (fun b => (map snd (bparams b), fresult fd))
    (Map.get nat_encoding (fentry fd) block_index) in
  PreparedFunction fd block_index type_index signature.

Definition prepared_entry_sig (index : Map.t func prepared_function)
    : func -> option (list ty * ty) :=
  let signatures := Map.map prepared_signature index in
  fun f => match Map.get nat_encoding f signatures with
  | None => None
  | Some signature => signature
  end.

Definition function_check_prepared (operators : sop -> option (list ty * ty))
    (entry : func -> option (list ty * ty)) (index : Map.t func prepared_function)
    (ffd : func * fdef) : bool :=
  match Map.get nat_encoding (fst ffd) index with
  | None => false
  | Some ready =>
    function_check_with operators entry (prepared_def ready)
      (fun x => Map.get nat_encoding x (prepared_type_index ready))
      (fun l => Map.get nat_encoding l (prepared_block_index ready))
  end.

(** The executable checker validates finite structure, types and an availability certificate. *)
Definition wf_check (P : program) : bool :=
  let functions := first_index (funcs P) in
  let operators := op_sig P in
  let prepared := Map.map (prepare_function operators) functions in
  let entry := prepared_entry_sig prepared in
  (match Map.get nat_encoding (main P) functions with Some _ => true | None => false end) &&
  unique_check Map.empty (map fst (funcs P)) &&
  unique_check Map.empty (all_definitions P) &&
  forallb (function_check_prepared operators entry prepared) (funcs P).
