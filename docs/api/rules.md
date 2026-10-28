# Gaulois.Rules

Rules is a Datalog-style front end for dataflow analyses. An analysis is written as inference
rules over facts, as in the 15-411 notes (Pfenning, Platzer and Simmons), and the package compiles
it into the constraint systems of Fixpoint, one static system per stratum, and solves it with the
same engine. Facts are ground atoms whose arguments are the numeric codes of the client's keys. For
example, `live(n,x) :- use(n,x).` and `live(n,x) :- succ(n,m), live(m,x), !def(n,x).` with the facts
`use(2,7)`, `succ(1,2)` and no `def` give `live(2,7)` and `live(1,7)`. The *model* of a program is
defined by derivability, it is stratum-wise least (each stratum is least over the model below), and
the theorem of this package is that the engine computes exactly it.

Conventions of this document. Names are those of the anchors; `finite_set`,
`finite_powerset_lattice`, `finite_powerset_height` and `finite_powerset_laws` come from Order,
`list_encoding` from Collections, and the engine from Fixpoint (`System.t`, `Query.Ret`, `ask_all`,
`solve_total`, `rpo_scheduler`, `reached`, `least_solution`). Sets are `FinSet.t K`, written with
the encoding first. The names of this package are bare: a client writes `program`, `holds`,
`least_model`, `TVar`, and qualifies by the shortest module prefix only when its own names clash.
There is no text parser: a rule is written as a value. Statements sit in `Section`s whose `Context`
and `Variables` declare what they mention. Every `Inductive` and `Record` takes its parameters
implicitly in constructors and projections (`Arguments` declarations are omitted).

## Files

| File | Contents | Card |
|---|---|---|
| `RulesSyntax.v` | `term`, `atom`, `literal`, `rule`, `program`, `ground_atom`, `inst`, `ground`, `program_wf` | RUL-1a |
| `RulesStratify.v` | `stratification`, `stratified`, `stratify` (check and complete) | RUL-1a |
| `RulesCompile.v` | `preds`, `constants`, `in_universe`, `herbrand` (proof-only), `relation`, `restrict`, `fire_rule`, `rconstraint`, `stratum_system`, `stratum_static`; `fire_rule_exact`, `stratum_system_monotone` | RUL-1a |
| `RulesModel.v` | `derives`, `model_below`, `perfect_model`, `least_model`, `holds`; `least_model_closed` | RUL-1b |
| `RulesSolve.v` | `solve_program`, `db_holds`, `represents`; stratum soundness and completeness, `solve_program_exact` | RUL-1b |

Prerequisites. RUL-1a needs FIX-1 and ORD-2. RUL-1b needs RUL-1a and FIX-2b (it uses
`solve_total`, `solve_total_reached` and `solve_total_least`).

## Definitions

### Syntax and well-formedness

Predicates are of any encodable type `P`; variables are numbers; constants are the `positive`
codes of the client's keys (`encode E k`), so a ground atom is a predicate and a list of codes.

```coq
Definition tuple : Type := list positive.
Inductive term : Type := TVar (v : nat) | TConst (c : positive).
Record atom (P : Type) : Type := Atom { pred : P; args : list term }.
Inductive literal (P : Type) : Type := LPos (a : atom P) | LNeg (a : atom P).
Record rule (P : Type) : Type := Rule { head : atom P; body : list (literal P) }.
Record program (P : Type) : Type := Program {
  penc : encoding P;                     (* how predicates are keyed *)
  arity : P -> nat;
  rules : list (rule P)
}.
Definition ground_atom (P : Type) : Type := (P * tuple)%type.     (* a fact: the extensional facts are a list of them *)
Definition inst (sigma : nat -> positive) (t : term) : positive :=
  match t with TVar v => sigma v | TConst c => c end.
Definition ground {P} (sigma : nat -> positive) (a : atom P) : ground_atom P :=
  (pred a, map (inst sigma) (args a)).
Definition lit_atom {P} (l : literal P) : atom P := match l with LPos a | LNeg a => a end.
Definition atom_vars {P} (a : atom P) : list nat :=
  flat_map (fun t => match t with TVar v => [v] | TConst _ => [] end) (args a).
(* range restriction: every variable of the head or of a negative literal occurs in a positive literal *)
Definition safe_rule {P} (r : rule P) : Prop :=
  forall v, (In v (atom_vars (head r)) \/ exists a, In (LNeg a) (body r) /\ In v (atom_vars a)) ->
    exists a, In (LPos a) (body r) /\ In v (atom_vars a).
Definition program_wf {P} (prog : program P) (facts : list (ground_atom P)) : Prop :=
  (forall r, In r (rules prog) -> safe_rule r /\
     length (args (head r)) = arity prog (pred (head r)) /\
     forall l, In l (body r) -> length (args (lit_atom l)) = arity prog (pred (lit_atom l))) /\
  forall f, In f facts -> length (snd f) = arity prog (fst f).
```

### Stratification (`RulesStratify.v`)

A stratification gives each predicate a level. Negation may only read a strictly lower level, so
extensional predicates (level 0, no rules) can be negated freely.

```coq
Record stratification (P : Type) : Type := Stratification { level : P -> nat; count : nat }.
Definition stratified {P} (prog : program P) (st : stratification P) : Prop :=
  (forall p, level st p < count st) /\
  forall r l, In r (rules prog) -> In l (body r) ->
    match l with
    | LPos a => level st (pred a) <= level st (pred (head r))
    | LNeg a => level st (pred a) < level st (pred (head r))
    end.
Definition stratify {P} (prog : program P) : option (stratification P).
(* n := the number of distinct predicates that occur in rules. Raise levels to a fixpoint: all 0; each
   round is one pass over the rules, with a Map from predicate code to level, raising the level of the
   head to the maximum of itself, the level of each positive body predicate and one more than the
   level of each negative one. Fuel n*n+1 rounds: None if a level reaches n, or if the fuel runs out;
   otherwise level 0 for predicates outside the rules and count one more than the largest level *)
```

### The model (`RulesModel.v`)

Derivability is an inductive definition, so the model is the least set closed under its rules. At
level `k` it is taken over a given model `lower` of the levels below; a positive literal of level
`k` is derived recursively, a lower one and a negative one are read from `lower`. The perfect model
is built stratum by stratum, each stratum least over the one below.

```coq
Inductive derives {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P)
    (k : nat) (lower : ground_atom P -> Prop) : ground_atom P -> Prop :=
  | derive_fact : forall f, In f facts -> level st (fst f) = k -> derives prog facts st k lower f
  | derive_rule : forall r sigma, In r (rules prog) -> level st (pred (head r)) = k ->
      (forall a, In (LPos a) (body r) -> level st (pred a) < k -> lower (ground sigma a)) ->
      (forall a, In (LPos a) (body r) -> level st (pred a) = k ->
         derives prog facts st k lower (ground sigma a)) ->
      (forall a, In (LNeg a) (body r) -> ~ lower (ground sigma a)) ->
      derives prog facts st k lower (ground sigma (head r)).
(* the atoms of levels below n *)
Fixpoint model_below {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P)
    (n : nat) : ground_atom P -> Prop :=
  match n with
  | O => fun _ => False
  | S k => fun f => model_below prog facts st k f \/
                    derives prog facts st k (model_below prog facts st k) f
  end.
Definition perfect_model {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P) :
  ground_atom P -> Prop := model_below prog facts st (count st).
Definition least_model {P} (prog : program P) (facts : list (ground_atom P)) : ground_atom P -> Prop :=
  match stratify prog with Some st => perfect_model prog facts st | None => fun _ => False end.
Definition holds {P} (M : ground_atom P -> Prop) (p : P) (args : tuple) : Prop := M (p, args).
```

### Compilation to constraint systems (`RulesCompile.v`)

Negation makes the whole program non-monotone (`p :- !q.` with no rule for `q` has no least
post-solution), so each level compiles to its own static system in which every lower level is a
constant relation, and the levels are solved in order. Values are finite sets of tuples inside the
Herbrand universe, which gives a finite height.

The universe is described, never enumerated. `preds` and `constants` are finite sets computed in one
pass over the rules and facts (the predicates that occur, and every `TConst` and every component of
a fact). A tuple is inside the universe of a predicate when `in_universe` says so, a test that costs
its length. `herbrand` lists all such tuples and exists only as the `U` argument of Order's
finite-set lattice, in types and proofs: it is never evaluated. The `extraction/` directory (not
`theories/`) declares `Extraction Implicit` for the `U` argument of `finite_powerset_lattice` and
`finite_powerset_top`, and TOOL-2 checks that the extracted `solve_program` never mentions
`herbrand`.

```coq
Definition tuple_encoding : encoding tuple := list_encoding positive_encoding.
Definition preds {P} (prog : program P) (facts : list (ground_atom P)) : FinSet.t P.
(* FinSet.of_list (penc prog) of the head and body predicates of the rules and the predicates of the facts *)
Definition constants {P} (prog : program P) (facts : list (ground_atom P)) : FinSet.t positive.
(* FinSet.of_list positive_encoding of every TConst of the rules and every component of every fact *)
Definition in_universe {P} (prog : program P) (facts : list (ground_atom P)) (p : P) (ts : tuple) : bool :=
  FinSet.mem (penc prog) p (preds prog facts) && Nat.eqb (length ts) (arity prog p) &&
  forallb (fun c => FinSet.mem positive_encoding c (constants prog facts)) ts.
Definition herbrand {P} (prog : program P) (facts : list (ground_atom P)) : list tuple.
(* PROOF-ONLY: the distinct tuples over the constants whose length is the arity of a predicate that
   occurs, with herbrand_spec and herbrand_nodup below; never evaluated *)
Definition relation {P} (prog : program P) (facts : list (ground_atom P)) : Type :=
  finite_set tuple_encoding (herbrand prog facts).
Definition relation_lattice {P} (prog : program P) (facts : list (ground_atom P)) : lattice (relation prog facts) :=
  finite_powerset_lattice tuple_encoding (herbrand prog facts).
(* the tuples of s that are inside the universe of p, normalised through FinSet.of_list; membership in
   herbrand is proved from in_universe by herbrand_spec. This is the identity on the filtered
   output of fire_rule at the head predicate (restrict_spec). *)
Definition restrict {P} (prog : program P) (facts : list (ground_atom P)) (p : P) (s : FinSet.t tuple) :
  relation prog facts.
(* every tuple of env p has the arity of p, and env p is well formed *)
Definition env_wf {P} (prog : program P) (env : P -> FinSet.t tuple) : Prop :=
  forall p, FinSet.wf tuple_encoding (env p) /\
    forall ts, FinSet.mem tuple_encoding ts (env p) = true -> length ts = arity prog p.
(* head tuples of valuations satisfying the body, filtered to the head predicate's universe *)
Definition fire_rule {P} (prog : program P) (facts : list (ground_atom P)) (r : rule P)
  (env : P -> FinSet.t tuple) : FinSet.t tuple.
(* an index nested-loop join of the positive literals in order, each probed through a Table on its
   already-bound argument positions, built once per firing from the relation with FinSet.elements; a
   tuple whose length differs from the literal's matches nothing; a negative literal is a membership
   test; filter each head tuple with in_universe prog facts (pred (head r)), then build the result
   with FinSet.of_list, so it is well formed *)
Inductive rconstraint (P : Type) : Type := FromRule (i : nat) (h : P) | FromFact (p : P).
Definition rconstraint_encoding {P} (EP : encoding P) : encoding (rconstraint P).
Definition stratum_system {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P)
  (lower : P -> FinSet.t tuple) (k : nat) : System.t P (rconstraint P) (relation prog facts).
(* constraints: FromRule i (pred (head r_i)) for each rule r_i whose head has level k (i its position
   in rules prog), and FromFact p for each distinct predicate p of level k that has facts.
   target (FromRule _ h) = h and target (FromFact p) = p.
   rhs (FromRule i h) = ask_all the distinct level-k predicates of the positive literals of r_i
     (fun rels => Query.Ret (restrict prog facts h (fire_rule prog facts r_i env))), where env p is the
     asked relation (its underlying set) if level p = k, and lower p otherwise; an index i out of
     range gives Query.Ret of the empty relation;
   rhs (FromFact p) = Query.Ret (restrict prog facts p (the set of the facts of p)) *)
Definition stratum_static {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P)
  (lower : P -> FinSet.t tuple) (k : nat) : System.static (stratum_system prog facts st lower k).
(* deps (FromRule i _) = those level-k predicates; deps (FromFact _) = []; side_targets _ = [];
   reads_within and sides_within hold by ask_all_spec: the evidence is built with the system *)
```

### Solving (`RulesSolve.v`)

```coq
Definition database (P : Type) : Type := Map.t P (FinSet.t tuple).
Definition rel_of {P} (prog : program P) (db : database P) (p : P) : FinSet.t tuple :=
  match Map.get (penc prog) p db with Some s => s | None => FinSet.empty end.
Definition db_holds {P} (prog : program P) (db : database P) (p : P) (ts : tuple) : bool :=
  FinSet.mem tuple_encoding ts (rel_of prog db p).
Definition solve_program {P} (prog : program P) (facts : list (ground_atom P)) : option (database P).
(* stratify prog; for k = 0 .. count - 1: solve_total (penc prog) (rconstraint_encoding (penc prog))
   over stratum_system with lower = rel_of of the database so far, strategy Joining, scheduler
   rpo_scheduler, evidence inhabits (base_height (finite_powerset_height tuple_encoding
   (herbrand prog facts) herbrand_nodup)), a proof-only term that extraction erases. For the solver
   result s, add proj1_sig ((proj1_sig s) p) for each distinct target p of the stratum; None if not
   stratifiable *)
(* db represents a model M: every relation is well formed and holds exactly the atoms of M *)
Definition represents {P} (db : P -> FinSet.t tuple) (M : ground_atom P -> Prop) : Prop :=
  (forall p, FinSet.wf tuple_encoding (db p)) /\
  forall p ts, FinSet.mem tuple_encoding ts (db p) = true <-> M (p, ts).
```

## Theorems

```coq
Section Rules.
Context {P : Type} (prog : program P) (facts : list (ground_atom P)) (st : stratification P).
Variables (k : nat) (lower : P -> FinSet.t tuple) (env : P -> FinSet.t tuple) (r : rule P)
  (p : P) (ts : tuple) (s0 : FinSet.t tuple).

(** The proof-only universe is exactly the tuples inside it, without repetition. *)
Theorem herbrand_spec : In ts (herbrand prog facts) <-> exists p', FinSet.mem (penc prog) p' (preds prog facts) = true /\
  length ts = arity prog p' /\ forall c, In c ts -> FinSet.mem positive_encoding c (constants prog facts) = true.
Theorem herbrand_nodup : NoDup (herbrand prog facts).
(* Proof idea: the tuples of each arity over the elements of the constants set, deduplicated; FinSet.elements_spec and FinSet.elements_nodup. Card: RUL-1a. *)
(** `restrict` keeps exactly the members of a well-formed set that lie in the universe of the predicate. *)
Theorem restrict_spec : FinSet.wf tuple_encoding s0 ->
  FinSet.mem tuple_encoding ts (proj1_sig (restrict prog facts p s0)) = true <->
  FinSet.mem tuple_encoding ts s0 = true /\ in_universe prog facts p ts = true.
(* Proof idea: FinSet.of_list_spec and the membership of FinSet.elements. Card: RUL-1a. *)

(** `stratify` returns a stratification, and returns one whenever one exists. *)
Theorem stratify_sound : stratify prog = Some st -> stratified prog st.
Theorem stratify_complete : (exists st', stratified prog st') -> exists st'', stratify prog = Some st''.
(* Proof idea: soundness: the loop stops at a fixpoint of the raising rules. Completeness: if some level reaches n, the number of occurring predicates, a chain of raises through at least n negative edges visits a predicate twice, so a cycle through a negative literal exists and no stratification does; hence a stratifiable program keeps every level below n, each round that changes something raises the sum of the levels by at least one, the sum stays below n*n, and n*n+1 rounds reach a fixpoint. Card: RUL-1a. *)

(** A tuple is fired exactly when it lies in the universe and a valuation instantiates the head
    to it while satisfying the body on the relations. *)
Theorem fire_rule_exact : program_wf prog facts -> In r (rules prog) -> env_wf prog env -> forall ts',
  FinSet.mem tuple_encoding ts' (fire_rule prog facts r env) = true <->
  in_universe prog facts (pred (head r)) ts' = true /\
  exists sigma, ts' = map (inst sigma) (args (head r)) /\
    (forall a, In (LPos a) (body r) ->
       FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) /\
    (forall a, In (LNeg a) (body r) ->
       FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = false).
Theorem fire_rule_wf : (forall q, FinSet.wf tuple_encoding (env q)) ->
  FinSet.wf tuple_encoding (fire_rule prog facts r env).
(* Proof idea: induction on the positive literals in join order: the partial bindings are exactly
   those of the satisfied prefix; safety binds every head and negative variable; a variable outside
   the rule is free in sigma; the arity premise makes every stored tuple the instance of its own
   literal; the filter enforces in_universe and the result is FinSet.of_list. Card: RUL-1a. *)
(** The converse needs no environment arity: an in-universe head satisfying the body is fired. *)
Theorem fire_rule_complete : program_wf prog facts -> In r (rules prog) ->
  (forall q, FinSet.wf tuple_encoding (env q)) -> forall sigma,
  in_universe prog facts (pred (head r)) (map (inst sigma) (args (head r))) = true ->
  (forall a, In (LPos a) (body r) ->
     FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) ->
  (forall a, In (LNeg a) (body r) ->
     FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = false) ->
  FinSet.mem tuple_encoding (map (inst sigma) (args (head r))) (fire_rule prog facts r env) = true.
(* Proof idea: as fire_rule_exact, one direction; a tuple of the wrong length is ignored by the
   index and never needed, and the in_universe premise passes the output filter. Card: RUL-1a. *)

(** Each level compiles to a monotone system: lower levels and negated predicates are constants. *)
Theorem stratum_system_monotone : program_wf prog facts -> env_wf prog lower -> stratified prog st ->
  monotone_system (relation_lattice prog facts) (stratum_system prog facts st lower k).
(* Proof idea: a positive level-k literal grows with its relation (monotone_query of ask_all and a join whose probes only gain matches); restrict is monotone (restrict_spec); every other literal reads the constant `lower`. Card: RUL-1a. *)

(** The model contains the facts and is closed under every rule: a satisfied body gives its head. *)
Theorem least_model_closed : stratify prog = Some st ->
  (forall f, In f facts -> least_model prog facts f) /\
  forall sigma, In r (rules prog) ->
    (forall a, In (LPos a) (body r) -> least_model prog facts (ground sigma a)) ->
    (forall a, In (LNeg a) (body r) -> ~ least_model prog facts (ground sigma a)) ->
    least_model prog facts (ground sigma (head r)).
(* Proof idea: an atom of level j is in model_below n exactly when it is derived at stage j, for every n above j, since a stage derives only atoms of its own level; then derive_fact and derive_rule. Card: RUL-1b. *)
(** Every atom of the model lies in the universe of its predicate: right arity, constants of the program. *)
Theorem model_constants : program_wf prog facts -> stratified prog st ->
  forall n a, model_below prog facts st n a -> in_universe prog facts (fst a) (snd a) = true.
(* Proof idea: induction on n and on the derivation: facts use their constants; a derived head has the arity of its predicate (program_wf) and each component is a rule constant or, by safety, a component of a positive body atom, which lies in the universe. Card: RUL-1b. *)

(** On a database that represents the levels below, every post-solution of the level's system contains what is derived there. *)
Theorem stratum_post_solution_contains : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) ->
  forall s, post_solution (relation_lattice prog facts) (stratum_system prog facts st lower k) s ->
  forall p' ts', level st p' = k -> derives prog facts st k (model_below prog facts st k) (p', ts') ->
  FinSet.mem tuple_encoding ts' (proj1_sig (s p')) = true.
(* Proof idea: induction on the derivation: a fact is its FromFact constraint. For a rule instance,
   model_constants supplies the in_universe premise of fire_rule_complete; positive level-k atoms
   are in the contained relations by the induction hypothesis, and lower atoms and the absence of
   negated ones follow from represents. restrict_spec keeps the result, and the post-solution
   inequality puts it in s. Card: RUL-1b. *)
(** What a run of the engine reaches from bottom is derived: member implies derived. *)
Theorem stratum_reached_derives : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) ->
  forall s, reached (penc prog) (relation_lattice prog facts) (stratum_system prog facts st lower k) s ->
  forall p' ts', level st p' = k -> FinSet.mem tuple_encoding ts' (proj1_sig (s p')) = true ->
  derives prog facts st k (model_below prog facts st k) (p', ts').
(* Proof idea: induction on reached: bottom has no members; a run adds only tuples of fire_rule_exact on the current relations, whose own members are derived by the induction hypothesis (and are arity-respecting, since restrict keeps in_universe), so each added tuple is a derive_rule or derive_fact instance. Card: RUL-1b. *)
(** A least solution of the level's system holds exactly what is derived there. *)
Theorem stratum_least_is_derives : program_wf prog facts -> stratified prog st -> (k < count st)%nat ->
  represents lower (model_below prog facts st k) ->
  forall s, least_solution (relation_lattice prog facts) (stratum_system prog facts st lower k) s ->
  forall p' ts', level st p' = k ->
    (FinSet.mem tuple_encoding ts' (proj1_sig (s p')) = true <->
     derives prog facts st k (model_below prog facts st k) (p', ts')).
(* Proof idea: derived implies member is stratum_post_solution_contains. Member implies derived: the engine's result s' is reached (solve_total_reached, with the evidence from finite_powerset_height) and a post-solution, hence least (reached_least, with finite_powerset_laws, finite_powerset_lub and stratum_system_monotone); least_solution_unique makes s and s' equivalent, so they have the same members, and stratum_reached_derives applies to s'. Card: RUL-1b. *)

(** The solver fails exactly on unstratifiable programs and otherwise computes the least model; since each level is solved to its least solution, the result of the engine with `Joining` is the model, stratum by stratum. *)
Theorem solve_program_exact : program_wf prog facts -> (exists st', stratified prog st') ->
  exists db, solve_program prog facts = Some db /\ represents (rel_of prog db) (least_model prog facts).
Theorem solve_program_none : (forall st', ~ stratified prog st') -> solve_program prog facts = None.
(* Proof idea: induction on the level k: the database before level k represents model_below k; solve_total_least (lub_laws and the height of the finite powerset, monotone by stratum_system_monotone) makes the level's values a least solution, which stratum_least_is_derives identifies with the derivations, so the database represents model_below (k + 1). The second is stratify_complete. Card: RUL-1b. *)
End Rules.
```

## Algorithms and references

- **Analyses as inference rules:** the 15-411 lecture notes of Pfenning, Platzer and Simmons give
  liveness, neededness (`N1` to `N3`) and reaching definitions as rules over `use`, `def`, `succ`
  and `nec`; ANA-11 writes them as `program` values. Datalog for program analysis: Whaley, Avots,
  Carbin and Lam (APLAS 2005); Soufflé (Jordan, Scholz and Subotic, CAV 2016).
- **Stratified negation and the perfect model:** Apt, Blair and Walker, "Towards a theory of
  declarative knowledge" (1988); Przymusinski (1988). `derives` is the textbook inductive
  definition of derivability, taken one level at a time over the model below.
- **Evaluation:** naive bottom-up evaluation through the Fixpoint engine, one level at a time.
  Semi-naive evaluation (Bancilhon and Ramakrishnan, 1986) would fire only on the new tuples and
  changes `fire_rule` and not the theorems.
- **Joins:** index nested loops over the positive literals in order, as in a Datalog interpreter.

## Performance notes

- Each positive literal is probed through an index on its already-bound argument positions: a
  `Table` keyed by the list of bound codes, built once per firing from the relation in
  O(size of the relation), then one probe per partial binding. No list of tuples is scanned inside
  the join; a negative literal is one `FinSet.mem`. The agreement lemma of these indexes (a probe
  returns exactly the tuples that match the bound positions) is internal to `fire_rule_exact`.
- The compiled system is static, so the engine reads dependencies from its prepared `sys_index`
  (`index_system_laws`). A rule fires again whenever a level-`k` relation in its body changes, so
  evaluation is naive: polynomial in the number of constants, quadratic in the worst case.
- `stratify` makes at most `n*n+1` rounds, each a pass over the rules with a `Map` from predicate
  code to level.
- `preds` and `constants` are built once per `solve_program` call, linear in the program and facts;
  `fire_rule` filters each firing's output with `in_universe`, linear in the output. `herbrand`
  appears only in types and proofs and is erased: the `U` argument of `finite_powerset_lattice` and
  `finite_powerset_top` is `Extraction Implicit`, and the evidence passed to `solve_total` is
  `inhabited`, which extraction erases.

## Open questions

1. **Interface assumed by ANA-11.** `program P`, `ground_atom P`, `least_model prog facts`,
   `holds` and arguments as lists of codes are as ANA-11 writes them. A program here also carries
   `penc` and `arity`, so ANA-11's `liveness_program` supplies them. The three programs of ANA-11
   are written as values; a printer or notation is not part of this card.
2. **One system per level.** A single system for the whole program is non-monotone under negation
   and has no least post-solution (`p :- !q.` has post-solutions with `q` empty and `p` full, and
   with `q` full and `p` empty), so the compile is per level and the engine runs level by level.
3. **Facts for derived predicates** are allowed (`FromFact`); a fact of level `k` feeds level `k`.
4. **Safety is required** so that every derived tuple lies inside the universe; `program_wf`
   rejects an unsafe rule, and `least_model` is only claimed to match the engine under it.
5. **Unstratifiable programs** have the empty `least_model` and `solve_program = None`; a client
   checks `stratify` first.
6. **Constants are codes.** There is no constant type parameter; a client encodes its keys with
   `encode`, and `holds` takes the codes, as ANA-11 does, so no decoding is needed.

## Cross-document contracts

Analyses uses the bare Rules names. Where a constructor conflicts, it uses its defining module.
`program_wf` takes the program and facts. The solvers return functions with post-solution proofs.
Order provides the finite powerset laws and height. Collections provides well-formed finite sets
and a `Table` keyed by `list positive`.
