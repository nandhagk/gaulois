# Gaulois.Collections

## Dense finite-universe set backend (COL-3)

`CollectionsDenseSet.v` defines a separate set carrier for a fixed finite universe; it does not
change `FinSet.t` or C4. Its bitset is a nonnegative `N`, and its operations ignore all bits at
positions at or above the universe length. `universe` has no duplicate keys. Index lookup is built
once as a `Map.t K N` and retains the exact positions in `universe`; no operation scans `universe`
except conversion to a list or `FinSet` and initial index construction. All operations take the
same prepared universe and reject keys outside it by leaving the set unchanged.

```coq
Record dense_universe (K : Type) : Type := DenseUniverse {
  dense_keys : list K;
  dense_index : Map.t K N;
  dense_length : N
}.
Definition dense_universe_wf {K} (E : encoding K) (u : dense_universe K) : Prop :=
  NoDup (dense_keys u) /\ Map.wf E (dense_index u) /\
  dense_length u = N.of_nat (List.length (dense_keys u)) /\
  (forall k i, Map.get E k (dense_index u) = Some i <->
    nth_error (dense_keys u) (N.to_nat i) = Some k).
Definition dense_prepare {K} (E : encoding K) (keys : list K) : dense_universe K.
(* Keep the first occurrence of each key, in input order; construct dense_index and
   dense_length once. *)
Definition dense_set := N.
Definition dense_empty : dense_set := 0%N.
Definition dense_mem {K} (E : encoding K) (u : dense_universe K) (k : K) (s : dense_set) : bool.
Definition dense_add {K} (E : encoding K) (u : dense_universe K) (k : K) (s : dense_set) :
  dense_set.
Definition dense_remove {K} (E : encoding K) (u : dense_universe K) (k : K) (s : dense_set) :
  dense_set.
Definition dense_union {K} (u : dense_universe K) (a b : dense_set) : dense_set.
Definition dense_inter {K} (u : dense_universe K) (a b : dense_set) : dense_set.
Definition dense_diff {K} (u : dense_universe K) (a b : dense_set) : dense_set.
Definition dense_subset {K} (u : dense_universe K) (a b : dense_set) : bool.
Definition dense_to_finset {K} (E : encoding K) (u : dense_universe K) (s : dense_set) : FinSet.t K.
Definition dense_of_finset {K} (E : encoding K) (u : dense_universe K) (s : FinSet.t K) : dense_set.
(* Bit i corresponds to nth_error (dense_keys u) i. Binary operations first mask to the cached
   dense_length; dense_to_finset enumerates dense_keys in order, retaining precisely its set bits.
   The length cache agrees with the keys when dense_universe_wf holds. *)

Theorem dense_prepare_wf {K} (E : encoding K) (keys : list K) :
  dense_universe_wf E (dense_prepare E keys).
Theorem dense_mem_refines {K} (E : encoding K) (u : dense_universe K) (s : dense_set) (k : K) :
  dense_universe_wf E u ->
  dense_mem E u k s = FinSet.mem E k (dense_to_finset E u s).
Theorem dense_roundtrip {K} (E : encoding K) (u : dense_universe K) (s : FinSet.t K) (k : K) :
  dense_universe_wf E u -> FinSet.wf E s ->
  dense_mem E u k (dense_of_finset E u s) =
    (FinSet.mem E k s && existsb (fun x => Pos.eqb (encode E x) (encode E k)) (dense_keys u)).
Theorem dense_union_mem {K} (E : encoding K) (u : dense_universe K) (a b : dense_set) (k : K) :
  dense_universe_wf E u -> dense_mem E u k (dense_union u a b) =
    (dense_mem E u k a || dense_mem E u k b).
Theorem dense_inter_mem {K} (E : encoding K) (u : dense_universe K) (a b : dense_set) (k : K) :
  dense_universe_wf E u -> dense_mem E u k (dense_inter u a b) =
    (dense_mem E u k a && dense_mem E u k b).
Theorem dense_diff_mem {K} (E : encoding K) (u : dense_universe K) (a b : dense_set) (k : K) :
  dense_universe_wf E u -> dense_mem E u k (dense_diff u a b) =
    (dense_mem E u k a && negb (dense_mem E u k b)).
Theorem dense_subset_spec {K} (E : encoding K) (u : dense_universe K) (a b : dense_set) :
  dense_universe_wf E u ->
  (dense_subset u a b = true <-> forall k, dense_mem E u k a = true -> dense_mem E u k b = true).
Theorem dense_add_mem {K} (E : encoding K) (u : dense_universe K) (s : dense_set) (k x : K) :
  dense_universe_wf E u -> dense_mem E u x (dense_add E u k s) =
    (dense_mem E u x s ||
      (Pos.eqb (encode E x) (encode E k) &&
       existsb (fun y => Pos.eqb (encode E y) (encode E k)) (dense_keys u))).
Theorem dense_remove_mem {K} (E : encoding K) (u : dense_universe K) (s : dense_set) (k x : K) :
  dense_universe_wf E u -> dense_mem E u x (dense_remove E u k s) =
    (dense_mem E u x s && negb (Pos.eqb (encode E x) (encode E k))).
```

The bounds on the bitset operations count arbitrary-precision bit operations, not machine-word
O(1). Dense sets and FinSet have the same membership for keys in the prepared universe; they do
not promise the same enumeration order. Card: COL-3.

Collections provides the data structures every other package builds on: encodings that turn any
key type into `positive`, canonical binary tries, maps and sets over encodable keys, a priority
queue, a persistent union-find, and tables keyed by lists of numbers. A client never sees a trie;
it passes an `encoding K` to each map operation. For example, with `E := pair_encoding
positive_encoding positive_encoding`:

```coq
Definition m : Map.t (positive * positive) nat := Map.set E (1%positive, 2%positive) 7 Map.empty.
(* Map.get E (1%positive, 2%positive) m = Some 7  and  Map.get E (2%positive, 1%positive) m = None *)
```

Conventions of this document. A theorem written `Theorem M.name` is declared as `name` inside
`Module M`. Statements sit in `Section`s that declare the variables they mention. Record
projections take their parameters implicitly (`Arguments encode {K}`). Stdlib imports
(`ZArith`, `List`, `Bool`, `Sorting.Sorted`, `Relations.Relation_Definitions`,
`Relations.Relation_Operators`) are implicit. The set module is `FinSet`, because `Set` is a Rocq
keyword. A law holds for every trie, well formed or not, unless its statement says `wf`. The
position-level API (`Map.code_get` and its laws, `FinSet.subset_code`) states what holds position
by position, so that Order proves its lattice laws for every trie without a `wf` premise.

## Files

| File | Contents | Card |
|---|---|---|
| `CollectionsEncoding.v` | `encoding`, the ten provided encodings, their codes | COL-1a |
| `CollectionsTrie.v` | `Trie`: canonical binary tries, traversal and extensionality | COL-1b |
| `CollectionsMap.v` | `Map`: maps, well-formedness, position API and equality | COL-1c |
| `CollectionsFinSet.v` | `FinSet`: sets, set algebra and size lemmas | COL-1c |
| `CollectionsHeap.v` | `PQueue`: min-priority queue with membership | COL-2 |
| `CollectionsUnionFind.v` | `UnionFind`: persistent union-find, rank, path compression | COL-2 |
| `CollectionsTable.v` | `Table`: maps keyed by `list positive`, as a flat `Map` | COL-2 |
| `CollectionsDenseSet.v` | Prepared finite universes and packed set refinement | COL-3 |

## Definitions

### Encodings (`CollectionsEncoding.v`)

```coq
Record encoding (K : Type) : Type := Encoding {
  encode : K -> positive;
  encode_injective : forall x y, encode x = encode y -> x = y
}.
Definition positive_encoding : encoding positive.   (* encode p = p *)
Definition N_encoding : encoding N.                 (* encode n = N.succ_pos n *)
Definition nat_encoding : encoding nat.             (* encode n = Pos.of_succ_nat n *)
Definition Z_encoding : encoding Z.                 (* 0 -> 1, Zpos p -> p~0, Zneg p -> p~1 *)
Definition bool_encoding : encoding bool.           (* false -> 1, true -> 2 *)
Definition unit_encoding : encoding unit.           (* tt -> 1 *)
Definition option_encoding {A} (EA : encoding A) : encoding (option A).
(* None -> 1, Some a -> (encode a)~0 *)
Definition sum_encoding {A B} (EA : encoding A) (EB : encoding B) : encoding (A + B).
(* inl a -> (encode a)~0, inr b -> (encode b)~1 *)
Definition pair_encoding {A B} (EA : encoding A) (EB : encoding B) : encoding (A * B).
Definition list_encoding {A} (EA : encoding A) : encoding (list A).
```

The codes of `positive`, `N`, `nat`, `Z`, `bool`, `unit`, `option` and `sum` are exactly those
shown, so that element order is predictable. `pair_encoding` and `list_encoding` fix only
injectivity. Build both through `list bool`: write each code's bits below its leading 1, doubling
each bit (`0` as `00`, `1` as `11`) and ending each code with `01`. Concatenate the two encoded
codes for a pair or the encoded codes of all list elements, then convert the complete bit list to
`positive` once, with a leading 1. Use accumulators or another linear construction, so encoding
takes time linear in the total number of emitted bits. Card: COL-1a. COL-1a also removes the
temporary `(allow_empty)` from `dune-project`. COL-1c depends on COL-1a and COL-1b.

### Tries (`CollectionsTrie.v`)

A trie is canonical by construction: there is no representation of an empty subtree, so two tries
with the same bindings are equal. Suggested representation (internal; clients never match on it):

```coq
Inductive ne (A : Type) : Type :=              (* non-empty trees: 7 shapes *)
  | N001 (r : ne A) | N010 (v : A) | N011 (v : A) (r : ne A)
  | N100 (l : ne A) | N101 (l r : ne A) | N110 (l : ne A) (v : A) | N111 (l : ne A) (v : A) (r : ne A).
Inductive t (A : Type) : Type := Empty | Nodes (n : ne A).
```

A key is read least-significant bit first: `xH` is the root, `xO p` goes left, `xI p` goes right.

```coq
Definition Trie.empty {A} : Trie.t A.
Definition Trie.is_empty {A} (t : Trie.t A) : bool.
Definition Trie.get {A} (p : positive) (t : Trie.t A) : option A.
Definition Trie.set {A} (p : positive) (v : A) (t : Trie.t A) : Trie.t A.
Definition Trie.remove {A} (p : positive) (t : Trie.t A) : Trie.t A.
Definition Trie.map {A B} (f : A -> B) (t : Trie.t A) : Trie.t B.
Definition Trie.combine {A B C} (f : option A -> option B -> option C)
  (t1 : Trie.t A) (t2 : Trie.t B) : Trie.t C.    (* pointwise when f None None = None *)
Definition Trie.fold {A B} (f : B -> positive -> A -> B) (t : Trie.t A) (b : B) : B.
Definition Trie.elements {A} (t : Trie.t A) : list (positive * A).
Definition Trie.size {A} (t : Trie.t A) : nat.
Definition Trie.beq {A} (eqb : A -> A -> bool) (t1 t2 : Trie.t A) : bool.
Definition Trie.forall2 {A B} (r : A -> option B -> bool) (t1 : Trie.t A) (t2 : Trie.t B) : bool.
Definition Trie.union_opt {A} (f : A -> A -> A) (a b : option A) : option A :=
  match a, b with
  | Some x, Some y => Some (f x y) | Some x, None => Some x
  | None, Some y => Some y | None, None => None
  end.
Definition Trie.union_with {A} (f : A -> A -> A) (t1 t2 : Trie.t A) : Trie.t A.
```

`Trie.elements` and `Trie.fold` visit keys in the in-order of the trie: left subtree, root,
right subtree. That order is the strict order `Trie.key_lt`:

```coq
Fixpoint Trie.key_lt (p q : positive) {struct p} : Prop :=
  match p, q with
  | xO p', xO q' => Trie.key_lt p' q'
  | xI p', xI q' => Trie.key_lt p' q'
  | xO _, xH | xO _, xI _ | xH, xI _ => True
  | _, _ => False
  end.
```

When `f None None = None`, `Trie.combine f t1 t2` binds `p` to
`f (Trie.get p t1) (Trie.get p t2)` whenever that is `Some`. It visits only the paths present in
`t1` or `t2` (cost linear in their sizes, no key enumeration).
`Trie.forall2 r t1 t2` is true when `r a (Trie.get p t2) = true` for every binding `(p, a)` of `t1`;
it stops at the first failure and follows `t2` only along the paths of `t1`. `Trie.union_with f t1
t2` binds `p` to `Trie.union_opt f (Trie.get p t1) (Trie.get p t2)`; a subtree present in one trie
only is shared, never rebuilt. `combine` is the general operation (it rebuilds one-sided subtrees
through `f`); `forall2` and `union_with` are the cheap cases that subset tests and unions need.

### Maps (`CollectionsMap.v`)

```coq
Definition Map.t (K V : Type) : Type := Trie.t (K * V).   (* the key is stored at its code *)
Definition Map.empty {K V} : Map.t K V := Trie.empty.
Definition Map.wf {K V} (E : encoding K) (m : Map.t K V) : Prop :=
  forall p k v, Trie.get p m = Some (k, v) -> encode E k = p.
Definition Map.code_get {K V} (p : positive) (m : Map.t K V) : option V := option_map snd (Trie.get p m).
(* the value at a position, whatever key is stored there: the position-level API *)
Definition Map.get {K V} (E : encoding K) (k : K) (m : Map.t K V) : option V :=
  Map.code_get (encode E k) m.
Definition Map.set {K V} (E : encoding K) (k : K) (v : V) (m : Map.t K V) : Map.t K V.
Definition Map.remove {K V} (E : encoding K) (k : K) (m : Map.t K V) : Map.t K V.
Definition Map.map {K V W} (f : V -> W) (m : Map.t K V) : Map.t K W.
Definition Map.combine {K V W U} (E : encoding K) (f : option V -> option W -> option U)
  (m1 : Map.t K V) (m2 : Map.t K W) : Map.t K U.   (* pointwise when f None None = None *)
Definition Map.fold {K V B} (f : B -> K -> V -> B) (m : Map.t K V) (b : B) : B.
Definition Map.elements {K V} (m : Map.t K V) : list (K * V).     (* Trie order of the codes *)
Definition Map.size {K V} (m : Map.t K V) : nat.
Definition Map.is_empty {K V} (m : Map.t K V) : bool.
Definition Map.mem {K V} (E : encoding K) (k : K) (m : Map.t K V) : bool.
Definition Map.of_list {K V} (E : encoding K) (l : list (K * V)) : Map.t K V.
(* fold_left of Map.set from Map.empty: a later binding replaces an earlier one *)
Definition Map.beq {K V} (eqb : V -> V -> bool) (m1 m2 : Map.t K V) : bool.   (* values only *)
Definition Map.forall2 {K V W} (r : V -> option W -> bool) (m1 : Map.t K V) (m2 : Map.t K W) : bool.
(* Trie.forall2 on the stored pairs: r is applied to the value of m1 and the value (if any) of m2 *)
Definition Map.union_with {K V} (f : V -> V -> V) (m1 m2 : Map.t K V) : Map.t K V.
(* Trie.union_with on the stored pairs; a position bound in both keeps the key of m1 *)
```

`Map.get E k m` reads the trie at `encode E k` and drops the stored key. `Map.set E k v m` stores
`(k, v)` at `encode E k`. `Map.map f` maps values and keeps keys. `Map.combine` keeps, at each
position it binds, the key stored in `m1` if present and otherwise the key stored in `m2`.
`Map.size`, `Map.is_empty` and `Map.mem` are defined from `Trie.size`, `Trie.is_empty` and
`Map.get`.
`Map.beq eqb` is `Trie.beq` on the stored pairs comparing values only, which is sound for
well-formed
maps because stored keys at equal codes are equal.

`Map.code_get p m` reads the trie at the code `p` and never decodes a key; `Map.get E k m` is
`Map.code_get (encode E k) m` by definition. `Map.forall2` and `Map.union_with` are the map forms of
`Trie.forall2` and `Trie.union_with`; Order's pointwise comparison and join, and `FinSet.subset` and
`FinSet.union`, are defined through them.

### Finite sets (`CollectionsFinSet.v`)

```coq
Definition FinSet.t (K : Type) : Type := Map.t K unit.
Definition FinSet.wf {K} (E : encoding K) (s : FinSet.t K) : Prop := Map.wf E s.
Definition FinSet.empty {K} : FinSet.t K := Map.empty.
Definition FinSet.mem {K} (E : encoding K) (k : K) (s : FinSet.t K) : bool.
Definition FinSet.add {K} (E : encoding K) (k : K) (s : FinSet.t K) : FinSet.t K := Map.set E k tt s.
Definition FinSet.remove {K} (E : encoding K) (k : K) (s : FinSet.t K) : FinSet.t K := Map.remove E k s.
Definition FinSet.union {K} (E : encoding K) (s1 s2 : FinSet.t K) : FinSet.t K :=
  Map.union_with (fun a _ => a) s1 s2.
Definition FinSet.inter {K} (E : encoding K) (s1 s2 : FinSet.t K) : FinSet.t K :=
  Map.combine E (fun a b => match a, b with Some _, Some _ => Some tt | _, _ => None end) s1 s2.
Definition FinSet.diff {K} (E : encoding K) (s1 s2 : FinSet.t K) : FinSet.t K :=
  Map.combine E (fun a b => match a, b with Some _, None => Some tt | _, _ => None end) s1 s2.
Definition FinSet.subset {K} (E : encoding K) (s1 s2 : FinSet.t K) : bool :=
  Map.forall2 (fun _ o => match o with Some _ => true | None => false end) s1 s2.
Definition FinSet.elements {K} (s : FinSet.t K) : list K := List.map fst (Map.elements s).
Definition FinSet.size {K} (s : FinSet.t K) : nat := Map.size s.
Definition FinSet.is_empty {K} (s : FinSet.t K) : bool := Map.is_empty s.
Definition FinSet.of_list {K} (E : encoding K) (l : list K) : FinSet.t K.     (* fold of FinSet.add *)
```

`FinSet.union`, `FinSet.inter`, `FinSet.diff` and `FinSet.subset` are position-wise: they compare
codes and
never decode keys, so they are correct for every trie, well-formed or not; the specification
theorems below add `FinSet.wf` only where they speak about keys.
`FinSet.subset` stops at the first binding of `s1` that `s2` lacks, and `FinSet.union` shares the
subtrees
that only one operand has; neither builds an intermediate trie.

### Priority queue (`CollectionsHeap.v`)

`PQueue.t K` holds each key at most once, with one priority. The pop order is the lexicographic
order on `(priority, encode key)`, so ties between keys of equal priority are broken by code and a
run is deterministic.

```coq
Definition PQueue.t (K : Type) : Type.
Definition PQueue.empty {K} : PQueue.t K.
Definition PQueue.is_empty {K} (q : PQueue.t K) : bool.
Definition PQueue.size {K} (q : PQueue.t K) : nat.        (* number of keys held; O(1) *)
Definition PQueue.push {K} (E : encoding K) (p : positive) (k : K) (q : PQueue.t K) : PQueue.t K.
(* absent key: inserted with priority p; present key: priority becomes Pos.min p old *)
Definition PQueue.pop {K} (E : encoding K) (q : PQueue.t K) : option (positive * K * PQueue.t K).
(* None on an empty queue; else the minimal (priority, code) key with its priority, and the rest *)
Definition PQueue.priority {K} (E : encoding K) (k : K) (q : PQueue.t K) : option positive.
Definition PQueue.members {K} (q : PQueue.t K) : list (K * positive).   (* the held pairs *)
Definition PQueue.wf {K} (E : encoding K) (q : PQueue.t K) : Prop.
Definition PQueue.before (p1 c1 p2 c2 : positive) : Prop :=
  (p1 < p2)%positive \/ (p1 = p2 /\ (c1 <= c2)%positive).
```

The specification is the finite map `key -> priority` that `PQueue.priority` reads and
`PQueue.members` lists. Use a persistent rank-position binomial heap of entries
`(priority, code, key)`, a `Map.t K positive` of live priorities, and cached live and pending
entry counts. A push that lowers a priority inserts a new entry and leaves the old entry stale;
`pop` discards an entry
whose priority differs from the live one, including when its key is absent from the live map.
`PQueue.wf` says the heap order holds, every entry's code is `encode E key`, the live map satisfies
`Map.wf E`, every live key has an entry with its live priority, and the counters agree with the
live keys and pending entries. Heap ranks are represented by position, so linking and merging do
not compare rank values. `pop` uses the cached entry count as fuel, decreasing it for each
discarded entry.

### Union-find (`CollectionsUnionFind.v`)

Every key starts alone in its own class, so `UnionFind.make` needs no key list. The structure is a
record that lives in its own module, so that its field names never clash with Order's `rank`:

```coq
Record UnionFind.t (K : Type) : Type := Forest {
  parents : Map.t K K;                         (* absent: the key is a root *)
  ranks : Map.t K nat;                         (* absent: rank 0 *)
  max_rank : nat                               (* an upper bound on every rank *)
}.
Definition UnionFind.make {K} : UnionFind.t K := Forest Map.empty Map.empty 0.
Definition UnionFind.find {K} (E : encoding K) (x : K) (uf : UnionFind.t K) : K * UnionFind.t K.
(* the representative of x, and uf with the path from x compressed *)
Definition UnionFind.union {K} (E : encoding K) (x y : K) (uf : UnionFind.t K) : UnionFind.t K.
Definition UnionFind.equiv {K} (E : encoding K) (uf : UnionFind.t K) (x y : K) : Prop :=
  fst (UnionFind.find E x uf) = fst (UnionFind.find E y uf).
Definition UnionFind.equivb {K} (E : encoding K) (x y : K) (uf : UnionFind.t K) :
  bool * UnionFind.t K.                       (* the test, and the compressed structure *)
Definition UnionFind.keys {K} (E : encoding K) (uf : UnionFind.t K) : list K.
(* the support: the keys with a parent or a rank entry, each once; the FinSet.elements of the union
   of the key sets of parents and ranks *)
Definition UnionFind.wf {K} (E : encoding K) (uf : UnionFind.t K) : Prop.
Definition UnionFind.of_unions {K} (E : encoding K) (l : list (K * K)) : UnionFind.t K :=
  List.fold_left (fun uf xy => UnionFind.union E (fst xy) (snd xy) uf) l UnionFind.make.
```

`UnionFind.find` follows parent links with fuel `S (max_rank uf)`. A key with no parent is a root.
Otherwise it recurses with one unit less and, on return, sets the parent of the current key to the
root found (path compression). When the fuel runs out it returns the current key and the structure
unchanged; a well-formed structure never runs out, because ranks strictly increase along parent
links and are at most `max_rank`, so a path has at most `max_rank` links. `UnionFind.wf E uf`
says: `Map.wf E` holds for `parents uf` and for `ranks uf`; every rank is at most `max_rank uf`;
and, reading an absent rank as 0, the rank of a key is strictly below the rank of its parent
(acyclicity follows).

`UnionFind.union E x y uf` finds both representatives `rx` and `ry`. If they are equal it records
`rx` in the support (rank 0 if new) and returns the structure after the two finds. Otherwise it
links by rank: the lower rank goes below the higher; on equal ranks `ry` goes below `rx` and the
rank of `rx` grows by one, so the representative is a deterministic function of the call
sequence. `max_rank` becomes the larger of its old value and any rank written.

### Tables (`CollectionsTable.v`)

A table maps a `list positive` to a value; hash-consing uses it to map an operator code followed by
operand numbers to a node number. It is a flat `Map` keyed by the list encoding, and every
operation is the `Map` operation at that encoding:

```coq
Definition Table.key : encoding (list positive) := list_encoding positive_encoding.
Definition Table.t (V : Type) : Type := Map.t (list positive) V.
Definition Table.empty {V} : Table.t V := Map.empty.
Definition Table.wf {V} (t : Table.t V) : Prop := Map.wf Table.key t.
(* a flat map has no nodes, so there is no root to exempt: the empty list is an ordinary key *)
Definition Table.get {V} (k : list positive) (t : Table.t V) : option V := Map.get Table.key k t.
Definition Table.set {V} (k : list positive) (v : V) (t : Table.t V) : Table.t V :=
  Map.set Table.key k v t.
Definition Table.remove {V} (k : list positive) (t : Table.t V) : Table.t V :=
  Map.remove Table.key k t.
Definition Table.is_empty {V} (t : Table.t V) : bool := Map.is_empty t.
Definition Table.fold {V B} (f : B -> list positive -> V -> B) (t : Table.t V) (b : B) : B :=
  Map.fold f t b.
Definition Table.elements {V} (t : Table.t V) : list (list positive * V) := Map.elements t.
Definition Table.size {V} (t : Table.t V) : nat := Map.size t.
```

`Table.elements` lists the bindings in the trie order of the list codes, not in lexicographic order
of the keys. Keys that share a prefix share no structure.

## Theorems

Each group sits in a `Section` whose `Context` and `Variables` lines declare the types and
variables it mentions; a theorem is generalised over exactly the ones it uses, in declaration
order. A `(* Proof idea ... Card ... *)` line follows each group of theorems.

### Tries

```coq
Section TrieLaws.
Context {A B C : Type}.
Variables (t t1 t2 : Trie.t A) (u : Trie.t B) (p q : positive) (v : A)
  (f : option A -> option B -> option C).

(** Two tries with the same bindings are equal: the representation is canonical. *)
Theorem Trie.extensionality : (forall p, Trie.get p t1 = Trie.get p t2) -> t1 = t2.
(* Proof idea: induction on both trees; the seven shapes are fixed by get at xH, xO _, xI _.
   Card: COL-1b. *)

(** An empty trie binds nothing, and a trie that binds nothing is the empty trie. *)
Theorem Trie.get_empty : Trie.get p (@Trie.empty A) = None.
Theorem Trie.is_empty_spec : Trie.is_empty t = true <-> t = Trie.empty.
(* Proof idea: unfolding; the second by canonicity. Card: COL-1b. *)

(** Lookup after update. *)
Theorem Trie.get_set_same : Trie.get p (Trie.set p v t) = Some v.
Theorem Trie.get_set_other : p <> q -> Trie.get q (Trie.set p v t) = Trie.get q t.
Theorem Trie.get_remove_same : Trie.get p (Trie.remove p t) = None.
Theorem Trie.get_remove_other : p <> q -> Trie.get q (Trie.remove p t) = Trie.get q t.
(* Proof idea: induction on the path p, splitting on the node shape. Card: COL-1b. *)

(** Mapping and combining act position by position; combining needs f None None = None. *)
Theorem Trie.get_map : forall (g : A -> B), Trie.get p (Trie.map g t) = option_map g (Trie.get p t).
Theorem Trie.get_combine : f None None = None ->
  Trie.get p (Trie.combine f t u) = f (Trie.get p t) (Trie.get p u).
(* Proof idea: induction on both tries, rebuilding through a constructor that drops empty subtrees.
   Card: COL-1b. *)

(** The elements are the bindings, each once, in trie order. *)
Theorem Trie.elements_sound : In (p, v) (Trie.elements t) -> Trie.get p t = Some v.
Theorem Trie.elements_complete : Trie.get p t = Some v -> In (p, v) (Trie.elements t).
Theorem Trie.elements_nodup : NoDup (List.map fst (Trie.elements t)).
Theorem Trie.elements_sorted :
  StronglySorted (fun a b => Trie.key_lt (fst a) (fst b)) (Trie.elements t).
(* Proof idea: induction on the shapes; xO-keys precede the root key, which precedes xI-keys.
   Card: COL-1b. *)

(** Folding visits the elements in order; the size counts them. *)
Theorem Trie.fold_elements : forall (g : B -> positive -> A -> B) (b : B),
  Trie.fold g t b = List.fold_left (fun acc pv => g acc (fst pv) (snd pv)) (Trie.elements t) b.
Theorem Trie.size_elements : Trie.size t = List.length (Trie.elements t).
(* Proof idea: induction on the shapes, with an accumulator for the fold. Card: COL-1b. *)

(** Structural comparison compares the bindings position by position, whatever `eqb` is; with an
    `eqb` that decides equality it is equality of tries. *)
Theorem Trie.beq_pointwise : forall (eqb : A -> A -> bool),
  Trie.beq eqb t1 t2 = true <-> forall p, match Trie.get p t1, Trie.get p t2 with
    | None, None => True | Some a, Some b => eqb a b = true | _, _ => False end.
Theorem Trie.beq_correct : forall (eqb : A -> A -> bool),
  (forall a b, eqb a b = true <-> a = b) -> (Trie.beq eqb t1 t2 = true <-> t1 = t2).
(* Proof idea: beq_pointwise by induction on both trees, with no assumption on eqb; beq_correct
   from beq_pointwise and Trie.extensionality. Card: COL-1b. *)

(** Subset tests and unions without rebuilding: `forall2` tests the bindings of the first trie
    against the second; `union_with` binds each position by `union_opt`, sharing one-sided subtrees. *)
Theorem Trie.forall2_spec : forall (r : A -> option B -> bool),
  Trie.forall2 r t u = true <-> forall (p : positive) (a : A), Trie.get p t = Some a ->
  r a (Trie.get p u) = true.
Theorem Trie.get_union_with : forall (f : A -> A -> A),
  Trie.get p (Trie.union_with f t t1) = Trie.union_opt f (Trie.get p t) (Trie.get p t1).
Theorem Trie.union_with_combine : forall (f : A -> A -> A),
  Trie.union_with f t t1 = Trie.combine (Trie.union_opt f) t t1.
(* Proof idea: induction on both tries; the last by Trie.extensionality, since union_opt f None None
   is None. Card: COL-1b. *)
End TrieLaws.
```

### Maps

```coq
Section MapLaws.
Context {K V W U : Type} (E : encoding K).
Variables (k k1 k2 : K) (v : V) (m m' : Map.t K V) (n : Map.t K W).

(** The position-level API: it reads the trie by code and never decodes a key, so these laws hold
    for every map, well formed or not. `Map.get` is `Map.code_get` at the code of the key. *)
Theorem Map.get_code : Map.get E k m = Map.code_get (encode E k) m.
Theorem Map.code_get_empty : forall p, Map.code_get p (@Map.empty K V) = None.
Theorem Map.code_get_combine : forall (f : option V -> option W -> option U) (p : positive),
  f None None = None ->
  Map.code_get p (Map.combine E f m n) = f (Map.code_get p m) (Map.code_get p n).
Theorem Map.code_get_union_with : forall (f : V -> V -> V) (p : positive),
  Map.code_get p (Map.union_with f m m') = Trie.union_opt f (Map.code_get p m) (Map.code_get p m').
Theorem Map.forall2_spec : forall (r : V -> option W -> bool),
  Map.forall2 r m n = true <-> forall (p : positive) (v : V), Map.code_get p m = Some v ->
  r v (Map.code_get p n) = true.
Theorem Map.wf_union_with : forall (f : V -> V -> V), Map.wf E m -> Map.wf E m' ->
  Map.wf E (Map.union_with f m m').
Theorem Map.mem_spec : Map.mem E k m = true <-> Map.get E k m <> None.
Theorem Map.is_empty_spec : Map.wf E m -> (Map.is_empty m = true <-> forall k, Map.get E k m = None).
(* Proof idea: Map.get_code is the definition; the others are Trie.get_combine, Trie.get_union_with
   and Trie.forall2_spec on the stored pairs, with the key dropped by snd; is_empty_spec by
   Trie.is_empty_spec, since wf puts a stored key at its code. Card: COL-1c. *)

(** Every operation keeps stored keys at their codes. *)
Theorem Map.wf_empty : Map.wf E (@Map.empty K V).
Theorem Map.wf_set : Map.wf E m -> Map.wf E (Map.set E k v m).
Theorem Map.wf_remove : Map.wf E m -> Map.wf E (Map.remove E k m).
Theorem Map.wf_map : forall (f : V -> W), Map.wf E m -> Map.wf E (Map.map f m).
Theorem Map.wf_combine : forall (f : option V -> option W -> option U),
  Map.wf E m -> Map.wf E n -> Map.wf E (Map.combine E f m n).
Theorem Map.wf_of_list : forall (l : list (K * V)), Map.wf E (Map.of_list E l).
(* Proof idea: Trie.get_set_*, Trie.get_combine at a position, then encode_injective.
   Card: COL-1c. *)

(** Lookup after update; these hold for every map, well-formed or not. *)
Theorem Map.get_empty : Map.get E k (@Map.empty K V) = None.
Theorem Map.get_set_same : Map.get E k (Map.set E k v m) = Some v.
Theorem Map.get_set_other : k1 <> k2 -> Map.get E k1 (Map.set E k2 v m) = Map.get E k1 m.
Theorem Map.get_remove_same : Map.get E k (Map.remove E k m) = None.
Theorem Map.get_remove_other : k1 <> k2 -> Map.get E k1 (Map.remove E k2 m) = Map.get E k1 m.
Theorem Map.get_map : forall (f : V -> W), Map.get E k (Map.map f m) = option_map f (Map.get E k m).
Theorem Map.get_combine : forall (f : option V -> option W -> option U), f None None = None ->
  Map.get E k (Map.combine E f m n) = f (Map.get E k m) (Map.get E k n).
Theorem Map.get_of_list : forall (l : list (K * V)), Map.get E k (Map.of_list E l) =
  option_map snd (List.find (fun kv => Pos.eqb (encode E (fst kv)) (encode E k)) (List.rev l)).
(* Proof idea: unfold to Trie.get at encode E k; the _other laws use encode_injective.
   Card: COL-1c. *)

(** Well-formed maps with the same lookups are equal. *)
Theorem Map.extensionality :
  Map.wf E m -> Map.wf E m' -> (forall k, Map.get E k m = Map.get E k m') -> m = m'.
(* Proof idea: a stored (k, v) sits at encode E k, so the other map stores the same pair
   there; then Trie.extensionality. Card: COL-1c. *)

(** Elements list each binding of a well-formed map once; fold is a fold over them. *)
Theorem Map.elements_sound : Map.wf E m -> In (k, v) (Map.elements m) -> Map.get E k m = Some v.
Theorem Map.elements_complete : Map.wf E m -> Map.get E k m = Some v -> In (k, v) (Map.elements m).
Theorem Map.elements_nodup : Map.wf E m -> NoDup (List.map fst (Map.elements m)).
Theorem Map.fold_elements : forall (B : Type) (f : B -> K -> V -> B) (b : B),
  Map.fold f m b = List.fold_left (fun acc kv => f acc (fst kv) (snd kv)) (Map.elements m) b.
Theorem Map.size_elements : Map.size m = List.length (Map.elements m).
(* Proof idea: from the Trie versions; well-formedness identifies stored keys with codes.
   Card: COL-1c. *)

(** Comparing values position by position is equality of lookups, for well-formed maps. *)
Theorem Map.beq_correct : forall (eqb : V -> V -> bool), (forall a b, eqb a b = true <-> a = b) ->
  Map.wf E m -> Map.wf E m' -> (Map.beq eqb m m' = true <-> forall k, Map.get E k m = Map.get E k m').
(* Proof idea: Trie.beq_pointwise on the stored pairs; wf puts every stored key at its code, so a
   position bound in one map is bound in the other with the same lookups. Card: COL-1c. *)
End MapLaws.
```

### Finite sets

```coq
Section FinSetLaws.
Context {K : Type} (E : encoding K).
Variables (k k1 k2 : K) (s s1 s2 s3 : FinSet.t K) (l : list K) (p : positive).

(** Membership laws, each unconditional. *)
Theorem FinSet.mem_empty : FinSet.mem E k (@FinSet.empty K) = false.
Theorem FinSet.mem_add : FinSet.mem E k1 (FinSet.add E k2 s) = true <-> k1 = k2 \/ FinSet.mem E k1 s = true.
Theorem FinSet.mem_remove : FinSet.mem E k1 (FinSet.remove E k2 s) = true <-> k1 <> k2 /\ FinSet.mem E k1 s = true.
Theorem FinSet.mem_union : FinSet.mem E k (FinSet.union E s1 s2) = true <->
  FinSet.mem E k s1 = true \/ FinSet.mem E k s2 = true.
Theorem FinSet.mem_inter : FinSet.mem E k (FinSet.inter E s1 s2) = true <->
  FinSet.mem E k s1 = true /\ FinSet.mem E k s2 = true.
Theorem FinSet.mem_diff : FinSet.mem E k (FinSet.diff E s1 s2) = true <->
  FinSet.mem E k s1 = true /\ FinSet.mem E k s2 = false.
Theorem FinSet.of_list_spec : FinSet.mem E k (FinSet.of_list E l) = true <-> In k l.
(* Proof idea: the Map.get_* laws and encode_injective. Card: COL-1c. *)

(** Every set operation keeps well-formedness. *)
Theorem FinSet.wf_ops : FinSet.wf E s1 -> FinSet.wf E s2 ->
  FinSet.wf E (@FinSet.empty K) /\ FinSet.wf E (FinSet.add E k s1) /\ FinSet.wf E (FinSet.remove E k s1) /\
  FinSet.wf E (FinSet.union E s1 s2) /\ FinSet.wf E (FinSet.inter E s1 s2) /\ FinSet.wf E (FinSet.diff E s1 s2) /\
  FinSet.wf E (FinSet.of_list E l).
(* Proof idea: the Map.wf_* theorems. Card: COL-1c. *)

(** Well-formed sets with the same members are equal; subset is inclusion of members. *)
Theorem FinSet.extensionality :
  FinSet.wf E s1 -> FinSet.wf E s2 -> (forall k, FinSet.mem E k s1 = FinSet.mem E k s2) -> s1 = s2.
Theorem FinSet.subset_spec : FinSet.wf E s1 ->
  (FinSet.subset E s1 s2 = true <-> forall k, FinSet.mem E k s1 = true -> FinSet.mem E k s2 = true).
(* Proof idea: Map.extensionality (unit has one value); subset_spec from FinSet.subset_code,
   since wf puts every stored key of s1 at its code.
   Card: COL-1c. *)

(** Elements are the members, once each; the size counts them. *)
Theorem FinSet.elements_spec : FinSet.wf E s -> (In k (FinSet.elements s) <-> FinSet.mem E k s = true).
Theorem FinSet.elements_nodup : FinSet.wf E s -> NoDup (FinSet.elements s).
Theorem FinSet.size_elements : FinSet.size s = List.length (FinSet.elements s).
(* Proof idea: from Map.elements_*. Card: COL-1c. *)

(** The position-level API: membership, union, intersection, difference and subset read one
    position, for every set, well formed or not. *)
Theorem FinSet.mem_code : FinSet.mem E k s = true <-> Map.code_get (encode E k) s <> None.
Theorem FinSet.union_code : Map.code_get p (FinSet.union E s1 s2) <> None <->
  Map.code_get p s1 <> None \/ Map.code_get p s2 <> None.
Theorem FinSet.inter_code : Map.code_get p (FinSet.inter E s1 s2) <> None <->
  Map.code_get p s1 <> None /\ Map.code_get p s2 <> None.
Theorem FinSet.diff_code : Map.code_get p (FinSet.diff E s1 s2) <> None <->
  Map.code_get p s1 <> None /\ Map.code_get p s2 = None.
Theorem FinSet.subset_code : FinSet.subset E s1 s2 = true <->
  forall p, Map.code_get p s1 <> None -> Map.code_get p s2 <> None.
(* Proof idea: unfolding mem; Map.code_get_union_with and Map.code_get_combine; Map.forall2_spec for
   subset, the unit value being discarded. Card: COL-1c. *)

(** Emptiness and size: a well-formed set with no member is empty; inclusion bounds the size, and
    strictly when it is proper; a set inside a universe is no larger than the universe. *)
Theorem FinSet.is_empty_spec : FinSet.wf E s -> (FinSet.is_empty s = true <-> forall k, FinSet.mem E k s = false).
Theorem FinSet.size_subset : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.subset E s1 s2 = true ->
  FinSet.size s1 <= FinSet.size s2.
Theorem FinSet.size_lt : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.subset E s1 s2 = true ->
  FinSet.subset E s2 s1 = false -> FinSet.size s1 < FinSet.size s2.
Theorem FinSet.size_le_length : forall U : list K, FinSet.wf E s1 ->
  (forall k, FinSet.mem E k s1 = true -> In k U) -> FinSet.size s1 <= List.length U.
(* Proof idea: Map.is_empty_spec; the size is the length of the elements, which are NoDup and are
   exactly the members (FinSet.elements_spec); NoDup_incl_length, adding one member outside s1 for the
   strict case. Card: COL-1c. *)

(** The algebra of well-formed sets, as equalities. *)
Theorem FinSet.union_comm : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.union E s1 s2 = FinSet.union E s2 s1.
Theorem FinSet.union_assoc : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.wf E s3 ->
  FinSet.union E s1 (FinSet.union E s2 s3) = FinSet.union E (FinSet.union E s1 s2) s3.
Theorem FinSet.union_idem : FinSet.wf E s -> FinSet.union E s s = s.
Theorem FinSet.union_empty_r : FinSet.wf E s -> FinSet.union E s FinSet.empty = s.
Theorem FinSet.inter_comm : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.inter E s1 s2 = FinSet.inter E s2 s1.
Theorem FinSet.inter_assoc : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.wf E s3 ->
  FinSet.inter E s1 (FinSet.inter E s2 s3) = FinSet.inter E (FinSet.inter E s1 s2) s3.
Theorem FinSet.inter_idem : FinSet.wf E s -> FinSet.inter E s s = s.
Theorem FinSet.inter_empty_r : FinSet.wf E s -> FinSet.inter E s FinSet.empty = FinSet.empty.
Theorem FinSet.inter_union_distr : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.wf E s3 ->
  FinSet.inter E s1 (FinSet.union E s2 s3) = FinSet.union E (FinSet.inter E s1 s2) (FinSet.inter E s1 s3).
Theorem FinSet.union_inter_absorb : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.union E s1 (FinSet.inter E s1 s2) = s1.
Theorem FinSet.diff_self : FinSet.wf E s -> FinSet.diff E s s = FinSet.empty.
(* Proof idea: FinSet.extensionality after FinSet.wf_ops, then Boolean reasoning on FinSet.mem_*.
   Card: COL-1c. *)
End FinSetLaws.
```

### Priority queue

```coq
Section PQueueLaws.
Context {K : Type} (E : encoding K).
Variables (q q' : PQueue.t K) (p p2 : positive) (k k1 k2 : K).

(** The empty queue is well formed and holds no key. *)
Theorem PQueue.wf_empty : PQueue.wf E (@PQueue.empty K).
Theorem PQueue.priority_empty : PQueue.priority E k (@PQueue.empty K) = None.
(* Proof idea: unfolding the empty heap and the empty live map. Card: COL-2. *)

(** Push keeps the smaller priority of a present key and leaves other keys alone. *)
Theorem PQueue.priority_push_same : PQueue.wf E q -> PQueue.priority E k (PQueue.push E p k q) =
  Some (match PQueue.priority E k q with None => p | Some p0 => Pos.min p0 p end).
Theorem PQueue.priority_push_other : PQueue.wf E q -> k1 <> k2 ->
  PQueue.priority E k1 (PQueue.push E p k2 q) = PQueue.priority E k1 q.
Theorem PQueue.size_push_new : PQueue.wf E q -> PQueue.priority E k q = None ->
  PQueue.size (PQueue.push E p k q) = S (PQueue.size q).
Theorem PQueue.size_push_old : PQueue.wf E q -> PQueue.priority E k q <> None ->
  PQueue.size (PQueue.push E p k q) = PQueue.size q.
Theorem PQueue.wf_push : PQueue.wf E q -> PQueue.wf E (PQueue.push E p k q).
(* Proof idea: binomial-heap insertion plus a live-map update; a lowering push adds one entry
   and makes the old one stale. Card: COL-2. *)

(** Pop fails exactly on an empty queue. *)
Theorem PQueue.pop_none : PQueue.wf E q -> (PQueue.pop E q = None <-> PQueue.is_empty q = true).
(** Pop returns a key of minimal (priority, code) and removes exactly that key. *)
Theorem PQueue.pop_min : PQueue.wf E q -> PQueue.pop E q = Some (p, k, q') ->
  PQueue.priority E k q = Some p /\
  forall (k2 : K) (p2 : positive), PQueue.priority E k2 q = Some p2 ->
    PQueue.before p (encode E k) p2 (encode E k2).
Theorem PQueue.pop_rest : PQueue.wf E q -> PQueue.pop E q = Some (p, k, q') ->
  PQueue.priority E k q' = None /\
  (forall k2 : K, k2 <> k -> PQueue.priority E k2 q' = PQueue.priority E k2 q) /\
  PQueue.size q = S (PQueue.size q').
Theorem PQueue.wf_pop : PQueue.wf E q -> PQueue.pop E q = Some (p, k, q') -> PQueue.wf E q'.
(* Proof idea: discard heap tops that disagree with the live map, then merge the subheaps of the
   first top that agrees. Card: COL-2. *)

(** The held pairs are the live map, once per key, and their number is the size. *)
Theorem PQueue.members_spec : PQueue.wf E q ->
  (In (k, p) (PQueue.members q) <-> PQueue.priority E k q = Some p).
Theorem PQueue.members_nodup : PQueue.wf E q -> NoDup (List.map fst (PQueue.members q)).
Theorem PQueue.size_members : PQueue.wf E q -> PQueue.size q = List.length (PQueue.members q).
Theorem PQueue.is_empty_spec : PQueue.wf E q ->
  (PQueue.is_empty q = true <-> forall k, PQueue.priority E k q = None).
(* Proof idea: members is Map.elements of the live map; Map.elements_* and wf link the counter. Card: COL-2. *)
End PQueueLaws.
```

### Union-find

```coq
Section UnionFindLaws.
Context {K : Type} (E : encoding K).
Variables (uf : UnionFind.t K) (x y z a b : K) (l : list (K * K)).

(** Equivalence is an equivalence relation, whatever the structure. *)
Theorem UnionFind.equiv_equivalence : equivalence K (UnionFind.equiv E uf).
(* Proof idea: equality of representatives. Card: COL-2. *)

(** Every operation keeps the structure well formed. *)
Theorem UnionFind.wf_make : UnionFind.wf E (@UnionFind.make K).
Theorem UnionFind.wf_find : UnionFind.wf E uf -> UnionFind.wf E (snd (UnionFind.find E x uf)).
Theorem UnionFind.wf_union : UnionFind.wf E uf -> UnionFind.wf E (UnionFind.union E x y uf).
(* Proof idea: compression redirects a node to an ancestor, which has a larger rank; linking
   raises a rank only on a tie. Card: COL-2. *)

(** Finding never changes anyone's representative, and a representative represents itself:
    representatives are canonical. *)
Theorem UnionFind.find_rep_stable : UnionFind.wf E uf ->
  fst (UnionFind.find E x (snd (UnionFind.find E y uf))) = fst (UnionFind.find E x uf).
Theorem UnionFind.find_rep_canonical : UnionFind.wf E uf ->
  fst (UnionFind.find E (fst (UnionFind.find E x uf)) uf) = fst (UnionFind.find E x uf).
(* Proof idea: the root reached from x is the root reached from every node on its path. Card: COL-2. *)

(** A fresh structure relates only equal keys; union merges exactly the classes of its arguments. *)
Theorem UnionFind.make_equiv : UnionFind.equiv E UnionFind.make a b <-> a = b.
Theorem UnionFind.union_equiv : UnionFind.wf E uf ->
  (UnionFind.equiv E (UnionFind.union E x y uf) a b <->
   UnionFind.equiv E uf a b \/
   (UnionFind.equiv E uf a x /\ UnionFind.equiv E uf y b) \/
   (UnionFind.equiv E uf a y /\ UnionFind.equiv E uf x b)).
(* Proof idea: the linked root becomes the representative of both classes; other roots stay. Card: COL-2. *)

(** Equivalence is the equivalence closure of the unions performed. *)
Theorem UnionFind.of_unions_equiv : UnionFind.equiv E (UnionFind.of_unions E l) a b <->
  clos_refl_sym_trans K (fun x y => In (x, y) l) a b.
(* Proof idea: induction on l from the right with make_equiv, union_equiv and wf_union. Card: COL-2. *)

(** The boolean test agrees with equiv and returns an equivalent structure. *)
Theorem UnionFind.equivb_correct : UnionFind.wf E uf ->
  (fst (UnionFind.equivb E x y uf) = true <-> UnionFind.equiv E uf x y) /\
  UnionFind.wf E (snd (UnionFind.equivb E x y uf)) /\
  (forall a b, UnionFind.equiv E (snd (UnionFind.equivb E x y uf)) a b <-> UnionFind.equiv E uf a b).
(* Proof idea: two finds, then find_rep_stable and wf_find. Card: COL-2. *)

(** Keys outside the support are alone in their class; the support is exactly the unioned keys,
    each once. *)
Theorem UnionFind.keys_support : UnionFind.wf E uf -> ~ In x (UnionFind.keys E uf) ->
  UnionFind.equiv E uf x y -> y = x.
Theorem UnionFind.keys_make : UnionFind.keys E (@UnionFind.make K) = nil.
Theorem UnionFind.keys_union : UnionFind.wf E uf ->
  (In z (UnionFind.keys E (UnionFind.union E x y uf)) <-> z = x \/ z = y \/ In z (UnionFind.keys E uf)).
Theorem UnionFind.keys_nodup : UnionFind.wf E uf -> NoDup (UnionFind.keys E uf).
(* Proof idea: a key has a parent or rank entry exactly after it is unioned, and a parent has a
   positive rank, so it has a rank entry; the key sets are FinSet.wf by Map.wf, so the union's
   elements are NoDup. Card: COL-2. *)
End UnionFindLaws.
```

### Tables

```coq
Section TableLaws.
Context {V : Type}.
Variables (t t' : Table.t V) (k k1 k2 : list positive) (v : V).

(** Lookup after update, for every table. *)
Theorem Table.get_empty : Table.get k (@Table.empty V) = None.
Theorem Table.get_set_same : Table.get k (Table.set k v t) = Some v.
Theorem Table.get_set_other : k1 <> k2 -> Table.get k1 (Table.set k2 v t) = Table.get k1 t.
Theorem Table.get_remove_same : Table.get k (Table.remove k t) = None.
Theorem Table.get_remove_other : k1 <> k2 -> Table.get k1 (Table.remove k2 t) = Table.get k1 t.
(* Proof idea: the Map laws at Table.key. Card: COL-2. *)

(** Well-formedness is preserved, and well-formed tables with equal lookups are equal. *)
Theorem Table.wf_empty : Table.wf (@Table.empty V).
Theorem Table.wf_set : Table.wf t -> Table.wf (Table.set k v t).
Theorem Table.wf_remove : Table.wf t -> Table.wf (Table.remove k t).
Theorem Table.extensionality :
  Table.wf t -> Table.wf t' -> (forall k, Table.get k t = Table.get k t') -> t = t'.
(* Proof idea: Map.wf_empty, Map.wf_set, Map.wf_remove and Map.extensionality. Card: COL-2. *)

(** Elements list each binding of a well-formed table once; fold, size and emptiness follow. *)
Theorem Table.elements_sound : Table.wf t -> In (k, v) (Table.elements t) -> Table.get k t = Some v.
Theorem Table.elements_complete : Table.wf t -> Table.get k t = Some v -> In (k, v) (Table.elements t).
Theorem Table.elements_nodup : Table.wf t -> NoDup (List.map fst (Table.elements t)).
Theorem Table.fold_elements : forall (B : Type) (f : B -> list positive -> V -> B) (b : B),
  Table.fold f t b = List.fold_left (fun acc kv => f acc (fst kv) (snd kv)) (Table.elements t) b.
Theorem Table.size_elements : Table.size t = List.length (Table.elements t).
Theorem Table.is_empty_spec : Table.wf t -> (Table.is_empty t = true <-> forall k, Table.get k t = None).
(* Proof idea: Map.elements_sound, Map.elements_complete, Map.elements_nodup, Map.fold_elements,
   Map.size_elements and Map.is_empty_spec. Card: COL-2. *)
End TableLaws.
```

## Algorithms and references

- **Tries.** Little-endian radix-2 tries: a key is consumed least-significant bit first, as in
  Okasaki and Gill, "Fast mergeable integer maps" (ML Workshop 1998), but with fixed-depth paths
  and no prefix compression. The seven-shape canonical form makes empty subtrees unrepresentable.
  `Trie.combine` recurses on both tries at once and rebuilds a node only through a smart
  constructor that drops empty children. `Trie.union_with` is Okasaki and Gill's `merge`: a subtree
  present in one trie only is returned as it is. `Trie.forall2` is a short-circuit walk of the
  first trie that follows the second trie only along the paths of the first.
- **Encodings.** An injective code into `positive`, as `Countable` in std++ (Krebbers et al.);
  pairs and lists use a self-delimiting prefix code (doubled bits, then a delimiter).
- **Priority queue.** A rank-position binomial heap ordered by `(priority, code)`. Lowering a
  priority uses lazy deletion: the old entry stays in the heap and `pop` skips an entry that
  disagrees with the live map.
- **Union-find.** Union by rank and path compression (Tarjan, "Efficiency of a good but not linear
  set union algorithm", JACM 1975; Tarjan and van Leeuwen, JACM 1984), made persistent with
  tries in place of arrays (compare Conchon and Filliâtre, "A persistent union-find data
  structure", ML Workshop 2007). The correctness argument follows Charguéraud and Pottier (JAR
  2019),
  stated here on a functional model. `find` takes fuel `S max_rank`, which the rank invariant makes
  sufficient.
- **Tables.** A flat `Map` keyed by `list_encoding positive_encoding`; hash-consing as in
  Filliâtre and Conchon, "Type-safe modular hash-consing", ML Workshop 2006.

## Performance notes

- A trie of `n` bindings whose codes have at most `b` bits has at most `n * b` nodes. Count each
  constructor and branch as a unit operation, separately from work done by supplied functions.
  `Trie.get`, `set` and `remove` cost O(bits of the key); `Trie.combine`, `map`, `beq` and `size`
  cost O(nodes), plus supplied-function work. For two inputs, nodes counts both input tries.
  For `Trie.fold` and `Trie.elements`, let `N` be the number of visited nodes and `L` the sum of
  the bit lengths of the emitted positive keys. Their cost is O(N + L), plus fold callback work.
  `Trie.elements` builds its list with an accumulator (no left-nested append). `Trie.size` is not
  cached; `PQueue.size` is.
- `Trie.forall2` costs at most O(nodes of `t1`) and stops at the first failure; `Trie.union_with`
  costs O(1 + the number of node positions present in both tries), because a one-sided subtree is
  shared in O(1). Both bounds exclude supplied-function work. `FinSet.subset` is one
  `Trie.forall2` (no difference trie is built) and
  `FinSet.union` is one `Trie.union_with`.
- `Map.get`, `set` and `remove` add one `encode`. Prepared index: `Map.wf`, with
  `Map.elements_sound` and `Map.elements_complete` as the agreement lemmas between the trie and the
  key view; `Map.code_get` is the same index read by position.
- With `n` pending heap entries, `PQueue.push` takes O(log(2 + n)) structural heap work and
  O(log(2 + n)) priority/code comparisons, plus a constant number of live-map operations. `pop`
  takes O((1 + d) log(2 + n)) structural heap work and priority/code comparisons, and O(1 + d)
  live-map operations when it discards `d` stale entries, with fuel equal to the entry count.
  Structural work counts constructors and branches; comparison, encoding and live-map costs are
  separate. A positive priority/code comparison may inspect O(bit lengths) bits.
  These are per-call bounds, including on persistent branches, with no amortised bound claimed.
  Prepared index: the live map and counters, with `PQueue.members_spec` and
  `PQueue.size_members` as the agreement lemmas.
- `UnionFind.find` is O(log n) by the rank bound on a single call. Path compression pays off only
  when the client threads the returned structure; `equivb` returns it for that purpose.
- `Table.get` and `Table.set` cost one `encode` of the key plus O(bits of its code). No complexity
  statement in this document is a theorem.

## Open questions

1. **Element order.** `Map.elements` follows `Trie.key_lt` on codes, not the order of keys. A client
   that needs numeric order of keys must sort. Whether to pin the pair and list codes exactly is
   open; pinning makes order portable but forbids improvements.
2. **Added to the anchors:** `Trie.is_empty`, `Map.size/is_empty/mem/of_list/map/beq`,
   `FinSet.is_empty`, `PQueue.priority/members/wf/before`,
   `UnionFind.make/equivb/keys/wf/of_unions`,
   and the `Table` operations. `UnionFind.keys` exists for the join of equality partitions (DOM-7).
3. **`Map.t` stores each key** beside its value so that `elements` needs no decoder. The cost is one
   extra word per binding; the alternative is an `encoding` with a decode function.
4. **Lazy deletion** lets stale heap entries accumulate under many priority decreases; a position
   map for a true decrease-key would avoid it at higher proof cost.

## Cross-document contracts

The collection modules are `Map`, `FinSet`, `PQueue`, `UnionFind` and `Table`.
`UnionFind.keys` takes its encoding, and its support and union laws require well-formedness.
Order uses the position-level map API and the trie-based set operations.
