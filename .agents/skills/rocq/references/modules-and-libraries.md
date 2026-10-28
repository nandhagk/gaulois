# Modules and library interfaces

## Contents

- [Expose the carrier your clients need](#expose-the-carrier-your-clients-need)
- [Treat aliases as APIs](#treat-aliases-as-apis)
- [Use manifest equalities intentionally](#use-manifest-equalities-intentionally)
- [Group refinements in module headers](#group-refinements-in-module-headers)
- [Pilot interfaces with clients](#pilot-interfaces-with-clients)
- [Separate metadata from control](#separate-metadata-from-control)
- [Use primitive projections conditionally](#use-primitive-projections-conditionally)
- [Keep import and export boundaries explicit](#keep-import-and-export-boundaries-explicit)
- [Instances and comparators](#resolve-instances-and-comparators-at-their-source)
- [Nested induction principles](#inspect-induction-principles-for-nested-containers)
- [Mathematical libraries](#interoperate-with-mathematical-libraries-deliberately)

## Expose the carrier your clients need

Use `Inductive` when the constructors and their eliminators are part of the public
meaning of a type. Use a `Parameter` or an abstract module signature when clients
should reason only through declared operations and laws. Do not choose abstraction
solely to hide a large implementation if clients need to destruct the value or
compute over its constructors.

Keep the signature at the narrowest useful level. Expose a carrier, operations,
and laws that support clients' proofs; keep representation and helper definitions
private when clients do not need them. An abstract carrier may still have a
computable realization in a module implementation, but clients cannot rely on
hidden representation equations unless the signature provides them.

Before changing a concrete carrier into an abstract one, search for clients that
pattern-match on it, depend on its constructor shape, or use its generated
induction principle. Replace those dependencies with explicit interface lemmas
only when the abstraction preserves the intended semantics and the migration is
within scope.

## Treat aliases as APIs

An abbreviation may preserve the same type while changing what names and
notations are available to a client. Read an alias's definition and imports;
do not infer its behavior from its name. Check whether it exposes a constructor,
re-exports a notation, adds a coercion, or changes implicit-argument inference.

When a proof fails after an alias or import change, compare the elaborated types
and selected constants before changing the theorem. An unchanged proof can now
refer to a different short name or parse under another scope. Qualify the owner
or import the intended interface rather than adding a broad notation import.

## Use manifest equalities intentionally

A module signature can expose definitional equalities with `Definition` fields
while hiding implementation values behind abstract fields. Use manifest types
when clients need conversion between a member's carrier and a shared carrier.
Use abstract types when clients must not rely on representation equality. State the
needed equality at the signature boundary; do not expect clients to unfold a
hidden functor body to recover it.

Inspect the exact signature and application when type equality fails. Rocq
module type identity is observable through the declarations used to expose the
carrier, the module path that names it, signature sealing, and any manifest
equalities. Inspect those declarations and ask Rocq for the actual inferred
types at a scratch boundary. Do not infer sharing or separation merely from a
functor-shaped declaration, or extrapolate from a different application.

If a module match fails, distinguish a mismatch in type identity, constructor
shape, included fields, or a required law. Repair the smallest interface that
expresses the intended sharing. A coercion or equality proof can bridge
representations only when the underlying types are related as claimed.

## Group refinements in module headers

Parenthesize a refined module type in an outer signature constraint, so that the
refinement's `:=` stays distinct from the `:=` that begins an inline module body:

```rocq
Module Type Carrier.
  Parameter t : Type.
End Carrier.

Module Nat_carrier.
  Definition t := nat.
End Nat_carrier.

Module Checked <: (Carrier with Definition t := nat) := Nat_carrier.
```

Keep binder and signature parentheses balanced. A refinement inside binder parentheses
is already grouped. Readers, and tools that scan a header up to its first `:=`, then see
where the constraint ends.

## Pilot interfaces with clients

Share an implementation when its parameters capture genuine common structure
and its result keeps the distinctions clients require. A family functor can
reduce duplicated leaf, checker, interpreter, agreement, or proof code while
each language retains its own syntax and semantics types. Conversely, a
particular module signature/application may incur expensive matching, expose
the wrong type identity to a client, interact poorly with implicit inference,
or break a downstream rewrite.

Pilot a proposed abstraction with representative members and compile actual
clients, including a proof that uses the intended public equality or rewrite
interface. Inspect the resulting types at the declaration and application
boundaries. Measure the costly target if compile time motivates the change.
Keep a local implementation when sharing obscures an important type distinction
or does not reduce maintenance; do not generalize from one blocked match to a
different module interface.

## Separate metadata from control

When a large dependent record carries both data and proof evidence, avoid
rebuilding or reducing the whole package to prove a small change in one field.
State projection equations or observational lemmas at the field boundary, then
transport only the facts that depend on the changed field. Prove whole-record
equality only when clients genuinely require it; extensional equality of
observations may be sufficient.

For a control proof, keep the relevant transition or branch visible and move
unrelated metadata reasoning into a small helper. If a fallback branch repeats
a large continuation, factor the discriminant into a helper that preserves
branch order, error priority, and payload. Prove the helper's equation and test
the overlapping cases; a shorter match is not correct merely because it is
easier to elaborate.

## Use primitive projections conditionally

Primitive projections can make projection reduction predictable and may help
conversion on large records. They can also alter the conversion behavior or
available terms expected by existing clients and libraries. Check the pinned
Rocq version, record declaration, consumers, and extraction behavior before
changing projection style.

Prefer a local projection equation or a narrower record view when only one
proof is expensive. Use a global primitive-projection change when the record
API benefits consistently and representative consumers confirm the change.
Do not treat a projection-optimization flag as a substitute for profiling the
actual bottleneck.

## Keep import and export boundaries explicit

Write one import header at the top of the file, outside every `Module` and `Section`:
first every `Require` (with `From` for a library path), then the `Import`s of modules
the file uses. Group the lines by origin, with the standard library first, then other
libraries, then the project's own, and write one line per directory:

```rocq
From Stdlib.Lists Require Import List.
From Stdlib.ZArith Require Import ZArith.
Import List.ListNotations.
```

Write `Require Import` for a library whose exported names the file uses, and a plain
`Require` when it is needed only for loading or qualification; never `Require` a
library and `Import` it separately. Require or import nothing twice, and import only
the names or notation the file needs. Import a module defined in the file right after
its `End`. Qualify a notation module that several libraries define
(`List.ListNotations`).

Write a name with the shortest unambiguous owner prefix, such as `List.map`; never
spell a full logical path (`Stdlib.Lists.List.map`) in an expression, or a file's own
path inside that file. Avoid unqualified imports that create collisions.

Treat exported modules, definitions, notation, instances, hint databases, and
implicit arguments as API. After moving a definition or changing an import,
compile representative clients and inspect their resolved constants. Do not
hide a breaking API change by retaining an alias whose type identity or
notation behavior differs.

Compiled reference records such as `.glob` provide evidence of particular uses and bindings;
an absent reference does not prove an import unused. Loading a library can activate notation,
hints or instances before a later dependency loads it again. Review first-load effects and
declaration order as well as direct names. Bind reference evidence to the actual source and
compiled artifacts; stale records cannot validate a proposed import rewrite.

## Resolve instances and comparators at their source

When inference selects an unexpected operation, inspect the expected type,
available typeclass instances, scopes, coercions, and local imports. Make the
carrier or instance explicit at the use site when that clarifies the intended
operation. Avoid adding a global instance to make one local goal elaborate;
global instance search can silently change unrelated clients.

For maps, sets, and ordered containers, use the comparator and equality
structure required by the chosen library. Prove comparator laws once at the
boundary if the library expects them. Distinguish structural equality,
key-equivalence, lookup equality, and pointwise behavior. A finite map may
represent the same lookup function with different stored defaults, so use the
equality notion required by the client rather than assuming canonical
representation.

Check canonical-structure unification and typeclass search separately. Inspect the expected
carrier and registered canonical projections when a structure or view fails to infer;
inspect active instances when a class constraint resolves unexpectedly. Make the intended
structure argument explicit locally before adding a global registration.

When bridging mathematical libraries, state the conversion at a named boundary
and preserve its conditions. Natural-to-integer conversion, finite indices,
machine words, and option-valued lookups each have edge behavior; do not use a
conversion as if it were an inverse without proving sign, range, or membership
facts.

## Inspect induction principles for nested containers

Do not assume a generated eliminator recurses through every nested occurrence
of an inductive type. A constructor field such as `list term` may yield an
induction principle without one hypothesis for each list element. Inspect the
generated scheme's type and identify exactly which induction hypotheses it
provides.

If a proof needs recursive evidence under a container, use a supported
container `All` scheme, a mutual scheme, a custom induction principle, or an
induction over explicit container evidence. Keep an existing weak public scheme
when clients rely on its smaller motive; add a separately named stronger scheme
when both interfaces are useful. Check the command syntax and registration
behavior in the pinned Rocq version. In Rocq 9.3, `Scheme All for container`
generates an `All` predicate and `AllForall` theorem, then registers them so
eliminators for types nested through that container can carry recursive
hypotheses. The declarations must be available before the nested inductive is
defined; a missing registered scheme means no nested hypothesis is generated.
See the Rocq 9.3 reference manual:
<https://rocq-prover.org/doc/V9.3.0/refman/proofs/writing-proofs/reasoning-inductives.html>
For another release or a non-inductive container, check its manual and provide
the appropriate `All` interface explicitly when needed.

For indexed or mutually defined judgments, inspect index equalities and the
sort of generated hypotheses before choosing `induction`, `dependent
induction`, or `dependent destruction`. Prefer the least powerful principle
that retains the equation needed by the proof.

## Interoperate with mathematical libraries deliberately

Use the project's established library for each mathematical domain instead of
recreating its notation and algebraic hierarchy. Coq/Rocq developments may
combine Stdlib, MathComp, CompCert, Flocq, and project-local theories; their
coercions, scopes, equality views, and theorem orientations are not
interchangeable by name alone.

At each boundary, make the carrier and scope clear, then use the library's
canonical views or conversion lemmas. For example, a boolean equality test,
a propositional equality, and a MathComp `reflect` view express related but
different interfaces. Bridge them explicitly rather than duplicating a local
boolean inversion tactic or silently changing the equality notion.

Read the imported theorem's type and orientation before rewriting. Prefer a
small interoperability lemma that records the needed bridge, such as a
quotient/remainder equation with an explicit zero-divisor case, over repeated
unfolding of a library implementation. Keep such lemmas near the boundary
between the two mathematical APIs, and avoid introducing global notation or
coercions solely to shorten one proof.
