# Proof construction and debugging

## Contents

- [Find the missing fact](#find-the-missing-fact)
- [Choose the induction motive](#choose-the-induction-motive)
- [Preserve useful equations](#preserve-useful-equations)
- [Handle dependent equality](#handle-dependent-equality)
- [Check sorts and universes](#check-sorts-and-universes)
- [Use reflection and arithmetic deliberately](#use-reflection-and-arithmetic-deliberately)
- [Control automation](#control-automation)
- [Finish and review](#finish-and-review)

## Find the missing fact

Start with the first failing sentence, its full goal/context and the declaration being
applied. Check the types of the goal, hypotheses, constructor, implicit arguments and
selected instance. A missing premise, wrong owner, wrong numeric carrier and blocked
conversion can produce similar surface symptoms but need different repairs.

Use scratch `About`, `Check`, `Print`, `Search` or printing options through the capped
runner. Search by the actual expression or relation before inventing a helper. Inspect a
lemma's orientation and argument names instead of inferring them from its name. Keep query
commands out of maintained source when the repository requires that separation.

Write the intermediate fact in mathematical language: what would make the next step
immediate? Then state that fact with explicit inputs. A small helper often reveals that the
proof needs an existing invariant or a stronger IH rather than another unfolding tactic.

| Symptom | First question |
| --- | --- |
| `apply` cannot unify the conclusion | Are carriers, arguments, scopes and indices correct? |
| `rewrite` finds no subterm | Is the term still present, and is the equality oriented correctly? |
| `reflexivity` gets stuck | Which conversion is required, and what blocks it? |
| An existential variable remains | Which witness or missing premise determines it? |
| An impossible case survives inversion | Was a relation/index equation lost or overspecialized? |
| A tactic runs for a long time | Is it searching or normalizing the wrong abstraction layer? |

Do not expand a whole semantic machine to compensate for an unresolved argument. Supply the
specific witness, owner or expected type first and inspect the smaller remaining goal.

## Choose the induction motive

Match the proof to the recursion or evidence that controls the claim:

| What changes | Useful starting point |
| --- | --- |
| A structurally processed list/tree | Induction on that structure |
| A derivation or multi-step path | Induction on the derivation/path |
| A fuel-bounded computation | Fuel induction with the state invariant generalized |
| Mutually defined syntax/judgments | The appropriate mutual or combined scheme |
| Recursive children nested in a container | Inspect the generated scheme and container evidence |
| A well-founded recursive function | Its equation/functional induction API |

Generalize values that a recursive call changes: accumulator, environment, continuation,
endpoint, suffix or dependent state. State the invariant before choosing which introductions
to delay. Generalizing everything can make the proof harder; specializing too early can
make the IH unusable.

A complete accumulator example:

```rocq
From Stdlib.Lists Require Import List.

Fixpoint reverse_onto {A : Type} (xs acc : list A) : list A :=
  match xs with
  | nil => acc
  | x :: rest => reverse_onto rest (x :: acc)
  end.

Lemma reverse_onto_spec : forall (A : Type) (xs acc : list A),
  reverse_onto xs acc = rev xs ++ acc.
Proof.
  intros A xs.
  induction xs as [| x rest IH]; intro acc.
  - reflexivity.
  - cbn [reverse_onto rev].
    rewrite IH.
    rewrite <- app_assoc.
    reflexivity.
Qed.
```

The IH quantifies over `acc`, so it applies to `x :: acc`. The associativity rewrite uses
the library lemma's actual orientation. A proof with an already-fixed accumulator would
need a suitable strengthening before the recursive case can use it.

For nested inductives, check the generated principle's sort and hypotheses. A `Forall`
property in `Prop` is different from evidence in `Type`; a weak eliminator may omit the
recursive-child hypotheses the proof needs. Modern Rocq supports registered container
`All` schemes, including `Scheme All` in supported versions. Generate/register them at the
appropriate point, inspect the resulting principle, and adapt its evidence to the required
container predicate. Alternatively use a justified custom nested induction principle.
Preserve an existing public weak scheme when changing generated defaults would break clients.
For registration order and container-specific details, see
[nested containers](modules-and-libraries.md#inspect-induction-principles-for-nested-containers).

For indexed predicates, ordinary induction can lose a fixed-index equation. Use a carefully
chosen motive, explicit index equalities, or supported dependent induction/destruction.
The appropriate scheme depends on the statement; stronger automation is not always needed.

## Preserve useful equations

When later reasoning needs the original expression, use a named equation with case
analysis, for example `destruct (lookup key table) eqn:Hlookup`. Check the resulting context:
dependent case analysis may also rewrite the IH and other hypotheses.

An IH can now expect a reduced equation such as `Some v = Some v`; supply reflexivity if
that is its new type. Rewriting the old lookup equation again may fail because the term
has already disappeared. Conversely, if the original equation is still needed to invoke
another theorem, do not discard it through anonymous case analysis.

Use `remember` when retaining a relationship to a complex dependent term is useful. Inspect
the orientation of the remembered equality. Keep a semantic fact separate from a particular
syntactic presentation when a later simplification should not invalidate it.

## Handle dependent equality

For a mismatch between `Vec A n` and `Vec A m`, first identify the required index equation
and its direction. Equality transport is a real operation; two mathematically equal indices
need not be definitionally convertible. Check the exact type of the supplied equation before
writing a cast or rewriting through the family.

Use an explicit dependent `match ... return ...` when the return type changes with a
constructor. Introduce a small transport lemma when it explains the relationship reused by
several clients. Avoid building a large dependent record and then asking broad simplification
to discover all its projection equalities at once.

Do not infer equality of whole dependent packages from equality of a few data fields.
Proof fields can make package equality need an additional principle. If clients only use
lookups, projections or pointwise behavior, prove those observations. For sparse maps, equal
reads can hold even when representations differ by explicit default entries; structural
equality would demand more than that client needs.

When full proof-field equality is required, inspect its actual type. Decidable equality can
justify a local UIP argument for equality proofs over the specific decidable carrier. That
does not provide proof irrelevance for every proposition. Likewise pointwise function
equality is not automatically Leibniz equality of functions, even on a finite domain.
Use an explicitly accepted extensionality principle when the stronger conclusion is needed.

Dependent induction/destruction is useful, but inspect the finished theorem's assumptions
after adding it. Some proof routes use equality principles that the chosen foundation may
not accept. Prefer an available constructive indexed-elimination lemma when it fits the goal.

## Check sorts and universes

When a type looks right but fails to unify, inspect its sort, universe instance and
constraints as well as its printed name. In scratch, use the pinned version's explicit
universe printing and focused universe queries. Distinguish an unsolved implicit or universe
variable from inconsistent constraints. Do not disable universe checking or add global
constraints simply to silence a local mismatch.

Choose monomorphic or universe-polymorphic declarations according to their intended clients.
A reusable abstraction can need independent instantiations; a concrete declaration can have
valid fixed constraints. Check actual applications before changing a whole theory's default.

Evidence in `Prop` cannot in general be eliminated to computational data in `Type`. An
existential proposition can establish that a witness exists without exposing a witness to
an executable function. Use a data-carrying dependent pair or another constructive interface
when the algorithm needs that witness; do not add an unaccepted choice principle. Check the
actual elimination rule, including the permitted singleton cases, before generalizing a
failed elimination to every proposition. Proof erasure during extraction is a separate stage.

## Use reflection and arithmetic deliberately

Bridge booleans and propositions at a named boundary. Apply the checker's soundness theorem
to discharge a large declarative fixture by computation when it exactly proves that property.
Keep the checker equation small and the semantic conclusion explicit. This is often more
stable than reconstructing dozens of conjunction fields by arithmetic tactics.

Prove checker completeness separately when required. Its proof may need uniqueness or a
canonical witness even when soundness or exact lookup agreement handles duplicate keys.
Derive those facts from the actual source invariant rather than adding them to an arbitrary
input theorem merely to satisfy an optimized implementation.

Use the development's reflection vocabulary. Stdlib boolean equivalences and MathComp
`reflect` views serve related purposes but have different interfaces and proof idioms.
Import and reuse the existing view instead of duplicating an ad hoc inversion tactic.

Choose arithmetic tools by the remaining mathematics:

- `lia` handles linear arithmetic; expose the needed inequalities and conversion facts first.
- `ring`/`ring_nf` normalize appropriate algebraic identities; give order or domain reasoning
  separately when needed.
- Nonlinear reasoning, bounded case analysis and bit-vector reasoning need their corresponding
  libraries or explicit lemmas, rather than a longer linear-arithmetic search.
- For division/modulo, inspect zero/sign conditions and the relevant quotient/remainder laws.
  Then let arithmetic automation close the resulting suitable relations.
- For casts between signed integers, naturals and machine words, prove range/sign facts before
  invoking inverse-conversion or no-wrap equations. A conversion may clamp or reduce modulo.

Do not turn a failure of one tactic into a mathematical impossibility claim. A division term
can occur inside an otherwise simple algebraic goal; conversely a short-looking goal can
hide a nontrivial range or representation invariant.

## Control automation

Use automation to discharge a known class of side conditions. Keep the important witness,
induction invariant and semantic step visible. Prefer scoped hint databases and local helper
tactics over global unfolding/search changes introduced for one goal.

Name hypotheses that later steps use. After inversion, destruct or monadic inversion, avoid
depending on generated names such as `H0`; import or use the project's established helper
when it supplies the right semantic decomposition. Do not replace it with a similar helper
whose clearing/substitution behavior differs silently.

Avoid unfocused `repeat constructor` on large nested propositions. It can create a large
search/reduction tree, choose an inappropriate constructor, or hide the one nontrivial case.
Use a finite case split and the specific constructor or reflection lemma needed at the head.

Use `solve [tactic]` when the test requires all generated goals to close. A tactic can succeed
without solving the goal; `Fail tactic` then tests a different property. For a negative proof
check, `Fail solve [...]` or a precisely ill-typed term can be appropriate, followed by
`Abort` for a scratch goal. Inspect the expected diagnostic so an unrelated syntax/import
failure does not falsely validate the negative control.

Check the surrounding goal structure after automation changes. A library upgrade can make
`auto` solve an additional goal; a following tactic that expected that goal can now fail.
Use explicit focusing and complete branches instead of a fragile chain that depends on
automation solving exactly a particular number of goals.

## Finish and review

Close the proof with the intended opacity, compile its actual clients and inspect assumptions
at the exported claim. Keep logical proofs separate from a finite fixture's computed result.
If downstream tooling prints or traverses the proof body, exercise that operation too: a
proof can typecheck while its fully expanded term is impractical to print.

Read the finished script as an explanation of the invariant. Factor a coherent repeated or
non-obvious subargument into a lemma; shortening a proof is useful when it improves this
structure, not merely because a tactical fits on one line. Preserve the statements and
computation behavior required by clients while making that change.

The [Rocq 9.3 induction reference][induction] explains generated and dependent induction;
the [equality reference][equality] describes conversion and reduction. Check the actual
generated principles and library lemma signatures for the pinned versions.

The [universe polymorphism reference][universes] explains explicit universe instances,
constraints and monomorphic/polymorphic declaration choices.

[induction]: https://rocq-prover.org/doc/V9.3.0/refman/proofs/writing-proofs/reasoning-inductives.html
[equality]: https://rocq-prover.org/doc/V9.3.0/refman/proofs/writing-proofs/equality.html
[universes]: https://rocq-prover.org/doc/V9.3.0/refman/addendum/universe-polymorphism.html
