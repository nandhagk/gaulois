# Computation, recursion and extraction

## Contents

- [Find the boundary that blocks reduction](#find-the-boundary-that-blocks-reduction)
- [Use opacity deliberately](#use-opacity-deliberately)
- [Control the next reduction](#control-the-next-reduction)
- [Choose a recursion strategy](#choose-structural-recursion-well-founded-recursion-or-fuel)
- [Preserve behavior through extraction](#preserve-behavior-through-extraction)
- [Check native bindings and generated code](#check-native-bindings-and-generated-code)
- [Match evidence to the claim](#match-evidence-to-the-claim)
- [Versioned references](#versioned-references)

Use this reference when a goal reduces unexpectedly, recursive definitions fail the guard
checker or scale poorly, or an extracted program behaves differently from its Rocq model.
First locate the boundary involved; do not change proof opacity, recursion or runtime
realizations until the failing layer is clear.

## Find the boundary that blocks reduction

Reduction and conversion are related but not identical. Conversion lets Rocq check
definitional equality; tactics such as `cbn`, `cbv`, `lazy`, `vm_compute` and `native_compute`
control or accelerate particular reductions. A stuck `reflexivity` goal can be caused by a
different carrier, an opaque constant, an unreduced match, a non-convertible dependent index,
or a large term. Expand only the layer needed to distinguish these causes.

Use the following three opacity boundaries as separate questions:

| Boundary | Question |
| --- | --- |
| Proof and constant opacity | Can kernel conversion unfold the body? |
| Module abstraction | What does the module type or functor expose? |
| Extraction access | Can extraction inspect opaque proofs, or are they treated as axioms? |

Inspect the signature, manifest type equalities, projections, actual functor application,
`Qed` versus `Defined`, `About`, explicit opacity settings, `Extraction AccessOpaque`, warnings,
roots and realizations for the boundary involved.

A proof closed with `Qed` is opaque to ordinary conversion; `Defined` leaves its body
transparent. A transparent algorithm can still call an opaque helper. A body can also be
hidden by a module signature even when its defining source is transparent. Diagnose the
specific term or module path rather than making unrelated declarations transparent.

Extraction has an independent policy. In Rocq 9.3, `Extraction AccessOpaque` controls whether
opaque proof bodies are available to the extractor; with access disabled, they are treated as
axioms. A project can still promote an opaque-access warning to a build error. Thus an
extraction diagnostic may be a warning-policy failure even when a body was available and
generated. Do not change `Qed` to `Defined` as a generic extraction workaround. First check
whether the problem is unavailable computational content, an unrealized axiom, a promoted
warning, generated-code typing, or runtime behavior.

Do not use proof transparency to make a computational definition work around an unrelated
module boundary. If clients need a computation, expose a small executable function or a
statement-level equation in the intended interface. Keep representation hidden when clients
need only an abstract theorem.

## Use opacity deliberately

Choose `Qed` when downstream clients need the proposition but not its proof body for
computation. Choose `Defined` when the proof term itself is intentionally data consumed by
computation. A theorem used only as a rewrite lemma normally does not need a transparent proof.
There is no general rule that every definition should be opaque or every computational lemma
should end in `Defined`; test the real consumer and respect local trust and extraction policy.

When a transparent body makes conversion expensive, state the needed equation once and rewrite
with it. Keep the executable definition and its proof interface distinct. Avoid repeatedly
unfolding a large evaluator, dependent record or memory model merely to rediscover a small
field equation. For an abstract module, prove the equation against its public operations rather
than reaching through a hidden implementation.

If a refactor moves definitions under a functor or changes the module type, compile real
members and downstream clients. Applications can alter type identity and inference even when
the source bodies look identical. Preserve the needed equalities and argument types in the
interface; do not add broad unfolding or casts to mask an interface mismatch.

## Control the next reduction

Start from the exact goal and identify the head computation needed next. Prefer a named
equation, a small helper lemma, an explicit witness or a narrower return clause before
normalizing a large term.

- Use `cbn [f g]` or a directed `unfold` when only named transparent definitions should
  unfold. Check that the reduced goal still contains the fact needed by later steps.
- Use `change` when the current goal is definitionally equal to a clearer presentation; it
  does not prove a non-convertible equality.
- Record a case equation when later reasoning needs it, such as a lookup result or matched
  branch. After destructing, inspect whether simplification already consumed the expression
  before trying another rewrite.
- Use `rewrite` with a semantic or specification lemma when conversion would expand an
  implementation. Generalize any changing accumulator, environment or continuation before
  induction.
- Use `vm_compute` or `native_compute` for a bounded executable check when appropriate. Such
  a check establishes that instance; it is not a universal theorem or a substitute for proving
  the relation between an optimized implementation and its specification.

Inspect the remaining goals after normalization. Reducing an equality to `true = true`
can still require a closing step such as `reflexivity`. A printed `Eval` result does not
prove the corresponding goal. If the reduced result is wrong, inspect the elaborated input
and split the checker or proposition into meaningful components before changing expectations.

Large conversion is often a symptom of the wrong abstraction boundary. If a full match
expands many constructors, factor the discriminant into a small helper and prove that the
helper preserves the original branch, priority and payload. Keep the large continuation in
one place rather than duplicating it in every fallback arm. Measure equivalent compiled
targets before claiming a speed improvement.

## Choose structural recursion, well-founded recursion or fuel

For ordinary `Fixpoint`, make the decreasing argument and recursive subterm visible to the
guard checker. A recursive call is not accepted merely because a human can see that an
expression gets smaller. Match on the inductive argument and recurse directly on its
constructor subterm. If a lambda, wrapper or nested pattern hides the descent, factor a helper
whose explicit argument is the list, tree or syntax node that decreases. Preserve the original
case order and prove the helper equation against the unfactored definition.

Use well-founded recursion or a measure when the algorithm terminates but the decrease is not
structural. Prove the relation for every recursive call and inspect the generated equation and
functional induction principles. Such definitions add proof obligations and can reduce less
directly than structural recursion. They do not make a potentially diverging evaluator total.

For an evaluator that may diverge, choose an explicit partiality model, step relation, or
fuelled runner with a stated observation policy. Define whether fuel measures recursive depth,
transitions, rounds or another resource, and decrease it as that policy requires. Exhaustion
alone does not establish a semantic result, rejection or undefined behavior. An explicit
exhaustion result is often useful. If an API returns a fallback, specify that behavior; prove
or validate any semantic guarantee consumers rely on. Preserve the promised observations.
Propagate a whole-operation budget through helpers; separately specified per-call depth
limits may restart. Test these limits independently from a wall-clock/process deadline.

Useful evidence differs by recursion kind:

| Technique | Check that the evidence establishes |
| --- | --- |
| Structural helper | Guard-checked definition and equation preserving the old traversal |
| Well-founded or measured recursion | Decrease obligations and the intended functional equation |
| Fuelled execution | Positive-budget behavior and the specified exhaustion or fallback policy |
| Unbounded semantics | A relation or partiality account for divergence, not a larger finite fuel |

Never disable guard checking or disguise an unbounded loop as a terminating recursive
function. A finite successful run shows behavior only for that input and budget.

## Preserve behavior through extraction

Rocq reduction and target-language evaluation are different semantics. OCaml is strict:
function arguments and ordinary value expressions are evaluated before the function body.
The evaluation order of several OCaml subexpressions is not generally a left-to-right
contract. Make sequencing explicit when effects or exceptions make order observable.

Avoid eager failure defaults. For example, do not pass a raising expression as the fallback
argument to an indexing function if the fallback is evaluated before selection. First inspect
the optional lookup result, then raise or return the model's failure only in the missing case.
Check both valid and invalid inputs in the generated executable; kernel reduction of the Rocq
definition alone will not reveal an eager target-language default.

Preserve the exact error and observation boundary across the bridge. Distinguish a semantic
failure from an implementation exception, timeout, signal, resource exhaustion and incomplete
enumeration. Keep traces, error labels, locations, output and result order when the contract
requires them. If the reference interface omits observations, compare the shared projection
and check the richer candidate observations independently. Empty or incomplete runs do not
establish agreement.

Extraction erases proof material in `Prop` and realizes computational roots according to the
configured mappings. A theorem that compiles does not establish that its extracted caller
uses the expected representation. For representation changes, establish the required Rocq-level
equation or relational agreement, or identify the explicitly accepted extraction mapping and its
trust boundary. Then check generated code and execute boundary cases.
For example, replacing unary recursive natural-number comparison with a native big-integer
comparison requires a proved correspondence or an explicitly trusted realization, plus
checks that large extracted inputs exercise the intended representation and operation.

## Check native bindings and generated code

Treat native extraction realizations as an explicit trust boundary. For each executable root,
check the declared Rocq type, the selected realization, its target-language interface and the
callers that can reach it. An external function name is not an implementation or a proof of
its semantics. Do not fill missing operations with dummy values, unresolved placeholders or
unreviewed casts.

Polymorphic and phantom type parameters can be erased or omitted by extraction. Inspect the
actual generated `.ml` types and any generated `.mli` when a generic function or module
application appears to lose a type distinction. Keep module instances and native adapters
aligned with the extracted signatures. A type annotation such as an explicit unit binder may
be needed to disambiguate a generated pattern; verify it in emitted code and its clients.
Reject unexpected unsafe casts or unresolved symbols when the project contract forbids them.

Use a staged check:

1. Compile the Rocq declarations for the actual dependency closure.
2. Inspect assumptions of the claims for logical dependencies. Separately audit which ordinary
   definitions and native realizations each executable root reaches; `Print Assumptions` alone
   does not establish that dependency closure or the meaning of a native binding.
3. Extract the actual public roots and inspect generated types, warnings and unresolved names.
4. Compile the generated target code with the pinned compiler and real runtime adapters.
5. Run positive, negative and boundary fixtures through the extracted entry point, including
   budget exhaustion and representation-sensitive values.

Keep diagnostic generation separate from the executable import. A probe with deliberately
unresolved foreign calls can reveal dependencies, but its generated files must not be counted
as an executable model. Conversely, an operational closure that compiles does not establish a
source-to-model correspondence theorem unless that bridge is separately stated and checked.

## Match evidence to the claim

| Evidence | What it establishes |
| --- | --- |
| Source inspection or reduction hypothesis | Intended mechanism only |
| Compiled definition or theorem | The kernel accepted that declaration under its dependencies |
| `Print Assumptions` on a claim | Its reported logical dependencies, not native runtime behavior |
| Generated target code compiles | Extraction and target-language typing for that closure |
| Extracted execution test | Those inputs, observations and runtime configuration |
| Capped benchmark | The measured target and controls only; not semantic correctness |

Report exactly which roots, compiler version, extraction mappings and fixtures were checked.
A complete audit of one set of roots says nothing about omitted roots. A timeout is an
incomplete experiment, not a semantic empty result. Keep source-to-extraction refinement,
native runtime correctness and compiler correctness as separate claims unless explicit proofs
connect them.

## Versioned references

- [Conversion and equality, Rocq 9.3][rocq-equality]
- [Definitions and bodies, Rocq 9.3][rocq-definitions]
- [Inductive types and recursive functions, Rocq 9.3][rocq-recursion]
- [Well-founded and measured recursion, Rocq 9.3][rocq-program]
- [Program extraction and `AccessOpaque`, Rocq 9.3][rocq-extraction]
- [OCaml expressions and evaluation, OCaml 5.5](https://ocaml.org/manual/5.5/expr.html)

[rocq-equality]: <https://rocq-prover.org/doc/V9.3.0/refman/proofs/writing-proofs/equality.html>
[rocq-definitions]: <https://rocq-prover.org/doc/V9.3.0/refman/language/core/definitions.html>
[rocq-recursion]: <https://rocq-prover.org/doc/V9.3.0/refman/language/core/inductive.html>
[rocq-program]: <https://rocq-prover.org/doc/V9.3.0/refman/addendum/program.html>
[rocq-extraction]: <https://rocq-prover.org/doc/V9.3.0/refman/addendum/extraction.html>
