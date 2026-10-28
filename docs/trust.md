# Trust and evidence

Every contracted `Theorem` is a claim to prove, not evidence by itself. A kernel-checked claim is a
proved theorem whose assumptions meet the policy below. A statement that compiles has type-checked;
it does not establish a proof. A smoke check reports an outcome on examples. An experiment reports
measurements and does not prove a general complexity or soundness claim.

The revised contracts have not been compiled as a whole. The original skeleton's successful
build is a smoke check of the setup, not evidence that the contracted theorems hold.
The implementation run checks each card's theorems and examples, and FINAL checks a fresh build.

## Assumptions

Outside Float, each `Theorem` must be closed under the global context. No new axioms, `Parameter`,
`Conjecture`, `Admitted` or admitted proofs are permitted. Do not import axiom-bearing Stdlib
modules for those proofs. Before the claims tool exists, use `Print Assumptions` on each theorem;
then `gaulois check claims` audits the claims. Its implementation is planned in TOOL-1.

C13 permits Float theorems to depend only on the exact classical real-number axioms used by Flocq:
`ClassicalDedekindReals`'s `sig_forall_dec` and `sig_not_dec`, and the functional extensionality
used by Reals. The Float contract specifies the precise names, and the claims checker permits them
only for `Gaulois.Float`. This allowance does not extend to other packages.

## Producers and checkers

A solver's post-solution proof establishes its stated constraints under its hypotheses. Semantic
soundness also depends on the client's view laws. Verified checkers allow untrusted producers to
supply candidates; acceptance is meaningful only under the checker's stated premises. Cards require
nontrivial accepted examples or a suitable completeness theorem so that a checker is exercised.
Checked narrowing retains the previous solution if a candidate fails. Directly proved internal
producers need their own closed correctness proofs; checkers remain available for external and
cached candidates. Legacy MemorySSA byte preservation retains its stated stronger premises and
requires a proved projection from the new version graph where applicable.

The behaviour theorem distinguishes the effect policies: retaining traps supports the stated
behaviour equality; deleting unread traps supports the contract's conditional refinement. Proofs
about examples demonstrate the toy clients under their own semantics, not arbitrary client code.
