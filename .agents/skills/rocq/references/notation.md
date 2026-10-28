# Notation, scopes and concrete syntax

## Contents

- [Separate parsing from elaboration](#separate-parsing-from-elaboration)
- [Choose precedence and scope deliberately](#choose-precedence-and-scope-deliberately)
- [Test the constructor tree](#test-the-constructor-tree)
- [Keep custom grammars compositional](#keep-custom-grammars-compositional)
- [Diagnose collisions in a real client](#diagnose-collisions-in-a-real-client)
- [Keep printers and examples honest](#keep-printers-and-examples-honest)
- [Versioned references](#versioned-references)

Use this reference before adding notation, moving syntax declarations, changing imports,
or diagnosing a term that parses or elaborates differently from its intended meaning.

## Separate parsing from elaboration

First determine whether the failure is tokenization, grammar, name resolution or typing.
A message about the next expected token can be caused by an earlier expression consuming
too much input. A term that parses can still select an unexpected notation interpretation,
implicit argument, coercion, numeric carrier or typeclass instance.

In scratch queries, compare the surface expression with an explicitly constructed term.
Use `Locate`, `Print Notation`, `Print Grammar`, `Check`, `About` and suitably explicit
printing to inspect the relevant layer. Start with a small expression and the actual
import header; do not print the entire grammar or a huge elaborated development first.
Keep diagnostic settings and queries out of maintained theory files unless they are
intentional tests under the project's conventions.

Use an explicit scope delimiter, type annotation, qualified constructor or explicit
argument to isolate an ambiguity. Once the cause is understood, choose the smallest
interface change that preserves the intended language. Renaming many unrelated identifiers
can hide a lexical or grammar problem without fixing the syntax design.

## Choose precedence and scope deliberately

Rocq's lower precedence numbers bind more tightly. Specify associativity and operand
levels where the intended grouping requires them. A scope chooses an interpretation;
it does not provide a completely independent parser grammar. Reusing a token pattern with
incompatible levels can conflict even in another scope.

Before assigning levels, inspect existing reserved notation and expressions that share
the same prefix. Respect the parser's factorization requirements. Parenthesizing one
fixture does not repair a grammar that rejects other intended compositions.

Use `Declare Scope`, `Delimit Scope` and explicit delimiters when clients need to choose
between interpretations. Use local opening where practical. Treat `Bind Scope`, imported
notations and scope-opening commands as part of the API: inference and surrounding
imports can affect which interpretation becomes active.

Reserve notation when mutually defined syntax or several interpretations share a grammar.
Keep its level and associativity consistent with later declarations. Distinguish a reserved
grammar rule from a notation that already denotes a term.

Adding literal tokens can change lexical behavior outside the visually delimited example.
Check whether a new word became a keyword and whether existing binders or identifiers
still parse in importing files. A custom entry or scope does not justify assuming that
all tokenization effects are confined to the intended notation block.

## Test the constructor tree

Use a reflexive equality against explicit constructors to check the parsed AST. An
evaluation result can hide a grouping error when operations happen to be associative,
commutative or equivalent on the chosen values.

The following standalone example checks both precedence and left association:

```rocq
Inductive expr : Type :=
  | Lit : nat -> expr
  | Add : expr -> expr -> expr
  | Mul : expr -> expr -> expr.

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.
Infix "⊕" := Add (at level 50, left associativity) : expr_scope.
Infix "⊗" := Mul (at level 40, left associativity) : expr_scope.

Example mixed_precedence :
    (Lit 1 ⊕ Lit 2 ⊗ Lit 3)%expr = Add (Lit 1) (Mul (Lit 2) (Lit 3)).
Proof.
  reflexivity.
Qed.

Example left_association :
    (Lit 1 ⊕ Lit 2 ⊕ Lit 3)%expr = Add (Add (Lit 1) (Lit 2)) (Lit 3).
Proof.
  reflexivity.
Qed.
```

Choose cases that distinguish the intended tree: mixed operators, repeated operators,
nested blocks, singleton and empty forms, and delimiters inside another notation.
Check identifier, numeral and string escapes at their actual syntactic positions.
For a binder, test scope of the bound variable and capture behavior as well as parsing.

Add rejected forms when rejection is part of the interface. A `Fail` command establishes
that its command failed, not that the intended diagnostic caused the failure. Keep the
negative case small and inspect its message; pair it with a nearby accepted case.

Compile an importing client with the normal dependency set. A notation can work in its
defining file yet conflict with another library or fail because its export path changed.

## Keep custom grammars compositional

Use a custom entry when an object language needs a grammar distinct from ordinary Rocq
terms. Choose which positions accept object-language expressions and which intentionally
escape to `constr`, identifiers, numerals or strings. A broad `constr` slot can consume
separators or accept host-language expressions beyond the object language's intended AST.

Define the small atomic forms and their escaping rules before composing larger blocks.
Check list separators, terminating keywords, optional sections and empty productions.
For overlapping prefixes, inspect where the parser can decide between alternatives;
align shared prefixes instead of relying on later type errors to choose the branch.

Treat a grammar-level repair as a design change. Check old accepted forms, old rejected
forms, pretty output and important importing clients. Preserve AST meaning through any
notation migration; a mechanically updated surface spelling is insufficient evidence.

Keep notation ownership clear. A shared leaf should have a consistent spelling across
related syntaxes when its meaning is shared. Distinct semantic constructs can need distinct
spellings even when their current constructors happen to have similar fields.

## Diagnose collisions in a real client

When an unchanged expression stops compiling after a move or import change:

1. Reproduce its original imports, scopes and declaration order in a scratch file.
2. Check which qualified constant and notation interpretation each short name denotes.
3. Inspect implicit arguments, coercions and selected instances with explicit printing.
4. Replace only the suspect syntax with its intended constructor application.
5. Repair the responsible declaration or public import, then recheck both clients.

A successful qualification experiment identifies a resolution issue; it does not mean
every name in the file should become fully qualified. Follow local naming conventions and
use the shortest owner prefix that makes the intended declaration unambiguous.

Do not assume same-spelled helpers from different libraries are interchangeable. Their
types, argument order, notation support or reduction behavior can differ. Check a lemma's
actual statement and orientation before rewriting, especially across library upgrades.

## Keep printers and examples honest

Treat printed syntax and the underlying AST as separate interfaces. A pretty string can
omit defaults, normalize layout or choose another notation without changing semantics.
Conversely, visually similar output can conceal a different constructor or outcome tag.

If a project provides both a parser and printer, test the promised round-trip law on the
supported domain and document normalization. If it provides only notation and a printer,
do not introduce a parser merely to test it: check notation ASTs and printer observations
at the existing boundary.

Use `only parsing` and `only printing` deliberately. Reimporting libraries or changing
notation declarations can affect which presentation is selected. Do not infer a unique
surface representation from a term unless the API promises one.

Keep examples representative of real syntax and observations. Constructor-only fixtures
remain useful for isolated semantic tests, but they do not exercise notation. Printer
snapshots exercise text layout, while AST equalities exercise parsing and elaboration;
neither substitutes for the other.

## Versioned references

- [Syntax extensions and notation scopes, Rocq 9.3][syntax]
- [Implicit arguments, Rocq 9.3][implicits]
- [Coercions, Rocq 9.3][coercions]

[syntax]: <https://rocq-prover.org/doc/V9.3.0/refman/user-extensions/syntax-extensions.html>
[implicits]: <https://rocq-prover.org/doc/V9.3.0/refman/language/extensions/implicit-arguments.html>
[coercions]: <https://rocq-prover.org/doc/V9.3.0/refman/addendum/implicit-coercions.html>
