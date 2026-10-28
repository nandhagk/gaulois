# References

These sources inform the planned algorithms and proofs. Each API contract's “Algorithms and
references” section gives the relevant details and identifies the local design choices.

- P. Cousot and R. Cousot, “Abstract interpretation: a unified lattice model for static analysis
  of programs by construction or approximation of fixpoints,” POPL, 1977;
  “Systematic design of program analysis frameworks,” POPL, 1979.
- G. A. Kildall, “A unified approach to global program optimization,” POPL, 1973.
- K. Apinis, H. Seidl and V. Vojdani, “Side-effecting constraint systems: a Swiss Army knife for
  program analysis,” APLAS, 2012.
- F. Bourdoncle, “Efficient chaotic iteration strategies with widenings,” 1993.
- F. Besson, T. Jensen and D. Pichardie, “Proof-carrying code from certified abstract
  interpretation and fixpoint compression,” Theoretical Computer Science, 2006.
- R. E. Tarjan, “Depth-first search and linear graph algorithms,” SIAM Journal on Computing, 1972.
- K. Cooper, T. Harvey and K. Kennedy, “A simple, fast dominance algorithm,” 2001.
- M. N. Wegman and F. K. Zadeck, “Constant propagation with conditional branches,” ACM TOPLAS,
  1991.
- F. Pfenning, A. Platzer and R. Simmons, 15-411 lecture 7, “Dataflow Analysis,” 2015.
- J. Navas, P. Schachte, H. Søndergaard and P. Stuckey, “Signedness-agnostic program analysis:
  precise integer bounds for low-level code,” APLAS, 2012.
- M. Willsey et al., “egg: Fast and extensible equality saturation,” POPL, 2021.
- L. Andersen, *Program Analysis and Specialization for the C Programming Language*, PhD thesis,
  1994; B. Steensgaard, “Points-to analysis in almost linear time,” POPL, 1996.
- S. Boldo and G. Melquiond, “Flocq: a unified library for proving floating-point algorithms in
  Coq,” 2011. Float uses Flocq's floating-point semantics.
- SMT-LIB, theory `FixedSizeBitVectors`: the word semantics used by Bits. The API contract states
  the chosen operations and total division conventions.
