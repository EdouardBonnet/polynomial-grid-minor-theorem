This submission formalizes the polynomial excluded-grid theorem of Chuzhoy
and Tan in an explicit exponent-ten form. It proves that there are universal
positive constants \(c\) and \(d\) such that every finite simple graph of
treewidth at least
\[
  c\,g^{10}(\log_2 g)^d
\]
contains the \(g\times g\) square grid as a minor.

Treewidth is defined through finite tree decompositions, with width equal to
the largest bag cardinality minus one. The grid is the box product of two
finite path graphs, and the minor relation is the standard branch-set model.
Major structural results in the proof are exposed as separate statements,
including finite Menger theorems, the degree-three treewidth sparsifier,
strong and hairy path-of-sets constructions, the crossbar dichotomy, the
cut-matching expansion theorem, and the expander-to-grid argument.

The proof follows the weaker Section 4 route of Chuzhoy--Tan, giving the
polynomial exponent ten. Algorithmic running times and probability guarantees
are deliberately omitted; all submitted claims are finite existential
statements.
