This submission formalizes an exponent-eight polynomial excluded-grid
theorem. It proves that there are positive integers $K$ and $b$ such that
every finite simple graph of treewidth at least
$$
  K g^8(\log_2 g)^b
$$
contains the $g\times g$ square grid as a minor. Thus the polynomial loss is
exactly $g^8$; the remaining loss is polylogarithmic. This strengthens the
previous exponent-$8+\varepsilon$ endpoint, which is retained as a corollary.

Treewidth is defined through finite tree decompositions, with width equal to
the largest bag cardinality minus one. The grid is the box product of two
finite path graphs, and the minor relation is the standard branch-set model.
The improvement comes from a logarithmic-depth amortized controller for the
recursive slicing argument in Section 5 of Chuzhoy--Tan. It produces a square
strong Path-of-Sets system with width and length $g^2$ from a local threshold
of order $g^8\operatorname{polylog}(g)$. All combinatorial producers, the
controller, the explicit natural-number inequalities, and the final global
composition are checked in Lean.

Algorithmic running times and probability guarantees are deliberately
omitted; the submitted graph-theoretic claims are finite existential
statements.
