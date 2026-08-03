This submission formalizes an improved polynomial excluded-grid theorem. It
proves that, for every real $\varepsilon>0$, there is a positive constant
$C_\varepsilon$ such that every finite simple graph of treewidth at least
$$
  C_\varepsilon g^{8+\varepsilon}
$$
contains the $g\times g$ square grid as a minor.

The proof first establishes a division-free natural-number statement. For
each integer $t\geq2$, let $\rho_t(g)$ be the least natural number with
$g^2\leq\rho_t(g)^t$. There are positive integers $K_t,b_t$, depending
only on $t$, for which treewidth at least
$$
  K_t g^8\rho_t(g)(\log_2 g)^{b_t}
$$
forces the same grid minor. The estimate
$\rho_t(g)\leq2g^{2/t}$, followed by a choice of fixed $t$, gives the
stated $8+\varepsilon$ result.

Treewidth is defined through finite tree decompositions, with width equal to
the largest bag cardinality minus one. The grid is the box product of two
finite path graphs, and the minor relation is the standard branch-set model.
The improvement comes from a finite, parameterized iteration of the recursive
slicing argument in Section 5 of Chuzhoy--Tan. All combinatorial producers,
the finite controller, the explicit parameter inequalities, and the final
real-exponent conversion are checked in Lean.

Algorithmic running times and probability guarantees are deliberately
omitted; the submitted graph-theoretic claims are finite existential
statements.
