import Mathlib.Data.Nat.Log
import Lax17.GridMinor
import Lax17.Treewidth

/-!
---
title: Polynomial grid-minor theorem with exponent ten
type: theorem
---
There are positive universal constants \(c\) and \(d\) such that, for every
integer \(g\geq 2\), every finite simple graph of treewidth at least
\(c g^{10}(\log_2 g)^d\) contains the \(g\times g\) square grid as a minor.

Treewidth is the parameter defined by the `Lax17.Treewidth` concept. The
explicit exponent-ten statement is the weaker Section 4 consequence of
Chuzhoy and Tan's polynomial excluded-grid theorem.
-/

namespace Lax17.PolynomialGridMinor

universe u

/-- The exponent-ten polynomial excluded-grid theorem. -/
axiom polynomial_grid_minor :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {g : ℕ},
          2 ≤ g →
            c * g ^ 10 * (Nat.log 2 g) ^ d ≤
                Lax17.Treewidth.treewidth G →
              Lax17.GridMinor.ContainsGridMinor G g

end Lax17.PolynomialGridMinor
