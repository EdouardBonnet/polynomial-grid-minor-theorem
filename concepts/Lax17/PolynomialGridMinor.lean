import Mathlib.Analysis.SpecialFunctions.Log.Base
import Lax17.GridMinor
import Lax17.Treewidth

/-!
---
title: 'Polynomial grid-minor theorem with exponent $8$ up to polylogarithmic factors'
type: theorem
---
There are positive integers $K$ and $b$ such that every finite simple graph
of treewidth at least
$$
  K g^8 (\log_2 g)^b
$$
contains the $g\times g$ square grid as a minor. In particular, the
polynomial exponent is exactly eight; all remaining loss is polylogarithmic.

The earlier exponent-$8+\varepsilon$ formulation is retained below as a
compatibility corollary.

Treewidth is the parameter defined by the `Lax17.Treewidth` concept. The
minor conclusion uses the branch-set model in `Lax17.GridMinor`.
-/

namespace Lax17.PolynomialGridMinor

universe u

/-- Polynomial excluded-grid theorem with exact polynomial exponent eight
and an explicit natural-number polylogarithmic factor. The constants are
selected before the graph and grid order. -/
axiom polynomial_grid_minor_eight_polylog :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {g : ℕ},
          2 ≤ g →
            K * g ^ 8 * (Nat.log 2 g) ^ b ≤
                Lax17.Treewidth.treewidth G →
              Lax17.GridMinor.ContainsGridMinor G g

/-- Polynomial excluded-grid theorem with exponent `8 + epsilon`.

The exponent on `(g : ℝ)` is real exponentiation.  The constant is selected
before the graph and grid order, so it depends only on `epsilon`. -/
axiom polynomial_grid_minor_eight_add_epsilon :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 < C ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) {g : ℕ},
            2 ≤ g →
              C * (g : ℝ) ^ ((8 : ℝ) + epsilon) ≤
                  (Lax17.Treewidth.treewidth G : ℝ) →
                Lax17.GridMinor.ContainsGridMinor G g

end Lax17.PolynomialGridMinor
