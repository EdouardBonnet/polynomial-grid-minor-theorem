import Mathlib.Analysis.SpecialFunctions.Log.Base
import Lax17.GridMinor
import Lax17.Treewidth

/-!
---
title: Polynomial grid-minor theorem with exponent 8 + epsilon
type: theorem
---
For every real \(\varepsilon>0\), there is a positive constant
\(C_\varepsilon\) such that every finite simple graph of treewidth at least
\(C_\varepsilon g^{8+\varepsilon}\) contains the \(g\times g\) square grid
as a minor.

Treewidth is the parameter defined by the `Lax17.Treewidth` concept. The
minor conclusion uses the branch-set model in `Lax17.GridMinor`.
-/

namespace Lax17.PolynomialGridMinor

universe u

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
