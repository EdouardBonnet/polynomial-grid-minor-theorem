import Mathlib.Analysis.SpecialFunctions.Log.Base
import Lax17.GridMinor
import Lax17.PowerRoot
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

The exact integer statement preceding the real-exponent corollary is also
recorded.  For each integer \(t\geq2\), let \(\rho\) be the least natural
number satisfying \(g^2\leq\rho^t\).  Then the checked proof gives a bound
\(K_t g^8\rho(\log_2 g)^{b_t}\), where the positive integers \(K_t,b_t\)
depend only on `t`.
-/

namespace Lax17.PolynomialGridMinor

universe u

/-- Exact natural-number fixed-round theorem.  The relation
`IsCeilingPowerRoot t g rho` spells out the value of `rho`; no asymptotic
notation or real root is hidden in this statement. -/
axiom polynomial_grid_minor_fixed_t :
    ∀ t : ℕ, 2 ≤ t →
      ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) {g rho : ℕ},
            2 ≤ g →
              Lax17.PowerRoot.IsCeilingPowerRoot t g rho →
                K * g ^ 8 * rho * (Nat.log 2 g) ^ b ≤
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
