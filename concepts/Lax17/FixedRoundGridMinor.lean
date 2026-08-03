import Mathlib.Data.Nat.Log
import Lax17.GridMinor
import Lax17.PowerRoot
import Lax17.Treewidth

/-!
---
title: 'Exact fixed-round grid-minor theorem'
type: theorem
---
For every integer $t \geq 2$, let $\rho_t(g)$ be the least natural number
such that $g^2 \leq \rho_t(g)^t$. There are positive integers $K_t$ and
$b_t$, depending only on $t$, such that treewidth at least
$K_t g^8 \rho_t(g)(\log_2 g)^{b_t}$ forces a $g \times g$ grid minor.

This division-free natural-number theorem is the fixed-round combinatorial
core used by the exponent-$8+\varepsilon$ endpoint.
-/

namespace Lax17.FixedRoundGridMinor

universe u

/-- Exact natural-number theorem obtained from $t-1$ recursive slicing
rounds. The transparent root relation determines the factor `rho`. -/
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

end Lax17.FixedRoundGridMinor
