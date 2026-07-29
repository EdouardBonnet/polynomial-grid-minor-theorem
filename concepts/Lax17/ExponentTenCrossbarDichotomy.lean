import Mathlib.Data.Nat.Log
import Lax17.Crossbar
import Lax17.GridMinor
import Lax17.PathOfSets

/-!
---
title: Exponent-ten crossbar dichotomy
type: theorem
---
At the exponent-ten scale, a hairy path-of-sets system either already
contains the target grid or supplies a local crossbar at every position.
-/

namespace Lax17.ExponentTenCrossbarDichotomy

universe u

/-- At the exponent-ten scale, a hairy path-of-sets system either already
contains the target grid or supplies a local crossbar at every position. -/
axiom exponentTenCrossbarDichotomy :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {ℓ w g : ℕ}
      (H : Lax17.PathOfSets.HairySystem G ℓ w),
        2 ≤ g → g ≤ ℓ →
          c * g ^ 10 * (Nat.log 2 g) ^ d ≤ w →
            Lax17.GridMinor.ContainsGridMinor G g ∨
              ∀ i : Fin ℓ,
                Nonempty
                  (Lax17.Crossbar.System G
                    (H.base.left i) (H.base.right i)
                    (H.hairEndpoint i) g)

end Lax17.ExponentTenCrossbarDichotomy
