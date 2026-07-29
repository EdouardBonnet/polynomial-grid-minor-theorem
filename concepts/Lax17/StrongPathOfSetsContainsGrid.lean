import Mathlib.Data.Nat.Log
import Lax17.GridMinor
import Lax17.PathOfSets

/-!
---
title: A grid minor from a strong path-of-sets system
type: theorem
---
A sufficiently long and wide strong path-of-sets system contains a
prescribed square grid minor.
-/

namespace Lax17.StrongPathOfSetsContainsGrid

universe u

/-- A sufficiently long and wide strong path-of-sets system contains a
prescribed square grid minor. -/
axiom strongPathOfSetsContainsGrid :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {ℓ w g : ℕ},
        Nonempty (Lax17.PathOfSets.StrongSystem G ℓ w) →
          2 ≤ g → c * g ≤ ℓ →
            c * g ^ 2 * (Nat.log 2 g) ^ d ≤ w →
              Lax17.GridMinor.ContainsGridMinor G g

end Lax17.StrongPathOfSetsContainsGrid
