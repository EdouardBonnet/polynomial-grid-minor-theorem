import Mathlib.Data.Nat.Log
import Lax17.PathOfSets
import Lax17.Treewidth

/-!
---
title: A hairy path-of-sets system from treewidth
type: theorem
---
Sufficiently large treewidth produces a hairy strong path-of-sets system.
-/

namespace Lax17.HairyPathOfSetsFromTreewidth

universe u

/-- Sufficiently large treewidth produces a hairy strong path-of-sets
system. -/
axiom hairyPathOfSetsFromTreewidth :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (ℓ w : ℕ),
        2 ≤ ℓ → 2 ≤ w →
          c * ℓ * w * (Nat.log 2 (ℓ * w)) ^ d ≤
              Lax17.Treewidth.treewidth G →
            Nonempty (Lax17.PathOfSets.HairySystem G ℓ w)

end Lax17.HairyPathOfSetsFromTreewidth
