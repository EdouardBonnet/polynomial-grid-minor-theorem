import Mathlib.Data.Nat.Log
import Lax17.PathOfSets
import Lax17.Treewidth

/-!
---
title: A strong path-of-sets system from treewidth
type: theorem
---
Sufficiently large treewidth produces a strong path-of-sets system of
prescribed length and width.
-/

namespace Lax17.StrongPathOfSetsFromTreewidth

universe u

/-- Sufficiently large treewidth produces a strong path-of-sets system of
prescribed length and width. -/
axiom strongPathOfSetsFromTreewidth :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (ℓ w : ℕ),
        2 ≤ ℓ → 2 ≤ w →
          c * ℓ * w * (Nat.log 2 (ℓ * w)) ^ d ≤
              Lax17.Treewidth.treewidth G →
            Nonempty (Lax17.PathOfSets.StrongSystem G ℓ w)

end Lax17.StrongPathOfSetsFromTreewidth
