import Mathlib.Data.Nat.Log
import Lax17.TreeOfSets

/-!
---
title: Strong tree-of-sets construction
type: theorem
---
A sufficiently large node-well-linked set supports a strong subcubic
tree-of-sets system.
-/

namespace Lax17.StrongTreeOfSetsConstruction

universe u

/-- A sufficiently large node-well-linked set supports a strong subcubic
tree-of-sets system. -/
axiom strongTreeOfSetsConstruction :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (X : Finset V) (m w : ℕ),
        Lax17.Linkedness.NodeWellLinkedIn G Finset.univ X →
          2 ≤ m → 2 ≤ w →
            c * m * w * (Nat.log 2 (m * w)) ^ d ≤ X.card →
              Nonempty (Lax17.TreeOfSets.StrongSystem G m w)

end Lax17.StrongTreeOfSetsConstruction
