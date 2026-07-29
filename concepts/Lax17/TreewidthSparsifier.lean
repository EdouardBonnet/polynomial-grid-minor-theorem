import Mathlib.Data.Nat.Log
import Lax17.Degree
import Lax17.Minor
import Lax17.Treewidth

/-!
---
title: Degree-three treewidth sparsifier
type: theorem
---
Large treewidth contains a degree-three minor of prescribed smaller
treewidth, with only a polylogarithmic loss.
-/

namespace Lax17.TreewidthSparsifier

universe u

/-- Large treewidth has a degree-three minor of any prescribed smaller
treewidth, with only a polylogarithmic loss. -/
axiom degreeThreeTreewidthSparsifier :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {k : ℕ},
        2 ≤ k →
          c * k * (Nat.log 2 k) ^ d ≤ Lax17.Treewidth.treewidth G →
            ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
              (H : SimpleGraph W),
                Lax17.Minor.IsMinor H G ∧
                  Lax17.Degree.MaximumAtMost H 3 ∧
                    k ≤ Lax17.Treewidth.treewidth H

end Lax17.TreewidthSparsifier
