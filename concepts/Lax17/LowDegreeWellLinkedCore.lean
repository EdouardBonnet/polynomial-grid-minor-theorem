import Lax17.Degree
import Lax17.Linkedness

/-!
---
title: A low-degree well-linked core
type: theorem
---
A sufficiently large node-well-linked set contains a large subcubic
well-linked core in a spanning subgraph.
-/

namespace Lax17.LowDegreeWellLinkedCore

universe u

/-- A sufficiently large node-well-linked set has a large subcubic
well-linked core in a spanning subgraph. -/
axiom lowDegreeWellLinkedCore :
  ∃ c : ℕ, 0 < c ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (X : Finset V) {k : ℕ},
        Lax17.Linkedness.NodeWellLinkedIn G Finset.univ X →
          c * k ≤ X.card →
            ∃ H : SimpleGraph V, ∃ Y : Finset V,
              H ≤ G ∧ Y ⊆ X ∧ k ≤ Y.card ∧
                Lax17.Degree.MaximumAtMost H 3 ∧
                  Lax17.Linkedness.NodeWellLinkedIn H Finset.univ Y

end Lax17.LowDegreeWellLinkedCore
