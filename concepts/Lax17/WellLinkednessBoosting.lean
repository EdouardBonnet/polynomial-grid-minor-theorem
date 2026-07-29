import Lax17.Degree
import Lax17.Linkedness

/-!
---
title: Well-linkedness boosting
type: theorem
---
In bounded degree, edge well-linkedness can be boosted to node
well-linkedness after losing only a constant-factor number of terminals.
-/

namespace Lax17.WellLinkednessBoosting

universe u

/-- In bounded degree, edge well-linkedness can be boosted to node
well-linkedness after losing only a constant-factor number of terminals. -/
axiom wellLinkednessBoosting :
  ∃ c : ℕ, 0 < c ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (X : Finset V) (Δ k : ℕ),
        Lax17.Degree.MaximumAtMost G Δ →
          Lax17.Linkedness.EdgeWellLinkedIn G Finset.univ X →
            c * (Δ + 1) * k ≤ X.card →
              ∃ Y : Finset V, Y ⊆ X ∧ k ≤ Y.card ∧
                Lax17.Linkedness.NodeWellLinkedIn G Finset.univ Y

end Lax17.WellLinkednessBoosting
