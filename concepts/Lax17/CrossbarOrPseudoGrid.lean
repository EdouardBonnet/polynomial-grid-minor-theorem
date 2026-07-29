import Lax17.Crossbar
import Lax17.Linkedness

/-!
---
title: Crossbar-or-pseudo-grid dichotomy
type: theorem
---
Large linked terminal sets yield either a crossbar or a pseudo-grid.
-/

namespace Lax17.CrossbarOrPseudoGrid

universe u

/-- Large linked terminal sets yield either a crossbar or a pseudo-grid. -/
axiom crossbarOrPseudoGrid :
  ∃ c : ℕ, 0 < c ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (A B X : Finset V) (k ρ : ℕ),
        Disjoint A B → Disjoint A X → Disjoint B X →
          Lax17.Linkedness.NodeWellLinkedIn G Finset.univ (A ∪ B ∪ X) →
            c * ρ ^ 2 ≤ k →
              k ≤ A.card → k ≤ B.card → k ≤ X.card →
                Nonempty (Lax17.Crossbar.System G A B X ρ) ∨
                  Nonempty (Lax17.Crossbar.PseudoGrid G ρ ρ)

end Lax17.CrossbarOrPseudoGrid
