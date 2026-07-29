import Lax17.PathOfSets

/-!
---
title: Parallel cluster splitting
type: theorem
---
Three large linked terminal sets in one cluster can be retained in three
pairwise disjoint connected subclusters.
-/

namespace Lax17.ParallelClusterSplitting

universe u

/-- Three large linked terminal sets in one cluster can be retained in three
pairwise disjoint connected subclusters. -/
axiom parallelClusterSplitting :
  ∃ c : ℕ, 0 < c ∧
    ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V)
      (C A B X : Finset V) (q : ℕ),
        Lax17.PathOfSets.IsCluster G C →
          A ⊆ C → B ⊆ C → X ⊆ C →
            Disjoint A B → Disjoint A X → Disjoint B X →
              Lax17.Linkedness.NodeWellLinkedIn G C (A ∪ B ∪ X) →
                c * q ≤ A.card → c * q ≤ B.card → c * q ≤ X.card →
                  Nonempty
                    (Lax17.PathOfSets.ThreeWayClusterSplit
                      G C A B X q)

end Lax17.ParallelClusterSplitting
