import Lax17.GridMinor
import Lax17.PathOfSets

/-!
---
title: Local routing-or-grid alternative
type: theorem
---
In one strong cluster, large equal terminal sets either admit the desired
local routing or force the target grid minor.
-/

namespace Lax17.LocalRoutingOrGrid

universe u

/-- In one strong cluster, large equal terminal sets either admit the desired
local routing or force the target grid minor. -/
axiom localRoutingOrGrid :
  ∃ c : ℕ, 0 < c ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {ℓ w g k : ℕ}
      (P : Lax17.PathOfSets.StrongSystem G ℓ w)
      (i : Fin ℓ) (A B : Finset V),
        A ⊆ P.cluster i → B ⊆ P.cluster i →
          Disjoint A B → A.card = k → B.card = k →
            2 ≤ g → c * g ^ 2 ≤ k →
              Lax17.GridMinor.ContainsGridMinor G g ∨
                ∃ Q : Lax17.Paths.VertexLinkage G A B k,
                  ∀ j : Fin k, (Q.path j).StaysIn (P.cluster i)

end Lax17.LocalRoutingOrGrid
