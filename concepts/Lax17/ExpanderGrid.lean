import Mathlib.Data.Nat.Log
import Lax17.Degree
import Lax17.Expansion
import Lax17.GridMinor

/-!
---
title: Grid minors in bounded-degree expanders
type: theorem
---
A sufficiently large bounded-degree constant edge-expander contains a
prescribed square grid as a minor.  The size threshold is polynomial in the
grid order and maximum degree, with a polylogarithmic factor in the number of
vertices.
-/

namespace Lax17.ExpanderGrid

universe u

/-- The bounded-degree expander-to-grid theorem. -/
axiom expanderContainsGrid :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (Δ g : ℕ),
        Lax17.Expansion.IsEdgeExpander G 1 4 →
          Lax17.Degree.MaximumAtMost G Δ →
            2 ≤ g →
              c * (Δ + 1) ^ 2 * g ^ 2 *
                  (Nat.log 2 (Fintype.card V)) ^ d ≤ Fintype.card V →
                Lax17.GridMinor.ContainsGridMinor G g

end Lax17.ExpanderGrid
