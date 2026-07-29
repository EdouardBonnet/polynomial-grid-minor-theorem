import Mathlib.Data.Nat.Log
import Lax17.Expansion

/-!
---
title: Cut-matching expansion theorem
type: theorem
---
On every finite even vertex set, a logarithmic-squared number of perfect
matching rounds can be chosen across successive bisections so that the union
of the matchings is a constant edge-expander.  This is the existential form of
the cut-matching game used in the grid-minor proof; algorithmic running-time
claims are intentionally omitted.
-/

namespace Lax17.CutMatchingTheorem

universe u

/-- A cut-matching transcript of \(O(\log^2 n)\) rounds whose union is a
constant edge-expander. -/
axiom logarithmicCutMatchingExpansion :
  ∃ c : ℕ, 0 < c ∧
    ∀ (V : Type u) [Fintype V] [DecidableEq V],
      2 ≤ Fintype.card V → (∃ n : ℕ, Fintype.card V = 2 * n) →
        ∃ rounds : ℕ,
          ∃ T : Lax17.Expansion.CutMatchingTranscript V rounds,
            rounds ≤ c * (Nat.log 2 (Fintype.card V)) ^ 2 ∧
              Lax17.Expansion.IsEdgeExpander T.unionGraph 1 4

end Lax17.CutMatchingTheorem
