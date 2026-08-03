import Lax17Proofs.Public
import Lax17Proofs.Source.Exponent8Epsilon.AsymptoticCorollary

namespace Lax17Proofs

universe u

namespace Final

open SimpleGraph.Exponent8Epsilon

/--
---
conclusion: Lax17.PolynomialGridMinor.polynomial_grid_minor_eight_add_epsilon
---
For every positive real `epsilon`, a constant depending only on `epsilon`
makes treewidth `C * g^(8 + epsilon)` sufficient for a `g × g` grid minor.
-/
theorem polynomial_grid_minor_eight_add_epsilon :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 < C ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) {g : ℕ},
            2 ≤ g →
              C * (g : ℝ) ^ ((8 : ℝ) + epsilon) ≤
                  (Lax17.Treewidth.treewidth G : ℝ) →
                Lax17.GridMinor.ContainsGridMinor G g := by
  intro epsilon hepsilon
  rcases
      SimpleGraph.Exponent8Epsilon.polynomial_grid_minor_theorem_exponent_eight_add_epsilon
        epsilon hepsilon with
    ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro V _ _ G g hg htw
  apply Bridge.containsGridMinorToPublic
  apply hmain G hg
  simpa [Bridge.treewidth_eq] using htw

end Final

end Lax17Proofs
