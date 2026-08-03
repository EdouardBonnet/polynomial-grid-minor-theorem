import Lax17Proofs.Public
import Lax17Proofs.Source.Exponent8Epsilon.AsymptoticCorollary

namespace Lax17Proofs

universe u

namespace Final

open SimpleGraph.Exponent8Epsilon

/-- The transparent public ceiling-root relation denotes exactly the
`Nat.find` value used by the recursive-slicing implementation. -/
private theorem fixedRoundRho_eq_of_isCeilingPowerRoot
    {t g rho : ℕ} (ht : 2 ≤ t) (hg : 2 ≤ g)
    (hroot : Lax17.PowerRoot.IsCeilingPowerRoot t g rho) :
    fixedRoundRho t g = rho := by
  have heq : t - 1 + 1 = t := by omega
  apply Nat.le_antisymm
  · by_contra hle
    have hrho_lt : rho < fixedRoundRho t g := Nat.lt_of_not_ge hle
    have hrho_pred : rho ≤ fixedRoundRho t g - 1 := by omega
    have hpow_le :
        rho ^ t ≤ (fixedRoundRho t g - 1) ^ t :=
      Nat.pow_le_pow_left hrho_pred t
    have hpred : (fixedRoundRho t g - 1) ^ t < g ^ 2 := by
      simpa [fixedRoundRho, heq] using
        fixedRoundFanout_pred_pow_lt (rounds := t - 1) (g := g) hg
    exact (not_lt_of_ge hroot.1) (hpow_le.trans_lt hpred)
  · by_contra hle
    have hfixed_lt : fixedRoundRho t g < rho := Nat.lt_of_not_ge hle
    have htooSmall := hroot.2 (fixedRoundRho t g) hfixed_lt
    exact (not_lt_of_ge (fixedRoundRho_spec (t := t) (g := g) (by omega)))
      htooSmall

/--
---
conclusion: Lax17.PolynomialGridMinor.polynomial_grid_minor_fixed_t
---
The exact fixed-parameter theorem.  For every integer `t ≥ 2`, the factor
`rho` is explicitly characterized as the least natural number whose `t`-th
power dominates `g²`.
-/
theorem polynomial_grid_minor_fixed_t :
    ∀ t : ℕ, 2 ≤ t →
      ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) {g rho : ℕ},
            2 ≤ g →
              Lax17.PowerRoot.IsCeilingPowerRoot t g rho →
                K * g ^ 8 * rho * (Nat.log 2 g) ^ b ≤
                    Lax17.Treewidth.treewidth G →
                  Lax17.GridMinor.ContainsGridMinor G g := by
  intro t ht
  rcases
      SimpleGraph.Exponent8Epsilon.polynomial_grid_minor_theorem_fixed_t
        t ht with
    ⟨K, b, hK, hb, hmain⟩
  refine ⟨K, b, hK, hb, ?_⟩
  intro V _ _ G g rho hg hroot htw
  have hrho : fixedRoundRho t g = rho :=
    fixedRoundRho_eq_of_isCeilingPowerRoot ht hg hroot
  apply Bridge.containsGridMinorToPublic
  apply hmain G hg
  simpa [hrho, Bridge.treewidth_eq] using htw

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
