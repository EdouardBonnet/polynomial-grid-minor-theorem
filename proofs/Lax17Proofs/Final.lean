import Lax17Proofs.Exposed
import Lax17Proofs.Source.Exponent8Epsilon.AsymptoticCorollary
import Lax17Proofs.Source.Exponent8Polylog.NumericalEndpoint

namespace Lax17Proofs

universe u

namespace Final

open SimpleGraph.Exponent8Epsilon

/-- Keep a paper-level theorem boundary visible when the public statement and
the source composition use different but equivalent interfaces. -/
private theorem rebuildFrom {P Q : Prop} (_dependency : Q) (result : P) : P :=
  result

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

/-- The source fanout is itself the public ceiling power root. -/
private theorem fixedRoundFanout_isCeilingPowerRoot
    {rounds g : ℕ} (hg : 2 ≤ g) :
    Lax17.PowerRoot.IsCeilingPowerRoot
      (rounds + 1) g (fixedRoundFanout rounds g) := by
  constructor
  · exact fixedRoundFanout_spec rounds g
  · intro a ha
    have hle : a ≤ fixedRoundFanout rounds g - 1 := by omega
    exact
      (Nat.pow_le_pow_left hle (rounds + 1)).trans_lt
        (fixedRoundFanout_pred_pow_lt (rounds := rounds) (g := g) hg)

/-- The public exact fixed-round statement supplies the input expected by the
purely analytic source-level conversion. -/
private theorem fixedRoundGridMinorInputFromPublic :
    FixedRoundGridMinorInput.{u} := by
  intro rounds hrounds
  have ht : 2 ≤ rounds + 1 := by omega
  rcases
      Lax17.FixedRoundGridMinor.polynomial_grid_minor_fixed_t.{u}
        (rounds + 1) ht with
    ⟨K, b, hK, hb, hpublic⟩
  refine ⟨K, b, hK, hb, ?_⟩
  intro V _ _ G target htarget htw
  have hroot :=
    fixedRoundFanout_isCeilingPowerRoot
      (rounds := rounds) (g := target) htarget
  apply Bridge.containsGridMinorToSource
  apply hpublic G htarget hroot
  simpa [Bridge.treewidth_eq] using htw

/--
---
conclusion: Lax17.PolynomialGridMinor.polynomial_grid_minor_eight_polylog
assumptions:
  - Lax17.CrossbarOrPseudoGrid.crossbarOrPseudoGrid
  - Lax17.CutMatchingTheorem.logarithmicCutMatchingExpansion
  - Lax17.ExpanderGrid.expanderContainsGrid
  - Lax17.HairyPathOfSetsFromTreewidth.hairyPathOfSetsFromTreewidth
  - Lax17.StrongPathOfSetsContainsGrid.strongPathOfSetsContainsGrid
---
There are universal positive integers $K,b$ such that treewidth at least
$K g^8 (\log_2 g)^b$ forces a $g \times g$ grid minor.
-/
theorem polynomial_grid_minor_eight_polylog :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {g : ℕ},
          2 ≤ g →
            K * g ^ 8 * (Nat.log 2 g) ^ b ≤
                Lax17.Treewidth.treewidth G →
              Lax17.GridMinor.ContainsGridMinor G g := by
  apply rebuildFrom
    (@Lax17.CrossbarOrPseudoGrid.crossbarOrPseudoGrid.{u})
  apply rebuildFrom
    (@Lax17.CutMatchingTheorem.logarithmicCutMatchingExpansion.{u})
  apply rebuildFrom (@Lax17.ExpanderGrid.expanderContainsGrid.{u})
  apply rebuildFrom
    (@Lax17.HairyPathOfSetsFromTreewidth.hairyPathOfSetsFromTreewidth.{u})
  apply rebuildFrom
    (@Lax17.StrongPathOfSetsContainsGrid.strongPathOfSetsContainsGrid.{u})
  rcases
      _root_.Lax17Proofs.SimpleGraph.Exponent8Polylog.polynomial_grid_minor_theorem_exponentEightPolylog.{u} with
    ⟨K, b, hK, hb, hmain⟩
  refine ⟨K, b, hK, hb, ?_⟩
  intro V _ _ G g hg htw
  apply Bridge.containsGridMinorToPublic
  apply hmain G hg
  simpa [SimpleGraph.Exponent8Polylog.polynomialGridMinorTreewidthBound8,
    Bridge.treewidth_eq] using htw

/--
---
conclusion: Lax17.FixedRoundGridMinor.polynomial_grid_minor_fixed_t
assumptions:
  - Lax17.CrossbarOrPseudoGrid.crossbarOrPseudoGrid
  - Lax17.CutMatchingTheorem.logarithmicCutMatchingExpansion
  - Lax17.ExpanderGrid.expanderContainsGrid
  - Lax17.HairyPathOfSetsFromTreewidth.hairyPathOfSetsFromTreewidth
  - Lax17.StrongPathOfSetsContainsGrid.strongPathOfSetsContainsGrid
---
The exact fixed-parameter theorem. For every integer $t \geq 2$, the factor
$\rho$ is explicitly characterized as the least natural number whose
$t$-th power dominates $g^2$.
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
  apply rebuildFrom
    (@Lax17.CrossbarOrPseudoGrid.crossbarOrPseudoGrid.{u})
  apply rebuildFrom
    (@Lax17.CutMatchingTheorem.logarithmicCutMatchingExpansion.{u})
  apply rebuildFrom (@Lax17.ExpanderGrid.expanderContainsGrid.{u})
  apply rebuildFrom
    (@Lax17.HairyPathOfSetsFromTreewidth.hairyPathOfSetsFromTreewidth.{u})
  apply rebuildFrom
    (@Lax17.StrongPathOfSetsContainsGrid.strongPathOfSetsContainsGrid.{u})
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
assumptions:
  - Lax17.FixedRoundGridMinor.polynomial_grid_minor_fixed_t
---
For every positive real $\varepsilon$, a constant depending only on
$\varepsilon$ makes treewidth $C g^{8+\varepsilon}$ sufficient for a
$g \times g$ grid minor.
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
      polynomial_grid_minor_theorem_exponent_eight_add_epsilon_of_input
        fixedRoundGridMinorInputFromPublic epsilon hepsilon with
    ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro V _ _ G g hg htw
  apply Bridge.containsGridMinorToPublic
  apply hmain G hg
  simpa [Bridge.treewidth_eq] using htw

end Final

end Lax17Proofs
