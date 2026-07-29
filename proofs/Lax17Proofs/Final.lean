import Lax17Proofs.Exposed
import Lax17Proofs.Source.PolynomialGridMinor

namespace Lax17Proofs

universe u

namespace Final

/-- Keep a paper-level theorem boundary visible when the public statement and
the source composition use different but equivalent interfaces. -/
private theorem rebuildFrom {P Q : Prop} (_dependency : Q) (result : P) : P :=
  result

/-- The public hairy path-of-sets theorem supplies the exact high-level input
used by the exponent-ten composition. -/
private theorem hairyInputFromPublic :
    ∃ cHair cHairLog : ℕ, 0 < cHair ∧ 0 < cHairLog ∧
      Lax17Proofs.SimpleGraph.PolynomialGridMinor.HairyPathOfSetsInput.{u}
        cHair cHairLog := by
  rcases
      Lax17.HairyPathOfSetsFromTreewidth.hairyPathOfSetsFromTreewidth.{u} with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  refine ⟨cHair, cHairLog, hcHair, hcHairLog, ?_⟩
  intro V _ _ G ell w k hell hw hk htree hlarge
  rw [Lax17Proofs.Bridge.treewidth_eq] at htree
  rcases hhairy G hell hw hk htree hlarge with
    ⟨H, hHG, hdegree, ⟨S⟩⟩
  exact
    ⟨H, hHG, hdegree,
      ⟨Lax17Proofs.Bridge.hairyPathOfSetsToSource S⟩⟩

/-- The public exponent-ten dichotomy supplies the Section 4 input expected by
the composition theorem. -/
private theorem crossbarInputFromPublic :
    ∃ cCross : ℕ, 0 < cCross ∧
      Lax17Proofs.SimpleGraph.HairyPathOfSetsSystem.CrossbarDichotomyInput10.{u}
        cCross := by
  rcases
      Lax17.ExponentTenCrossbarDichotomy.exponentTenCrossbarDichotomy.{u} with
    ⟨cCross, hcCross, hcrossbar⟩
  refine ⟨cCross, hcCross, ?_⟩
  intro V _ _ G g kappa A B X hg hpower hA hB hX hAB hAX hBX
    hlarge hdegree Pab hPab Pax hPax
  have hpowerPublic : Lax17.Crossbar.IsPowerOfTwo g := by
    simpa [Lax17.Crossbar.IsPowerOfTwo,
      Lax17Proofs.SimpleGraph.CrossbarContract.IsPowerOfTwo] using hpower
  have hdegreePublic :
      ∀ x ∈ X, Lax17.Degree.Exactly G x 1 := by
    simpa [Lax17.Degree.Exactly, Lax17.Degree.IsNeighbourhood,
      Lax17Proofs.SimpleGraph.DegreeEquals,
      Lax17Proofs.SimpleGraph.IsNeighborFinset] using hdegree
  rcases
      hcrossbar G hg hpowerPublic hA hB hX hAB hAX hBX hlarge
        hdegreePublic
        (Lax17Proofs.Bridge.pathPackingToPublic Pab kappa hPab)
        (Lax17Proofs.Bridge.pathPackingToPublic Pax kappa hPax) with
    hsystem | hminor
  · rcases hsystem with ⟨C⟩
    exact Or.inl ⟨Lax17Proofs.Bridge.crossbarToSource C⟩
  · rcases hminor with ⟨length, width, hlength, hwidth, hsystemMinor⟩
    exact
      Or.inr
        ⟨length, width, hlength, hwidth,
          Lax17Proofs.Bridge.strongPathOfSetsMinorToSource hsystemMinor⟩

/-- The public path-of-sets-to-grid theorem is a direct realization of the
Corollary 3.2 input used by the minor-closed strong branch. -/
private theorem corollary32InputFromPublic :
    Lax17Proofs.SimpleGraph.ChekuriChuzhoy.Corollary32Input.{u} := by
  intro V _ _ G g hg P
  left
  apply Lax17Proofs.Bridge.containsGridMinorToSource
  exact
    Lax17.StrongPathOfSetsContainsGrid.strongPathOfSetsContainsGrid
      G ⟨Lax17Proofs.Bridge.strongPathOfSetsToPublic P⟩
        hg le_rfl le_rfl

/-- The public strong path theorem therefore supplies the scaled
strong-minor-to-grid input. -/
private theorem strongGridInputFromPublic :
    ∃ cStrong : ℕ, 0 < cStrong ∧
      Lax17Proofs.SimpleGraph.PolynomialGridMinor.StrongMinorGridInput.{u}
        cStrong :=
  Lax17Proofs.SimpleGraph.PolynomialGridMinor.strongMinorGridInput_of_corollary32Input
    corollary32InputFromPublic

/--
---
conclusion: Lax17.PolynomialGridMinor.polynomial_grid_minor
assumptions:
  - Lax17.CutMatchingTheorem.logarithmicCutMatchingExpansion
  - Lax17.ExponentTenCrossbarDichotomy.exponentTenCrossbarDichotomy
  - Lax17.ExpanderGrid.expanderContainsGrid
  - Lax17.HairyPathOfSetsFromTreewidth.hairyPathOfSetsFromTreewidth
  - Lax17.StrongPathOfSetsContainsGrid.strongPathOfSetsContainsGrid
---
The direct exponent-ten polynomial grid-minor theorem, assembled from the
exposed hairy-system theorem, exponent-ten crossbar dichotomy, and
path-of-sets-to-grid theorem.
-/
theorem polynomial_grid_minor :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) {g : ℕ},
          2 ≤ g →
            c * g ^ 10 * (Nat.log 2 g) ^ d ≤
                Lax17.Treewidth.treewidth G →
              Lax17.GridMinor.ContainsGridMinor G g := by
  apply rebuildFrom
    (@Lax17.CutMatchingTheorem.logarithmicCutMatchingExpansion.{u})
  apply rebuildFrom (@Lax17.ExpanderGrid.expanderContainsGrid.{u})
  rcases
      Lax17Proofs.SimpleGraph.PolynomialGridMinor.polynomial_grid_minor_theorem_degree10_of_inputs10_and_cutMatchingGame
        hairyInputFromPublic crossbarInputFromPublic
          strongGridInputFromPublic with
    ⟨c, d, hc, hd, hmain⟩
  refine ⟨c, d, hc, hd, ?_⟩
  intro V _ _ G g hg htw
  apply Lax17Proofs.Bridge.containsGridMinorToPublic
  apply hmain G hg
  rw [Lax17Proofs.Bridge.treewidth_eq]
  simpa [Lax17Proofs.SimpleGraph.polynomialGridMinorTreewidthBound10]
    using htw

end Final

end Lax17Proofs
