import Lax17Proofs.Source.Exponent8Epsilon.FixedRoundLocalDichotomy
import Lax17Proofs.Source.CutMatchingGame
import Lax17Proofs.Source.HairyPathOfSetsComplete
import Lax17Proofs.Source.ChekuriChuzhoyWP6Complete

namespace Lax17Proofs

/-!
# Global consumers of the fixed-round local dichotomy

The proofs here are threshold-parametric copies of the established
exponent-8.5 propagation.  The crossbar and strong Path-of-Sets consumers are
unchanged; `rounds` appears only in `fixedRoundLocalThreshold`.
-/

namespace SimpleGraph
namespace Exponent8Epsilon

universe u

theorem crossbar_or_strong_minor_in_hairLocalGraph_fixedRound
    (rounds : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : _root_.SimpleGraph V} {ell w g : ℕ}
      (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
        0 < rounds →
        2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
        fixedRoundLocalThreshold rounds g ≤ w →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)) ∨
          ∃ ell' w' : ℕ,
            g ^ 2 ≤ 20000 * ell' ∧
            g ^ 2 ≤ 20000 * w' ∧
            CrossbarContract.HasStrongPathOfSetsMinor
              (Hsys.hairLocalGraph i) ell' w' := by
  intro V _ _ G ell w g Hsys i hrounds hg hpow hlarge
  rcases Hsys.exists_left_right_linkage_inHairLocalGraph_with_staysIn i with
    ⟨Pab, hPab_card, _⟩
  rcases Hsys.exists_left_y_perfect_linkage_inHairLocalGraph i with
    ⟨Pax, hPax_card⟩
  have hleft_y : Disjoint (Hsys.base.left i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvleft hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.left_subset_cluster i hvleft)
  have hright_y : Disjoint (Hsys.base.right i) (Hsys.y i) := by
    rw [Finset.disjoint_left]
    intro v hvright hvy
    exact Finset.disjoint_left.mp (Hsys.hairCluster_disjoint_base i i)
      (Hsys.y_subset_hairCluster i hvy)
      (Hsys.base.right_subset_cluster i hvright)
  exact crossbarDichotomyInputFixedRound_proved rounds
    (Hsys.hairLocalGraph i) hrounds hg hpow
    (Hsys.base.left_card i) (Hsys.base.right_card i) (Hsys.y_card i)
    (Hsys.base.left_right_disjoint i) hleft_y hright_y hlarge
    (fun x hx => Hsys.hairLocalGraph_degreeEquals_one_of_mem_y i hx)
    Pab hPab_card Pax.toPathPacking (by simpa using hPax_card)

theorem crossbar_or_strong_minor_in_hairyCluster_fixedRound
    (rounds : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : _root_.SimpleGraph V} {ell w g : ℕ}
      (Hsys : HairyPathOfSetsSystem G ell w) (i : Fin ell),
        0 < rounds →
        2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
        fixedRoundLocalThreshold rounds g ≤ w →
        Nonempty (Crossbar (Hsys.hairLocalGraph i)
          (Hsys.base.left i) (Hsys.base.right i)
          (Hsys.y i) (g ^ 2)) ∨
          ∃ ell' w' : ℕ,
            g ^ 2 ≤ 20000 * ell' ∧
            g ^ 2 ≤ 20000 * w' ∧
            CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  intro V _ _ G ell w g Hsys i hrounds hg hpow hlarge
  rcases crossbar_or_strong_minor_in_hairLocalGraph_fixedRound rounds
      Hsys i hrounds hg hpow hlarge with hcrossbar | hstrong
  · exact Or.inl hcrossbar
  · rcases hstrong with ⟨ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw,
      hminor.mono (Hsys.hairLocalGraph_le i)⟩

theorem local_crossbars_or_strong_minor_fixedRound
    (rounds : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : _root_.SimpleGraph V} {ell w g : ℕ}
      (Hsys : HairyPathOfSetsSystem G ell w),
        0 < rounds →
        2 ≤ g →
        CrossbarContract.IsPowerOfTwo g →
        fixedRoundLocalThreshold rounds g ≤ w →
        (∀ i : Fin ell,
          HairyCrossbarGrid.OneBasedOdd i →
          Nonempty (Crossbar (Hsys.hairLocalGraph i)
            (Hsys.base.left i) (Hsys.base.right i)
            (Hsys.y i) (g ^ 2))) ∨
          ∃ ell' w' : ℕ,
            g ^ 2 ≤ 20000 * ell' ∧
            g ^ 2 ≤ 20000 * w' ∧
            CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  intro V _ _ G ell w g Hsys hrounds hg hpow hlarge
  by_cases hstrong :
      ∃ i : Fin ell, HairyCrossbarGrid.OneBasedOdd i ∧
        ∃ ell' w' : ℕ,
          g ^ 2 ≤ 20000 * ell' ∧
          g ^ 2 ≤ 20000 * w' ∧
          CrossbarContract.HasStrongPathOfSetsMinor G ell' w'
  · rcases hstrong with ⟨_, _, ell', w', hell, hw, hminor⟩
    exact Or.inr ⟨ell', w', hell, hw, hminor⟩
  · refine Or.inl ?_
    intro i hi
    rcases crossbar_or_strong_minor_in_hairyCluster_fixedRound rounds
        Hsys i hrounds hg hpow hlarge with hcrossbar | hminor
    · exact hcrossbar
    · exact False.elim (hstrong ⟨i, hi, hminor⟩)

theorem gridMinor_or_strong_minor_of_hairy_fixedRound (rounds : ℕ) :
    ∃ cGrid : ℕ, 0 < cGrid ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          0 < rounds →
          2 ≤ g →
          CrossbarContract.IsPowerOfTwo g →
          MaxDegreeAtMost G 3 →
          cGrid * Nat.log 2 g ≤ ell →
          g ^ 2 ≤ w →
          fixedRoundLocalThreshold rounds g ≤ w →
          (∃ g' : ℕ,
            g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
            ContainsGridMinor G g') ∨
            ∃ ell' w' : ℕ,
              g ^ 2 ≤ 20000 * ell' ∧
              g ^ 2 ≤ 20000 * w' ∧
              CrossbarContract.HasStrongPathOfSetsMinor G ell' w' := by
  rcases
      HairyCrossbarGrid.exists_gridMinor_of_hairy_pathOfSets_and_crossbars_of_cutMatchingGame
      with ⟨cGrid, hcGrid, hgrid⟩
  refine ⟨cGrid, hcGrid, ?_⟩
  intro V _ _ G ell w g Hsys hrounds hg hpow hdegree hell hw hlarge
  rcases local_crossbars_or_strong_minor_fixedRound rounds
      Hsys hrounds hg hpow hlarge with hcrossbars | hstrong
  · exact Or.inl (hgrid G Hsys hg hpow hdegree hell hw hcrossbars)
  · exact Or.inr hstrong

theorem square_le_of_scaled_square_le_fixedRound
    {g r n : ℕ} (hscaled : 20000 * r ^ 2 ≤ g ^ 2)
    (hn : g ^ 2 ≤ 20000 * n) : r ^ 2 ≤ n :=
  Nat.le_of_mul_le_mul_left (hscaled.trans hn) (by norm_num)

theorem gridMinor_or_gridMinor_of_hairy_fixedRound (rounds : ℕ) :
    ∃ cGrid cStrong : ℕ,
      0 < cGrid ∧ 0 < cStrong ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w g r : ℕ}
        (Hsys : HairyPathOfSetsSystem G ell w),
          0 < rounds →
          2 ≤ g →
          2 ≤ r →
          CrossbarContract.IsPowerOfTwo g →
          MaxDegreeAtMost G 3 →
          cGrid * Nat.log 2 g ≤ ell →
          g ^ 2 ≤ w →
          fixedRoundLocalThreshold rounds g ≤ w →
          20000 * r ^ 2 ≤ g ^ 2 →
          (∃ g' : ℕ,
            g ≤ cGrid * g' * (Nat.log 2 g) ^ 2 ∧
            ContainsGridMinor G g') ∨
            ∃ r' : ℕ,
              r ≤ cStrong * r' ∧ ContainsGridMinor G r' := by
  rcases gridMinor_or_strong_minor_of_hairy_fixedRound rounds with
    ⟨cGrid, hcGrid, hmain⟩
  rcases
      PolynomialGridMinor.strongMinorGridInput_of_corollary32Input
        ChekuriChuzhoy.corollary32Input_proved with
    ⟨cStrong, hcStrong, hstrongGrid⟩
  refine ⟨cGrid, cStrong, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w g r Hsys hrounds hg hr hpow hdegree hell hw
    hlarge hscaled
  rcases hmain G Hsys hrounds hg hpow hdegree hell hw hlarge with
    hgrid | hstrong
  · exact Or.inl hgrid
  · rcases hstrong with ⟨ell', w', hell', hw', hminor⟩
    exact Or.inr (hstrongGrid hr
      (square_le_of_scaled_square_le_fixedRound hscaled hell')
      (square_le_of_scaled_square_le_fixedRound hscaled hw') hminor)

/-- Parameterized graph theorem.  All remaining hypotheses are explicit
natural-number inequalities; every semantic paper input is produced by a
proved declaration. -/
theorem containsGridMinor_of_treewidth_parameters_fixedRound
    (rounds : ℕ) :
    ∃ cHair cHairLog cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cGrid ∧ 0 < cStrong ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {ell w k g r target : ℕ},
          1 < ell →
          1 < w →
          1 < k →
          k ≤ treewidth G →
          cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k →
          0 < rounds →
          2 ≤ g →
          2 ≤ r →
          CrossbarContract.IsPowerOfTwo g →
          cGrid * Nat.log 2 g ≤ ell →
          g ^ 2 ≤ w →
          fixedRoundLocalThreshold rounds g ≤ w →
          20000 * r ^ 2 ≤ g ^ 2 →
          cGrid * target * (Nat.log 2 g) ^ 2 ≤ g →
          cStrong * target ≤ r →
          ContainsGridMinor G target := by
  rcases PolynomialGridMinor.exists_hairyPathOfSetsInput_proved with
    ⟨cHair, cHairLog, hcHair, hcHairLog, hhairy⟩
  rcases gridMinor_or_gridMinor_of_hairy_fixedRound rounds with
    ⟨cGrid, cStrong, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cGrid, cStrong,
    hcHair, hcHairLog, hcGrid, hcStrong, ?_⟩
  intro V _ _ G ell w k g r target hell hw hk htw hhairyLarge
    hrounds hg hr hpow hellGrid hwGrid hlarge hscaled
    htargetDirect htargetStrong
  rcases hhairy G hell hw hk htw hhairyLarge with
    ⟨H, hHG, hdegree, ⟨Hsys⟩⟩
  rcases hmain H Hsys hrounds hg hr hpow hdegree hellGrid hwGrid
      hlarge hscaled with hdirect | hstrong
  · rcases hdirect with ⟨g', hproduced, hgrid⟩
    exact (hgrid.mono hHG).of_order_le
      (PolynomialGridMinor.le_gridOrder_of_direct_branch_bound
        hcGrid hg htargetDirect hproduced)
  · rcases hstrong with ⟨r', hproduced, hgrid⟩
    have htarget_le : target ≤ r' :=
      PolynomialGridMinor.le_of_const_mul_le_const_mul hcStrong
        (htargetStrong.trans hproduced)
    exact (hgrid.mono hHG).of_order_le htarget_le

end Exponent8Epsilon
end SimpleGraph

end Lax17Proofs
