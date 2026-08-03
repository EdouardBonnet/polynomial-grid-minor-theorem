import Lax17Proofs.Source.Exponent8Epsilon.FixedRoundSection5Assembly
import Lax17Proofs.Source.Section4Assembly
import Lax17Proofs.Source.Theorem41

namespace Lax17Proofs

/-!
# The fixed-round local crossbar dichotomy

For every positive fixed number of refinement rounds, the local threshold is
`2^(4*rounds+20) * g^8 * fixedRoundFanout rounds g * (log_2 g + 1)`.
The graph-theoretic control flow is exactly the proved exponent-8.5 local
dichotomy; only its finite numerical controller has been generalized.
-/

namespace SimpleGraph
namespace Exponent8Epsilon

universe u

open Finset
open Section4Reduction

def CrossbarDichotomyInputFixedRound (c rounds : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : _root_.SimpleGraph V) {g kappa : ℕ}
    {A B X : Finset V},
      0 < rounds →
      2 ≤ g →
      CrossbarContract.IsPowerOfTwo g →
      A.card = kappa →
      B.card = kappa →
      X.card = kappa →
      Disjoint A B →
      Disjoint A X →
      Disjoint B X →
      fixedRoundLocalThreshold rounds g ≤ kappa →
      (∀ x ∈ X, DegreeEquals H x 1) →
      (Pab : PathPacking H A B) →
      Pab.card = kappa →
      (Pax : PathPacking H A X) →
      Pax.card = kappa →
      Nonempty (Crossbar H A B X (g ^ 2)) ∨
        ∃ ell w : ℕ,
          g ^ 2 ≤ c * ell ∧
          g ^ 2 ≤ c * w ∧
          CrossbarContract.HasStrongPathOfSetsMinor H ell w

namespace PseudoGrid

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B X : Finset V} {rounds g kappa : ℕ}
variable {P : PerfectPathPacking G A B}
variable {Q : PerfectPathPacking G A X}

theorem discardCost_le_fixedRoundInitialCost
    (Gamma : PseudoGrid G A B X g (64 * g ^ 4) P Q)
    (hrounds : 0 < rounds) :
    (64 * g ^ 4) * (2 * g ^ 2) ≤
      fixedRoundM rounds g 0 * fixedRoundWidth rounds g 0 +
        (fixedRoundM rounds g 0 + 1) * Gamma.rowPacking.card := by
  by_cases hg0 : g = 0
  · subst g
    simp
  have hgpos : 0 < g := Nat.pos_of_ne_zero hg0
  have hf : 1 ≤ fixedRoundFanout rounds g := by
    have hspec := fixedRoundFanout_spec rounds g
    have hfp : 0 < fixedRoundFanout rounds g := by
      by_contra h
      have hf0 : fixedRoundFanout rounds g = 0 :=
        Nat.eq_zero_of_not_pos h
      rw [hf0, zero_pow (by omega : rounds + 1 ≠ 0)] at hspec
      have hgpow : 0 < g ^ 2 := by positivity
      omega
    omega
  have hm : 16 * g ^ 2 ≤ fixedRoundM rounds g 0 := by
    have htwo : 2 ≤ 2 ^ rounds := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ rounds :=
          Nat.pow_le_pow_right (n := 2) (by decide) hrounds
    have hL : 1 ≤ fixedRoundLogFactor g := by
      simp [fixedRoundLogFactor]
    calc
      16 * g ^ 2 = 8 * 2 * g ^ 2 * 1 * 1 := by ring
      _ ≤ 8 * 2 ^ rounds * g ^ 2 *
          fixedRoundFanout rounds g * fixedRoundLogFactor g := by gcongr
      _ = fixedRoundM rounds g 0 := by simp [fixedRoundM]
  have hw : 8 * g ^ 4 ≤ fixedRoundWidth rounds g 0 := by
    calc
      8 * g ^ 4 ≤ 16 * g ^ 4 :=
        Nat.mul_le_mul_right (g ^ 4) (by omega)
      _ ≤ fixedRoundWidth rounds g 0 := by
        simpa [fixedRoundWidth] using
          fixedRoundWidthRev_base_le g
            (fixedRoundFanout rounds g) rounds hf
  calc
    (64 * g ^ 4) * (2 * g ^ 2) =
        (16 * g ^ 2) * (8 * g ^ 4) := by ring
    _ ≤ fixedRoundM rounds g 0 * fixedRoundWidth rounds g 0 :=
      Nat.mul_le_mul hm hw
    _ ≤ fixedRoundM rounds g 0 * fixedRoundWidth rounds g 0 +
          (fixedRoundM rounds g 0 + 1) * Gamma.rowPacking.card :=
      Nat.le_add_right _ _

theorem fixedRound_slicing_budget
    (Gamma : PseudoGrid G A B X g (64 * g ^ 4) P Q)
    (hrounds : 0 < rounds)
    (hg : 2 ≤ g)
    (hlarge : fixedRoundLocalThreshold rounds g ≤ kappa)
    (hPcard : P.card = kappa) :
    fixedRoundM rounds g 0 * fixedRoundWidth rounds g 0 +
          (fixedRoundM rounds g 0 + 1) * Gamma.rowPacking.card ≤
      Gamma.goodQSet.card := by
  let N := Gamma.rowPacking.card
  have hNupper : N ≤ 64 * g ^ 6 := by
    calc
      N = Gamma.reservedUnion.card := by simp [N]
      _ ≤ (64 * g ^ 4) * g ^ 2 := Gamma.reservedUnion_card_le
      _ = 64 * g ^ 6 := by ring
  let p := explicitFixedRoundParameters rounds g N (32 * g ^ 4)
    hrounds hg hNupper rfl
  let cost := fixedRoundM rounds g 0 * fixedRoundWidth rounds g 0 +
    (fixedRoundM rounds g 0 + 1) * Gamma.rowPacking.card
  let discarded := (64 * g ^ 4) * (2 * g ^ 2)
  have hdiscard : discarded ≤ cost := by
    simpa [discarded, cost] using
      discardCost_le_fixedRoundInitialCost Gamma hrounds
  have hlocal : 8 * cost ≤ fixedRoundLocalThreshold rounds g := by
    simpa [p, N, cost, explicitFixedRoundParameters] using p.local_cost
  have htotal : 4 * (discarded + cost) ≤ kappa := by
    calc
      4 * (discarded + cost) ≤ 4 * (cost + cost) :=
        Nat.mul_le_mul_left 4 (Nat.add_le_add_right hdiscard cost)
      _ = 8 * cost := by ring
      _ ≤ fixedRoundLocalThreshold rounds g := hlocal
      _ ≤ kappa := hlarge
  apply Gamma.goodQSet_card_lower_bound_of_packing_bound
  rw [hPcard]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
  simpa [discarded, cost, Nat.mul_comm] using htotal

theorem hasStrongPathOfSetsMinor_of_noCrossbar_fixedRound
    (Gamma : PseudoGrid G A B X g (64 * g ^ 4) P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hrounds : 0 < rounds)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hlarge : fixedRoundLocalThreshold rounds g ≤ kappa)
    (hPcard : P.card = kappa)
    (hXdisjoint : ∀ p : P.Index, Disjoint X (P.path p).vertexSet)
    (hnoCrossbar : ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    ∃ ell w : ℕ,
      g ^ 2 ≤ 20000 * ell ∧
      g ^ 2 ≤ 20000 * w ∧
      CrossbarContract.HasStrongPathOfSetsMinor G ell w := by
  have hbudget := fixedRound_slicing_budget
    Gamma hrounds hg hlarge hPcard
  have hgoodPos : 0 < Gamma.goodQSet.card := by
    have hmain : 0 < fixedRoundM rounds g 0 *
        fixedRoundWidth rounds g 0 := by
      apply Nat.mul_pos
      · exact fixedRoundM_pos hg 0
      · exact fixedRoundWidthRev_pos (by omega)
    exact hmain.trans_le
      ((Nat.le_add_right _ _).trans hbudget)
  have hgood : Gamma.goodQSet.Nonempty := Finset.card_pos.mp hgoodPos
  have hrowBounds :
      64 * g ^ 4 ≤ Gamma.rowPacking.card ∧
      Gamma.rowPacking.card ≤ 64 * g ^ 6 := by
    have h := Gamma.rowPacking_card_bounds_of_goodQSet_nonempty hgood
    exact ⟨h.1, by
      simpa only [show (64 * g ^ 4) * g ^ 2 = 64 * g ^ 6 by ring]
        using h.2⟩
  rcases
      exists_reduced_weakPathOfSetsSystem_fixedRound
        Gamma hminimal hrounds hg hpow hrowBounds.1 hrowBounds.2 le_rfl
        hbudget hXdisjoint hnoCrossbar with
    ⟨Root, hReduced, ⟨Pweak⟩⟩
  let w := Section4Assembly.strongifiedWidth (g ^ 2)
  let Dstrong :=
    Section4Assembly.strongificationData_of_weakPathOfSetsSystem_maxDegreeFour
      Pweak (Root.state.reducedGraph_maxDegreeAtMost_four hReduced)
  let Pstrong : StrongPathOfSetsSystem
      (Root.state.reducedGraph hReduced) (g ^ 2) w :=
    Section46.strong_pathOfSetsSystem_of_strongificationData Pweak Dstrong
  refine ⟨g ^ 2, w, ?_, ?_, ?_⟩
  · simpa using Nat.le_mul_of_pos_left (g ^ 2) (by norm_num : 0 < 20000)
  · exact Section4Assembly.le_twentyThousand_mul_strongifiedWidth
      (by positivity)
  · exact
      ⟨Root.state.RowVertex, inferInstance, inferInstance,
        Root.state.reducedGraph hReduced,
        Root.state.reducedGraph_isMinor hReduced, ⟨Pstrong⟩⟩

end PseudoGrid

theorem crossbarDichotomyInputFixedRound_proved (rounds : ℕ) :
    CrossbarDichotomyInputFixedRound.{u} 20000 rounds := by
  intro V _ _ H g kappa A B X hrounds hg hpow hA hB hX hAB hAX hBX
    hlarge hdegree Pab hPab Pax hPax
  have hdepthCost : (64 * g ^ 4) * (2 * g ^ 2) ≤ kappa := by
    have hg68 : g ^ 6 ≤ g ^ 8 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hf : 1 ≤ fixedRoundFanout rounds g :=
      fixedRoundFanout_pos (rounds := rounds) hg
    have hL : 1 ≤ fixedRoundLogFactor g := by simp [fixedRoundLogFactor]
    have hC : 128 ≤ fixedRoundLocalConstant rounds := by
      unfold fixedRoundLocalConstant
      calc
        128 = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ (4 * rounds + 20) :=
          Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
    calc
      (64 * g ^ 4) * (2 * g ^ 2) = 128 * g ^ 6 := by ring
      _ ≤ 128 * g ^ 8 := Nat.mul_le_mul_left 128 hg68
      _ ≤ fixedRoundLocalConstant rounds * g ^ 8 := by gcongr
      _ = fixedRoundLocalConstant rounds * g ^ 8 * 1 * 1 := by ring
      _ ≤ fixedRoundLocalThreshold rounds g := by
        simp only [fixedRoundLocalThreshold]
        gcongr
      _ ≤ kappa := hlarge
  have hDle : 64 * g ^ 4 ≤ kappa / (2 * g ^ 2) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * g ^ 2)).2
    exact hdepthCost
  rcases
      theorem_four_one_of_pathPackings
        H hg hpow hA hB hX hAB hAX hBX hdegree
        Pab hPab Pax hPax (by
          have : 0 < 64 * g ^ 4 := by positivity
          omega) hDle with
    ⟨P, Q, hPcard, hQcard, hminimal, hconclusion⟩
  rcases hconclusion with hcross | hpseudo
  · exact Or.inl hcross
  · by_cases hcross : Nonempty (Crossbar H A B X (g ^ 2))
    · exact Or.inl hcross
    · rcases hpseudo with ⟨Gamma⟩
      have hXdisjoint :
          ∀ p : P.Index, Disjoint X (P.path p).vertexSet := by
        let Setup : Theorem41Setup
            H A B X g kappa (64 * g ^ 4) P Q :=
          { two_le_g := hg
            g_power_two := hpow
            A_card := hA
            B_card := hB
            X_card := hX
            disjoint_A_B := hAB
            disjoint_A_X := hAX
            disjoint_B_X := hBX
            degree_X := hdegree
            P_card := hPcard
            Q_card := hQcard
            minimal_pair := hminimal
            D_pos := by
              have : 0 < 64 * g ^ 4 := by positivity
              omega
            D_le := hDle }
        intro p
        exact (Setup.P_path_disjoint_X p).symm
      exact Or.inr <|
        PseudoGrid.hasStrongPathOfSetsMinor_of_noCrossbar_fixedRound
          Gamma hminimal hrounds hg hpow hlarge hPcard hXdisjoint hcross

theorem exists_crossbarDichotomyInputFixedRound_proved (rounds : ℕ) :
    ∃ c : ℕ, 0 < c ∧ CrossbarDichotomyInputFixedRound.{u} c rounds :=
  ⟨20000, by norm_num, crossbarDichotomyInputFixedRound_proved rounds⟩

end Exponent8Epsilon
end SimpleGraph

end Lax17Proofs
