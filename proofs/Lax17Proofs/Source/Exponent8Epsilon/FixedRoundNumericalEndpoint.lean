import Lax17Proofs.Source.Exponent8Epsilon.FixedRoundGlobalDichotomy

namespace Lax17Proofs

/-!
# Closed numerical endpoint for every fixed number of rounds

The kernel-facing theorem uses the exact natural-number factor
`fixedRoundFanout rounds target`.  When `rounds + 1 = t`, this is the least
integer whose `t`-th power dominates `target^2`.
-/

namespace SimpleGraph
namespace Exponent8Epsilon

universe u

noncomputable def polynomialGridMinorTreewidthBoundFixedRound
    (rounds K b target : ℕ) : ℕ :=
  K * target ^ 8 * fixedRoundFanout rounds target *
    (Nat.log 2 target) ^ b

noncomputable def widthScaleFixedRound (rounds n : ℕ) : ℕ :=
  max 2 (max ((GridMinorArithmetic.powTwoFloor n) ^ 2)
    (fixedRoundLocalThreshold rounds
      (GridMinorArithmetic.powTwoFloor n)))

theorem widthScaleFixedRound_gt_one (rounds n : ℕ) :
    1 < widthScaleFixedRound rounds n :=
  lt_of_lt_of_le (by decide : 1 < 2) (le_max_left 2 _)

theorem widthScaleFixedRound_grid_width (rounds n : ℕ) :
    (GridMinorArithmetic.powTwoFloor n) ^ 2 ≤
      widthScaleFixedRound rounds n :=
  le_trans (le_max_left _ _) (le_max_right 2 _)

theorem widthScaleFixedRound_crossbar_width (rounds n : ℕ) :
    fixedRoundLocalThreshold rounds
        (GridMinorArithmetic.powTwoFloor n) ≤
      widthScaleFixedRound rounds n :=
  le_trans (le_max_right _ _) (le_max_right 2 _)

theorem rounded_fixedRoundLocalThreshold_le
    {rounds n : ℕ} (hn : 2 ≤ n) :
    fixedRoundLocalThreshold rounds
        (GridMinorArithmetic.powTwoFloor n) ≤
      fixedRoundLocalThreshold rounds n := by
  have hfloor := GridMinorArithmetic.powTwoFloor_le_self hn
  simp only [fixedRoundLocalThreshold]
  gcongr
  · exact fixedRoundFanout_mono hfloor
  · unfold fixedRoundLogFactor
    exact Nat.add_le_add_right (Nat.log_mono_right hfloor) 1

theorem two_le_fixedRoundLocalThreshold
    {rounds n : ℕ} (hn : 2 ≤ n) :
    2 ≤ fixedRoundLocalThreshold rounds n := by
  have hf : 1 ≤ fixedRoundFanout rounds n :=
    fixedRoundFanout_pos (rounds := rounds) hn
  have hlog : 1 ≤ fixedRoundLogFactor n := by simp [fixedRoundLogFactor]
  have hC : 2 ≤ fixedRoundLocalConstant rounds := by
    unfold fixedRoundLocalConstant
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (4 * rounds + 20) :=
        Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
  calc
    2 ≤ fixedRoundLocalConstant rounds := hC
    _ = fixedRoundLocalConstant rounds * 1 * 1 * 1 := by ring
    _ ≤ fixedRoundLocalThreshold rounds n := by
      simp only [fixedRoundLocalThreshold]
      gcongr
      exact Nat.one_le_pow 8 n (by omega)

theorem square_le_fixedRoundLocalThreshold
    {rounds n : ℕ} (hn : 2 ≤ n) :
    n ^ 2 ≤ fixedRoundLocalThreshold rounds n := by
  have hnpos : 0 < n := by omega
  have hp : n ^ 2 ≤ n ^ 8 :=
    Nat.pow_le_pow_right hnpos (by omega)
  have hf : 1 ≤ fixedRoundFanout rounds n :=
    fixedRoundFanout_pos (rounds := rounds) hn
  have hlog : 1 ≤ fixedRoundLogFactor n := by simp [fixedRoundLogFactor]
  have hC : 1 ≤ fixedRoundLocalConstant rounds := by
    unfold fixedRoundLocalConstant
    exact Nat.one_le_pow (4 * rounds + 20) 2 (by decide)
  calc
    n ^ 2 ≤ n ^ 8 := hp
    _ = 1 * n ^ 8 * 1 * 1 := by ring
    _ ≤ fixedRoundLocalThreshold rounds n := by
      simp only [fixedRoundLocalThreshold]
      gcongr

theorem widthScaleFixedRound_le_unrounded
    {rounds n : ℕ} (hn : 2 ≤ n) :
    widthScaleFixedRound rounds n ≤
      fixedRoundLocalThreshold rounds n := by
  rw [widthScaleFixedRound]
  apply max_le
  · exact two_le_fixedRoundLocalThreshold hn
  · apply max_le
    · exact (GridMinorArithmetic.pow_powTwoFloor_le_pow
        (m := 2) hn).trans (square_le_fixedRoundLocalThreshold hn)
    · exact rounded_fixedRoundLocalThreshold_le hn

noncomputable def fixedRoundHairyConstant
    (rounds cHair cGrid : ℕ) : ℕ :=
  cHair * fixedRoundLocalConstant rounds * (max 2 cGrid) ^ 50

set_option maxHeartbeats 800000 in
theorem hairy_size_fixedRound_le_normalized
    (rounds cHair cHairLog cGrid k n : ℕ) (hn : 2 ≤ n) :
    cHair * widthScaleFixedRound rounds n *
        (PolynomialGridMinor.lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      fixedRoundHairyConstant rounds cHair cGrid *
        n ^ 8 * fixedRoundFanout rounds n *
        (Nat.log 2 n + 1) ^ 51 *
        (Nat.log 2 k) ^ cHairLog := by
  have hw : widthScaleFixedRound rounds n ≤
      fixedRoundLocalConstant rounds * n ^ 8 *
        fixedRoundFanout rounds n * (Nat.log 2 n + 1) := by
    simpa [fixedRoundLocalThreshold, fixedRoundLogFactor] using
      widthScaleFixedRound_le_unrounded (rounds := rounds) hn
  have hell : PolynomialGridMinor.lengthScale cGrid n ≤
      max 2 cGrid * (Nat.log 2 n + 1) := by
    calc
      PolynomialGridMinor.lengthScale cGrid n ≤
          PolynomialGridMinor.coarseLengthScale cGrid n :=
        PolynomialGridMinor.lengthScale_le_unrounded cGrid n hn
      _ ≤ max 2 cGrid * Nat.log 2 n :=
        PolynomialGridMinor.coarseLengthScale_le_logarithmic cGrid hn
      _ ≤ max 2 cGrid * (Nat.log 2 n + 1) := by
        gcongr
        exact Nat.le_add_right _ _
  calc
    cHair * widthScaleFixedRound rounds n *
        (PolynomialGridMinor.lengthScale cGrid n) ^ 50 *
        (Nat.log 2 k) ^ cHairLog ≤
      cHair * (fixedRoundLocalConstant rounds * n ^ 8 *
          fixedRoundFanout rounds n * (Nat.log 2 n + 1)) *
        (max 2 cGrid * (Nat.log 2 n + 1)) ^ 50 *
        (Nat.log 2 k) ^ cHairLog := by gcongr
    _ = fixedRoundHairyConstant rounds cHair cGrid *
        n ^ 8 * fixedRoundFanout rounds n *
        (Nat.log 2 n + 1) ^ 51 *
        (Nat.log 2 k) ^ cHairLog := by
      rw [mul_pow]
      simp only [fixedRoundHairyConstant]
      rw [show (51 : ℕ) = 1 + 50 by decide, pow_add, pow_one]
      ring

theorem log_logProductScale_add_one_le_fixedRound
    (C p : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (PolynomialGridMinor.logProductScale C p target) + 1 ≤
      (Nat.clog 2 C + p + 2 + 1) * Nat.log 2 target := by
  let L := Nat.log 2 target
  have hL : 1 ≤ L := Nat.succ_le_of_lt (by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget)
  calc
    Nat.log 2 (PolynomialGridMinor.logProductScale C p target) + 1 ≤
        (Nat.clog 2 C + p + 2) * L + 1 :=
      Nat.add_le_add_right (by
        simpa [L] using
          PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
            C p htarget) 1
    _ ≤ (Nat.clog 2 C + p + 2) * L + L := by gcongr
    _ = (Nat.clog 2 C + p + 2 + 1) * Nat.log 2 target := by
      simp [L]
      ring

theorem polynomialGridMinorTreewidthBoundFixedRound_le_monomial
    {rounds K b target : ℕ} (htarget : 2 ≤ target) :
    polynomialGridMinorTreewidthBoundFixedRound rounds K b target ≤
      PolynomialGridMinor.monomialLogScale K 10 b target := by
  have hf := fixedRoundFanout_le_sq rounds target
  simp only [polynomialGridMinorTreewidthBoundFixedRound,
    PolynomialGridMinor.monomialLogScale]
  calc
    K * target ^ 8 * fixedRoundFanout rounds target *
        (Nat.log 2 target) ^ b ≤
      K * target ^ 8 * target ^ 2 *
        (Nat.log 2 target) ^ b := by gcongr
    _ = K * target ^ 10 * (Nat.log 2 target) ^ b := by
      rw [show (10 : ℕ) = 8 + 2 by decide, pow_add]
      ring

theorem log_polynomialGridMinorTreewidthBoundFixedRound_le
    (rounds K b : ℕ) {target : ℕ} (htarget : 2 ≤ target) :
    Nat.log 2 (polynomialGridMinorTreewidthBoundFixedRound
      rounds K b target) ≤
      (Nat.clog 2 K + 2 * 10 + b) * Nat.log 2 target :=
  (Nat.log_mono_right
    (polynomialGridMinorTreewidthBoundFixedRound_le_monomial htarget)).trans
      (PolynomialGridMinor.log_monomialLogScale_le_clog_const_mul_log
        K 10 b htarget)

theorem polynomialGridMinorTreewidthBoundFixedRound_gt_one
    {rounds K b target : ℕ} (hK : 1 ≤ K) (htarget : 2 ≤ target) :
    1 < polynomialGridMinorTreewidthBoundFixedRound rounds K b target := by
  have hlog : 0 < Nat.log 2 target :=
    Nat.log_pos (by decide : 1 < 2) htarget
  have htwo : 2 ≤ target ^ 8 := by
    calc
      2 ≤ 2 ^ 8 := by decide
      _ ≤ target ^ 8 := Nat.pow_le_pow_left htarget 8
  have hf : 1 ≤ fixedRoundFanout rounds target :=
    fixedRoundFanout_pos (rounds := rounds) htarget
  have hl : 1 ≤ (Nat.log 2 target) ^ b :=
    Nat.succ_le_of_lt (Nat.pow_pos hlog)
  have : 2 ≤ K * target ^ 8 * fixedRoundFanout rounds target *
      (Nat.log 2 target) ^ b := by
    calc
      2 = 1 * 2 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  exact lt_of_lt_of_le (by decide : 1 < 2) (by
    simpa [polynomialGridMinorTreewidthBoundFixedRound] using this)

theorem hairy_large_threshold_fixedRound_of_coeff
    {rounds cHair cHairLog cGrid C p Dn Dk K b target : ℕ}
    (htarget : 2 ≤ target)
    (hexponent : p * 9 + 51 + cHairLog ≤ b)
    (hcoeff : fixedRoundHairyConstant rounds cHair cGrid * C ^ 9 *
      Dn ^ 51 * Dk ^ cHairLog < K) :
    fixedRoundHairyConstant rounds cHair cGrid *
        (PolynomialGridMinor.logProductScale C p target) ^ 8 *
        (C * fixedRoundFanout rounds target *
          (Nat.log 2 target) ^ p) *
        (Dn * Nat.log 2 target) ^ 51 *
        (Dk * Nat.log 2 target) ^ cHairLog <
      polynomialGridMinorTreewidthBoundFixedRound
        rounds K b target := by
  let L := Nat.log 2 target
  let f := fixedRoundFanout rounds target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have htpos : 0 < target := by omega
  have hmult : 0 < target ^ 8 * f * L ^ b := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos htpos)
      (fixedRoundFanout_pos (rounds := rounds) htarget))
      (Nat.pow_pos hLpos)
  have hleft :
      fixedRoundHairyConstant rounds cHair cGrid *
          (PolynomialGridMinor.logProductScale C p target) ^ 8 *
          (C * f * L ^ p) * (Dn * L) ^ 51 *
          (Dk * L) ^ cHairLog =
        (fixedRoundHairyConstant rounds cHair cGrid * C ^ 9 *
          Dn ^ 51 * Dk ^ cHairLog) * target ^ 8 * f *
          L ^ (p * 9 + 51 + cHairLog) := by
    rw [PolynomialGridMinor.logProductScale]
    repeat rw [mul_pow]
    rw [show (L ^ p) ^ 8 = L ^ (p * 8) by
      simpa using (Nat.pow_mul L p 8).symm]
    rw [show p * 9 + 51 + cHairLog =
      (p * 8 + p) + 51 + cHairLog by omega]
    rw [pow_add, pow_add, pow_add]
    ring
  have hpow : L ^ (p * 9 + 51 + cHairLog) ≤ L ^ b :=
    Nat.pow_le_pow_right hLpos hexponent
  calc
    fixedRoundHairyConstant rounds cHair cGrid *
        (PolynomialGridMinor.logProductScale C p target) ^ 8 *
        (C * fixedRoundFanout rounds target *
          (Nat.log 2 target) ^ p) *
        (Dn * Nat.log 2 target) ^ 51 *
        (Dk * Nat.log 2 target) ^ cHairLog =
      (fixedRoundHairyConstant rounds cHair cGrid * C ^ 9 *
        Dn ^ 51 * Dk ^ cHairLog) * target ^ 8 * f *
        L ^ (p * 9 + 51 + cHairLog) := by simpa [L, f] using hleft
    _ ≤ (fixedRoundHairyConstant rounds cHair cGrid * C ^ 9 *
        Dn ^ 51 * Dk ^ cHairLog) * target ^ 8 * f * L ^ b := by
      gcongr
    _ < K * target ^ 8 * f * L ^ b := by
      calc
        _ = (fixedRoundHairyConstant rounds cHair cGrid * C ^ 9 *
            Dn ^ 51 * Dk ^ cHairLog) *
              (target ^ 8 * f * L ^ b) := by ring
        _ < K * (target ^ 8 * f * L ^ b) :=
          Nat.mul_lt_mul_of_pos_right hcoeff hmult
        _ = K * target ^ 8 * f * L ^ b := by ring
    _ = polynomialGridMinorTreewidthBoundFixedRound
        rounds K b target := by
      simp [polynomialGridMinorTreewidthBoundFixedRound, L, f]

structure ParameterChoiceFixedRound
    (rounds cHair cHairLog cGrid cStrong target tw : ℕ) where
  ell : ℕ
  w : ℕ
  k : ℕ
  g : ℕ
  r : ℕ
  ell_gt_one : 1 < ell
  w_gt_one : 1 < w
  k_gt_one : 1 < k
  k_le_treewidth : k ≤ tw
  hairy_large :
    cHair * w * ell ^ 50 * (Nat.log 2 k) ^ cHairLog < k
  rounds_pos : 0 < rounds
  g_ge_two : 2 ≤ g
  r_ge_two : 2 ≤ r
  g_powerOfTwo : CrossbarContract.IsPowerOfTwo g
  grid_length : cGrid * Nat.log 2 g ≤ ell
  grid_width : g ^ 2 ≤ w
  crossbar_width : fixedRoundLocalThreshold rounds g ≤ w
  strong_scale : 20000 * r ^ 2 ≤ g ^ 2
  target_direct : cGrid * target * (Nat.log 2 g) ^ 2 ≤ g
  target_strong : cStrong * target ≤ r

structure PolynomialThresholdTemplateFixedRound
    (rounds cHair cHairLog cGrid cStrong : ℕ) where
  K : ℕ
  b : ℕ
  C : ℕ
  p : ℕ
  rounds_pos : 0 < rounds
  K_pos : 0 < K
  b_pos : 0 < b
  C_pos : 1 ≤ C
  p_ge_two : 2 ≤ p
  strong_coeff : 4 * 20000 * (max 2 cStrong) ^ 2 ≤ C ^ 2
  direct_coeff :
    2 * cGrid * (Nat.clog 2 C + p + 2) ^ 2 ≤ C
  hairy_exponent : p * 9 + 51 + cHairLog ≤ b
  hairy_coeff :
    fixedRoundHairyConstant rounds cHair cGrid * C ^ 9 *
      (Nat.clog 2 C + p + 2 + 1) ^ 51 *
      (Nat.clog 2 K + 2 * 10 + b) ^ cHairLog < K

namespace PolynomialThresholdTemplateFixedRound

noncomputable def toParameterChoice
    {rounds cHair cHairLog cGrid cStrong : ℕ}
    (T : PolynomialThresholdTemplateFixedRound
      rounds cHair cHairLog cGrid cStrong)
    (target : ℕ) (htarget : 2 ≤ target) :
    ParameterChoiceFixedRound rounds cHair cHairLog cGrid cStrong target
      (polynomialGridMinorTreewidthBoundFixedRound
        rounds T.K T.b target) := by
  let n := PolynomialGridMinor.logProductScale T.C T.p target
  let k := polynomialGridMinorTreewidthBoundFixedRound
    rounds T.K T.b target
  let Dn := Nat.clog 2 T.C + T.p + 2
  let Dk := Nat.clog 2 T.K + 2 * 10 + T.b
  refine
    { ell := PolynomialGridMinor.lengthScale cGrid n
      w := widthScaleFixedRound rounds n
      k := k
      g := GridMinorArithmetic.powTwoFloor n
      r := PolynomialGridMinor.strongScale cStrong target
      ell_gt_one := PolynomialGridMinor.lengthScale_gt_one cGrid n
      w_gt_one := widthScaleFixedRound_gt_one rounds n
      k_gt_one := polynomialGridMinorTreewidthBoundFixedRound_gt_one
        (Nat.succ_le_of_lt T.K_pos) htarget
      k_le_treewidth := le_rfl
      hairy_large := ?_
      rounds_pos := T.rounds_pos
      g_ge_two := GridMinorArithmetic.two_le_powTwoFloor
        (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
      r_ge_two := PolynomialGridMinor.strongScale_ge_two cStrong target
      g_powerOfTwo := GridMinorArithmetic.isPowerOfTwo_powTwoFloor n
      grid_length := PolynomialGridMinor.lengthScale_grid_length cGrid n
      grid_width := widthScaleFixedRound_grid_width rounds n
      crossbar_width := widthScaleFixedRound_crossbar_width rounds n
      strong_scale := ?_
      target_direct := ?_
      target_strong :=
        PolynomialGridMinor.target_le_strongScale cStrong target }
  · have hn : 2 ≤ n :=
      PolynomialGridMinor.two_le_logProductScale T.C_pos htarget
    apply lt_of_le_of_lt
      (hairy_size_fixedRound_le_normalized
        rounds cHair cHairLog cGrid k n hn)
    have hfanout : fixedRoundFanout rounds n ≤
        T.C * fixedRoundFanout rounds target *
          (Nat.log 2 target) ^ T.p := by
      simpa [n] using fixedRoundFanout_logProductScale_le
        (rounds := rounds) T.rounds_pos T.C_pos htarget
    have hlogn : Nat.log 2 n + 1 ≤
        (Dn + 1) * Nat.log 2 target := by
      simpa [n, Dn, Nat.add_assoc] using
        log_logProductScale_add_one_le_fixedRound T.C T.p htarget
    have hlogk : Nat.log 2 k ≤ Dk * Nat.log 2 target := by
      simpa [k, Dk] using
        log_polynomialGridMinorTreewidthBoundFixedRound_le
          rounds T.K T.b htarget
    have hthreshold :
        fixedRoundHairyConstant rounds cHair cGrid * n ^ 8 *
            (T.C * fixedRoundFanout rounds target *
              (Nat.log 2 target) ^ T.p) *
            ((Dn + 1) * Nat.log 2 target) ^ 51 *
            (Dk * Nat.log 2 target) ^ cHairLog < k := by
      simpa [n, k, Dn, Dk, Nat.add_assoc] using
        hairy_large_threshold_fixedRound_of_coeff htarget
          T.hairy_exponent T.hairy_coeff
    exact lt_of_le_of_lt (by gcongr) hthreshold
  · apply GridMinorArithmetic.le_powTwoFloor_sq_of_four_mul_le_sq
    simpa [n] using
      PolynomialGridMinor.strong_scale_logProduct_sq_of_coeff
        htarget T.strong_coeff
  · have hlog_n : Nat.log 2 n ≤ Dn * Nat.log 2 target := by
      simpa [n, Dn] using
        PolynomialGridMinor.log_logProductScale_le_clog_const_mul_log
          T.C T.p htarget
    apply GridMinorArithmetic.direct_bound_powTwoFloor_of_two_mul_le
      (PolynomialGridMinor.two_le_logProductScale T.C_pos htarget)
    calc
      2 * (cGrid * target * (Nat.log 2 n) ^ 2) ≤
          2 * (cGrid * target *
            (Dn * Nat.log 2 target) ^ 2) := by gcongr
      _ ≤ n := by
        simpa [n, Dn] using
          PolynomialGridMinor.target_direct_logProduct_of_coeff
            htarget T.p_ge_two T.direct_coeff

noncomputable def canonical
    (rounds cHair cHairLog cGrid cStrong : ℕ)
    (hrounds : 0 < rounds) :
    PolynomialThresholdTemplateFixedRound
      rounds cHair cHairLog cGrid cStrong := by
  let C := PolynomialGridMinor.crossbarCoefficient 20000 cGrid cStrong
  let b := 2 * 10 + 51 + cHairLog
  let A := fixedRoundHairyConstant rounds cHair cGrid * C ^ 9 *
    (Nat.clog 2 C + 2 + 2 + 1) ^ 51
  let E := 2 * 10 + b
  refine
    { K := PolynomialGridMinor.thresholdCoefficient A cHairLog E
      b := b
      C := C
      p := 2
      rounds_pos := hrounds
      K_pos := by
        dsimp [PolynomialGridMinor.thresholdCoefficient]
        positivity
      b_pos := by omega
      C_pos := by
        dsimp [C, PolynomialGridMinor.crossbarCoefficient]
        exact Nat.one_le_pow _ 2 (by decide)
      p_ge_two := le_rfl
      strong_coeff := by
        simpa [C] using
          PolynomialGridMinor.strong_coeff_crossbarCoefficient
            20000 cGrid cStrong
      direct_coeff := by
        simpa [C] using
          PolynomialGridMinor.direct_coeff_crossbarCoefficient
            20000 cGrid cStrong
      hairy_exponent := by omega
      hairy_coeff := by
        simpa [A, E, Nat.add_assoc] using
          PolynomialGridMinor.coeff_mul_clog_thresholdCoefficient_add_pow_lt
            A cHairLog E }

end PolynomialThresholdTemplateFixedRound

theorem containsGridMinor_of_parameterChoice_fixedRound (rounds : ℕ) :
    ∃ cHair cHairLog cGrid cStrong : ℕ,
      0 < cHair ∧ 0 < cHairLog ∧ 0 < cGrid ∧ 0 < cStrong ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) (target : ℕ),
          ParameterChoiceFixedRound rounds cHair cHairLog cGrid cStrong
            target (treewidth G) → ContainsGridMinor G target := by
  rcases containsGridMinor_of_treewidth_parameters_fixedRound rounds with
    ⟨cHair, cHairLog, cGrid, cStrong,
      hcHair, hcHairLog, hcGrid, hcStrong, hmain⟩
  refine ⟨cHair, cHairLog, cGrid, cStrong,
    hcHair, hcHairLog, hcGrid, hcStrong, ?_⟩
  intro V _ _ G target P
  exact hmain G P.ell_gt_one P.w_gt_one P.k_gt_one P.k_le_treewidth
    P.hairy_large P.rounds_pos P.g_ge_two P.r_ge_two P.g_powerOfTwo
    P.grid_length P.grid_width P.crossbar_width P.strong_scale
    P.target_direct P.target_strong

/-- Exact natural-number fixed-round excluded-grid theorem. -/
theorem polynomial_grid_minor_theorem_fixed_rounds
    (rounds : ℕ) (hrounds : 1 ≤ rounds) :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
          K * target ^ 8 * fixedRoundFanout rounds target *
              (Nat.log 2 target) ^ b ≤ treewidth G →
          ContainsGridMinor G target := by
  rcases containsGridMinor_of_parameterChoice_fixedRound rounds with
    ⟨cHair, cHairLog, cGrid, cStrong,
      hcHair, hcHairLog, hcGrid, hcStrong, hmain⟩
  let T := PolynomialThresholdTemplateFixedRound.canonical
    rounds cHair cHairLog cGrid cStrong hrounds
  refine ⟨T.K, T.b, T.K_pos, T.b_pos, ?_⟩
  intro V _ _ G target htarget htw
  let P := T.toParameterChoice target htarget
  apply hmain G target
  exact { P with
    k_le_treewidth := by
      exact P.k_le_treewidth.trans (by
        simpa [polynomialGridMinorTreewidthBoundFixedRound] using htw) }

/-- Equivalent version displaying the named exact threshold. -/
theorem polynomial_grid_minor_theorem_fixed_rounds_named
    (rounds : ℕ) (hrounds : 1 ≤ rounds) :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
          polynomialGridMinorTreewidthBoundFixedRound
              rounds K b target ≤ treewidth G →
          ContainsGridMinor G target := by
  rcases polynomial_grid_minor_theorem_fixed_rounds rounds hrounds with
    ⟨K, b, hK, hb, hmain⟩
  exact ⟨K, b, hK, hb, by
    intro V _ _ G target ht htw
    exact hmain G ht (by
      simpa [polynomialGridMinorTreewidthBoundFixedRound] using htw)⟩

/-- Paper-facing fixed-`t` form.  Here `fixedRoundRho t g` is the minimum
natural `f` satisfying `g^2 ≤ f^t`. -/
theorem polynomial_grid_minor_theorem_fixed_t
    (t : ℕ) (ht : 2 ≤ t) :
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
          K * target ^ 8 * fixedRoundRho t target *
              (Nat.log 2 target) ^ b ≤ treewidth G →
          ContainsGridMinor G target := by
  rcases polynomial_grid_minor_theorem_fixed_rounds (t - 1) (by omega) with
    ⟨K, b, hK, hb, hmain⟩
  refine ⟨K, b, hK, hb, ?_⟩
  intro V _ _ G target htarget htw
  exact hmain G htarget (by
    simpa [fixedRoundRho] using htw)

end Exponent8Epsilon
end SimpleGraph

end Lax17Proofs
