import Lax17Proofs.Source.Exponent8Epsilon.FixedRoundNumericalEndpoint
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Lax17Proofs

/-!
# The real exponent-`8 + epsilon` corollary

This module converts the exact natural-number fixed-round theorem into its
usual analytic formulation.  No graph-theoretic statement is used here: the
only ingredients are the rounding bound for `fixedRoundFanout` and the
elementary fact that a fixed power of a logarithm is eventually dominated by
every positive real power.
-/

namespace SimpleGraph
namespace Exponent8Epsilon

universe u

/-- The exact fixed-round endpoint, abstracted as an input to the purely
analytic conversion from `8 + 2/t` (up to logarithms) to `8 + epsilon`.

Keeping this input explicit lets the public submission expose the fixed-round
theorem as a genuine intermediate node in its proof graph. -/
def FixedRoundGridMinorInput : Prop :=
  ∀ rounds : ℕ, 1 ≤ rounds →
    ∃ K b : ℕ, 0 < K ∧ 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
          K * target ^ 8 * fixedRoundFanout rounds target *
              (Nat.log 2 target) ^ b ≤ treewidth G →
          ContainsGridMinor G target

/-- The least integral fanout is at most twice the corresponding real root. -/
theorem fixedRoundFanout_cast_le
    {rounds g : ℕ} (hg : 2 ≤ g) :
    (fixedRoundFanout rounds g : ℝ) ≤
      2 * (g : ℝ) ^ ((2 : ℝ) / (rounds + 1 : ℕ)) := by
  let f := fixedRoundFanout rounds g
  let t := rounds + 1
  let a : ℝ := (2 : ℝ) / (t : ℝ)
  let rhs : ℝ := 2 * (g : ℝ) ^ a
  have ht : t ≠ 0 := by simp [t]
  have hg0 : 0 ≤ (g : ℝ) := by positivity
  have hrhs0 : 0 ≤ rhs := by
    dsimp [rhs]
    positivity
  have hnat := fixedRoundFanout_pow_le (rounds := rounds) hg
  have hcast : (f : ℝ) ^ t ≤ (2 : ℝ) ^ t * (g : ℝ) ^ 2 := by
    exact_mod_cast hnat
  have ha_mul : a * (t : ℝ) = 2 := by
    dsimp [a]
    field_simp
  have hrootPow : ((g : ℝ) ^ a) ^ t = (g : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg0, ha_mul]
    exact Real.rpow_natCast (g : ℝ) 2
  have hrhsPow : rhs ^ t = (2 : ℝ) ^ t * (g : ℝ) ^ 2 := by
    dsimp [rhs]
    rw [mul_pow, hrootPow]
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (f : ℝ)) hrhs0 ht).mp
  simpa [hrhsPow] using hcast

/-- The paper-facing form `rho_t(g) ≤ 2 g^(2/t)`. -/
theorem fixedRoundRho_cast_le
    {t g : ℕ} (ht : 2 ≤ t) (hg : 2 ≤ g) :
    (fixedRoundRho t g : ℝ) ≤
      2 * (g : ℝ) ^ ((2 : ℝ) / (t : ℝ)) := by
  have heq : t - 1 + 1 = t := by omega
  simpa [fixedRoundRho, heq] using
    (fixedRoundFanout_cast_le (rounds := t - 1) hg)

/-- A fixed power of the binary natural logarithm is bounded by an arbitrary
positive real power, uniformly for natural arguments at least two.  The proof
uses the explicit inequality `log x ≤ x^δ/δ`. -/
theorem exists_natLog_pow_le_const_mul_rpow
    (b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 2 ≤ n →
      ((Nat.log 2 n : ℕ) : ℝ) ^ b ≤ A * (n : ℝ) ^ ε := by
  let δ : ℝ := ε / (b + 1 : ℕ)
  let c : ℝ := δ * Real.log 2
  let A : ℝ := c⁻¹ ^ b
  have hbden : 0 < ((b + 1 : ℕ) : ℝ) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro n hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : ((Nat.log 2 n : ℕ) : ℝ) ≤
      c⁻¹ * (n : ℝ) ^ δ := by
    calc
      ((Nat.log 2 n : ℕ) : ℝ) ≤
          Real.logb (2 : ℝ) (n : ℝ) :=
        Real.natLog_le_logb n 2
      _ = Real.log (n : ℝ) / Real.log 2 := by
        rfl
      _ ≤ ((n : ℝ) ^ δ / δ) / Real.log 2 :=
        div_le_div_of_nonneg_right
          (Real.log_natCast_le_rpow_div n hδ) (le_of_lt hlog2)
      _ = c⁻¹ * (n : ℝ) ^ δ := by
        rw [div_div, ← inv_mul_eq_div]
  have hpow := pow_le_pow_left₀
    (by positivity : 0 ≤ ((Nat.log 2 n : ℕ) : ℝ)) hlog b
  have hrootPow : ((n : ℝ) ^ δ) ^ b =
      (n : ℝ) ^ (δ * (b : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
  have hexp : δ * (b : ℝ) ≤ ε := by
    calc
      δ * (b : ℝ) ≤ δ * ((b + 1 : ℕ) : ℝ) := by
        gcongr
        exact_mod_cast (Nat.le_add_right b 1)
      _ = ε := by
        dsimp [δ]
        field_simp
  calc
    ((Nat.log 2 n : ℕ) : ℝ) ^ b ≤
        (c⁻¹ * (n : ℝ) ^ δ) ^ b := hpow
    _ = A * (n : ℝ) ^ (δ * (b : ℝ)) := by
      rw [mul_pow, hrootPow]
    _ ≤ A * (n : ℝ) ^ ε := by
      gcongr

/-- A positive epsilon admits a positive finite number of rounds whose root
exponent is at most `epsilon / 2`. -/
theorem exists_rounds_rootExponent_le_half
    {ε : ℝ} (hε : 0 < ε) :
    ∃ rounds : ℕ, 1 ≤ rounds ∧
      (2 : ℝ) / (rounds + 1 : ℕ) ≤ ε / 2 := by
  rcases exists_nat_gt ((4 : ℝ) / ε) with ⟨rounds, hrounds⟩
  have hquot : 0 < (4 : ℝ) / ε := by positivity
  have hroundsReal : 0 < (rounds : ℝ) := hquot.trans hrounds
  have hroundsNat : 1 ≤ rounds := by
    exact_mod_cast hroundsReal
  refine ⟨rounds, hroundsNat, ?_⟩
  have ht : 0 < ((rounds + 1 : ℕ) : ℝ) := by positivity
  have hfour : (4 : ℝ) < (rounds : ℝ) * ε := by
    exact (div_lt_iff₀ hε).mp hrounds
  apply (div_le_iff₀ ht).2
  have hcast : ((rounds + 1 : ℕ) : ℝ) = (rounds : ℝ) + 1 := by
    norm_num
  rw [hcast]
  nlinarith

/-- The analytic conversion with the exact fixed-round theorem supplied as an
explicit input. -/
theorem polynomial_grid_minor_theorem_exponent_eight_add_epsilon_of_input
    (hfixedInput : FixedRoundGridMinorInput.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
          C * (target : ℝ) ^ ((8 : ℝ) + ε) ≤
            (treewidth G : ℝ) →
          ContainsGridMinor G target := by
  rcases exists_rounds_rootExponent_le_half hε with
    ⟨rounds, hrounds, hrootExp⟩
  rcases hfixedInput rounds hrounds with
    ⟨K, b, hK, hb, hfixed⟩
  have hhalf : 0 < ε / 2 := by positivity
  rcases exists_natLog_pow_le_const_mul_rpow b hhalf with
    ⟨A, hA, hlogBound⟩
  let C : ℝ := 2 * (K : ℝ) * A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro V _ _ G target htarget htw
  have ht0 : 0 ≤ (target : ℝ) := by positivity
  have ht1 : 1 ≤ (target : ℝ) := by
    exact_mod_cast (show 1 ≤ target by omega)
  have hfan : (fixedRoundFanout rounds target : ℝ) ≤
      2 * (target : ℝ) ^ (ε / 2) := by
    calc
      (fixedRoundFanout rounds target : ℝ) ≤
          2 * (target : ℝ) ^
            ((2 : ℝ) / (rounds + 1 : ℕ)) :=
        fixedRoundFanout_cast_le htarget
      _ ≤ 2 * (target : ℝ) ^ (ε / 2) := by
        gcongr
  have hlog : (((Nat.log 2 target) ^ b : ℕ) : ℝ) ≤
      A * (target : ℝ) ^ (ε / 2) := by
    rw [Nat.cast_pow]
    exact hlogBound target htarget
  have hpowers :
      (target : ℝ) ^ (8 : ℕ) *
          (target : ℝ) ^ (ε / 2) *
          (target : ℝ) ^ (ε / 2) =
        (target : ℝ) ^ ((8 : ℝ) + ε) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add (by positivity : 0 < (target : ℝ))]
    rw [← Real.rpow_add (by positivity : 0 < (target : ℝ))]
    congr 1
    ring
  have hboundCast :
      ((K * target ^ 8 * fixedRoundFanout rounds target *
          (Nat.log 2 target) ^ b : ℕ) : ℝ) ≤
        C * (target : ℝ) ^ ((8 : ℝ) + ε) := by
    simp only [Nat.cast_mul, Nat.cast_pow]
    calc
      (K : ℝ) * (target : ℝ) ^ 8 *
          (fixedRoundFanout rounds target : ℝ) *
          (Nat.log 2 target : ℝ) ^ b ≤
        (K : ℝ) * (target : ℝ) ^ 8 *
          (2 * (target : ℝ) ^ (ε / 2)) *
          (A * (target : ℝ) ^ (ε / 2)) := by
            gcongr
            simpa only [Nat.cast_pow] using hlog
      _ = C * (target : ℝ) ^ ((8 : ℝ) + ε) := by
        dsimp [C]
        rw [← hpowers]
        ring
  have hnat :
      K * target ^ 8 * fixedRoundFanout rounds target *
          (Nat.log 2 target) ^ b ≤ treewidth G := by
    exact_mod_cast hboundCast.trans htw
  exact hfixed G htarget hnat

/-- The usual closed analytic corollary: for every positive real `epsilon`,
one constant (depending only on `epsilon`) makes the exponent `8 + epsilon`
sufficient for all finite simple graphs and all grid orders at least two. -/
theorem polynomial_grid_minor_theorem_exponent_eight_add_epsilon
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : _root_.SimpleGraph V) {target : ℕ},
          2 ≤ target →
          C * (target : ℝ) ^ ((8 : ℝ) + ε) ≤
            (treewidth G : ℝ) →
          ContainsGridMinor G target :=
  polynomial_grid_minor_theorem_exponent_eight_add_epsilon_of_input
    (fun rounds hrounds =>
      polynomial_grid_minor_theorem_fixed_rounds rounds hrounds)
    ε hε

end Exponent8Epsilon
end SimpleGraph

end Lax17Proofs
