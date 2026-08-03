import Lax17Proofs.Source.PolynomialGridMinor

namespace Lax17Proofs

/-!
# A rounding-safe integral power root

For `rounds + 1 = t`, `fixedRoundFanout rounds g` is the least natural
number `f` with `g^2 <= f^t`.  This is the exact integral fanout used by the
fixed-round recursive slicing theorem.
-/

namespace SimpleGraph
namespace Exponent8Epsilon

/-- The candidate set defining `fixedRoundFanout` is nonempty. -/
private theorem exists_fixedRoundFanout (rounds g : ℕ) :
    ∃ f : ℕ, g ^ 2 ≤ f ^ (rounds + 1) := by
  refine ⟨g ^ 2, ?_⟩
  exact Nat.le_self_pow (a := g ^ 2) (by omega)

/-- Least integral `(rounds+1)`-st root dominating `g^2`. -/
noncomputable def fixedRoundFanout (rounds g : ℕ) : ℕ :=
  Nat.find (exists_fixedRoundFanout rounds g)

/-- Paper-facing notation: `fixedRoundRho t g` is the least natural `f`
whose `t`-th power dominates `g^2`.  The fixed-round controller uses
`rounds = t - 1`. -/
noncomputable def fixedRoundRho (t g : ℕ) : ℕ :=
  fixedRoundFanout (t - 1) g

/-- The selected fanout satisfies its defining inequality. -/
theorem fixedRoundFanout_spec (rounds g : ℕ) :
    g ^ 2 ≤ (fixedRoundFanout rounds g) ^ (rounds + 1) := by
  exact Nat.find_spec (exists_fixedRoundFanout rounds g)

theorem fixedRoundRho_spec
    {t g : ℕ} (ht : 1 ≤ t) :
    g ^ 2 ≤ (fixedRoundRho t g) ^ t := by
  have heq : t - 1 + 1 = t := by omega
  simpa [fixedRoundRho, heq] using
    fixedRoundFanout_spec (t - 1) g

/-- The fanout is positive in the nondegenerate grid range. -/
theorem fixedRoundFanout_pos
    {rounds g : ℕ} (hg : 2 ≤ g) :
    0 < fixedRoundFanout rounds g := by
  have hspec := fixedRoundFanout_spec rounds g
  by_contra h
  have hf : fixedRoundFanout rounds g = 0 := Nat.eq_zero_of_not_pos h
  simp [hf] at hspec
  have : 0 < g ^ 2 := by positivity
  omega

/-- Minimality: the predecessor fanout is too small. -/
theorem fixedRoundFanout_pred_pow_lt
    {rounds g : ℕ} (hg : 2 ≤ g) :
    (fixedRoundFanout rounds g - 1) ^ (rounds + 1) < g ^ 2 := by
  let f := fixedRoundFanout rounds g
  have hfpos : 0 < f := by
    simpa [f] using fixedRoundFanout_pos (rounds := rounds) hg
  have hpred : f - 1 < f := by omega
  have hnot :
      ¬ g ^ 2 ≤ (f - 1) ^ (rounds + 1) := by
    simpa [fixedRoundFanout, f] using
      Nat.find_min (exists_fixedRoundFanout rounds g) hpred
  simpa [f] using Nat.lt_of_not_ge hnot

/-- The rounding loss is at most a factor `2^(rounds+1)` after taking the
power. -/
theorem fixedRoundFanout_pow_le
    {rounds g : ℕ} (hg : 2 ≤ g) :
    (fixedRoundFanout rounds g) ^ (rounds + 1) ≤
      2 ^ (rounds + 1) * g ^ 2 := by
  let f := fixedRoundFanout rounds g
  have hfpos : 0 < f := by
    simpa [f] using fixedRoundFanout_pos (rounds := rounds) hg
  change f ^ (rounds + 1) ≤ 2 ^ (rounds + 1) * g ^ 2
  by_cases hf : f = 1
  · rw [hf, one_pow]
    have hpos : 0 < 2 ^ (rounds + 1) * g ^ 2 := by positivity
    omega
  · have hf2 : 2 ≤ f := by omega
    have hbase : f ≤ 2 * (f - 1) := by omega
    have hpred : (f - 1) ^ (rounds + 1) ≤ g ^ 2 := by
      have hlt := fixedRoundFanout_pred_pow_lt
        (rounds := rounds) (g := g) hg
      simpa [f] using Nat.le_of_lt hlt
    calc
      f ^ (rounds + 1) ≤ (2 * (f - 1)) ^ (rounds + 1) :=
        Nat.pow_le_pow_left hbase _
      _ = 2 ^ (rounds + 1) * (f - 1) ^ (rounds + 1) := by
        rw [Nat.mul_pow]
      _ ≤ 2 ^ (rounds + 1) * g ^ 2 :=
        Nat.mul_le_mul_left _ hpred

theorem fixedRoundRho_pow_le
    {t g : ℕ} (ht : 2 ≤ t) (hg : 2 ≤ g) :
    (fixedRoundRho t g) ^ t ≤ 2 ^ t * g ^ 2 := by
  have heq : t - 1 + 1 = t := by omega
  simpa [fixedRoundRho, heq] using
    fixedRoundFanout_pow_le (rounds := t - 1) hg

/-- The least integral power root is monotone in the target. -/
theorem fixedRoundFanout_mono
    {rounds a b : ℕ} (hab : a ≤ b) :
    fixedRoundFanout rounds a ≤ fixedRoundFanout rounds b := by
  apply Nat.find_min'
    (H := exists_fixedRoundFanout rounds a)
  calc
    a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
    _ ≤ (fixedRoundFanout rounds b) ^ (rounds + 1) :=
      fixedRoundFanout_spec rounds b

/-- The trivial candidate gives a useful exponent-ten bound for logarithmic
bookkeeping. -/
theorem fixedRoundFanout_le_sq (rounds g : ℕ) :
    fixedRoundFanout rounds g ≤ g ^ 2 := by
  apply Nat.find_min'
    (H := exists_fixedRoundFanout rounds g)
  exact Nat.le_self_pow (a := g ^ 2) (by omega)

/-- A polynomial-logarithmic rescaling costs only the same rescaling of the
integral power root. -/
theorem fixedRoundFanout_logProductScale_le
    {rounds C p target : ℕ}
    (hrounds : 1 ≤ rounds)
    (hC : 1 ≤ C)
    (htarget : 2 ≤ target) :
    fixedRoundFanout rounds
        (PolynomialGridMinor.logProductScale C p target) ≤
      C * fixedRoundFanout rounds target *
        (Nat.log 2 target) ^ p := by
  let L := Nat.log 2 target
  let LP := L ^ p
  let f := fixedRoundFanout rounds target
  have hLpos : 0 < L := by
    simpa [L] using Nat.log_pos (by decide : 1 < 2) htarget
  have hLP : 1 ≤ LP := Nat.succ_le_of_lt (Nat.pow_pos hLpos)
  have hexp : 2 ≤ rounds + 1 := by omega
  have hCpow : C ^ 2 ≤ C ^ (rounds + 1) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hLPpow : LP ^ 2 ≤ LP ^ (rounds + 1) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hfpow : target ^ 2 ≤ f ^ (rounds + 1) := by
    simpa [f] using fixedRoundFanout_spec rounds target
  apply Nat.find_min'
    (H := exists_fixedRoundFanout rounds
      (PolynomialGridMinor.logProductScale C p target))
  calc
    (PolynomialGridMinor.logProductScale C p target) ^ 2 =
        C ^ 2 * target ^ 2 * LP ^ 2 := by
      simp [PolynomialGridMinor.logProductScale, L, LP]
      ring
    _ ≤ C ^ (rounds + 1) * f ^ (rounds + 1) *
        LP ^ (rounds + 1) := by
      gcongr
    _ = (C * f * LP) ^ (rounds + 1) := by
      rw [Nat.mul_pow, Nat.mul_pow]
    _ = (C * fixedRoundFanout rounds target *
        (Nat.log 2 target) ^ p) ^ (rounds + 1) := by
      rfl

end Exponent8Epsilon
end SimpleGraph

end Lax17Proofs
