import Lax17Proofs.Source.Exponent8.ThreeRoundRecursion
import Lax17Proofs.Source.Exponent8Epsilon.CeilingPowerRoot

namespace Lax17Proofs

/-!
# Explicit parameters for an arbitrary fixed number of slicing rounds

This is the division-free, finite version of the fixed-round calculation.
For `rounds + 1 = t`, the fanout is the least `f` satisfying
`g^2 <= f^(rounds+1)`.  Slice counts and row caps are indexed by their
actual recursion depth, while widths are defined backwards from `16*g^4`.

The only paper hypotheses used here are the Section 4 bounds
`N <= 64*g^6` and `Dhat = 32*g^4`.
-/

namespace SimpleGraph
namespace Exponent8Epsilon

open Exponent8

def fixedRoundLogFactor (g : ℕ) : ℕ := Nat.log 2 g + 1

noncomputable def fixedRoundM
    (rounds g : ℕ) (j : Fin (rounds + 1)) : ℕ :=
  8 * 2 ^ (rounds - j.1) * g ^ 2 *
    (fixedRoundFanout rounds g) ^ (j.1 + 1) *
    fixedRoundLogFactor g

theorem fixedRoundM_pos
    {rounds g : ℕ} (hg : 2 ≤ g)
    (j : Fin (rounds + 1)) :
    0 < fixedRoundM rounds g j := by
  have hf : 0 < fixedRoundFanout rounds g :=
    fixedRoundFanout_pos (rounds := rounds) hg
  unfold fixedRoundM fixedRoundLogFactor
  positivity

noncomputable def fixedRoundCap
    (rounds g : ℕ) (j : Fin rounds) : ℕ :=
  256 * g ^ 4 *
    (fixedRoundFanout rounds g) ^ (rounds - j.1)

def fixedRoundWidthRev (g f : ℕ) : ℕ → ℕ
  | 0 => 16 * g ^ 4
  | n + 1 =>
      2 * (f * fixedRoundWidthRev g f n +
        (f + 1) * (256 * g ^ 4 * f ^ (n + 1)) +
        4 * g ^ 4)

noncomputable def fixedRoundWidth
    (rounds g : ℕ) (j : Fin (rounds + 1)) : ℕ :=
  fixedRoundWidthRev g (fixedRoundFanout rounds g)
    (rounds - j.1)

def fixedRoundAssemblyMass (N g : ℕ) : ℕ :=
  32 * N * g ^ 2 * fixedRoundLogFactor g

def fixedRoundLocalConstant (rounds : ℕ) : ℕ :=
  2 ^ (4 * rounds + 20)

noncomputable def fixedRoundLocalThreshold (rounds g : ℕ) : ℕ :=
  fixedRoundLocalConstant rounds * g ^ 8 *
    fixedRoundFanout rounds g * fixedRoundLogFactor g

/-- Numerical contract consumed by the generic finite-round controller.  The
explicit constructor below proves every field from the formulas above. -/
structure FixedRoundParameters (rounds g N Dhat : ℕ) where
  fanout : ℕ
  m : Fin (rounds + 1) → ℕ
  width : Fin (rounds + 1) → ℕ
  cap : Fin rounds → ℕ
  assemblyMass : ℕ
  fanout_eq : fanout = fixedRoundFanout rounds g
  assemblyMass_eq : assemblyMass = fixedRoundAssemblyMass N g
  rounds_pos : 0 < rounds
  g_at_least_two : 2 ≤ g
  Dhat_pos : 0 < Dhat
  theorem411_scale : 8 * g ^ 2 ≤ Dhat
  fanout_pos : 0 < fanout
  counts_pos : ∀ j, 0 < m j
  widths_pos : ∀ j, 0 < width j
  count_step : ∀ j : Fin rounds,
    2 * m j.succ ≤ m j.castSucc * fanout
  refine_step : ∀ j : Fin rounds,
    2 * (fanout * width j.succ +
      (fanout + 1) * cap j + 4 * g ^ 4) ≤
        width j.castSucc
  large_mass : ∀ j : Fin rounds,
    2 * assemblyMass ≤ m j.castSucc * cap j
  final_slice_count :
    8 * g ^ 4 * fixedRoundLogFactor g ≤ m (Fin.last rounds)
  final_pruning :
    2 * N * (4 * g ^ 2) ≤ Dhat * width (Fin.last rounds)
  local_cost :
    8 * (m 0 * width 0 + (m 0 + 1) * N) ≤
      fixedRoundLocalThreshold rounds g

namespace FixedRoundParameters

theorem width_anti
    {rounds g N Dhat : ℕ}
    (p : FixedRoundParameters rounds g N Dhat)
    (j : Fin rounds) : p.width j.succ ≤ p.width j.castSucc := by
  have hone : 1 ≤ p.fanout := p.fanout_pos
  have hmul : p.width j.succ ≤ p.fanout * p.width j.succ := by
    simpa using Nat.mul_le_mul_right (p.width j.succ) hone
  let total := p.fanout * p.width j.succ +
    (p.fanout + 1) * p.cap j + 4 * g ^ 4
  have hsum : p.fanout * p.width j.succ ≤ total := by
    dsimp [total]
    omega
  have hdouble : total ≤ 2 * total := by omega
  exact hmul.trans (hsum.trans (hdouble.trans (p.refine_step j)))

/-- Every earlier layer inherits the final additive-pruning budget. -/
theorem pruning_at
    {rounds g N Dhat : ℕ}
    (p : FixedRoundParameters rounds g N Dhat)
    (j : Fin (rounds + 1)) :
    2 * N * (4 * g ^ 2) ≤ Dhat * p.width j := by
  have hmono : p.width (Fin.last rounds) ≤ p.width j := by
    have hantitone : Antitone p.width :=
      Fin.antitone_iff_succ_le.2 p.width_anti
    exact hantitone j.le_last
  exact p.final_pruning.trans (Nat.mul_le_mul_left Dhat hmono)

end FixedRoundParameters

/-- The backwards width recurrence is positive in the nondegenerate range. -/
theorem fixedRoundWidthRev_pos
    {g f n : ℕ} (hg : 0 < g) :
    0 < fixedRoundWidthRev g f n := by
  cases n with
  | zero =>
      simp [fixedRoundWidthRev]
      positivity
  | succ n =>
      simp only [fixedRoundWidthRev]
      positivity

theorem fixedRoundWidthRev_base_le (g f n : ℕ) (hf : 1 ≤ f) :
    16 * g ^ 4 ≤ fixedRoundWidthRev g f n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      have hmul : fixedRoundWidthRev g f n ≤
          f * fixedRoundWidthRev g f n := by
        simpa using Nat.mul_le_mul_right (fixedRoundWidthRev g f n) hf
      calc
        16 * g ^ 4 ≤ fixedRoundWidthRev g f n := ih
        _ ≤ f * fixedRoundWidthRev g f n := hmul
        _ ≤ fixedRoundWidthRev g f (n + 1) := by
          simp only [fixedRoundWidthRev]
          omega

/-- Uniform closed upper bound for the backwards width recurrence. -/
theorem fixedRoundWidthRev_le
    {g f n : ℕ} (hf : 1 ≤ f) :
    fixedRoundWidthRev g f n ≤
      1032 * 3 ^ n * g ^ 4 * f ^ (n + 1) := by
  induction n with
  | zero =>
      have hcoef : 16 ≤ 1032 * f := by omega
      calc
        fixedRoundWidthRev g f 0 = 16 * g ^ 4 := rfl
        _ ≤ (1032 * f) * g ^ 4 := Nat.mul_le_mul_right _ hcoef
        _ = 1032 * 3 ^ 0 * g ^ 4 * f ^ (0 + 1) := by ring
  | succ n ih =>
      have hpow : 1 ≤ f ^ (n + 2) := Nat.one_le_pow _ f hf
      have hfdouble : f + 1 ≤ 2 * f := by omega
      have hfirst :
          f * fixedRoundWidthRev g f n ≤
            f * (1032 * 3 ^ n * g ^ 4 * f ^ (n + 1)) :=
        Nat.mul_le_mul_left f ih
      have hsecond :
          (f + 1) * (256 * g ^ 4 * f ^ (n + 1)) ≤
            (2 * f) * (256 * g ^ 4 * f ^ (n + 1)) :=
        Nat.mul_le_mul_right _ hfdouble
      have hthird :
          4 * g ^ 4 ≤ 4 * g ^ 4 * f ^ (n + 2) := by
        simpa using Nat.mul_le_mul_left (4 * g ^ 4) hpow
      calc
        fixedRoundWidthRev g f (n + 1) =
            2 * (f * fixedRoundWidthRev g f n +
              (f + 1) * (256 * g ^ 4 * f ^ (n + 1)) +
              4 * g ^ 4) := by rfl
        _ ≤ 2 * (f *
              (1032 * 3 ^ n * g ^ 4 * f ^ (n + 1)) +
              (2 * f) * (256 * g ^ 4 * f ^ (n + 1)) +
              4 * g ^ 4 * f ^ (n + 2)) := by
          exact Nat.mul_le_mul_left 2
            (Nat.add_le_add (Nat.add_le_add hfirst hsecond) hthird)
        _ = (2064 * 3 ^ n + 1024 + 8) *
              g ^ 4 * f ^ (n + 2) := by ring
        _ ≤ (1032 * 3 ^ (n + 1)) *
              g ^ 4 * f ^ (n + 2) := by
          gcongr
          have hthree : 1 ≤ 3 ^ n := Nat.one_le_pow _ 3 (by decide)
          omega
        _ = 1032 * 3 ^ (n + 1) * g ^ 4 *
              f ^ ((n + 1) + 1) := by ring

theorem fixedRound_count_step
    {rounds g : ℕ} (j : Fin rounds) :
    2 * fixedRoundM rounds g j.succ =
      fixedRoundM rounds g j.castSucc *
        fixedRoundFanout rounds g := by
  have hj : j.1 < rounds := j.2
  have hsub : rounds - j.1 = rounds - (j.1 + 1) + 1 := by omega
  simp [fixedRoundM, hsub, Nat.pow_succ]
  ring

theorem fixedRound_refine_step
    {rounds g : ℕ} (j : Fin rounds) :
    2 * (fixedRoundFanout rounds g *
          fixedRoundWidth rounds g j.succ +
        (fixedRoundFanout rounds g + 1) *
          fixedRoundCap rounds g j + 4 * g ^ 4) =
      fixedRoundWidth rounds g j.castSucc := by
  have hj : j.1 < rounds := j.2
  have hsub : rounds - j.1 = rounds - (j.1 + 1) + 1 := by omega
  simp [fixedRoundWidth, fixedRoundCap, hsub, fixedRoundWidthRev]

/-- The explicit formulas inhabit the full fixed-round numerical contract. -/
noncomputable def explicitFixedRoundParameters
    (rounds g N Dhat : ℕ)
    (hrounds : 0 < rounds)
    (hg : 2 ≤ g)
    (hN : N ≤ 64 * g ^ 6)
    (hDhat : Dhat = 32 * g ^ 4) :
    FixedRoundParameters rounds g N Dhat := by
  let f := fixedRoundFanout rounds g
  let L := fixedRoundLogFactor g
  have hfpos : 0 < f := by
    simpa [f] using fixedRoundFanout_pos (rounds := rounds) hg
  have hf1 : 1 ≤ f := hfpos
  have hLpos : 0 < L := by simp [L, fixedRoundLogFactor]
  have hpow : g ^ 2 ≤ f ^ (rounds + 1) := by
    simpa [f] using fixedRoundFanout_spec rounds g
  refine
    { fanout := f
      m := fixedRoundM rounds g
      width := fixedRoundWidth rounds g
      cap := fixedRoundCap rounds g
      assemblyMass := fixedRoundAssemblyMass N g
      fanout_eq := rfl
      assemblyMass_eq := rfl
      rounds_pos := hrounds
      g_at_least_two := hg
      Dhat_pos := by rw [hDhat]; positivity
      theorem411_scale := by
        rw [hDhat]
        have hg1 : 1 ≤ g := by omega
        nlinarith [Nat.pow_le_pow_left hg1 2]
      fanout_pos := hfpos
      counts_pos := by
        intro j
        unfold fixedRoundM fixedRoundLogFactor
        have hfp : 0 < fixedRoundFanout rounds g ^ (j.1 + 1) :=
          Nat.pow_pos (fixedRoundFanout_pos (rounds := rounds) hg)
        positivity
      widths_pos := by
        intro j
        simpa [fixedRoundWidth] using
          (fixedRoundWidthRev_pos
            (f := fixedRoundFanout rounds g)
            (n := rounds - j.1) (by omega))
      count_step := by
        intro j
        exact (fixedRound_count_step j).le
      refine_step := by
        intro j
        exact (fixedRound_refine_step j).le
      large_mass := by
        intro j
        have hj : j.1 < rounds := j.2
        have hexp : (j.1 + 1) + (rounds - j.1) = rounds + 1 := by
          omega
        have htwo : 2 ≤ 2 ^ (rounds - j.1) := by
          calc
            2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (rounds - j.1) :=
              Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
        have hsplit :
            f ^ (j.1 + 1) * f ^ (rounds - j.1) =
              f ^ (rounds + 1) := by
          rw [← Nat.pow_add, hexp]
        calc
          2 * fixedRoundAssemblyMass N g =
              64 * N * g ^ 2 * L := by
            simp [fixedRoundAssemblyMass, L]
            ring
          _ ≤ 4096 * g ^ 8 * L := by
            calc
              64 * N * g ^ 2 * L ≤
                  64 * (64 * g ^ 6) * g ^ 2 * L := by gcongr
              _ = 4096 * g ^ 8 * L := by ring
          _ ≤ 2048 * 2 ^ (rounds - j.1) * g ^ 6 *
                f ^ (j.1 + 1) * L * f ^ (rounds - j.1) := by
            calc
              4096 * g ^ 8 * L =
                  2048 * 2 * g ^ 6 * (g ^ 2) * L := by ring
              _ ≤ 2048 * 2 ^ (rounds - j.1) *
                    g ^ 6 * f ^ (rounds + 1) * L := by gcongr
              _ = 2048 * 2 ^ (rounds - j.1) * g ^ 6 *
                    f ^ (j.1 + 1) * L * f ^ (rounds - j.1) := by
                rw [← hsplit]
                ring
          _ = fixedRoundM rounds g j.castSucc *
                fixedRoundCap rounds g j := by
            simp [fixedRoundM, fixedRoundCap, L]
            ring
      final_slice_count := by
        calc
          8 * g ^ 4 * L = (8 * g ^ 2 * L) * g ^ 2 := by ring
          _ ≤ (8 * g ^ 2 * L) * f ^ (rounds + 1) :=
            Nat.mul_le_mul_left _ hpow
          _ = fixedRoundM rounds g (Fin.last rounds) := by
            simp [fixedRoundM, L]
            ring
      final_pruning := by
        rw [hDhat]
        calc
          2 * N * (4 * g ^ 2) ≤
              2 * (64 * g ^ 6) * (4 * g ^ 2) := by gcongr
          _ = (32 * g ^ 4) *
                fixedRoundWidth rounds g (Fin.last rounds) := by
            simp [fixedRoundWidth, fixedRoundWidthRev]
            ring
      local_cost := by
        have hw : fixedRoundWidth rounds g 0 ≤
            1032 * 3 ^ rounds * g ^ 4 * f ^ (rounds + 1) := by
          simpa [fixedRoundWidth] using
            (fixedRoundWidthRev_le (g := g) (f := f)
              (n := rounds) hf1)
        have hfpow : f ^ (rounds + 1) ≤
            2 ^ (rounds + 1) * g ^ 2 := by
          simpa [f] using fixedRoundFanout_pow_le
            (rounds := rounds) hg
        have hw' : fixedRoundWidth rounds g 0 ≤
            1032 * 3 ^ rounds * 2 ^ (rounds + 1) * g ^ 6 := by
          calc
            fixedRoundWidth rounds g 0 ≤
                1032 * 3 ^ rounds * g ^ 4 * f ^ (rounds + 1) := hw
            _ ≤ 1032 * 3 ^ rounds * g ^ 4 *
                  (2 ^ (rounds + 1) * g ^ 2) := by gcongr
            _ = 1032 * 3 ^ rounds * 2 ^ (rounds + 1) * g ^ 6 := by ring
        have hm : fixedRoundM rounds g 0 =
            8 * 2 ^ rounds * g ^ 2 * f * L := by
          simp [fixedRoundM, f, L]
        have hbase : 1 ≤ g ^ 2 * f * L := by
          have : 0 < g ^ 2 * f * L := by positivity
          omega
        have hNsmall : N ≤ 64 * g ^ 8 * f * L := by
          calc
            N ≤ 64 * g ^ 6 := hN
            _ = (64 * g ^ 6) * 1 := by ring
            _ ≤ (64 * g ^ 6) * (g ^ 2 * f * L) := by gcongr
            _ = 64 * g ^ 8 * f * L := by ring
        have hcoef1 :
            8 * (1032 * 2 ^ (2 * rounds + 4) * 3 ^ rounds) ≤
              2 ^ (4 * rounds + 18) := by
          have h1032 : 1032 ≤ 2 ^ 11 := by decide
          have h3 : 3 ^ rounds ≤ 2 ^ (2 * rounds) := by
            calc
              3 ^ rounds ≤ 4 ^ rounds :=
                Nat.pow_le_pow_left (by decide) _
              _ = 2 ^ (2 * rounds) := by
                rw [show 4 = 2 ^ 2 by norm_num, ← Nat.pow_mul]
          calc
            8 * (1032 * 2 ^ (2 * rounds + 4) * 3 ^ rounds) ≤
                8 * (2 ^ 11 * 2 ^ (2 * rounds + 4) *
                  2 ^ (2 * rounds)) := by gcongr
            _ = 2 ^ (4 * rounds + 18) := by
              rw [show 8 = 2 ^ 3 by norm_num]
              rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
              congr 1
              omega
        have hcoef2 :
            8 * (2 ^ (rounds + 9) + 64) ≤
              2 ^ (4 * rounds + 18) := by
          have hr : rounds + 12 ≤ 4 * rounds + 17 := by omega
          calc
            8 * (2 ^ (rounds + 9) + 64) =
                2 ^ (rounds + 12) + 512 := by ring
            _ ≤ 2 ^ (4 * rounds + 17) + 2 ^ (4 * rounds + 17) := by
              apply Nat.add_le_add
              · exact Nat.pow_le_pow_right (n := 2) (by decide) hr
              · calc
                  512 = 2 ^ 9 := by norm_num
                  _ ≤ 2 ^ (4 * rounds + 17) :=
                    Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
            _ = 2 ^ (4 * rounds + 18) := by
              rw [Nat.pow_succ]
              ring
        have hcoefSum :
            8 * (1032 * 2 ^ (2 * rounds + 4) * 3 ^ rounds) +
                8 * (2 ^ (rounds + 9) + 64) ≤
              fixedRoundLocalConstant rounds := by
          unfold fixedRoundLocalConstant
          calc
            _ ≤ 2 ^ (4 * rounds + 18) +
                2 ^ (4 * rounds + 18) := Nat.add_le_add hcoef1 hcoef2
            _ = 2 ^ (4 * rounds + 19) := by
              rw [Nat.pow_succ]
              ring
            _ ≤ 2 ^ (4 * rounds + 20) :=
              Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
        rw [hm]
        have hmw :
            (8 * 2 ^ rounds * g ^ 2 * f * L) *
                fixedRoundWidth rounds g 0 ≤
              (1032 * 2 ^ (2 * rounds + 4) * 3 ^ rounds) *
                (g ^ 8 * f * L) := by
          calc
            (8 * 2 ^ rounds * g ^ 2 * f * L) *
                fixedRoundWidth rounds g 0 ≤
              (8 * 2 ^ rounds * g ^ 2 * f * L) *
                (1032 * 3 ^ rounds * 2 ^ (rounds + 1) * g ^ 6) := by
              gcongr
            _ = (1032 * 2 ^ (2 * rounds + 4) * 3 ^ rounds) *
                (g ^ 8 * f * L) := by ring
        have hmN :
            ((8 * 2 ^ rounds * g ^ 2 * f * L) + 1) * N ≤
              (2 ^ (rounds + 9) + 64) * (g ^ 8 * f * L) := by
          calc
            ((8 * 2 ^ rounds * g ^ 2 * f * L) + 1) * N =
                (8 * 2 ^ rounds * g ^ 2 * f * L) * N + N := by ring
            _ ≤ (8 * 2 ^ rounds * g ^ 2 * f * L) *
                  (64 * g ^ 6) + 64 * g ^ 8 * f * L := by gcongr
            _ = (2 ^ (rounds + 9) + 64) *
                  (g ^ 8 * f * L) := by ring
        calc
          8 * ((8 * 2 ^ rounds * g ^ 2 * f * L) *
              fixedRoundWidth rounds g 0 +
              ((8 * 2 ^ rounds * g ^ 2 * f * L) + 1) * N) ≤
            (8 * (1032 * 2 ^ (2 * rounds + 4) * 3 ^ rounds) +
              8 * (2 ^ (rounds + 9) + 64)) *
                (g ^ 8 * f * L) := by
            calc
              8 * (_ + _) ≤ 8 *
                    ((1032 * 2 ^ (2 * rounds + 4) * 3 ^ rounds) *
                      (g ^ 8 * f * L) +
                    (2 ^ (rounds + 9) + 64) *
                      (g ^ 8 * f * L)) := by gcongr
              _ = _ := by ring
          _ ≤ fixedRoundLocalConstant rounds *
                (g ^ 8 * f * L) := by
            exact Nat.mul_le_mul_right _ hcoefSum
          _ = fixedRoundLocalThreshold rounds g := by
            simp [fixedRoundLocalThreshold, f, L]
            ring }

end Exponent8Epsilon
end SimpleGraph

end Lax17Proofs
