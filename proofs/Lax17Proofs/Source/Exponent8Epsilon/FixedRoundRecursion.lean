import Lax17Proofs.Source.Exponent8Epsilon.FixedRoundParameters

namespace Lax17Proofs

/-!
# An arbitrary finite number of recursive slicing rounds

This module contains no new graph-theoretic argument.  It structurally
iterates `Exponent8.recursiveSlicingRound`.  At the first majority-large
depth it records that exit; if every processed depth is small, it records the
terminal layer after exactly `rounds` refinements.
-/

namespace SimpleGraph
namespace Exponent8Epsilon

open Exponent8

universe u v

inductive FixedRoundRecursiveSlicingResult
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (A B X : Finset V)
    (P : PerfectPathPacking G A B)
    (Q : PerfectPathPacking G A X)
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    (rounds g Dhat : ℕ)
    (p : FixedRoundParameters rounds g Rbar.card Dhat) :
    Type (max u v)
  | large
      (j : Fin rounds)
      (layer : RecursiveSliceLayer
        G H A B X P Q Rbar Qbar
        (p.m j.castSucc) (p.width j.castSucc)
        (4 * g ^ 2) Dhat)
      (output : LargeSliceLayer layer (p.cap j))
  | final
      (layer : RecursiveSliceLayer
        G H A B X P Q Rbar Qbar
        (p.m (Fin.last rounds)) (p.width (Fin.last rounds))
        (4 * g ^ 2) Dhat)

private noncomputable def fixedRoundRecursiveSlicingAux
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {rounds g Dhat : ℕ}
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar Dhat)
    (p : FixedRoundParameters rounds g Rbar.card Dhat)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2)))
    (remaining depth : ℕ)
    (hsum : depth + remaining = rounds)
    (hdepth : depth < rounds + 1)
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (p.m ⟨depth, hdepth⟩) (p.width ⟨depth, hdepth⟩)
      (4 * g ^ 2) Dhat) :
    FixedRoundRecursiveSlicingResult
      G H A B X P Q Rbar Qbar rounds g Dhat p := by
  induction remaining generalizing depth with
  | zero =>
      have hdeq : depth = rounds := by omega
      subst depth
      exact FixedRoundRecursiveSlicingResult.final L
  | succ remaining ih =>
      have hdlt : depth < rounds := by omega
      let j : Fin rounds := ⟨depth, hdlt⟩
      let Lcur : RecursiveSliceLayer
          G H A B X P Q Rbar Qbar
          (p.m j.castSucc) (p.width j.castSucc)
          (4 * g ^ 2) Dhat := by
        simpa [j] using L
      have hgpos : 0 < g := by
        have := p.g_at_least_two
        omega
      let roundResult := Classical.choice <|
        recursiveSlicingRound C Lcur hgpos p.fanout_pos
          (p.counts_pos j.succ) (p.widths_pos j.succ)
          (p.count_step j) (p.refine_step j)
          (p.pruning_at j.succ) hnoCrossbar
      cases roundResult with
      | large output =>
          exact FixedRoundRecursiveSlicingResult.large j Lcur output
      | refined Lnext =>
          exact ih (depth + 1) (by omega) (by omega) Lnext

/-- Complete finite controller for `rounds` recursive slicing steps. -/
theorem fixedRoundRecursiveSlicing
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {rounds g Dhat : ℕ}
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar Dhat)
    (p : FixedRoundParameters rounds g Rbar.card Dhat)
    (L0 : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      (p.m 0) (p.width 0) (4 * g ^ 2) Dhat)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    Nonempty (FixedRoundRecursiveSlicingResult
      G H A B X P Q Rbar Qbar rounds g Dhat p) := by
  exact ⟨fixedRoundRecursiveSlicingAux C p hnoCrossbar
    rounds 0 (by omega) (by omega) L0⟩

end Exponent8Epsilon
end SimpleGraph

end Lax17Proofs
