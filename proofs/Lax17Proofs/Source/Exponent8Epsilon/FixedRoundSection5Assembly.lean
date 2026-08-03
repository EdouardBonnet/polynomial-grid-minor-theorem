import Lax17Proofs.Source.Exponent8.Section5Assembly
import Lax17Proofs.Source.Exponent8Epsilon.FixedRoundRecursion

namespace Lax17Proofs

/-!
# Section 5 assembly after an arbitrary fixed number of rounds

The large-depth and terminal consumers in `Exponent8.Section5Assembly` are
already parameter-generic.  This file merely dispatches the two constructors
of the fixed-round controller to those existing theorems.
-/

namespace SimpleGraph
namespace Exponent8Epsilon

open Exponent8

universe u v

theorem FixedRoundRecursiveSlicingResult.weakPathOfSetsSystem
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {rounds g : ℕ}
    {p : FixedRoundParameters rounds g Rbar.card (32 * g ^ 4)}
    (Result : FixedRoundRecursiveSlicingResult
      G H A B X P Q Rbar Qbar rounds g (32 * g ^ 4) p)
    (hintersects : PathSlicing.PathPackingIntersectsLinkage Rbar Qbar)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hNlower : 64 * g ^ 4 ≤ Rbar.card)
    (hNupper : Rbar.card ≤ 64 * g ^ 6) :
    Nonempty (WeakPathOfSetsSystem H (g ^ 2) (g ^ 2)) := by
  cases Result with
  | large j layer output =>
      apply layer.weakPathOfSetsSystem_of_largeSliceLayer
        output hintersects p.g_at_least_two hpow hNlower hNupper
      simpa [p.assemblyMass_eq, fixedRoundAssemblyMass,
        fixedRoundLogFactor] using p.large_mass j
  | final layer =>
      exact layer.weakPathOfSetsSystem_of_finalLayer
        hintersects p.g_at_least_two hNlower hNupper
        (p.widths_pos (Fin.last rounds))
        (by simpa [fixedRoundLogFactor] using p.final_slice_count)

/-- Source-level fixed-round Section 5 producer in the reduced graph created
by Observation 4.4. -/
theorem exists_reduced_weakPathOfSetsSystem_fixedRound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {rounds g D : ℕ}
    (Gamma : PseudoGrid G A B X g D P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hrounds : 0 < rounds)
    (hg : 2 ≤ g)
    (hpow : CrossbarContract.IsPowerOfTwo g)
    (hNlower : 64 * g ^ 4 ≤ Gamma.rowPacking.card)
    (hNupper : Gamma.rowPacking.card ≤ 64 * g ^ 6)
    (hDscale : 64 * g ^ 4 ≤ D)
    (hgood :
      fixedRoundM rounds g 0 * fixedRoundWidth rounds g 0 +
          (fixedRoundM rounds g 0 + 1) * Gamma.rowPacking.card ≤
        Gamma.goodQSet.card)
    (hXdisjoint :
      ∀ p : P.Index, Disjoint X (P.path p).vertexSet)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2))) :
    ∃ Root : RootedObservation44State Gamma,
      ∃ hReduced : Root.state.IsReduced,
        Nonempty
          (WeakPathOfSetsSystem
            (Root.state.reducedGraph hReduced)
            (g ^ 2) (g ^ 2)) := by
  have hDpos : 0 < D := by
    have : 0 < 64 * g ^ 4 := by positivity
    exact this.trans_le hDscale
  have hNpos : 0 < Gamma.rowPacking.card := by
    have : 0 < 64 * g ^ 4 := by positivity
    exact this.trans_le hNlower
  let p0 := explicitFixedRoundParameters rounds g
    Gamma.rowPacking.card (32 * g ^ 4)
    hrounds hg hNupper rfl
  have hinitialMass :
      2 * Gamma.rowPacking.card * (4 * g ^ 2) ≤
        (32 * g ^ 4) * fixedRoundWidth rounds g 0 := by
    simpa [p0, explicitFixedRoundParameters] using p0.pruning_at (0 : Fin (rounds + 1))
  rcases
      exists_initialRecursiveSliceLayer_of_pseudoGrid
        Gamma hminimal hDpos
        (by
          simpa [p0, explicitFixedRoundParameters] using
            p0.counts_pos (0 : Fin (rounds + 1)))
        (by
          simpa [p0, explicitFixedRoundParameters] using
            p0.widths_pos (0 : Fin (rounds + 1)))
        hgood
        (by positivity : 0 < 32 * g ^ 4)
        (by
          calc
            2 * (32 * g ^ 4) = 64 * g ^ 4 := by ring
            _ ≤ D := hDscale)
        hinitialMass hXdisjoint with
    ⟨Root, hReduced, ⟨L0⟩⟩
  let Rbar := Root.state.reducedRow hReduced
  let Qbar := Root.state.reducedRetained hReduced
  have hRcard : Rbar.card = Gamma.rowPacking.card := by
    simp [Rbar]
  have hRlower : 64 * g ^ 4 ≤ Rbar.card := by
    rw [hRcard]
    exact hNlower
  have hRupper : Rbar.card ≤ 64 * g ^ 6 := by
    rw [hRcard]
    exact hNupper
  let p := explicitFixedRoundParameters rounds g
    Rbar.card (32 * g ^ 4) hrounds hg hRupper rfl
  let Ctxt :=
    Root.recursiveSlicingContext hReduced hNpos
      (by positivity : 0 < 32 * g ^ 4)
      (by
        calc
          2 * (32 * g ^ 4) = 64 * g ^ 4 := by ring
          _ ≤ D := hDscale)
      hXdisjoint
  have hintersects :
      PathSlicing.PathPackingIntersectsLinkage Rbar Qbar := by
    simpa [Rbar, Qbar] using
      Root.state.reducedRetained_intersects_reducedRow hReduced hDpos
  let L0' :
      RecursiveSliceLayer
        G (Root.state.reducedGraph hReduced) A B X P Q
        Rbar Qbar (p.m 0) (p.width 0)
        (4 * g ^ 2) (32 * g ^ 4) := by
    simpa [p, explicitFixedRoundParameters] using L0
  rcases fixedRoundRecursiveSlicing Ctxt p L0' hnoCrossbar with
    ⟨Result⟩
  refine ⟨Root, hReduced, ?_⟩
  exact Result.weakPathOfSetsSystem
    hintersects hpow hRlower hRupper

end Exponent8Epsilon
end SimpleGraph

end Lax17Proofs
