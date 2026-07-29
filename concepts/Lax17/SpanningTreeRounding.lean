import Mathlib.Data.Rat.Defs
import Lax17.Degree

/-!
---
title: Bounded-degree spanning-tree relaxation
type: definition
---
A feasible bounded-degree spanning-tree point assigns nonnegative rational
weights to the edges, has total weight \(|V|-1\), satisfies every forest
inequality, and has fractional degree at most \(B\) at every vertex.  This is
the unweighted relaxation used by the Singh--Lau rounding theorem.
-/

namespace Lax17.SpanningTreeRounding

universe u

open Finset

/-- Both endpoints of an unordered pair lie in `S`. -/
def PairInside {V : Type u} [DecidableEq V]
    (S : Finset V) : Sym2 V → Prop :=
  Sym2.lift
    ⟨fun x y => x ∈ S ∧ y ∈ S, by
      intro x y
      exact propext and_comm⟩

/-- The edges from `edges` with both endpoints in `S`. -/
noncomputable def internalEdges {V : Type u} [DecidableEq V]
    (edges : Finset (Sym2 V)) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact edges.filter (PairInside S)

/-- The edges from `edges` incident with `v`. -/
noncomputable def incidentEdges {V : Type u} [DecidableEq V]
    (edges : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) := by
  classical
  exact edges.filter fun e => v ∈ e

/-- A feasible point of the bounded-degree spanning-tree relaxation. -/
structure FeasiblePoint {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : ℕ) where
  /-- A finite enumeration of the host edges. -/
  edges : Finset (Sym2 V)
  /-- The enumeration contains exactly the edges of `G`. -/
  edges_spec : ∀ e : Sym2 V, e ∈ edges ↔ e ∈ G.edgeSet
  weight : Sym2 V → ℚ
  nonnegative : ∀ e : Sym2 V, e ∈ edges → 0 ≤ weight e
  total :
    edges.sum weight = (Fintype.card V - 1 : ℕ)
  forest :
    ∀ S : Finset V, S ≠ Finset.univ →
      (internalEdges edges S).sum weight ≤ (S.card - 1 : ℕ)
  degree :
    ∀ v : V, (incidentEdges edges v).sum weight ≤ B

end Lax17.SpanningTreeRounding
