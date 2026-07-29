import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Lax17.Degree

/-!
---
title: Edge expansion and cut-matching transcripts
type: definition
---
The edge boundary of a vertex set consists of the graph edges with exactly one
endpoint in the set.  A finite graph is an \((a/b)\)-edge-expander when every
set containing at most half of the vertices has boundary at least
\((a/b)\) times its size.

A cut-matching transcript is a sequence of perfect matchings, each crossing a
bisection chosen in that round.  Its union graph is the union of those
matchings.
-/

namespace Lax17.Expansion

universe u

open Lax17.Degree

/-- The finite edge boundary of `S`. -/
noncomputable def edgeBoundary {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e =>
    ∃ x y : V, e = s(x, y) ∧
      ((x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S))

/-- Every set of at most half the vertices expands by a factor of `a / b`. -/
def IsEdgeExpander {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧
    ∀ S : Finset V, 0 < S.card → 2 * S.card ≤ Fintype.card V →
      b * (edgeBoundary G S).card ≥ a * S.card

/-- Every vertex has exactly one neighbour. -/
def IsPerfectMatching {V : Type u}
    (M : SimpleGraph V) : Prop :=
  ∀ v : V, Exactly M v 1

/-- A sequence of perfect matchings crossing prescribed bisections. -/
structure CutMatchingTranscript (V : Type u) [Fintype V] [DecidableEq V]
    (rounds : ℕ) where
  cut : Fin rounds → Finset V
  cut_is_half :
    ∀ i : Fin rounds, 2 * (cut i).card = Fintype.card V
  matching : Fin rounds → SimpleGraph V
  matching_perfect :
    ∀ i : Fin rounds, IsPerfectMatching (matching i)
  matching_crosses_cut :
    ∀ i : Fin rounds, ∀ ⦃x y : V⦄,
      (matching i).Adj x y →
        (x ∈ cut i ∧ y ∉ cut i) ∨ (y ∈ cut i ∧ x ∉ cut i)

namespace CutMatchingTranscript

/-- The graph obtained by taking the union of all matching rounds. -/
def unionGraph {V : Type u} [Fintype V] [DecidableEq V] {rounds : ℕ}
    (T : CutMatchingTranscript V rounds) : SimpleGraph V :=
  ⨆ i : Fin rounds, T.matching i

end CutMatchingTranscript

end Lax17.Expansion
