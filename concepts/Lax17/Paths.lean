import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sym

/-!
---
title: Paths, linkages, and separators
type: definition
---
A path is a simple finite walk with named endpoints.  A vertex linkage is an
indexed family of paths joining two terminal sets whose vertex sets are
pairwise disjoint; an edge linkage asks instead that their edge sets be
pairwise disjoint.  Vertex and edge separators are finite sets meeting every
path between the terminal sets.

All endpoint conventions are oriented.  Reversing every path gives the
corresponding unoriented formulation.
-/

namespace Lax17.Paths

universe u

/-- A simple finite path in `G`, with its orientation recorded. -/
structure Path {V : Type u} (G : SimpleGraph V) where
  source : V
  target : V
  walk : G.Walk source target
  simple : walk.IsPath

namespace Path

/-- The finite set of vertices used by a path. -/
noncomputable def vertices {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) : Finset V :=
  P.walk.support.toFinset

/-- The finite set of edges used by a path. -/
noncomputable def edges {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) : Finset (Sym2 V) :=
  P.walk.edges.toFinset

/-- `P` is oriented from `A` to `B`. -/
def Connects {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (A B : Finset V) : Prop :=
  P.source ∈ A ∧ P.target ∈ B

/-- Every vertex of `P` lies in `C`. -/
def StaysIn {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (C : Finset V) : Prop :=
  P.vertices ⊆ C

/-- The internal vertices of `P` avoid `X`. -/
def InternallyAvoids {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (X : Finset V) : Prop :=
  ∀ v ∈ P.vertices, v ∈ X → v = P.source ∨ v = P.target

end Path

/-- Exactly `k` pairwise vertex-disjoint paths oriented from `A` to `B`. -/
structure VertexLinkage {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) where
  path : Fin k → Path G
  connects : ∀ i : Fin k, (path i).Connects A B
  vertex_disjoint :
    Pairwise fun i j => Disjoint (path i).vertices (path j).vertices

/-- Exactly `k` pairwise edge-disjoint paths oriented from `A` to `B`. -/
structure EdgeLinkage {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) where
  path : Fin k → Path G
  connects : ∀ i : Fin k, (path i).Connects A B
  edge_disjoint :
    Pairwise fun i j => Disjoint (path i).edges (path j).edges

/-- A vertex set meeting every oriented `A`-to-`B` path. -/
def IsVertexSeparator {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∀ P : Path G, P.Connects A B →
    ∃ v ∈ P.vertices, v ∈ X

/-- An edge set meeting every oriented `A`-to-`B` path. -/
def IsEdgeSeparator {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (F : Finset (Sym2 V)) : Prop :=
  ∀ P : Path G, P.Connects A B →
    ∃ e ∈ P.edges, e ∈ F

end Lax17.Paths
