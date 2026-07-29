import Lax17.Paths

/-!
---
title: Linked terminal sets
type: definition
---
Two terminal sets are linked inside a cluster when equally large subsets can
be joined by that many vertex-disjoint paths contained in the cluster.  A
terminal set is node-well-linked when every two disjoint equally large subsets
of it are linked.  The edge versions replace vertex-disjointness by
edge-disjointness.
-/

namespace Lax17.Linkedness

universe u

open Lax17.Paths

/-- `A` and `B` are node-linked by paths contained in `C`. -/
def NodeLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C A B : Finset V) : Prop :=
  ∀ A' B' : Finset V,
    A' ⊆ A → B' ⊆ B → A'.card = B'.card →
      ∃ P : VertexLinkage G A' B' A'.card,
        ∀ i : Fin A'.card, (P.path i).StaysIn C

/-- `X` is node-well-linked inside `C`. -/
def NodeWellLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C X : Finset V) : Prop :=
  ∀ A B : Finset V,
    A ⊆ X → B ⊆ X → Disjoint A B → A.card = B.card →
      ∃ P : VertexLinkage G A B A.card,
        ∀ i : Fin A.card, (P.path i).StaysIn C

/-- `A` and `B` are edge-linked by paths contained in `C`. -/
def EdgeLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C A B : Finset V) : Prop :=
  ∀ A' B' : Finset V,
    A' ⊆ A → B' ⊆ B → A'.card = B'.card →
      ∃ P : EdgeLinkage G A' B' A'.card,
        ∀ i : Fin A'.card, (P.path i).StaysIn C

/-- `X` is edge-well-linked inside `C`. -/
def EdgeWellLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C X : Finset V) : Prop :=
  ∀ A B : Finset V,
    A ⊆ X → B ⊆ X → Disjoint A B → A.card = B.card →
      ∃ P : EdgeLinkage G A B A.card,
        ∀ i : Fin A.card, (P.path i).StaysIn C

end Lax17.Linkedness
