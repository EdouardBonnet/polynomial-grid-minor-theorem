import Lax17.Paths

/-!
---
title: Edge-Menger theorem
type: theorem
---
The edge form of Menger's theorem gives an exact alternative between
\(k\) edge-disjoint terminal-to-terminal paths and an edge separator of
size less than \(k\).
-/

namespace Lax17.EdgeMenger

universe u

/-- Finite edge-Menger in packing-or-separator form. -/
axiom edgeMenger :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ),
      Nonempty (Lax17.Paths.EdgeLinkage G A B k) ∨
        ∃ F : Finset (Sym2 V),
          F.card < k ∧ Lax17.Paths.IsEdgeSeparator G A B F

end Lax17.EdgeMenger
