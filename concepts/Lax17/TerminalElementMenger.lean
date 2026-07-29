import Lax17.TerminalConnectivity

/-!
---
title: Terminal element-Menger theorem
type: theorem
---
For a named-edge multigraph, terminal element-connectivity is equivalent to
the existence of paths disjoint in both internal vertices and named edge
copies between every pair of terminals.
-/

namespace Lax17.TerminalElementMenger

universe u

/-- Terminal element-Menger for named-edge multigraphs. -/
axiom terminalElementMenger :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (H : Lax17.TerminalConnectivity.EdgeIndexedGraph V)
    (terminals : Finset V) (k : ℕ),
      H.TerminalElementConnectedAtLeast terminals k ↔
        ∀ ⦃a : V⦄, a ∈ terminals →
          ∀ ⦃b : V⦄, b ∈ terminals → a ≠ b →
            Nonempty (H.ElementLinkage a b k)

end Lax17.TerminalElementMenger
