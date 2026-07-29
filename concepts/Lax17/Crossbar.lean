import Lax17.Paths

/-!
---
title: Crossbars and pseudo-grids
type: definition
---
An \((A,B,X)\)-crossbar consists of disjoint main paths from \(A\) to \(B\)
and one disjoint spoke from every main path to \(X\).  Each spoke meets its own
main path exactly once and avoids all other main paths.

A pseudo-grid is a pair of internally disjoint path families in which every
row meets every column.  It records the grid-like alternative produced by the
crossbar analysis before branch sets are assembled.
-/

namespace Lax17.Crossbar

universe u

open Lax17.Paths

/-- A crossbar of width `ρ`. -/
structure System {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B X : Finset V) (ρ : ℕ) where
  mainPath : Fin ρ → Path G
  main_connects : ∀ i : Fin ρ, (mainPath i).Connects A B
  main_disjoint :
    Pairwise fun i j => Disjoint (mainPath i).vertices (mainPath j).vertices
  spokePath : Fin ρ → Path G
  spoke_disjoint :
    Pairwise fun i j => Disjoint (spokePath i).vertices (spokePath j).vertices
  attachment : Fin ρ → V
  attachment_on_main :
    ∀ i : Fin ρ, attachment i ∈ (mainPath i).vertices
  attachment_on_spoke :
    ∀ i : Fin ρ, attachment i ∈ (spokePath i).vertices
  exact_attachment :
    ∀ i : Fin ρ,
      (mainPath i).vertices ∩ (spokePath i).vertices = {attachment i}
  spoke_reaches_X :
    ∀ i : Fin ρ,
      (spokePath i).source ∈ X ∨ (spokePath i).target ∈ X
  spoke_avoids_other_main :
    ∀ ⦃i j : Fin ρ⦄, i ≠ j →
      Disjoint (spokePath i).vertices (mainPath j).vertices

/-- A grid-like family of rows and columns. -/
structure PseudoGrid {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (rows columns : ℕ) where
  row : Fin rows → Path G
  column : Fin columns → Path G
  rows_disjoint :
    Pairwise fun i j => Disjoint (row i).vertices (row j).vertices
  columns_disjoint :
    Pairwise fun i j => Disjoint (column i).vertices (column j).vertices
  row_meets_column :
    ∀ i : Fin rows, ∀ j : Fin columns,
      ((row i).vertices ∩ (column j).vertices).Nonempty

end Lax17.Crossbar
