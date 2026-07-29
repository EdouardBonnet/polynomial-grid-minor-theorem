import Lax17.Crossbar
import Lax17.GridMinor
import Lax17.PathOfSets

/-!
---
title: Crossbar stitching
type: theorem
---
Compatible local crossbars along a hairy path-of-sets system can be stitched
into a square grid minor.
-/

namespace Lax17.CrossbarStitching

universe u

/-- Compatible local crossbars along a hairy path-of-sets system can be
stitched into a square grid minor. -/
axiom crossbarStitching :
  ∃ c : ℕ, 0 < c ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {ℓ w g : ℕ}
      (H : Lax17.PathOfSets.HairySystem G ℓ w),
        2 ≤ g → c * g ≤ ℓ → g ≤ w →
          (∀ i : Fin ℓ,
            Nonempty
              (Lax17.Crossbar.System G
                (H.base.left i) (H.base.right i)
                (H.hairEndpoint i) g)) →
            Lax17.GridMinor.ContainsGridMinor G g

end Lax17.CrossbarStitching
