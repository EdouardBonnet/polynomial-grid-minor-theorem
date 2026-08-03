/-!
---
title: 'Integral ceiling power roots'
type: definition
---
For positive $t$, the integer $\rho_t(g)$ used in the fixed-round
grid-minor bound is the least natural number whose $t$-th power is at least
$g^2$. We expose that meaning as a relation instead of hiding it behind a
choice operator.

The first conjunct says that `rho` is large enough. The second says that
every smaller natural number is too small. Thus the relation determines
`rho` uniquely whenever it is inhabited.
-/

namespace Lax17.PowerRoot

/-- `rho` is the least natural number satisfying $g^2 \leq \rho^t$. -/
def IsCeilingPowerRoot (t g rho : Nat) : Prop :=
  g ^ 2 ≤ rho ^ t ∧
    ∀ a : Nat, a < rho → a ^ t < g ^ 2

end Lax17.PowerRoot
