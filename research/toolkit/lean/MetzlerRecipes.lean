/-
# The Metzler recipe outside round 8's parameter set

`AC8.metzler_recipe (k m t j) (hk : k = 1 + t*j)` moves `metz k m 1` to `metz k m j` for all
parameters at once.  Round 8's record shows the kernel instances at Metzler's own pair and two
family rows (`(5,5,2,2)`, `(5,5,1,4)`, `(13,7,4,3)`).  Here are further instances, deliberately
outside that set: different `m` (including `m = 1`), larger `t`, and `j > 2`.  Each is a
kernel-checked existential over a move list, and each is non-vacuous (the two endpoints are
different presentations, checked below).

The point is not that instantiating a proved `∀` is hard — it is a one-line application — but
that the recipe's domain is *not* confined to the worked parameters, and that every instance
automatically satisfies `gcd(j,k) = 1` (`MetzlerSharp.coprime_of_recipe_hypothesis`), which is
why the group obstruction of `MetzlerSharp` can never obstruct the recipe itself.

Nothing here proves or disproves the Andrews-Curtis conjecture.
-/
import MetzlerSharp
import AC8

namespace MetzlerRecipes

open AC8

/-- `(k,m,t,j) = (9,4,4,2)`: `k = 1 + t*j = 9`, coprime pair `(2,9)`. -/
theorem recipe_k9_m4_j2 : ∃ ms : List QMove, replay ms (metz 9 4 1) = some (metz 9 4 2) :=
  AC8.metzler_recipe 9 4 4 2 (by decide)

/-- `(k,m,t,j) = (10,3,3,3)`: `k = 1 + 3*3 = 10`, coprime pair `(3,10)`. -/
theorem recipe_k10_m3_j3 : ∃ ms : List QMove, replay ms (metz 10 3 1) = some (metz 10 3 3) :=
  AC8.metzler_recipe 10 3 3 3 (by decide)

/-- `(k,m,t,j) = (7,2,2,3)`: `k = 1 + 2*3 = 7`, coprime pair `(3,7)`. -/
theorem recipe_k7_m2_j3 : ∃ ms : List QMove, replay ms (metz 7 2 1) = some (metz 7 2 3) :=
  AC8.metzler_recipe 7 2 2 3 (by decide)

/-- `(k,m,t,j) = (25,6,3,8)`: `k = 1 + 3*8 = 25`, coprime pair `(8,25)`. -/
theorem recipe_k25_m6_j8 : ∃ ms : List QMove, replay ms (metz 25 6 1) = some (metz 25 6 8) :=
  AC8.metzler_recipe 25 6 3 8 (by decide)

/-- `(k,m,t,j) = (13,9,3,4)`: `k = 1 + 3*4 = 13`, coprime pair `(4,13)`; `m = 9` is outside
round 8's `m = 5, 7`. -/
theorem recipe_k13_m9_j4 : ∃ ms : List QMove, replay ms (metz 13 9 1) = some (metz 13 9 4) :=
  AC8.metzler_recipe 13 9 3 4 (by decide)

/-- `(k,m,t,j) = (6,1,1,5)`: `k = 1 + 5 = 6`, coprime pair `(5,6)`, and the degenerate
`m = 1` (so `y = 1` in the presented group). -/
theorem recipe_k6_m1_j5 : ∃ ms : List QMove, replay ms (metz 6 1 1) = some (metz 6 1 5) :=
  AC8.metzler_recipe 6 1 1 5 (by decide)

/-- Non-vacuity of the `(9,4,2)` instance: the endpoints are different presentations. -/
theorem metz_9_4_1_ne_2 : metz 9 4 1 ≠ metz 9 4 2 := by decide

/-- Non-vacuity of the `(10,3,3)` instance. -/
theorem metz_10_3_1_ne_3 : metz 10 3 1 ≠ metz 10 3 3 := by decide

/-- Every recipe instance has `gcd(j,k) = 1` (pure arithmetic, by
`MetzlerSharp.coprime_of_recipe_hypothesis`). -/
theorem coprime_k25_j8 : Nat.Coprime 8 25 :=
  MetzlerSharp.coprime_of_recipe_hypothesis (k := 25) (j := 8) (t := 3) (by decide)

/- Axiom audit. -/
#print axioms recipe_k9_m4_j2
#print axioms recipe_k10_m3_j3
#print axioms recipe_k7_m2_j3
#print axioms recipe_k25_m6_j8
#print axioms recipe_k13_m9_j4
#print axioms recipe_k6_m1_j5
#print axioms metz_9_4_1_ne_2
#print axioms metz_10_3_1_ne_3
#print axioms coprime_k25_j8

end MetzlerRecipes
