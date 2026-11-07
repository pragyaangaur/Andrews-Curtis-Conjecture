/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import ACConj

/-!
# ACConjCex: kernel-checked counterexamples for the conjugator layer

Two negative facts, both `decide`-checked in the kernel, that pin down what a proof of
the general peak lemma has to use.  See `ACConj.lean` for the definitions.

Nothing here says anything about the Andrews-Curtis conjecture.
-/

set_option maxRecDepth 1000000

namespace ACConj

/-- **The naive prefix-order simulation is not peak-free.**  Conjugating `a⁻¹b⁻¹` by
the prefixes of `w = a⁻¹b⁻¹` passes through the conjugate by `a⁻¹` alone, of length 4,
while both endpoints (`r` and the conjugate by all of `w`) have length 2. -/
theorem prefix_peak_fails :
    ¬ ((conjW [LA] [LA, LB]).length ≤
        max ([LA, LB] : Word).length (conjW [LA, LB] [LA, LB]).length) := by
  decide

/-- The same instance with its numbers. -/
theorem prefix_peak_fails_data :
    (conjW [LA] [LA, LB]).length = 4 ∧ ([LA, LB] : Word).length = 2 ∧
      (conjW [LA, LB] [LA, LB]).length = 2 := by
  decide

/-- The suffix-order simulation is peak-free on the same instance (the other order). -/
theorem suffix_ok_on_the_same_instance :
    (conjW [LB] [LA, LB]).length ≤
      max ([LA, LB] : Word).length (conjW [LA, LB] [LA, LB]).length := by
  decide

/-- **The suffix-order chain is not monotone in general.**  For the relator
`r = a⁻¹a⁻¹baa`, which is not cyclically reduced, the chain of suffix conjugations
drops from length 3 to length 1 when the conjugator grows from `a` to `aa`. -/
theorem monotone_fails :
    (conjW [La, La] [LA, LA, Lb, La, La]).length <
      (conjW [La] [LA, LA, Lb, La, La]).length := by
  decide

/-- The monotonicity failure, with its numbers. -/
theorem monotone_fails_data :
    (conjW [La, La] [LA, LA, Lb, La, La]).length = 1 ∧
      (conjW [La] [LA, LA, Lb, La, La]).length = 3 ∧
      ([LA, LA, Lb, La, La] : Word).length = 5 := by
  decide

/-- On the same relator the *peak* claim is not violated: the peak is the endpoint
`r` itself.  So the counterexample is to monotonicity, not to the peak bound. -/
theorem peak_ok_on_that_relator :
    max ((conjW [La] [LA, LA, Lb, La, La]).length)
        ((conjW [La, La] [LA, LA, Lb, La, La]).length) ≤
      max ([LA, LA, Lb, La, La] : Word).length
        ((conjW [La, La] [LA, LA, Lb, La, La]).length) := by
  decide

/-! ## Axiom audit -/

#print axioms ACConj.prefix_peak_fails
#print axioms ACConj.prefix_peak_fails_data
#print axioms ACConj.suffix_ok_on_the_same_instance
#print axioms ACConj.monotone_fails
#print axioms ACConj.monotone_fails_data
#print axioms ACConj.peak_ok_on_that_relator

end ACConj
