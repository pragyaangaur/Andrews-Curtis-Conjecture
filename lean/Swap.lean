import Mathlib
import Derived

/-!
Referee check, not part of the project's work.  `AC.lean`'s docstring claims
"Relator permutations are reachable, so the ordered standard target adds no
restriction"; `lean/Derived.lean` proves inverse multiplication but no theorem in
the repository states relator permutation.  This file supplies the missing
derivation at rank 2, using nothing but the constructors of `AC.Step` and the
submitted `AC.reachable_mul_inv`:

  (a, b) --mulRight 0 1--> (a b, b) --mul by (ab)⁻¹--> (a b, a⁻¹)
         --conj 0 by a⁻¹--> (b a, a⁻¹) --inv 1--> (b a, a) --mul by a⁻¹--> (b, a)

Nine `Step` applications in total.
-/

set_option autoImplicit false

namespace AC

theorem referee_swap (R : Relators 2) :
    Reachable R (Function.update (Function.update R 0 (R 1)) 1 (R 0)) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  set S1 : Relators 2 := Function.update R 0 (R 0 * R 1) with hS1
  set S2 : Relators 2 := Function.update S1 1 (S1 1 * (S1 0)⁻¹) with hS2
  set S3 : Relators 2 := Function.update S2 0 ((R 0)⁻¹ * S2 0 * ((R 0)⁻¹)⁻¹) with hS3
  set S4 : Relators 2 := Function.update S3 1 (S3 1)⁻¹ with hS4
  have e1 : Step R S1 := by rw [hS1]; exact Step.mulRight R 0 1 h01
  have e2 : Reachable S1 S2 := by
    rw [hS2]; exact reachable_mul_inv S1 (p := 1) (q := 0) h10
  have e3 : Step S2 S3 := by rw [hS3]; exact Step.conj S2 0 ((R 0)⁻¹)
  have e4 : Step S3 S4 := by rw [hS4]; exact Step.inv S3 1
  have e5 : Reachable S4 (Function.update S4 0 (S4 0 * (S4 1)⁻¹)) :=
    reachable_mul_inv S4 (p := 0) (q := 1) h01
  have hchain : Reachable R (Function.update S4 0 (S4 0 * (S4 1)⁻¹)) :=
    Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single e1)
      (Relation.ReflTransGen.trans e2
        (Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single e3)
          (Relation.ReflTransGen.trans (Relation.ReflTransGen.single e4) e5)))
  have hX : Function.update S4 0 (S4 0 * (S4 1)⁻¹)
      = Function.update (Function.update R 0 (R 1)) 1 (R 0) := by
    funext i
    fin_cases i
    · show S4 0 * (S4 1)⁻¹ = Function.update (Function.update R 0 (R 1)) 1 (R 0) 0
      rw [hS4, hS3, hS2, hS1]
      simp
    · show S4 1 = Function.update (Function.update R 0 (R 1)) 1 (R 0) 1
      rw [hS4, hS3, hS2, hS1]
      simp
  rw [hX] at hchain
  exact hchain

end AC
#print axioms AC.referee_swap
