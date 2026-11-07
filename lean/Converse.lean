import AC

/-!
# The converse: every published move is a finite sequence of verifier moves

`AC.lean` allows a single `Step` to conjugate a relator by an arbitrary element
of the free group. The competition's frozen move set `ac-r2-v1` allows only
conjugation by a single generator letter or its inverse, multiplication by the
other relator, and inversion. Soundness, that every verifier move is a `Step`,
was proved separately. This file proves the other direction at rank two: every
`Step` is a finite sequence of verifier moves.

The only substantive point is that conjugation by a product splits. Conjugating
by `a * b` is conjugating by `b` and then by `a`, so by induction on the word,
conjugation by any element is conjugation by each letter in turn. That is the
step which makes the two move sets agree rather than merely overlap.

Everything is at rank two, which is the rank the competition scores.
-/

set_option autoImplicit false

namespace AC

/-- The verifier's move at rank two: invert a relator, multiply one relator by
the other, or conjugate one relator by a generator or by its inverse.

Twelve of the fourteen rows of `ac-r2-v1` appear here directly. The two that do
not are rows 3 and 5, multiplication by the inverse of the other relator, and
those are not omitted from the correspondence: they are three-step composites,
as `AC.reachable_mul_inv` in `lean/Derived.lean` shows, and the argument below
therefore covers them through that derived move rather than as a single
constructor. -/
inductive VStep : Relators 2 → Relators 2 → Prop
  /-- Moves 0 and 1: invert a relator. -/
  | inv (R : Relators 2) (i : Fin 2) : VStep R (Function.update R i (R i)⁻¹)
  /-- Moves 2 and 4: multiply a relator by the other one. -/
  | mul (R : Relators 2) (i j : Fin 2) (h : i ≠ j) :
      VStep R (Function.update R i (R i * R j))
  /-- Moves 6 to 13, conjugation by a generator. -/
  | conj (R : Relators 2) (i : Fin 2) (x : Fin 2) :
      VStep R (Function.update R i (FreeGroup.of x * R i * (FreeGroup.of x)⁻¹))
  /-- Moves 6 to 13, conjugation by the inverse of a generator. -/
  | conjInv (R : Relators 2) (i : Fin 2) (x : Fin 2) :
      VStep R (Function.update R i ((FreeGroup.of x)⁻¹ * R i * (FreeGroup.of x)))

/-- Conjugating by a product is conjugating by each factor in turn. -/
theorem conj_mul_eq (R : Relators 2) (i : Fin 2) (a b : Word 2) :
    Function.update R i ((a * b) * R i * (a * b)⁻¹)
      = Function.update (Function.update R i (b * R i * b⁻¹)) i
          (a * (b * R i * b⁻¹) * a⁻¹) := by
  rw [Function.update_idem]
  congr 1
  rw [mul_inv_rev]
  simp only [mul_assoc]

/-- Conjugation by any element of the free group is a finite sequence of
conjugations by generators and their inverses. -/
theorem conj_word_reachable (i : Fin 2) (w : Word 2) :
    ∀ R : Relators 2,
      Relation.ReflTransGen VStep R (Function.update R i (w * R i * w⁻¹)) := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      intro R
      have h : Function.update R i ((1 : Word 2) * R i * (1 : Word 2)⁻¹) = R := by simp
      rw [h]
  | of x =>
      intro R
      exact Relation.ReflTransGen.single (VStep.conj R i x)
  | inv_of x ih =>
      intro R
      have h : Function.update R i ((FreeGroup.of x)⁻¹ * R i * ((FreeGroup.of x)⁻¹)⁻¹)
          = Function.update R i ((FreeGroup.of x)⁻¹ * R i * FreeGroup.of x) := by
        rw [inv_inv]
      rw [h]
      exact Relation.ReflTransGen.single (VStep.conjInv R i x)
  | mul a b iha ihb =>
      intro R
      have hstep : Relation.ReflTransGen VStep R
          (Function.update R i (b * R i * b⁻¹)) := ihb R
      rw [conj_mul_eq R i a b]
      refine Relation.ReflTransGen.trans hstep ?_
      simpa using iha (Function.update R i (b * R i * b⁻¹))

/-- Every single move of the published relation at rank two is a finite sequence
of verifier moves. -/
theorem step_to_vstep {R S : Relators 2} (h : Step R S) :
    Relation.ReflTransGen VStep R S := by
  induction h with
  | inv i => exact Relation.ReflTransGen.single (VStep.inv R i)
  | mulRight i j hij => exact Relation.ReflTransGen.single (VStep.mul R i j hij)
  | conj i w => exact conj_word_reachable i w R

/-- **The converse.** Every finite sequence of published moves at rank two is a
finite sequence of verifier moves. -/
theorem reachable_to_vstep {R S : Relators 2} (h : Reachable R S) :
    Relation.ReflTransGen VStep R S := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.trans ih (step_to_vstep hs)

end AC

#print axioms AC.conj_mul_eq
#print axioms AC.conj_word_reachable
#print axioms AC.step_to_vstep
#print axioms AC.reachable_to_vstep
