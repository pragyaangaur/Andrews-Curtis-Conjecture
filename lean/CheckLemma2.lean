/-
Lemma 2 of notes/lit-verifier-ac-r2-v1.md, checked in Lean 4.

Each of the 14 moves of the verifier specification `ac-r2-v1`, read as a
transformation of the ordered pair of relators at rank 2, is a single
`AC.Step` or a composite of three `AC.Step`s.  The four lemmas below cover
all 14 move ids:

  moves 0, 1              reachable_inv     (any index i)
  moves 2, 4              reachable_mul     (any i ≠ j)
  moves 3, 5              reachable_mul_inv (any i ≠ j, three steps)
  moves 6 to 13           reachable_conj    (any index i and any word w)

`AC` is the file upstream/competition/tools/lean/AC.lean at commit
a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e, copied unmodified into this
directory so that `import AC` resolves.
-/
import Mathlib
import AC

open AC

namespace ACCheck

/-- Move 0 or 1: invert a relator. -/
theorem reachable_inv (R : Relators 2) (i : Fin 2) :
    Reachable R (Function.update R i (R i)⁻¹) :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Step.inv R i)

/-- Move 2 or 4: multiply a relator by the other one. -/
theorem reachable_mul (R : Relators 2) (i j : Fin 2) (h : i ≠ j) :
    Reachable R (Function.update R i (R i * R j)) :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Step.mulRight R i j h)

/-- Moves 6 to 13: conjugate a relator by one of the four letters. -/
theorem reachable_conj (R : Relators 2) (i : Fin 2) (w : Word 2) :
    Reachable R (Function.update R i (w * R i * w⁻¹)) :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Step.conj R i w)

/-- Move 3 or 5: multiply a relator by the inverse of the other one.
This is the only nontrivial row of the table: three `Step`s. -/
theorem reachable_mul_inv (R : Relators 2) (i j : Fin 2) (h : i ≠ j) :
    Reachable R (Function.update R i (R i * (R j)⁻¹)) := by
  let S : Relators 2 := Function.update R j (R j)⁻¹
  have step1 : Step R S := Step.inv R j
  have step2 : Step S (Function.update S i (S i * S j)) := Step.mulRight S i j h
  have step3 : Step (Function.update S i (S i * S j))
      (Function.update (Function.update S i (S i * S j)) j
        ((Function.update S i (S i * S j)) j)⁻¹) :=
    Step.inv _ j
  have hji : j ≠ i := fun h' => h h'.symm
  have hSj : S j = (R j)⁻¹ := Function.update_self j ((R j)⁻¹) R
  have hSi : S i = R i := by
    show Function.update R j (R j)⁻¹ i = R i
    rw [Function.update_apply]
    simp [h]
  have key : Function.update (Function.update S i (S i * S j)) j
        ((Function.update S i (S i * S j)) j)⁻¹
      = Function.update R i (R i * (R j)⁻¹) := by
    have e1 : (Function.update S i (S i * S j)) j = S j := by
      rw [Function.update_apply]
      simp [hji]
    rw [e1, hSj, inv_inv]
    rw [Function.update_comm h]
    have e2 : Function.update S j (R j) = R := by
      show Function.update (Function.update R j (R j)⁻¹) j (R j) = R
      rw [Function.update_idem]
      exact Function.update_eq_self j R
    rw [e2, hSi]
  rw [← key]
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl step1) step2) step3

/-- The composition step behind the letter by letter expansion of Lemma 3:
conjugating by `a * b` is conjugating by `b` and then by `a`.  Iterating this
over the letters of a reduced word gives the verifier path of length `L`. -/
theorem conj_mul (R : Relators 2) (i : Fin 2) (a b : Word 2) :
    Function.update R i ((a * b) * R i * (a * b)⁻¹)
      = Function.update (Function.update R i (b * R i * b⁻¹)) i
          (a * (b * R i * b⁻¹) * a⁻¹) := by
  rw [Function.update_idem]
  congr 1
  group

/-- Hence conjugation by `a * b` is reachable in two AC steps. -/
theorem reachable_conj_mul (R : Relators 2) (i : Fin 2) (a b : Word 2) :
    Reachable R (Function.update R i ((a * b) * R i * (a * b)⁻¹)) := by
  rw [conj_mul, Function.update_idem]
  have h1 : Reachable R (Function.update R i (b * R i * b⁻¹)) := reachable_conj R i b
  have h2 : Step (Function.update R i (b * R i * b⁻¹))
      (Function.update R i (a * (b * R i * b⁻¹) * a⁻¹)) := by
    have := Step.conj (Function.update R i (b * R i * b⁻¹)) i a
    rw [Function.update_idem] at this
    simpa [Function.update_self] using this
  exact Relation.ReflTransGen.tail h1 h2

#check @ACCheck.reachable_inv
#check @ACCheck.reachable_mul
#check @ACCheck.reachable_conj
#check @ACCheck.reachable_mul_inv
#check @ACCheck.reachable_conj_mul

end ACCheck

#print axioms ACCheck.reachable_inv
#print axioms ACCheck.reachable_mul
#print axioms ACCheck.reachable_conj
#print axioms ACCheck.reachable_mul_inv
#print axioms ACCheck.reachable_conj_mul
