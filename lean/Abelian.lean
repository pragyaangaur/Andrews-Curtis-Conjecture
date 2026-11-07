import AC
import Mathlib.Tactic

/-!
# The exponent-sum matrix and the invariant it carries

Every `ac-r2-v1` move is a Tietze move, so it preserves the group presented.
This file records the computable version of that fact which the search used as a
lower bound. Map each word to its exponent-sum vector in `ℤ × ℤ`, the image of
the abelianisation. The ordered pair of relators then gives a pair of integer
vectors, and each kind of move acts on them in a fixed elementary way:

* inversion negates a vector,
* multiplication of one relator by another adds one vector to the other,
* conjugation by any word leaves both vectors unchanged.

Two things follow and both are proved below. The determinant is preserved up to
sign along every path, so a presentation whose matrix has determinant other than
plus or minus one admits no path to the standard presentation at all. And the
pair of vectors moves only by elementary row operations, which is the form in
which it bounds path length from below.

This is a lower bound on path length and an obstruction to triviality in the
abelian case. It says nothing about the Andrews-Curtis conjecture itself.
-/

set_option autoImplicit false

namespace AC

/-- Local helper: the value of `Function.update` at the updated index. -/
theorem upd_same' (f : Fin 2 → Word 2) (i : Fin 2) (v : Word 2) :
    Function.update f i v i = v := by
  simp

/-- Local helper: the value of `Function.update` away from the updated index. -/
theorem upd_other' (f : Fin 2 → Word 2) {i j : Fin 2} (h : i ≠ j) (v : Word 2) :
    Function.update f i v j = f j := by
  simp only [Function.update_apply]
  rw [if_neg]
  exact fun hji => h hji.symm

/-- The exponent sum of a word, as an element of the additive group `ℤ × ℤ`,
written multiplicatively so that it is a group homomorphism out of the free
group. The two generators map to the two standard basis vectors. -/
noncomputable def expsum : Word 2 →* Multiplicative (ℤ × ℤ) :=
  FreeGroup.lift (fun x : Fin 2 =>
    if x = 0 then Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ))
    else Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)))

/-- The exponent sum in additive notation, which is what the estimates use. -/
noncomputable def exAdd (w : Word 2) : ℤ × ℤ := (expsum w).toAdd

theorem exAdd_mul (w v : Word 2) : exAdd (w * v) = exAdd w + exAdd v := by
  simp [exAdd, map_mul]

theorem exAdd_inv (w : Word 2) : exAdd w⁻¹ = - exAdd w := by
  simp [exAdd, map_inv]

/-- Conjugation leaves the exponent sum unchanged. This is the fact that makes
the matrix a bound on path length rather than merely an invariant of the group. -/
theorem exAdd_conj (w r : Word 2) : exAdd (w * r * w⁻¹) = exAdd r := by
  rw [exAdd_mul, exAdd_mul, exAdd_inv]
  abel

/-- Move 0 or 1, inverting a relator, negates its exponent vector. -/
theorem exAdd_update_inv (i : Fin 2) (R : Relators 2) :
    exAdd (Function.update R i (R i)⁻¹ i) = - exAdd (R i) := by
  rw [upd_same', exAdd_inv]

/-- Moves 2 and 4, multiplying a relator by the other, add the two vectors. -/
theorem exAdd_update_mul (i j : Fin 2) (R : Relators 2) (_h : i ≠ j) :
    exAdd (Function.update R i (R i * R j) i) = exAdd (R i) + exAdd (R j) := by
  rw [upd_same', exAdd_mul]

/-- Moves 6 to 13, conjugation by a generator or its inverse, leave the vector
of the conjugated relator exactly as it was. -/
theorem exAdd_update_conj (i : Fin 2) (R : Relators 2) (w : Word 2) :
    exAdd (Function.update R i (w * R i * w⁻¹) i) = exAdd (R i) := by
  rw [upd_same', exAdd_conj]

/-- The exponent matrix of a balanced presentation of rank two. -/
noncomputable def expmat (R : Relators 2) : Fin 2 → ℤ × ℤ := fun i => exAdd (R i)

/-- The determinant of the exponent matrix. -/
noncomputable def detm (R : Relators 2) : ℤ :=
  (expmat R 0).1 * (expmat R 1).2 - (expmat R 0).2 * (expmat R 1).1

/-- The standard presentation has the identity matrix and determinant one. -/
theorem detm_standard : detm (standard 2) = 1 := by
  unfold detm expmat standard exAdd expsum
  simp

/-- Inverting a relator flips the sign of the determinant. -/
theorem detm_inv_zero (R : Relators 2) :
    detm (Function.update R 0 (R 0)⁻¹) = - detm R := by
  have h1 : Function.update R 0 (R 0)⁻¹ 1 = R 1 :=
    upd_other' R (by decide : (0 : Fin 2) ≠ 1) _
  unfold detm expmat
  rw [upd_same', exAdd_inv, h1, Prod.fst_neg, Prod.snd_neg]
  ring

theorem detm_inv_one (R : Relators 2) :
    detm (Function.update R 1 (R 1)⁻¹) = - detm R := by
  have h0 : Function.update R 1 (R 1)⁻¹ 0 = R 0 :=
    upd_other' R (by decide : (1 : Fin 2) ≠ 0) _
  unfold detm expmat
  rw [upd_same', exAdd_inv, h0, Prod.fst_neg, Prod.snd_neg]
  ring

/-- Inverting a relator flips the sign of the determinant. -/
theorem detm_inv (R : Relators 2) (i : Fin 2) :
    detm (Function.update R i (R i)⁻¹) = - detm R := by
  fin_cases i
  · exact detm_inv_zero R
  · exact detm_inv_one R

/-- Multiplying relator 0 by relator 1 leaves the determinant unchanged: this is
the elementary row operation that adds one row to another. -/
theorem detm_mul_zero (R : Relators 2) :
    detm (Function.update R 0 (R 0 * R 1)) = detm R := by
  have h1 : Function.update R 0 (R 0 * R 1) 1 = R 1 :=
    upd_other' R (by decide : (0 : Fin 2) ≠ 1) _
  unfold detm expmat
  rw [upd_same', exAdd_mul, h1, Prod.fst_add, Prod.snd_add]
  ring

/-- Multiplying relator 1 by relator 0 leaves the determinant unchanged. -/
theorem detm_mul_one (R : Relators 2) :
    detm (Function.update R 1 (R 1 * R 0)) = detm R := by
  have h0 : Function.update R 1 (R 1 * R 0) 0 = R 0 :=
    upd_other' R (by decide : (1 : Fin 2) ≠ 0) _
  unfold detm expmat
  rw [upd_same', exAdd_mul, h0, Prod.fst_add, Prod.snd_add]
  ring

/-- Multiplying one relator by another leaves the determinant unchanged for any
pair of distinct indices at rank two. -/
theorem detm_mul (R : Relators 2) (i j : Fin 2) (h : i ≠ j) :
    detm (Function.update R i (R i * R j)) = detm R := by
  fin_cases i
  · have hj : j = 1 := by fin_cases j <;> simp_all
    subst hj
    exact detm_mul_zero R
  · have hj : j = 0 := by fin_cases j <;> simp_all
    subst hj
    exact detm_mul_one R

/-- Conjugation leaves the whole exponent matrix fixed. -/
theorem expmat_update_conj (R : Relators 2) (i : Fin 2) (w : Word 2) :
    expmat (Function.update R i (w * R i * w⁻¹)) = expmat R := by
  funext k
  unfold expmat
  by_cases hk : k = i
  · subst hk; rw [upd_same', exAdd_conj]
  · rw [upd_other' _ (Ne.symm hk)]

/-- Conjugation changes the determinant not at all. -/
theorem detm_conj (R : Relators 2) (i : Fin 2) (w : Word 2) :
    detm (Function.update R i (w * R i * w⁻¹)) = detm R := by
  unfold detm
  rw [expmat_update_conj]

/-- One step preserves the absolute value of the determinant. -/
theorem detm_natAbs_step {A B : Relators 2} (h : Step A B) :
    (detm B).natAbs = (detm A).natAbs := by
  cases h with
  | inv i => rw [detm_inv A i]; simp
  | mulRight i j hij => rw [detm_mul A i j hij]
  | conj i w => rw [detm_conj A i w]

/-- The absolute value of the determinant is invariant along every path. -/
theorem detm_natAbs_invariant {R S : Relators 2} (h : Reachable R S) :
    (detm S).natAbs = (detm R).natAbs := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (detm_natAbs_step hstep).trans ih

/-- **The obstruction.** If the determinant is not plus or minus one then no
Andrews-Curtis path to the standard presentation exists, at any length. -/
theorem no_trivialisation_of_det (R : Relators 2) (h : (detm R).natAbs ≠ 1) :
    ¬ Reachable R (standard 2) := by
  intro hR
  have h1 := detm_natAbs_invariant hR
  rw [detm_standard] at h1
  simp only [Int.natAbs_one] at h1
  exact h h1.symm

end AC

#print axioms AC.exAdd_conj
#print axioms AC.exAdd_update_conj
#print axioms AC.detm_inv
#print axioms AC.detm_mul
#print axioms AC.detm_conj
#print axioms AC.detm_natAbs_invariant
#print axioms AC.no_trivialisation_of_det
