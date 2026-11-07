import AC

/-!
# Derived moves and the equivalence-relation structure of `AC.Reachable`

`AC.lean` proves that the ordinary conjecture implies the stable one, but two
facts it uses informally appear only in docstrings:

* "Every move can be undone by a finite sequence of moves, so `Reachable` is an
  equivalence relation."
* "Multiplication by inverse relators and relator permutations are derivable."

Neither is proved there.  The second is what makes the competition's *ordered*
target legitimate: the verifier demands exactly `(x, y)` in that order, which is
harmless only if inverse multiplication and relator order are derived moves.

This file proves the equivalence-relation part and the inverse-multiplication
part.  Everything is about `AC.Step` at arbitrary rank and uses no extra axioms.
-/

set_option autoImplicit false

namespace AC

variable {n : ℕ}

/-- Value of `Function.update` at the updated index. -/
theorem upd_self (f : Fin n → Word n) (i : Fin n) (v : Word n) :
    Function.update f i v i = v := by
  simp

/-- Value of `Function.update` away from the updated index. -/
theorem upd_other (f : Fin n → Word n) {i j : Fin n} (h : i ≠ j) (v : Word n) :
    Function.update f i v j = f j := by
  simp only [Function.update_apply]
  rw [if_neg]
  exact fun hji => h hji.symm

/-- A single `Step` can be undone by a finite sequence of moves.  Inversion and
conjugation are undone in one move.  Right multiplication needs three, because
the move set multiplies only by `R j` and not by `R j⁻¹`: invert `R j`,
multiply, invert it back. -/
theorem step_rev {R S : Relators n} (h : Step R S) : Reachable S R := by
  induction h with
  | inv i =>
      have key : Function.update (Function.update R i (R i)⁻¹) i
          ((Function.update R i (R i)⁻¹) i)⁻¹ = R := by
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [upd_other _ (Ne.symm hk)]
      have hh := Relation.ReflTransGen.single (Step.inv (Function.update R i (R i)⁻¹) i)
      rwa [key] at hh
  | mulRight a b hab =>
      set S : Relators n := Function.update R a (R a * R b) with hS
      set U : Relators n := Function.update S b (S b)⁻¹ with hU
      set V : Relators n := Function.update U a (U a * U b) with hV
      have hSa : S a = R a * R b := by simp [hS]
      have hSb : S b = R b := by simp [hS, upd_other _ hab]
      have hUa : U a = S a := by simp [hU, upd_other _ (Ne.symm hab)]
      have hUb : U b = (S b)⁻¹ := by simp [hU]
      have hVa : V a = U a * U b := by simp [hV]
      have hVb : V b = (S b)⁻¹ := by simp [hV, upd_other _ hab, hUb]
      have s1 : Step (Function.update R a (R a * R b)) U := Step.inv _ b
      have s2 : Step U V := Step.mulRight _ a b hab
      have s3 : Step V (Function.update V b (V b)⁻¹) := Step.inv _ b
      have key : Function.update V b (V b)⁻¹ = R := by
        funext k
        by_cases hka : k = a
        · subst hka
          rw [upd_other _ (Ne.symm hab), hVa, hUa, hUb, hSa, hSb, mul_assoc,
            mul_inv_cancel, mul_one]
        · by_cases hkb : k = b
          · subst hkb
            rw [upd_self, hVb, inv_inv, hSb]
          · rw [upd_other _ (Ne.symm hkb), hV, upd_other _ (Ne.symm hka), hU,
              upd_other _ (Ne.symm hkb), hS, upd_other _ (Ne.symm hka)]
      have hh := Relation.ReflTransGen.head s1
        (Relation.ReflTransGen.head s2 (Relation.ReflTransGen.single s3))
      rwa [key] at hh
  | conj i w =>
      have key : Function.update (Function.update R i (w * R i * w⁻¹)) i
          (w⁻¹ * (Function.update R i (w * R i * w⁻¹)) i * (w⁻¹)⁻¹) = R := by
        funext k
        by_cases hk : k = i
        · rw [hk]
          simp only [upd_self, inv_inv]
          simp [mul_assoc]
        · simp [upd_other _ (Ne.symm hk)]
      have hh := Relation.ReflTransGen.single
        (Step.conj (Function.update R i (w * R i * w⁻¹)) i w⁻¹)
      rwa [key] at hh

/-- `Reachable` is symmetric: the docstring claim that every move can be undone
by a finite sequence of moves. -/
theorem reachable_symm {R S : Relators n} (h : Reachable R S) : Reachable S R := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans (step_rev hstep) ih

/-- `Reachable` is transitive. -/
theorem reachable_trans {R S T : Relators n} (h₁ : Reachable R S) (h₂ : Reachable S T) :
    Reachable R T :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Reachability is an equivalence relation on balanced presentations of a fixed
rank.  `AC.lean` asserts this in a docstring; this is the proof. -/
theorem reachable_equivalence (n : ℕ) : Equivalence (@Reachable n) :=
  ⟨fun _ => Relation.ReflTransGen.refl, reachable_symm, reachable_trans⟩

/-- Multiplying a relator by the *inverse* of another relator is a derived move,
in three steps: invert the other relator, multiply, invert it back.  The
competition's move set needs this because its multiplication moves only offer
`R j`, never `R j⁻¹`. -/
theorem reachable_mul_inv (R : Relators n) {p q : Fin n} (hpq : p ≠ q) :
    Reachable R (Function.update R p (R p * (R q)⁻¹)) := by
  set A : Relators n := Function.update R q (R q)⁻¹ with hA
  set B : Relators n := Function.update A p (A p * A q) with hB
  have hAq : A q = (R q)⁻¹ := by simp [hA]
  have hAp : A p = R p := by simp [hA, upd_other _ (Ne.symm hpq)]
  have hBp : B p = R p * (R q)⁻¹ := by simp [hB, hAp, hAq]
  have hBq : B q = (R q)⁻¹ := by simp [hB, upd_other _ hpq, hAq]
  have s1 : Step R A := Step.inv R q
  have s2 : Step A B := Step.mulRight _ p q hpq
  have s3 : Step B (Function.update B q (B q)⁻¹) := Step.inv _ q
  have key : Function.update B q (B q)⁻¹ = Function.update R p (R p * (R q)⁻¹) := by
    funext k
    by_cases hkp : k = p
    · subst hkp
      rw [upd_other _ (Ne.symm hpq), upd_self, hBp]
    · by_cases hkq : k = q
      · subst hkq
        rw [upd_self, hBq, inv_inv]
        exact (upd_other _ hpq _).symm
      · rw [upd_other _ (Ne.symm hkq), hB, upd_other _ (Ne.symm hkp), hA,
          upd_other _ (Ne.symm hkq), upd_other _ (Ne.symm hkp)]
  have hh := Relation.ReflTransGen.head s1
    (Relation.ReflTransGen.head s2 (Relation.ReflTransGen.single s3))
  rw [key] at hh
  exact hh

end AC
