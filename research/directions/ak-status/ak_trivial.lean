/-
# The Akbulut-Kirby presentations present the trivial group

The Akbulut-Kirby family (Akbulut and Kirby, Topology 24 (1985) 375-390) is

  AK(n) = <x, y | x^n = y^(n+1), xyx = yxy>.

The paper states the case n = 4, with relators x^5 y^-4 and xyx y^-1 x^-1 y^-1,
and remarks that the same proof works for the family with x^(n+1) = y^n.  Here
the triviality is checked for every n at once, in Lean 4 with Mathlib only.

The proof is the published computation.  In the presented group put X = x and
Y = y.  From X Y X = Y X Y we get Y^-1 X Y = X Y X^-1, hence
Y^-1 X^n Y = X Y^n X^-1.  Since X^n = Y^(n+1), the left side is Y^(n+1), so
Y^(n+1) = X Y^n X^-1, and multiplying by X on both sides gives
Y^n = X^-1 X^n X = X^n = Y^(n+1), so Y = 1.  Then X Y X = Y X Y becomes
X X = X, so X = 1.

This is triviality of the presented group.  It is not Andrews-Curtis
triviality, and it says nothing about the Andrews-Curtis conjecture. -/
import Mathlib

open PresentedGroup

namespace AK

/-- The first generator x of the free group on two letters. -/
def X : FreeGroup (Fin 2) := FreeGroup.of 0

/-- The second generator y of the free group on two letters. -/
def Y : FreeGroup (Fin 2) := FreeGroup.of 1

/-- The relators of AK(n) = <x, y | x^n = y^(n+1), xyx = yxy>. -/
def akRels (n : ℕ) : Set (FreeGroup (Fin 2)) :=
  {X ^ n * (Y ^ (n + 1))⁻¹, X * Y * X * Y⁻¹ * X⁻¹ * Y⁻¹}

variable (n : ℕ)

/-- The image of x in the presented group AK(n). -/
def Xp : PresentedGroup (akRels n) := PresentedGroup.of (0 : Fin 2)

/-- The image of y in the presented group AK(n). -/
def Yp : PresentedGroup (akRels n) := PresentedGroup.of (1 : Fin 2)

theorem Xp_eq_mk : Xp n = PresentedGroup.mk (akRels n) X := rfl

theorem Yp_eq_mk : Yp n = PresentedGroup.mk (akRels n) Y := rfl

/-- x^n = y^(n+1) in the presented group. -/
theorem rel_pow : Xp n ^ n = Yp n ^ (n + 1) := by
  have hmem : X ^ n * (Y ^ (n + 1))⁻¹ ∈ akRels n := by simp [akRels]
  have hmk : PresentedGroup.mk (akRels n) (X ^ n * (Y ^ (n + 1))⁻¹) = 1 :=
    PresentedGroup.one_of_mem hmem
  rw [map_mul, map_inv, map_pow, map_pow] at hmk
  rw [Xp_eq_mk, Yp_eq_mk]
  exact eq_of_mul_inv_eq_one hmk

/-- xyx = yxy in the presented group. -/
theorem rel_conj : Xp n * Yp n * Xp n = Yp n * Xp n * Yp n := by
  have hmem : X * Y * X * Y⁻¹ * X⁻¹ * Y⁻¹ ∈ akRels n := by simp [akRels]
  have hmk : PresentedGroup.mk (akRels n) (X * Y * X * Y⁻¹ * X⁻¹ * Y⁻¹) = 1 :=
    PresentedGroup.one_of_mem hmem
  simp only [map_mul, map_inv, ← Xp_eq_mk, ← Yp_eq_mk] at hmk
  have h2 : Xp n * Yp n * Xp n * (Yp n * Xp n * Yp n)⁻¹ = 1 := by
    rw [mul_inv_rev, mul_inv_rev]
    simpa only [mul_assoc] using hmk
  exact mul_inv_eq_one.mp h2

/-- y^-1 x y = x y x^-1, the form of xyx = yxy used below. -/
theorem conj_rel : (Yp n)⁻¹ * Xp n * Yp n = Xp n * Yp n * (Xp n)⁻¹ := by
  have h := rel_conj n
  calc (Yp n)⁻¹ * Xp n * Yp n
      = (Yp n)⁻¹ * (Xp n * Yp n * Xp n) * (Xp n)⁻¹ := by group
    _ = (Yp n)⁻¹ * (Yp n * Xp n * Yp n) * (Xp n)⁻¹ := by rw [h]
    _ = Xp n * Yp n * (Xp n)⁻¹ := by group

/-- Powers of x are conjugated to powers of y. -/
theorem conj_pow_rel (k : ℕ) :
    (Yp n)⁻¹ * Xp n ^ k * Yp n = Xp n * Yp n ^ k * (Xp n)⁻¹ := by
  have hbase : (Yp n)⁻¹ * Xp n * Yp n = Xp n * Yp n * (Xp n)⁻¹ := conj_rel n
  induction k with
  | zero => simp
  | succ k ih =>
      calc (Yp n)⁻¹ * Xp n ^ (k + 1) * Yp n
          = ((Yp n)⁻¹ * Xp n ^ k * Yp n) * ((Yp n)⁻¹ * Xp n * Yp n) := by group
        _ = (Xp n * Yp n ^ k * (Xp n)⁻¹) * (Xp n * Yp n * (Xp n)⁻¹) := by rw [ih, hbase]
        _ = Xp n * Yp n ^ (k + 1) * (Xp n)⁻¹ := by group

/-- y^(n+1) = x y^n x^-1. -/
theorem key : Yp n ^ (n + 1) = Xp n * Yp n ^ n * (Xp n)⁻¹ := by
  have h := conj_pow_rel n n
  rw [rel_pow n] at h
  have hL : (Yp n)⁻¹ * Yp n ^ (n + 1) * Yp n = Yp n ^ (n + 1) := by group
  rw [hL] at h
  exact h

/-- y^n = x^n. -/
theorem pow_eq : Yp n ^ n = Xp n ^ n := by
  have h1 : Yp n ^ n = (Xp n)⁻¹ * Yp n ^ (n + 1) * Xp n := by
    calc Yp n ^ n = (Xp n)⁻¹ * (Xp n * Yp n ^ n * (Xp n)⁻¹) * Xp n := by group
      _ = (Xp n)⁻¹ * Yp n ^ (n + 1) * Xp n := by rw [← key n]
  have h2 : (Xp n)⁻¹ * Yp n ^ (n + 1) * Xp n = Xp n ^ n := by
    rw [← rel_pow n]
    group
  rw [h1, h2]

/-- y = 1 in the presented group. -/
theorem Yp_eq_one : Yp n = 1 := by
  have hEq : Yp n ^ n * Yp n = Yp n ^ n * 1 := by
    rw [← pow_succ, ← rel_pow n, ← pow_eq n, mul_one]
  exact mul_left_cancel hEq

/-- x = 1 in the presented group. -/
theorem Xp_eq_one : Xp n = 1 := by
  have h := rel_conj n
  rw [Yp_eq_one n] at h
  have h1 : Xp n * Xp n = 1 * Xp n := by simpa using h
  exact mul_right_cancel h1

/-- Every generator of the presented group AK(n) is the identity. -/
theorem of_eq_one (a : Fin 2) : (PresentedGroup.of (rels := akRels n) a) = 1 := by
  fin_cases a
  · exact Xp_eq_one n
  · exact Yp_eq_one n

/-- **The group presented by AK(n) is trivial, for every n.** -/
theorem ak_trivial : Subsingleton (PresentedGroup (akRels n)) := by
  refine ⟨fun x y => ?_⟩
  have hgen : ∀ j : Fin 2, (PresentedGroup.of (rels := akRels n) j) ∈ (⊥ : Subgroup _) :=
    fun j => by simpa using of_eq_one n j
  have hx : x = 1 := by
    have hmem := PresentedGroup.generated_by (akRels n) ⊥ hgen x
    simpa using hmem
  have hy : y = 1 := by
    have hmem := PresentedGroup.generated_by (akRels n) ⊥ hgen y
    simpa using hmem
  rw [hx, hy]

/-- Every element of the presented group AK(n) is the identity. -/
theorem ak_all_eq_one (a : PresentedGroup (akRels n)) : a = 1 :=
  (ak_trivial n).allEq a 1

end AK

#print axioms AK.rel_pow
#print axioms AK.rel_conj
#print axioms AK.conj_rel
#print axioms AK.conj_pow_rel
#print axioms AK.key
#print axioms AK.pow_eq
#print axioms AK.Yp_eq_one
#print axioms AK.Xp_eq_one
#print axioms AK.ak_trivial
#print axioms AK.ak_all_eq_one
#print axioms AK.of_eq_one
