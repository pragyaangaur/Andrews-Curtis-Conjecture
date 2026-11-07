/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Stabilization moves for presentations, and redundancy of the free-generator move

Companion file to `survey/stabilization-moves.md`.  The question there is
whether the two published definitions of "stably AC-equivalent" agree:

* Myasnikov, Myasnikov and Shpilrain, *On the Andrews-Curtis equivalence*,
  Contemp. Math. 296 (2002) 183-198, arXiv:math/0302080, moves (AC4)/(AC5);
* Shehper, Medina-Mardones, Fagan, Lewandowski, Gruen, Qiu and others,
  arXiv:2408.15332v2 section 2 and Fagan, Qiu and Wang, arXiv:2412.12293,
  moves (AC4)/(AC5).

Both (AC4) moves add a new generator together with the relator equal to that
generator, so the two relations are the same relation; the survey does the
reading of the sources.  What this file proves is the statement that decides
the opposite reading, the one that adds a *free* generator and no relator.
That move is not a Tietze move: it changes the deficiency and it changes the
presented group.  It is also redundant, in the following precise sense.

**Main theorem (`free_generator_redundant`).**  Let `T` and `T'` be tuples of
`m` words in the free group on `n` letters.  If `T` and `T'` become
AC-equivalent in the free group on `n + k` letters, where the `k` extra
letters are free in both tuples, then `T` and `T'` were already AC-equivalent
in the free group on `n` letters.

The proof is a retraction: the homomorphism `F_{n+k} -> F_n` that fixes the
first `n` letters and sends each of the `k` extra letters to `1` carries each
of the three AC moves to the same move on the image tuple, so it carries a
whole AC-derivation to an AC-derivation of the retracted tuples.

**Corollary (`acTrivial_of_free_generators`).**  A balanced presentation that
becomes AC-trivial after free generators are adjoined was already AC-trivial.
So adjoining free generators proves nothing about the Andrews-Curtis
conjecture, and the deficiency-changing move cannot be the stabilization move
of the two sources: their weak conjecture would collapse to the strong one.

Nothing here proves or disproves the Andrews-Curtis conjecture, and nothing
here is about the (AC4) move itself, which is balance-preserving.
-/

namespace Stabilization

/-- A tuple of `m` words in the free group on `n` generators.  The number of
relators `m` and the number of generators `n` are independent, so unbalanced
tuples are covered. -/
abbrev Tuple (m n : Nat) : Type := Fin m → FreeGroup (Fin n)

namespace Tuple

variable {m n n' : Nat}

/-! ## The three moves and AC-equivalence -/

/-- Replace the `i`-th entry of a tuple. -/
def setAt (T : Tuple m n) (i : Fin m) (v : FreeGroup (Fin n)) : Tuple m n :=
  fun k => if k = i then v else T k

@[simp] theorem setAt_self (T : Tuple m n) (i : Fin m) (v : FreeGroup (Fin n)) :
    setAt T i v i = v := by simp [setAt]

theorem setAt_of_ne (T : Tuple m n) {i k : Fin m} (h : k ≠ i) (v : FreeGroup (Fin n)) :
    setAt T i v k = T k := by simp [setAt, h]

/-- (AC1): invert the `i`-th relator. -/
def invertAt (T : Tuple m n) (i : Fin m) : Tuple m n := setAt T i (T i)⁻¹

/-- (AC2): multiply the `i`-th relator on the right by the `j`-th. -/
def mulAt (T : Tuple m n) (i j : Fin m) : Tuple m n := setAt T i (T i * T j)

/-- (AC3): conjugate the `i`-th relator by an arbitrary word. -/
def conjAt (T : Tuple m n) (i : Fin m) (w : FreeGroup (Fin n)) : Tuple m n :=
  setAt T i (w * T i * w⁻¹)

/-- One elementary AC move on relator tuples. -/
inductive Move : Tuple m n → Tuple m n → Prop where
  | invert (i : Fin m) (T : Tuple m n) : Move T (invertAt T i)
  | mul (i j : Fin m) (h : i ≠ j) (T : Tuple m n) : Move T (mulAt T i j)
  | conj (i : Fin m) (w : FreeGroup (Fin n)) (T : Tuple m n) : Move T (conjAt T i w)

/-- AC-equivalence: the reflexive transitive closure of the three moves. -/
def Equiv (T T' : Tuple m n) : Prop := Relation.ReflTransGen Move T T'

theorem Equiv.refl (T : Tuple m n) : Equiv T T := Relation.ReflTransGen.refl

theorem Equiv.step {T T' : Tuple m n} (h : Move T T') : Equiv T T' :=
  Relation.ReflTransGen.single h

theorem Equiv.trans {T T' T'' : Tuple m n} (h₁ : Equiv T T') (h₂ : Equiv T' T'') :
    Equiv T T'' := Relation.ReflTransGen.trans h₁ h₂

/-! ## A homomorphism acts on tuples -/

/-- Apply a homomorphism of free groups to every entry of a tuple. -/
def map (φ : FreeGroup (Fin n) →* FreeGroup (Fin n')) (T : Tuple m n) : Tuple m n' :=
  fun k => φ (T k)

theorem map_setAt (φ : FreeGroup (Fin n) →* FreeGroup (Fin n')) (T : Tuple m n)
    (i : Fin m) (v : FreeGroup (Fin n)) :
    map φ (setAt T i v) = setAt (map φ T) i (φ v) := by
  funext k
  by_cases h : k = i <;> simp [map, setAt, h]

theorem map_invertAt (φ : FreeGroup (Fin n) →* FreeGroup (Fin n')) (T : Tuple m n)
    (i : Fin m) : map φ (invertAt T i) = invertAt (map φ T) i := by
  simp [invertAt, map_setAt, map]

theorem map_mulAt (φ : FreeGroup (Fin n) →* FreeGroup (Fin n')) (T : Tuple m n)
    (i j : Fin m) : map φ (mulAt T i j) = mulAt (map φ T) i j := by
  simp [mulAt, map_setAt, map]

theorem map_conjAt (φ : FreeGroup (Fin n) →* FreeGroup (Fin n')) (T : Tuple m n)
    (i : Fin m) (w : FreeGroup (Fin n)) :
    map φ (conjAt T i w) = conjAt (map φ T) i (φ w) := by
  simp [conjAt, map_setAt, map]

/-- A homomorphism carries each elementary move to an elementary move of the
same type on the image tuple.  This is the step that makes the retraction
argument work: the conjugating word is mapped along with the relators. -/
theorem move_map (φ : FreeGroup (Fin n) →* FreeGroup (Fin n')) {T T' : Tuple m n}
    (h : Move T T') : Move (map φ T) (map φ T') := by
  cases h with
  | invert i T => simpa [map_invertAt] using Move.invert i (map φ T)
  | mul i j hij T => simpa [map_mulAt] using Move.mul i j hij (map φ T)
  | conj i w T => simpa [map_conjAt] using Move.conj i (φ w) (map φ T)

/-- A homomorphism carries an AC-equivalence to an AC-equivalence of the
image tuples. -/
theorem equiv_map (φ : FreeGroup (Fin n) →* FreeGroup (Fin n')) {T T' : Tuple m n}
    (h : Equiv T T') : Equiv (map φ T) (map φ T') := by
  induction h with
  | refl => exact Equiv.refl _
  | tail _ hmv ih => exact Relation.ReflTransGen.tail ih (move_map φ hmv)

/-! ## The inclusion of the first `n` letters and its retraction -/

/-- The inclusion `F_n -> F_{n+k}` of free groups. -/
def incl (n k : Nat) : FreeGroup (Fin n) →* FreeGroup (Fin (n + k)) :=
  FreeGroup.lift fun i => FreeGroup.of (Fin.castLE (Nat.le_add_right n k) i)

/-- The retraction `F_{n+k} -> F_n` that fixes the first `n` letters and sends
each of the `k` extra letters to `1`. -/
def retr (n k : Nat) : FreeGroup (Fin (n + k)) →* FreeGroup (Fin n) :=
  FreeGroup.lift fun i => if h : (i : Nat) < n then FreeGroup.of ⟨(i : Nat), h⟩ else 1

theorem incl_apply (n k : Nat) (i : Fin n) :
    incl n k (FreeGroup.of i) = FreeGroup.of (Fin.castLE (Nat.le_add_right n k) i) :=
  FreeGroup.lift_apply_of

theorem retr_incl_apply (n k : Nat) (x : FreeGroup (Fin n)) : retr n k (incl n k x) = x := by
  have hcomp : (retr n k).comp (incl n k) = MonoidHom.id (FreeGroup (Fin n)) := by
    refine FreeGroup.ext_hom _ _ (fun i => ?_)
    simp [incl, retr, Fin.val_castLE]
  exact DFunLike.congr_fun hcomp x

/-! ## The main theorem -/

/-- **Adjoining free generators does not change AC-equivalence.**  If two
tuples of `m` words in `F_n` become AC-equivalent after `k` free generators
are adjoined, they were already AC-equivalent. -/
theorem free_generator_redundant {T T' : Tuple m n}
    (h : Equiv (map (incl n k) T) (map (incl n k) T')) : Equiv T T' := by
  have h₂ := equiv_map (retr n k) h
  have e₁ : map (retr n k) (map (incl n k) T) = T := by
    funext i; exact retr_incl_apply n k (T i)
  have e₂ : map (retr n k) (map (incl n k) T') = T' := by
    funext i; exact retr_incl_apply n k (T' i)
  rwa [e₁, e₂] at h₂

/-- The standard balanced tuple `(x_1, ..., x_n)`. -/
def standard (n : Nat) : Tuple n n := fun i => FreeGroup.of i

/-- **Corollary.**  A balanced presentation that becomes AC-trivial after `k`
free generators are adjoined was already AC-trivial.  Consequently the
deficiency-changing stabilization move adds nothing to the AC move set, and
it is not the move that the 2002 and 2024 sources call (AC4). -/
theorem acTrivial_of_free_generators {n k : Nat} (P : Tuple n n)
    (h : Equiv (map (incl n k) P) (map (incl n k) (standard n))) :
    Equiv P (standard n) :=
  free_generator_redundant h

/-- The same statement with the hypothesis and the conclusion in the other
order, for comparison with the statement of the stable conjecture. -/
theorem not_acTrivial_of_free_generators {n k : Nat} (P : Tuple n n)
    (h : ¬ Equiv P (standard n)) :
    ¬ Equiv (map (incl n k) P) (map (incl n k) (standard n)) :=
  fun hh => h (free_generator_redundant hh)

end Tuple

end Stabilization

/-! ## Axiom audit -/

#print axioms Stabilization.Tuple.equiv_map
#print axioms Stabilization.Tuple.retr_incl_apply
#print axioms Stabilization.Tuple.free_generator_redundant
#print axioms Stabilization.Tuple.acTrivial_of_free_generators
#print axioms Stabilization.Tuple.not_acTrivial_of_free_generators
