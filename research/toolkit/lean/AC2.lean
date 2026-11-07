/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Andrews-Curtis moves, part 2: normal closure, letter deletion, and two class theorems

This file continues `toolkit/lean/AC.lean`.  It is deliberately self-contained: it imports
only `Mathlib` and repeats the definitions of `AC.lean` that it needs, so that it can be
checked with a single `lean toolkit/lean/AC2.lean` from the repository root, with no
`LEAN_PATH` adjustment and no build step.  The definitions of `Word`, `Presentation`,
`setAt`, `invertAt`, `conjAt`, `mulAt`, `mulInvAt`, `ACMove`, `ACEquiv`, `standard` and the
lemmas `ACEquiv.symm`, `ACEquiv.mulInv`, `ACEquiv.mulLeft` are copied verbatim from
`AC.lean`; everything below them is new.

## What is proved here

* **(a) The normal closure of the relator tuple is an AC-invariant.**  For each of the three
  moves, and hence for every AC-equivalence, the normal closure in `F_n` of the relator tuple
  is unchanged (`nclRange_*`, `nclRange_eq_of_acEquiv`).  Consequently AC-equivalent
  presentations present the same group (`presentedGroup_mulEquiv_of_acEquiv`), and in
  particular the triviality of `PresentedGroup (Set.range P)` is an AC-invariant
  (`presentedGroup_subsingleton_iff`).  This is the engine of Lemma 1 of
  `survey/invariants.md`, and the only consequence of (a) that the rest of the file uses.

* **The letter-deletion lemma.**  If the tuple has a relator which is a signed generator `x`
  (or `x^-1`) at a position other than `i`, then any word at position `i` can be stripped of
  all its `x`-letters by AC moves that touch only position `i` (`delete_letter_gen`,
  `delete_letters`).  The deletion step is three moves; no freeness hypothesis on the rest of
  the word is needed, because the step works at an arbitrary occurrence of the letter.  The
  bookkeeping is on lists, so the length of the word drops by exactly one at each step and the
  induction terminates.  This is Lemma 5 of `survey/special-classes.md` in the form the two
  class theorems need, and it is also the deletion step of Lemma 8 of
  `survey/q-transformations.md`.

* **Interchange and sign fixing.**  Two entries can be exchanged in seven moves
  (`acEquiv_swap`, Lemma 2 of `survey/special-classes.md`), and a tuple whose relators are the
  generators up to sign is AC-standard at a cost of one move per negative sign
  (`acEquiv_standard_of_signs`, `acEquiv_standard_of_signed`).

* **(b) Corollary 7 of `survey/special-classes.md`.**  A balanced rank-two presentation of the
  trivial group with a relator conjugate to a generator or to the inverse of a generator is
  AC-equivalent to the standard tuple `(x, y)` (`acEquiv_standard_of_conj_generator`).

* **(c) Lemma 8 of `survey/q-transformations.md`, in the AC form.**  If the relators at all
  positions other than `i` are the generators `x_j` up to sign and the presentation is of the
  trivial group, then the tuple is AC-equivalent to the standard tuple `(x_1, ..., x_n)`
  (`acEquiv_standard_of_generator_relators`).  The survey states this for Q-equivalence; the
  proof there uses only conjugations and multiplications by relators, so it is an AC proof, and
  this file formalizes the AC statement.  The version in which the generator relators occur in
  a permuted order needs the interchange lemma once per inversion and is not formalized here.

Neither (b) nor (c) is a step towards the Andrews-Curtis conjecture itself: both hypotheses
force the presentation to be AC-standard for a reason (one relator is a conjugate of a
generator, or all but one relator are generators) which is exactly the configuration the
conjecture denies for its own hard cases.  Nothing here bears on the truth of the conjecture.

## Ledger: what is not formalized

* Theorem 6 of `survey/special-classes.md` is formalized only in the form (b) needs.  The
  converse implication (AC-standard forces the retracted tuple to be AC-standard) is not.
* Lemma 8 with the generator relators in a permuted order: not formalized (see above).
* The passage from Q-equivalence to AC-equivalence: not needed, since the AC form is proved
  directly.
* Nothing about AK(n) or about any particular candidate counterexample is formalized here.

## Conventions

* `Word n = FreeGroup (Fin n)`, `Presentation n = Fin n → Word n`.
* A presentation is a relator tuple; `PresentedGroup (Set.range P)` is the group it presents,
  and `Subsingleton (PresentedGroup (Set.range P))` is the statement that this group is
  trivial.
* Move counts quoted in docstrings count elementary moves; the one derived move used,
  `ACEquiv.mulInv` (multiply a relator by the inverse of another), costs three elementary
  moves.
-/

namespace AndrewsCurtis

/-! ## Words, presentations, and replacement of one relator -/

/-- A word in the free group on `n` generators. -/
abbrev Word (n : Nat) : Type := FreeGroup (Fin n)

/-- A rank-`n` presentation: `n` relators in the free group on `n` letters. -/
abbrev Presentation (n : Nat) : Type := Fin n → Word n

/-- The relator tuple as an honest list. -/
def Presentation.toList {n : Nat} (P : Presentation n) : List (Word n) := List.ofFn P

/-- A rank-`n` presentation has exactly `n` relators. -/
theorem Presentation.length_toList {n : Nat} (P : Presentation n) : P.toList.length = n :=
  List.length_ofFn

/-- Replace the `i`-th relator by `v`. -/
def setAt {n : Nat} (P : Presentation n) (i : Fin n) (v : Word n) : Presentation n :=
  fun k => if k = i then v else P k

theorem setAt_apply {n : Nat} (P : Presentation n) (i k : Fin n) (v : Word n) :
    setAt P i v k = if k = i then v else P k := rfl

theorem setAt_self {n : Nat} (P : Presentation n) (i : Fin n) (v : Word n) :
    setAt P i v i = v := by simp [setAt]

theorem setAt_of_ne {n : Nat} (P : Presentation n) {i : Fin n} (v : Word n) {k : Fin n}
    (h : k ≠ i) : setAt P i v k = P k := by simp [setAt, h]

/-- Invert the `i`-th relator: AC move (1). -/
def invertAt {n : Nat} (P : Presentation n) (i : Fin n) : Presentation n :=
  setAt P i (P i)⁻¹

/-- Conjugate the `i`-th relator by `w`: AC move (3). -/
def conjAt {n : Nat} (P : Presentation n) (i : Fin n) (w : Word n) : Presentation n :=
  setAt P i (w * P i * w⁻¹)

/-- Multiply the `i`-th relator on the right by the `j`-th relator: AC move (2). -/
def mulAt {n : Nat} (P : Presentation n) (i j : Fin n) : Presentation n :=
  setAt P i (P i * P j)

/-- Multiply the `i`-th relator on the right by the inverse of the `j`-th relator.
This is not one of the three moves; it is a derived move, three moves long. -/
def mulInvAt {n : Nat} (P : Presentation n) (i j : Fin n) : Presentation n :=
  setAt P i (P i * (P j)⁻¹)

/-! ## The moves and AC-equivalence -/

variable {n : Nat}

/-- The three Andrews-Curtis moves on relator tuples of rank `n`. -/
inductive ACMove : Presentation n → Presentation n → Prop where
  | invert (i : Fin n) (P : Presentation n) : ACMove P (invertAt P i)
  | mul (i j : Fin n) (h : i ≠ j) (P : Presentation n) : ACMove P (mulAt P i j)
  | conj (i : Fin n) (w : Word n) (P : Presentation n) : ACMove P (conjAt P i w)

/-- Andrews-Curtis equivalence: the reflexive transitive closure of `ACMove`. -/
def ACEquiv (P Q : Presentation n) : Prop := Relation.ReflTransGen ACMove P Q

theorem ACEquiv.refl (P : Presentation n) : ACEquiv P P := Relation.ReflTransGen.refl

theorem ACEquiv.trans {P Q R : Presentation n} (h₁ : ACEquiv P Q) (h₂ : ACEquiv Q R) :
    ACEquiv P R := Relation.ReflTransGen.trans h₁ h₂

theorem ACEquiv.of_move {P Q : Presentation n} (h : ACMove P Q) : ACEquiv P Q :=
  Relation.ReflTransGen.single h

/-! ## Each move is undone by a short sequence of moves -/

/-- Inverting twice restores the tuple. -/
theorem invertAt_involutive {n : Nat} (P : Presentation n) (i : Fin n) :
    invertAt (invertAt P i) i = P := by
  funext k
  by_cases hk : k = i
  · rw [hk]
    simp [invertAt, setAt]
  · simp [invertAt, setAt, hk]

/-- Conjugating by `w` and then by `w⁻¹` restores the tuple. -/
theorem conjAt_undo {n : Nat} (P : Presentation n) (i : Fin n) (w : Word n) :
    conjAt (conjAt P i w) i w⁻¹ = P := by
  funext k
  by_cases hk : k = i
  · rw [hk]
    simp only [conjAt, setAt]
    simp
    group
  · simp [conjAt, setAt, hk]

/-- Multiplying the `i`-th relator by the inverse of the `j`-th relator undoes
multiplication by the `j`-th relator. -/
theorem mulInvAt_mulAt {n : Nat} {i j : Fin n} (h : i ≠ j) (P : Presentation n) :
    mulInvAt (mulAt P i j) i j = P := by
  funext k
  by_cases hk : k = i
  · rw [hk]
    simp only [mulInvAt, mulAt, setAt]
    simp_all [Ne.symm h]
  · by_cases hk' : k = j
    · rw [hk']
      simp only [mulInvAt, mulAt, setAt]
      simp_all
    · simp only [mulInvAt, mulAt, setAt]
      simp_all

/-- Three moves carry `P` to `mulInvAt P i j`: invert `j`, multiply `i` by `j`,
invert `j` again. -/
theorem invertAt_mulAt_invertAt {n : Nat} {i j : Fin n} (h : i ≠ j) (P : Presentation n) :
    invertAt (mulAt (invertAt P j) i j) j = mulInvAt P i j := by
  funext k
  by_cases hk : k = j
  · rw [hk]
    simp only [invertAt, mulAt, mulInvAt, setAt]
    simp_all [Ne.symm h]
  · by_cases hk' : k = i
    · rw [hk']
      simp only [invertAt, mulAt, mulInvAt, setAt]
      simp_all
    · simp only [invertAt, mulAt, mulInvAt, setAt]
      simp_all

/-- Every AC move is reversed by a sequence of at most three AC moves. -/
theorem ACMove.toEquiv {P Q : Presentation n} (h : ACMove P Q) : ACEquiv Q P := by
  induction h with
  | invert i P =>
      have h2 : ACMove (invertAt P i) (invertAt (invertAt P i) i) :=
        ACMove.invert i (invertAt P i)
      rw [invertAt_involutive] at h2
      exact Relation.ReflTransGen.single h2
  | conj i w P =>
      have h2 : ACMove (conjAt P i w) (conjAt (conjAt P i w) i w⁻¹) :=
        ACMove.conj i w⁻¹ (conjAt P i w)
      rw [conjAt_undo] at h2
      exact Relation.ReflTransGen.single h2
  | mul i j hij P =>
      have s1 : ACMove (mulAt P i j) (invertAt (mulAt P i j) j) :=
        ACMove.invert j (mulAt P i j)
      have s2 : ACMove (invertAt (mulAt P i j) j) (mulAt (invertAt (mulAt P i j) j) i j) :=
        ACMove.mul i j hij (invertAt (mulAt P i j) j)
      have s3 : ACMove (mulAt (invertAt (mulAt P i j) j) i j)
          (invertAt (mulAt (invertAt (mulAt P i j) j) i j) j) :=
        ACMove.invert j (mulAt (invertAt (mulAt P i j) j) i j)
      have heq : invertAt (mulAt (invertAt (mulAt P i j) j) i j) j = P := by
        rw [invertAt_mulAt_invertAt hij, mulInvAt_mulAt hij]
      rw [heq] at s3
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single s1)
        (Relation.ReflTransGen.trans (Relation.ReflTransGen.single s2)
          (Relation.ReflTransGen.single s3))

/-- AC-equivalence is symmetric. -/
theorem ACEquiv.symm {P Q : Presentation n} (h : ACEquiv P Q) : ACEquiv Q P := by
  induction h with
  | refl => exact ACEquiv.refl P
  | tail _ hstep ih => exact ACEquiv.trans (ACMove.toEquiv hstep) ih

/-- The derived move: multiply the `i`-th relator by the inverse of the `j`-th relator. -/
theorem ACEquiv.mulInv {n : Nat} {i j : Fin n} (h : i ≠ j) (P : Presentation n) :
    ACEquiv P (mulInvAt P i j) := by
  have s1 : ACEquiv P (invertAt P j) := Relation.ReflTransGen.single (ACMove.invert j P)
  have s2 : ACEquiv (invertAt P j) (mulAt (invertAt P j) i j) :=
    Relation.ReflTransGen.single (ACMove.mul i j h (invertAt P j))
  have s3 : ACEquiv (mulAt (invertAt P j) i j) (invertAt (mulAt (invertAt P j) i j) j) :=
    Relation.ReflTransGen.single (ACMove.invert j (mulAt (invertAt P j) i j))
  rw [invertAt_mulAt_invertAt h] at s3
  exact ACEquiv.trans s1 (ACEquiv.trans s2 s3)

/-! ## Two concrete presentations -/

/-- The standard balanced presentation of the trivial group at rank `n`:
the relators are the generators. -/
def standard (n : Nat) : Presentation n := fun i => FreeGroup.of i
/-! ## A derived move: left multiplication by another relator -/

/-- Left multiplication by another relator is available: conjugate `r i` by `r j` and
then multiply by `r j` on the right. -/
theorem ACEquiv.mulLeft {n : Nat} {i j : Fin n} (h : i ≠ j) (P : Presentation n) :
    ACEquiv P (setAt P i (P j * P i)) := by
  have s1 : ACEquiv P (conjAt P i (P j)) :=
    Relation.ReflTransGen.single (ACMove.conj i (P j) P)
  have s2 : ACEquiv (conjAt P i (P j)) (mulAt (conjAt P i (P j)) i j) :=
    Relation.ReflTransGen.single (ACMove.mul i j h (conjAt P i (P j)))
  have heq : mulAt (conjAt P i (P j)) i j = setAt P i (P j * P i) := by
    funext k
    by_cases hk : k = i
    · rw [hk]
      simp only [mulAt, conjAt, setAt]
      simp_all
    · simp only [mulAt, conjAt, setAt]
      simp_all
  rw [heq] at s2
  exact ACEquiv.trans s1 s2

/-! ## (a) The normal closure of the relator tuple is an AC-invariant -/

/-- The normal closure in `F_n` of the relator tuple `P`.  By definition
`PresentedGroup (Set.range P)` is the quotient of `F_n` by this subgroup, so two tuples with
the same `nclRange` present the same group. -/
def nclRange {n : Nat} (P : Presentation n) : Subgroup (Word n) :=
  Subgroup.normalClosure (Set.range P)

theorem nclRange_normal {n : Nat} (P : Presentation n) : (nclRange P).Normal :=
  Subgroup.normalClosure_normal

attribute [local instance] nclRange_normal

/-- Every relator belongs to the normal closure of the relators. -/
theorem mem_nclRange {n : Nat} (P : Presentation n) (k : Fin n) : P k ∈ nclRange P :=
  Subgroup.subset_normalClosure ⟨k, rfl⟩

/-- Move 1 does not enlarge the normal closure. -/
theorem nclRange_invertAt_le {n : Nat} (P : Presentation n) (i : Fin n) :
    nclRange (invertAt P i) ≤ nclRange P := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨k, rfl⟩
  by_cases hk : k = i
  · have hmem : (P i)⁻¹ ∈ nclRange P := Subgroup.inv_mem (nclRange P) (mem_nclRange P i)
    simpa [invertAt, setAt, hk] using hmem
  · simpa [invertAt, setAt, hk] using mem_nclRange P k

/-- Move 1 does not change the normal closure. -/
theorem nclRange_invertAt {n : Nat} (P : Presentation n) (i : Fin n) :
    nclRange (invertAt P i) = nclRange P := by
  refine le_antisymm (nclRange_invertAt_le P i) ?_
  have h := nclRange_invertAt_le (invertAt P i) i
  rwa [invertAt_involutive] at h

/-- Move 3 does not enlarge the normal closure. -/
theorem nclRange_conjAt_le {n : Nat} (P : Presentation n) (i : Fin n) (w : Word n) :
    nclRange (conjAt P i w) ≤ nclRange P := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨k, rfl⟩
  by_cases hk : k = i
  · have hmem : P i ∈ nclRange P := mem_nclRange P i
    have hconj : w * P i * w⁻¹ ∈ nclRange P :=
      (Subgroup.normalClosure_normal (s := Set.range P)).conj_mem (P i) hmem w
    simpa [conjAt, setAt, hk] using hconj
  · simpa [conjAt, setAt, hk] using mem_nclRange P k

/-- Move 3 does not change the normal closure: a conjugate of a relator generates the same
normal closure as the relator. -/
theorem nclRange_conjAt {n : Nat} (P : Presentation n) (i : Fin n) (w : Word n) :
    nclRange (conjAt P i w) = nclRange P := by
  refine le_antisymm (nclRange_conjAt_le P i w) ?_
  have h := nclRange_conjAt_le (conjAt P i w) i w⁻¹
  rwa [conjAt_undo] at h

/-- Move 2 does not enlarge the normal closure. -/
theorem nclRange_mulAt_le {n : Nat} (P : Presentation n) {i j : Fin n} (h : i ≠ j) :
    nclRange (mulAt P i j) ≤ nclRange P := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨k, rfl⟩
  by_cases hk : k = i
  · have hprod : P i * P j ∈ nclRange P :=
      Subgroup.mul_mem _ (mem_nclRange P i) (mem_nclRange P j)
    simpa [mulAt, setAt, hk] using hprod
  · simpa [mulAt, setAt, hk] using mem_nclRange P k

/-- Move 2 does not change the normal closure: `P i` can be recovered from `P i * P j` and
`P j`. -/
theorem nclRange_mulAt {n : Nat} (P : Presentation n) {i j : Fin n} (h : i ≠ j) :
    nclRange (mulAt P i j) = nclRange P := by
  refine le_antisymm (nclRange_mulAt_le P h) ?_
  have hQi : P i * P j ∈ nclRange (mulAt P i j) := by
    have := mem_nclRange (mulAt P i j) i
    simpa [mulAt, setAt] using this
  have hQj : P j ∈ nclRange (mulAt P i j) := by
    have := mem_nclRange (mulAt P i j) j
    simpa [mulAt, setAt, h, Ne.symm h] using this
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨k, rfl⟩
  by_cases hk : k = i
  · have hrec : (P i * P j) * (P j)⁻¹ ∈ nclRange (mulAt P i j) :=
      Subgroup.mul_mem _ hQi (Subgroup.inv_mem _ hQj)
    simpa [hk] using hrec
  · have := mem_nclRange (mulAt P i j) k
    simpa [mulAt, setAt, hk] using this

/-- Every AC move preserves the normal closure of the relator tuple. -/
theorem nclRange_eq_of_acMove {n : Nat} {P Q : Presentation n} (h : ACMove P Q) :
    nclRange P = nclRange Q := by
  induction h with
  | invert i P => exact (nclRange_invertAt P i).symm
  | mul i j hij P => exact (nclRange_mulAt P hij).symm
  | conj i w P => exact (nclRange_conjAt P i w).symm

/-- The normal closure of the relator tuple is an invariant of AC-equivalence. -/
theorem nclRange_eq_of_acEquiv {n : Nat} {P Q : Presentation n} (h : ACEquiv P Q) :
    nclRange P = nclRange Q := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (nclRange_eq_of_acMove hstep)

/-- AC-equivalent presentations present the same group. -/
noncomputable def presentedGroup_mulEquiv_of_acEquiv {n : Nat} {P Q : Presentation n}
    (h : ACEquiv P Q) :
    PresentedGroup (Set.range P) ≃* PresentedGroup (Set.range Q) := by
  have h2 : nclRange P = nclRange Q := nclRange_eq_of_acEquiv h
  have h3 : Subgroup.normalClosure (Set.range P) = Subgroup.normalClosure (Set.range Q) := h2
  exact QuotientGroup.quotientMulEquivOfEq h3

/-- Triviality of the presented group is an AC-invariant.  This is the only consequence of
part (a) that the rest of this file uses. -/
theorem presentedGroup_subsingleton_iff {n : Nat} {P Q : Presentation n} (h : ACEquiv P Q) :
    Subsingleton (PresentedGroup (Set.range P)) ↔
      Subsingleton (PresentedGroup (Set.range Q)) := by
  have h2 : nclRange P = nclRange Q := nclRange_eq_of_acEquiv h
  have h3 : Subgroup.normalClosure (Set.range P) = Subgroup.normalClosure (Set.range Q) := h2
  show Subsingleton (FreeGroup (Fin n) ⧸ Subgroup.normalClosure (Set.range P)) ↔
    Subsingleton (FreeGroup (Fin n) ⧸ Subgroup.normalClosure (Set.range Q))
  rw [h3]

/-! ## Letter deletion -/

/-- Writing the same value twice at the same position: only the second survives. -/
theorem setAt_setAt {n : Nat} (P : Presentation n) (i : Fin n) (v v' : Word n) :
    setAt (setAt P i v) i v' = setAt P i v' := by
  funext k
  by_cases hk : k = i <;> simp [setAt, hk]

/-- The one-letter list spells the generator or its inverse. -/
theorem mk_singleton {n : Nat} (i : Fin n) (b : Bool) :
    FreeGroup.mk [(i, b)] = if b then FreeGroup.of i else (FreeGroup.of i)⁻¹ := by
  cases b
  · show FreeGroup.mk [(i, false)] = (FreeGroup.mk [(i, true)])⁻¹
    rw [FreeGroup.inv_mk]
    simp [FreeGroup.invRev]
  · rfl

/-- The subgroup of words in which only generators other than `a` occur. -/
def freeOf {n : Nat} (a : Fin n) : Subgroup (Word n) :=
  Subgroup.closure (Set.range fun i : {i : Fin n // i ≠ a} => FreeGroup.of i.1)

/-- A generator other than `a` lies in `freeOf a`. -/
theorem of_mem_freeOf {n : Nat} {a i : Fin n} (h : i ≠ a) : FreeGroup.of i ∈ freeOf a :=
  Subgroup.subset_closure ⟨⟨i, h⟩, rfl⟩

/-- A word built from letters other than `a` lies in `freeOf a`. -/
theorem mk_mem_freeOf {n : Nat} {a : Fin n} :
    ∀ {l : List (Fin n × Bool)}, (∀ p ∈ l, p.1 ≠ a) → FreeGroup.mk l ∈ freeOf a := by
  intro l
  induction l with
  | nil => intro _; exact Subgroup.one_mem _
  | cons x t ih =>
      intro h
      obtain ⟨i, b⟩ := x
      have hi : i ≠ a := h (i, b) (List.mem_cons_self ..)
      have ht : ∀ p ∈ t, p.1 ≠ a := fun p hp => h p (List.mem_cons_of_mem _ hp)
      have hsplit : FreeGroup.mk ((i, b) :: t) = FreeGroup.mk [(i, b)] * FreeGroup.mk t := by
        rw [FreeGroup.mul_mk]
        rfl
      rw [hsplit]
      refine Subgroup.mul_mem _ ?_ (ih ht)
      rw [mk_singleton]
      cases b
      · exact Subgroup.inv_mem _ (of_mem_freeOf hi)
      · exact of_mem_freeOf hi

/-! ### The three-move deletion step

The step needs no hypothesis on the two words `u` and `v`: the letter is deleted wherever it
occurs. -/

/-- Deletion step in general form.  Let the tuple have `h = P a0` at position `a0 ≠ i`, and
let the word at position `i` be `u * x * v` where `x` is `h` or `h⁻¹` (so `x` is a signed
generator).  Three AC moves, all of them touching only position `i`, carry `u x v` to `v u`.
No hypothesis is made on `u` and `v`. -/
theorem delete_letter_gen {n : Nat} (P : Presentation n) {a0 i : Fin n} (hne : a0 ≠ i)
    (u v : Word n) {x : Word n} (hx : x = P a0 ∨ x = (P a0)⁻¹) :
    ACEquiv (setAt P i (u * x * v)) (setAt P i (v * u)) := by
  rcases hx with rfl | rfl
  · -- the letter is the helper relator itself
    have hconj1 : conjAt (setAt P i (u * P a0 * v)) i u⁻¹
        = setAt P i (P a0 * v * u) := by
      rw [conjAt, setAt_setAt, setAt_self, inv_inv]
      congr 1
      group
    have hmul : mulInvAt (setAt P i (P a0 * v * u)) i a0
        = setAt P i (P a0 * v * u * (P a0)⁻¹) := by
      rw [mulInvAt, setAt_setAt, setAt_self]
      simp [setAt_of_ne (P := P) (i := i) (v := _) (k := a0) hne]
    have hconj2 : conjAt (setAt P i (P a0 * v * u * (P a0)⁻¹)) i (P a0)⁻¹
        = setAt P i (v * u) := by
      rw [conjAt, setAt_setAt, setAt_self, inv_inv]
      congr 1
      group
    have s1 : ACEquiv (setAt P i (u * P a0 * v)) (setAt P i (P a0 * v * u)) := by
      rw [← hconj1]
      exact ACEquiv.of_move (ACMove.conj i u⁻¹ _)
    have s2 : ACEquiv (setAt P i (P a0 * v * u))
        (setAt P i (P a0 * v * u * (P a0)⁻¹)) := by
      rw [← hmul]
      exact ACEquiv.mulInv (Ne.symm hne) _
    have s3 : ACEquiv (setAt P i (P a0 * v * u * (P a0)⁻¹)) (setAt P i (v * u)) := by
      rw [← hconj2]
      exact ACEquiv.of_move (ACMove.conj i (P a0)⁻¹ _)
    exact s1.trans (s2.trans s3)
  · -- the letter is the inverse of the helper relator
    have hconj1 : conjAt (setAt P i (u * (P a0)⁻¹ * v)) i u⁻¹
        = setAt P i ((P a0)⁻¹ * v * u) := by
      rw [conjAt, setAt_setAt, setAt_self, inv_inv]
      congr 1
      group
    have hmul : mulAt (setAt P i ((P a0)⁻¹ * v * u)) i a0
        = setAt P i ((P a0)⁻¹ * v * u * P a0) := by
      rw [mulAt, setAt_setAt, setAt_self]
      simp [setAt_of_ne (P := P) (i := i) (v := _) (k := a0) hne]
    have hconj2 : conjAt (setAt P i ((P a0)⁻¹ * v * u * P a0)) i (P a0)
        = setAt P i (v * u) := by
      rw [conjAt, setAt_setAt, setAt_self]
      congr 1
      group
    have s1 : ACEquiv (setAt P i (u * (P a0)⁻¹ * v)) (setAt P i ((P a0)⁻¹ * v * u)) := by
      rw [← hconj1]
      exact ACEquiv.of_move (ACMove.conj i u⁻¹ _)
    have s2 : ACEquiv (setAt P i ((P a0)⁻¹ * v * u))
        (setAt P i ((P a0)⁻¹ * v * u * P a0)) := by
      rw [← hmul]
      exact ACEquiv.of_move (ACMove.mul i a0 (Ne.symm hne) _)
    have s3 : ACEquiv (setAt P i ((P a0)⁻¹ * v * u * P a0)) (setAt P i (v * u)) := by
      rw [← hconj2]
      exact ACEquiv.of_move (ACMove.conj i (P a0) _)
    exact s1.trans (s2.trans s3)

/-- The deletion step in the special case where the helper relator is the generator `of a` and
the deleted letter is that same generator. -/
theorem delete_letter_of {n : Nat} (P : Presentation n) {a0 i : Fin n} (hne : a0 ≠ i)
    {a : Fin n} (ha : P a0 = FreeGroup.of a) (u v : Word n) :
    ACEquiv (setAt P i (u * FreeGroup.of a * v)) (setAt P i (v * u)) :=
  delete_letter_gen P hne u v (Or.inl ha.symm)

/-- The deletion step in the special case where the helper relator is `(of a)⁻¹` and the
deleted letter is `(of a)⁻¹`. -/
theorem delete_letter_inv {n : Nat} (P : Presentation n) {a0 i : Fin n} (hne : a0 ≠ i)
    {a : Fin n} (ha : P a0 = (FreeGroup.of a)⁻¹) (u v : Word n) :
    ACEquiv (setAt P i (u * (FreeGroup.of a)⁻¹ * v)) (setAt P i (v * u)) :=
  delete_letter_gen P hne u v (Or.inl ha.symm)

/-- The one-letter list spells the generator when the second component is `true`. -/
theorem mk_true {n : Nat} (i : Fin n) : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl

/-- The one-letter list spells the inverse of the generator when the second component is
`false`. -/
theorem mk_false {n : Nat} (i : Fin n) : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := by
  show FreeGroup.mk [(i, false)] = (FreeGroup.mk [(i, true)])⁻¹
  rw [FreeGroup.inv_mk]
  simp [FreeGroup.invRev]

/-! ### Killing all letters from a set of generator positions -/

/-- A list either avoids a finite set of letter positions, or splits at an occurrence of one
of them. -/
theorem list_split_finset {n : Nat} (S : Finset (Fin n)) :
    ∀ l : List (Fin n × Bool), (∀ p ∈ l, p.1 ∉ S) ∨
      ∃ (p q : List (Fin n × Bool)) (a : Fin n) (b : Bool),
        a ∈ S ∧ l = p ++ (a, b) :: q := by
  intro l
  induction l with
  | nil => exact Or.inl (by simp)
  | cons x t ih =>
      obtain ⟨a, b⟩ := x
      by_cases ha : a ∈ S
      · exact Or.inr ⟨[], t, a, b, ha, rfl⟩
      · rcases ih with h | ⟨p, q, a', b', ha', hsplit⟩
        · refine Or.inl ?_
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact ha
          · exact h y hy'
        · exact Or.inr ⟨(a, b) :: p, q, a', b', ha', by rw [hsplit]; rfl⟩

/-- The engine of Lemma 5 and of Lemma 8.  Suppose that for every `a ∈ S` the tuple has, at some
position `a0 ≠ i`, a relator equal to `of a` or to `(of a)⁻¹`.  Then every word at position `i`
can be carried, by AC moves that touch only position `i`, to a word with no letters from `S`.
The number of letters from `S` drops by exactly one at each deletion step, which is why the
induction terminates. -/
theorem delete_letters {n : Nat} (P : Presentation n) {i : Fin n} (S : Finset (Fin n))
    (hhelp : ∀ a ∈ S, ∃ a0 : Fin n, a0 ≠ i ∧
      (P a0 = FreeGroup.of a ∨ P a0 = (FreeGroup.of a)⁻¹)) :
    ∀ l : List (Fin n × Bool), ∃ l' : List (Fin n × Bool),
      (∀ p ∈ l', p.1 ∉ S) ∧
      ACEquiv (setAt P i (FreeGroup.mk l)) (setAt P i (FreeGroup.mk l')) := by
  have key : ∀ N : Nat, ∀ l : List (Fin n × Bool), l.length ≤ N →
      ∃ l' : List (Fin n × Bool), (∀ p ∈ l', p.1 ∉ S) ∧
        ACEquiv (setAt P i (FreeGroup.mk l)) (setAt P i (FreeGroup.mk l')) := by
    intro N
    induction N with
    | zero =>
        intro l hl
        have hl0 : l.length = 0 := Nat.le_zero.mp hl
        have hl' : l = [] := List.length_eq_zero_iff.mp hl0
        subst hl'
        exact ⟨[], by simp, ACEquiv.refl _⟩
    | succ N ih =>
        intro l hl
        rcases list_split_finset S l with hfree | ⟨p, q, a, b, ha, rfl⟩
        · exact ⟨l, hfree, ACEquiv.refl _⟩
        · obtain ⟨a0, hne, hsign⟩ := hhelp a ha
          have hsplit : FreeGroup.mk (p ++ (a, b) :: q)
              = FreeGroup.mk p * FreeGroup.mk [(a, b)] * FreeGroup.mk q := by
            rw [show FreeGroup.mk (p ++ (a, b) :: q)
                = FreeGroup.mk p * FreeGroup.mk ((a, b) :: q) from FreeGroup.mul_mk (L₁ := p) (L₂ := (a, b) :: q)]
            rw [show FreeGroup.mk ((a, b) :: q) = FreeGroup.mk [(a, b)] * FreeGroup.mk q
                from FreeGroup.mul_mk (L₁ := [(a, b)]) (L₂ := q)]
            rw [mul_assoc]
          have hx : FreeGroup.mk [(a, b)] = P a0 ∨ FreeGroup.mk [(a, b)] = (P a0)⁻¹ := by
            cases b
            · rw [mk_false]
              rcases hsign with h | h
              · exact Or.inr (by rw [h])
              · exact Or.inl (by rw [h])
            · rcases hsign with h | h
              · exact Or.inl h.symm
              · exact Or.inr (by rw [h]; simp only [inv_inv]; rfl)
          have hdel : ACEquiv (setAt P i (FreeGroup.mk (p ++ (a, b) :: q)))
              (setAt P i (FreeGroup.mk q * FreeGroup.mk p)) := by
            rw [hsplit]
            exact delete_letter_gen P hne _ _ hx
          have hlen : (q ++ p).length ≤ N := by
            have h1 : (p ++ (a, b) :: q).length = p.length + 1 + q.length := by
              rw [List.length_append, List.length_cons]
              omega
            have h2 : p.length + 1 + q.length ≤ N + 1 := by rw [← h1]; exact hl
            have h3 : (q ++ p).length = q.length + p.length := List.length_append ..
            omega
          obtain ⟨l', hl', hac⟩ := ih (q ++ p) hlen
          refine ⟨l', hl', hdel.trans ?_⟩
          have hmk : FreeGroup.mk q * FreeGroup.mk p = FreeGroup.mk (q ++ p) :=
            FreeGroup.mul_mk (L₁ := q) (L₂ := p)
          rw [hmk]
          exact hac
  intro l
  exact key l.length l (le_refl _)

/-- The word version of `delete_letters`: a single relator can be stripped of all letters from
`S`. -/
theorem exists_freeOf_of_acEquiv {n : Nat} (P : Presentation n) {i : Fin n} {a : Fin n}
    (hhelp : ∃ a0 : Fin n, a0 ≠ i ∧
      (P a0 = FreeGroup.of a ∨ P a0 = (FreeGroup.of a)⁻¹)) (w : Word n) :
    ∃ w' : Word n, w' ∈ freeOf a ∧ ACEquiv (setAt P i w) (setAt P i w') := by
  obtain ⟨l', hl', hac⟩ := delete_letters P {a} (by
    intro c hc
    rw [Finset.mem_singleton] at hc
    subst hc
    exact hhelp) w.toWord
  refine ⟨FreeGroup.mk l', mk_mem_freeOf ?_, ?_⟩
  · intro p hp
    have := hl' p hp
    simpa using this
  · have : FreeGroup.mk w.toWord = w := FreeGroup.mk_toWord
    rwa [this] at hac

/-! ## The exponent sum of one generator, and the class hypothesis that forces it to be `±1` -/

/-- The exponent sum of the generator `a` in a word, as a homomorphism to the multiplicative
integers. -/
noncomputable def expSumAt {n : Nat} (a : Fin n) : Word n →* Multiplicative ℤ :=
  FreeGroup.lift fun i => if i = a then Multiplicative.ofAdd (1 : ℤ) else 1

/-- The exponent sum of the generator `a` in the generator `a` is one. -/
theorem expSumAt_same {n : Nat} (a : Fin n) :
    expSumAt a (FreeGroup.of a) = Multiplicative.ofAdd (1 : ℤ) := by
  simp [expSumAt]

/-- The exponent sum of the generator `a` in any other generator is zero. -/
theorem expSumAt_of_ne {n : Nat} {a i : Fin n} (h : i ≠ a) :
    expSumAt a (FreeGroup.of i) = 1 := by
  simp [expSumAt, h]

/-- The exponent sum of a power of a generator. -/
theorem expSumAt_generator_zpow {n : Nat} (a : Fin n) (k : ℤ) :
    expSumAt a (FreeGroup.of a ^ k) = Multiplicative.ofAdd k := by
  rw [map_zpow, expSumAt_same, ← ofAdd_zsmul]
  simp

/-- The reduction of the exponent sum at `a` modulo `m`, as a homomorphism. -/
noncomputable def modExpAt {n : Nat} (a : Fin n) (m : Nat) : Word n →* Multiplicative (ZMod m) :=
  FreeGroup.lift fun i => if i = a then Multiplicative.ofAdd (1 : ZMod m) else 1

/-- The reduction of the exponent sum at `a` in any other generator is zero. -/
theorem modExpAt_of_ne {n : Nat} {a i : Fin n} (m : Nat) (h : i ≠ a) :
    modExpAt a m (FreeGroup.of i) = 1 := by
  simp [modExpAt, h]

/-- The cast from the integers to `ZMod m`, as a homomorphism of multiplicative groups. -/
noncomputable def castHom (m : Nat) : Multiplicative ℤ →* Multiplicative (ZMod m) :=
  (Int.castAddHom (ZMod m)).toMultiplicative

/-- The reduction modulo `m` of the exponent sum at `a` is the exponent sum at `a` followed by
the cast to `ZMod m`. -/
theorem modExpAt_eq_cast_comp {n : Nat} (a : Fin n) (m : Nat) :
    modExpAt a m = (castHom m).comp (expSumAt a) := by
  refine FreeGroup.ext_hom _ _ fun j => ?_
  by_cases h : j = a <;> simp [modExpAt, expSumAt, castHom, h]

/-- If every relator other than the one at position `i` has zero exponent sum in the generator
`a`, and the presentation is of the trivial group, then the exponent sum of `x_a` in the `i`-th
relator is `±1`.  This is the arithmetic step of Lemma 8 of `survey/q-transformations.md` and of
Corollary 7 of `survey/special-classes.md`, in the only form either proof needs. -/
theorem expSum_eq_pm_one {n : Nat} (P : Presentation n) (i a : Fin n)
    (hkill : ∀ j, j ≠ i → expSumAt a (P j) = 1)
    (htriv : Subsingleton (PresentedGroup (Set.range P))) :
    expSumAt a (P i) = Multiplicative.ofAdd (1 : ℤ) ∨
      expSumAt a (P i) = Multiplicative.ofAdd (-1 : ℤ) := by
  set e : ℤ := (expSumAt a (P i)).toAdd with he
  -- the normal closure of the relators is everything
  have htop : Subgroup.normalClosure (Set.range P) = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    have h1 : PresentedGroup.mk (Set.range P) x = 1 := Subsingleton.elim _ _
    exact PresentedGroup.mk_eq_one_iff.mp h1
  -- every relator dies under the reduction of the exponent sum modulo `e.natAbs`
  have hrel : ∀ r ∈ Set.range P, modExpAt a e.natAbs r = 1 := by
    rintro r ⟨k, rfl⟩
    by_cases hk : k = i
    · -- the `i`-th relator: its exponent sum is `e`, which is zero modulo `e.natAbs`
      have hcast : modExpAt a e.natAbs (P k) = castHom e.natAbs (expSumAt a (P k)) := by
        rw [modExpAt_eq_cast_comp]
        rfl
      rw [hcast]
      have hzero : ((e : ℤ) : ZMod e.natAbs) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact Int.natAbs_dvd.mpr (dvd_refl e)
      have hki : P k = P i := by rw [hk]
      have hval : expSumAt a (P k) = Multiplicative.ofAdd e := by
        rw [he, hki]
        simp
      rw [hval]
      show Multiplicative.ofAdd ((e : ℤ) : ZMod e.natAbs) = 1
      rw [hzero]
      rfl
    · -- another position: the exponent sum there is zero by hypothesis
      rw [modExpAt_eq_cast_comp, MonoidHom.comp_apply, hkill k hk, map_one]
  -- the reduction therefore factors through the trivial group, so it kills every generator
  have hone : modExpAt a e.natAbs (FreeGroup.of a) = 1 := by
    have hmem : (FreeGroup.of a : Word n) ∈ Subgroup.normalClosure (Set.range P) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact PresentedGroup.to_group_eq_one_of_mem_closure
      (f := fun j => if j = a then Multiplicative.ofAdd (1 : ZMod e.natAbs) else 1) hrel _ hmem
  have hmod : ((1 : ℤ) : ZMod e.natAbs) = 0 := by
    have h2 : Multiplicative.ofAdd ((1 : ℤ) : ZMod e.natAbs) = 1 := by
      simpa [modExpAt] using hone
    simpa using h2
  have hm1 : e.natAbs = 1 := by
    have h2 : (e.natAbs : ℤ) ∣ 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 e.natAbs).mp hmod
    have h3 : e.natAbs ∣ 1 := by exact_mod_cast h2
    exact Nat.dvd_one.mp h3
  have h4 : expSumAt a (P i) = Multiplicative.ofAdd e := by
    rw [he]
    simp
  rcases Int.natAbs_eq_iff.mp hm1 with h | h
  · left
    rw [h4, h]
    norm_num
  · right
    rw [h4, h]
    norm_num

/-- The form of `expSum_eq_pm_one` used when the relators away from position `i` are the
generators `x_j` up to sign: the exponent sum of `x_i` in the `i`-th relator is `±1`. -/
theorem expSum_self_eq_pm_one {n : Nat} (P : Presentation n) (i : Fin n)
    (hgen : ∀ j, j ≠ i → P j = FreeGroup.of j ∨ P j = (FreeGroup.of j)⁻¹)
    (htriv : Subsingleton (PresentedGroup (Set.range P))) :
    expSumAt i (P i) = Multiplicative.ofAdd (1 : ℤ) ∨
      expSumAt i (P i) = Multiplicative.ofAdd (-1 : ℤ) := by
  refine expSum_eq_pm_one P i i ?_ htriv
  intro j hj
  rcases hgen j hj with h | h
  · rw [h, expSumAt_of_ne (a := i) (i := j) hj]
  · rw [h, map_inv, expSumAt_of_ne (a := i) (i := j) hj, inv_one]

/-! ## Interchanging two relators (Lemma 2 of `survey/special-classes.md`) -/

/-- Writing at two distinct positions in either order gives the same tuple. -/
theorem setAt_comm {n : Nat} (P : Presentation n) {i j : Fin n} (h : i ≠ j) (x y : Word n) :
    setAt (setAt P i x) j y = setAt (setAt P j y) i x := by
  funext k
  by_cases hki : k = i
  · rw [hki]
    simp only [setAt_apply]
    simp [h]
  · by_cases hkj : k = j
    · rw [hkj]
      simp only [setAt_apply]
      simp [Ne.symm h]
    · simp only [setAt_apply]
      simp [hki, hkj]

/-- Lemma 2 of `survey/special-classes.md`, in the form needed below: the two entries at
positions `i` and `j` can be exchanged, at a cost of seven moves: multiply, multiply by an
inverse, multiply, invert, conjugate, where the second step is the three-move derived move
`ACEquiv.mulInv`.  This matches the count in the survey. -/
theorem acEquiv_swap {n : Nat} (P : Presentation n) {i j : Fin n} (h : i ≠ j) :
    ACEquiv P (setAt (setAt P i (P j)) j (P i)) := by
  set T1 : Presentation n := setAt P i (P i * P j) with hT1
  set T2 : Presentation n := setAt T1 j ((P i)⁻¹) with hT2
  set T3 : Presentation n := setAt T2 i ((P i * P j) * (P i)⁻¹) with hT3
  set T4 : Presentation n := setAt T3 j (P i) with hT4
  set T5 : Presentation n := setAt T4 i (P j) with hT5
  have s1 : ACEquiv P T1 := by
    rw [hT1]
    exact ACEquiv.of_move (ACMove.mul i j h P)
  have s2 : ACEquiv T1 T2 := by
    have h1 : T1 j = P j := by rw [hT1]; simp [setAt, Ne.symm h]
    have h2 : T1 i = P i * P j := by rw [hT1]; simp [setAt]
    have hm : mulInvAt T1 j i = T2 := by
      rw [hT2, mulInvAt]
      congr 1
      rw [h1, h2]
      group
    rw [← hm]
    exact ACEquiv.mulInv (Ne.symm h) T1
  have s3 : ACEquiv T2 T3 := by
    have h1 : T2 i = P i * P j := by rw [hT2]; simp [hT1, setAt, h]
    have h2 : T2 j = (P i)⁻¹ := by rw [hT2]; simp [setAt]
    have hm : mulAt T2 i j = T3 := by
      rw [hT3, mulAt]
      congr 1
      rw [h1, h2]
    rw [← hm]
    exact ACEquiv.of_move (ACMove.mul i j h T2)
  have s4 : ACEquiv T3 T4 := by
    have h1 : T3 j = (P i)⁻¹ := by rw [hT3]; simp [hT2, setAt, Ne.symm h]
    have hm : invertAt T3 j = T4 := by
      rw [hT4, invertAt]
      congr 1
      rw [h1]
      group
    rw [← hm]
    exact ACEquiv.of_move (ACMove.invert j T3)
  have s5 : ACEquiv T4 T5 := by
    have h1 : T4 i = (P i * P j) * (P i)⁻¹ := by rw [hT4]; simp [hT3, setAt, h]
    have hm : conjAt T4 i (P i)⁻¹ = T5 := by
      rw [hT5, conjAt]
      congr 1
      rw [h1]
      group
    rw [← hm]
    exact ACEquiv.of_move (ACMove.conj i (P i)⁻¹ T4)
  have hcollapse : T5 = setAt (setAt P i (P j)) j (P i) := by
    rw [hT5, hT4, hT3, hT2, hT1]
    funext k
    by_cases hki : k = i
    · rw [hki]
      simp only [setAt_apply]
      simp [h]
    · by_cases hkj : k = j
      · rw [hkj]
        simp only [setAt_apply]
        simp [Ne.symm h]
      · simp only [setAt_apply]
        simp [hki, hkj]
  rw [hcollapse] at s5
  exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

/-! ## A tuple of signed generators in place is AC-standard -/

/-- If every relator is the corresponding generator, up to sign, then the tuple is
AC-equivalent to the standard tuple.  Each negative sign costs one move. -/
theorem acEquiv_standard_of_signs {n : Nat} (Q : Presentation n) (T : Finset (Fin n))
    (hQ : ∀ j, Q j = if j ∈ T then (FreeGroup.of j)⁻¹ else FreeGroup.of j) :
    ACEquiv Q (standard n) := by
  have key : ∀ T : Finset (Fin n), ∀ R : Presentation n,
      (∀ j, R j = if j ∈ T then (FreeGroup.of j)⁻¹ else FreeGroup.of j) →
      ACEquiv R (standard n) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro R hR
        have hstd : R = standard n := by
          funext j
          simpa [standard] using hR j
        rw [hstd]
        exact ACEquiv.refl _
    | insert a T' ha ih =>
        intro R hR
        have hR' : ∀ j, invertAt R a j =
            if j ∈ T' then (FreeGroup.of j)⁻¹ else FreeGroup.of j := by
          intro j
          by_cases hj : j = a
          · have h1 : R a = (FreeGroup.of a)⁻¹ := by
              rw [hR a]
              simp [ha]
            rw [hj]
            rw [invertAt, setAt_self, h1, inv_inv]
            simp [ha]
          · rw [invertAt, setAt_of_ne (P := R) (i := a) (v := _) (k := j) hj, hR j]
            by_cases hmem : j ∈ T'
            · simp [hmem]
            · simp [hmem, hj]
        exact (ACEquiv.of_move (ACMove.invert a R)).trans (ih (invertAt R a) hR')
  exact key T Q hQ

/-! ## (b) Corollary 7: a rank-two presentation with a relator conjugate to a generator -/

/-- A word all of whose letters are the same generator is a power of that generator. -/
theorem exists_zpow_of_letters {n : Nat} (i : Fin n) :
    ∀ {l : List (Fin n × Bool)}, (∀ p ∈ l, p.1 = i) →
      ∃ k : ℤ, FreeGroup.mk l = FreeGroup.of i ^ k := by
  intro l
  induction l with
  | nil => intro _
           exact ⟨0, by rw [zpow_zero]; exact (FreeGroup.one_eq_mk).symm⟩
  | cons x t ih =>
      intro h
      obtain ⟨c, b⟩ := x
      have hc : c = i := h (c, b) (List.mem_cons_self ..)
      obtain ⟨k, hk⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
      refine ⟨(if b then (1 : ℤ) else -1) + k, ?_⟩
      rw [show FreeGroup.mk ((c, b) :: t) = FreeGroup.mk [(c, b)] * FreeGroup.mk t from
        FreeGroup.mul_mk (L₁ := [(c, b)]) (L₂ := t), hk]
      rw [hc, mk_singleton]
      cases b
      · rw [if_neg (by simp), zpow_add]
        simp
      · rw [if_pos rfl, zpow_add]
        simp

/-- If every relator is the corresponding generator up to sign, the tuple is AC-standard. -/
theorem acEquiv_standard_of_signed {n : Nat} (Q : Presentation n)
    (h : ∀ j, Q j = FreeGroup.of j ∨ Q j = (FreeGroup.of j)⁻¹) : ACEquiv Q (standard n) := by
  classical
  refine acEquiv_standard_of_signs Q (Finset.univ.filter (fun j => Q j ≠ FreeGroup.of j)) ?_
  intro j
  by_cases hmem : j ∈ Finset.univ.filter (fun j => Q j ≠ FreeGroup.of j)
  · rw [if_pos hmem]
    rcases h j with h1 | h1
    · exact absurd h1 (Finset.mem_filter.mp hmem).2
    · exact h1
  · rw [if_neg hmem]
    by_contra hne
    exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩)

/-- Two rank-two presentations with the same entries at `0` and `1` are equal. -/
theorem presentation_two_ext {P Q : Presentation 2} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) :
    P = Q := by
  funext j
  fin_cases j
  · simpa using h0
  · simpa using h1

/-- The rank-two endgame: the tuple `(y, x^k)` with `k = ±1` is AC-standard.  The swap costs
seven moves and the sign at most one. -/
theorem acEquiv_standard_two_of_entries (Q : Presentation 2) (k : ℤ) (hk : k = 1 ∨ k = -1)
    (h0 : Q 0 = FreeGroup.of 1) (h1 : Q 1 = FreeGroup.of 0 ^ k) : ACEquiv Q (standard 2) := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have hswap := acEquiv_swap (P := Q) (i := 0) (j := 1) hne
  have hQ0 : setAt (setAt Q 0 (Q 1)) 1 (Q 0) 0 = FreeGroup.of 0 ^ k := by
    rw [setAt_of_ne (P := setAt Q 0 (Q 1)) (i := 1) (v := Q 0) (k := 0) hne, setAt_self, h1]
  have hQ1 : setAt (setAt Q 0 (Q 1)) 1 (Q 0) 1 = FreeGroup.of 1 := by
    rw [setAt_self, h0]
  rcases hk with rfl | rfl
  · have hstd : setAt (setAt Q 0 (Q 1)) 1 (Q 0) = standard 2 := by
      refine presentation_two_ext ?_ ?_
      · rw [hQ0]
        rfl
      · rw [hQ1]
        rfl
    rw [hstd] at hswap
    exact hswap
  · have hinv : ACEquiv (setAt (setAt Q 0 (Q 1)) 1 (Q 0))
        (invertAt (setAt (setAt Q 0 (Q 1)) 1 (Q 0)) 0) :=
      ACEquiv.of_move (ACMove.invert 0 _)
    have hstd : invertAt (setAt (setAt Q 0 (Q 1)) 1 (Q 0)) 0 = standard 2 := by
      refine presentation_two_ext ?_ ?_
      · rw [invertAt, setAt_self, hQ0]
        rw [zpow_neg_one, inv_inv]
        rfl
      · rw [invertAt, setAt_of_ne (P := setAt (setAt Q 0 (Q 1)) 1 (Q 0)) (i := 0)
          (v := (setAt (setAt Q 0 (Q 1)) 1 (Q 0) 0)⁻¹) (k := 1) (by decide), hQ1]
        rfl
    rw [hstd] at hinv
    exact hswap.trans hinv

/-! ## (b) Corollary 7 of `survey/special-classes.md` -/

/-- The direct case of Corollary 7 for the first position: if the first relator of a balanced
rank-two presentation of the trivial group is conjugate to a generator, the presentation is
AC-standard. -/
theorem acEquiv_standard_of_conj_zero_direct (P : Presentation 2)
    (htriv : Subsingleton (PresentedGroup (Set.range P)))
    (hconj : ∃ (a : Fin 2) (w : Word 2), P 0 = w * FreeGroup.of a * w⁻¹) :
    ACEquiv P (standard 2) := by
  classical
  obtain ⟨a, w, hw⟩ := hconj
  -- put `of a` at position 0
  have hP'0 : conjAt P 0 w⁻¹ 0 = FreeGroup.of a := by
    rw [conjAt, setAt_self, hw]
    group
  have hstep : ACEquiv P (conjAt P 0 w⁻¹) := ACEquiv.of_move (ACMove.conj 0 w⁻¹ P)
  -- strip the `a`-letters from the second relator
  obtain ⟨l', hl', hac⟩ := delete_letters (conjAt P 0 w⁻¹) (i := 1) {a} (by
    intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨0, by decide, Or.inl hP'0⟩) (FreeGroup.toWord (conjAt P 0 w⁻¹ 1))
  have hset : setAt (conjAt P 0 w⁻¹) 1 (conjAt P 0 w⁻¹ 1) = conjAt P 0 w⁻¹ := by
    funext k
    by_cases hk : k = 1
    · rw [hk, setAt_self]
    · rw [setAt_of_ne (P := conjAt P 0 w⁻¹) (i := 1) (v := _) (k := k) hk]
  have hfull : ACEquiv (conjAt P 0 w⁻¹) (setAt (conjAt P 0 w⁻¹) 1 (FreeGroup.mk l')) := by
    rw [FreeGroup.mk_toWord, hset] at hac
    exact hac
  have hQ0 : setAt (conjAt P 0 w⁻¹) 1 (FreeGroup.mk l') 0 = FreeGroup.of a := by
    rw [setAt_of_ne (P := conjAt P 0 w⁻¹) (i := 1) (v := FreeGroup.mk l') (k := 0) (by decide)]
    exact hP'0
  have htrivQ : Subsingleton
      (PresentedGroup (Set.range (setAt (conjAt P 0 w⁻¹) 1 (FreeGroup.mk l')))) :=
    (presentedGroup_subsingleton_iff (hstep.trans hfull)).mp htriv
  have hletters : ∀ p ∈ l', p.1 ≠ a := fun p hp => by simpa using hl' p hp
  fin_cases a
  · -- the helper relator is `x`, so the remaining letters are `y`
    obtain ⟨k, hk⟩ := exists_zpow_of_letters (i := (1 : Fin 2)) (l := l') (fun p hp => by
      have hpa : p.1 ≠ 0 := hletters p hp
      obtain ⟨c, b⟩ := p
      simp only at hpa ⊢
      fin_cases c <;> simp_all)
    have hQ1 : setAt (conjAt P 0 w⁻¹) 1 (FreeGroup.mk l') 1 = FreeGroup.of 1 ^ k := by
      rw [setAt_self, hk]
    have hpm : k = 1 ∨ k = -1 := by
      have hexp := expSum_eq_pm_one (P := setAt (conjAt P 0 w⁻¹) 1 (FreeGroup.mk l'))
        (i := 1) (a := 1) (by
          intro j hj
          have hj0 : j = 0 := by fin_cases j <;> simp_all
          rw [hj0, hQ0]
          exact expSumAt_of_ne (a := 1) (i := 0) (by decide : (0 : Fin 2) ≠ 1)) htrivQ
      rw [hQ1, expSumAt_generator_zpow] at hexp
      rcases hexp with h | h
      · exact Or.inl (Multiplicative.ofAdd.injective h)
      · exact Or.inr (Multiplicative.ofAdd.injective h)
    refine (hstep.trans hfull).trans (acEquiv_standard_of_signed _ ?_)
    intro j
    fin_cases j
    · exact Or.inl (by simpa using hQ0)
    · rcases hpm with rfl | rfl
      · exact Or.inl (by simpa using hQ1)
      · exact Or.inr (by simpa using hQ1)
  · -- the helper relator is `y`, so the remaining letters are `x`
    obtain ⟨k, hk⟩ := exists_zpow_of_letters (i := (0 : Fin 2)) (l := l') (fun p hp => by
      have hpa : p.1 ≠ 1 := hletters p hp
      obtain ⟨c, b⟩ := p
      simp only at hpa ⊢
      fin_cases c <;> simp_all)
    have hQ1 : setAt (conjAt P 0 w⁻¹) 1 (FreeGroup.mk l') 1 = FreeGroup.of 0 ^ k := by
      rw [setAt_self, hk]
    have hpm : k = 1 ∨ k = -1 := by
      have hexp := expSum_eq_pm_one (P := setAt (conjAt P 0 w⁻¹) 1 (FreeGroup.mk l'))
        (i := 1) (a := 0) (by
          intro j hj
          have hj0 : j = 0 := by fin_cases j <;> simp_all
          rw [hj0, hQ0]
          exact expSumAt_of_ne (a := 0) (i := 1) (by decide : (1 : Fin 2) ≠ 0)) htrivQ
      rw [hQ1, expSumAt_generator_zpow] at hexp
      rcases hexp with h | h
      · exact Or.inl (Multiplicative.ofAdd.injective h)
      · exact Or.inr (Multiplicative.ofAdd.injective h)
    exact (hstep.trans hfull).trans (acEquiv_standard_two_of_entries _ k hpm hQ0 hQ1)

/-- The case of Corollary 7 where the first relator is conjugate to the inverse of a generator:
invert the relator and apply the direct case. -/
theorem acEquiv_standard_of_conj_zero_inv (P : Presentation 2)
    (htriv : Subsingleton (PresentedGroup (Set.range P)))
    (hconj : ∃ (a : Fin 2) (w : Word 2), P 0 = w * (FreeGroup.of a)⁻¹ * w⁻¹) :
    ACEquiv P (standard 2) := by
  obtain ⟨a, w, hw⟩ := hconj
  have hP'0 : conjAt P 0 w⁻¹ 0 = (FreeGroup.of a)⁻¹ := by
    rw [conjAt, setAt_self, hw]
    group
  have hstep : ACEquiv P (conjAt P 0 w⁻¹) := ACEquiv.of_move (ACMove.conj 0 w⁻¹ P)
  have hstep2 : ACEquiv (conjAt P 0 w⁻¹) (invertAt (conjAt P 0 w⁻¹) 0) :=
    ACEquiv.of_move (ACMove.invert 0 _)
  have hinv0 : invertAt (conjAt P 0 w⁻¹) 0 0 = FreeGroup.of a := by
    rw [invertAt, setAt_self, hP'0, inv_inv]
  have hconj' : ∃ (a : Fin 2) (u : Word 2),
      invertAt (conjAt P 0 w⁻¹) 0 0 = u * FreeGroup.of a * u⁻¹ := by
    refine ⟨a, 1, ?_⟩
    rw [hinv0]
    simp
  have htriv' : Subsingleton (PresentedGroup (Set.range (invertAt (conjAt P 0 w⁻¹) 0))) :=
    (presentedGroup_subsingleton_iff hstep2).mp ((presentedGroup_subsingleton_iff hstep).mp htriv)
  exact (hstep.trans hstep2).trans (acEquiv_standard_of_conj_zero_direct _ htriv' hconj')

/-- Corollary 7 of `survey/special-classes.md`, first position: a balanced rank-two
presentation of the trivial group whose first relator is conjugate to a generator or to its
inverse is AC-standard. -/
theorem acEquiv_standard_of_conj_generator_zero (P : Presentation 2)
    (htriv : Subsingleton (PresentedGroup (Set.range P)))
    (hconj : ∃ (a : Fin 2) (w : Word 2),
      (P 0 = w * FreeGroup.of a * w⁻¹) ∨ (P 0 = w * (FreeGroup.of a)⁻¹ * w⁻¹)) :
    ACEquiv P (standard 2) := by
  obtain ⟨a, w, h | h⟩ := hconj
  · exact acEquiv_standard_of_conj_zero_direct P htriv ⟨a, w, h⟩
  · exact acEquiv_standard_of_conj_zero_inv P htriv ⟨a, w, h⟩

/-- Corollary 7 of `survey/special-classes.md`: a balanced rank-two presentation of the trivial
group with a relator conjugate to a generator or to its inverse is AC-standard. -/
theorem acEquiv_standard_of_conj_generator (P : Presentation 2) (i : Fin 2)
    (htriv : Subsingleton (PresentedGroup (Set.range P)))
    (hconj : ∃ (a : Fin 2) (w : Word 2),
      ((P i = w * FreeGroup.of a * w⁻¹) ∨ (P i = w * (FreeGroup.of a)⁻¹ * w⁻¹))) :
    ACEquiv P (standard 2) := by
  fin_cases i
  · obtain ⟨a, w, h⟩ := hconj
    exact acEquiv_standard_of_conj_generator_zero P htriv ⟨a, w, h⟩
  · -- move the special relator to the first position
    obtain ⟨a, w, h⟩ := hconj
    have hne : (0 : Fin 2) ≠ 1 := by decide
    have hswap := acEquiv_swap (P := P) (i := 0) (j := 1) hne
    have hS0 : setAt (setAt P 0 (P 1)) 1 (P 0) 0 = P 1 := by
      rw [setAt_of_ne (P := setAt P 0 (P 1)) (i := 1) (v := P 0) (k := 0) hne, setAt_self]
    have htrivS : Subsingleton
        (PresentedGroup (Set.range (setAt (setAt P 0 (P 1)) 1 (P 0)))) :=
      (presentedGroup_subsingleton_iff hswap).mp htriv
    have hconjS : ∃ (a : Fin 2) (w : Word 2),
        (setAt (setAt P 0 (P 1)) 1 (P 0) 0 = w * FreeGroup.of a * w⁻¹) ∨
          (setAt (setAt P 0 (P 1)) 1 (P 0) 0 = w * (FreeGroup.of a)⁻¹ * w⁻¹) :=
      ⟨a, w, by rw [hS0]; exact h⟩
    exact hswap.trans (acEquiv_standard_of_conj_generator_zero _ htrivS hconjS)

/-! ## (c) Lemma 8 of `survey/q-transformations.md` -/

/-- Lemma 8 of `survey/q-transformations.md`, in the AC form.  Let `P` be a balanced
presentation of rank `n` of the trivial group whose relators at all positions other than `i`
are the generators `x_j` up to sign.  Then `P` is AC-equivalent to the standard tuple.  The
proof deletes the letters of the other generators from the `i`-th relator and then uses that
its exponent sum is `±1`. -/
theorem acEquiv_standard_of_generator_relators {n : Nat} (P : Presentation n) (i : Fin n)
    (hgen : ∀ j, j ≠ i → P j = FreeGroup.of j ∨ P j = (FreeGroup.of j)⁻¹)
    (htriv : Subsingleton (PresentedGroup (Set.range P))) :
    ACEquiv P (standard n) := by
  classical
  set S : Finset (Fin n) := Finset.univ.erase i with hS
  -- delete the letters of every generator other than `x_i` from the `i`-th relator
  obtain ⟨l', hl', hac⟩ := delete_letters P (i := i) S (by
    intro a ha
    rw [hS, Finset.mem_erase] at ha
    exact ⟨a, ha.1, hgen a ha.1⟩) (FreeGroup.toWord (P i))
  have hset : setAt P i (P i) = P := by
    funext k
    by_cases hk : k = i
    · rw [hk, setAt_self]
    · rw [setAt_of_ne (P := P) (i := i) (v := _) (k := k) hk]
  have hstep : ACEquiv P (setAt P i (FreeGroup.mk l')) := by
    rw [FreeGroup.mk_toWord, hset] at hac
    exact hac
  -- all remaining letters are the letter `x_i`
  have hletters : ∀ p ∈ l', p.1 = i := by
    intro p hp
    have h1 : p.1 ∉ S := hl' p hp
    rw [hS, Finset.mem_erase] at h1
    by_contra hne
    exact h1 ⟨hne, Finset.mem_univ _⟩
  obtain ⟨k, hk⟩ := exists_zpow_of_letters (i := i) (l := l') hletters
  have hQ1 : setAt P i (FreeGroup.mk l') i = FreeGroup.of i ^ k := by
    rw [setAt_self, hk]
  have htrivQ : Subsingleton (PresentedGroup (Set.range (setAt P i (FreeGroup.mk l')))) :=
    (presentedGroup_subsingleton_iff hstep).mp htriv
  have hQj : ∀ j, j ≠ i → setAt P i (FreeGroup.mk l') j = FreeGroup.of j ∨
      setAt P i (FreeGroup.mk l') j = (FreeGroup.of j)⁻¹ := by
    intro j hj
    rw [setAt_of_ne (P := P) (i := i) (v := FreeGroup.mk l') (k := j) hj]
    exact hgen j hj
  -- the exponent sum of `x_i` in the surviving relator is `±1`
  have hpm : k = 1 ∨ k = -1 := by
    have hexp := expSum_eq_pm_one (P := setAt P i (FreeGroup.mk l')) (i := i) (a := i) (by
      intro j hj
      rcases hQj j hj with h | h
      · rw [h, expSumAt_of_ne (a := i) (i := j) hj]
      · rw [h, map_inv, expSumAt_of_ne (a := i) (i := j) hj, inv_one]) htrivQ
    rw [hQ1, expSumAt_generator_zpow] at hexp
    rcases hexp with h | h
    · exact Or.inl (Multiplicative.ofAdd.injective h)
    · exact Or.inr (Multiplicative.ofAdd.injective h)
  refine hstep.trans (acEquiv_standard_of_signed _ ?_)
  intro j
  by_cases hj : j = i
  · rw [hj]
    rcases hpm with rfl | rfl
    · exact Or.inl (by rw [hQ1, zpow_one])
    · exact Or.inr (by rw [hQ1, zpow_neg_one])
  · exact hQj j hj

/-! ## The hypotheses of the two class theorems are satisfiable

The standard tuple is a witness: it presents the trivial group, its `j`-th relator is the
generator `x_j`, and its first relator is a conjugate of `x_0`.  These instances exist only to
show that (b) and (c) are not vacuous, since a theorem with an unsatisfiable hypothesis would
prove nothing. -/

/-- The standard tuple presents the trivial group. -/
theorem subsingleton_presentedGroup_standard (n : Nat) :
    Subsingleton (PresentedGroup (Set.range (standard n))) := by
  have hgen : ∀ x : PresentedGroup (Set.range (standard n)), x = 1 := by
    intro x
    have h := PresentedGroup.generated_by (Set.range (standard n))
      (⊥ : Subgroup (PresentedGroup (Set.range (standard n)))) ?_ x
    · simpa using h
    · intro j
      have h1 : PresentedGroup.of j = 1 :=
        PresentedGroup.one_of_mem (show FreeGroup.of j ∈ Set.range (standard n) from ⟨j, rfl⟩)
      simpa using h1
  exact ⟨fun x y => by rw [hgen x, hgen y]⟩

/-- Corollary 7 applies to the standard tuple: its first relator is a conjugate of `x`. -/
example : ACEquiv (standard 2) (standard 2) :=
  acEquiv_standard_of_conj_generator (standard 2) 0 (subsingleton_presentedGroup_standard 2)
    ⟨0, 1, Or.inl (by simp [standard])⟩

/-- Lemma 8 applies to the standard tuple. -/
example : ACEquiv (standard 2) (standard 2) :=
  acEquiv_standard_of_generator_relators (standard 2) 1
    (by intro j hj; simp [standard])
    (subsingleton_presentedGroup_standard 2)

/-! ## Axiom audit

Every theorem of this file, with the axioms its proof uses.  There is no `sorry`, no new
axiom, and no use of `native_decide` anywhere in the file; the only axioms are Lean's three
standard ones. -/

-- Part (a): the normal closure is an AC-invariant
#print axioms mem_nclRange
#print axioms nclRange_normal
#print axioms nclRange_invertAt_le
#print axioms nclRange_invertAt
#print axioms nclRange_conjAt_le
#print axioms nclRange_conjAt
#print axioms nclRange_mulAt_le
#print axioms nclRange_mulAt
#print axioms nclRange_eq_of_acMove
#print axioms nclRange_eq_of_acEquiv
#print axioms presentedGroup_mulEquiv_of_acEquiv
#print axioms presentedGroup_subsingleton_iff
-- the copied base lemmas that part (a) uses
#print axioms ACEquiv.symm
#print axioms ACEquiv.mulInv
#print axioms ACEquiv.mulLeft
-- the deletion engine
#print axioms setAt_setAt
#print axioms mk_singleton
#print axioms mk_true
#print axioms mk_false
#print axioms of_mem_freeOf
#print axioms mk_mem_freeOf
#print axioms delete_letter_gen
#print axioms delete_letter_of
#print axioms delete_letter_inv
#print axioms list_split_finset
#print axioms delete_letters
#print axioms exists_freeOf_of_acEquiv
#print axioms exists_zpow_of_letters
-- the exponent-sum step
#print axioms expSumAt_same
#print axioms expSumAt_of_ne
#print axioms expSumAt_generator_zpow
#print axioms modExpAt_of_ne
#print axioms modExpAt_eq_cast_comp
#print axioms expSum_eq_pm_one
#print axioms expSum_self_eq_pm_one
-- interchange, signs, endgames
#print axioms setAt_comm
#print axioms acEquiv_swap
#print axioms acEquiv_standard_of_signs
#print axioms acEquiv_standard_of_signed
#print axioms presentation_two_ext
#print axioms acEquiv_standard_two_of_entries
-- (b) Corollary 7
#print axioms acEquiv_standard_of_conj_zero_direct
#print axioms acEquiv_standard_of_conj_zero_inv
#print axioms acEquiv_standard_of_conj_generator_zero
#print axioms acEquiv_standard_of_conj_generator
-- (c) Lemma 8
#print axioms acEquiv_standard_of_generator_relators
-- satisfiability of the hypotheses
#print axioms subsingleton_presentedGroup_standard

end AndrewsCurtis
