/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AC2

/-!
# Quotient witnesses: kernel-checked non-AC-triviality of balanced rank-two presentations

`toolkit/lean/AC2.lean` proves that AC-equivalence preserves the presented group
(`nclRange_eq_of_acEquiv`, `presentedGroup_subsingleton_iff`).  Every kernel check of the
campaign before this file goes the other way: it certifies that a presentation *is*
AC-trivial, by replaying a move list into the standard tuple.  This file adds the
complementary direction, a *quotient witness*, and with it the first kernel-checked
theorems of the form "this balanced rank-two presentation is **not** AC-trivial".

A quotient witness for a relator pair `(r1, r2)` is a pair of permutations `(s, t)` of
`Fin m` such that `r1(s,t) = 1`, `r2(s,t) = 1` and `(s,t) != (1,1)`.  It is a
homomorphism `F_2 -> Sym(m)` that kills both relators and does not kill the whole free
group, so the presented group has a non-trivial quotient and cannot be trivial, while the
standard tuple presents the trivial group.  Since AC-equivalence preserves the presented
group, the presentation is not AC-equivalent to the standard tuple.  All 38 instances
below were found, and are re-verified, by the Python and GAP scripts of this directory
(`quot.py`, `check.g`, `gen_lean.py`); the kernel check is the `decide` in each proof.

Nothing here bears on the truth of the Andrews-Curtis conjecture: every instance presents
a group that is not trivial, so it lies outside the conjecture's scope by a classical
invariant (the group), not by an Andrews-Curtis argument.
-/

set_option maxRecDepth 10000

namespace AndrewsCurtis

/-! ## The bridge -/

/-- The normal closure of the standard relator tuple is the whole free group: the standard
tuple presents the trivial group. -/
theorem nclRange_standard (n : Nat) : nclRange (standard n) = ⊤ := by
  have h : nclRange (standard n)
      = Subgroup.normalClosure (Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n))) := rfl
  rw [h, eq_top_iff]
  calc (⊤ : Subgroup (Word n))
      = Subgroup.closure (Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n))) :=
        (FreeGroup.closure_range_of (Fin n)).symm
    _ ≤ Subgroup.normalClosure (Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n))) := by
        rw [Subgroup.closure_le]
        exact Subgroup.subset_normalClosure

/-- **The quotient-witness bridge.**  A homomorphism out of the free group that kills
every relator of `P` but not every generator witnesses that `P` is not AC-equivalent to
the standard tuple. -/
theorem not_acEquiv_standard_of_witness {n : Nat} (P : Presentation n)
    {G : Type*} [Group G] (φ : Word n →* G) (hrel : ∀ k, φ (P k) = 1)
    {a : Fin n} (hgen : φ (FreeGroup.of a) ≠ 1) :
    ¬ ACEquiv P (standard n) := by
  intro h
  have hncl : nclRange P = ⊤ := by rw [nclRange_eq_of_acEquiv h, nclRange_standard]
  have hle : nclRange P ≤ φ.ker := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨k, rfl⟩
    exact MonoidHom.mem_ker.mpr (hrel k)
  rw [hncl] at hle
  exact hgen (MonoidHom.mem_ker.mp (hle (Subgroup.mem_top _)))

/-- The same bridge in group-theoretic form: a presentation whose presented group is not
trivial is not AC-equivalent to the standard tuple. -/
theorem not_acEquiv_standard_of_not_subsingleton {n : Nat} {P : Presentation n}
    (h : ¬ Subsingleton (PresentedGroup (Set.range P))) : ¬ ACEquiv P (standard n) :=
  fun hac => h ((presentedGroup_subsingleton_iff hac).mpr (subsingleton_presentedGroup_standard n))

/-- The homomorphism determined by a pair of permutations of `Fin m`. -/
def pairHom {m : Nat} (s t : Equiv.Perm (Fin m)) : Word 2 →* Equiv.Perm (Fin m) :=
  FreeGroup.lift (fun i => if i = 0 then s else t)

theorem pairHom_zero {m : Nat} (s t : Equiv.Perm (Fin m)) :
    pairHom s t (FreeGroup.of 0) = s := by
  simp [pairHom]

theorem pairHom_one {m : Nat} (s t : Equiv.Perm (Fin m)) :
    pairHom s t (FreeGroup.of 1) = t := by
  simp [pairHom, show (1 : Fin 2) ≠ 0 from by decide]


/-! ## A sound certificate checker for non-AC-triviality

The campaign's Lean layer certifies AC-*triviality* by replaying move lists
(`checkCert` in `AC3.lean`, with `checkCert_sound`).  This is the missing other half: a
Boolean checker for a quotient witness, with a soundness theorem, so that a
non-AC-triviality certificate is one `decide` away. -/

/-- `checkWitness P s t` is `true` exactly when `(s,t)` is a quotient witness for the
rank-two presentation `P`: both relators die and the pair is not `(1,1)`. -/
def checkWitness {m : Nat} (P : Presentation 2) (s t : Equiv.Perm (Fin m)) : Bool :=
  decide (pairHom s t (P 0) = 1) && decide (pairHom s t (P 1) = 1) &&
    (decide (s ≠ 1) || decide (t ≠ 1))

/-- **Soundness.**  A witness accepted by the checker proves that `P` is not
AC-equivalent to the standard tuple. -/
theorem checkWitness_sound {m : Nat} {P : Presentation 2} {s t : Equiv.Perm (Fin m)}
    (h : checkWitness P s t = true) : ¬ ACEquiv P (standard 2) := by
  simp only [checkWitness, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, hs | ht⟩ := h
  · exact not_acEquiv_standard_of_witness P (pairHom s t) (fun k => by
      fin_cases k
      · simpa using h1
      · simpa using h2) (a := 0) (by rwa [pairHom_zero])
  · exact not_acEquiv_standard_of_witness P (pairHom s t) (fun k => by
      fin_cases k
      · simpa using h1
      · simpa using h2) (a := 1) (by rwa [pairHom_one])

/-! ## The instances

A block per presentation: the two permutations, the two relators, the relator check (a
`decide` on a permutation equation) and the non-AC-triviality theorem. -/

/-- total relator length 12, relators `BAABa` and `BBBBAbA`, witness in `S5`. -/
def s0 : Equiv.Perm (Fin 5) := (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t0 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u0 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v0 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def Q0 : Presentation 2 := ![u0, v0]
theorem Q0_rel : ∀ k, pairHom s0 t0 (Q0 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q0, u0, v0, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q0_not_acTrivial : ¬ ACEquiv Q0 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q0 (pairHom s0 t0) Q0_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 12, relators `BABaa` and `BBBBaba`, witness in `S5`. -/
def s1 : Equiv.Perm (Fin 5) := (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t1 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u1 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def v1 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def Q1 : Presentation 2 := ![u1, v1]
theorem Q1_rel : ∀ k, pairHom s1 t1 (Q1 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q1, u1, v1, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q1_not_acTrivial : ¬ ACEquiv Q1 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q1 (pairHom s1 t1) Q1_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 12, relators `BBAbA` and `BAAAABa`, witness in `S5`. -/
def s2 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t2 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4)
def u2 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def v2 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def Q2 : Presentation 2 := ![u2, v2]
theorem Q2_rel : ∀ k, pairHom s2 t2 (Q2 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q2, u2, v2, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q2_not_acTrivial : ¬ ACEquiv Q2 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q2 (pairHom s2 t2) Q2_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 12, relators `BBaba` and `BABaaaa`, witness in `S5`. -/
def s3 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t3 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 4) * (Equiv.swap (2 : Fin 5) 4)
def u3 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v3 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0
def Q3 : Presentation 2 := ![u3, v3]
theorem Q3_rel : ∀ k, pairHom s3 t3 (Q3 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q3, u3, v3, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q3_not_acTrivial : ¬ ACEquiv Q3 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q3 (pairHom s3 t3) Q3_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BAABa` and `BBBAbabA`, witness in `S5`. -/
def s4 : Equiv.Perm (Fin 5) := (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t4 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u4 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v4 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def Q4 : Presentation 2 := ![u4, v4]
theorem Q4_rel : ∀ k, pairHom s4 t4 (Q4 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q4, u4, v4, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q4_not_acTrivial : ¬ ACEquiv Q4 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q4 (pairHom s4 t4) Q4_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BAABa` and `BBBBBAAA`, witness in `S5`. -/
def s5 : Equiv.Perm (Fin 5) := (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t5 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u5 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v5 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹
def Q5 : Presentation 2 := ![u5, v5]
theorem Q5_rel : ∀ k, pairHom s5 t5 (Q5 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q5, u5, v5, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q5_not_acTrivial : ¬ ACEquiv Q5 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q5 (pairHom s5 t5) Q5_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BABABa` and `BBBBBAA`, witness in `S5`. -/
def s6 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (3 : Fin 5) 4)
def t6 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u6 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v6 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹
def Q6 : Presentation 2 := ![u6, v6]
theorem Q6_rel : ∀ k, pairHom s6 t6 (Q6 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q6, u6, v6, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q6_not_acTrivial : ¬ ACEquiv Q6 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q6 (pairHom s6 t6) Q6_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BABAbA` and `BBAAAAA`, witness in `S5`. -/
def s7 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t7 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (3 : Fin 5) 4)
def u7 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def v7 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹
def Q7 : Presentation 2 := ![u7, v7]
theorem Q7_rel : ∀ k, pairHom s7 t7 (Q7 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q7, u7, v7, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q7_not_acTrivial : ¬ ACEquiv Q7 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q7 (pairHom s7 t7) Q7_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BABaBa` and `BBBBBaa`, witness in `S5`. -/
def s8 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (3 : Fin 5) 4)
def t8 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u8 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v8 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def Q8 : Presentation 2 := ![u8, v8]
theorem Q8_rel : ∀ k, pairHom s8 t8 (Q8 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q8, u8, v8, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q8_not_acTrivial : ¬ ACEquiv Q8 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q8 (pairHom s8 t8) Q8_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BABaa` and `BBBBBaaa`, witness in `S5`. -/
def s9 : Equiv.Perm (Fin 5) := (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t9 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u9 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def v9 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0
def Q9 : Presentation 2 := ![u9, v9]
theorem Q9_rel : ∀ k, pairHom s9 t9 (Q9 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q9, u9, v9, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q9_not_acTrivial : ¬ ACEquiv Q9 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q9 (pairHom s9 t9) Q9_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BABaa` and `BBBabAba`, witness in `S5`. -/
def s10 : Equiv.Perm (Fin 5) := (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t10 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u10 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def v10 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0
def Q10 : Presentation 2 := ![u10, v10]
theorem Q10_rel : ∀ k, pairHom s10 t10 (Q10 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q10, u10, v10, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q10_not_acTrivial : ¬ ACEquiv Q10 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q10 (pairHom s10 t10) Q10_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BABaba` and `BAABaaa`, witness in `S5`. -/
def s11 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t11 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u11 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v11 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0
def Q11 : Presentation 2 := ![u11, v11]
theorem Q11_rel : ∀ k, pairHom s11 t11 (Q11 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q11, u11, v11, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q11_not_acTrivial : ¬ ACEquiv Q11 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q11 (pairHom s11 t11) Q11_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BABaba` and `BAbABaa`, witness in `S5`. -/
def s12 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t12 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u12 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v12 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def Q12 : Presentation 2 := ![u12, v12]
theorem Q12_rel : ∀ k, pairHom s12 t12 (Q12 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q12, u12, v12, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q12_not_acTrivial : ¬ ACEquiv Q12 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q12 (pairHom s12 t12) Q12_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BABaba` and `BBBabba`, witness in `S5`. -/
def s13 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t13 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u13 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v13 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 1 * FreeGroup.of 0
def Q13 : Presentation 2 := ![u13, v13]
theorem Q13_rel : ∀ k, pairHom s13 t13 (Q13 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q13, u13, v13, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q13_not_acTrivial : ¬ ACEquiv Q13 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q13 (pairHom s13 t13) Q13_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BABaba` and `BBabAba`, witness in `S5`. -/
def s14 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t14 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u14 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v14 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0
def Q14 : Presentation 2 := ![u14, v14]
theorem Q14_rel : ∀ k, pairHom s14 t14 (Q14 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q14, u14, v14, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q14_not_acTrivial : ¬ ACEquiv Q14 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q14 (pairHom s14 t14) Q14_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BAbABa` and `BAAABaa`, witness in `S5`. -/
def s15 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t15 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u15 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v15 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def Q15 : Presentation 2 := ![u15, v15]
theorem Q15_rel : ∀ k, pairHom s15 t15 (Q15 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q15, u15, v15, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q15_not_acTrivial : ¬ ACEquiv Q15 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q15 (pairHom s15 t15) Q15_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BAbABa` and `BAABaba`, witness in `S5`. -/
def s16 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t16 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u16 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v16 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def Q16 : Presentation 2 := ![u16, v16]
theorem Q16_rel : ∀ k, pairHom s16 t16 (Q16 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q16, u16, v16, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q16_not_acTrivial : ¬ ACEquiv Q16 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q16 (pairHom s16 t16) Q16_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BAbABa` and `BBAbabA`, witness in `S5`. -/
def s17 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t17 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u17 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v17 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def Q17 : Presentation 2 := ![u17, v17]
theorem Q17_rel : ∀ k, pairHom s17 t17 (Q17 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q17, u17, v17, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q17_not_acTrivial : ¬ ACEquiv Q17 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q17 (pairHom s17 t17) Q17_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BAbABa` and `BBBAbbA`, witness in `S5`. -/
def s18 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t18 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u18 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v18 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def Q18 : Presentation 2 := ![u18, v18]
theorem Q18_rel : ∀ k, pairHom s18 t18 (Q18 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q18, u18, v18, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q18_not_acTrivial : ¬ ACEquiv Q18 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q18 (pairHom s18 t18) Q18_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BAbAbA` and `BBaaaaa`, witness in `S5`. -/
def s19 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t19 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (3 : Fin 5) 4)
def u19 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def v19 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0
def Q19 : Presentation 2 := ![u19, v19]
theorem Q19_rel : ∀ k, pairHom s19 t19 (Q19 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q19, u19, v19, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q19_not_acTrivial : ¬ ACEquiv Q19 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q19 (pairHom s19 t19) Q19_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BBAbA` and `BAAABaba`, witness in `S5`. -/
def s20 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t20 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4)
def u20 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def v20 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def Q20 : Presentation 2 := ![u20, v20]
theorem Q20_rel : ∀ k, pairHom s20 t20 (Q20 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q20, u20, v20, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q20_not_acTrivial : ¬ ACEquiv Q20 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q20 (pairHom s20 t20) Q20_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BBAbA` and `BBBAAAAA`, witness in `S5`. -/
def s21 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t21 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4)
def u21 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def v21 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹
def Q21 : Presentation 2 := ![u21, v21]
theorem Q21_rel : ∀ k, pairHom s21 t21 (Q21 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q21, u21, v21, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q21_not_acTrivial : ¬ ACEquiv Q21 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q21 (pairHom s21 t21) Q21_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BBaba` and `BAbABaaa`, witness in `S5`. -/
def s22 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t22 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 4) * (Equiv.swap (2 : Fin 5) 4)
def u22 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v22 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0
def Q22 : Presentation 2 := ![u22, v22]
theorem Q22_rel : ∀ k, pairHom s22 t22 (Q22 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q22, u22, v22, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q22_not_acTrivial : ¬ ACEquiv Q22 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q22 (pairHom s22 t22) Q22_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 13, relators `BBaba` and `BBBaaaaa`, witness in `S5`. -/
def s23 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t23 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 4) * (Equiv.swap (2 : Fin 5) 4)
def u23 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v23 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0
def Q23 : Presentation 2 := ![u23, v23]
theorem Q23_rel : ∀ k, pairHom s23 t23 (Q23 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q23, u23, v23, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q23_not_acTrivial : ¬ ACEquiv Q23 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q23 (pairHom s23 t23) Q23_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BAABa` and `BBAbababA`, witness in `S5`. -/
def s24 : Equiv.Perm (Fin 5) := (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t24 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u24 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v24 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def Q24 : Presentation 2 := ![u24, v24]
theorem Q24_rel : ∀ k, pairHom s24 t24 (Q24 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q24, u24, v24, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q24_not_acTrivial : ¬ ACEquiv Q24 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q24 (pairHom s24 t24) Q24_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BAABa` and `BBBBBBAbA`, witness in `S7`. -/
def s25 : Equiv.Perm (Fin 7) := (Equiv.swap (1 : Fin 7) 3) * (Equiv.swap (2 : Fin 7) 4) * (Equiv.swap (3 : Fin 7) 5) * (Equiv.swap (4 : Fin 7) 6)
def t25 : Equiv.Perm (Fin 7) := (Equiv.swap (0 : Fin 7) 1) * (Equiv.swap (1 : Fin 7) 3) * (Equiv.swap (2 : Fin 7) 5) * (Equiv.swap (3 : Fin 7) 4) * (Equiv.swap (4 : Fin 7) 6) * (Equiv.swap (5 : Fin 7) 6)
def u25 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def v25 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def Q25 : Presentation 2 := ![u25, v25]
theorem Q25_rel : ∀ k, pairHom s25 t25 (Q25 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q25, u25, v25, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q25_not_acTrivial : ¬ ACEquiv Q25 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q25 (pairHom s25 t25) Q25_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BAABaaa` and `BAbABaa`, witness in `S5`. -/
def s26 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t26 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u26 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0
def v26 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def Q26 : Presentation 2 := ![u26, v26]
theorem Q26_rel : ∀ k, pairHom s26 t26 (Q26 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q26, u26, v26, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q26_not_acTrivial : ¬ ACEquiv Q26 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q26 (pairHom s26 t26) Q26_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BAABaba` and `BAAABaa`, witness in `S5`. -/
def s27 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t27 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u27 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v27 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def Q27 : Presentation 2 := ![u27, v27]
theorem Q27_rel : ∀ k, pairHom s27 t27 (Q27 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q27, u27, v27, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q27_not_acTrivial : ¬ ACEquiv Q27 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q27 (pairHom s27 t27) Q27_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BABaa` and `BBBBBBaba`, witness in `S7`. -/
def s28 : Equiv.Perm (Fin 7) := (Equiv.swap (1 : Fin 7) 3) * (Equiv.swap (2 : Fin 7) 4) * (Equiv.swap (3 : Fin 7) 5) * (Equiv.swap (4 : Fin 7) 6)
def t28 : Equiv.Perm (Fin 7) := (Equiv.swap (0 : Fin 7) 1) * (Equiv.swap (1 : Fin 7) 4) * (Equiv.swap (2 : Fin 7) 6) * (Equiv.swap (3 : Fin 7) 4) * (Equiv.swap (4 : Fin 7) 6) * (Equiv.swap (5 : Fin 7) 6)
def u28 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def v28 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def Q28 : Presentation 2 := ![u28, v28]
theorem Q28_rel : ∀ k, pairHom s28 t28 (Q28 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q28, u28, v28, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q28_not_acTrivial : ¬ ACEquiv Q28 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q28 (pairHom s28 t28) Q28_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BABaa` and `BBabAbAba`, witness in `S5`. -/
def s29 : Equiv.Perm (Fin 5) := (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t29 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u29 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def v29 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0
def Q29 : Presentation 2 := ![u29, v29]
theorem Q29_rel : ∀ k, pairHom s29 t29 (Q29 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q29, u29, v29, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q29_not_acTrivial : ¬ ACEquiv Q29 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q29 (pairHom s29 t29) Q29_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BBAbA` and `BAAAAAABa`, witness in `S7`. -/
def s30 : Equiv.Perm (Fin 7) := (Equiv.swap (0 : Fin 7) 1) * (Equiv.swap (1 : Fin 7) 3) * (Equiv.swap (2 : Fin 7) 5) * (Equiv.swap (3 : Fin 7) 5) * (Equiv.swap (4 : Fin 7) 5) * (Equiv.swap (5 : Fin 7) 6)
def t30 : Equiv.Perm (Fin 7) := (Equiv.swap (1 : Fin 7) 6) * (Equiv.swap (2 : Fin 7) 5) * (Equiv.swap (3 : Fin 7) 5) * (Equiv.swap (4 : Fin 7) 6)
def u30 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def v30 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0
def Q30 : Presentation 2 := ![u30, v30]
theorem Q30_rel : ∀ k, pairHom s30 t30 (Q30 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q30, u30, v30, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q30_not_acTrivial : ¬ ACEquiv Q30 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q30 (pairHom s30 t30) Q30_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BBAbA` and `BABAbaabA`, witness in `S5`. -/
def s31 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t31 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4)
def u31 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def v31 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def Q31 : Presentation 2 := ![u31, v31]
theorem Q31_rel : ∀ k, pairHom s31 t31 (Q31 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q31, u31, v31, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q31_not_acTrivial : ¬ ACEquiv Q31 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q31 (pairHom s31 t31) Q31_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BBAbabA` and `BAABaba`, witness in `S5`. -/
def s32 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t32 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u32 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def v32 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def Q32 : Presentation 2 := ![u32, v32]
theorem Q32_rel : ∀ k, pairHom s32 t32 (Q32 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q32, u32, v32, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q32_not_acTrivial : ¬ ACEquiv Q32 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q32 (pairHom s32 t32) Q32_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BBBAbbA` and `BBAbabA`, witness in `S5`. -/
def s33 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t33 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 3) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def u33 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def v33 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹
def Q33 : Presentation 2 := ![u33, v33]
theorem Q33_rel : ∀ k, pairHom s33 t33 (Q33 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q33, u33, v33, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q33_not_acTrivial : ¬ ACEquiv Q33 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q33 (pairHom s33 t33) Q33_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BBBabba` and `BBabAba`, witness in `S5`. -/
def s34 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t34 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u34 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 1 * FreeGroup.of 0
def v34 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0
def Q34 : Presentation 2 := ![u34, v34]
theorem Q34_rel : ∀ k, pairHom s34 t34 (Q34 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q34, u34, v34, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q34_not_acTrivial : ¬ ACEquiv Q34 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q34 (pairHom s34 t34) Q34_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BBabAba` and `BAbABaa`, witness in `S5`. -/
def s35 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t35 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 2) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 4) * (Equiv.swap (3 : Fin 5) 4)
def u35 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 0
def v35 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def Q35 : Presentation 2 := ![u35, v35]
theorem Q35_rel : ∀ k, pairHom s35 t35 (Q35 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q35, u35, v35, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q35_not_acTrivial : ¬ ACEquiv Q35 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q35 (pairHom s35 t35) Q35_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BBaba` and `BABaaaaaa`, witness in `S7`. -/
def s36 : Equiv.Perm (Fin 7) := (Equiv.swap (0 : Fin 7) 1) * (Equiv.swap (1 : Fin 7) 3) * (Equiv.swap (2 : Fin 7) 5) * (Equiv.swap (3 : Fin 7) 5) * (Equiv.swap (4 : Fin 7) 5) * (Equiv.swap (5 : Fin 7) 6)
def t36 : Equiv.Perm (Fin 7) := (Equiv.swap (1 : Fin 7) 4) * (Equiv.swap (2 : Fin 7) 3) * (Equiv.swap (3 : Fin 7) 5) * (Equiv.swap (4 : Fin 7) 6)
def u36 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v36 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 0
def Q36 : Presentation 2 := ![u36, v36]
theorem Q36_rel : ∀ k, pairHom s36 t36 (Q36 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q36, u36, v36, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q36_not_acTrivial : ¬ ACEquiv Q36 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q36 (pairHom s36 t36) Q36_rel (a := 0) ?_
  rw [pairHom_zero]
  decide

/-- total relator length 14, relators `BBaba` and `BAbAbABaa`, witness in `S5`. -/
def s37 : Equiv.Perm (Fin 5) := (Equiv.swap (0 : Fin 5) 1) * (Equiv.swap (1 : Fin 5) 2) * (Equiv.swap (2 : Fin 5) 3) * (Equiv.swap (3 : Fin 5) 4)
def t37 : Equiv.Perm (Fin 5) := (Equiv.swap (1 : Fin 5) 4) * (Equiv.swap (2 : Fin 5) 4)
def u37 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0
def v37 : Word 2 := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0
def Q37 : Presentation 2 := ![u37, v37]
theorem Q37_rel : ∀ k, pairHom s37 t37 (Q37 k) = 1 := by
  intro k
  fin_cases k <;> simp [Q37, u37, v37, pairHom_zero, pairHom_one, map_mul] <;> decide
theorem Q37_not_acTrivial : ¬ ACEquiv Q37 (standard 2) := by
  refine not_acEquiv_standard_of_witness Q37 (pairHom s37 t37) Q37_rel (a := 0) ?_
  rw [pairHom_zero]
  decide
/-! ## Checker demonstrations and tamper controls -/

theorem Q0_via_checker : ¬ ACEquiv Q0 (standard 2) :=
  checkWitness_sound (P := Q0) (s := s0) (t := t0) (by decide)

theorem Q3_via_checker : ¬ ACEquiv Q3 (standard 2) :=
  checkWitness_sound (P := Q3) (s := s3) (t := t3) (by decide)

theorem Q25_via_checker : ¬ ACEquiv Q25 (standard 2) :=
  checkWitness_sound (P := Q25) (s := s25) (t := t25) (by decide)

theorem Q28_via_checker : ¬ ACEquiv Q28 (standard 2) :=
  checkWitness_sound (P := Q28) (s := s28) (t := t28) (by decide)

theorem Q36_via_checker : ¬ ACEquiv Q36 (standard 2) :=
  checkWitness_sound (P := Q36) (s := s36) (t := t36) (by decide)

theorem Q37_via_checker : ¬ ACEquiv Q37 (standard 2) :=
  checkWitness_sound (P := Q37) (s := s37) (t := t37) (by decide)

/-- Positive control for the checker on a row it must accept. -/
example : checkWitness Q0 s0 t0 = true := by decide

/-- Tamper control: squaring the first permutation spoils the witness. -/
example : checkWitness Q0 (s0 * s0) t0 = false := by decide

/-- Tamper control: squaring the second permutation spoils the witness. -/
example : checkWitness Q3 s3 (t3 * t3) = false := by decide

/-- Tamper control: the identity pair is rejected although it kills both relators. -/
example : checkWitness Q3 (1 : Equiv.Perm (Fin 5)) 1 = false := by decide
/-! ## Axiom audit -/

#print axioms nclRange_standard
#print axioms not_acEquiv_standard_of_witness
#print axioms not_acEquiv_standard_of_not_subsingleton
#print axioms checkWitness_sound
#print axioms Q0_not_acTrivial
#print axioms Q1_not_acTrivial
#print axioms Q2_not_acTrivial
#print axioms Q3_not_acTrivial
#print axioms Q4_not_acTrivial
#print axioms Q5_not_acTrivial
#print axioms Q6_not_acTrivial
#print axioms Q7_not_acTrivial
#print axioms Q8_not_acTrivial
#print axioms Q9_not_acTrivial
#print axioms Q10_not_acTrivial
#print axioms Q11_not_acTrivial
#print axioms Q12_not_acTrivial
#print axioms Q13_not_acTrivial
#print axioms Q14_not_acTrivial
#print axioms Q15_not_acTrivial
#print axioms Q16_not_acTrivial
#print axioms Q17_not_acTrivial
#print axioms Q18_not_acTrivial
#print axioms Q19_not_acTrivial
#print axioms Q20_not_acTrivial
#print axioms Q21_not_acTrivial
#print axioms Q22_not_acTrivial
#print axioms Q23_not_acTrivial
#print axioms Q24_not_acTrivial
#print axioms Q25_not_acTrivial
#print axioms Q26_not_acTrivial
#print axioms Q27_not_acTrivial
#print axioms Q28_not_acTrivial
#print axioms Q29_not_acTrivial
#print axioms Q30_not_acTrivial
#print axioms Q31_not_acTrivial
#print axioms Q32_not_acTrivial
#print axioms Q33_not_acTrivial
#print axioms Q34_not_acTrivial
#print axioms Q35_not_acTrivial
#print axioms Q36_not_acTrivial
#print axioms Q37_not_acTrivial
#print axioms Q0_via_checker
#print axioms Q3_via_checker
#print axioms Q25_via_checker
#print axioms Q28_via_checker
#print axioms Q36_via_checker
#print axioms Q37_via_checker

end AndrewsCurtis
