/-
# The Metzler recipe's parameter boundary: the group-theoretic obstruction

`toolkit/lean/AC8.lean` proves the recipe

    metzler_recipe (k m t j) (hk : k = 1 + t * j) :
      ∃ ms : List QMove, replay ms (metz k m 1) = some (metz k m j)

for the presentations `metz k m j = <x,y | y^m, [x^j,y], x^k>`: it moves `metz k m 1` to
`metz k m j` whenever `j ∣ k - 1`.  This file is about the other side of that hypothesis.

This is the pure group-theory file: it imports nothing from the campaign, so it elaborates in
seconds.  `MetzlerSharpBridge.lean` transfers the statements to the campaign's `AC5.QPres` /
`QSound.QEquiv` layer and adds the checker corollary.

## Results

* `abelian_metz_one` : for every `k m` the group presented by `metz k m 1` is abelian (the
  relation `[x,y] = 1` alone forces it).
* `abelian_of_coprime` : if `Nat.Coprime j k` then the group presented by `metz k m j` is
  abelian too, so the group invariant cannot obstruct the recipe there.
* `not_commutative_four_even` : if `m` and `j` are both even then `metz 4 m j` presents a
  NON-abelian group.  Witness: the dihedral group of order eight with `x ↦ r`, `y ↦ s`;
  `s^m = 1` for even `m`, and `r^j` is central for even `j`, so the relation `[x^j,y] = 1`
  holds, while `r` and `s` do not commute.
* `not_mulEquiv_four_even` : hence `metz 4 m 1` and `metz 4 m j` present NON-isomorphic
  groups for even `m, j` — so no chain of group-preserving moves (in particular no `Q**`
  chain and no Andrews-Curtis chain, whatever its length or intermediate size) joins them.
  Every even `j` is outside the recipe's hypothesis at `k = 4` (which needs `j ∣ 3`), so at
  `k = 4` the hypothesis fails exactly on the half refuted here.
* `same_abelianisation` : the exponent-sum matrices of `metz 4 2 1` and `metz 4 2 2` are
  equal, so the campaign's only implemented invariant (the Smith normal form of the
  exponent-sum matrix) cannot see this obstruction: the obstruction is strictly finer.

Nothing here proves or disproves the Andrews-Curtis conjecture.
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

namespace MetzlerSharp

/-- The word `x^j * y * x^-j * y^-1`, i.e. the commutator `[x^j, y]`. -/
def com (j : Nat) : FreeGroup (Fin 2) :=
  (FreeGroup.of 0) ^ j * FreeGroup.of 1 * ((FreeGroup.of 0) ^ j)⁻¹ * (FreeGroup.of 1)⁻¹

/-- The relator list `<x,y | y^m, [x^j,y], x^k>` of `AC8.metz`, in `AC8`'s relator order. -/
def metzRels (k m j : Nat) : Fin 3 → FreeGroup (Fin 2) :=
  fun i => if i = 0 then (FreeGroup.of 1) ^ m
    else if i = 1 then com j
    else (FreeGroup.of 0) ^ k

@[simp] theorem metzRels_zero (k m j : Nat) :
    metzRels k m j 0 = (FreeGroup.of 1) ^ m := rfl

@[simp] theorem metzRels_one (k m j : Nat) : metzRels k m j 1 = com j := rfl

@[simp] theorem metzRels_two (k m j : Nat) :
    metzRels k m j 2 = (FreeGroup.of 0) ^ k := rfl

/-- The group presented by `metz k m j`. -/
abbrev G (k m j : Nat) : Type := PresentedGroup (Set.range (metzRels k m j))

/-- The image of the generator `x`. -/
def X (k m j : Nat) : G k m j := PresentedGroup.of 0

/-- The image of the generator `y`. -/
def Y (k m j : Nat) : G k m j := PresentedGroup.of 1

/-! ## Reading the relators in the group -/

/-- The image of a relator is trivial. -/
theorem mk_rels (k m j : Nat) (i : Fin 3) :
    PresentedGroup.mk (Set.range (metzRels k m j)) (metzRels k m j i) = 1 :=
  PresentedGroup.one_of_mem (Set.mem_range_self i)

theorem mk_y_pow (k m j : Nat) :
    PresentedGroup.mk (Set.range (metzRels k m j)) ((FreeGroup.of 1) ^ m) = 1 := by
  rw [← metzRels_zero]
  exact mk_rels k m j 0

theorem mk_com (k m j : Nat) :
    PresentedGroup.mk (Set.range (metzRels k m j)) (com j) = 1 := by
  rw [← metzRels_one]
  exact mk_rels k m j 1

theorem mk_x_pow (k m j : Nat) :
    PresentedGroup.mk (Set.range (metzRels k m j)) ((FreeGroup.of 0) ^ k) = 1 := by
  rw [← metzRels_two]
  exact mk_rels k m j 2

/-- `Y^m = 1` in the presented group. -/
theorem Y_pow (k m j : Nat) : (Y k m j) ^ m = 1 := by
  have h := mk_y_pow k m j
  rwa [map_pow] at h

/-- `X^k = 1` in the presented group. -/
theorem X_pow (k m j : Nat) : (X k m j) ^ k = 1 := by
  have h := mk_x_pow k m j
  rwa [map_pow] at h

/-- The commutator relator, read in the group: `X^j` and `Y` commute. -/
theorem commute_X_pow_Y (k m j : Nat) : Commute ((X k m j) ^ j) (Y k m j) := by
  have h := mk_com k m j
  simp only [com, map_mul, map_inv, map_pow] at h
  have h1 : (X k m j) ^ j * (Y k m j) * ((X k m j) ^ j)⁻¹ * (Y k m j)⁻¹ = 1 := by
    simpa only [X, Y, PresentedGroup.of] using h
  have h' : (X k m j) ^ j * (Y k m j) = (Y k m j) * (X k m j) ^ j := by
    conv_lhs => rw [show (X k m j) ^ j * Y k m j
        = ((X k m j) ^ j * Y k m j * ((X k m j) ^ j)⁻¹ * (Y k m j)⁻¹)
            * (Y k m j * (X k m j) ^ j) from by group]
    rw [h1, one_mul]
  exact h'

/-! ## Abelianness from commuting generators -/

/-- If the two generator images commute, the presented group is abelian. -/
theorem abelian_of_commute_gens (k m j : Nat) (hXY : Commute (X k m j) (Y k m j)) :
    ∀ u v : G k m j, u * v = v * u := by
  -- the elements that commute with everything form a subgroup
  let H : Subgroup (G k m j) :=
    { carrier := {u | ∀ v, Commute u v}
      one_mem' := by intro v; exact Commute.one_left v
      mul_mem' := by intro a b ha hb v; exact (ha v).mul_left (hb v)
      inv_mem' := by intro a ha v; exact (ha v).inv_left }
  have hX : X k m j ∈ H := by
    intro v
    induction v using PresentedGroup.induction_on with
    | _ z =>
      refine FreeGroup.induction_on z ?_ ?_ ?_ ?_
      · exact Commute.one_right _
      · intro a
        fin_cases a
        · exact Commute.refl _
        · exact hXY
      · intro a ih
        exact ih.inv_right
      · intro a b iha ihb
        exact iha.mul_right ihb
  have hY : Y k m j ∈ H := by
    intro v
    induction v using PresentedGroup.induction_on with
    | _ z =>
      refine FreeGroup.induction_on z ?_ ?_ ?_ ?_
      · exact Commute.one_right _
      · intro a
        fin_cases a
        · exact hXY.symm
        · exact Commute.refl _
      · intro a ih
        exact ih.inv_right
      · intro a b iha ihb
        exact iha.mul_right ihb
  intro u v
  have hu : u ∈ H :=
    PresentedGroup.generated_by (Set.range (metzRels k m j)) H
      (fun i => by fin_cases i; exact hX; exact hY) u
  exact (hu v).eq

/-- For every `k m` the presentation `metz k m 1` presents an abelian group. -/
theorem abelian_metz_one (k m : Nat) : ∀ u v : G k m 1, u * v = v * u := by
  apply abelian_of_commute_gens
  simpa using commute_X_pow_Y k m 1

/-! ## The coprime case: the group invariant cannot obstruct -/

/-- **Bézout, in the form used below.** -/
theorem bezout_int (j k : Nat) (h : Nat.Coprime j k) :
    (j : ℤ) * Int.gcdA (j : ℤ) (k : ℤ) + (k : ℤ) * Int.gcdB (j : ℤ) (k : ℤ) = 1 := by
  have h1 := Int.gcd_eq_gcd_ab (j : ℤ) (k : ℤ)
  rw [Int.gcd_natCast_natCast, h] at h1
  simpa using h1.symm

/-- If `gcd(j,k) = 1`, the generator images commute: `X` is a power of the central `X^j`. -/
theorem commute_gens_of_coprime (k m j : Nat) (h : Nat.Coprime j k) :
    Commute (X k m j) (Y k m j) := by
  have hbez := bezout_int j k h
  have hkj : Commute ((X k m j) ^ j) (Y k m j) := commute_X_pow_Y k m j
  have hkY : Commute ((X k m j) ^ k) (Y k m j) := by
    rw [X_pow]
    exact Commute.one_left _
  have hXeq : X k m j
      = ((X k m j) ^ j) ^ (Int.gcdA (j : ℤ) (k : ℤ)) *
        ((X k m j) ^ k) ^ (Int.gcdB (j : ℤ) (k : ℤ)) := by
    simp only [← zpow_natCast]
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, hbez]
    simp
  have hcomm : Commute (((X k m j) ^ j) ^ (Int.gcdA (j : ℤ) (k : ℤ)) *
      ((X k m j) ^ k) ^ (Int.gcdB (j : ℤ) (k : ℤ))) (Y k m j) :=
    (hkj.zpow_left _).mul_left (hkY.zpow_left _)
  rwa [← hXeq] at hcomm

/-- If `gcd(j,k) = 1` the presentation `metz k m j` presents an abelian group. -/
theorem abelian_of_coprime (k m j : Nat) (h : Nat.Coprime j k) :
    ∀ u v : G k m j, u * v = v * u :=
  abelian_of_commute_gens k m j (commute_gens_of_coprime k m j h)

/-- **The recipe's hypothesis forces coprimality**: `k = 1 + t*j` implies `gcd(j,k) = 1`.
So the recipe never enters the region where the group invariant obstructs, and by
`abelian_of_coprime` its target group is always abelian. -/
theorem coprime_of_recipe_hypothesis {k j t : Nat} (hk : k = 1 + t * j) : Nat.Coprime j k := by
  rw [hk, Nat.coprime_add_mul_right_right]
  exact Nat.coprime_one_right j

/-- At `k = 4` the recipe's hypothesis `j ∣ k - 1 = 3` excludes every even `j`. -/
theorem four_ne_one_add_mul (j t : Nat) (hj : Even j) : 4 ≠ 1 + t * j := by
  intro h
  have h1 : 1 + 3 = 1 + t * j := by rw [← h]
  have h3 : 3 = t * j := Nat.add_left_cancel h1
  have hjt : j * t = 3 := by rw [mul_comm]; exact h3.symm
  have hdvd : 2 ∣ 3 := (even_iff_two_dvd.mp hj).trans ⟨t, hjt.symm⟩
  norm_num at hdvd

/-! ## The dihedral witness: `metz 4 m j` is non-abelian for even `m`, `j` -/

/-- The images used in the dihedral witness: `x ↦ r`, `y ↦ sr`. -/
def fD : Fin 2 → DihedralGroup 4 :=
  fun i => if i = 0 then DihedralGroup.r 1 else DihedralGroup.sr 0

theorem fD_zero : fD 0 = DihedralGroup.r 1 := rfl

theorem fD_one : fD 1 = DihedralGroup.sr 0 := rfl

theorem sr_pow_eq_one (m : Nat) (hm : Even m) :
    (DihedralGroup.sr 0 : DihedralGroup 4) ^ m = 1 := by
  obtain ⟨t, rfl⟩ := hm
  rw [← two_mul, pow_mul]
  rw [show (DihedralGroup.sr 0 : DihedralGroup 4) ^ 2 = 1 by decide]
  exact one_pow t

/-- For even `j`, `r^j` is central in the dihedral group of order eight. -/
theorem commute_r_pow_sr (j : Nat) (hj : Even j) :
    Commute ((DihedralGroup.r 1 : DihedralGroup 4) ^ j) (DihedralGroup.sr 0) := by
  obtain ⟨t, rfl⟩ := hj
  rw [← two_mul, pow_mul]
  have h2 : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 * DihedralGroup.sr 0 =
      DihedralGroup.sr 0 * (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 := by decide
  have h2c : Commute ((DihedralGroup.r 1 : DihedralGroup 4) ^ 2) (DihedralGroup.sr 0) := h2
  exact h2c.pow_left t

/-- A trivial commutator from a commuting pair. -/
theorem comm_mul_inv_eq_one {Gr : Type} [Group Gr] {a b : Gr} (h : Commute a b) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [h.eq]
  group

/-- The map `G 4 m j →* DihedralGroup 4`, `x ↦ r`, `y ↦ sr`, for even `m` and `j`. -/
def toDihedral (m j : Nat) (hm : Even m) (hj : Even j) : G 4 m j →* DihedralGroup 4 :=
  PresentedGroup.toGroup (rels := Set.range (metzRels 4 m j)) (f := fD) (by
    intro r hr
    obtain ⟨i, rfl⟩ := hr
    fin_cases i
    · change FreeGroup.lift fD (metzRels 4 m j 0) = 1
      rw [metzRels_zero]
      simp only [map_pow, FreeGroup.lift_apply_of, fD_one]
      exact sr_pow_eq_one m hm
    · change FreeGroup.lift fD (metzRels 4 m j 1) = 1
      rw [metzRels_one]
      simp only [com, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, fD_zero, fD_one]
      exact comm_mul_inv_eq_one (commute_r_pow_sr j hj)
    · change FreeGroup.lift fD (metzRels 4 m j 2) = 1
      rw [metzRels_two]
      simp only [map_pow, FreeGroup.lift_apply_of, fD_zero]
      decide)

/-- For even `m, j` the presentation `metz 4 m j` presents a non-abelian group. -/
theorem not_commutative_four_even (m j : Nat) (hm : Even m) (hj : Even j) :
    ¬ ∀ u v : G 4 m j, u * v = v * u := by
  intro h
  have hXY : X 4 m j * Y 4 m j = Y 4 m j * X 4 m j := h _ _
  have himg : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.sr 0
      = DihedralGroup.sr 0 * DihedralGroup.r 1 := by
    have hc := congrArg (toDihedral m j hm hj) hXY
    simpa [map_mul, toDihedral, X, Y, fD] using hc
  exact absurd himg (by decide)

/-- **The obstruction.** For even `m` and `j`, `metz 4 m 1` and `metz 4 m j` present
non-isomorphic groups, so no group-preserving transformation joins them. -/
theorem not_mulEquiv_four_even (m j : Nat) (hm : Even m) (hj : Even j) :
    ¬ Nonempty (G 4 m 1 ≃* G 4 m j) := by
  rintro ⟨e⟩
  have hab : ∀ u v : G 4 m j, u * v = v * u := by
    intro u v
    obtain ⟨a, rfl⟩ := e.surjective u
    obtain ⟨b, rfl⟩ := e.surjective v
    rw [← e.map_mul, abelian_metz_one 4 m a b, e.map_mul]
  exact not_commutative_four_even m j hm hj hab

theorem even_two : Even 2 := ⟨1, rfl⟩

theorem even_four : Even 4 := ⟨2, rfl⟩

/-- The pair `(k,m,j) = (4,2,1)` versus `(4,2,2)`: not equivalent. -/
theorem not_mulEquiv_four_two_two : ¬ Nonempty (G 4 2 1 ≃* G 4 2 2) :=
  not_mulEquiv_four_even 2 2 even_two even_two

theorem not_mulEquiv_four_two_four : ¬ Nonempty (G 4 2 1 ≃* G 4 2 4) :=
  not_mulEquiv_four_even 2 4 even_two even_four

theorem not_mulEquiv_four_four_two : ¬ Nonempty (G 4 4 1 ≃* G 4 4 2) :=
  not_mulEquiv_four_even 4 2 even_four even_two

/-! ## The general dihedral obstruction: `k ≥ 3`, `m` even, `k ∣ 2j` -/

/-- The images used in the dihedral witness, general `k`: `x ↦ r`, `y ↦ sr`. -/
def fDK (k : Nat) : Fin 2 → DihedralGroup k :=
  fun i => if i = 0 then DihedralGroup.r 1 else DihedralGroup.sr 0

theorem fDK_zero (k : Nat) : fDK k 0 = DihedralGroup.r 1 := rfl

theorem fDK_one (k : Nat) : fDK k 1 = DihedralGroup.sr 0 := rfl

/-- `sr^m = 1` in any dihedral group, for even `m`. -/
theorem sr_pow_eq_one_k (k m : Nat) (hm : Even m) :
    (DihedralGroup.sr 0 : DihedralGroup k) ^ m = 1 := by
  obtain ⟨t, rfl⟩ := hm
  rw [← two_mul, pow_mul, show (DihedralGroup.sr 0 : DihedralGroup k) ^ 2 = 1 by
    rw [pow_two, DihedralGroup.sr_mul_self]]
  exact one_pow t

section General

variable {k : Nat}

/-- In `DihedralGroup k`, `r^j` is central modulo the reflection when `k ∣ 2j`. -/
theorem commute_r_pow_sr_of_dvd (j : Nat) (hdvd : k ∣ 2 * j) :
    Commute ((DihedralGroup.r 1 : DihedralGroup k) ^ j) (DihedralGroup.sr 0) := by
  have hzero : ((2 * j : Nat) : ZMod k) = 0 :=
    (ZMod.natCast_eq_zero_iff (2 * j) k).mpr hdvd
  have hsum : ((j : Nat) : ZMod k) + ((j : Nat) : ZMod k) = 0 := by
    rw [← Nat.cast_add, show j + j = 2 * j from by ring]; exact hzero
  rw [DihedralGroup.r_one_pow]
  show DihedralGroup.r ((j : Nat) : ZMod k) * DihedralGroup.sr 0 =
    DihedralGroup.sr 0 * DihedralGroup.r ((j : Nat) : ZMod k)
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, zero_sub, zero_add]
  congr 1
  exact neg_eq_iff_add_eq_zero.mpr hsum

/-- In `DihedralGroup k` with `k ≥ 3`, the rotation and the reflection do not commute. -/
theorem r_mul_sr_ne (hk : 3 ≤ k) :
    (DihedralGroup.r 1 : DihedralGroup k) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1 := by
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, zero_sub, zero_add]
  intro h
  injection h with h1
  have h2' : ((1 : ZMod k) + 1) = 0 := by
    have hh := congrArg (fun t : ZMod k => t + 1) h1
    simpa using hh.symm
  have h2 : ((2 : Nat) : ZMod k) = 0 := by
    rw [show ((2 : Nat) : ZMod k) = (1 : ZMod k) + 1 from by push_cast; ring]
    exact h2'
  have h3 : k ∣ 2 := (ZMod.natCast_eq_zero_iff 2 k).mp h2
  have h4 : k ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  exact absurd (Nat.le_trans hk h4) (by norm_num)

end General

/-- The map `G k m j →* DihedralGroup k`, `x ↦ r`, `y ↦ sr`, for even `m` and `k ∣ 2j`. -/
def toDihedralK (k m j : Nat) (hm : Even m) (hdvd : k ∣ 2 * j) : G k m j →* DihedralGroup k :=
  PresentedGroup.toGroup (rels := Set.range (metzRels k m j)) (f := fDK k) (by
    intro r hr
    obtain ⟨i, rfl⟩ := hr
    fin_cases i
    · change FreeGroup.lift (fDK k) (metzRels k m j 0) = 1
      rw [metzRels_zero]
      simp only [map_pow, FreeGroup.lift_apply_of, fDK_one]
      exact sr_pow_eq_one_k k m hm
    · change FreeGroup.lift (fDK k) (metzRels k m j 1) = 1
      rw [metzRels_one]
      simp only [com, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, fDK_zero, fDK_one]
      exact comm_mul_inv_eq_one (commute_r_pow_sr_of_dvd j hdvd)
    · change FreeGroup.lift (fDK k) (metzRels k m j 2) = 1
      rw [metzRels_two]
      simp only [map_pow, FreeGroup.lift_apply_of, fDK_zero]
      rw [DihedralGroup.r_one_pow, ZMod.natCast_self]
      rfl)

/-- For even `m` and `k ≥ 3` with `k ∣ 2j`, the presentation `metz k m j` presents a non-abelian
group (the dihedral quotient of order `2k`). -/
theorem not_commutative_dihedral (k m j : Nat) (hk : 3 ≤ k) (hm : Even m) (hdvd : k ∣ 2 * j) :
    ¬ ∀ u v : G k m j, u * v = v * u := by
  intro h
  have hXY : X k m j * Y k m j = Y k m j * X k m j := h _ _
  have himg : (DihedralGroup.r 1 : DihedralGroup k) * DihedralGroup.sr 0
      = DihedralGroup.sr 0 * DihedralGroup.r 1 := by
    have hc := congrArg (toDihedralK k m j hm hdvd) hXY
    simpa [map_mul, toDihedralK, X, Y, fDK] using hc
  exact r_mul_sr_ne hk himg

/-- **The general obstruction.** For even `m`, `k ≥ 3` and `k ∣ 2j`, the presentations
`metz k m 1` and `metz k m j` are not isomorphic, hence not connected by any group-preserving
move list. -/
theorem not_mulEquiv_dihedral (k m j : Nat) (hk : 3 ≤ k) (hm : Even m) (hdvd : k ∣ 2 * j) :
    ¬ Nonempty (G k m 1 ≃* G k m j) := by
  rintro ⟨e⟩
  have hab : ∀ u v : G k m j, u * v = v * u := by
    intro u v
    obtain ⟨a, rfl⟩ := e.surjective u
    obtain ⟨b, rfl⟩ := e.surjective v
    rw [← e.map_mul, abelian_metz_one k m a b, e.map_mul]
  exact not_commutative_dihedral k m j hk hm hdvd hab

/-! ## The obstruction is finer than the abelianisation -/

/-- Exponent sums, as a monoid homomorphism `F_n → (ℤ)^n`: the abelianisation map. -/
def expHom (n : Nat) : FreeGroup (Fin n) →* Multiplicative (Fin n → ℤ) :=
  FreeGroup.lift (fun g => Multiplicative.ofAdd (Pi.single g (1 : ℤ)))

/-- The exponent-sum vector of a word. -/
def expSumWord {n : Nat} (w : FreeGroup (Fin n)) : Fin n → ℤ :=
  Multiplicative.toAdd (expHom n w)

theorem expSumWord_of {n : Nat} (g h : Fin n) :
    expSumWord (FreeGroup.of g) h = if h = g then 1 else 0 := by
  simp [expSumWord, expHom, Pi.single_apply, eq_comm]

theorem expSumWord_one {n : Nat} (h : Fin n) : expSumWord (1 : FreeGroup (Fin n)) h = 0 := by
  simp [expSumWord]

theorem expSumWord_mul {n : Nat} (a b : FreeGroup (Fin n)) (h : Fin n) :
    expSumWord (a * b) h = expSumWord a h + expSumWord b h := by
  simp [expSumWord, map_mul, Pi.add_apply]

theorem expSumWord_inv {n : Nat} (a : FreeGroup (Fin n)) (h : Fin n) :
    expSumWord (a⁻¹) h = - expSumWord a h := by
  simp [expSumWord, map_inv]

theorem expSumWord_pow {n : Nat} (a : FreeGroup (Fin n)) (m : Nat) (h : Fin n) :
    expSumWord (a ^ m) h = m * expSumWord a h := by
  simp [expSumWord, map_pow, nsmul_eq_mul]

/-- The exponent-sum matrix (the abelianisation data) of the presentation `metz k m j`. -/
def expSum (k m j : Nat) : Fin 3 → Fin 2 → ℤ :=
  fun i => expSumWord (metzRels k m j i)

/-- The exponent-sum matrix does not depend on `j` at all: the middle relator `[x^j,y]` has
zero exponent sums for every `j`.  In particular `metz k m 1` and `metz k m j` have the same
exponent-sum matrix for all `j`. -/
theorem expSum_eq (k m j : Nat) (i : Fin 3) :
    expSum k m j i = fun g =>
      if i = 0 then (if g = 1 then (m : ℤ) else 0)
      else if i = 1 then 0 else if g = 0 then (k : ℤ) else 0 := by
  funext g
  fin_cases i
  · show expSumWord (metzRels k m j 0) g = if g = 1 then (m : ℤ) else 0
    rw [metzRels_zero, expSumWord_pow, expSumWord_of]
    by_cases h : g = 1 <;> simp [h]
  · show expSumWord (metzRels k m j 1) g = 0
    simp only [metzRels_one, com, expSumWord_mul, expSumWord_inv, expSumWord_pow,
      expSumWord_of]
    ring
  · show expSumWord (metzRels k m j 2) g = if g = 0 then (k : ℤ) else 0
    rw [metzRels_two, expSumWord_pow, expSumWord_of]
    by_cases h : g = 0 <;> simp [h]

/-- The two presentations of `not_mulEquiv_four_two_two` have the SAME exponent-sum matrix,
so the Smith normal form (the campaign's only implemented invariant) cannot separate them. -/
theorem same_abelianisation : expSum 4 2 1 = expSum 4 2 2 := by
  funext i
  rw [expSum_eq, expSum_eq]

/-- At fixed `k m` the exponent-sum matrix is independent of `j`, for every `j`. -/
theorem same_abelianisation_general (k m j : Nat) : expSum k m 1 = expSum k m j := by
  funext i
  rw [expSum_eq, expSum_eq]

/-- The two relator lists of `(4,2,1)` and `(4,2,2)` are different presentations (the
obstruction is not of a pair that is syntactically the same). -/
theorem metzRels_four_two_one_ne_two : metzRels 4 2 1 ≠ metzRels 4 2 2 := by
  intro h
  have h1 := congrFun h 1
  simp only [metzRels_one] at h1
  have h2 : com 1 ≠ com 2 := by decide
  exact h2 h1

/-! ## Axiom audit -/

#print axioms abelian_metz_one
#print axioms abelian_of_coprime
#print axioms coprime_of_recipe_hypothesis
#print axioms four_ne_one_add_mul
#print axioms not_commutative_four_even
#print axioms not_mulEquiv_four_even
#print axioms not_mulEquiv_four_two_two
#print axioms not_mulEquiv_four_two_four
#print axioms not_mulEquiv_four_four_two
#print axioms same_abelianisation
#print axioms same_abelianisation_general
#print axioms metzRels_four_two_one_ne_two
#print axioms commute_r_pow_sr_of_dvd
#print axioms r_mul_sr_ne
#print axioms sr_pow_eq_one_k
#print axioms not_commutative_dihedral
#print axioms not_mulEquiv_dihedral

end MetzlerSharp
