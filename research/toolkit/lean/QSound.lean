/-
Q** soundness for the Q** layer of `AC5.lean`.

`AC5.lean` checks Q**-certificates by replaying Barmak's moves (i)-(vi) as a `Bool` computed in
the kernel, but it contains no theorem that relates a passing certificate to a group-theoretic
statement.  This file supplies one: a Q**-analogue of `AC3.lean`'s `checkCert_sound`.

The invariant is the isomorphism class of the presented group.  For a `QPres` with rank `n` and
relators `r : Fin m → Word n` it is `PresentedGroup (Set.range r)`; a move is *sound* when it
carries a presentation to one presenting an isomorphic group.

Nothing in this file proves or disproves the Andrews-Curtis conjecture.
-/
import AC5

namespace AC5

attribute [local instance] Subgroup.normalClosure_normal

set_option maxHeartbeats 1000000

/-! ## The invariant: the presented group up to isomorphism -/

/-- Two `QPres` present isomorphic groups.  This is the group-theoretic reading of a Q\*\*-move
chain: the proposition that `AC5.lean`'s `checkCert` had no theorem about. -/
def QEquiv (P Q : QPres) : Prop :=
  Nonempty (PresentedGroup (Set.range P.rels) ≃* PresentedGroup (Set.range Q.rels))

theorem QEquiv.refl (P : QPres) : QEquiv P P := ⟨MulEquiv.refl _⟩

theorem QEquiv.symm {P Q : QPres} (h : QEquiv P Q) : QEquiv Q P :=
  ⟨(Classical.choice h).symm⟩

theorem QEquiv.trans {P Q R : QPres} (h₁ : QEquiv P Q) (h₂ : QEquiv Q R) : QEquiv P R :=
  ⟨(Classical.choice h₁).trans (Classical.choice h₂)⟩

/-! ## Two elementary lemmas about `PresentedGroup` -/

/-- The lifted substitution read through `PresentedGroup.mk`. -/
theorem lift_mk {n n' : Nat} (rels : Set (Word n')) (τ : Fin n → Word n') :
    ∀ u : Word n, FreeGroup.lift (fun k => PresentedGroup.mk rels (τ k)) u =
      PresentedGroup.mk rels (FreeGroup.lift τ u) := by
  intro u
  refine FreeGroup.induction_on u ?_ ?_ ?_ ?_
  · simp
  · intro a; simp
  · intro a ih; simp [ih]
  · intro x y ihx ihy; simp [ihx, ihy]

/-- The value of `PresentedGroup.toGroup` on a class. -/
theorem toGroup_mk {n : Nat} {G : Type} [Group G] (rels : Set (Word n)) (f : Fin n → G)
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (y : Word n) :
    PresentedGroup.toGroup (rels := rels) (f := f) h (PresentedGroup.mk rels y) =
      FreeGroup.lift f y := rfl

/-- Two homomorphisms out of a presented group are equal when they agree on the generators. -/
theorem presented_hom_ext {n : Nat} {rels : Set (Word n)} {G : Type} [Group G]
    {f g : PresentedGroup rels →* G} (h : ∀ a, f (PresentedGroup.of a) = g (PresentedGroup.of a)) :
    f = g := by
  refine MonoidHom.ext fun x => ?_
  refine PresentedGroup.induction_on (C := fun y => f y = g y) x ?_
  intro z
  refine FreeGroup.induction_on z ?_ ?_ ?_ ?_
  · simp
  · intro a; simpa [PresentedGroup.of] using h a
  · intro a ih; simp only [MonoidHom.map_inv, ih]
  · intro x y ihx ihy; simp only [MonoidHom.map_mul, ihx, ihy]

/-! ## The transport lemma -/

/-- **The workhorse.**  If the substitutions `σ : F_n → F_{n'}` and `τ : F_{n'} → F_n` witness
each other's relations — (A) `σ` carries every relator of `r` into the normal closure of `r'`,
(B) `τ` carries every relator of `r'` into the normal closure of `r`, and (C), (D) the two
composites are the identity modulo the relators — then the two presentations present isomorphic
groups: the maps are `x_k ↦ σ k` and `x_k ↦ τ k`, (A) and (B) say that they are well defined and
(C) and (D) that they are mutually inverse on generators. -/
theorem qEquiv_of_data {n n' m m' : Nat} {r : Fin m → Word n} {r' : Fin m' → Word n'}
    (σ : Fin n → Word n') (τ : Fin n' → Word n)
    (hA : ∀ j, PresentedGroup.mk (Set.range r') (FreeGroup.lift σ (r j)) = 1)
    (hB : ∀ j, PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (r' j)) = 1)
    (hC : ∀ k, PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (σ k)) =
      PresentedGroup.mk (Set.range r) (FreeGroup.of k))
    (hD : ∀ k, PresentedGroup.mk (Set.range r') (FreeGroup.lift σ (τ k)) =
      PresentedGroup.mk (Set.range r') (FreeGroup.of k)) :
    Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range r')) := by
  let hA' : ∀ x ∈ Set.range r, FreeGroup.lift (fun k => PresentedGroup.mk (Set.range r') (σ k)) x = 1 :=
    fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      rw [lift_mk (Set.range r') σ]
      exact hA j
  let hB' : ∀ x ∈ Set.range r', FreeGroup.lift (fun k => PresentedGroup.mk (Set.range r) (τ k)) x = 1 :=
    fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      rw [lift_mk (Set.range r) τ]
      exact hB j
  let α : PresentedGroup (Set.range r) →* PresentedGroup (Set.range r') :=
    PresentedGroup.toGroup (rels := Set.range r) (f := fun k => PresentedGroup.mk (Set.range r') (σ k)) hA'
  let β : PresentedGroup (Set.range r') →* PresentedGroup (Set.range r) :=
    PresentedGroup.toGroup (rels := Set.range r') (f := fun k => PresentedGroup.mk (Set.range r) (τ k)) hB'
  have hα : ∀ y, α (PresentedGroup.mk (Set.range r) y) =
      PresentedGroup.mk (Set.range r') (FreeGroup.lift σ y) := by
    intro y
    rw [show α (PresentedGroup.mk (Set.range r) y) =
      FreeGroup.lift (fun k => PresentedGroup.mk (Set.range r') (σ k)) y from toGroup_mk _ _ hA' y]
    exact lift_mk _ σ y
  have hβ : ∀ y, β (PresentedGroup.mk (Set.range r') y) =
      PresentedGroup.mk (Set.range r) (FreeGroup.lift τ y) := by
    intro y
    rw [show β (PresentedGroup.mk (Set.range r') y) =
      FreeGroup.lift (fun k => PresentedGroup.mk (Set.range r) (τ k)) y from toGroup_mk _ _ hB' y]
    exact lift_mk _ τ y
  have hαβ : β.comp α = MonoidHom.id _ := by
    refine presented_hom_ext fun k => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, PresentedGroup.of, hα, hβ,
      FreeGroup.lift_apply_of]
    exact hC k
  have hβα : α.comp β = MonoidHom.id _ := by
    refine presented_hom_ext fun k => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, PresentedGroup.of, hα, hβ,
      FreeGroup.lift_apply_of]
    exact hD k
  exact ⟨{ toFun := α
           invFun := β
           left_inv := fun x => by
             have h := congrFun (congrArg DFunLike.coe hαβ) x
             simpa using h
           right_inv := fun x => by
             have h := congrFun (congrArg DFunLike.coe hβα) x
             simpa using h
           map_mul' := α.map_mul }⟩

/-! ## Composition of substitutions -/

/-- If `τ` undoes `σ` on the generators then the composite of the lifted substitutions is the
identity. -/
theorem lift_comp_lift {n : Nat} {σ τ : Fin n → Word n}
    (h : ∀ k, FreeGroup.lift τ (σ k) = FreeGroup.of k) :
    (FreeGroup.lift τ).comp (FreeGroup.lift σ) = MonoidHom.id (Word n) := by
  refine FreeGroup.ext_hom _ _ fun k => ?_
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, FreeGroup.lift_apply_of]
  exact h k

/-! ## Relator membership helpers -/

/-- If every relator of `r'` lies in the normal closure of `r`, so does the normal closure of
`r'`. -/
theorem normalClosure_le_of_forall {n m m' : Nat} {r : Fin m → Word n} {r' : Fin m' → Word n}
    (h : ∀ j, r' j ∈ Subgroup.normalClosure (Set.range r)) :
    Subgroup.normalClosure (Set.range r') ≤ Subgroup.normalClosure (Set.range r) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨j, rfl⟩
  exact h j

/-- A relator of `r` is trivial in the group presented by `r'` when it lies in the normal closure
of `r'`. -/
theorem mk_relator_eq_one {n m m' : Nat} {r : Fin m → Word n} {r' : Fin m' → Word n}
    (h : Subgroup.normalClosure (Set.range r) ≤ Subgroup.normalClosure (Set.range r'))
    (j : Fin m) : PresentedGroup.mk (Set.range r') (r j) = 1 :=
  PresentedGroup.mk_eq_one_iff.mpr (h (Subgroup.subset_normalClosure ⟨j, rfl⟩))

/-! ## The four relator moves (i)-(iii) -/

/-- **Move (ii), invert a relator.** -/
theorem inv_core {n m : Nat} (r : Fin m → Word n) (i : Fin m) :
    Nonempty (PresentedGroup (Set.range r) ≃*
      PresentedGroup (Set.range (fun k => if k = i then (r i)⁻¹ else r k))) := by
  have hle₁ : Subgroup.normalClosure (Set.range (fun k => if k = i then (r i)⁻¹ else r k)) ≤
      Subgroup.normalClosure (Set.range r) := by
    refine normalClosure_le_of_forall ?_
    intro j
    by_cases hj : j = i
    · rw [hj] at *
      have h1 : r i ∈ Subgroup.normalClosure (Set.range r) :=
        Subgroup.subset_normalClosure ⟨i, rfl⟩
      simpa using Subgroup.inv_mem _ h1
    · simpa [hj] using Subgroup.subset_normalClosure (s := Set.range r) ⟨j, rfl⟩
  have hle₂ : Subgroup.normalClosure (Set.range r) ≤
      Subgroup.normalClosure (Set.range (fun k => if k = i then (r i)⁻¹ else r k)) := by
    refine normalClosure_le_of_forall ?_
    intro j
    by_cases hj : j = i
    · rw [hj] at *
      have h1 : (r i)⁻¹ ∈
          Subgroup.normalClosure (Set.range (fun k => if k = i then (r i)⁻¹ else r k)) :=
        Subgroup.subset_normalClosure ⟨i, by simp⟩
      simpa using Subgroup.inv_mem _ h1
    · exact Subgroup.subset_normalClosure ⟨j, by simp [hj]⟩
  refine qEquiv_of_data (r := r) (r' := fun k => if k = i then (r i)⁻¹ else r k)
    FreeGroup.of FreeGroup.of ?_ ?_ ?_ ?_
  · intro j
    rw [FreeGroup.lift_of_apply]
    exact mk_relator_eq_one hle₂ j
  · intro j
    rw [FreeGroup.lift_of_apply]
    exact mk_relator_eq_one hle₁ j
  · intro k; simp
  · intro k; simp

/-- **Move (i), multiply a relator by another on the right.** -/
theorem mul_core {n m : Nat} (r : Fin m → Word n) (i j : Fin m) (hij : i ≠ j) :
    Nonempty (PresentedGroup (Set.range r) ≃*
      PresentedGroup (Set.range (fun k => if k = i then r i * r j else r k))) := by
  have hle₁ : Subgroup.normalClosure (Set.range (fun k => if k = i then r i * r j else r k)) ≤
      Subgroup.normalClosure (Set.range r) := by
    refine normalClosure_le_of_forall ?_
    intro k
    by_cases hk : k = i
    · rw [hk] at *
      have h1 : r i * r j ∈ Subgroup.normalClosure (Set.range r) :=
        Subgroup.mul_mem _ (Subgroup.subset_normalClosure ⟨i, rfl⟩)
          (Subgroup.subset_normalClosure ⟨j, rfl⟩)
      simpa using h1
    · simpa [hk] using Subgroup.subset_normalClosure (s := Set.range r) ⟨k, rfl⟩
  have hle₂ : Subgroup.normalClosure (Set.range r) ≤
      Subgroup.normalClosure (Set.range (fun k => if k = i then r i * r j else r k)) := by
    refine normalClosure_le_of_forall ?_
    intro k
    by_cases hk : k = i
    · rw [hk] at *
      have h1 : r i * r j ∈
          Subgroup.normalClosure (Set.range (fun k => if k = i then r i * r j else r k)) :=
        Subgroup.subset_normalClosure ⟨i, by simp⟩
      have h2 : r j ∈
          Subgroup.normalClosure (Set.range (fun k => if k = i then r i * r j else r k)) :=
        Subgroup.subset_normalClosure ⟨j, by simp [hij.symm]⟩
      have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      simpa using h3
    · exact Subgroup.subset_normalClosure ⟨k, by simp [hk]⟩
  refine qEquiv_of_data (r := r) (r' := fun k => if k = i then r i * r j else r k)
    FreeGroup.of FreeGroup.of ?_ ?_ ?_ ?_
  · intro k
    rw [FreeGroup.lift_of_apply]
    exact mk_relator_eq_one hle₂ k
  · intro k
    rw [FreeGroup.lift_of_apply]
    exact mk_relator_eq_one hle₁ k
  · intro k; simp
  · intro k; simp

/-- **Move (iii), conjugate a relator.** -/
theorem conj_core {n m : Nat} (r : Fin m → Word n) (i : Fin m) (w : Word n) :
    Nonempty (PresentedGroup (Set.range r) ≃*
      PresentedGroup (Set.range (fun k => if k = i then w * r i * w⁻¹ else r k))) := by
  have hle₁ : Subgroup.normalClosure (Set.range (fun k => if k = i then w * r i * w⁻¹ else r k)) ≤
      Subgroup.normalClosure (Set.range r) := by
    refine normalClosure_le_of_forall ?_
    intro k
    by_cases hk : k = i
    · rw [hk] at *
      simpa using (Subgroup.normalClosure_normal (s := Set.range r)).conj_mem (r i)
        (Subgroup.subset_normalClosure ⟨i, rfl⟩) w
    · simpa [hk] using Subgroup.subset_normalClosure (s := Set.range r) ⟨k, rfl⟩
  have hle₂ : Subgroup.normalClosure (Set.range r) ≤
      Subgroup.normalClosure (Set.range (fun k => if k = i then w * r i * w⁻¹ else r k)) := by
    refine normalClosure_le_of_forall ?_
    intro k
    by_cases hk : k = i
    · rw [hk] at *
      have h1 : w * r i * w⁻¹ ∈
          Subgroup.normalClosure (Set.range (fun k => if k = i then w * r i * w⁻¹ else r k)) :=
        Subgroup.subset_normalClosure ⟨i, by simp⟩
      have h2 := (Subgroup.normalClosure_normal
        (s := Set.range (fun k => if k = i then w * r i * w⁻¹ else r k))).conj_mem _ h1 w⁻¹
      convert h2 using 1
      group
    · exact Subgroup.subset_normalClosure ⟨k, by simp [hk]⟩
  refine qEquiv_of_data (r := r) (r' := fun k => if k = i then w * r i * w⁻¹ else r k)
    FreeGroup.of FreeGroup.of ?_ ?_ ?_ ?_
  · intro k
    rw [FreeGroup.lift_of_apply]
    exact mk_relator_eq_one hle₂ k
  · intro k
    rw [FreeGroup.lift_of_apply]
    exact mk_relator_eq_one hle₁ k
  · intro k; simp
  · intro k; simp

/-- **Move (iii)+(i), left multiply a relator by another.** -/
theorem lmul_core {n m : Nat} (r : Fin m → Word n) (i j : Fin m) (hij : i ≠ j) :
    Nonempty (PresentedGroup (Set.range r) ≃*
      PresentedGroup (Set.range (fun k => if k = i then r j * r i else r k))) := by
  have hle₁ : Subgroup.normalClosure (Set.range (fun k => if k = i then r j * r i else r k)) ≤
      Subgroup.normalClosure (Set.range r) := by
    refine normalClosure_le_of_forall ?_
    intro k
    by_cases hk : k = i
    · rw [hk] at *
      have h1 : r j * r i ∈ Subgroup.normalClosure (Set.range r) :=
        Subgroup.mul_mem _ (Subgroup.subset_normalClosure ⟨j, rfl⟩)
          (Subgroup.subset_normalClosure ⟨i, rfl⟩)
      simpa using h1
    · simpa [hk] using Subgroup.subset_normalClosure (s := Set.range r) ⟨k, rfl⟩
  have hle₂ : Subgroup.normalClosure (Set.range r) ≤
      Subgroup.normalClosure (Set.range (fun k => if k = i then r j * r i else r k)) := by
    refine normalClosure_le_of_forall ?_
    intro k
    by_cases hk : k = i
    · rw [hk] at *
      have h1 : r j * r i ∈
          Subgroup.normalClosure (Set.range (fun k => if k = i then r j * r i else r k)) :=
        Subgroup.subset_normalClosure ⟨i, by simp⟩
      have h2 : r j ∈
          Subgroup.normalClosure (Set.range (fun k => if k = i then r j * r i else r k)) :=
        Subgroup.subset_normalClosure ⟨j, by simp [hij.symm]⟩
      have h3 := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
      simpa using h3
    · exact Subgroup.subset_normalClosure ⟨k, by simp [hk]⟩
  refine qEquiv_of_data (r := r) (r' := fun k => if k = i then r j * r i else r k)
    FreeGroup.of FreeGroup.of ?_ ?_ ?_ ?_
  · intro k
    rw [FreeGroup.lift_of_apply]
    exact mk_relator_eq_one hle₂ k
  · intro k
    rw [FreeGroup.lift_of_apply]
    exact mk_relator_eq_one hle₁ k
  · intro k; simp
  · intro k; simp

/-! ## The Nielsen moves (iv) -/

/-- **Move (iv), `x_i ↦ x_i⁻¹`.** -/
theorem neg_core {n m : Nat} (r : Fin m → Word n) (i : Fin n) :
    Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range
      (fun k => FreeGroup.lift
        (fun t => if t = i then (FreeGroup.of t)⁻¹ else FreeGroup.of t) (r k)))) := by
  set σ : Fin n → Word n := fun k => if k = i then (FreeGroup.of k)⁻¹ else FreeGroup.of k with hσ
  have hround : ∀ k, FreeGroup.lift σ (σ k) = FreeGroup.of k := by
    intro k
    by_cases hk : k = i
    · rw [hk] at *; simp [σ, hσ]
    · simp [σ, hσ, hk]
  refine qEquiv_of_data (r := r) (r' := fun k => FreeGroup.lift σ (r k)) σ σ ?_ ?_ ?_ ?_
  · intro k
    exact PresentedGroup.one_of_mem (rels := Set.range (fun k => FreeGroup.lift σ (r k))) ⟨k, rfl⟩
  · intro k
    have hc : FreeGroup.lift σ (FreeGroup.lift σ (r k)) = r k := by
      rw [← MonoidHom.comp_apply, lift_comp_lift hround, MonoidHom.id_apply]
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift σ (FreeGroup.lift σ (r k))) = 1
    rw [hc]
    exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨k, rfl⟩)
  · intro k
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift σ (σ k)) =
      PresentedGroup.mk (Set.range r) (FreeGroup.of k)
    rw [hround k]
  · intro k
    show PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.lift σ (σ k)) =
      PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.of k)
    rw [hround k]

/-- **Move (iv), `x_i ↦ x_i x_j`.**  `AC5.lean` has no `i ≠ j` guard on this move; `hij` is the
admissibility condition that supplies it. -/
theorem nij_core {n m : Nat} (r : Fin m → Word n) (i j : Fin n) (hij : i ≠ j) :
    Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range
      (fun k => FreeGroup.lift
        (fun t => if t = i then FreeGroup.of t * FreeGroup.of j else FreeGroup.of t) (r k)))) := by
  set σ : Fin n → Word n :=
    fun k => if k = i then FreeGroup.of k * FreeGroup.of j else FreeGroup.of k with hσ
  set τ : Fin n → Word n :=
    fun k => if k = i then FreeGroup.of k * (FreeGroup.of j)⁻¹ else FreeGroup.of k with hτ
  have h1 : ∀ k, FreeGroup.lift τ (σ k) = FreeGroup.of k := by
    intro k
    by_cases hk : k = i
    · rw [hk] at *; simp [σ, hσ, τ, hτ, hij.symm]
    · simp [σ, hσ, τ, hτ, hk]
  have h2 : ∀ k, FreeGroup.lift σ (τ k) = FreeGroup.of k := by
    intro k
    by_cases hk : k = i
    · rw [hk] at *; simp [σ, hσ, τ, hτ, hij.symm]
    · simp [σ, hσ, τ, hτ, hk]
  refine qEquiv_of_data (r := r) (r' := fun k => FreeGroup.lift σ (r k)) σ τ ?_ ?_ ?_ ?_
  · intro k
    exact PresentedGroup.one_of_mem (rels := Set.range (fun k => FreeGroup.lift σ (r k))) ⟨k, rfl⟩
  · intro k
    have hc : FreeGroup.lift τ (FreeGroup.lift σ (r k)) = r k := by
      rw [← MonoidHom.comp_apply, lift_comp_lift h1, MonoidHom.id_apply]
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (FreeGroup.lift σ (r k))) = 1
    rw [hc]
    exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨k, rfl⟩)
  · intro k
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (σ k)) =
      PresentedGroup.mk (Set.range r) (FreeGroup.of k)
    rw [h1 k]
  · intro k
    show PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.lift σ (τ k)) =
      PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.of k)
    rw [h2 k]

/-- **Move (iv), `x_i ↦ x_j x_i`.** -/
theorem nji_core {n m : Nat} (r : Fin m → Word n) (i j : Fin n) (hij : i ≠ j) :
    Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range
      (fun k => FreeGroup.lift
        (fun t => if t = i then FreeGroup.of j * FreeGroup.of t else FreeGroup.of t) (r k)))) := by
  set σ : Fin n → Word n :=
    fun k => if k = i then FreeGroup.of j * FreeGroup.of k else FreeGroup.of k with hσ
  set τ : Fin n → Word n :=
    fun k => if k = i then (FreeGroup.of j)⁻¹ * FreeGroup.of k else FreeGroup.of k with hτ
  have h1 : ∀ k, FreeGroup.lift τ (σ k) = FreeGroup.of k := by
    intro k
    by_cases hk : k = i
    · rw [hk] at *; simp [σ, hσ, τ, hτ, hij.symm]
    · simp [σ, hσ, τ, hτ, hk]
  have h2 : ∀ k, FreeGroup.lift σ (τ k) = FreeGroup.of k := by
    intro k
    by_cases hk : k = i
    · rw [hk] at *; simp [σ, hσ, τ, hτ, hij.symm]
    · simp [σ, hσ, τ, hτ, hk]
  refine qEquiv_of_data (r := r) (r' := fun k => FreeGroup.lift σ (r k)) σ τ ?_ ?_ ?_ ?_
  · intro k
    exact PresentedGroup.one_of_mem (rels := Set.range (fun k => FreeGroup.lift σ (r k))) ⟨k, rfl⟩
  · intro k
    have hc : FreeGroup.lift τ (FreeGroup.lift σ (r k)) = r k := by
      rw [← MonoidHom.comp_apply, lift_comp_lift h1, MonoidHom.id_apply]
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (FreeGroup.lift σ (r k))) = 1
    rw [hc]
    exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨k, rfl⟩)
  · intro k
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (σ k)) =
      PresentedGroup.mk (Set.range r) (FreeGroup.of k)
    rw [h1 k]
  · intro k
    show PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.lift σ (τ k)) =
      PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.of k)
    rw [h2 k]

/-- **Move (iv), `x_i ↦ x_i x_j⁻¹`.** -/
theorem nijinv_core {n m : Nat} (r : Fin m → Word n) (i j : Fin n) (hij : i ≠ j) :
    Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range
      (fun k => FreeGroup.lift
        (fun t => if t = i then FreeGroup.of t * (FreeGroup.of j)⁻¹ else FreeGroup.of t)
        (r k)))) := by
  set σ : Fin n → Word n :=
    fun k => if k = i then FreeGroup.of k * (FreeGroup.of j)⁻¹ else FreeGroup.of k with hσ
  set τ : Fin n → Word n :=
    fun k => if k = i then FreeGroup.of k * FreeGroup.of j else FreeGroup.of k with hτ
  have h1 : ∀ k, FreeGroup.lift τ (σ k) = FreeGroup.of k := by
    intro k
    by_cases hk : k = i
    · rw [hk] at *; simp [σ, hσ, τ, hτ, hij.symm]
    · simp [σ, hσ, τ, hτ, hk]
  have h2 : ∀ k, FreeGroup.lift σ (τ k) = FreeGroup.of k := by
    intro k
    by_cases hk : k = i
    · rw [hk] at *; simp [σ, hσ, τ, hτ, hij.symm]
    · simp [σ, hσ, τ, hτ, hk]
  refine qEquiv_of_data (r := r) (r' := fun k => FreeGroup.lift σ (r k)) σ τ ?_ ?_ ?_ ?_
  · intro k
    exact PresentedGroup.one_of_mem (rels := Set.range (fun k => FreeGroup.lift σ (r k))) ⟨k, rfl⟩
  · intro k
    have hc : FreeGroup.lift τ (FreeGroup.lift σ (r k)) = r k := by
      rw [← MonoidHom.comp_apply, lift_comp_lift h1, MonoidHom.id_apply]
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (FreeGroup.lift σ (r k))) = 1
    rw [hc]
    exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨k, rfl⟩)
  · intro k
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (σ k)) =
      PresentedGroup.mk (Set.range r) (FreeGroup.of k)
    rw [h1 k]
  · intro k
    show PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.lift σ (τ k)) =
      PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.of k)
    rw [h2 k]

/-- **Move (iv), `x_i ↦ x_j⁻¹ x_i`.** -/
theorem njiinv_core {n m : Nat} (r : Fin m → Word n) (i j : Fin n) (hij : i ≠ j) :
    Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range
      (fun k => FreeGroup.lift
        (fun t => if t = i then (FreeGroup.of j)⁻¹ * FreeGroup.of t else FreeGroup.of t)
        (r k)))) := by
  set σ : Fin n → Word n :=
    fun k => if k = i then (FreeGroup.of j)⁻¹ * FreeGroup.of k else FreeGroup.of k with hσ
  set τ : Fin n → Word n :=
    fun k => if k = i then FreeGroup.of j * FreeGroup.of k else FreeGroup.of k with hτ
  have h1 : ∀ k, FreeGroup.lift τ (σ k) = FreeGroup.of k := by
    intro k
    by_cases hk : k = i
    · rw [hk] at *; simp [σ, hσ, τ, hτ, hij.symm]
    · simp [σ, hσ, τ, hτ, hk]
  have h2 : ∀ k, FreeGroup.lift σ (τ k) = FreeGroup.of k := by
    intro k
    by_cases hk : k = i
    · rw [hk] at *; simp [σ, hσ, τ, hτ, hij.symm]
    · simp [σ, hσ, τ, hτ, hk]
  refine qEquiv_of_data (r := r) (r' := fun k => FreeGroup.lift σ (r k)) σ τ ?_ ?_ ?_ ?_
  · intro k
    exact PresentedGroup.one_of_mem (rels := Set.range (fun k => FreeGroup.lift σ (r k))) ⟨k, rfl⟩
  · intro k
    have hc : FreeGroup.lift τ (FreeGroup.lift σ (r k)) = r k := by
      rw [← MonoidHom.comp_apply, lift_comp_lift h1, MonoidHom.id_apply]
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (FreeGroup.lift σ (r k))) = 1
    rw [hc]
    exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨k, rfl⟩)
  · intro k
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (σ k)) =
      PresentedGroup.mk (Set.range r) (FreeGroup.of k)
    rw [h1 k]
  · intro k
    show PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.lift σ (τ k)) =
      PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.of k)
    rw [h2 k]

/-- **Move (iv), exchange two generators.**  Sound also at `i = j`, where the substitution is the
identity. -/
theorem swap_core {n m : Nat} (r : Fin m → Word n) (i j : Fin n) :
    Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range
      (fun k => FreeGroup.lift
        (fun t => if t = i then FreeGroup.of j else if t = j then FreeGroup.of i
          else FreeGroup.of t) (r k)))) := by
  rcases eq_or_ne i j with rfl | hij
  · have hid : ∀ t : Fin n, (if t = i then FreeGroup.of i else if t = i then
        FreeGroup.of i else FreeGroup.of t) = FreeGroup.of t := by
      intro t
      by_cases ht : t = i
      · rw [if_pos ht, ht]
      · rw [if_neg ht, if_neg ht]
    have hfun : (fun k => FreeGroup.lift (fun t => if t = i then FreeGroup.of i else
        if t = i then FreeGroup.of i else FreeGroup.of t) (r k)) = r := by
      funext k
      rw [funext hid, FreeGroup.lift_of_eq_id, MonoidHom.id_apply]
    rw [hfun]
    exact ⟨MulEquiv.refl _⟩
  · set σ : Fin n → Word n :=
      fun k => if k = i then FreeGroup.of j else if k = j then FreeGroup.of i
        else FreeGroup.of k with hσ
    have h1 : ∀ k, FreeGroup.lift σ (σ k) = FreeGroup.of k := by
      intro k
      by_cases hk : k = i
      · simp only [σ, hσ, if_pos hk, reduceIte]
        rw [hk]
        simp only [σ, hσ, if_neg (Ne.symm hij), if_pos rfl, reduceIte, FreeGroup.lift_apply_of]
      · by_cases hk2 : k = j
        · simp only [σ, hσ, if_neg hk, if_pos hk2, reduceIte]
          rw [hk2]
          simp only [σ, hσ, if_pos rfl, reduceIte, FreeGroup.lift_apply_of]
        · simp only [σ, hσ, if_neg hk, if_neg hk2, reduceIte, FreeGroup.lift_apply_of]
    refine qEquiv_of_data (r := r) (r' := fun k => FreeGroup.lift σ (r k)) σ σ ?_ ?_ ?_ ?_
    · intro k
      exact PresentedGroup.one_of_mem (rels := Set.range (fun k => FreeGroup.lift σ (r k)))
        ⟨k, rfl⟩
    · intro k
      have hc : FreeGroup.lift σ (FreeGroup.lift σ (r k)) = r k := by
        rw [← MonoidHom.comp_apply, lift_comp_lift h1, MonoidHom.id_apply]
      show PresentedGroup.mk (Set.range r) (FreeGroup.lift σ (FreeGroup.lift σ (r k))) = 1
      rw [hc]
      exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨k, rfl⟩)
    · intro k
      show PresentedGroup.mk (Set.range r) (FreeGroup.lift σ (σ k)) =
        PresentedGroup.mk (Set.range r) (FreeGroup.of k)
      rw [h1 k]
    · intro k
      show PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.lift σ (σ k)) =
        PresentedGroup.mk (Set.range (fun k => FreeGroup.lift σ (r k))) (FreeGroup.of k)
      rw [h1 k]

/-! ## Index arithmetic for deletion -/

theorem skipEmb_val {n : Nat} (i : Fin n) (k : Fin (n - 1)) :
    (skipEmb i k).val = if k.val < i.val then k.val else k.val + 1 := by
  simp only [skipEmb]
  split <;> rfl

theorem skipIndex_val {n : Nat} (i t : Fin n) (h : t ≠ i) :
    (skipIndex i t h).val = if t.val < i.val then t.val else t.val - 1 := by
  simp only [skipIndex]
  split <;> rfl

theorem skipEmb_ne {n : Nat} (i : Fin n) (k : Fin (n - 1)) : skipEmb i k ≠ i := by
  intro h
  have hv : (skipEmb i k).val = i.val := by rw [h]
  rw [skipEmb_val] at hv
  by_cases hlt : k.val < i.val
  · rw [if_pos hlt] at hv; omega
  · rw [if_neg hlt] at hv; omega

theorem skipIndex_skipEmb {n : Nat} (i : Fin n) (k : Fin (n - 1)) :
    skipIndex i (skipEmb i k) (skipEmb_ne i k) = k := by
  apply Fin.ext
  rw [skipIndex_val, skipEmb_val]
  by_cases hlt : k.val < i.val
  · rw [if_pos hlt, if_pos hlt]
  · rw [if_neg hlt]
    have h2 : ¬ (k.val + 1 < i.val) := by omega
    rw [if_neg h2]
    omega

theorem skipEmb_skipIndex {n : Nat} (i t : Fin n) (h : t ≠ i) :
    skipEmb i (skipIndex i t h) = t := by
  apply Fin.ext
  rw [skipEmb_val, skipIndex_val]
  by_cases hlt : t.val < i.val
  · rw [if_pos hlt, if_pos hlt]
  · have hgt : i.val < t.val := by
      rcases Nat.lt_or_ge i.val t.val with h' | h'
      · exact h'
      · exact absurd (Fin.ext (by omega)) h
    rw [if_neg hlt]
    have h2 : ¬ (t.val - 1 < i.val) := by omega
    rw [if_neg h2]
    omega

/-! ## Two substitution facts -/

/-- Composition of a lifted substitution with a `FreeGroup.map`. -/
theorem lift_comp_map {n n' : Nat} (τ : Fin n' → Word n) (f : Fin n → Fin n') :
    (FreeGroup.lift τ).comp (FreeGroup.map f) = FreeGroup.lift (fun k => τ (f k)) := by
  refine FreeGroup.ext_hom _ _ fun k => ?_
  simp only [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.lift_apply_of]

/-- If `τ` undoes `f` on the generators, `lift τ` undoes `map f`. -/
theorem lift_map_of_eq {n n' : Nat} (τ : Fin n' → Word n) (f : Fin n → Fin n')
    (h : ∀ k, τ (f k) = FreeGroup.of k) (u : Word n) :
    FreeGroup.lift τ (FreeGroup.map f u) = u := by
  have h1 : (FreeGroup.lift τ).comp (FreeGroup.map f) = MonoidHom.id (Word n) := by
    rw [lift_comp_map, show (fun k => τ (f k)) = (fun k => FreeGroup.of k) from funext h,
      FreeGroup.lift_of_eq_id]
  have h2 := congrFun (congrArg DFunLike.coe h1) u
  simpa using h2

/-! ## Prolongation (v) -/

/-- **Move (v), adjoin a generator together with the relator equal to it.** -/
theorem prolong_core {n m : Nat} (r : Fin m → Word n) :
    Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range
      (fun k => Fin.lastCases (FreeGroup.of (Fin.last n))
        (fun t => FreeGroup.map Fin.castSucc (r t)) k))) := by
  set R' : Fin (m + 1) → Word (n + 1) := (fun k => Fin.lastCases (FreeGroup.of (Fin.last n))
    (fun t => FreeGroup.map Fin.castSucc (r t)) k) with hR'
  set τ : Fin (n + 1) → Word n := (fun k => Fin.lastCases 1 (fun t => FreeGroup.of t) k) with hτ
  change Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range R'))
  refine qEquiv_of_data (n := n) (n' := n + 1) (m := m) (m' := m + 1) (r := r)
    (r' := R') (fun k => FreeGroup.of (Fin.castSucc k)) τ ?_ ?_ ?_ ?_
  · intro j
    have hmap : FreeGroup.lift (fun k => FreeGroup.of (Fin.castSucc k)) (r j) =
        FreeGroup.map Fin.castSucc (r j) := by
      rw [FreeGroup.map_eq_lift]
      rfl
    show PresentedGroup.mk (Set.range R')
      (FreeGroup.lift (fun k => FreeGroup.of (Fin.castSucc k)) (r j)) = 1
    rw [hmap]
    exact PresentedGroup.one_of_mem ⟨Fin.castSucc j, by
      show R' (Fin.castSucc j) = FreeGroup.map Fin.castSucc (r j)
      simp only [R', Fin.lastCases_castSucc]⟩
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (R' (Fin.last m))) = 1
      rw [show R' (Fin.last m) = FreeGroup.of (Fin.last n) from by
        simp only [R', Fin.lastCases_last]]
      rw [FreeGroup.lift_apply_of]
      show PresentedGroup.mk (Set.range r) (τ (Fin.last n)) = 1
      rw [show τ (Fin.last n) = 1 from by simp only [τ, Fin.lastCases_last]]
      simp
    · intro t
      show PresentedGroup.mk (Set.range r)
        (FreeGroup.lift τ (R' (Fin.castSucc t))) = 1
      rw [show R' (Fin.castSucc t) = FreeGroup.map Fin.castSucc (r t) from by
        simp only [R', Fin.lastCases_castSucc]]
      rw [lift_map_of_eq τ Fin.castSucc (fun k => by
        simp only [τ, Fin.lastCases_castSucc])]
      exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨t, rfl⟩)
  · intro k
    show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (FreeGroup.of (Fin.castSucc k))) =
      PresentedGroup.mk (Set.range r) (FreeGroup.of k)
    rw [FreeGroup.lift_apply_of]
    show PresentedGroup.mk (Set.range r) (τ (Fin.castSucc k)) =
      PresentedGroup.mk (Set.range r) (FreeGroup.of k)
    rw [show τ (Fin.castSucc k) = FreeGroup.of k from by
      simp only [τ, Fin.lastCases_castSucc]]
  · intro k
    refine Fin.lastCases ?_ ?_ k
    · show PresentedGroup.mk (Set.range R')
        (FreeGroup.lift (fun k => FreeGroup.of (Fin.castSucc k)) (τ (Fin.last n))) =
        PresentedGroup.mk (Set.range R') (FreeGroup.of (Fin.last n))
      rw [show τ (Fin.last n) = 1 from by simp only [τ, Fin.lastCases_last]]
      rw [MonoidHom.map_one]
      exact (PresentedGroup.one_of_mem (rels := Set.range R') ⟨Fin.last m, by
        show R' (Fin.last m) = FreeGroup.of (Fin.last n)
        simp only [R', Fin.lastCases_last]⟩).symm
    · intro t
      show PresentedGroup.mk (Set.range R')
        (FreeGroup.lift (fun k => FreeGroup.of (Fin.castSucc k)) (τ (Fin.castSucc t))) =
        PresentedGroup.mk (Set.range R') (FreeGroup.of (Fin.castSucc t))
      rw [show τ (Fin.castSucc t) = FreeGroup.of t from by
        simp only [τ, Fin.lastCases_castSucc]]
      rw [FreeGroup.lift_apply_of]

/-- The conjugacy guard of `QMove.delete` puts the deleted generator in the normal closure of the
relators. -/
theorem of_mem_normalClosure {n m : Nat} (r : Fin m → Word n) (I : Fin n) (j : Fin m)
    (wk : Word n)
    (h : r j = wk * FreeGroup.of I * wk⁻¹ ∨ r j = wk * (FreeGroup.of I)⁻¹ * wk⁻¹) :
    FreeGroup.of I ∈ Subgroup.normalClosure (Set.range r) := by
  have hmem : r j ∈ Subgroup.normalClosure (Set.range r) :=
    Subgroup.subset_normalClosure ⟨j, rfl⟩
  have hnorm := Subgroup.normalClosure_normal (s := Set.range r)
  rcases h with h | h
  · rw [h] at hmem
    have h2 := hnorm.conj_mem _ hmem wk⁻¹
    convert h2 using 1
    group
  · rw [h] at hmem
    have h2 := hnorm.conj_mem _ hmem wk⁻¹
    have h3 : (FreeGroup.of I)⁻¹ ∈ Subgroup.normalClosure (Set.range r) := by
      convert h2 using 1
      group
    simpa using Subgroup.inv_mem _ h3

/-- **Move (vi), delete a generator whose relator is a conjugate of it.** -/
theorem delete_core {n m : Nat} (r : Fin m → Word n) (I : Fin n) (J : Fin m) (wk : Word n)
    (hconj : r J = wk * FreeGroup.of I * wk⁻¹ ∨ r J = wk * (FreeGroup.of I)⁻¹ * wk⁻¹) :
    Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range
      (fun k => FreeGroup.lift
        (fun t => if h : t = I then 1 else FreeGroup.of (skipIndex I t h))
        (r (skipEmb J k))))) := by
  set σ : Fin n → Word (n - 1) :=
    (fun t => if h : t = I then 1 else FreeGroup.of (skipIndex I t h)) with hσ
  set τ : Fin (n - 1) → Word n := (fun k => FreeGroup.of (skipEmb I k)) with hτ
  set R' : Fin (m - 1) → Word (n - 1) :=
    (fun k => FreeGroup.lift σ (r (skipEmb J k))) with hR'
  change Nonempty (PresentedGroup (Set.range r) ≃* PresentedGroup (Set.range R'))
  have hI : FreeGroup.of I ∈ Subgroup.normalClosure (Set.range r) :=
    of_mem_normalClosure r I J wk hconj
  have hmkI : PresentedGroup.mk (Set.range r) (FreeGroup.of I) = 1 :=
    PresentedGroup.mk_eq_one_iff.mpr hI
  have hσI : σ I = 1 := by
    simp only [σ, dif_pos rfl]
  have hδ : ∀ u : Word n,
      PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (FreeGroup.lift σ u)) =
        PresentedGroup.mk (Set.range r) u := by
    have h1 : (PresentedGroup.mk (Set.range r)).comp
          ((FreeGroup.lift τ).comp (FreeGroup.lift σ)) = PresentedGroup.mk (Set.range r) := by
      refine FreeGroup.ext_hom _ _ fun t => ?_
      simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      show PresentedGroup.mk (Set.range r) (FreeGroup.lift τ (σ t)) =
        PresentedGroup.mk (Set.range r) (FreeGroup.of t)
      by_cases ht : t = I
      · rw [ht, hσI]
        show PresentedGroup.mk (Set.range r) 1 = PresentedGroup.mk (Set.range r) (FreeGroup.of I)
        rw [hmkI, MonoidHom.map_one]
      · rw [show σ t = FreeGroup.of (skipIndex I t ht) from by simp only [σ, dif_neg ht]]
        show PresentedGroup.mk (Set.range r) (FreeGroup.of (skipEmb I (skipIndex I t ht))) =
          PresentedGroup.mk (Set.range r) (FreeGroup.of t)
        rw [skipEmb_skipIndex]
    intro u
    have h2 := congrFun (congrArg DFunLike.coe h1) u
    simpa only [MonoidHom.comp_apply] using h2
  refine qEquiv_of_data (n := n) (n' := n - 1) (m := m) (m' := m - 1) (r := r)
    (r' := R') σ τ ?_ ?_ ?_ ?_
  · intro j
    by_cases hj : j = J
    · rw [hj]
      have hzero : FreeGroup.lift σ (r J) = 1 := by
        rcases hconj with hc | hc
        · rw [hc, MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv,
            FreeGroup.lift_apply_of, hσI, mul_one]
          simp
        · rw [hc, MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv,
            FreeGroup.lift_apply_of, hσI, inv_one, mul_one]
          simp
      show PresentedGroup.mk (Set.range R') (FreeGroup.lift σ (r J)) = 1
      rw [hzero, MonoidHom.map_one]
    · rw [← skipEmb_skipIndex J j hj]
      exact PresentedGroup.one_of_mem ⟨skipIndex J j hj, rfl⟩
  · intro k
    show PresentedGroup.mk (Set.range r)
      (FreeGroup.lift τ (FreeGroup.lift σ (r (skipEmb J k)))) = 1
    rw [hδ]
    exact PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨skipEmb J k, rfl⟩)
  · intro k
    by_cases hk : k = I
    · rw [hk, hσI]
      show PresentedGroup.mk (Set.range r) 1 = PresentedGroup.mk (Set.range r) (FreeGroup.of I)
      rw [hmkI, MonoidHom.map_one]
    · rw [show σ k = FreeGroup.of (skipIndex I k hk) from by simp only [σ, dif_neg hk]]
      show PresentedGroup.mk (Set.range r) (FreeGroup.of (skipEmb I (skipIndex I k hk))) =
        PresentedGroup.mk (Set.range r) (FreeGroup.of k)
      rw [skipEmb_skipIndex]
  · intro k
    show PresentedGroup.mk (Set.range R') (FreeGroup.lift σ (τ k)) =
      PresentedGroup.mk (Set.range R') (FreeGroup.of k)
    rw [show τ k = FreeGroup.of (skipEmb I k) from by simp only [τ]]
    rw [FreeGroup.lift_apply_of]
    rw [show σ (skipEmb I k) =
        FreeGroup.of (skipIndex I (skipEmb I k) (skipEmb_ne I k)) from by
      simp only [σ, dif_neg (skipEmb_ne I k)]]
    rw [skipIndex_skipEmb]

/-! ## The admissibility condition -/

/-- The syntactic admissibility condition on a move: the four diagonal Nielsen moves are excluded.
`AC5.lean`'s `QMove.apply` has no `i ≠ j` guard on `nij`, `nji`, `nijinv`, `njiinv`; those four
moves change the presented group at `i = j`, so a soundness theorem has to exclude them. -/
def QMove.WF : QMove → Prop
  | .nij i j => i ≠ j
  | .nji i j => i ≠ j
  | .nijinv i j => i ≠ j
  | .njiinv i j => i ≠ j
  | _ => True

/-- Boolean version of `QMove.WF`, for `decide` on certificate literals. -/
def QMove.wfBool : QMove → Bool
  | .nij i j => i != j
  | .nji i j => i != j
  | .nijinv i j => i != j
  | .njiinv i j => i != j
  | _ => true

theorem QMove.wf_of_wfBool {m : QMove} (h : m.wfBool = true) : m.WF := by
  cases m with
  | inv i => simp [QMove.wfBool, QMove.WF]
  | mul i j => simp [QMove.wfBool, QMove.WF]
  | conj i w => simp [QMove.wfBool, QMove.WF]
  | lmul i j => simp [QMove.wfBool, QMove.WF]
  | neg i => simp [QMove.wfBool, QMove.WF]
  | nij i j => simpa [QMove.wfBool, QMove.WF] using h
  | nji i j => simpa [QMove.wfBool, QMove.WF] using h
  | nijinv i j => simpa [QMove.wfBool, QMove.WF] using h
  | njiinv i j => simpa [QMove.wfBool, QMove.WF] using h
  | swap i j => simp [QMove.wfBool, QMove.WF]
  | prolong => simp [QMove.wfBool, QMove.WF]
  | delete i j w => simp [QMove.wfBool, QMove.WF]

/-- Admissibility of a recorded move list. -/
def CheckWF (ms : List QMove) : Bool := ms.all QMove.wfBool

theorem forall_wf_of_checkWF {ms : List QMove} (h : CheckWF ms = true) :
    ∀ m ∈ ms, m.WF := by
  intro m hm
  exact QMove.wf_of_wfBool (List.all_eq_true.mp h m hm)


/-! ## The soundness theorem -/

/-- **Every admissible Q\*\*-move is sound.**  This is the twelve branches of `QMove.apply`; the
Nielsen branches use `hwf` for the `i ≠ j` guard that `AC5.lean` omits. -/
theorem apply_sound (m : QMove) (hwf : m.WF) (P Q : QPres) (h : m.apply P = some Q) :
    QEquiv P Q := by
  cases m with
  | inv i =>
    by_cases hi : i < P.m
    · have hstep : (QMove.inv i).apply P = some (setRel P ⟨i, hi⟩ ((P.rels ⟨i, hi⟩))⁻¹) := by
        simp only [QMove.apply, dif_pos hi]
      rw [hstep] at h
      simp only [Option.some.injEq] at h
      subst h
      exact inv_core P.rels ⟨i, hi⟩
    · have hstep : (QMove.inv i).apply P = none := by simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | mul i j =>
    by_cases hi : i < P.m
    · by_cases hj : j < P.m
      · by_cases hij : i ≠ j
        · have hfin : (⟨i, hi⟩ : Fin P.m) ≠ ⟨j, hj⟩ := fun hh => hij (congrArg Fin.val hh)
          have hstep : (QMove.mul i j).apply P =
              some (setRel P ⟨i, hi⟩ (P.rels ⟨i, hi⟩ * P.rels ⟨j, hj⟩)) := by
            simp only [QMove.apply, dif_pos hi, dif_pos hj, dif_pos hij]
          rw [hstep] at h
          simp only [Option.some.injEq] at h
          subst h
          exact mul_core P.rels ⟨i, hi⟩ ⟨j, hj⟩ hfin
        · have hstep : (QMove.mul i j).apply P = none := by
            simp only [QMove.apply, dif_pos hi, dif_pos hj, dif_neg hij]
          rw [hstep] at h
          exact absurd h (by simp)
      · have hstep : (QMove.mul i j).apply P = none := by
          simp only [QMove.apply, dif_pos hi, dif_neg hj]
        rw [hstep] at h
        exact absurd h (by simp)
    · have hstep : (QMove.mul i j).apply P = none := by simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | conj i w =>
    by_cases hi : i < P.m
    · cases hw : mkWordOpt P.n w with
      | none =>
        have hstep : (QMove.conj i w).apply P = none := by
          simp only [QMove.apply, dif_pos hi, hw]
        rw [hstep] at h
        exact absurd h (by simp)
      | some wk =>
        have hstep : (QMove.conj i w).apply P =
            some (setRel P ⟨i, hi⟩ (wk * P.rels ⟨i, hi⟩ * wk⁻¹)) := by
          simp only [QMove.apply, dif_pos hi, hw]
        rw [hstep] at h
        simp only [Option.some.injEq] at h
        subst h
        exact conj_core P.rels ⟨i, hi⟩ wk
    · have hstep : (QMove.conj i w).apply P = none := by
        simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | lmul i j =>
    by_cases hi : i < P.m
    · by_cases hj : j < P.m
      · by_cases hij : i ≠ j
        · have hfin : (⟨i, hi⟩ : Fin P.m) ≠ ⟨j, hj⟩ := fun hh => hij (congrArg Fin.val hh)
          have hstep : (QMove.lmul i j).apply P =
              some (setRel P ⟨i, hi⟩ (P.rels ⟨j, hj⟩ * P.rels ⟨i, hi⟩)) := by
            simp only [QMove.apply, dif_pos hi, dif_pos hj, dif_pos hij]
          rw [hstep] at h
          simp only [Option.some.injEq] at h
          subst h
          exact lmul_core P.rels ⟨i, hi⟩ ⟨j, hj⟩ hfin
        · have hstep : (QMove.lmul i j).apply P = none := by
            simp only [QMove.apply, dif_pos hi, dif_pos hj, dif_neg hij]
          rw [hstep] at h
          exact absurd h (by simp)
      · have hstep : (QMove.lmul i j).apply P = none := by
          simp only [QMove.apply, dif_pos hi, dif_neg hj]
        rw [hstep] at h
        exact absurd h (by simp)
    · have hstep : (QMove.lmul i j).apply P = none := by simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | neg i =>
    by_cases hi : i < P.n
    · have hstep : (QMove.neg i).apply P =
          some (substRel P (fun k => if k = (⟨i, hi⟩ : Fin P.n) then (FreeGroup.of k)⁻¹
            else FreeGroup.of k)) := by
        simp only [QMove.apply, dif_pos hi]
      rw [hstep] at h
      simp only [Option.some.injEq] at h
      subst h
      exact neg_core P.rels ⟨i, hi⟩
    · have hstep : (QMove.neg i).apply P = none := by simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | nij i j =>
    by_cases hi : i < P.n
    · by_cases hj : j < P.n
      · have hij : i ≠ j := hwf
        have hfin : (⟨i, hi⟩ : Fin P.n) ≠ ⟨j, hj⟩ := fun hh => hij (congrArg Fin.val hh)
        have hstep : (QMove.nij i j).apply P =
            some (substRel P (fun k => if k = (⟨i, hi⟩ : Fin P.n) then
              FreeGroup.of k * FreeGroup.of (⟨j, hj⟩ : Fin P.n) else FreeGroup.of k)) := by
          simp only [QMove.apply, dif_pos hi, dif_pos hj]
        rw [hstep] at h
        simp only [Option.some.injEq] at h
        subst h
        exact nij_core P.rels ⟨i, hi⟩ ⟨j, hj⟩ hfin
      · have hstep : (QMove.nij i j).apply P = none := by
          simp only [QMove.apply, dif_pos hi, dif_neg hj]
        rw [hstep] at h
        exact absurd h (by simp)
    · have hstep : (QMove.nij i j).apply P = none := by simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | nji i j =>
    by_cases hi : i < P.n
    · by_cases hj : j < P.n
      · have hij : i ≠ j := hwf
        have hfin : (⟨i, hi⟩ : Fin P.n) ≠ ⟨j, hj⟩ := fun hh => hij (congrArg Fin.val hh)
        have hstep : (QMove.nji i j).apply P =
            some (substRel P (fun k => if k = (⟨i, hi⟩ : Fin P.n) then
              FreeGroup.of (⟨j, hj⟩ : Fin P.n) * FreeGroup.of k else FreeGroup.of k)) := by
          simp only [QMove.apply, dif_pos hi, dif_pos hj]
        rw [hstep] at h
        simp only [Option.some.injEq] at h
        subst h
        exact nji_core P.rels ⟨i, hi⟩ ⟨j, hj⟩ hfin
      · have hstep : (QMove.nji i j).apply P = none := by
          simp only [QMove.apply, dif_pos hi, dif_neg hj]
        rw [hstep] at h
        exact absurd h (by simp)
    · have hstep : (QMove.nji i j).apply P = none := by simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | nijinv i j =>
    by_cases hi : i < P.n
    · by_cases hj : j < P.n
      · have hij : i ≠ j := hwf
        have hfin : (⟨i, hi⟩ : Fin P.n) ≠ ⟨j, hj⟩ := fun hh => hij (congrArg Fin.val hh)
        have hstep : (QMove.nijinv i j).apply P =
            some (substRel P (fun k => if k = (⟨i, hi⟩ : Fin P.n) then
              FreeGroup.of k * (FreeGroup.of (⟨j, hj⟩ : Fin P.n))⁻¹ else FreeGroup.of k)) := by
          simp only [QMove.apply, dif_pos hi, dif_pos hj]
        rw [hstep] at h
        simp only [Option.some.injEq] at h
        subst h
        exact nijinv_core P.rels ⟨i, hi⟩ ⟨j, hj⟩ hfin
      · have hstep : (QMove.nijinv i j).apply P = none := by
          simp only [QMove.apply, dif_pos hi, dif_neg hj]
        rw [hstep] at h
        exact absurd h (by simp)
    · have hstep : (QMove.nijinv i j).apply P = none := by simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | njiinv i j =>
    by_cases hi : i < P.n
    · by_cases hj : j < P.n
      · have hij : i ≠ j := hwf
        have hfin : (⟨i, hi⟩ : Fin P.n) ≠ ⟨j, hj⟩ := fun hh => hij (congrArg Fin.val hh)
        have hstep : (QMove.njiinv i j).apply P =
            some (substRel P (fun k => if k = (⟨i, hi⟩ : Fin P.n) then
              (FreeGroup.of (⟨j, hj⟩ : Fin P.n))⁻¹ * FreeGroup.of k else FreeGroup.of k)) := by
          simp only [QMove.apply, dif_pos hi, dif_pos hj]
        rw [hstep] at h
        simp only [Option.some.injEq] at h
        subst h
        exact njiinv_core P.rels ⟨i, hi⟩ ⟨j, hj⟩ hfin
      · have hstep : (QMove.njiinv i j).apply P = none := by
          simp only [QMove.apply, dif_pos hi, dif_neg hj]
        rw [hstep] at h
        exact absurd h (by simp)
    · have hstep : (QMove.njiinv i j).apply P = none := by simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | swap i j =>
    by_cases hi : i < P.n
    · by_cases hj : j < P.n
      · have hstep : (QMove.swap i j).apply P =
            some (substRel P (fun k => if k = (⟨i, hi⟩ : Fin P.n) then
              FreeGroup.of (⟨j, hj⟩ : Fin P.n) else if k = (⟨j, hj⟩ : Fin P.n) then
              FreeGroup.of (⟨i, hi⟩ : Fin P.n) else FreeGroup.of k)) := by
          simp only [QMove.apply, dif_pos hi, dif_pos hj]
        rw [hstep] at h
        simp only [Option.some.injEq] at h
        subst h
        exact swap_core P.rels ⟨i, hi⟩ ⟨j, hj⟩
      · have hstep : (QMove.swap i j).apply P = none := by
          simp only [QMove.apply, dif_pos hi, dif_neg hj]
        rw [hstep] at h
        exact absurd h (by simp)
    · have hstep : (QMove.swap i j).apply P = none := by simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)
  | prolong =>
    have hstep : (QMove.prolong).apply P = some ⟨P.n + 1, P.m + 1, fun k =>
        Fin.lastCases (FreeGroup.of (Fin.last P.n))
          (fun t => FreeGroup.map Fin.castSucc (P.rels t)) k⟩ := by
      simp only [QMove.apply]
    rw [hstep] at h
    simp only [Option.some.injEq] at h
    subst h
    exact prolong_core P.rels
  | delete i j w =>
    by_cases hi : i < P.n
    · by_cases hj : j < P.m
      · cases hw : mkWordOpt P.n w with
        | none =>
          have hstep : (QMove.delete i j w).apply P = none := by
            simp only [QMove.apply, dif_pos hi, dif_pos hj, hw]
          rw [hstep] at h
          exact absurd h (by simp)
        | some wk =>
          by_cases hconj : P.rels ⟨j, hj⟩ = wk * FreeGroup.of (⟨i, hi⟩ : Fin P.n) * wk⁻¹ ∨
              P.rels ⟨j, hj⟩ = wk * (FreeGroup.of (⟨i, hi⟩ : Fin P.n))⁻¹ * wk⁻¹
          · have hstep : (QMove.delete i j w).apply P = some ⟨P.n - 1, P.m - 1, fun k =>
                FreeGroup.lift (fun t => if h : t = (⟨i, hi⟩ : Fin P.n) then 1
                  else FreeGroup.of (skipIndex ⟨i, hi⟩ t h)) (P.rels (skipEmb ⟨j, hj⟩ k))⟩ := by
              simp only [QMove.apply, dif_pos hi, dif_pos hj, hw, if_pos hconj]
            rw [hstep] at h
            simp only [Option.some.injEq] at h
            subst h
            exact delete_core P.rels ⟨i, hi⟩ ⟨j, hj⟩ wk hconj
          · have hstep : (QMove.delete i j w).apply P = none := by
              simp only [QMove.apply, dif_pos hi, dif_pos hj, hw, if_neg hconj]
            rw [hstep] at h
            exact absurd h (by simp)
      · have hstep : (QMove.delete i j w).apply P = none := by
          simp only [QMove.apply, dif_pos hi, dif_neg hj]
        rw [hstep] at h
        exact absurd h (by simp)
    · have hstep : (QMove.delete i j w).apply P = none := by
        simp only [QMove.apply, dif_neg hi]
      rw [hstep] at h
      exact absurd h (by simp)

/-- **Soundness of replay**: an admissible move list that replays from `P` to `Q` presents
isomorphic groups. -/
theorem replay_sound : ∀ (ms : List QMove) (P Q : QPres), (∀ m ∈ ms, m.WF) →
    replay ms P = some Q → QEquiv P Q
  | [], P, Q, _, h => by
      have h' : P = Q := by simpa [replay] using h
      subst h'
      exact QEquiv.refl P
  | m :: ms, P, Q, hwf, h => by
      cases hstep : m.apply P with
      | none => simp [replay, hstep] at h
      | some R =>
          have hrest : replay ms R = some Q := by simpa [replay, hstep] using h
          exact QEquiv.trans (apply_sound m (hwf m (by simp)) P R hstep)
            (replay_sound ms R Q (fun m' hm' => hwf m' (by simp [hm'])) hrest)

/-- **The Q\*\*-analogue of `AC3.lean`'s `checkCert_sound`.**  A certificate that the kernel
accepts, all of whose moves are admissible, carries the start presentation to one presenting an
isomorphic group. -/
theorem checkCert_sound {ms : List QMove} {start finish : QPres}
    (hc : checkCert ms start finish = true) (hwf : CheckWF ms = true) : QEquiv start finish :=
  replay_sound ms start finish (forall_wf_of_checkWF hwf) (of_decide_eq_true hc)

/-! ## The unsoundness of the unguarded diagonal Nielsen moves -/

/-- `<x | x>`: presents the trivial group. -/
def presX : QPres := ⟨1, 1, fun _ => FreeGroup.of 0⟩

/-- `<x | x²>`: presents the group of order two. -/
def presX2 : QPres := ⟨1, 1, fun _ => FreeGroup.of (0 : Fin 1) * FreeGroup.of 0⟩

/-- The unguarded diagonal move `nij 0 0` fires on `<x | x>` and lands on `<x | x²>`. -/
theorem nij_diag_step : (QMove.nij 0 0).apply presX = some presX2 := by decide

/-- Every element of the group presented by `<x | x>` is trivial. -/
theorem presX_trivial :
    ∀ x : PresentedGroup (Set.range (fun _ : Fin 1 => FreeGroup.of (0 : Fin 1))), x = 1 := by
  intro x
  refine PresentedGroup.induction_on (C := fun y => y = 1) x ?_
  intro z
  refine FreeGroup.induction_on z ?_ ?_ ?_ ?_
  · simp
  · intro k
    have hk : k = (0 : Fin 1) := Subsingleton.elim k 0
    rw [hk]
    exact PresentedGroup.one_of_mem (x := FreeGroup.of (0 : Fin 1)) ⟨0, rfl⟩
  · intro k ih; simp [ih]
  · intro a b iha ihb; simp [iha, ihb]

/-- **The unguarded diagonal move is unsound**: `nij 0 0` carries the trivial group `<x | x>` to
`<x | x²>`, which is the group of order two.  So no soundness theorem can cover `AC5.lean`'s
`QMove.apply` without the `i ≠ j` guard on the four diagonal Nielsen moves. -/
theorem nij_diag_unsound : ¬ QEquiv presX presX2 := by
  rintro ⟨e⟩
  have hP : ∀ x : PresentedGroup (Set.range presX.rels), x = 1 := presX_trivial
  have hsub : Subsingleton (PresentedGroup (Set.range presX2.rels)) :=
    ⟨fun a b => e.symm.injective (by rw [hP (e.symm a), hP (e.symm b)])⟩
  have hrel : ∀ r ∈ Set.range (fun _ : Fin 1 => FreeGroup.of (0 : Fin 1) * FreeGroup.of 0),
      FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) r = 1 := by
    rintro r ⟨k, rfl⟩
    have hk : k = (0 : Fin 1) := Subsingleton.elim k 0
    rw [hk]
    show FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ZMod 2))
      (FreeGroup.of (0 : Fin 1) * FreeGroup.of 0) = 1
    rw [MonoidHom.map_mul, FreeGroup.lift_apply_of]
    show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1
    decide
  let φ : PresentedGroup (Set.range (fun _ : Fin 1 => FreeGroup.of (0 : Fin 1) * FreeGroup.of 0))
      →* Multiplicative (ZMod 2) :=
    PresentedGroup.toGroup
      (rels := Set.range (fun _ : Fin 1 => FreeGroup.of (0 : Fin 1) * FreeGroup.of 0))
      (f := fun _ => Multiplicative.ofAdd (1 : ZMod 2)) hrel
  haveI hsub' : Subsingleton
      (PresentedGroup (Set.range (fun _ : Fin 1 => FreeGroup.of (0 : Fin 1) * FreeGroup.of 0))) :=
    hsub
  have h1 : φ (PresentedGroup.of (0 : Fin 1)) = Multiplicative.ofAdd (1 : ZMod 2) := by
    have h0 := toGroup_mk (G := Multiplicative (ZMod 2))
      (Set.range (fun _ : Fin 1 => FreeGroup.of (0 : Fin 1) * FreeGroup.of 0))
      (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) hrel (FreeGroup.of (0 : Fin 1))
    rw [show φ (PresentedGroup.of (0 : Fin 1)) =
      FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) (FreeGroup.of (0 : Fin 1))
      from h0]
    rw [FreeGroup.lift_apply_of]
  have h2 : φ (PresentedGroup.of (0 : Fin 1)) = 1 := by
    have h3 : (PresentedGroup.of (rels := Set.range (fun _ : Fin 1 =>
        FreeGroup.of (0 : Fin 1) * FreeGroup.of 0)) (0 : Fin 1)) = 1 := Subsingleton.elim _ _
    rw [h3, MonoidHom.map_one]
  rw [h1] at h2
  exact one_ne_zero (Multiplicative.ofAdd.injective h2)

/-- Triviality of the presented group passes across a Q\*\*-move chain. -/
theorem QEquiv.subsingleton_iff {P Q : QPres} (h : QEquiv P Q) :
    Subsingleton (PresentedGroup (Set.range P.rels)) ↔
      Subsingleton (PresentedGroup (Set.range Q.rels)) := by
  obtain ⟨e⟩ := h
  constructor
  · intro hP
    haveI := hP
    exact ⟨fun a b => e.symm.injective (Subsingleton.elim _ _)⟩
  · intro hQ
    haveI := hQ
    exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- **A certificate moves a presentation to one that is trivial exactly when the original is.** -/
theorem checkCert_subsingleton_iff {ms : List QMove} {start finish : QPres}
    (hc : checkCert ms start finish = true) (hwf : CheckWF ms = true) :
    Subsingleton (PresentedGroup (Set.range start.rels)) ↔
      Subsingleton (PresentedGroup (Set.range finish.rels)) :=
  (checkCert_sound hc hwf).subsingleton_iff

/-! ## Non-vacuity controls for the admissibility predicate -/

/-- The admissibility predicate rejects exactly the diagonal Nielsen move. -/
theorem wfBool_nij_diag : QMove.wfBool (QMove.nij 0 0) = false := by decide

/-- ... and accepts its non-diagonal instance. -/
theorem wfBool_nij_offdiag : QMove.wfBool (QMove.nij 0 1) = true := by decide

/-- The list predicate accepts a list of admissible moves ... -/
theorem checkWF_accepts : CheckWF [QMove.nij 0 1, QMove.inv 0, QMove.delete 0 0
    [(0, true)]] = true := by decide

/-- ... and rejects the list containing the diagonal move. -/
theorem checkWF_rejects : CheckWF [QMove.inv 0, QMove.nji 2 2] = false := by decide

/-- Every move of the list of the `presX`/`presX2` step is admissible, and the step is exactly the
diagonal move that the predicate rejects: this is the sense in which the guard is not vacuous. -/
theorem wfBool_nij_diag_zero : QMove.wfBool (QMove.nij (0 : Nat) 0) = false ∧
    (QMove.nij 0 0).apply presX = some presX2 := by
  decide

end AC5
