/-
# The Metzler recipe's other boundary: shifting `j` by `k` in seven AC moves

`AC8.metzler_recipe` moves `metz k m 1` to `metz k m j` when `j ∣ k - 1`.  This file proves a
second, disjoint family of reachabilities: **`metz k m j` and `metz k m (j + k)` are
Andrews-Curtis equivalent, by an explicit 7-move list, for every `k, m, j`**.

The construction (rank two, relators `(y^m, [x^j,y], x^k)`, zero-based positions 1 and 2):

    conj 1 by x^k            r_1 = [x^j,y]        -> x^k [x^j,y] x^-k
    mul 1 2                  r_1                 -> x^k [x^j,y] x^-k . x^k
    inv 2                    r_2 = x^k           -> x^-k
    conj 2 by y              r_2                 -> y x^-k y^-1
    mul 1 2                  r_1                 -> x^k [x^j,y] x^-k x^k y x^-k y^-1
    conj 2 by y^-1           r_2                 -> x^-k
    inv 2                    r_2                 -> x^k

and the new middle relator is `x^k [x^j,y] y x^-k y^-1 = [x^(j+k), y]`: the identity
`[x^(j+k),y] = [x^j,y]^(x^k) . [x^k,y]` with `[x^k,y] = x^k . (y x^-k y^-1)`, a product of two
conjugates of the relator `x^k`.  Every move is rank-preserving, so this is an ordinary
Andrews-Curtis equivalence, not merely a `Q**` one.

Consequence (`reachable_four_odd`): at `k = 4` every ODD `j` is reachable from `metz 4 m 1` —
`j = 1 (mod 4)` by shifts alone, `j = 3 (mod 4)` by one recipe step (`t = 1`) followed by
shifts.  Combined with `MetzlerSharp.not_mulEquiv_four_even` (every even `j` is obstructed by
the presented group) this gives a complete classification of the parameter boundary at `k = 4`
for even `m`: `metz 4 m j` is equivalent to `metz 4 m 1` exactly when `j` is odd.

Nothing here proves or disproves the Andrews-Curtis conjecture.
-/
import AC8

namespace MetzlerShift

open AC8

/-! ## The two rank-two move lemmas `AC8.lean` does not need -/

theorem ap2_conj_2 (r : Fin 3 → Word 2) (w : Word 2) :
    QMove.apply (.conj 2 (lettersOf w)) (st2 r) = some (st2 (upd r 2 (w * r 2 * w⁻¹))) := by
  simp only [QMove.apply, mkWordOpt_lettersOf]
  rfl

theorem ap2_mul_12 (r : Fin 3 → Word 2) :
    QMove.apply (.mul 1 2) (st2 r) = some (st2 (upd r 1 (r 1 * r 2))) := by
  simp only [QMove.apply]
  rfl

/-! ## The block -/

/-- The 7-move list of the shift, with the conjugator `C` (which will be `x^k`) given explicitly. -/
def shiftMs (C : Word 2) : List QMove :=
  [.conj 1 (lettersOf C), .mul 1 2, .inv 2, .conj 2 (lettersOf y2), .mul 1 2,
   .conj 2 (lettersOf (y2⁻¹)), .inv 2]

/-- The middle relator produced by the block: `C B C^-1 C y C^-1 y^-1`. -/
def shiftWord (B C : Word 2) : Word 2 := C * B * C⁻¹ * C * y2 * C⁻¹ * y2⁻¹

/-- The block, symbolically on an arbitrary triple `(A, B, C)` of relators. -/
theorem shift_block (A B C : Word 2) :
    replay (shiftMs C) (q2 A B C) = some (q2 A (shiftWord B C) C) := by
  have s1 : QMove.apply (.conj 1 (lettersOf C)) (q2 A B C)
      = some (q2 A (C * B * C⁻¹) C) := by
    simp only [ap2_conj_1, upd_q2f_1, q2f_0, q2f_1, q2f_2]
  have s2 : QMove.apply (.mul 1 2) (q2 A (C * B * C⁻¹) C)
      = some (q2 A ((C * B * C⁻¹) * C) C) := by
    simp only [ap2_mul_12, upd_q2f_1, q2f_0, q2f_1, q2f_2]
  have s3 : QMove.apply (.inv 2) (q2 A ((C * B * C⁻¹) * C) C)
      = some (q2 A ((C * B * C⁻¹) * C) C⁻¹) := by
    simp only [ap2_inv_2, upd_q2f_2, q2f_0, q2f_1, q2f_2]
  have s4 : QMove.apply (.conj 2 (lettersOf y2)) (q2 A ((C * B * C⁻¹) * C) C⁻¹)
      = some (q2 A ((C * B * C⁻¹) * C) (y2 * C⁻¹ * y2⁻¹)) := by
    simp only [ap2_conj_2, upd_q2f_2, q2f_0, q2f_1, q2f_2]
  have s5 : QMove.apply (.mul 1 2) (q2 A ((C * B * C⁻¹) * C) (y2 * C⁻¹ * y2⁻¹))
      = some (q2 A (((C * B * C⁻¹) * C) * (y2 * C⁻¹ * y2⁻¹)) (y2 * C⁻¹ * y2⁻¹)) := by
    simp only [ap2_mul_12, upd_q2f_1, q2f_0, q2f_1, q2f_2]
  have s6 : QMove.apply (.conj 2 (lettersOf (y2⁻¹))) (q2 A (((C * B * C⁻¹) * C) * (y2 * C⁻¹ * y2⁻¹))
        (y2 * C⁻¹ * y2⁻¹))
      = some (q2 A (((C * B * C⁻¹) * C) * (y2 * C⁻¹ * y2⁻¹))
          (y2⁻¹ * (y2 * C⁻¹ * y2⁻¹) * y2⁻¹⁻¹)) := by
    simp only [ap2_conj_2, upd_q2f_2, q2f_0, q2f_1, q2f_2]
  have s7 : QMove.apply (.inv 2) (q2 A (((C * B * C⁻¹) * C) * (y2 * C⁻¹ * y2⁻¹))
        (y2⁻¹ * (y2 * C⁻¹ * y2⁻¹) * y2⁻¹⁻¹))
      = some (q2 A (((C * B * C⁻¹) * C) * (y2 * C⁻¹ * y2⁻¹))
          (y2⁻¹ * (y2 * C⁻¹ * y2⁻¹) * y2⁻¹⁻¹)⁻¹) := by
    simp only [ap2_inv_2, upd_q2f_2, q2f_0, q2f_1, q2f_2]
  have h1 : ((C * B * C⁻¹) * C) * (y2 * C⁻¹ * y2⁻¹) = shiftWord B C := by
    simp only [shiftWord]
    group
  have h2 : (y2⁻¹ * (y2 * C⁻¹ * y2⁻¹) * y2⁻¹⁻¹)⁻¹ = C := by
    group
  simp only [shiftMs, replay, s1, s2, s3, s4, s5, s6, s7, Option.bind_some]
  simp only [h1, h2]

/-- The algebra of the middle relator: for `C = x^k` and `B = [x^j,y]` it is `[x^(j+k), y]`. -/
theorem shiftWord_com (j k : Nat) :
    shiftWord (x2 ^ j * y2 * (x2 ^ j)⁻¹ * y2⁻¹) (x2 ^ k) =
      x2 ^ (j + k) * y2 * (x2 ^ (j + k))⁻¹ * y2⁻¹ := by
  simp only [shiftWord]
  conv_rhs => rw [pow_add]
  group

/-! ## The shift theorem -/

/-- **`metz k m j` and `metz k m (j + k)` are AC-equivalent in 7 moves.** -/
theorem shift_step (k m j : Nat) :
    replay (shiftMs (x2 ^ k)) (metz k m j) = some (metz k m (j + k)) := by
  have h := shift_block (y2 ^ m) (x2 ^ j * y2 * (x2 ^ j)⁻¹ * y2⁻¹) (x2 ^ k)
  rw [shiftWord_com] at h
  simpa [metz] using h

/-- Iterating the shift: `metz k m j` reaches `metz k m (j + s*k)` in `s` blocks. -/
theorem shift_iter (k m j : Nat) : ∀ s : Nat,
    ∃ ms : List QMove, replay ms (metz k m j) = some (metz k m (j + s * k))
  | 0 => ⟨[], by simp [replay]⟩
  | (s + 1) => by
      obtain ⟨ms, hms⟩ := shift_iter k m j s
      have hstep := shift_step k m (j + s * k)
      refine ⟨ms ++ shiftMs (x2 ^ k), ?_⟩
      have hfin : replay (shiftMs (x2 ^ k)) (metz k m (j + s * k))
          = some (metz k m (j + (s + 1) * k)) := by
        rw [show j + s * k + k = j + (s + 1) * k from by ring] at hstep
        exact hstep
      exact replay_concat ms (shiftMs (x2 ^ k)) _ _ _ hms hfin

/-! ## The `k = 4` classification: every odd `j` is reachable -/

/-- Arithmetic: an odd number is `1 + 4u` or `3 + 4u`. -/
theorem odd_eq_one_or_three_mod_four (j : Nat) (hj : Odd j) :
    (∃ u, j = 1 + u * 4) ∨ (∃ u, j = 3 + u * 4) := by
  obtain ⟨s, rfl⟩ : ∃ s, j = 2 * s + 1 := hj
  induction s with
  | zero => exact Or.inl ⟨0, by ring⟩
  | succ s ih =>
      rcases ih with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact Or.inr ⟨u, by
          rw [show 2 * (s + 1) + 1 = (2 * s + 1) + 2 from by ring, hu]; ring⟩
      · exact Or.inl ⟨u + 1, by
          rw [show 2 * (s + 1) + 1 = (2 * s + 1) + 2 from by ring, hu]; ring⟩

/-- At `k = 4`, `j ≡ 1 (mod 4)` is reachable from `j = 1` by shifts alone. -/
theorem reachable_four_one (m u : Nat) :
    ∃ ms : List QMove, replay ms (metz 4 m 1) = some (metz 4 m (1 + u * 4)) := by
  obtain ⟨ms, hms⟩ := shift_iter 4 m 1 u
  exact ⟨ms, hms⟩

/-- At `k = 4`, `j ≡ 3 (mod 4)` is reachable: one recipe step (`t = 1`, `4 = 1 + 1*3`) to `j = 3`,
then shifts. -/
theorem reachable_four_three (m u : Nat) :
    ∃ ms : List QMove, replay ms (metz 4 m 1) = some (metz 4 m (3 + u * 4)) := by
  obtain ⟨ms₁, h₁⟩ := metzler_recipe 4 m 1 3 rfl
  obtain ⟨ms₂, h₂⟩ := shift_iter 4 m 3 u
  exact ⟨ms₁ ++ ms₂, replay_concat ms₁ ms₂ _ _ _ h₁ h₂⟩

/-- **Every odd `j` is reachable from `metz 4 m 1`.** -/
theorem reachable_four_odd (m j : Nat) (hj : Odd j) :
    ∃ ms : List QMove, replay ms (metz 4 m 1) = some (metz 4 m j) := by
  rcases odd_eq_one_or_three_mod_four j hj with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · exact reachable_four_one m u
  · exact reachable_four_three m u

/- Axiom audit. -/
#print axioms ap2_conj_2
#print axioms ap2_mul_12
#print axioms shift_block
#print axioms shiftWord_com
#print axioms shift_step
#print axioms shift_iter
#print axioms odd_eq_one_or_three_mod_four
#print axioms reachable_four_one
#print axioms reachable_four_three
#print axioms reachable_four_odd

end MetzlerShift
