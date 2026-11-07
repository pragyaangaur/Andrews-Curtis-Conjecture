/-
Free reduction as the scored verifier performs it, and its agreement with
the free group normal form.

The scored verifier `ac-r2-v1` (commit a0fd6e6 of the competition
repository) represents a word over two generators as a tuple of nonzero
integers, where `1` is `x`, `-1` is `x^-1`, `2` is `y` and `-2` is
`y^-1`. After every move it calls `free_reduce`, which scans the word
from left to right, keeps an output stack, and pops the top of the stack
when the incoming letter is the inverse of that top.

This file formalises that function on the word encoding Mathlib already
uses for free groups, namely `List (Fin 2 × Bool)` where the second
component is the exponent sign. It proves that the result is a left fold
(`loop_eq_foldl`, `freeReduce_eq_foldl`), that the output is freely
reduced (`freeReduce_isReduced`), that it is idempotent, and that it
equals Mathlib's maximal reduction `FreeGroup.reduce`
(`freeReduce_eq_reduce`). The last step makes free reduction a normal
form: two words have the same free reduction exactly when they have the
same product in the free group (`freeReduce_eq_iff`).

The final section writes the verifier's fourteen move branches as a
function on pairs of words, and proves that each branch, including its
internal free reductions, is reachable by `AC.Step` moves in the
competition's own statement file when the two relators are read in the
free group. A whole verified path therefore turns into an
`AC.Reachable` statement from the group element of the initial
presentation to the standard relator tuple.

No claim is made here about the conjecture itself. This is a statement
about two implementations of free reduction and about the move table.
-/
import Mathlib.Tactic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.List.Chain
import AC

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace VFree

variable {α : Type} [DecidableEq α]

/-! ### 1. Letters and the verifier's left fold -/

/-- The inverse of one letter: the same generator with the exponent flipped. -/
def flip (a : α × Bool) : α × Bool := (a.1, !a.2)

@[simp] theorem flip_flip (a : α × Bool) : flip (flip a) = a := by
  obtain ⟨g, b⟩ := a
  cases b <;> rfl

@[simp] theorem flip_fst (a : α × Bool) : (flip a).1 = a.1 := rfl

/-- The output stack of the verifier's loop, kept with its top at the head. -/
def loop : List (α × Bool) → List (α × Bool) → List (α × Bool)
  | [], out => out
  | a :: w, out =>
    if out.head? = some (flip a) then loop w out.tail else loop w (a :: out)

/-- One step of a left fold: cancel the next letter against the top of the
output stack when they are inverse, and push it otherwise. -/
def step (out : List (α × Bool)) (a : α × Bool) : List (α × Bool) :=
  if out.head? = some (flip a) then out.tail else a :: out

@[simp] theorem loop_nil (out : List (α × Bool)) : loop ([] : List (α × Bool)) out = out := by
  simp [loop]

theorem loop_cons_nil (a : α × Bool) (w : List (α × Bool)) :
    loop (a :: w) [] = loop w [a] := by simp [loop]

theorem loop_cons_cancel (a : α × Bool) (w t : List (α × Bool)) :
    loop (a :: w) (flip a :: t) = loop w t := by simp [loop]

theorem loop_cons_push (a b : α × Bool) (w t : List (α × Bool)) (h : b ≠ flip a) :
    loop (a :: w) (b :: t) = loop w (a :: b :: t) := by simp [loop, h]

/-- The verifier's `free_reduce`: the loop started on the empty stack, read
out bottom first, because the loop keeps the top of the stack at the head. -/
def freeReduce (w : List (α × Bool)) : List (α × Bool) := (loop w []).reverse

theorem loop_eq_foldl (w out : List (α × Bool)) : loop w out = w.foldl step out := by
  induction w generalizing out with
  | nil => rfl
  | cons a w ih =>
    rw [List.foldl_cons]
    cases out with
    | nil =>
      rw [loop_cons_nil, ih]
      simp [step]
    | cons b t =>
      by_cases hb : b = flip a
      · subst hb
        rw [loop_cons_cancel, ih]
        simp [step]
      · rw [loop_cons_push a b w t hb, ih]
        simp [step, hb]

/-- The verifier's free reduction is the left fold of `step` over the word. -/
theorem freeReduce_eq_foldl (w : List (α × Bool)) :
    freeReduce w = (w.foldl step []).reverse := by
  simp [freeReduce, loop_eq_foldl]

/-! ### 2. The group element of a word -/

/-- The free group element of a letter, with `true` meaning the generator
itself and `false` meaning its inverse. -/
def letter (a : α × Bool) : FreeGroup α :=
  cond a.2 (FreeGroup.of a.1) ((FreeGroup.of a.1)⁻¹)

@[simp] theorem letter_flip (a : α × Bool) : letter (flip a) = (letter a)⁻¹ := by
  obtain ⟨g, b⟩ := a
  cases b <;> simp [letter, flip]

/-- The free group element of a word, multiplied out from left to right. -/
def wordProd (L : List (α × Bool)) : FreeGroup α := (L.map letter).prod

@[simp] theorem wordProd_nil : wordProd ([] : List (α × Bool)) = 1 := rfl

@[simp] theorem wordProd_cons (a : α × Bool) (L : List (α × Bool)) :
    wordProd (a :: L) = letter a * wordProd L := by
  simp [wordProd]

@[simp] theorem wordProd_singleton (a : α × Bool) : wordProd [a] = letter a := by
  simp [wordProd]

theorem wordProd_append (L₁ L₂ : List (α × Bool)) :
    wordProd (L₁ ++ L₂) = wordProd L₁ * wordProd L₂ := by
  simp [wordProd, List.prod_append]

@[simp] theorem wordProd_append_singleton (L : List (α × Bool)) (a : α × Bool) :
    wordProd (L ++ [a]) = wordProd L * letter a := by
  rw [wordProd_append]
  simp [wordProd, wordProd_cons]

/-- The formal inverse of a word, exactly as `core.py`'s `invert` computes it. -/
def invWord (L : List (α × Bool)) : List (α × Bool) := L.reverse.map flip

@[simp] theorem invWord_nil : invWord ([] : List (α × Bool)) = [] := rfl

theorem invWord_cons (a : α × Bool) (L : List (α × Bool)) :
    invWord (a :: L) = invWord L ++ [flip a] := by
  simp [invWord, List.map_append]

theorem wordProd_invWord (L : List (α × Bool)) : wordProd (invWord L) = (wordProd L)⁻¹ := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [invWord_cons, wordProd_append, ih, wordProd_singleton, wordProd_cons, mul_inv_rev,
      letter_flip]

/-- The stack invariant of the verifier's loop: the element of the stack read
bottom first, times the element of the unread input, is the element of the
whole word. -/
theorem wordProd_loop (w out : List (α × Bool)) :
    wordProd (loop w out).reverse = wordProd out.reverse * wordProd w := by
  induction w generalizing out with
  | nil => simp
  | cons a w ih =>
    cases out with
    | nil =>
      rw [loop_cons_nil, ih [a]]
      simp
    | cons b t =>
      by_cases hb : b = flip a
      · subst hb
        rw [loop_cons_cancel, ih t, List.reverse_cons, wordProd_append_singleton, wordProd_cons,
          letter_flip]
        group
      · rw [loop_cons_push a b w t hb, ih (a :: b :: t), List.reverse_cons,
          wordProd_append_singleton, wordProd_cons]
        group

/-- Free reduction does not change the element of the free group. -/
theorem wordProd_freeReduce (L : List (α × Bool)) : wordProd (freeReduce L) = wordProd L := by
  show wordProd (loop L []).reverse = wordProd L
  rw [wordProd_loop]
  simp

/-! ### 3. The output of the loop is freely reduced -/

/-- Two adjacent letters are compatible when they are not mutually inverse. -/
def Compat (a b : α × Bool) : Prop := a.1 = b.1 → a.2 = b.2

theorem compat_comm (a b : α × Bool) : Compat a b ↔ Compat b a := by
  obtain ⟨g, c⟩ := a
  obtain ⟨g', c'⟩ := b
  cases c <;> cases c' <;> simp [Compat, ne_comm]

theorem compat_iff_ne_flip (a b : α × Bool) : Compat a b ↔ b ≠ flip a := by
  obtain ⟨g, c⟩ := a
  obtain ⟨g', c'⟩ := b
  cases c <;> cases c' <;> simp [Compat, flip, ne_comm]

theorem isReduced_cons_iff (a : α × Bool) (out : List (α × Bool)) :
    FreeGroup.IsReduced (a :: out) ↔ out.head? ≠ some (flip a) ∧ FreeGroup.IsReduced out := by
  cases out with
  | nil => simp [FreeGroup.IsReduced.nil, FreeGroup.IsReduced.singleton]
  | cons b t =>
    have hc : FreeGroup.IsReduced (a :: b :: t)
        ↔ Compat a b ∧ FreeGroup.IsReduced (b :: t) := FreeGroup.isReduced_cons_cons
    rw [hc, compat_iff_ne_flip]
    simp

theorem isReduced_tail {a : α × Bool} {t : List (α × Bool)}
    (h : FreeGroup.IsReduced (a :: t)) : FreeGroup.IsReduced t := by
  cases t with
  | nil => exact FreeGroup.IsReduced.nil
  | cons b s => exact (FreeGroup.isReduced_cons_cons.1 h).2

theorem isReduced_loop (w out : List (α × Bool)) (h : FreeGroup.IsReduced out) :
    FreeGroup.IsReduced (loop w out) := by
  induction w generalizing out with
  | nil => rw [loop_nil]; exact h
  | cons a w ih =>
    cases out with
    | nil =>
      rw [loop_cons_nil]
      exact ih [a] FreeGroup.IsReduced.singleton
    | cons b t =>
      by_cases hb : b = flip a
      · subst hb
        rw [loop_cons_cancel]
        exact ih t (isReduced_tail h)
      · rw [loop_cons_push a b w t hb]
        exact ih _ (isReduced_cons_iff a (b :: t) |>.2 ⟨by simpa using hb, h⟩)

theorem isReduced_reverse_iff {l : List (α × Bool)} :
    FreeGroup.IsReduced l.reverse ↔ FreeGroup.IsReduced l := by
  show l.reverse.IsChain (fun a b => a.1 = b.1 → a.2 = b.2)
      ↔ l.IsChain (fun a b => a.1 = b.1 → a.2 = b.2)
  rw [List.isChain_reverse]
  exact List.IsChain.iff (fun a b => (compat_comm a b).symm)

/-- The verifier's free reduction always returns a freely reduced word. -/
theorem freeReduce_isReduced (w : List (α × Bool)) : FreeGroup.IsReduced (freeReduce w) := by
  show FreeGroup.IsReduced (loop w []).reverse
  rw [isReduced_reverse_iff]
  exact isReduced_loop w [] FreeGroup.IsReduced.nil

/-! ### 4. Agreement with Mathlib's maximal reduction -/

theorem wordProd_eq_lift (L : List (α × Bool)) :
    wordProd L = FreeGroup.lift (FreeGroup.of) (FreeGroup.mk L) := rfl

theorem lift_of_apply (x : FreeGroup α) : FreeGroup.lift (FreeGroup.of) x = x :=
  (FreeGroup.lift_unique (MonoidHom.id (FreeGroup α)) (fun _ => rfl) (x := x)).symm

/-- Two words present the same element of the free group exactly when their
products agree. -/
theorem mk_eq_iff_wordProd (L₁ L₂ : List (α × Bool)) :
    FreeGroup.mk L₁ = FreeGroup.mk L₂ ↔ wordProd L₁ = wordProd L₂ := by
  constructor
  · intro h
    rw [wordProd_eq_lift, wordProd_eq_lift, h]
  · intro h
    rw [← lift_of_apply (FreeGroup.mk L₁), ← lift_of_apply (FreeGroup.mk L₂),
      ← wordProd_eq_lift, ← wordProd_eq_lift]
    exact h

/-- **The bridge.** The verifier's left fold is Mathlib's maximal reduction. -/
theorem freeReduce_eq_reduce (L : List (α × Bool)) : freeReduce L = FreeGroup.reduce L := by
  have hred : FreeGroup.IsReduced (freeReduce L) := freeReduce_isReduced L
  have hmk : FreeGroup.mk (freeReduce L) = FreeGroup.mk L :=
    (mk_eq_iff_wordProd _ _).2 (wordProd_freeReduce L)
  have h := FreeGroup.reduce.sound hmk
  rwa [FreeGroup.IsReduced.reduce_eq hred] at h

/-- The verifier's free reduction is idempotent. -/
theorem freeReduce_idem (L : List (α × Bool)) : freeReduce (freeReduce L) = freeReduce L := by
  rw [freeReduce_eq_reduce, freeReduce_eq_reduce, FreeGroup.reduce.idem]

/-- Free reduction is a normal form: two words reduce to the same word exactly
when they have the same product in the free group. -/
theorem freeReduce_eq_iff (L₁ L₂ : List (α × Bool)) :
    freeReduce L₁ = freeReduce L₂ ↔ wordProd L₁ = wordProd L₂ := by
  constructor
  · intro h
    rw [← wordProd_freeReduce L₁, ← wordProd_freeReduce L₂, h]
  · intro h
    rw [freeReduce_eq_reduce, freeReduce_eq_reduce,
      FreeGroup.reduce.sound ((mk_eq_iff_wordProd _ _).2 h)]

/-- Inserting a letter and its inverse changes nothing. -/
theorem freeReduce_insert_cancel (u v : List (α × Bool)) (a : α × Bool) :
    freeReduce (u ++ a :: flip a :: v) = freeReduce (u ++ v) := by
  rw [freeReduce_eq_iff]
  simp [wordProd_append, wordProd_cons]

/-- Multiplication in the free group is free reduction of the concatenation. -/
theorem wordProd_freeReduce_append (u v : List (α × Bool)) :
    wordProd (freeReduce (u ++ v)) = wordProd u * wordProd v := by
  rw [wordProd_freeReduce, wordProd_append]

/-- Free reduction of a concatenation only depends on the two factors. -/
theorem freeReduce_append_eq (u v : List (α × Bool)) :
    freeReduce (u ++ v) = freeReduce (freeReduce u ++ freeReduce v) := by
  rw [freeReduce_eq_iff]
  simp [wordProd_append, wordProd_freeReduce]

/-! ### 5. The verifier's own integer encoding -/

/- The verifier's `free_reduce` written on its own integer words. The two
functions below are the same algorithm as `loop` and `freeReduce`, with
negation of an integer in place of flipping a sign bit. The theorem
`freeReduceInt_map` states that the translation to `(generator, sign)` letters
carries one to the other. -/
namespace IntWord


def Legal (z : ℤ) : Prop := z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2

def decode (z : ℤ) : Fin 2 × Bool :=
  if z = 1 then ((0 : Fin 2), true)
  else if z = -1 then ((0 : Fin 2), false)
  else if z = 2 then ((1 : Fin 2), true)
  else if z = -2 then ((1 : Fin 2), false)
  else ((0 : Fin 2), true)

theorem legal_neg {z : ℤ} (h : Legal z) : Legal (-z) := by
  rcases h with h | h | h | h <;> subst h <;> simp [Legal]

theorem decode_neg {z : ℤ} (h : Legal z) : decode (-z) = flip (decode z) := by
  rcases h with h | h | h | h <;> subst h <;> simp [decode, flip]

theorem decode_inj {y z : ℤ} (hy : Legal y) (hz : Legal z) (h : decode y = decode z) : y = z := by
  rcases hy with hy | hy | hy | hy <;> rcases hz with hz | hz | hz | hz <;>
    subst_vars <;> simp [decode] at h ⊢

def loopInt : List ℤ → List ℤ → List ℤ
  | [], out => out
  | a :: w, out => if out.head? = some (-a) then loopInt w out.tail else loopInt w (a :: out)

def freeReduceInt (w : List ℤ) : List ℤ := (loopInt w []).reverse

@[simp] theorem loopInt_nil (out : List ℤ) : loopInt ([] : List ℤ) out = out := by simp [loopInt]

theorem loopInt_cons_nil (a : ℤ) (w : List ℤ) :
    loopInt (a :: w) [] = loopInt w [a] := by simp [loopInt]

theorem loopInt_cons_cancel (a : ℤ) (w t : List ℤ) :
    loopInt (a :: w) (-a :: t) = loopInt w t := by simp [loopInt]

theorem loopInt_cons_push (a b : ℤ) (w t : List ℤ) (h : b ≠ -a) :
    loopInt (a :: w) (b :: t) = loopInt w (a :: b :: t) := by simp [loopInt, h]

theorem head?_map_decode (s : List ℤ) : (s.map decode).head? = s.head?.map decode := by
  cases s <;> rfl

theorem loopInt_map (w : List ℤ) (out : List ℤ) (hw : ∀ a ∈ w, Legal a)
    (hout : ∀ b ∈ out, Legal b) :
    (loopInt w out).map decode = loop (w.map decode) (out.map decode) := by
  induction w generalizing out with
  | nil => rw [loopInt_nil]; simp
  | cons a w ih =>
    have ha : Legal a := hw a (by simp)
    have hw' : ∀ b ∈ w, Legal b := fun b hb => hw b (by simp [hb])
    cases out with
    | nil =>
      rw [loopInt_cons_nil]
      simp only [List.map_cons, List.map_nil, loop_cons_nil]
      rw [ih [a] hw' (by simp [ha])]
      simp
    | cons b t =>
      have hb : Legal b := hout b (by simp)
      have ht : ∀ c ∈ t, Legal c := fun c hc => hout c (by simp [hc])
      by_cases hba : b = -a
      · subst hba
        rw [loopInt_cons_cancel]
        simp only [List.map_cons]
        rw [decode_neg ha, loop_cons_cancel, ih t hw' ht]
      · have hne : decode b ≠ flip (decode a) := by
          intro h
          rw [← decode_neg ha] at h
          exact hba (decode_inj hb (legal_neg ha) h)
        have hout' : ∀ c ∈ a :: b :: t, Legal c := by
          intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact ha
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hb
          exact ht c hc
        rw [loopInt_cons_push a b w t hba]
        simp only [List.map_cons]
        rw [loop_cons_push (decode a) (decode b) (w.map decode) (t.map decode) hne,
          ih (a :: b :: t) hw' hout']
        simp

theorem freeReduceInt_map (w : List ℤ) (hw : ∀ a ∈ w, Legal a) :
    (freeReduceInt w).map decode = freeReduce (w.map decode) := by
  show ((loopInt w []).reverse).map decode = _
  rw [List.map_reverse, loopInt_map w [] hw (by simp)]
  rfl

/-- The verifier's own reduction of the first relator of `ms-train-0160`,
which is already freely reduced. -/
example : freeReduceInt [-1, 2, 1, -2, -2] = [-1, 2, 1, -2, -2] := by decide

/-- A word that does cancel, reduced by the verifier's own algorithm. -/
example : freeReduceInt [1, -1, 2, -2, -1] = [-1] := by decide

end IntWord

/-! ### 6. The fourteen verifier moves at the level of the free group -/

namespace RankTwo

/-- A verifier state: an ordered pair of relator words over `x, x^-1, y, y^-1`,
each written as a list of letters `(generator, exponent sign)`. -/
abbrev VState := List (Fin 2 × Bool) × List (Fin 2 × Bool)

/-- The letter `x`. -/
def xp : Fin 2 × Bool := (0, true)
/-- The letter `x^-1`. -/
def xm : Fin 2 × Bool := (0, false)
/-- The letter `y`. -/
def yp : Fin 2 × Bool := (1, true)
/-- The letter `y^-1`. -/
def ym : Fin 2 × Bool := (1, false)

@[simp] theorem flip_xp : flip xp = xm := rfl
@[simp] theorem flip_xm : flip xm = xp := rfl
@[simp] theorem flip_yp : flip yp = ym := rfl
@[simp] theorem flip_ym : flip ym = yp := rfl

/-- The verifier's `apply_move`, with exactly the fourteen branches of
`core.py`. The final branch returns the state unchanged; it is unreachable
for move ids below fourteen. -/
def applyMove (s : VState) (m : ℕ) : VState :=
  if m = 0 then (invWord s.1, s.2) else
  if m = 1 then (s.1, invWord s.2) else
  if m = 2 then (freeReduce (s.1 ++ s.2), s.2) else
  if m = 3 then (freeReduce (s.1 ++ invWord s.2), s.2) else
  if m = 4 then (s.1, freeReduce (s.2 ++ s.1)) else
  if m = 5 then (s.1, freeReduce (s.2 ++ invWord s.1)) else
  if m = 6 then (freeReduce (xp :: (s.1 ++ [xm])), s.2) else
  if m = 7 then (freeReduce (xm :: (s.1 ++ [xp])), s.2) else
  if m = 8 then (freeReduce (yp :: (s.1 ++ [ym])), s.2) else
  if m = 9 then (freeReduce (ym :: (s.1 ++ [yp])), s.2) else
  if m = 10 then (s.1, freeReduce (xp :: (s.2 ++ [xm]))) else
  if m = 11 then (s.1, freeReduce (xm :: (s.2 ++ [xp]))) else
  if m = 12 then (s.1, freeReduce (yp :: (s.2 ++ [ym]))) else
  if m = 13 then (s.1, freeReduce (ym :: (s.2 ++ [yp]))) else s

/-- The target of the scored problem: the ordered pair `(x, y)`. -/
def target : VState := ([xp], [yp])

/-- The group level state of a verifier state, exactly the `AC.Relators`
tuple that the competition's `AC.lean` uses. -/
def toRelators (s : VState) : AC.Relators 2 :=
  fun i => if i = 0 then wordProd s.1 else wordProd s.2

@[simp] theorem toRelators_zero (s : VState) : toRelators s 0 = wordProd s.1 := by
  simp [toRelators]

@[simp] theorem toRelators_one (s : VState) : toRelators s 1 = wordProd s.2 := by
  simp [toRelators]

theorem relators_ext {R S : AC.Relators 2} (h0 : R 0 = S 0) (h1 : R 1 = S 1) : R = S := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

@[simp] theorem update_zero_zero {X : Type} (R : Fin 2 → X) (v : X) :
    Function.update R 0 v 0 = v := by simp

@[simp] theorem update_zero_one {X : Type} (R : Fin 2 → X) (v : X) :
    Function.update R 0 v 1 = R 1 := by simp

@[simp] theorem update_one_zero {X : Type} (R : Fin 2 → X) (v : X) :
    Function.update R 1 v 0 = R 0 := by simp

@[simp] theorem update_one_one {X : Type} (R : Fin 2 → X) (v : X) :
    Function.update R 1 v 1 = v := by simp

theorem wordProd_conj (g : α) (w : List (α × Bool)) :
    wordProd ((g, true) :: (w ++ [(g, false)]))
      = FreeGroup.of g * wordProd w * (FreeGroup.of g)⁻¹ := by
  rw [wordProd_cons, wordProd_append_singleton]
  simp [letter, mul_assoc]

theorem wordProd_conj_inv (g : α) (w : List (α × Bool)) :
    wordProd ((g, false) :: (w ++ [(g, true)]))
      = (FreeGroup.of g)⁻¹ * wordProd w * FreeGroup.of g := by
  rw [wordProd_cons, wordProd_append_singleton]
  simp [letter, mul_assoc]

/-- The conjugation identity in the shape the move proofs reach. -/
theorem letter_conj_left (g : α) (w : List (α × Bool)) :
    letter (g, true) * (wordProd w * letter (g, false))
      = FreeGroup.of g * wordProd w * (FreeGroup.of g)⁻¹ := by
  simp [letter, mul_assoc]

/-- The inverse conjugation identity in the shape the move proofs reach. -/
theorem letter_conj_inv_left (g : α) (w : List (α × Bool)) :
    letter (g, false) * (wordProd w * letter (g, true))
      = (FreeGroup.of g)⁻¹ * wordProd w * FreeGroup.of g := by
  simp [letter, mul_assoc]

/-! Each of the fourteen verifier branches is an `AC.Reachable` step in the
group level model. Inversions and multiplications by the other relator are
one `AC.Step`. Multiplication by the inverse of the other relator is three,
because the other relator has to be inverted and restored. Conjugations are
one `AC.Step`, by the conjugating letter or by its inverse. -/

theorem reach_zero (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 0)) := by
  have h : toRelators (applyMove s 0)
      = Function.update (toRelators s) 0 ((toRelators s) 0)⁻¹ := by
    apply relators_ext <;> simp [applyMove, wordProd_invWord]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.inv _ 0)

theorem reach_one (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 1)) := by
  have h : toRelators (applyMove s 1)
      = Function.update (toRelators s) 1 ((toRelators s) 1)⁻¹ := by
    apply relators_ext <;> simp [applyMove, wordProd_invWord]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.inv _ 1)

theorem reach_two (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 2)) := by
  have h : toRelators (applyMove s 2)
      = Function.update (toRelators s) 0 ((toRelators s) 0 * (toRelators s) 1) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce_append]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.mulRight _ 0 1 (by decide))

theorem reach_three (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 3)) := by
  let R := toRelators s
  let R₁ := Function.update R 1 ((R 1)⁻¹)
  let R₂ := Function.update R₁ 0 ((R₁ 0) * (R₁ 1))
  have h : toRelators (applyMove s 3) = Function.update R₂ 1 ((R₂ 1)⁻¹) := by
    show toRelators (applyMove s 3) = _
    simp only [R₂, R₁, R]
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce_append, wordProd_invWord]
  rw [h]
  have h1 : AC.Step R R₁ := AC.Step.inv R 1
  have h2 : AC.Step R₁ R₂ := AC.Step.mulRight R₁ 0 1 (by decide)
  have h3 : AC.Step R₂ (Function.update R₂ 1 ((R₂ 1)⁻¹)) := AC.Step.inv R₂ 1
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.single h2)) (Relation.ReflTransGen.single h3)

theorem reach_four (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 4)) := by
  have h : toRelators (applyMove s 4)
      = Function.update (toRelators s) 1 ((toRelators s) 1 * (toRelators s) 0) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce_append]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.mulRight _ 1 0 (by decide))

theorem reach_five (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 5)) := by
  let R := toRelators s
  let R₁ := Function.update R 0 ((R 0)⁻¹)
  let R₂ := Function.update R₁ 1 ((R₁ 1) * (R₁ 0))
  have h : toRelators (applyMove s 5) = Function.update R₂ 0 ((R₂ 0)⁻¹) := by
    show toRelators (applyMove s 5) = _
    simp only [R₂, R₁, R]
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce_append, wordProd_invWord]
  rw [h]
  have h1 : AC.Step R R₁ := AC.Step.inv R 0
  have h2 : AC.Step R₁ R₂ := AC.Step.mulRight R₁ 1 0 (by decide)
  have h3 : AC.Step R₂ (Function.update R₂ 0 ((R₂ 0)⁻¹)) := AC.Step.inv R₂ 0
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.single h2)) (Relation.ReflTransGen.single h3)

theorem reach_six (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 6)) := by
  have h : toRelators (applyMove s 6)
      = Function.update (toRelators s) 0 ((FreeGroup.of (0 : Fin 2)) * (toRelators s) 0
        * (FreeGroup.of (0 : Fin 2))⁻¹) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce, letter_conj_left, xp, xm]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.conj _ 0 (FreeGroup.of (0 : Fin 2)))

theorem reach_seven (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 7)) := by
  have h : toRelators (applyMove s 7)
      = Function.update (toRelators s) 0 ((FreeGroup.of (0 : Fin 2))⁻¹ * (toRelators s) 0
        * ((FreeGroup.of (0 : Fin 2))⁻¹)⁻¹) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce, letter_conj_inv_left, xp, xm]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.conj _ 0 ((FreeGroup.of (0 : Fin 2))⁻¹))

theorem reach_eight (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 8)) := by
  have h : toRelators (applyMove s 8)
      = Function.update (toRelators s) 0 ((FreeGroup.of (1 : Fin 2)) * (toRelators s) 0
        * (FreeGroup.of (1 : Fin 2))⁻¹) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce, letter_conj_left, yp, ym]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.conj _ 0 (FreeGroup.of (1 : Fin 2)))

theorem reach_nine (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 9)) := by
  have h : toRelators (applyMove s 9)
      = Function.update (toRelators s) 0 ((FreeGroup.of (1 : Fin 2))⁻¹ * (toRelators s) 0
        * ((FreeGroup.of (1 : Fin 2))⁻¹)⁻¹) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce, letter_conj_inv_left, yp, ym]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.conj _ 0 ((FreeGroup.of (1 : Fin 2))⁻¹))

theorem reach_ten (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 10)) := by
  have h : toRelators (applyMove s 10)
      = Function.update (toRelators s) 1 ((FreeGroup.of (0 : Fin 2)) * (toRelators s) 1
        * (FreeGroup.of (0 : Fin 2))⁻¹) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce, letter_conj_left, xp, xm]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.conj _ 1 (FreeGroup.of (0 : Fin 2)))

theorem reach_eleven (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 11)) := by
  have h : toRelators (applyMove s 11)
      = Function.update (toRelators s) 1 ((FreeGroup.of (0 : Fin 2))⁻¹ * (toRelators s) 1
        * ((FreeGroup.of (0 : Fin 2))⁻¹)⁻¹) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce, letter_conj_inv_left, xp, xm]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.conj _ 1 ((FreeGroup.of (0 : Fin 2))⁻¹))

theorem reach_twelve (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 12)) := by
  have h : toRelators (applyMove s 12)
      = Function.update (toRelators s) 1 ((FreeGroup.of (1 : Fin 2)) * (toRelators s) 1
        * (FreeGroup.of (1 : Fin 2))⁻¹) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce, letter_conj_left, yp, ym]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.conj _ 1 (FreeGroup.of (1 : Fin 2)))

theorem reach_thirteen (s : VState) : AC.Reachable (toRelators s) (toRelators (applyMove s 13)) := by
  have h : toRelators (applyMove s 13)
      = Function.update (toRelators s) 1 ((FreeGroup.of (1 : Fin 2))⁻¹ * (toRelators s) 1
        * ((FreeGroup.of (1 : Fin 2))⁻¹)⁻¹) := by
    apply relators_ext <;> simp [applyMove, wordProd_freeReduce, letter_conj_inv_left, yp, ym]
  rw [h]
  exact Relation.ReflTransGen.single (AC.Step.conj _ 1 ((FreeGroup.of (1 : Fin 2))⁻¹))

/-- **The move table bridge.** Every move id of `ac-r2-v1`, applied to a
verifier state with its internal free reduction, is reachable in the group
level model by at most three `AC.Step`s. -/
theorem applyMove_reachable (s : VState) (m : Fin 14) :
    AC.Reachable (toRelators s) (toRelators (applyMove s m.val)) := by
  fin_cases m
  · simpa using reach_zero s
  · simpa using reach_one s
  · simpa using reach_two s
  · simpa using reach_three s
  · simpa using reach_four s
  · simpa using reach_five s
  · simpa using reach_six s
  · simpa using reach_seven s
  · simpa using reach_eight s
  · simpa using reach_nine s
  · simpa using reach_ten s
  · simpa using reach_eleven s
  · simpa using reach_twelve s
  · simpa using reach_thirteen s

theorem target_toRelators : toRelators target = AC.standard 2 := by
  apply relators_ext <;> simp [target, toRelators, xp, yp, AC.standard, letter]

/-- **The path bridge.** A verifier move sequence that takes a presentation to
the ordered pair `(x, y)` gives an `AC.Reachable` statement from the group
element of that presentation to the standard relator tuple of `AC.lean`. -/
theorem path_reachable (s : VState) (ms : List (Fin 14))
    (h : ms.foldl (fun s m => applyMove s m.val) s = target) :
    AC.Reachable (toRelators s) (AC.standard 2) := by
  induction ms generalizing s with
  | nil =>
    simp only [List.foldl_nil] at h
    subst h
    rw [target_toRelators]
    exact Relation.ReflTransGen.refl
  | cons m ms ih =>
    rw [List.foldl_cons] at h
    exact Relation.ReflTransGen.trans (applyMove_reachable s m) (ih _ h)

/-! ### 7. A worked example: a real training path, end to end -/

/-- The initial presentation of training id `ms-train-0160`, namely the
relators `x^-1 y x y^-1 y^-1` and `x y x y y x^-1 y^-1`. -/
def train0160 : VState :=
  ([(0, false), (1, true), (0, true), (1, false), (1, false)],
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, false), (1, false)])

/-- The published seven move training solution for `ms-train-0160`. -/
def train0160Path : List (Fin 14) := [6, 4, 2, 9, 1, 4, 1]

/-- Replaying the published path with the verifier's own move function,
including its free reductions, reaches the target pair `(x, y)`. -/
theorem train0160_reaches :
    train0160Path.foldl (fun s m => applyMove s m.val) train0160 = target := by
  decide

/-- The bridge applied to a real verified path: the group element of that
training presentation is `AC.Reachable` to the standard relator tuple. -/
theorem train0160_reachable : AC.Reachable (toRelators train0160) (AC.standard 2) :=
  path_reachable _ _ train0160_reaches

end RankTwo

/-! ### 8. The same fold at the stable verifier's rank bound -/

/-- The stable verifier uses the same `free_reduce` with up to eight
generators, and the fold is proved here for every generator type, so it is
the same function there too. -/
theorem freeReduce_rank_eight (w : List (Fin 8 × Bool)) :
    freeReduce w = FreeGroup.reduce w :=
  freeReduce_eq_reduce w

end VFree
