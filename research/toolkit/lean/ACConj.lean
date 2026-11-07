/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import AC

/-!
# ACConj: the conjugator layer of the closed-set method

The campaign's closed-set certificates (`ACBounds`, `ACClosed`, `ACKeys`, `ACTree`,
`ACComponents`) live in a *twelve-move* model of rank two: invert a relator, multiply
one relator by the other on the right, and conjugate a relator by one of the four
*letters*.  The Andrews-Curtis move set of `AC.lean` allows conjugation by an
arbitrary word of the free group, so a negative result in the twelve-move model is
prima facie weaker than a negative result for the AC move set.  The campaign's
round-4 report (directions/resisters/round4/README.md, section 5) argues that this
does not matter: inside a box, the reachable set is the same for every conjugator
bound.  That argument was refereed by hand and never machine-checked.

This file supplies the kernel side of that bridge.  Its contents, in order:

* the model: freely reduced words over `Fin 2 × Bool`, states, the twelve tokens and
  the extended move set `XTok` (the twelve tokens plus conjugation by any word);
* **faithfulness** (`applyX_ac`, `runX_ac`): every extended move, and every path, is
  an Andrews-Curtis move, resp. an `ACEquiv`, on the rank-two relator tuple;
* **length tools**: `length_red_append_ge` (appending `B` shortens the reduction by
  at most `|B|`), `conjW_length_le` (a conjugate is at most `|u| + 2|w|` long) and the
  **one-pair lemma** `conjL_length_ge`;
* **the simulation** (`sim`, `run_sim`, `sim_take`): conjugation by an arbitrary word
  is a twelve-move path, all of whose intermediate states are conjugates by suffixes,
  hence bounded by `|u| + 2|w| + |q|`;
* **the corollary for closed sets** (`full_conj_mem_of_closed`): a set closed under the
  twelve moves inside a box is closed under *every* conjugation whose crude bound fits
  in the box.

Nothing in this file says anything about the truth of the Andrews-Curtis conjecture:
every statement is about move sequences and their lengths inside a fixed box.
-/

set_option maxRecDepth 1000000

namespace ACConj

open AndrewsCurtis

/-! ## The model -/

/-- A letter: a generator `Fin 2` together with a sign (`true` = `+`). -/
abbrev Letter : Type := Fin 2 × Bool

/-- A word: a list of letters, kept freely reduced by `red`. -/
abbrev Word : Type := List Letter

/-- A rank-two presentation: a pair of relators. -/
abbrev St : Type := Word × Word

/-- Free reduction, as in `FreeGroup`. -/
abbrev red (w : Word) : Word := FreeGroup.reduce w

/-- The inverse word. -/
abbrev invW (w : Word) : Word := FreeGroup.invRev w

/-- Concatenation followed by free reduction. -/
abbrev mulW (u v : Word) : Word := red (u ++ v)

/-- The inverse letter. -/
abbrev invL (x : Letter) : Letter := (x.1, !x.2)

/-- Conjugation of a word by a single letter. -/
abbrev conjL (c : Letter) (u : Word) : Word := red (c :: (u ++ [invL c]))

/-- Conjugation of a word by an arbitrary word. -/
abbrev conjW (w u : Word) : Word := red (w ++ (u ++ invW w))

/-- Total relator length. -/
abbrev totLen (p : St) : Nat := p.1.length + p.2.length

/-! ## The letters of the twelve-move system -/

/-- The letter `a`. -/
def La : Letter := (0, true)
/-- The letter `a⁻¹`. -/
def LA : Letter := (0, false)
/-- The letter `b`. -/
def Lb : Letter := (1, true)
/-- The letter `b⁻¹`. -/
def LB : Letter := (1, false)

/-- The twelve move names of `ACBounds`. -/
inductive Tok : Type where
  | i0 | i1 | m0 | m1
  | c0a | c0A | c0b | c0B | c1a | c1A | c1b | c1B
  deriving DecidableEq, Repr

/-- One move of the twelve-move system. -/
def apply : Tok → St → St
  | Tok.i0, p => (invW p.1, p.2)
  | Tok.i1, p => (p.1, invW p.2)
  | Tok.m0, p => (mulW p.1 p.2, p.2)
  | Tok.m1, p => (p.1, mulW p.2 p.1)
  | Tok.c0a, p => (conjL La p.1, p.2)
  | Tok.c0A, p => (conjL LA p.1, p.2)
  | Tok.c0b, p => (conjL Lb p.1, p.2)
  | Tok.c0B, p => (conjL LB p.1, p.2)
  | Tok.c1a, p => (p.1, conjL La p.2)
  | Tok.c1A, p => (p.1, conjL LA p.2)
  | Tok.c1b, p => (p.1, conjL Lb p.2)
  | Tok.c1B, p => (p.1, conjL LB p.2)

/-- Run a list of twelve-move tokens. -/
def run (p : St) (ts : List Tok) : St := ts.foldl (fun s t => apply t s) p

/-- The extended move set: the twelve tokens, plus conjugation of either relator by an
arbitrary word.  This is the move set of the campaign's A/C engines, which allow
conjugators of bounded length. -/
inductive XTok : Type where
  | tok (t : Tok)
  | g0 (w : Word)
  | g1 (w : Word)

/-- One extended move. -/
def applyX : XTok → St → St
  | XTok.tok t, p => apply t p
  | XTok.g0 w, p => (conjW w p.1, p.2)
  | XTok.g1 w, p => (p.1, conjW w p.2)

/-- Run a list of extended moves. -/
def runX (p : St) (ts : List XTok) : St := ts.foldl (fun s t => applyX t s) p

@[simp] theorem run_nil (p : St) : run p [] = p := rfl

@[simp] theorem run_cons (p : St) (t : Tok) (ts : List Tok) :
    run p (t :: ts) = run (apply t p) ts := rfl

@[simp] theorem runX_nil (p : St) : runX p [] = p := rfl

@[simp] theorem runX_cons (p : St) (t : XTok) (ts : List XTok) :
    runX p (t :: ts) = runX (applyX t p) ts := rfl

/-! ## Free-group lemmas -/

/-- The free-group element of a word. -/
abbrev w2 (w : Word) : FreeGroup (Fin 2) := FreeGroup.mk w

theorem w2_red (w : Word) : w2 (red w) = w2 w := FreeGroup.reduce.self

theorem w2_invW (w : Word) : w2 (invW w) = (w2 w)⁻¹ := by
  show FreeGroup.mk (FreeGroup.invRev w) = (FreeGroup.mk w)⁻¹
  rw [FreeGroup.inv_mk]

theorem w2_mulW (u v : Word) : w2 (mulW u v) = w2 u * w2 v := by
  show FreeGroup.mk (FreeGroup.reduce (u ++ v)) = FreeGroup.mk u * FreeGroup.mk v
  rw [FreeGroup.reduce.self, FreeGroup.mul_mk]

/-- Conjugation of an arbitrary list by a letter, at the level of the free group. -/
theorem mk_conjL_list (c : Letter) (X : Word) :
    FreeGroup.mk (c :: (X ++ [invL c])) =
      FreeGroup.mk [c] * FreeGroup.mk X * (FreeGroup.mk [c])⁻¹ := by
  have hl : (c :: (X ++ [invL c]) : Word) = [c] ++ X ++ FreeGroup.invRev [c] := by
    simp [invL, FreeGroup.invRev]
  rw [hl, FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk]

/-- Conjugation by an arbitrary word, at the level of the free group. -/
theorem mk_conjW_list (w u : Word) :
    FreeGroup.mk (w ++ (u ++ FreeGroup.invRev w)) =
      FreeGroup.mk w * FreeGroup.mk u * (FreeGroup.mk w)⁻¹ := by
  rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk, List.append_assoc]

theorem w2_conjL (c : Letter) (u : Word) :
    w2 (conjL c u) = w2 [c] * w2 u * (w2 [c])⁻¹ := by
  show FreeGroup.mk (FreeGroup.reduce (c :: (u ++ [invL c]))) =
    FreeGroup.mk [c] * FreeGroup.mk u * (FreeGroup.mk [c])⁻¹
  rw [FreeGroup.reduce.self]
  exact mk_conjL_list c u

theorem w2_conjW (w u : Word) : w2 (conjW w u) = w2 w * w2 u * (w2 w)⁻¹ := by
  show FreeGroup.mk (FreeGroup.reduce (w ++ (u ++ FreeGroup.invRev w))) =
    FreeGroup.mk w * FreeGroup.mk u * (FreeGroup.mk w)⁻¹
  rw [FreeGroup.reduce.self]
  exact mk_conjW_list w u

/-- The rank-two relator tuple of a state. -/
def toPres (p : St) : Presentation 2 := Fin.cases (w2 p.1) (fun _ => w2 p.2)

theorem toPres_zero (p : St) : toPres p 0 = w2 p.1 := rfl

theorem toPres_one (p : St) : toPres p 1 = w2 p.2 := rfl

/-- Two rank-two relator tuples agreeing at the two literals are equal. -/
theorem pres_eq_of_components {P Q : Presentation 2} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) :
    P = Q := by
  funext k
  fin_cases k
  · exact h0
  · exact h1

/-! ## Component lemmas for the AC moves -/

theorem invertAt_zero_zero (P : Presentation 2) : invertAt P 0 0 = (P 0)⁻¹ := by
  simp [invertAt, setAt]

theorem invertAt_zero_one (P : Presentation 2) : invertAt P 0 1 = P 1 := by
  simp [invertAt, setAt]

theorem invertAt_one_one (P : Presentation 2) : invertAt P 1 1 = (P 1)⁻¹ := by
  simp [invertAt, setAt]

theorem invertAt_one_zero (P : Presentation 2) : invertAt P 1 0 = P 0 := by
  simp [invertAt, setAt]

theorem mulAt_zero_zero (P : Presentation 2) : mulAt P 0 1 0 = P 0 * P 1 := by
  simp [mulAt, setAt]

theorem mulAt_zero_one (P : Presentation 2) : mulAt P 0 1 1 = P 1 := by
  simp [mulAt, setAt]

theorem mulAt_one_one (P : Presentation 2) : mulAt P 1 0 1 = P 1 * P 0 := by
  simp [mulAt, setAt]

theorem mulAt_one_zero (P : Presentation 2) : mulAt P 1 0 0 = P 0 := by
  simp [mulAt, setAt]

theorem conjAt_zero_zero (P : Presentation 2) (w : FreeGroup (Fin 2)) : conjAt P 0 w 0 = w * P 0 * w⁻¹ := by
  simp [conjAt, setAt]

theorem conjAt_zero_one (P : Presentation 2) (w : FreeGroup (Fin 2)) : conjAt P 0 w 1 = P 1 := by
  simp [conjAt, setAt]

theorem conjAt_one_one (P : Presentation 2) (w : FreeGroup (Fin 2)) : conjAt P 1 w 1 = w * P 1 * w⁻¹ := by
  simp [conjAt, setAt]

theorem conjAt_one_zero (P : Presentation 2) (w : FreeGroup (Fin 2)) : conjAt P 1 w 0 = P 0 := by
  simp [conjAt, setAt]

/-! ## Faithfulness: every extended move is an `ACMove` -/

/-- **Faithfulness.**  Every move of the extended system is an Andrews-Curtis move on
the rank-two relator tuple.  In particular conjugation by an arbitrary word is
`ACMove.conj`. -/
theorem applyX_ac (t : XTok) (p : St) : ACEquiv (toPres p) (toPres (applyX t p)) := by
  obtain ⟨a, b⟩ := p
  cases t with
  | tok t =>
      cases t with
      | i0 =>
          refine ACEquiv.of_move ?_
          have h : toPres (invW a, b) = invertAt (toPres (a, b)) 0 := by
            exact pres_eq_of_components (by rw [toPres_zero, invertAt_zero_zero, toPres_zero, w2_invW]) (by rw [toPres_one, invertAt_zero_one, toPres_one])
          show ACMove (toPres (a, b)) (toPres (invW a, b))
          rw [h]
          exact ACMove.invert (0 : Fin 2) (toPres (a, b))
      | i1 =>
          refine ACEquiv.of_move ?_
          have h : toPres (a, invW b) = invertAt (toPres (a, b)) 1 := by
            exact pres_eq_of_components (by rw [toPres_zero, invertAt_one_zero, toPres_zero]) (by rw [toPres_one, invertAt_one_one, toPres_one, w2_invW])
          show ACMove (toPres (a, b)) (toPres (a, invW b))
          rw [h]
          exact ACMove.invert (1 : Fin 2) (toPres (a, b))
      | m0 =>
          refine ACEquiv.of_move ?_
          have h : toPres (mulW a b, b) = mulAt (toPres (a, b)) 0 1 := by
            exact pres_eq_of_components (by rw [toPres_zero, mulAt_zero_zero, toPres_zero, toPres_one, w2_mulW]) (by rw [toPres_one, mulAt_zero_one, toPres_one])
          show ACMove (toPres (a, b)) (toPres (mulW a b, b))
          rw [h]
          exact ACMove.mul (0 : Fin 2) 1 (by decide) (toPres (a, b))
      | m1 =>
          refine ACEquiv.of_move ?_
          have h : toPres (a, mulW b a) = mulAt (toPres (a, b)) 1 0 := by
            exact pres_eq_of_components (by rw [toPres_zero, mulAt_one_zero, toPres_zero]) (by rw [toPres_one, mulAt_one_one, toPres_one, toPres_zero, w2_mulW])
          show ACMove (toPres (a, b)) (toPres (a, mulW b a))
          rw [h]
          exact ACMove.mul (1 : Fin 2) 0 (by decide) (toPres (a, b))
      | c0a =>
          refine ACEquiv.of_move ?_
          have h : toPres (conjL La a, b) = conjAt (toPres (a, b)) 0 (w2 [La]) := by
            exact pres_eq_of_components (by rw [toPres_zero, conjAt_zero_zero, toPres_zero, w2_conjL]) (by rw [toPres_one, conjAt_zero_one, toPres_one])
          show ACMove (toPres (a, b)) (toPres (conjL La a, b))
          rw [h]
          exact ACMove.conj (0 : Fin 2) (w2 [La]) (toPres (a, b))
      | c0A =>
          refine ACEquiv.of_move ?_
          have h : toPres (conjL LA a, b) = conjAt (toPres (a, b)) 0 (w2 [LA]) := by
            exact pres_eq_of_components (by rw [toPres_zero, conjAt_zero_zero, toPres_zero, w2_conjL]) (by rw [toPres_one, conjAt_zero_one, toPres_one])
          show ACMove (toPres (a, b)) (toPres (conjL LA a, b))
          rw [h]
          exact ACMove.conj (0 : Fin 2) (w2 [LA]) (toPres (a, b))
      | c0b =>
          refine ACEquiv.of_move ?_
          have h : toPres (conjL Lb a, b) = conjAt (toPres (a, b)) 0 (w2 [Lb]) := by
            exact pres_eq_of_components (by rw [toPres_zero, conjAt_zero_zero, toPres_zero, w2_conjL]) (by rw [toPres_one, conjAt_zero_one, toPres_one])
          show ACMove (toPres (a, b)) (toPres (conjL Lb a, b))
          rw [h]
          exact ACMove.conj (0 : Fin 2) (w2 [Lb]) (toPres (a, b))
      | c0B =>
          refine ACEquiv.of_move ?_
          have h : toPres (conjL LB a, b) = conjAt (toPres (a, b)) 0 (w2 [LB]) := by
            exact pres_eq_of_components (by rw [toPres_zero, conjAt_zero_zero, toPres_zero, w2_conjL]) (by rw [toPres_one, conjAt_zero_one, toPres_one])
          show ACMove (toPres (a, b)) (toPres (conjL LB a, b))
          rw [h]
          exact ACMove.conj (0 : Fin 2) (w2 [LB]) (toPres (a, b))
      | c1a =>
          refine ACEquiv.of_move ?_
          have h : toPres (a, conjL La b) = conjAt (toPres (a, b)) 1 (w2 [La]) := by
            exact pres_eq_of_components (by rw [toPres_zero, conjAt_one_zero, toPres_zero]) (by rw [toPres_one, conjAt_one_one, toPres_one, w2_conjL])
          show ACMove (toPres (a, b)) (toPres (a, conjL La b))
          rw [h]
          exact ACMove.conj (1 : Fin 2) (w2 [La]) (toPres (a, b))
      | c1A =>
          refine ACEquiv.of_move ?_
          have h : toPres (a, conjL LA b) = conjAt (toPres (a, b)) 1 (w2 [LA]) := by
            exact pres_eq_of_components (by rw [toPres_zero, conjAt_one_zero, toPres_zero]) (by rw [toPres_one, conjAt_one_one, toPres_one, w2_conjL])
          show ACMove (toPres (a, b)) (toPres (a, conjL LA b))
          rw [h]
          exact ACMove.conj (1 : Fin 2) (w2 [LA]) (toPres (a, b))
      | c1b =>
          refine ACEquiv.of_move ?_
          have h : toPres (a, conjL Lb b) = conjAt (toPres (a, b)) 1 (w2 [Lb]) := by
            exact pres_eq_of_components (by rw [toPres_zero, conjAt_one_zero, toPres_zero]) (by rw [toPres_one, conjAt_one_one, toPres_one, w2_conjL])
          show ACMove (toPres (a, b)) (toPres (a, conjL Lb b))
          rw [h]
          exact ACMove.conj (1 : Fin 2) (w2 [Lb]) (toPres (a, b))
      | c1B =>
          refine ACEquiv.of_move ?_
          have h : toPres (a, conjL LB b) = conjAt (toPres (a, b)) 1 (w2 [LB]) := by
            exact pres_eq_of_components (by rw [toPres_zero, conjAt_one_zero, toPres_zero]) (by rw [toPres_one, conjAt_one_one, toPres_one, w2_conjL])
          show ACMove (toPres (a, b)) (toPres (a, conjL LB b))
          rw [h]
          exact ACMove.conj (1 : Fin 2) (w2 [LB]) (toPres (a, b))
  | g0 w =>
      refine ACEquiv.of_move ?_
      have h : toPres (conjW w a, b) = conjAt (toPres (a, b)) 0 (w2 w) := by
        exact pres_eq_of_components (by rw [toPres_zero, conjAt_zero_zero, toPres_zero, w2_conjW]) (by rw [toPres_one, conjAt_zero_one, toPres_one])
      show ACMove (toPres (a, b)) (toPres (conjW w a, b))
      rw [h]
      exact ACMove.conj (0 : Fin 2) (w2 w) (toPres (a, b))
  | g1 w =>
      refine ACEquiv.of_move ?_
      have h : toPres (a, conjW w b) = conjAt (toPres (a, b)) 1 (w2 w) := by
        exact pres_eq_of_components (by rw [toPres_zero, conjAt_one_zero, toPres_zero]) (by rw [toPres_one, conjAt_one_one, toPres_one, w2_conjW])
      show ACMove (toPres (a, b)) (toPres (a, conjW w b))
      rw [h]
      exact ACMove.conj (1 : Fin 2) (w2 w) (toPres (a, b))

/-- **Every path in the model is an AC-equivalence.** -/
theorem runX_ac (p : St) (ts : List XTok) : ACEquiv (toPres p) (toPres (runX p ts)) := by
  induction ts generalizing p with
  | nil => exact ACEquiv.refl _
  | cons t ts ih => exact ACEquiv.trans (applyX_ac t p) (ih (applyX t p))

/-! ## Length tools -/

/-- Reduction never lengthens a word. -/
theorem length_red_le (L : Word) : (red L).length ≤ L.length := by
  have h : (FreeGroup.mk L).norm ≤ L.length := FreeGroup.norm_mk_le
  simpa [red, FreeGroup.norm, FreeGroup.toWord_mk] using h

/-- `mk A = mk (A ++ B) * (mk B)⁻¹`. -/
theorem mk_mul_inv (A B : Word) :
    FreeGroup.mk A = FreeGroup.mk (A ++ B) * (FreeGroup.mk B)⁻¹ := by
  have h : FreeGroup.mk A = FreeGroup.mk A * FreeGroup.mk B * (FreeGroup.mk B)⁻¹ := by
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [h, ← FreeGroup.mul_mk, FreeGroup.inv_mk]

/-- **Appending shortens by at most the appended length.** -/
theorem length_red_append_ge (A B : Word) :
    (red A).length ≤ (red (A ++ B)).length + B.length := by
  have hsplit : FreeGroup.mk A = FreeGroup.mk (A ++ B) * (FreeGroup.mk B)⁻¹ := mk_mul_inv A B
  have hA : (red A).length = (FreeGroup.mk A).norm := by
    simp [red, FreeGroup.norm, FreeGroup.toWord_mk]
  have hAB : (FreeGroup.mk (A ++ B)).norm = (red (A ++ B)).length := by
    simp [red, FreeGroup.norm, FreeGroup.toWord_mk]
  have hB : (FreeGroup.mk B).norm ≤ B.length := by
    simpa [FreeGroup.norm, FreeGroup.toWord_mk] using length_red_le B
  calc (red A).length
      = (FreeGroup.mk A).norm := hA
    _ = (FreeGroup.mk (A ++ B) * (FreeGroup.mk B)⁻¹).norm := by rw [hsplit]
    _ ≤ (FreeGroup.mk (A ++ B)).norm + ((FreeGroup.mk B)⁻¹).norm := FreeGroup.norm_mul_le _ _
    _ = (FreeGroup.mk (A ++ B)).norm + (FreeGroup.mk B).norm := by rw [FreeGroup.norm_inv_eq]
    _ ≤ (red (A ++ B)).length + B.length := by
          rw [hAB]; omega

/-- Appending one letter shortens the reduction by at most one. -/
theorem length_red_snoc_ge (X : Word) (z : Letter) :
    (red X).length ≤ (red (X ++ [z])).length + 1 := by
  have h := length_red_append_ge X [z]
  simpa using h

/-- **The one-pair lemma.**  If `c Y` is already reduced, conjugation by `c` cannot
shorten `Y`: only the pair at the inner junction can cancel, and it costs one letter
against the two that `c` adds. -/
theorem conjL_length_ge {c : Letter} {Y : Word} (hY : red (c :: Y) = c :: Y) :
    Y.length ≤ (conjL c Y).length := by
  have h1 : conjL c Y = red ((c :: Y) ++ [invL c]) := by
    simp [conjL, List.cons_append]
  rw [h1]
  have h2 := length_red_snoc_ge (c :: Y) (invL c)
  rw [hY] at h2
  simp only [List.length_cons] at h2
  omega

/-- A conjugate is at most `|u| + 2|w|` long. -/
theorem conjW_length_le (w u : Word) : (conjW w u).length ≤ u.length + 2 * w.length := by
  have h : (conjW w u).length = (red (w ++ (u ++ FreeGroup.invRev w))).length := rfl
  rw [h]
  calc (red (w ++ (u ++ FreeGroup.invRev w))).length
      ≤ (w ++ (u ++ FreeGroup.invRev w)).length := length_red_le _
    _ = u.length + 2 * w.length := by
        rw [List.length_append, List.length_append, FreeGroup.invRev_length]
        omega

/-! ## Simulating a conjugation by twelve moves -/

/-- The token that conjugates relator `0` by the letter `c`.  Every letter of
`Fin 2 × Bool` is one of the four. -/
def tokC0 : Letter → Tok
  | (0, true) => Tok.c0a
  | (0, false) => Tok.c0A
  | (1, true) => Tok.c0b
  | (1, false) => Tok.c0B

theorem apply_tokC0 (c : Letter) (p : St) : apply (tokC0 c) p = (conjL c p.1, p.2) := by
  obtain ⟨g, s⟩ := c
  obtain ⟨a, b⟩ := p
  fin_cases g <;> cases s <;> rfl

/-- The one-letter step of the simulation. -/
theorem conjL_conjW (c : Letter) (w u : Word) : conjL c (conjW w u) = conjW (c :: w) u := by
  refine FreeGroup.reduce.sound ?_
  rw [mk_conjL_list]
  rw [show FreeGroup.mk (conjW w u) = FreeGroup.mk (w ++ (u ++ FreeGroup.invRev w)) from
    FreeGroup.reduce.self]
  rw [mk_conjW_list]
  rw [mk_conjW_list]
  rw [show FreeGroup.mk (c :: w) = FreeGroup.mk [c] * FreeGroup.mk w from
    (FreeGroup.mul_mk (L₁ := [c]) (L₂ := w)).symm]
  rw [mul_inv_rev]
  simp only [mul_assoc]

/-- The token list simulating conjugation by `w`. -/
def sim (u : Word) : Word → List Tok
  | [] => []
  | c :: w => sim u w ++ [tokC0 c]

theorem run_append (p : St) (ts₁ ts₂ : List Tok) :
    run p (ts₁ ++ ts₂) = run (run p ts₁) ts₂ := by
  simp [run, List.foldl_append]

/-- The simulation reaches the conjugate. -/
theorem run_sim (u q : Word) (hu : red u = u) :
    ∀ w : Word, run (u, q) (sim u w) = (conjW w u, q)
  | [] => by
      show (u, q) = (conjW [] u, q)
      simp [conjW, invW, FreeGroup.invRev, hu]
  | c :: w => by
      rw [sim, run_append, run_sim u q hu w]
      show apply (tokC0 c) (conjW w u, q) = (conjW (c :: w) u, q)
      rw [apply_tokC0, conjL_conjW]

/-- Every prefix of the token list is the token list of a suffix of the conjugator. -/
theorem sim_take (u : Word) (w : Word) (i : Nat) :
    ∃ (w' p : Word), w = p ++ w' ∧ (sim u w).take i = sim u w' := by
  induction w generalizing i with
  | nil => exact ⟨[], [], rfl, by simp [sim]⟩
  | cons c w ih =>
      by_cases hi : i ≤ (sim u w).length
      · obtain ⟨w', p, hw, ht⟩ := ih i
        exact ⟨w', c :: p, by simp [hw], by rw [sim, List.take_append_of_le_length hi, ht]⟩
      · refine ⟨c :: w, [], by simp, ?_⟩
        rw [sim, List.take_of_length_le (by simp; omega)]

/-- **The simulation stays in the crude box.** -/
theorem run_sim_totLen_le (u q : Word) (hu : red u = u) (w : Word) :
    ∀ i, i ≤ (sim u w).length →
      totLen (run (u, q) ((sim u w).take i)) ≤ u.length + 2 * w.length + q.length := by
  intro i hi
  obtain ⟨w', p, hw, ht⟩ := sim_take u w i
  rw [ht, run_sim u q hu w']
  have hlen : w'.length ≤ w.length := by rw [hw, List.length_append]; omega
  have h1 : (conjW w' u).length ≤ u.length + 2 * w'.length := conjW_length_le w' u
  simp only [totLen]
  omega

/-! ## The corollary for closed sets -/

/-- A set of states closed under the twelve moves inside the box of total relator
length at most `cap`.  This is the hypothesis of `ACBounds.not_reach_of_closed`. -/
def ClosedAt (cap : Nat) (S : List St) : Prop :=
  ∀ s ∈ S, ∀ t : Tok, totLen (apply t s) ≤ cap → apply t s ∈ S

/-- A token path whose intermediate states all lie in the box keeps the closed set. -/
theorem run_mem_of_closed {cap : Nat} {S : List St} (hS : ClosedAt cap S) :
    ∀ (ts : List Tok) (p : St), p ∈ S →
      (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) → run p ts ∈ S
  | [], p, hp, _ => by simpa using hp
  | t :: ts, p, hp, hbox => by
      have hstep : apply t p ∈ S := by
        refine hS p hp t ?_
        have h1 := hbox 1 (by simp)
        simpa using h1
      have hgoal : run (apply t p) ts ∈ S :=
        run_mem_of_closed hS ts (apply t p) hstep (fun i hi => by
          have h1 := hbox (i + 1) (by simp only [List.length_cons]; omega)
          simpa using h1)
      simpa using hgoal

/-- **Closed sets are closed under conjugations that fit with the crude bound.**  If a
set is closed under the twelve moves inside the box of cap `cap`, then the conjugate of
a member by any word `w` with `|u| + 2|w| + |q| ≤ cap` is again a member. -/
theorem full_conj_mem_of_closed {cap : Nat} {S : List St} (hS : ClosedAt cap S)
    {u q w : Word} (hu : red u = u) (hp : (u, q) ∈ S)
    (hbox : u.length + 2 * w.length + q.length ≤ cap) : (conjW w u, q) ∈ S := by
  have h := run_mem_of_closed hS (sim u w) (u, q) hp (fun i hi => by
    have h1 := run_sim_totLen_le u q hu w i hi
    omega)
  rwa [run_sim u q hu w] at h

/-! ## Axiom audit -/

#print axioms ACConj.applyX_ac
#print axioms ACConj.runX_ac
#print axioms ACConj.length_red_le
#print axioms ACConj.mk_mul_inv
#print axioms ACConj.length_red_append_ge
#print axioms ACConj.length_red_snoc_ge
#print axioms ACConj.conjL_length_ge
#print axioms ACConj.conjW_length_le
#print axioms ACConj.apply_tokC0
#print axioms ACConj.conjL_conjW
#print axioms ACConj.run_sim
#print axioms ACConj.sim_take
#print axioms ACConj.run_sim_totLen_le
#print axioms ACConj.run_mem_of_closed
#print axioms ACConj.full_conj_mem_of_closed

end ACConj
