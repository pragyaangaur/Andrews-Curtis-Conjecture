/-
Negative tests for the Andrews-Curtis certificate checker of `toolkit/lean/AC3.lean`
(`AndrewsCurtis.checkCert`, `AndrewsCurtis.Move`, `AndrewsCurtis.replay`).

Why: the checker is only ever run on certificates that are supposed to pass, so a
checker that returned `true` on everything would look exactly like a correct one.
Each theorem below feeds it a certificate that is wrong in exactly one way and
proves, in the kernel, that it is rejected; the positive controls next to them keep
the rejection statements from being vacuous.

No `sorry`, no new axiom, no `native_decide`: every `by decide` is a kernel
computation on the definitions of `AC3.lean`, and the general lemmas are ordinary
proofs.

Data provenance: `S`, `T`, `cert` are the contents of
`directions/ms-ak-certs/cert_n2.json` (the AK(2) certificate) read by
`ntest/ac2.py`, a reader written for this audit and not the campaign's
`cert_to_lean.py`; `ntest/ac2.py` replays the same move list independently in
Python (free reduction in `ntest/frog.py`) and prints the same start and finish
tuples.
-/
import AC3
open AndrewsCurtis

namespace ANeg

set_option maxRecDepth 100000

/-- start tuple of `cert_n2.json` (AK(2)), converted by `ntest/ac2.py`, an independent reader. -/
def S : Presentation 2 := mkPres (n := 2) [[(0, true), (0, true), (1, false), (1, false), (1, false)], [(0, true), (1, true), (0, true), (1, false), (0, false), (1, false)]]
/-- finish tuple of `cert_n2.json` (MS(2,w1)). -/
def T : Presentation 2 := mkPres (n := 2) [[(0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false)], [(0, false), (1, false), (0, false), (1, true), (0, true), (1, true)]]
/-- The 11 recorded moves of `cert_n2.json`. -/
def cert : List (Move 2) :=
  [ Move.conj 0 (mkWord (n := 2) [(1, true)]),
    Move.invert 1,
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true)]),
    Move.conj 1 (mkWord (n := 2) [(1, false), (0, false), (1, false)]) ]

/-- Positive control: the shipped certificate, read by my own converter, passes. -/
theorem pos : checkCert cert S T = true := by decide

/-- Its content: the two presentations are Andrews-Curtis equivalent. -/
theorem pos_sound : ACEquiv S T := checkCert_sound pos

/-- Tampering `drop_last`: ends elsewhere. -/
theorem bad_drop_last : checkCert [ Move.conj 0 (mkWord (n := 2) [(1, true)]),
    Move.invert 1,
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true)]) ] S T = false := by decide

/-- Tampering `drop_first`: ends elsewhere. -/
theorem bad_drop_first : checkCert [ Move.invert 1,
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true)]),
    Move.conj 1 (mkWord (n := 2) [(1, false), (0, false), (1, false)]) ] S T = false := by decide

/-- Tampering `diag`: no-replay. -/
theorem bad_diag : checkCert [ Move.conj 0 (mkWord (n := 2) [(1, true)]),
    Move.invert 1,
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.mul 0 0,
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true)]),
    Move.conj 1 (mkWord (n := 2) [(1, false), (0, false), (1, false)]) ] S T = false := by decide

/-- Tampering `mul_swap`: ends elsewhere. -/
theorem bad_mul_swap : checkCert [ Move.conj 0 (mkWord (n := 2) [(1, true)]),
    Move.invert 1,
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]),
    Move.mul 1 0,
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true)]),
    Move.conj 1 (mkWord (n := 2) [(1, false), (0, false), (1, false)]) ] S T = false := by decide

/-- Tampering `conj_sign`: ends elsewhere. -/
theorem bad_conj_sign : checkCert [ Move.conj 0 (mkWord (n := 2) [(1, false)]),
    Move.invert 1,
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true)]),
    Move.conj 1 (mkWord (n := 2) [(1, false), (0, false), (1, false)]) ] S T = false := by decide

/-- Tampering `rev`: ends elsewhere. -/
theorem bad_rev : checkCert [ Move.conj 1 (mkWord (n := 2) [(1, false), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, true)]),
    Move.mul 0 1,
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.invert 1,
    Move.conj 0 (mkWord (n := 2) [(1, true)]) ] S T = false := by decide

/-- Tampering `wrong_start`: the same moves from the finish tuple do not return to it. -/
theorem bad_wrong_start : checkCert cert T T = false := by decide

/-- Tampering `finish`: one letter of the finish tuple is inverted; the replay still ends at `T`, so only the endpoint comparison can reject this, and it must. -/
def T_bad : Presentation 2 := mkPres (n := 2) [[(0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false)], [(0, false), (1, false), (0, false), (1, true), (0, true), (1, false)]]
theorem bad_finish : checkCert cert S T_bad = false := by decide

/-- The state after the first four moves, used to check that `checkCert` composes. -/
def M : Presentation 2 := mkPres (n := 2) [[(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, false), (1, false), (0, true), (0, true), (1, false), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false)], [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]
theorem block1 : checkCert [ Move.conj 0 (mkWord (n := 2) [(1, true)]),
    Move.invert 1,
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]) ] S M = true := by decide
theorem block2 : checkCert [ Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true)]),
    Move.conj 1 (mkWord (n := 2) [(1, false), (0, false), (1, false)]) ] M T = true := by decide
/-- Composition is not vacuous: the two blocks chained give the whole certificate. -/
theorem composed : checkCert ([ Move.conj 0 (mkWord (n := 2) [(1, true)]),
    Move.invert 1,
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]) ] ++ [ Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true)]),
    Move.conj 1 (mkWord (n := 2) [(1, false), (0, false), (1, false)]) ]) S T = true :=
  checkCert_append (ms₁ := [ Move.conj 0 (mkWord (n := 2) [(1, true)]),
    Move.invert 1,
    Move.conj 1 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false)]),
    Move.conj 0 (mkWord (n := 2) [(1, true), (0, true), (1, false), (0, false), (1, true), (0, true), (1, true), (0, false), (0, false), (1, false)]) ]) (ms₂ := [ Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true), (1, true), (0, false), (1, false)]),
    Move.conj 1 (mkWord (n := 2) [(0, false)]),
    Move.conj 0 (mkWord (n := 2) [(0, false), (1, true), (0, true), (1, true), (0, false), (1, false)]),
    Move.mul 0 1,
    Move.conj 1 (mkWord (n := 2) [(0, true)]),
    Move.conj 1 (mkWord (n := 2) [(1, false), (0, false), (1, false)]) ]) block1 block2

/-! ## General facts about the checker

The tamperings above are single instances.  The two lemmas below are the general
statement behind the `diag` tampering: a certificate that contains the illegal
diagonal multiplication `mul i i` anywhere is rejected, for every rank, every start,
every finish and every position of the illegal move.  Together with `Move.apply`
returning `none` there, this is the exact reason `AC3.lean` can document that "a
certificate that does [use `mul i i`] is rejected". -/

theorem mul_self_apply {n : Nat} (P : Presentation n) (i : Fin n) :
    (Move.mul i i).apply P = none := by
  rw [Move.apply]
  simp

theorem replay_diag_none {n : Nat} :
    ∀ (ms₁ ms₂ : List (Move n)) (P : Presentation n) (i : Fin n),
      replay (ms₁ ++ Move.mul i i :: ms₂) P = none
  | [], ms₂, P, i => by
      rw [List.nil_append, replay]
      simp [Move.apply]
  | m :: ms₁, ms₂, P, i => by
      rw [List.cons_append, replay]
      cases h : m.apply P with
      | none => rfl
      | some P' => exact replay_diag_none ms₁ ms₂ P' i

theorem checkCert_diag_false {n : Nat} (ms₁ ms₂ : List (Move n))
    (start finish : Presentation n) (i : Fin n) :
    checkCert (ms₁ ++ Move.mul i i :: ms₂) start finish = false := by
  rw [checkCert, replay_diag_none]
  simp

/-! ## Axiom audit -/
#print axioms pos
#print axioms pos_sound
#print axioms block1
#print axioms block2
#print axioms composed
#print axioms bad_drop_last
#print axioms bad_drop_first
#print axioms bad_diag
#print axioms bad_mul_swap
#print axioms bad_conj_sign
#print axioms bad_rev
#print axioms bad_wrong_start
#print axioms bad_finish
#print axioms mul_self_apply
#print axioms replay_diag_none
#print axioms checkCert_diag_false

/-- The checker's content, instantiated: `checkCert_sound` on the independently
converted certificate makes the two presentations present the same group. -/
theorem pos_same_group :
    Subsingleton (PresentedGroup (Set.range S)) ↔ Subsingleton (PresentedGroup (Set.range T)) :=
  presentedGroup_subsingleton_iff pos_sound

#print axioms pos_same_group

end ANeg
