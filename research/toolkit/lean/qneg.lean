/-
Negative tests for the `Q**`-certificate checker of `toolkit/lean/AC5.lean`
(`AC5.QMove`, `AC5.QMove.apply`, `AC5.replay`, `AC5.checkCert`).

Why: the checker is only ever run on certificates that are supposed to pass, so a
checker that accepted everything, or that silently skipped a guard, would look
exactly like a correct one.  Each theorem below either feeds the checker a
certificate that is wrong in exactly one way and proves in the kernel that it is
rejected, or probes one guard exhaustively.  Positive controls sit next to the
negative ones so no statement is vacuous, in particular
`correct_delete_fires` (the deletion guard does fire on the recorded data) next to
`only_one_delete_fires` (out of 66 candidate deletions at the same state, one fires).

Data: `S`, `T` and every intermediate state are `mccool_pietrowski_2_2_2.cert` of
`directions/qdouble-star/m9/certs/`, read by `ntest/frog.py`, a reader and replayer
written for this audit (it does not import the campaign's `qverify.py` or
`gen_ac5.py`).  The kernel sees the certificate only through those generated
literals, so the positive control `q_pos` is also a check that the conversion is
faithful.

No `sorry`, no new axiom, no `native_decide`.
-/
import AC5
open AC5

namespace QNeg

set_option maxRecDepth 100000

/-- `S`: start tuple of `directions/qdouble-star/m9/certs/mccool_pietrowski_2_2_2.cert`, read by `ntest/frog.py`. -/
def S : QPres := mkQPres 2 1 [[(0, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, true), (1, true), (1, true)]]
/-- `T`: finish tuple of the same certificate. -/
def T : QPres := mkQPres 2 1 [[(0, true), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
/-- state after move 1 of the certificate. -/
def I1 : QPres := mkQPres 3 2 [[(0, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, true), (1, true), (1, true)], [(2, true)]]
/-- state after move 2 of the certificate. -/
def I2 : QPres := mkQPres 3 2 [[(0, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, true), (1, true), (1, true)], [(2, true), (0, false)]]
/-- state after move 3 of the certificate. -/
def I3 : QPres := mkQPres 3 2 [[(0, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, true), (1, true), (1, true)], [(2, true), (0, false), (0, false)]]
/-- state after move 4 of the certificate. -/
def I4 : QPres := mkQPres 3 2 [[(0, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, true), (1, true), (1, true)], [(2, true), (1, false), (0, false), (0, false)]]
/-- state after move 5 of the certificate. -/
def I5 : QPres := mkQPres 3 2 [[(0, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, true), (1, true), (1, true)], [(2, true), (1, false), (1, false), (0, false), (0, false)]]
/-- state after move 6 of the certificate. -/
def I6 : QPres := mkQPres 3 2 [[(0, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (1, true), (2, true), (1, false), (1, false), (0, false), (0, false), (1, false), (1, false), (0, false), (0, false)]]
/-- state after move 7 of the certificate. -/
def I7 : QPres := mkQPres 3 2 [[(0, true), (0, true), (1, true), (1, true), (2, true), (1, true)], [(0, true), (0, true), (1, true), (1, true), (2, true), (1, false), (1, false), (0, false), (0, false), (1, false), (1, false), (0, false), (0, false)]]
/-- state after move 8 of the certificate. -/
def I8 : QPres := mkQPres 3 2 [[(0, true), (0, true), (1, true), (1, true), (2, true), (1, true)], [(2, true), (1, false), (1, false), (0, false), (0, false)]]
/-- state after move 9 of the certificate. -/
def I9 : QPres := mkQPres 3 2 [[(2, true), (2, true), (1, true)], [(2, true), (1, false), (1, false), (0, false), (0, false)]]
/-- state after move 10 of the certificate. -/
def I10 : QPres := mkQPres 3 2 [[(2, true), (2, true), (2, true), (1, true), (2, false)], [(2, true), (1, false), (1, false), (0, false), (0, false)]]
/-- state after move 11 of the certificate. -/
def I11 : QPres := mkQPres 3 2 [[(2, true), (2, true), (2, true), (1, true), (2, false)], [(2, true), (2, true), (2, true), (1, false), (0, false), (0, false)]]
/-- state after move 12 of the certificate. -/
def I12 : QPres := mkQPres 3 2 [[(2, true), (2, true), (1, true)], [(2, true), (2, true), (2, true), (1, false), (0, false), (0, false)]]
/-- state after move 13 of the certificate. -/
def I13 : QPres := mkQPres 3 2 [[(2, true), (2, true), (2, true), (2, true), (2, true), (1, true), (2, false), (2, false), (2, false)], [(2, true), (2, true), (2, true), (1, false), (0, false), (0, false)]]
/-- state after move 14 of the certificate. -/
def I14 : QPres := mkQPres 3 2 [[(2, true), (2, true), (2, true), (2, true), (2, true), (1, true), (2, false), (2, false), (2, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (0, false), (0, false)]]
/-- state after move 15 of the certificate. -/
def I15 : QPres := mkQPres 3 2 [[(2, true), (2, true), (1, true)], [(2, true), (2, true), (2, true), (2, true), (2, true), (0, false), (0, false)]]
/-- state after move 16 of the certificate. -/
def I16 : QPres := mkQPres 3 2 [[(2, true), (2, true), (1, true), (2, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (0, false), (0, false)]]
/-- state after move 17 of the certificate. -/
def I17 : QPres := mkQPres 3 2 [[(2, true), (2, true), (1, true), (2, false), (2, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (0, false), (0, false)]]
/-- state after move 18 of the certificate. -/
def I18 : QPres := mkQPres 2 1 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, false), (0, false)]]
/-- state after move 19 of the certificate. -/
def I19 : QPres := mkQPres 2 1 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true)]]

/-- moves 1-2. -/
def C1 : List QMove := [ .prolong, .nijinv 2 0 ]
/-- moves 3-4. -/
def C2 : List QMove := [ .nijinv 2 0, .nijinv 2 1 ]
/-- moves 5-6. -/
def C3 : List QMove := [ .nijinv 2 1, .conj 1 [(0, true), (0, true), (1, true), (1, true)] ]
/-- moves 7-8. -/
def C4 : List QMove := [ .lmul 0 1, .conj 1 [(1, false), (1, false), (0, false), (0, false)] ]
/-- moves 9-10. -/
def C5 : List QMove := [ .lmul 0 1, .conj 0 [(2, true)] ]
/-- moves 11-12. -/
def C6 : List QMove := [ .lmul 1 0, .conj 0 [(2, false)] ]
/-- moves 13-14. -/
def C7 : List QMove := [ .conj 0 [(2, true), (2, true), (2, true)], .lmul 1 0 ]
/-- moves 15-16. -/
def C8 : List QMove := [ .conj 0 [(2, false), (2, false), (2, false)], .nijinv 1 2 ]
/-- moves 17-18. -/
def C9 : List QMove := [ .nijinv 1 2, .delete 1 0 [(2, true), (2, true)] ]
/-- moves 19-20. -/
def C10 : List QMove := [ .neg 0, .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false)] ]

/-- positive control: block 1 passes. -/
theorem pos1 : checkCert C1 S I2 = true := by decide
/-- positive control: block 2 passes. -/
theorem pos2 : checkCert C2 I2 I4 = true := by decide
/-- positive control: block 3 passes. -/
theorem pos3 : checkCert C3 I4 I6 = true := by decide
/-- positive control: block 4 passes. -/
theorem pos4 : checkCert C4 I6 I8 = true := by decide
/-- positive control: block 5 passes. -/
theorem pos5 : checkCert C5 I8 I10 = true := by decide
/-- positive control: block 6 passes. -/
theorem pos6 : checkCert C6 I10 I12 = true := by decide
/-- positive control: block 7 passes. -/
theorem pos7 : checkCert C7 I12 I14 = true := by decide
/-- positive control: block 8 passes. -/
theorem pos8 : checkCert C8 I14 I16 = true := by decide
/-- positive control: block 9 passes. -/
theorem pos9 : checkCert C9 I16 I18 = true := by decide
/-- positive control: block 10 passes. -/
theorem pos10 : checkCert C10 I18 T = true := by decide

/-- the first 2 blocks chain. -/
theorem k2 : checkCert (C1 ++ C2) S I4 = true := checkCert_append pos1 pos2
/-- the first 3 blocks chain. -/
theorem k3 : checkCert (C1 ++ C2 ++ C3) S I6 = true := checkCert_append k2 pos3
/-- the first 4 blocks chain. -/
theorem k4 : checkCert (C1 ++ C2 ++ C3 ++ C4) S I8 = true := checkCert_append k3 pos4
/-- the first 5 blocks chain. -/
theorem k5 : checkCert (C1 ++ C2 ++ C3 ++ C4 ++ C5) S I10 = true := checkCert_append k4 pos5
/-- the first 6 blocks chain. -/
theorem k6 : checkCert (C1 ++ C2 ++ C3 ++ C4 ++ C5 ++ C6) S I12 = true := checkCert_append k5 pos6
/-- the first 7 blocks chain. -/
theorem k7 : checkCert (C1 ++ C2 ++ C3 ++ C4 ++ C5 ++ C6 ++ C7) S I14 = true := checkCert_append k6 pos7
/-- the first 8 blocks chain. -/
theorem k8 : checkCert (C1 ++ C2 ++ C3 ++ C4 ++ C5 ++ C6 ++ C7 ++ C8) S I16 = true := checkCert_append k7 pos8
/-- the first 9 blocks chain. -/
theorem k9 : checkCert (C1 ++ C2 ++ C3 ++ C4 ++ C5 ++ C6 ++ C7 ++ C8 ++ C9) S I18 = true := checkCert_append k8 pos9
/-- the first 10 blocks chain. -/
theorem k10 : checkCert (C1 ++ C2 ++ C3 ++ C4 ++ C5 ++ C6 ++ C7 ++ C8 ++ C9 ++ C10) S T = true := checkCert_append k9 pos10

/-- Positive control: the entire shipped certificate, converted independently, passes. -/
theorem q_pos : checkCert (C1 ++ C2 ++ C3 ++ C4 ++ C5 ++ C6 ++ C7 ++ C8 ++ C9 ++ C10) S T = true := k10


/-! ## Negative tests: each tampered certificate is rejected -/

/-- Tampering `block1_finish`: the first block is checked against the state after one move instead of two. -/
theorem bad_block1_finish : checkCert C1 S I1 = false := by decide

/-- Tampering `gen_oob`: a Nielsen move on generator 9 of a rank-3 presentation. -/
theorem bad_gen_oob : checkCert [QMove.prolong, QMove.nijinv 9 0] S I2 = false := by decide

/-- Tampering `diag_mul`: the diagonal multiplication `mul 0 0`, which `QMove.apply` refuses. -/
theorem bad_diag_mul : checkCert [QMove.prolong, QMove.mul 0 0] S I2 = false := by decide

/-- Tampering `relator_oob`: conjugation of relator 7 of a two-relator presentation. -/
theorem bad_relator_oob : checkCert [QMove.prolong, QMove.conj 7 []] S I2 = false := by decide

/-- Tampering `nijinv_to_nij`: move 2 (`nijinv 2 0`) run as `nij 2 0`. -/
theorem bad_nijinv_to_nij : checkCert [QMove.nij 2 0] I1 I2 = false := by decide

/-- Move 12 is `conj 1 Z` (0-based: relator 0 by `z⁻¹`).  Tampering `conj_sign`: run it with `z`. -/
theorem bad_conj_sign : checkCert [QMove.conj 0 [(2, true)]] I11 I12 = false := by decide

/-- Tampering `conj_shift`: the same conjugation with the conjugating word cyclically shifted. -/
theorem bad_conj_shift : checkCert [QMove.conj 0 [(2, false), (2, true)]] I11 I12 = false := by decide

/-- Tampering `drop_last`: the final block with its last move (move 20, `conj 1 YYYYY`) dropped. -/
theorem bad_drop_last : checkCert [QMove.neg 0] I18 T = false := by decide

/-- The pre-deletion state of move 17, from `ntest/frog.py`. -/
def preDelete : QPres := mkQPres 3 2 [[(2, true), (2, true), (1, true), (2, false), (2, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (0, false), (0, false)]]
/-- The post-deletion state of move 17. -/
def postDelete : QPres := mkQPres 2 1 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, false), (0, false)]]

/-- Every deletion move tried at `preDelete`: every generator 0-2, every relator position 0-1, eleven conjugating words. -/
def deleteCands : List QMove := [
  QMove.delete 0 0 [],
  QMove.delete 0 0 [(0, true)],
  QMove.delete 0 0 [(0, false)],
  QMove.delete 0 0 [(1, true)],
  QMove.delete 0 0 [(1, false)],
  QMove.delete 0 0 [(2, true)],
  QMove.delete 0 0 [(2, false)],
  QMove.delete 0 0 [(2, true), (2, true)],
  QMove.delete 0 0 [(2, false), (2, false)],
  QMove.delete 0 0 [(2, true), (2, false)],
  QMove.delete 0 0 [(0, true), (1, true)],
  QMove.delete 0 1 [],
  QMove.delete 0 1 [(0, true)],
  QMove.delete 0 1 [(0, false)],
  QMove.delete 0 1 [(1, true)],
  QMove.delete 0 1 [(1, false)],
  QMove.delete 0 1 [(2, true)],
  QMove.delete 0 1 [(2, false)],
  QMove.delete 0 1 [(2, true), (2, true)],
  QMove.delete 0 1 [(2, false), (2, false)],
  QMove.delete 0 1 [(2, true), (2, false)],
  QMove.delete 0 1 [(0, true), (1, true)],
  QMove.delete 1 0 [],
  QMove.delete 1 0 [(0, true)],
  QMove.delete 1 0 [(0, false)],
  QMove.delete 1 0 [(1, true)],
  QMove.delete 1 0 [(1, false)],
  QMove.delete 1 0 [(2, true)],
  QMove.delete 1 0 [(2, false)],
  QMove.delete 1 0 [(2, true), (2, true)],
  QMove.delete 1 0 [(2, false), (2, false)],
  QMove.delete 1 0 [(2, true), (2, false)],
  QMove.delete 1 0 [(0, true), (1, true)],
  QMove.delete 1 1 [],
  QMove.delete 1 1 [(0, true)],
  QMove.delete 1 1 [(0, false)],
  QMove.delete 1 1 [(1, true)],
  QMove.delete 1 1 [(1, false)],
  QMove.delete 1 1 [(2, true)],
  QMove.delete 1 1 [(2, false)],
  QMove.delete 1 1 [(2, true), (2, true)],
  QMove.delete 1 1 [(2, false), (2, false)],
  QMove.delete 1 1 [(2, true), (2, false)],
  QMove.delete 1 1 [(0, true), (1, true)],
  QMove.delete 2 0 [],
  QMove.delete 2 0 [(0, true)],
  QMove.delete 2 0 [(0, false)],
  QMove.delete 2 0 [(1, true)],
  QMove.delete 2 0 [(1, false)],
  QMove.delete 2 0 [(2, true)],
  QMove.delete 2 0 [(2, false)],
  QMove.delete 2 0 [(2, true), (2, true)],
  QMove.delete 2 0 [(2, false), (2, false)],
  QMove.delete 2 0 [(2, true), (2, false)],
  QMove.delete 2 0 [(0, true), (1, true)],
  QMove.delete 2 1 [],
  QMove.delete 2 1 [(0, true)],
  QMove.delete 2 1 [(0, false)],
  QMove.delete 2 1 [(1, true)],
  QMove.delete 2 1 [(1, false)],
  QMove.delete 2 1 [(2, true)],
  QMove.delete 2 1 [(2, false)],
  QMove.delete 2 1 [(2, true), (2, true)],
  QMove.delete 2 1 [(2, false), (2, false)],
  QMove.delete 2 1 [(2, true), (2, false)],
  QMove.delete 2 1 [(0, true), (1, true)] ]

/-- The deletion guard is not vacuous: the recorded deletion of generator 1 through relator 0 by `z z` does fire. -/
theorem correct_delete_fires : (QMove.delete 1 0 [(2,true),(2,true)]).apply preDelete = some postDelete := by decide

/-- **The deletion guard is sharp**: of the 66 candidate deletions, exactly one applies, and it is the recorded one. -/
theorem only_one_delete_fires : (deleteCands.filter (fun m => (m.apply preDelete).isSome)).length = 1 := by decide

/-! ## General facts behind the `diag_mul` and `rel_oob` tamperings

The block tests above are single instances.  These lemmas are the general statement
behind the diagonal-multiplication tampering: a `Q**`-certificate that contains
`mul i i` at any position, for any rank, any state, any start and any finish, is
rejected, because `QMove.apply` refuses that move and `replay` therefore returns
`none`. -/

theorem mul_self_apply (P : QPres) (i : Nat) : (QMove.mul i i).apply P = none := by
  rw [QMove.apply]
  simp

theorem replay_diag_none :
    ∀ (ms₁ ms₂ : List QMove) (P : QPres) (i : Nat),
      replay (ms₁ ++ QMove.mul i i :: ms₂) P = none
  | [], ms₂, P, i => by
      rw [List.nil_append, replay]
      simp [QMove.apply]
  | m :: ms₁, ms₂, P, i => by
      rw [List.cons_append, replay]
      cases h : m.apply P with
      | none => rfl
      | some P' => exact replay_diag_none ms₁ ms₂ P' i

theorem checkCert_diag_false (ms₁ ms₂ : List QMove)
    (start finish : QPres) (i : Nat) :
    checkCert (ms₁ ++ QMove.mul i i :: ms₂) start finish = false := by
  rw [checkCert, replay_diag_none]
  simp

/-! ## Independent replay in Python

`ntest/frog.py` replays all 34 shipped `Q**`-certificates of
`directions/qdouble-star/m9/certs/` with its own free reduction and its own
implementation of the six moves, and reaches exactly the recorded finish tuple of
every one of them (`python3 ntest/replay_all.py`).  That is an independent check of
the data; the theorems above are the kernel check of the checker.
-/

/-! ## Axiom audit -/
#print axioms q_pos
#print axioms correct_delete_fires
#print axioms only_one_delete_fires
#print axioms bad_block1_finish
#print axioms bad_gen_oob
#print axioms bad_diag_mul
#print axioms bad_relator_oob
#print axioms bad_nijinv_to_nij
#print axioms bad_conj_sign
#print axioms bad_conj_shift
#print axioms bad_drop_last
#print axioms mul_self_apply
#print axioms replay_diag_none
#print axioms checkCert_diag_false

end QNeg
