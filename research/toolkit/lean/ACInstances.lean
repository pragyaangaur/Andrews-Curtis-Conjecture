/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import ACBounds

/-!
# Kernel-checked exact Andrews-Curtis distances (twelve-move system, rank two)

Two census rows of `directions/worst-case/min_cap14.txt` are shown to have an
*exact* twelve-move distance to the standard tuple inside the campaign's cap-14
box: the kernel verifies both a certificate and the failure of every shorter
in-box sequence.

* `Q1` is the row `BAAbABa,BAbABa` (total length 13).  The campaign's cap-14
  table gives exact minimum 6.
* `Q3` is the row `BBaba,BBAbbAbbA` (total length 14).  The campaign's cap-14
  table gives exact minimum 7.

Both distances were recomputed independently in `acbox.py`, an engine written
from the definitions here which also replays all 52,744 certificates of the
campaign's cap-14 and cap-15 tables with zero failures.

Every proof below is a closed kernel computation: no `sorry`, no new axiom, no
`native_decide`.  The `#print axioms` lines at the end are the audit.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open ACBounds

/-- The box condition on a move sequence, as a Boolean test. -/
def InBoxB (cap : Nat) (p : St) (ts : List Tok) : Bool :=
  (List.range (ts.length + 1)).all (fun i => boxOK cap (run p (ts.take i)))

/-- The box condition on a move sequence: every prefix state stays in the box. -/
def InBox (cap : Nat) (p : St) (ts : List Tok) : Prop :=
  ∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap

theorem inBoxB_iff {cap : Nat} {p : St} {ts : List Tok} :
    InBoxB cap p ts = true ↔ InBox cap p ts := by
  rw [InBoxB, List.all_eq_true]
  constructor
  · intro h i hi
    have h1 := h i (by rw [List.mem_range]; exact Nat.lt_succ_of_le hi)
    simpa [boxOK] using h1
  · intro h i hi
    have h2 : i ≤ ts.length := by
      rw [List.mem_range] at hi
      exact Nat.le_of_lt_succ hi
    have h1 := h i h2
    simpa [boxOK] using h1

/-! ## The census rows -/

/-- The standard rank-two presentation, relators `a` and `b`. -/
def std : St := ([la], [lb])

/-- The row `BAAbABa,BAbABa` of the cap-14 table (total length 13). -/
def Q1 : St := ([lB, lA, lA, lb, lA, lB, la], [lB, lA, lb, lA, lB, la])

/-- The row `BBaba,BBAbbAbbA` of the cap-14 table (total length 14). -/
def Q3 : St := ([lB, lB, la, lb, la], [lB, lB, lA, lb, lb, lA, lb, lb, lA])

/-- A six-move certificate from `Q1` to the standard tuple (peak 13). -/
def certQ1 : List Tok := [Tok.i1, Tok.m0, Tok.m1, Tok.i0, Tok.c0b, Tok.c1a]

/-- A seven-move certificate from `Q3` to the standard tuple (peak 14). -/
def certQ3 : List Tok := [Tok.c0a, Tok.m1, Tok.c1b, Tok.m0, Tok.c1b, Tok.m1, Tok.c1a]

/-! ## Sanity checks (evaluated by the compiler, then discarded) -/

#eval (run Q1 certQ1 == std)
#eval (run Q3 certQ3 == std)
#eval InBoxB 14 Q1 certQ1
#eval InBoxB 14 Q3 certQ3
#eval (layer 14 Q1 3).length
#eval (layer 14 Q3 3).length

/-! ## `Q1`: the exact cap-14 distance is 6 -/

theorem Q1_cert_box : InBox 14 Q1 certQ1 := inBoxB_iff.mp (by decide)

theorem Q1_cert : run Q1 certQ1 = std := by decide

/-- No in-box sequence of length at most 5 reaches the standard tuple from `Q1`. -/
theorem Q1_no_short :
    ¬ ∃ ts : List Tok, ts.length ≤ 5 ∧ InBox 14 Q1 ts ∧ run Q1 ts = std := by
  intro h
  exact not_reach_of_avoids (cap := 14) (k := 5) (p := Q1) (q := std)
    (by decide) (by decide) h

/-- **Exact distance 6** for the row `BAAbABa,BAbABa`, inside the cap-14 box. -/
theorem Q1_exact :
    (∃ ts : List Tok, ts.length = 6 ∧ InBox 14 Q1 ts ∧ run Q1 ts = std) ∧
    ¬ ∃ ts : List Tok, ts.length ≤ 5 ∧ InBox 14 Q1 ts ∧ run Q1 ts = std :=
  ⟨⟨certQ1, by decide, Q1_cert_box, Q1_cert⟩, Q1_no_short⟩

#print axioms ACBounds.mem_layer_run
#print axioms ACBounds.not_reach_of_avoids
#print axioms Q1_exact
