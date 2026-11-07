/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import ACConj

/-!
# ACConjPeak: the exact scope of the twelve-move model, and the transfer theorem from the peak lemma

Two things:

* `g0_singleton`, `g1_singleton`: the twelve-move system is *exactly* the extended move
  set with conjugators of length at most one.  So the closed-set layer's move set is the
  AC move set restricted to conjugators of length ≤ 1, no more and no less.
* the **peak lemma** `PeakLemma`, stated as a proposition, and the **transfer theorem**
  `full_conj_mem_of_closed_of_peak` derived from it: under the peak lemma a set closed
  under the twelve moves inside a box is closed under conjugation by an arbitrary word
  whose conjugate is in the box.  The peak lemma itself is not proved here; see
  `ACConj.md` section 4 for what is proved toward it and the two kernel-refuted
  shortcuts.

Nothing here says anything about the Andrews-Curtis conjecture.
-/

set_option maxRecDepth 1000000

namespace ACConj

/-- The token that conjugates relator `1` by the letter `c`. -/
def tokC1 : Letter → Tok
  | (0, true) => Tok.c1a
  | (0, false) => Tok.c1A
  | (1, true) => Tok.c1b
  | (1, false) => Tok.c1B

theorem apply_tokC1 (c : Letter) (p : St) : apply (tokC1 c) p = (p.1, conjL c p.2) := by
  obtain ⟨g, s⟩ := c
  obtain ⟨a, b⟩ := p
  fin_cases g <;> cases s <;> rfl

/-- A conjugation of relator `0` by a single letter is a twelve-move token. -/
theorem g0_singleton (c : Letter) (p : St) : applyX (XTok.g0 [c]) p = apply (tokC0 c) p := by
  rw [apply_tokC0]
  rfl

/-- A conjugation of relator `1` by a single letter is a twelve-move token. -/
theorem g1_singleton (c : Letter) (p : St) : applyX (XTok.g1 [c]) p = apply (tokC1 c) p := by
  rw [apply_tokC1]
  rfl

/-! ## The peak lemma -/

/-- **The peak lemma.**  Every intermediate conjugate along the suffix chain of a
conjugator is no longer than the longer of the two ends.  This is the single missing
ingredient of the unconditional transfer theorem; it holds on every instance tested
(`exp/peak.py`, `exp/peak3.py`, `exp/adversarial.py`) but is not proved here. -/
def PeakLemma : Prop :=
  ∀ (u w s : Word), (∃ p : Word, w = p ++ s) →
    (conjW s u).length ≤ max u.length (conjW w u).length

/-- Under the peak lemma, every intermediate state of the simulation of a conjugation
stays in the box spanned by the two endpoints. -/
theorem run_sim_totLen_le_of_peak (hLP : PeakLemma) (u q w : Word) (hu : red u = u) :
    ∀ i, i ≤ (sim u w).length →
      totLen (run (u, q) ((sim u w).take i)) ≤
        max u.length (conjW w u).length + q.length := by
  intro i hi
  obtain ⟨w', p, hw, ht⟩ := sim_take u w i
  rw [ht, run_sim u q hu w']
  have h1 : (conjW w' u).length ≤ max u.length (conjW w u).length := hLP u w w' ⟨p, hw⟩
  simp only [totLen]
  omega

/-- **The transfer theorem, from the peak lemma.**  If `S` is closed under the twelve
moves inside the box of cap `cap`, and both the member `(u,q)` and the conjugate
`(conjW w u, q)` are in the box, then the conjugate is again a member.  This is the
statement the closed-set layer needs in order to certify negatives for the full
Andrews-Curtis move set rather than for the twelve-move restriction. -/
theorem full_conj_mem_of_closed_of_peak (hLP : PeakLemma) {cap : Nat} {S : List St}
    (hS : ClosedAt cap S) {u q w : Word} (hu : red u = u) (hp : (u, q) ∈ S)
    (hpu : totLen (u, q) ≤ cap) (hbox : totLen (conjW w u, q) ≤ cap) :
    (conjW w u, q) ∈ S := by
  have h := run_mem_of_closed hS (sim u w) (u, q) hp (fun i hi => by
    have h1 := run_sim_totLen_le_of_peak hLP u q w hu i hi
    have h2 : max u.length (conjW w u).length + q.length ≤ cap := by
      simp only [totLen] at hpu hbox
      omega
    omega)
  rwa [run_sim u q hu w] at h

/-! ## Axiom audit -/

#print axioms ACConj.apply_tokC1
#print axioms ACConj.g0_singleton
#print axioms ACConj.g1_singleton
#print axioms ACConj.run_sim_totLen_le_of_peak
#print axioms ACConj.full_conj_mem_of_closed_of_peak

end ACConj
