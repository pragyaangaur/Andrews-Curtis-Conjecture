/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import ACClosed

/-!
# ACKeys: closed-set certificates over a two-`Nat` state encoding

`ACClosed.lean` checks a closed set given as a `List St`, i.e. as a list of pairs
of lists of letters.  At the size that matters for the campaign's cap-17 rows
(136,576 states) that literal is far too heavy for the elaborator — about 200 KB
of memory per state.  This file supplies a compact form: a state is written as a
pair of `Nat`s, the two relator codes of `ACClosed.encW`, and the checker decodes
them.  The data cost drops to one `Nat` per relator, and the decoder is structural
recursion on a fuel argument, so the kernel evaluates it directly.

* `decAux` / `decW` — the decoder for `encW`, with `decAux_encW`.
* `closedCheckK` — the closure check over the compact data.
* `closedCheckK_sound` — a passing check gives the closure hypothesis of
  `ACBounds.not_reach_of_closed`, exactly as in `ACClosed`.
* `not_reach_of_treeK` — the certificate format.

Nothing here says anything about the Andrews-Curtis conjecture: every statement is
about bounded move sequences inside a fixed box.
-/

set_option maxRecDepth 1000000

namespace ACKeys

open ACBounds ACClosed

/-! ## Decoding -/

/-- The letter of a base-`5` digit `1,2,3,4`. -/
def decDigit (d : Nat) : Letter :=
  if d = 1 then lA else if d = 2 then la else if d = 3 then lB else lb

theorem decDigit_code (x : Letter) : decDigit (code x + 1) = x := by
  obtain ⟨g, s⟩ := x
  cases g <;> cases s <;> decide

/-- The decoder for `encW`, with `fuel` digits. -/
def decAux : Nat → Nat → Word
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else decDigit (n % 5) :: decAux f (n / 5)

/-- The decoder at the fuel that the campaign's boxes need: every relator of a
state in a box of cap at most 31 has at most 31 letters. -/
def decW (n : Nat) : Word := decAux 32 n

theorem decAux_encW : ∀ (k : Nat) (w : Word), w.length ≤ k → decAux k (encW w) = w := by
  intro k
  induction k with
  | zero =>
      intro w hw
      have h0 : w.length = 0 := Nat.le_zero.mp hw
      have hw' : w = [] := List.length_eq_zero_iff.mp h0
      subst hw'
      rfl
  | succ k ih =>
      intro w hw
      cases w with
      | nil => rfl
      | cons x xs =>
          have hne : encW (x :: xs) ≠ 0 := by
            simp only [encW]
            have := code_le x
            omega
          have hm : encW (x :: xs) % 5 = code x + 1 := encW_cons_mod x xs
          have hd : encW (x :: xs) / 5 = encW xs := encW_cons_div x xs
          show decAux (k + 1) (encW (x :: xs)) = x :: xs
          rw [decAux, if_neg hne, hm, hd, decDigit_code,
            ih xs (by simpa using hw)]

/-- The decoder inverts the encoder, at the fuel the campaign uses. -/
theorem decW_encW {w : Word} (h : w.length ≤ 32) : decW (encW w) = w :=
  decAux_encW 32 w h

/-- A state from its two relator codes. -/
def decP (p : Nat × Nat) : St := (decW p.1, decW p.2)

/-- Two encoded states with the same key are equal (in a box of cap at most 31). -/
theorem decP_eq {p : Nat × Nat} {q : St} (h : Nat.pair p.1 p.2 = encS q)
    (h1 : q.1.length ≤ 32) (h2 : q.2.length ≤ 32) : decP p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  have h' : a = encW c ∧ b = encW d := Nat.pair_eq_pair.mp h
  obtain ⟨e1, e2⟩ := h'
  simp only [decP, e1, e2, decW_encW h1, decW_encW h2]

/-! ## The check -/

/-- Every in-box successor of every decoded member of `S` has its key in `t`. -/
def closedCheckK (cap : Nat) (t : BTree) (S : List (Nat × Nat)) : Bool :=
  S.all (fun p => (stepBox cap (decP p)).all (fun q => bmem (encS q) t))

/-- **Soundness of the compact check.** -/
theorem closedCheckK_sound {cap : Nat} {t : BTree} {S : List (Nat × Nat)}
    (hcap : cap ≤ 31)
    (hkeys : keys t = S.map (fun p => Nat.pair p.1 p.2))
    (hchk : closedCheckK cap t S = true) :
    ∀ s ∈ S.map decP, ∀ tok ∈ allToks, totLen (apply tok s) ≤ cap →
      apply tok s ∈ S.map decP := by
  intro s hs tok htok hbox
  rw [List.mem_map] at hs
  obtain ⟨p, hp, rfl⟩ := hs
  have h1 : (stepBox cap (decP p)).all (fun q => bmem (encS q) t) = true := by
    have := List.all_eq_true.mp hchk p hp
    simpa only [closedCheckK] using this
  have h2 : bmem (encS (apply tok (decP p))) t = true :=
    List.all_eq_true.mp h1 _ (mem_stepBox.mpr ⟨tok, htok, rfl, hbox⟩)
  have h3 : encS (apply tok (decP p)) ∈ keys t := bmem_sound t _ h2
  rw [hkeys, List.mem_map] at h3
  obtain ⟨p', hp', he⟩ := h3
  have hlen : (apply tok (decP p)).1.length ≤ 32 ∧ (apply tok (decP p)).2.length ≤ 32 := by
    have := hbox
    simp only [totLen] at this
    constructor <;> omega
  rw [List.mem_map]
  exact ⟨p', hp', decP_eq he hlen.1 hlen.2⟩

/-- **The certificate format over compact data.** -/
theorem not_reach_of_treeK {cap : Nat} {p q : St} {S : List (Nat × Nat)} {t : BTree}
    (hcap : cap ≤ 31)
    (hkeys : keys t = S.map (fun r => Nat.pair r.1 r.2))
    (hchk : closedCheckK cap t S = true)
    (hp : p ∈ S.map decP) (hq : q ∉ S.map decP) :
    ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧
        run p ts = q :=
  ACBounds.not_reach_of_closed hp (closedCheckK_sound hcap hkeys hchk) hq

/-! ## Chunking and the two endpoint facts -/

theorem closedCheckK_append {cap : Nat} {t : BTree} {l₁ l₂ : List (Nat × Nat)}
    (h1 : closedCheckK cap t l₁ = true) (h2 : closedCheckK cap t l₂ = true) :
    closedCheckK cap t (l₁ ++ l₂) = true := by
  have h1' : (l₁.all (fun s => (stepBox cap (decP s)).all (fun q => bmem (encS q) t))) = true := h1
  have h2' : (l₂.all (fun s => (stepBox cap (decP s)).all (fun q => bmem (encS q) t))) = true := h2
  show (l₁ ++ l₂).all (fun s => (stepBox cap (decP s)).all (fun q => bmem (encS q) t)) = true
  rw [List.all_append, h1', h2']
  rfl

theorem closedCheckK_flatten {cap : Nat} {t : BTree} :
    ∀ cs : List (List (Nat × Nat)),
      (cs.map (fun c => closedCheckK cap t c)).all id = true →
      closedCheckK cap t cs.flatten = true
  | [], _ => rfl
  | c :: cs, h => by
      have h1 : closedCheckK cap t c = true := by
        have hh := h
        simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true] at hh
        exact hh.1
      have h2 : (cs.map (fun c => closedCheckK cap t c)).all id = true := by
        have hh := h
        simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true] at hh
        exact hh.2
      rw [List.flatten_cons]
      exact closedCheckK_append h1 (closedCheckK_flatten cs h2)

/-- The row lies in the decoded set, from a key search. -/
theorem mem_map_decP_of_any {S : List (Nat × Nat)} {p : St}
    (h1 : p.1.length ≤ 32) (h2 : p.2.length ≤ 32)
    (h : S.any (fun r => decide (Nat.pair r.1 r.2 = encS p)) = true) : p ∈ S.map decP := by
  rw [List.any_eq_true] at h
  obtain ⟨r, hr, hd⟩ := h
  have he : Nat.pair r.1 r.2 = encS p := of_decide_eq_true hd
  rw [List.mem_map]
  exact ⟨r, hr, decP_eq he h1 h2⟩


/-- The target is absent from the decoded set, from a key search. -/
theorem notMem_map_decP_of_all {S : List (Nat × Nat)} {q : St}
    (h : S.all (fun r => !(decide (decP r = q))) = true) : q ∉ S.map decP := by
  intro hq
  rw [List.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  have h1 := List.all_eq_true.mp h r hr
  simp at h1

end ACKeys
