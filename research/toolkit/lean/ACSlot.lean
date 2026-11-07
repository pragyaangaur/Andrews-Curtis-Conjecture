/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import ACPack

/-!
# ACSlot: a closed-set certificate as a static slot array (batched build, no tree)

Round 9 (`ACPack`, member m8) removed the *listing* of a closed set by packing the
state codes into `Nat` chunks and **building** the lookup tree inside the kernel; it
measured the wall that remains: the built tree cannot be shared between two
`decide`s, so every group of ~10^2 states pays the whole tree build again, and at
cap 17 that is ~9x10^4 s of kernel CPU.

This file removes the build. The certificate data is a **static slot array**: a
5-level nested list of `Nat` leaves, each leaf holding eight 80-bit keys
(`relator-0 code * 2^40 + relator-1 code`). A slot index `i < 8^6` is read by
shifting the digits of `i` — no build, no cons cells, no tree, and the array is
read straight out of the environment as data.

The second design point is the one that makes the soundness proof short. The closed
set is **defined** as the image of `getSlot` over the index range
(`chunkStates T 0 NSLOT`), so no consistency fact between "the data" and "the set"
has to be proved at all; and a successor is accepted when `getSlot (H k) T = k` for
one of three hashes, which is a membership in that image because `H k < NSLOT`. That
is: **no induction over the structure is needed**, only `H k < NSLOT`, the range
lemma, and `List.mem_filterMap`.

The array is filled by 3-choice cuckoo hashing in the generator (Python), so the
lookup is three slot reads; the placement is a data property, not a proof
obligation: a badly placed key can only make a check fail, never pass wrongly.

Nothing here says anything for or against the Andrews-Curtis conjecture: every
statement is about move sequences whose intermediate states stay inside a fixed box.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace ACSlot

open ACBounds ACClosed ACKeys ACPack

/-! ## Slots and keys -/

/-- The number of slots: `8^6 = 262144`. -/
def NSLOT : Nat := 8 ^ 6

/-- The hash mask, `NSLOT - 1 = 2^18 - 1`. -/
def HM : Nat := NSLOT - 1

/-- The width of one relator code in a slot key.  Every relator in a box of cap at
most 32 has code below `5^32 < 2^75`, so the slots of this file are used for boxes
of cap at most 17, where the code is below `5^17 < 2^40`. -/
def FB : Nat := 2 ^ 40

/-- The key of a pair of relator codes. -/
def keyB (p : Nat × Nat) : Nat := p.1 * FB + p.2

/-- The key of a state. -/
def keySt (q : St) : Nat := encW q.1 * FB + encW q.2

/-- The pair of relator codes of a key. -/
def keyPair (k : Nat) : Nat × Nat := (k / FB, k % FB)

theorem NSLOT_eq : NSLOT = 2 ^ 18 := by decide

theorem NSLOT_pos : 0 < NSLOT := by decide

theorem keyB_keyPair (k : Nat) : keyB (keyPair k) = k := by
  have h := Nat.div_add_mod k FB
  simp only [keyB, keyPair]
  rw [Nat.mul_comm]
  exact h

/-- The code of a word is bounded by `5` to the length. -/
theorem encW_lt : ∀ (w : Word), encW w < 5 ^ w.length
  | [] => by simp [encW]
  | x :: xs => by
      have hx : code x + 1 ≤ 4 := by have := code_le x; omega
      have ih := encW_lt xs
      simp only [encW, List.length_cons, Nat.pow_succ]
      omega

theorem keyB_inj {p q : Nat × Nat} (h1 : p.1 < FB) (h2 : p.2 < FB)
    (h3 : q.1 < FB) (h4 : q.2 < FB) (h : keyB p = keyB q) : p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [FB] at h1 h2 h3 h4
  simp only [keyB, FB] at h
  have hab : a = c ∧ b = d := by omega
  obtain ⟨rfl, rfl⟩ := hab
  rfl

/-- Every relator code of a state of total length at most 17 fits in one field. -/
theorem encW_lt_FB {w : Word} (h : w.length ≤ 17) : encW w < FB := by
  have h1 := encW_lt w
  simp only [FB]
  calc encW w < 5 ^ w.length := h1
    _ ≤ 5 ^ 17 := Nat.pow_le_pow_right (by decide) h
    _ < 2 ^ 40 := by decide

/-- Two states with the same key, in a box of cap at most 17, are equal. -/
theorem keySt_inj {p q : St} (h1 : totLen p ≤ 17) (h2 : totLen q ≤ 17)
    (h : keySt p = keySt q) : p = q := by
  obtain ⟨pa, pb⟩ := p
  obtain ⟨qa, qb⟩ := q
  simp only [totLen] at h1 h2
  have hp : pa.length ≤ 17 ∧ pb.length ≤ 17 := by constructor <;> omega
  have hq : qa.length ≤ 17 ∧ qb.length ≤ 17 := by constructor <;> omega
  have e1 : encW pa < FB := encW_lt_FB hp.1
  have e2 : encW pb < FB := encW_lt_FB hp.2
  have e3 : encW qa < FB := encW_lt_FB hq.1
  have e4 : encW qb < FB := encW_lt_FB hq.2
  have hk := keyB_inj (p := (encW pa, encW pb)) (q := (encW qa, encW qb)) e1 e2 e3 e4 h
  simp only [Prod.mk.injEq] at hk
  have f1 : pa = qa := by
    rw [← decW_encW (w := pa) (by omega), ← decW_encW (w := qa) (by omega), hk.1]
  have f2 : pb = qb := by
    rw [← decW_encW (w := pb) (by omega), ← decW_encW (w := qb) (by omega), hk.2]
  rw [f1, f2]

/-! ## The slot array and its reader -/

/-- One leaf of the array: a `Nat` holding eight keys of 80 bits. -/
abbrev Leaf := Nat

/-- Eight leaves. -/
abbrev L1 := List Leaf

/-- The array: `8^5` leaves in five levels of fanout eight. -/
abbrev Arr := List (List (List (List L1)))

/-- Read slot `i` of the array.  No build, no recursion on the data: the digits of
`i` are read by shifts, and a slot outside the array reads as `0`. -/
def getSlot (i : Nat) (T : Arr) : Nat :=
  let a4 := T.getD (i >>> 15) []
  let a3 := a4.getD ((i >>> 12) &&& 7) []
  let a2 := a3.getD ((i >>> 9) &&& 7) []
  let a1 := a2.getD ((i >>> 6) &&& 7) []
  let lf := a1.getD ((i >>> 3) &&& 7) 0
  (lf >>> (80 * (i &&& 7))) &&& (2 ^ 80 - 1)

/-! ## The three hashes -/

/-- First hash. -/
def H1 (k : Nat) : Nat := (((k * 620362056297712349) >>> 33) ^^^ k) &&& HM

/-- Second hash. -/
def H2 (k : Nat) : Nat := (((k * 8216841060052185535) >>> 26) ^^^ k) &&& HM

/-- Third hash. -/
def H3 (k : Nat) : Nat := (((k * 5562572005648607371) >>> 42) ^^^ k) &&& HM

theorem H1_lt (k : Nat) : H1 k < NSLOT := by
  have h := Nat.and_le_right (n := ((k * 620362056297712349) >>> 33) ^^^ k) (m := HM)
  simp only [H1, HM, NSLOT] at *
  omega

theorem H2_lt (k : Nat) : H2 k < NSLOT := by
  have h := Nat.and_le_right (n := ((k * 8216841060052185535) >>> 26) ^^^ k) (m := HM)
  simp only [H2, HM, NSLOT] at *
  omega

theorem H3_lt (k : Nat) : H3 k < NSLOT := by
  have h := Nat.and_le_right (n := ((k * 5562572005648607371) >>> 42) ^^^ k) (m := HM)
  simp only [H3, HM, NSLOT] at *
  omega

/-! ## The index range -/

/-- The `n` indices starting at `a`. -/
def rng : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, a => a :: rng n (a + 1)

theorem rng_append : ∀ (n m a : Nat), rng (n + m) a = rng n a ++ rng m (a + n)
  | 0, m, a => by simp [rng]
  | n + 1, m, a => by
      have h1 : n + 1 + m = (n + m) + 1 := by omega
      have h2 : a + (n + 1) = a + 1 + n := by omega
      rw [h1, h2]
      simp only [rng, rng_append n m (a + 1), List.cons_append]

theorem mem_rng {i a n : Nat} (h1 : a ≤ i) (h2 : i < a + n) : i ∈ rng n a := by
  induction n generalizing a with
  | zero => simp only [rng, List.not_mem_nil]; omega
  | succ n ih =>
      rw [rng]
      by_cases hi : i = a
      · simp [hi]
      · refine List.mem_cons_of_mem _ (ih (by omega) (by omega))

theorem lt_of_mem_rng {i a n : Nat} (h : i ∈ rng n a) : a ≤ i ∧ i < a + n := by
  induction n generalizing a with
  | zero => simp [rng] at h
  | succ n ih =>
      rw [rng, List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · have := ih h; omega

/-! ## The certificate -/

/-- The state of a slot, if the slot is occupied. -/
def slotState (i : Nat) (T : Arr) : Option St :=
  let k := getSlot i T
  if k = 0 then none else some (decP (keyPair k))

theorem slotState_some {i : Nat} {T : Arr} {s : St} (h : slotState i T = some s) :
    getSlot i T ≠ 0 ∧ s = decP (keyPair (getSlot i T)) := by
  simp only [slotState] at h
  by_cases hk : getSlot i T = 0
  · rw [if_pos hk] at h
    simp at h
  · rw [if_neg hk] at h
    exact ⟨hk, (Option.some.inj h).symm⟩

theorem slotState_some_of {i : Nat} {T : Arr} (hk : getSlot i T ≠ 0) :
    slotState i T = some (decP (keyPair (getSlot i T))) := by
  simp only [slotState]
  rw [if_neg hk]

/-- The states of the slots in the index range `a, a+1, …, a+n-1`. -/
def chunkStates (T : Arr) (a n : Nat) : List St := (rng n a).filterMap (fun i => slotState i T)

/-- Successor lookup: the key is the content of one of its three slots. -/
def foundSt (T : Arr) (q : St) : Bool :=
  let k := keySt q
  if k = 0 then false
  else (getSlot (H1 k) T == k) || (getSlot (H2 k) T == k) || (getSlot (H3 k) T == k)

/-- Everything one slot has to satisfy: its content is a genuine key of the state it
decodes to, that state is closed under the in-box moves, and the key is not the
target's key. -/
def slotOK (cap : Nat) (T : Arr) (q : St) (i : Nat) : Bool :=
  let k := getSlot i T
  (if k = 0 then true
    else (keySt (decP (keyPair k)) == k) && (stepBox cap (decP (keyPair k))).all (foundSt T))
  && (k != keySt q)

/-- The check of one chunk: the index range `a, …, a+n-1`. -/
def chunkCheck (cap : Nat) (T : Arr) (q : St) (a n : Nat) : Bool := (rng n a).all (slotOK cap T q)

theorem chunkCheck_append {cap : Nat} {T : Arr} {q : St} {a n m : Nat}
    (h1 : chunkCheck cap T q a n = true) (h2 : chunkCheck cap T q (a + n) m = true) :
    chunkCheck cap T q a (n + m) = true := by
  have h1' : (rng n a).all (slotOK cap T q) = true := h1
  have h2' : (rng m (a + n)).all (slotOK cap T q) = true := h2
  show (rng (n + m) a).all (slotOK cap T q) = true
  rw [rng_append, List.all_append, h1', h2']
  rfl

theorem slotOK_closed {cap : Nat} {T : Arr} {q : St} {i : Nat}
    (h : slotOK cap T q i = true) (hk : getSlot i T ≠ 0) :
    (stepBox cap (decP (keyPair (getSlot i T)))).all (foundSt T) = true ∧
      keySt (decP (keyPair (getSlot i T))) = getSlot i T := by
  simp only [slotOK] at h
  rw [if_neg hk] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.2, beq_iff_eq.mp h.1.1⟩

theorem slotOK_target {cap : Nat} {T : Arr} {q : St} {i : Nat}
    (h : slotOK cap T q i = true) : getSlot i T ≠ keySt q := by
  simp only [slotOK] at h
  simp only [Bool.and_eq_true] at h
  exact bne_iff_ne.mp h.2

/-! ## Soundness -/

/-- A found key is the content of an in-range slot. -/
theorem found_imp {T : Arr} {p : St} (h : foundSt T p = true) :
    getSlot (H1 (keySt p)) T = keySt p ∨ getSlot (H2 (keySt p)) T = keySt p ∨
      getSlot (H3 (keySt p)) T = keySt p := by
  simp only [foundSt] at h
  split at h
  · simp at h
  · rw [Bool.or_eq_true, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact Or.inl (beq_iff_eq.mp h)
    · exact Or.inr (Or.inl (beq_iff_eq.mp h))
    · exact Or.inr (Or.inr (beq_iff_eq.mp h))

/-- The pair of codes of the key of a state in a box of cap at most 17. -/
theorem keyPair_keySt {p : St} (h1 : p.1.length ≤ 17) (h2 : p.2.length ≤ 17) :
    keyPair (keySt p) = (encW p.1, encW p.2) := by
  have e1 : encW p.1 < FB := encW_lt_FB h1
  have e2 : encW p.2 < FB := encW_lt_FB h2
  have hpos : 0 < FB := by decide
  have hd : (encW p.1 * FB + encW p.2) / FB = encW p.1 := by
    rw [Nat.mul_comm (encW p.1) FB, Nat.add_comm (FB * encW p.1) (encW p.2),
      Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt e2, Nat.zero_add]
  have hm : (encW p.1 * FB + encW p.2) % FB = encW p.2 := by
    rw [Nat.mul_comm (encW p.1) FB, Nat.mul_add_mod, Nat.mod_eq_of_lt e2]
  simp only [keyPair, keySt, hd, hm]

/-- A state whose key sits in an in-range slot is a state of the certificate. -/
theorem mem_chunkStates_of_slot {T : Arr} {p : St} (hlen : totLen p ≤ 17) {i : Nat}
    (hi : i < NSLOT) (h : getSlot i T = keySt p) (hne : keySt p ≠ 0) :
    p ∈ chunkStates T 0 NSLOT := by
  rw [chunkStates, List.mem_filterMap]
  have hp : p.1.length ≤ 17 ∧ p.2.length ≤ 17 := by
    simp only [totLen] at hlen; constructor <;> omega
  have hk : keyPair (getSlot i T) = (encW p.1, encW p.2) := by
    rw [h]; exact keyPair_keySt hp.1 hp.2
  refine ⟨i, mem_rng (by omega) (by omega), ?_⟩
  rw [slotState_some_of (by rw [h]; exact hne)]
  simp only [hk, decP, Option.some.injEq]
  rw [decW_encW (by omega), decW_encW (by omega)]

/-- **A found state is a state of the certificate.** -/
theorem mem_chunkStates_of_found {T : Arr} {p : St} (hlen : totLen p ≤ 17)
    (h : foundSt T p = true) : p ∈ chunkStates T 0 NSLOT := by
  have hne : keySt p ≠ 0 := by
    intro h0
    simp only [foundSt, h0] at h
    simp at h
  rcases found_imp h with h | h | h
  · exact mem_chunkStates_of_slot hlen (H1_lt _) h hne
  · exact mem_chunkStates_of_slot hlen (H2_lt _) h hne
  · exact mem_chunkStates_of_slot hlen (H3_lt _) h hne

/-- **Closure of the certificate**, from the slot checks. -/
theorem closed_of_slots {cap : Nat} {T : Arr} {q : St} (hcap : cap ≤ 17)
    (hchk : ∀ i, i < NSLOT → slotOK cap T q i = true) :
    ∀ s ∈ chunkStates T 0 NSLOT, ∀ t ∈ allToks, totLen (apply t s) ≤ cap →
      apply t s ∈ chunkStates T 0 NSLOT := by
  intro s hs t ht hbox
  rw [chunkStates, List.mem_filterMap] at hs
  obtain ⟨i, hi, hsi⟩ := hs
  have hi' : i < NSLOT := (lt_of_mem_rng hi).2
  obtain ⟨hk, rfl⟩ := slotState_some hsi
  obtain ⟨hfound, -⟩ := slotOK_closed (hchk i hi') hk
  have hmem : apply t (decP (keyPair (getSlot i T))) ∈
      stepBox cap (decP (keyPair (getSlot i T))) := mem_stepBox.mpr ⟨t, ht, rfl, hbox⟩
  have h2 := List.all_eq_true.mp hfound _ hmem
  exact mem_chunkStates_of_found (by omega) h2

/-- **The target is absent**, from the per-slot target checks. -/
theorem notMem_of_target {cap : Nat} {T : Arr} {q : St}
    (hchk : ∀ i, i < NSLOT → slotOK cap T q i = true) : q ∉ chunkStates T 0 NSLOT := by
  intro hq
  rw [chunkStates, List.mem_filterMap] at hq
  obtain ⟨i, hi, hqi⟩ := hq
  have hi' : i < NSLOT := (lt_of_mem_rng hi).2
  obtain ⟨hk, rfl⟩ := slotState_some hqi
  obtain ⟨-, hkey⟩ := slotOK_closed (hchk i hi') hk
  exact slotOK_target (hchk i hi') hkey.symm

/-! ## The certificate format -/

/-- **The row theorem from a slot-array certificate.**  If every slot of the array
passes the check and the start state is found by the hashes, then no in-box move
sequence takes the start to the target. -/
theorem not_reach_of_slots {cap : Nat} {T : Arr} {p q : St} (hcap : cap ≤ 17)
    (hp : foundSt T p = true) (hp17 : totLen p ≤ 17)
    (hchk : ∀ i, i < NSLOT → slotOK cap T q i = true) :
    ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧
        run p ts = q := by
  refine ACBounds.not_reach_of_closed (S := chunkStates T 0 NSLOT)
    (mem_chunkStates_of_found hp17 hp) ?_ (notMem_of_target hchk)
  intro s hs t ht hbox
  exact closed_of_slots hcap hchk s hs t ht hbox

/-- Slot checks out of a whole-array chunk check. -/
theorem slotOK_of_chunkCheck_all {cap : Nat} {T : Arr} {q : St}
    (h : chunkCheck cap T q 0 NSLOT = true) : ∀ i, i < NSLOT → slotOK cap T q i = true := by
  intro i hi
  exact List.all_eq_true.mp h i (mem_rng (by omega) (by omega))

end ACSlot
