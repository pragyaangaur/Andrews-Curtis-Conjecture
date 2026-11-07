/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Basic

/-!
# ACBounds: bounded search is exact, for the twelve-move Andrews-Curtis system

This file contains the reusable half of direction d9 (round 7, member m8): a
machine-checked bridge between a *breadth-first enumeration inside a box* and
the *existence of a move sequence inside that box*.

The campaign's negative bounds ("no AC path from P to the standard tuple with
every intermediate of total length at most c") are produced by hand-written
programs.  Nothing in the kernel says a bounded enumeration is exact: that a
list of states produced by a breadth-first expansion is precisely the set of
endpoints of in-box move sequences, and that an enumerated set which avoids a
target therefore certifies the absence of a short certificate.  This file
supplies that missing link for the twelve-move system of rank two.

## Conventions

* Letters are pairs `(generator, sign)`, with `false = a`, `true = b` for the
  generator and `true = +, false = -` for the sign.  A word is a list of
  letters, kept freely reduced.  A state is a pair of words, the relators
  `r₀, r₁` of a rank-two presentation.
* The twelve moves are `i0 i1` (invert a relator), `m0 m1` (right-multiply one
  relator by the other), and `c0a c0A c0b c0B c1a c1A c1b c1B` (conjugate a
  relator by one of the four letters).  This is exactly the move set of
  `toolkit/ac.py` with conjugator bound one, the "twelve-move system".
* The box is the set of states whose total relator length is at most `cap`.

## Main results

* `mem_stepBox`: membership in the boxed successor set, unpacked.
* `layer_transfer`: the layers of the expansion are monotone in the start.
* `mem_layer_run`: **completeness** — if every intermediate state of a move
  sequence stays in the box, the endpoint lies in the layer indexed by the
  length of the sequence.
* `not_reach_of_avoids`: **the lower-bound certificate format** — if the
  enumeration of all in-box endpoints of sequences of length at most `k`
  avoids a target, then no in-box sequence of length at most `k` reaches it.

No claim about the Andrews-Curtis conjecture is made or implied; the statement
is about bounded move sequences only.
-/

set_option maxRecDepth 1000000

namespace ACBounds

/-! ## Letters, words, states -/

/-- A letter: generator (`false` = a, `true` = b) and sign (`true` = +). -/
abbrev Letter : Type := Bool × Bool

/-- A word: a list of letters, kept freely reduced by `red`. -/
abbrev Word : Type := List Letter

/-- A rank-two presentation: the pair of relators. -/
abbrev St : Type := Word × Word

/-- Free reduction: fold with a reversed accumulator, then reverse. -/
def red (l : Word) : Word :=
  (l.foldl (fun acc x =>
    match acc with
    | [] => [x]
    | y :: t => if y.1 = x.1 then (if y.2 = !x.2 then t else x :: acc) else x :: acc) []).reverse

/-- The inverse letter. -/
def invL (x : Letter) : Letter := (x.1, !x.2)

/-- The inverse word (the word is reduced, so this is reduced). -/
def invW (w : Word) : Word := w.reverse.map invL

/-- Concatenation followed by reduction. -/
def mulW (u v : Word) : Word := red (u ++ v)

/-- Conjugation of a word by one letter. -/
def conjW (c : Letter) (u : Word) : Word := red (c :: (u ++ [invL c]))

/-- The total relator length of a state. -/
def totLen (p : St) : Nat := p.1.length + p.2.length

/-! ## The twelve moves -/

/-- The twelve move names of the system. -/
inductive Tok : Type where
  | i0 | i1 | m0 | m1
  | c0a | c0A | c0b | c0B | c1a | c1A | c1b | c1B
  deriving DecidableEq, Repr

/-- All twelve move names, in a fixed order. -/
def allToks : List Tok :=
  [Tok.i0, Tok.i1, Tok.m0, Tok.m1, Tok.c0a, Tok.c0A, Tok.c0b, Tok.c0B,
   Tok.c1a, Tok.c1A, Tok.c1b, Tok.c1B]

/-- Every move name is one of the twelve. -/
theorem allToks_complete (t : Tok) : t ∈ allToks := by
  cases t <;> simp [allToks]


/-- The letter `a`, `A`, `b`, `B` as `(generator, sign)`. -/
def la : Letter := (false, true)
def lA : Letter := (false, false)
def lb : Letter := (true, true)
def lB : Letter := (true, false)

/-- Apply one move to a state. -/
def apply : Tok → St → St
  | Tok.i0, p => (invW p.1, p.2)
  | Tok.i1, p => (p.1, invW p.2)
  | Tok.m0, p => (mulW p.1 p.2, p.2)
  | Tok.m1, p => (p.1, mulW p.2 p.1)
  | Tok.c0a, p => (conjW la p.1, p.2)
  | Tok.c0A, p => (conjW lA p.1, p.2)
  | Tok.c0b, p => (conjW lb p.1, p.2)
  | Tok.c0B, p => (conjW lB p.1, p.2)
  | Tok.c1a, p => (p.1, conjW la p.2)
  | Tok.c1A, p => (p.1, conjW lA p.2)
  | Tok.c1b, p => (p.1, conjW lb p.2)
  | Tok.c1B, p => (p.1, conjW lB p.2)

/-- Run a sequence of moves from a state. -/
def run (p : St) (ts : List Tok) : St := ts.foldl (fun s t => apply t s) p

@[simp] theorem run_nil (p : St) : run p [] = p := rfl

@[simp] theorem run_cons (p : St) (t : Tok) (ts : List Tok) :
    run p (t :: ts) = run (apply t p) ts := rfl

/-! ## The boxed successor set and its layers -/

/-- The box test: total relator length at most `cap`. -/
def boxOK (cap : Nat) (q : St) : Bool := decide (totLen q ≤ cap)

/-- The in-box successors of a state, in the fixed token order. -/
def stepBox (cap : Nat) (p : St) : List St :=
  (allToks.map (fun t => apply t p)).filter (boxOK cap)

/-- Layer `n` of the boxed expansion from `p`: the endpoints of the in-box
sequences of moves of length exactly `n`. -/
def layer (cap : Nat) (p : St) : Nat → List St
  | 0 => [p]
  | n + 1 => (layer cap p n).flatMap (stepBox cap)

/-- All endpoints of in-box sequences of length at most `k`. -/
def seenUpTo (cap : Nat) (p : St) (k : Nat) : List St :=
  (List.range (k + 1)).flatMap (fun i => layer cap p i)

/-! ## The three lemmas -/

/-- Membership in the boxed successor set, unpacked. -/
theorem mem_stepBox {cap : Nat} {p q : St} :
    q ∈ stepBox cap p ↔ ∃ t ∈ allToks, apply t p = q ∧ totLen q ≤ cap := by
  simp only [stepBox, List.mem_filter, List.mem_map, boxOK]
  constructor
  · rintro ⟨⟨t, ht, hq⟩, hbox⟩
    exact ⟨t, ht, hq, of_decide_eq_true hbox⟩
  · rintro ⟨t, ht, hq, hbox⟩
    exact ⟨⟨t, ht, hq⟩, decide_eq_true hbox⟩

/-- A monotonicity lemma for the expansion of a list. -/
theorem flatMap_mono {α β : Type} {f : α → List β} {l l' : List α}
    (h : ∀ x ∈ l, x ∈ l') : ∀ y ∈ l.flatMap f, y ∈ l'.flatMap f := by
  intro y hy
  rw [List.mem_flatMap] at hy ⊢
  obtain ⟨x, hx, hyx⟩ := hy
  exact ⟨x, h x hx, hyx⟩

/-- The layers from a state that already lies in layer one are contained in the
corresponding layers from the original state. -/
theorem layer_transfer {cap : Nat} {p q : St} (h : q ∈ layer cap p 1) :
    ∀ {m : Nat} {y : St}, y ∈ layer cap q m → y ∈ layer cap p (m + 1) := by
  intro m
  induction m with
  | zero =>
      intro y hy
      simp only [layer, List.mem_singleton] at hy
      subst hy
      simpa [layer] using h
  | succ m ih =>
      intro y hy
      have h1 : y ∈ (layer cap p (m + 1)).flatMap (stepBox cap) :=
        flatMap_mono (f := stepBox cap) (l := layer cap q m) (l' := layer cap p (m + 1))
          (fun x hx => ih hx) y hy
      simpa [layer] using h1

/-- **Completeness of the boxed enumeration.**  If every intermediate state of
the move sequence `ts` from `p` stays in the box, then the endpoint of `ts` lies
in the layer indexed by the length of `ts`. -/
theorem mem_layer_run (cap : Nat) : ∀ (p : St) (ts : List Tok), totLen p ≤ cap →
    (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) →
    run p ts ∈ layer cap p ts.length := by
  intro p ts
  induction ts generalizing p with
  | nil =>
      intro _ _
      simp [run, layer]
  | cons t ts ih =>
      intro hp hbox
      have hstep : totLen (apply t p) ≤ cap := by
        have h1 := hbox 1 (by simp)
        simpa [run] using h1
      have hmem1 : apply t p ∈ layer cap p 1 := by
        have h2 : apply t p ∈ stepBox cap p := by
          rw [mem_stepBox]
          exact ⟨t, allToks_complete t, rfl, hstep⟩
        simpa [layer] using h2
      have hbox' : ∀ i, i ≤ ts.length → totLen (run (apply t p) (ts.take i)) ≤ cap := by
        intro i hi
        have h1 := hbox (i + 1) (by simpa [List.length_cons] using Nat.succ_le_succ hi)
        simpa [run, List.take_succ_cons, List.foldl_cons] using h1
      have hrec := ih (apply t p) hstep hbox'
      have htrans := layer_transfer hmem1 hrec
      simpa [run, List.foldl_cons, List.length_cons] using htrans

/-! ## The lower-bound certificate format -/

/-- **The certificate format.**  If the enumeration of all in-box endpoints of
sequences of length at most `k` avoids the state `q`, then no in-box sequence of
length at most `k` reaches `q`. -/
theorem not_reach_of_avoids {cap k : Nat} {p q : St} (hp : totLen p ≤ cap)
    (h : (seenUpTo cap p k).all (fun s => !(s == q)) = true) :
    ¬ ∃ ts : List Tok, ts.length ≤ k ∧
        (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧ run p ts = q := by
  rintro ⟨ts, hk, hbox, hend⟩
  have hmem : run p ts ∈ seenUpTo cap p k := by
    rw [seenUpTo, List.mem_flatMap]
    exact ⟨ts.length, by rw [List.mem_range]; exact Nat.lt_succ_of_le hk,
      mem_layer_run cap p ts hp hbox⟩
  have hall := (List.all_eq_true.mp h) _ hmem
  rw [hend] at hall
  simp at hall

/-- A layer-by-layer form of the certificate format, convenient for the kernel:
if the target is absent from every layer up to `K`, no in-box sequence of
length at most `K` reaches it. -/
theorem not_reach_of_layers {cap K : Nat} {p q : St} (hp : totLen p ≤ cap)
    (h : ∀ k, k ≤ K → (layer cap p k).all (fun s => !(s == q)) = true) :
    ¬ ∃ ts : List Tok, ts.length ≤ K ∧
        (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧ run p ts = q := by
  rintro ⟨ts, hk, hbox, hend⟩
  have hmem : run p ts ∈ layer cap p ts.length := mem_layer_run cap p ts hp hbox
  have hall := (List.all_eq_true.mp (h ts.length hk)) _ hmem
  rw [hend] at hall
  simp at hall

/-! ## The closed-set certificate format -/

/-- **The closed-set certificate format.**  A list `S` of states that contains
the start, is closed under every in-box move, and avoids the target, certifies
that *no* in-box move sequence of any length reaches the target.  This is the
depth-unbounded form of a negative bound: the campaign's hand-written breadth
first searches produce exactly such sets. -/
theorem not_reach_of_closed {cap : Nat} {p q : St} {S : List St}
    (hp : p ∈ S)
    (hclosed : ∀ s ∈ S, ∀ t ∈ allToks, totLen (apply t s) ≤ cap → apply t s ∈ S)
    (hq : q ∉ S) :
    ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧
        run p ts = q := by
  rintro ⟨ts, hbox, hend⟩
  have hmain : ∀ (p : St), p ∈ S → ∀ ts : List Tok,
      (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) → run p ts ∈ S := by
    intro p hp' ts
    induction ts generalizing p with
    | nil => intro _; simpa [run] using hp'
    | cons t ts ih =>
        intro hbox
        have hstep : totLen (apply t p) ≤ cap := by
          have h1 := hbox 1 (by simp)
          simpa [run] using h1
        have hmem : apply t p ∈ S := hclosed p hp' t (allToks_complete t) hstep
        have hbox' : ∀ i, i ≤ ts.length → totLen (run (apply t p) (ts.take i)) ≤ cap := by
          intro i hi
          have h1 := hbox (i + 1) (by simpa [List.length_cons] using Nat.succ_le_succ hi)
          simpa [run, List.take_succ_cons, List.foldl_cons] using h1
        have := ih (apply t p) hmem hbox'
        rwa [run_cons]
  have hres := hmain p hp ts hbox
  rw [hend] at hres
  exact hq hres

end ACBounds

