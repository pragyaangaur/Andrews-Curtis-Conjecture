/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import ACBounds

/-!
# ACComponents: what a closed-set certificate can and cannot be

Direction K7 (round 8, member m8).  Round 7's `ACBounds.lean` proves the
*format* of a closed-set certificate.  This file settles the shape of the objects
that can inhabit it, which is what decides whether a *compact* certificate — a
monotone potential function, or a small closed set — can exist.

Fix a cap, so the box is the set of states whose total relator length is at most
`cap`, and let `Reach cap p q` be reachability from `p` to `q` by a sequence of
the twelve moves all of whose intermediate states stay in the box.

* `closed_reach_mem` — **the principal direction.**  A closed predicate that
  contains `p` contains every state reachable from `p` inside the box.  Hence a
  closed-set certificate for a negative bound has at least as many listed states
  as the in-box component of its start: the component is the *minimum* data, and
  every other certificate is a superset of it.
* `closed_iff_reach` — with the trivial bookkeeping hypothesis that the set lies
  in the box, a predicate is closed under the in-box moves exactly when it is a
  union of in-box reachable sets.  There is no third kind of object.
* `reach_closedP` — the component itself *is* a closed set, so the bound in the
  first item is attained.
* `potential_reach_le` / `potential_closed` — **the potential-function answer.**
  If `φ` does not increase along in-box moves then every state reachable from
  `p` satisfies `φ x ≤ φ p`; the potential's sublevel set is therefore a closed
  set of exactly the shape above, and the potential format adds nothing to the
  closed-set format.
* `potential_eq_of_reach` — and when two states are reachable from each other, a
  non-increasing potential is *constant* between them, i.e. it is an invariant.

Nothing here says anything about the Andrews-Curtis conjecture: every statement
is about bounded move sequences inside a fixed box.
-/

set_option maxRecDepth 1000000

namespace ACComp

open ACBounds

/-! ## In-box reachability -/

/-- `Reach cap p q`: some sequence of the twelve moves takes `p` to `q` with
every intermediate state inside the box. -/
inductive Reach (cap : Nat) : St → St → Prop where
  | refl {p : St} (h : totLen p ≤ cap) : Reach cap p p
  | step {p q : St} (h : Reach cap p q) (t : Tok) (hbox : totLen (apply t q) ≤ cap) :
      Reach cap p (apply t q)

/-- Reachability is transitive. -/
theorem Reach.trans {cap : Nat} {p q r : St} (h1 : Reach cap p q) (h2 : Reach cap q r) :
    Reach cap p r := by
  induction h2 with
  | refl _ => exact h1
  | step _ t hbox ih => exact Reach.step ih t hbox

/-- A run whose intermediates all stay in the box is a `Reach` derivation. -/
theorem Reach.of_run : ∀ (p : St) (ts : List Tok), totLen p ≤ cap →
    (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) → Reach cap p (run p ts) := by
  intro p ts
  induction ts generalizing p with
  | nil => intro hp _; simpa [run] using Reach.refl (cap := cap) hp
  | cons t ts ih =>
      intro hp hbox
      have h1 : totLen (apply t p) ≤ cap := by simpa [run] using hbox 1 (by simp)
      have hstep : Reach cap p (apply t p) := Reach.step (Reach.refl hp) t h1
      have hbox' : ∀ i, i ≤ ts.length → totLen (run (apply t p) (ts.take i)) ≤ cap := by
        intro i hi
        have h2 := hbox (i + 1) (by simpa [List.length_cons] using Nat.succ_le_succ hi)
        simpa [run, List.take_succ_cons, List.foldl_cons] using h2
      have hrec : Reach cap (apply t p) (run (apply t p) ts) := ih (apply t p) h1 hbox'
      rw [run_cons]
      exact hstep.trans hrec

/-- A predicate on states is closed when every in-box successor of a member is a
member. -/
def ClosedP (cap : Nat) (S : St → Prop) : Prop :=
  ∀ s, S s → ∀ t ∈ allToks, totLen (apply t s) ≤ cap → S (apply t s)

/-- **The principal direction.**  A closed predicate containing `p` contains
every state reachable from `p` inside the box. -/
theorem closed_reach_mem {cap : Nat} {S : St → Prop} (hS : ClosedP cap S) {p : St}
    (hp : S p) {q : St} (h : Reach cap p q) : S q := by
  induction h with
  | refl _ => exact hp
  | step _ t hbox ih => exact hS _ ih t (allToks_complete t) hbox

/-- The component of `p` inside the box is itself a closed set: the minimum data
that a closed-set certificate can carry. -/
theorem reach_closedP {cap : Nat} {p : St} :
    ClosedP cap (fun q => Reach cap p q) := by
  intro s hs t _ hbox
  exact Reach.step hs t hbox

/-- Closedness is *exactly* "is a union of in-box reachable sets", for sets that
lie in the box. -/
theorem closed_iff_reach {cap : Nat} {S : St → Prop} (hbox : ∀ s, S s → totLen s ≤ cap) :
    ClosedP cap S ↔ ∀ p, S p → ∀ q, Reach cap p q → S q := by
  constructor
  · intro hS p hp q h
    exact closed_reach_mem hS hp h
  · intro h s hs t _ hbox'
    exact h s hs (apply t s) (Reach.step (Reach.refl (hbox s hs)) t hbox')

/-- The closed-set certificate format in predicate form: a closed predicate that
contains the start and omits the target excludes every in-box sequence. -/
theorem not_reach_of_closedP {cap : Nat} {S : St → Prop} (hS : ClosedP cap S) {p q : St}
    (hpbox : totLen p ≤ cap) (hp : S p) (hq : ¬ S q) :
    ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧
        run p ts = q := by
  rintro ⟨ts, hbox, hend⟩
  have h := closed_reach_mem hS hp (Reach.of_run p ts hpbox hbox)
  rw [hend] at h
  exact hq h

/-! ## Potential functions -/

/-- A potential that does not increase along in-box moves is bounded above on
the component of `p` by its value at `p`. -/
theorem potential_reach_le {cap : Nat} {φ : St → Nat}
    (hmono : ∀ s t, t ∈ allToks → totLen (apply t s) ≤ cap → φ (apply t s) ≤ φ s)
    {p q : St} (h : Reach cap p q) : φ q ≤ φ p := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | step _ t hbox ih => exact Nat.le_trans (hmono _ t (allToks_complete t) hbox) ih

/-- Hence the sublevel sets of a non-increasing potential are closed sets. -/
theorem potential_closed {cap : Nat} {φ : St → Nat}
    (hmono : ∀ s t, t ∈ allToks → totLen (apply t s) ≤ cap → φ (apply t s) ≤ φ s)
    (k : Nat) : ClosedP cap (fun x => φ x ≤ k) := by
  intro s hs t _ hbox
  exact Nat.le_trans (hmono s t (allToks_complete t) hbox) hs

/-- A non-increasing potential is constant between states that are reachable from
each other inside the box: on a component it is an invariant. -/
theorem potential_eq_of_reach {cap : Nat} {φ : St → Nat}
    (hmono : ∀ s t, t ∈ allToks → totLen (apply t s) ≤ cap → φ (apply t s) ≤ φ s)
    {p q : St} (h1 : Reach cap p q) (h2 : Reach cap q p) : φ p = φ q :=
  Nat.le_antisymm (potential_reach_le hmono h2) (potential_reach_le hmono h1)

end ACComp
