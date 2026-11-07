/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import ACBounds
import Mathlib.Data.Nat.Pairing

/-!
# ACClosed: a verified checker for closed-set certificates over encoded states

Direction K7 (round 8, member m8).  `ACBounds.lean` (round 7) proves the
*logic* of the closed-set certificate format: a finite list `S` of states that
contains the start, is closed under the twelve in-box moves, and avoids the
target certifies that no in-box move sequence of any length reaches the target.
Applying that format to a real row needs the kernel to check closure of `S`,
which is `|S| * 12` move applications plus membership tests.  A naive
`List.Mem` makes the membership part quadratic.

This file supplies the missing engineering, in a form the kernel can run:

* states are encoded as `Nat` (`encS`), injectively (`encS_inj`);
* the set is stored twice: as a `List St` (the data `not_reach_of_closed`
  consumes) and as a balanced binary tree of the encoded keys (`BTree`), whose
  membership test `bmem` is `O(log |S|)` constructor matches;
* `closedCheck cap t S` is a `Bool` that is `true` exactly when every in-box
  successor of every member of `S` has its key found by `bmem`;
* `closedCheck_sound` turns `closedCheck = true`, together with the consistency
  of the tree with the list (`keys t = S.map encS`, itself a `decide`), into the
  closure hypothesis of `ACBounds.not_reach_of_closed`.

Nothing here says anything about the Andrews-Curtis conjecture: every statement
is about *bounded* move sequences inside a fixed box.
-/

set_option maxRecDepth 1000000

namespace ACClosed

open ACBounds

/-! ## Encoding a state as a `Nat` -/

/-- The four letters as the digits `0,1,2,3`. -/
def code (x : Letter) : Nat := 2 * (if x.1 then 1 else 0) + (if x.2 then 1 else 0)

theorem code_le (x : Letter) : code x ≤ 3 := by
  obtain ⟨g, s⟩ := x
  simp only [code]
  cases g <;> cases s <;> simp

/-- Letters are separated by `code`. -/
theorem code_inj : ∀ x y : Letter, code x = code y → x = y := by
  intro x y h
  obtain ⟨g₁, s₁⟩ := x
  obtain ⟨g₂, s₂⟩ := y
  simp only [code] at h
  cases g₁ <;> cases s₁ <;> cases g₂ <;> cases s₂ <;> simp_all

/-- A word as a base-`5` numeral with digits `code + 1 ∈ {1,2,3,4}` and no
leading zero.  The empty word is `0`. -/
def encW : Word → Nat
  | [] => 0
  | x :: xs => 5 * encW xs + (code x + 1)

/-- The top digit of a nonempty word is `code x + 1`. -/
theorem encW_cons_mod (x : Letter) (xs : Word) : encW (x :: xs) % 5 = code x + 1 := by
  have h1 : code x + 1 ≤ 4 := by have := code_le x; omega
  simp only [encW]
  omega

/-- The remaining digits of a nonempty word. -/
theorem encW_cons_div (x : Letter) (xs : Word) : encW (x :: xs) / 5 = encW xs := by
  have h1 : code x + 1 ≤ 4 := by have := code_le x; omega
  simp only [encW]
  omega

/-- The encoding of a word is injective. -/
theorem encW_inj : ∀ u v : Word, encW u = encW v → u = v := by
  intro u
  induction u with
  | nil =>
      intro v h
      cases v with
      | nil => rfl
      | cons y ys =>
          have h2 : 0 < code y + 1 := by omega
          simp only [encW] at h
          omega
  | cons x xs ih =>
      intro v h
      cases v with
      | nil =>
          have h2 : 0 < code x + 1 := by omega
          simp only [encW] at h
          omega
      | cons y ys =>
          have hdx := encW_cons_mod x xs
          have hdy := encW_cons_mod y ys
          rw [h] at hdx
          have hc : code x = code y := by omega
          have hc' : x = y := code_inj x y hc
          have hd : encW xs = encW ys := by
            have hx := encW_cons_div x xs
            have hy := encW_cons_div y ys
            rw [h] at hx
            omega
          rw [hc', ih ys hd]

/-- A state as one `Nat`: the two relator codes paired. -/
def encS (p : St) : Nat := Nat.pair (encW p.1) (encW p.2)

/-- The state encoding is injective. -/
theorem encS_inj {p q : St} (h : encS p = encS q) : p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  have h' : encW a = encW c ∧ encW b = encW d := Nat.pair_eq_pair.mp h
  obtain ⟨h1, h2⟩ := h'
  rw [encW_inj a c h1, encW_inj b d h2]

/-! ## A balanced binary tree of keys -/

/-- A binary tree of `Nat` keys. -/
inductive BTree : Type where
  | leaf : BTree
  | node : BTree → Nat → BTree → BTree
  deriving Repr

/-- Membership in a tree of keys: `O(log |S|)` constructor matches when the
tree is balanced, and `true` only ever means membership (no ordering
hypothesis is needed for soundness). -/
def bmem (k : Nat) : BTree → Bool
  | .leaf => false
  | .node l v r => if k = v then true else if k < v then bmem k l else bmem k r

/-- The keys of a tree, in inorder. -/
def keys : BTree → List Nat
  | .leaf => []
  | .node l v r => keys l ++ v :: keys r

theorem bmem_sound : ∀ (t : BTree) (k : Nat), bmem k t = true → k ∈ keys t := by
  intro t
  induction t with
  | leaf =>
      intro k h
      simp [bmem] at h
  | node l v r ihl ihr =>
      intro k h
      simp only [bmem] at h
      simp only [keys]
      by_cases h1 : k = v
      · subst h1
        simp
      · by_cases h2 : k < v
        · rw [if_neg h1, if_pos h2] at h
          have := ihl k h
          simp only [List.mem_append]
          exact Or.inl this
        · rw [if_neg h1, if_neg h2] at h
          have := ihr k h
          simp only [List.mem_append]
          exact Or.inr (by simp [this])

/-! ## The closure check -/

/-- Every in-box successor of every member of `S` has its key in `t`. -/
def closedCheck (cap : Nat) (t : BTree) (S : List St) : Bool :=
  S.all (fun s => (stepBox cap s).all (fun q => bmem (encS q) t))

/-- **Soundness of the Boolean check.**  If the tree is consistent with the list
and the check passes, then `S` is closed under the in-box moves. -/
theorem closedCheck_sound {cap : Nat} {t : BTree} {S : List St}
    (hkeys : keys t = S.map encS) (hchk : closedCheck cap t S = true)
    {s : St} (hs : s ∈ S) {tok : Tok} (htok : tok ∈ allToks)
    (hbox : totLen (apply tok s) ≤ cap) : apply tok s ∈ S := by
  have h1 : (stepBox cap s).all (fun q => bmem (encS q) t) = true := by
    have := List.all_eq_true.mp hchk s hs
    simpa only [closedCheck] using this
  have h2 : bmem (encS (apply tok s)) t = true := List.all_eq_true.mp h1 _ (mem_stepBox.mpr ⟨tok, htok, rfl, hbox⟩)
  have h3 : encS (apply tok s) ∈ keys t := bmem_sound t _ h2
  rw [hkeys, List.mem_map] at h3
  obtain ⟨s', hs', he⟩ := h3
  have : s' = apply tok s := encS_inj he
  rwa [this] at hs'

/-- **The certificate format, in checker form.**  A list `S` of states, a tree
`t` of their keys, the check `closedCheck`, and the two endpoint facts give the
depth-unbounded negative statement of `ACBounds.not_reach_of_closed`. -/
theorem not_reach_of_tree {cap : Nat} {p q : St} {S : List St} {t : BTree}
    (hkeys : keys t = S.map encS) (hchk : closedCheck cap t S = true)
    (hp : p ∈ S) (hq : q ∉ S) :
    ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧
        run p ts = q := by
  refine ACBounds.not_reach_of_closed hp ?_ hq
  intro s hs tok htok hbox
  exact closedCheck_sound hkeys hchk hs htok hbox


/-! ## Chunking: assembling a closure check from pieces

The kernel's cost for one `decide` grows with the size of the term it reduces, so
a large closed set is checked in chunks: each chunk gets its own `decide`, and the
chunk facts are assembled here.  This keeps the peak memory proportional to the
chunk size rather than to the size of the set. -/

/-- The closure check splits over concatenation. -/
theorem closedCheck_append {cap : Nat} {t : BTree} {l₁ l₂ : List St}
    (h1 : closedCheck cap t l₁ = true) (h2 : closedCheck cap t l₂ = true) :
    closedCheck cap t (l₁ ++ l₂) = true := by
  have h1' : (l₁.all (fun s => (stepBox cap s).all (fun q => bmem (encS q) t))) = true := h1
  have h2' : (l₂.all (fun s => (stepBox cap s).all (fun q => bmem (encS q) t))) = true := h2
  show (l₁ ++ l₂).all (fun s => (stepBox cap s).all (fun q => bmem (encS q) t)) = true
  rw [List.all_append, h1', h2']
  rfl

/-- The closure check of a flattened list of chunks, from the chunk checks. -/
theorem closedCheck_flatten {cap : Nat} {t : BTree} :
    ∀ cs : List (List St), (cs.map (fun c => closedCheck cap t c)).all id = true →
      closedCheck cap t cs.flatten = true
  | [], _ => rfl
  | c :: cs, h => by
      have h1 : closedCheck cap t c = true := by
        have hh := h
        simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true] at hh
        exact hh.1
      have h2 : (cs.map (fun c => closedCheck cap t c)).all id = true := by
        have hh := h
        simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true] at hh
        exact hh.2
      rw [List.flatten_cons]
      exact closedCheck_append h1 (closedCheck_flatten cs h2)

end ACClosed
