/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import ACKeys

/-!
# ACPack: closed-set certificates whose data is a packed numeral, tree built at check time

Round 8 (`ACClosed`, `ACKeys`, `ACTree`, member m8) turned the closed-set format of
`ACBounds.not_reach_of_closed` into a check the kernel can run at scale, and measured
the wall: the cap-17 component of the class-C rows has 136,576 states, and putting that
many *literally listed* states into the environment costs 6-7.5 GB (about 45 KB of
elaborator state per listed state), which does not fit alongside the lookup tree.

This file removes the listing.  The certificate data is a list of **packed numerals**:
each chunk is one `Nat` holding a run of 40-bit fields (one field = one relator code of
`ACClosed.encW`), so the whole 136,576-state set is ~10^6 bits of literal data instead of
136,576 list elements.  The kernel

* decodes the chunks (`decChunks`, `decF`) — arithmetic on `Nat`, which the kernel
  evaluates natively;
* builds the lookup tree from the decoded keys by folding an unbalanced binary search
  insert over the key list in **median-first order** (`ins`, `bld`), which produces a
  balanced tree without needing a `take`/`drop` recursion (those do not reduce in the
  kernel unless they are structural, the trap already recorded for `decW`);
* runs the closure check of `ACKeys.closedCheckK` against the built tree.

The only fact about the built tree that soundness needs is *no false positives*:
`bmem_bld`, that a successful lookup at a key built from the data implies the key is one
of the data's keys.  No ordering hypothesis is used — `bmem_sound` needs none — so a
badly shaped tree can only make the check fail, never pass wrongly.

Nothing here says anything for or against the Andrews-Curtis conjecture: every statement
is about move sequences whose intermediate states stay inside a fixed length box.
-/

set_option maxRecDepth 1000000

namespace ACPack

open ACBounds ACClosed ACKeys

/-! ## The packed data -/

/-- The field width of the packing: one relator code occupies a 40-bit field.  Every
relator occurring in a box of cap at most 31 has code below `5^31 < 2^72`, so the
decoder uses 40-bit fields only for boxes of cap at most 17, which is all this file
instantiates; the bound appears as the hypothesis `cap ≤ 17` of the final theorem. -/
def FB : Nat := 2 ^ 40

/-- Decode `f` fields of 40 bits from a packed numeral, low field first. -/
def decF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => n % FB :: decF f (n / FB)

/-- Pair up a flat list of fields into states. -/
def pairUp : List Nat → List (Nat × Nat)
  | a :: b :: t => (a, b) :: pairUp t
  | _ => []

/-- One chunk: `f` fields, i.e. `f / 2` states. -/
def decChunk (f n : Nat) : List (Nat × Nat) := pairUp (decF f n)

/-- The whole packed certificate. -/
def decChunks (f : Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | c :: cs => decChunk f c ++ decChunks f cs

/-- The key of a state given by its two relator codes: exactly `ACClosed.encS` of the
decoded state. -/
def keyOf (p : Nat × Nat) : Nat := Nat.pair p.1 p.2

/-! ## Building the tree from the keys

`ins` is the ordinary unbalanced binary search insert; `bld` folds it over the key list
in median-first order.  Median-first insertion produces the perfectly balanced tree of
the sorted key list, but nothing below needs the balance: it is what makes the kernel
fast, not what makes the check correct. -/

/-- Binary search insert. -/
def ins (k : Nat) : BTree → BTree
  | .leaf => .node .leaf k .leaf
  | .node l v r =>
      if k < v then .node (ins k l) v r
      else if v < k then .node l v (ins k r)
      else .node l v r

/-- The lookup tree of a key list, built by folding `ins` over it. -/
def bld (l : List Nat) : BTree := l.foldl (fun t k => ins k t) .leaf

/-- One unfold of `bmem` at a node. -/
theorem bmem_node (k v : Nat) (l r : BTree) :
    bmem k (BTree.node l v r) = if k = v then true else if k < v then bmem k l else bmem k r :=
  rfl

/-- **No false positives for one insertion.** -/
theorem bmem_ins : ∀ (t : BTree) (k a : Nat),
    bmem k (ins a t) = true → k = a ∨ bmem k t = true := by
  intro t
  induction t with
  | leaf =>
      intro k a h
      refine Or.inl ?_
      rw [ins, bmem_node] at h
      by_cases h1 : k = a
      · exact h1
      · rw [if_neg h1] at h
        by_cases h2 : k < a
        · rw [if_pos h2] at h
          simp [bmem] at h
        · rw [if_neg h2] at h
          simp [bmem] at h
  | node l v r ihl ihr =>
      intro k a h
      by_cases h1 : a < v
      · have h2 : bmem k (BTree.node (ins a l) v r) = true := by
          rw [ins] at h; rw [if_pos h1] at h; exact h
        rw [bmem_node] at h2
        by_cases h3 : k = v
        · refine Or.inr ?_
          rw [bmem_node k v l r, if_pos h3]
        · rw [if_neg h3] at h2
          by_cases h4 : k < v
          · rw [if_pos h4] at h2
            rcases ihl k a h2 with h5 | h5
            · exact Or.inl h5
            · refine Or.inr ?_
              rw [bmem_node, if_neg h3, if_pos h4]
              exact h5
          · rw [if_neg h4] at h2
            refine Or.inr ?_
            rw [bmem_node, if_neg h3, if_neg h4]
            exact h2
      · by_cases h1' : v < a
        · have h2 : bmem k (BTree.node l v (ins a r)) = true := by
            rw [ins] at h; rw [if_neg h1] at h; rw [if_pos h1'] at h; exact h
          rw [bmem_node] at h2
          by_cases h3 : k = v
          · refine Or.inr ?_
            rw [bmem_node k v l r, if_pos h3]
          · rw [if_neg h3] at h2
            by_cases h4 : k < v
            · rw [if_pos h4] at h2
              refine Or.inr ?_
              rw [bmem_node, if_neg h3, if_pos h4]
              exact h2
            · rw [if_neg h4] at h2
              rcases ihr k a h2 with h5 | h5
              · exact Or.inl h5
              · refine Or.inr ?_
                rw [bmem_node, if_neg h3, if_neg h4]
                exact h5
        · have h2 : bmem k (BTree.node l v r) = true := by
            rw [ins] at h; rw [if_neg h1] at h; rw [if_neg h1'] at h; exact h
          exact Or.inr h2

/-- **No false positives for the fold.** -/
theorem bmem_foldl : ∀ (l : List Nat) (acc : BTree) (k : Nat),
    bmem k (l.foldl (fun t j => ins j t) acc) = true → k ∈ l ∨ bmem k acc = true := by
  intro l
  induction l with
  | nil =>
      intro acc k h
      exact Or.inr (by simpa using h)
  | cons a as ih =>
      intro acc k h
      have h' : bmem k (as.foldl (fun t j => ins j t) (ins a acc)) = true := by
        simpa [List.foldl_cons] using h
      rcases ih (ins a acc) k h' with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem a h1)
      · rcases bmem_ins acc k a h1 with h2 | h2
        · exact Or.inl (by simp [h2])
        · exact Or.inr h2

/-- **No false positives for the built tree**: a successful lookup implies the key was
in the data.  This is the only property of the construction that soundness uses. -/
theorem bmem_bld (l : List Nat) (k : Nat) (h : bmem k (bld l) = true) : k ∈ l := by
  have h' := bmem_foldl l BTree.leaf k h
  rcases h' with h1 | h1
  · exact h1
  · simp [bmem] at h1

/-! ## The check -/

/-- Every in-box successor of every decoded member of the certificate has its key found
by the built tree. -/
def packCheck (cap : Nat) (t : BTree) (S : List (Nat × Nat)) : Bool :=
  S.all (fun p => (stepBox cap (decP p)).all (fun q => bmem (encS q) t))

/-- **Soundness of the packed check.**  This is `ACKeys.closedCheckK_sound` with the
equality `keys t = S.map keyOf` weakened to "no false positives", which is what a tree
built from the data at check time can supply. -/
theorem packCheck_sound {cap : Nat} {t : BTree} {S : List (Nat × Nat)}
    (hcap : cap ≤ 17)
    (hsub : ∀ k, bmem k t = true → k ∈ S.map keyOf)
    (hchk : packCheck cap t S = true) :
    ∀ s ∈ S.map decP, ∀ tok ∈ allToks, totLen (apply tok s) ≤ cap →
      apply tok s ∈ S.map decP := by
  intro s hs tok htok hbox
  rw [List.mem_map] at hs
  obtain ⟨p, hp, rfl⟩ := hs
  have h1 : (stepBox cap (decP p)).all (fun q => bmem (encS q) t) = true := by
    have h := List.all_eq_true.mp hchk p hp
    simpa only [packCheck] using h
  have h2 : bmem (encS (apply tok (decP p))) t = true :=
    List.all_eq_true.mp h1 _ (mem_stepBox.mpr ⟨tok, htok, rfl, hbox⟩)
  have h3 : encS (apply tok (decP p)) ∈ S.map keyOf := hsub _ h2
  rw [List.mem_map] at h3
  obtain ⟨p', hp', he⟩ := h3
  have hlen : (apply tok (decP p)).1.length ≤ 32 ∧ (apply tok (decP p)).2.length ≤ 32 := by
    have hb := hbox
    simp only [totLen] at hb
    constructor <;> omega
  rw [List.mem_map]
  refine ⟨p', hp', ?_⟩
  exact ACKeys.decP_eq (show Nat.pair p'.1 p'.2 = encS (apply tok (decP p)) from he)
    hlen.1 hlen.2

/-! ## Chunking the check

The kernel's peak memory for one `decide` is set by what that reduction holds at
once, not by the certificate: the data has to be decoded, the lookup tree built,
and every successor of every listed state visited.  Splitting the packed data into
groups and checking each group in its own `decide` keeps the peak at one group,
as in `ACClosed.closedCheck_flatten`; the two lemmas here assemble the group
checks into the check of the whole certificate. -/

theorem decChunks_append (f : Nat) : ∀ (a b : List Nat),
    decChunks f (a ++ b) = decChunks f a ++ decChunks f b
  | [], b => rfl
  | c :: cs, b => by
      simp only [List.cons_append, decChunks, decChunks_append f cs b, List.append_assoc]

/-- The closure check splits over the packed chunk groups. -/
theorem packCheck_append (cap : Nat) (t : BTree) (a b : List Nat) :
    packCheck cap t (decChunks f a ++ decChunks f b) =
      (packCheck cap t (decChunks f a) && packCheck cap t (decChunks f b)) := by
  simp only [packCheck, List.all_append]

/-- The closure check over a group of packed chunks. -/
def packCheckC (cap f : Nat) (t : BTree) (cs : List Nat) : Bool :=
  packCheck cap t (decChunks f cs)

/-- Group checks assemble: the check of `a ++ b` is the conjunction. -/
theorem packCheckC_append (cap f : Nat) (t : BTree) (a b : List Nat) :
    packCheckC cap f t (a ++ b) =
      (packCheckC cap f t a && packCheckC cap f t b) := by
  simp only [packCheckC, decChunks_append, packCheck_append]

/-- Group checks assemble over a list of groups, as in `ACClosed.closedCheck_flatten`. -/
theorem packCheckC_flatten (cap f : Nat) (t : BTree) :
    ∀ gs : List (List Nat),
      (gs.map (fun g => packCheckC cap f t g)).all id = true →
      packCheckC cap f t gs.flatten = true
  | [], _ => rfl
  | g :: gs, h => by
      have hh := h
      simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true] at hh
      rw [List.flatten_cons, packCheckC_append, hh.1]
      have h2 : (gs.map (fun g => packCheckC cap f t g)).all id = true := hh.2
      rw [packCheckC_flatten cap f t gs h2]
      rfl

/-! ## The whole certificate, in one reduction -/

/-- The certificate as the kernel sees it: decode the packed chunks, build the tree from
the decoded keys, check the two endpoints and the closure.  All of it is one `Bool`,
so one `decide` performs the whole verification. -/
def runPackS (cap : Nat) (S : List (Nat × Nat)) (p q : St) : Bool :=
  (S.any (fun r => decP r == p)) &&
  (S.all (fun r => !(decP r == q))) &&
  packCheck cap (bld (S.map keyOf)) S

/-- The certificate with the packed data in place. -/
def runPack (cap f : Nat) (cs : List Nat) (p q : St) : Bool :=
  runPackS cap (decChunks f cs) p q

/-- **The certificate format over packed data.**  If `runPack` returns `true`, then no
in-box move sequence of any length takes `p` to `q`. -/
theorem not_reach_of_facts {cap : Nat} {S : List (Nat × Nat)} {p q : St} (hcap : cap ≤ 17)
    (hany : S.any (fun r => decP r == p) = true)
    (hall : S.all (fun r => !(decP r == q)) = true)
    (hchk : packCheck cap (bld (S.map keyOf)) S = true) :
    ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧
        run p ts = q := by
  refine ACBounds.not_reach_of_closed (S := S.map decP) ?_ ?_ ?_
  · rw [List.any_eq_true] at hany
    obtain ⟨r, hr, he⟩ := hany
    have he' : decP r = p := beq_iff_eq.mp he
    rw [List.mem_map]
    exact ⟨r, hr, he'⟩
  · intro s hs tok htok hbox
    exact packCheck_sound hcap (fun k hk => bmem_bld (S.map keyOf) k hk) hchk s hs tok htok hbox
  · intro hq
    rw [List.mem_map] at hq
    obtain ⟨r, hr, he⟩ := hq
    have h1 := List.all_eq_true.mp hall r hr
    have h2 : decP r = q := he
    rw [h2] at h1
    simp at h1

theorem runPackS_sound {cap : Nat} {S : List (Nat × Nat)} {p q : St} (hcap : cap ≤ 17)
    (h : runPackS cap S p q = true) :
    ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧
        run p ts = q := by
  rw [runPackS, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hany, hall⟩, hchk⟩ := h
  exact not_reach_of_facts hcap hany hall hchk

/-- **The certificate format over packed data.**  If `runPack` returns `true`, then no
in-box move sequence of any length takes `p` to `q`. -/
theorem runPack_sound {cap f : Nat} {cs : List Nat} {p q : St} (hcap : cap ≤ 17)
    (h : runPack cap f cs p q = true) :
    ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧
        run p ts = q :=
  runPackS_sound hcap h

end ACPack
