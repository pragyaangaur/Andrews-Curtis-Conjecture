/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/

import ACKeys

/-!
# ACTree: a closed-set certificate whose data is the lookup tree alone

At 136,576 states the elaborator cannot hold two copies of the certificate data
(the tree and the list).  This file makes the *tree* the only data: the closed
set is recovered from it as `Sset t = (keys t).map Nat.unpair`, the chunks used
for the chunked closure check are recovered by `cutAt d t`, and the two
consistency facts that `ACKeys` needs are

* `keys_eq_map`: `keys t = (Sset t).map (fun p => Nat.pair p.1 p.2)`, a general
  theorem (`Nat.pair_unpair`) rather than a computation on the data;
* `keyOK`: every key of the tree is the code of the state it decodes to, a
  one-pass check over the keys.

Nothing here says anything about the Andrews-Curtis conjecture: every statement
is about bounded move sequences inside a fixed box.
-/

set_option maxRecDepth 1000000

namespace ACTree

open ACBounds ACClosed ACKeys

/-! ## Cutting a tree into chunks -/

/-- The subtrees at depth `d`, with the nodes on the cut turned into leaves. -/
def cutAt : Nat → BTree → List BTree
  | 0, t => [t]
  | _ + 1, BTree.leaf => []
  | d + 1, BTree.node l v r =>
      cutAt d l ++ [BTree.node BTree.leaf v BTree.leaf] ++ cutAt d r

theorem flatten_map_append (a b : List (List Nat)) :
    (a ++ b).flatten = a.flatten ++ b.flatten := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [List.flatten_cons, ih]

/-- The inorder of the whole tree is the concatenation of the inorders of the
chunks. -/
theorem keys_cutAt : ∀ (d : Nat) (t : BTree), ((cutAt d t).map keys).flatten = keys t := by
  intro d
  induction d with
  | zero => intro t; simp [cutAt]
  | succ d ih =>
      intro t
      cases t with
      | leaf => rfl
      | node l v r =>
          simp only [cutAt, List.map_append, List.map_cons, List.map_nil,
            flatten_map_append, List.flatten_cons, List.flatten_nil, List.nil_append,
            keys, ih l, ih r, List.append_nil]
          rw [List.append_assoc]
          rfl

/-- The map of a flattened list. -/
theorem map_flatten' {α β : Type} (f : α → β) :
    ∀ (l : List (List α)), (l.flatten).map f = (l.map (List.map f)).flatten
  | [] => rfl
  | a :: as => by
      simp only [List.flatten_cons, List.map_append, List.map_cons, map_flatten' f as]

/-! ## The set derived from the tree -/

/-- The closed set carried by a tree: its keys, unpaired. -/
def Sset (t : BTree) : List (Nat × Nat) := (keys t).map Nat.unpair

/-- The chunks of the derived set, cut at depth `d`. -/
def chunk (d : Nat) (t : BTree) : List (List (Nat × Nat)) :=
  (cutAt d t).map (fun sub => (keys sub).map Nat.unpair)

/-- The tree's keys are the codes of the derived set: a general theorem, not a
computation on the data. -/
theorem keys_eq_map (t : BTree) : keys t = (Sset t).map (fun p => Nat.pair p.1 p.2) := by
  simp only [Sset, List.map_map]
  rw [show ((fun p : Nat × Nat => Nat.pair p.1 p.2) ∘ Nat.unpair) = id from
    funext (fun k => Nat.pair_unpair k)]
  exact (List.map_id (keys t)).symm

theorem Sset_eq_flatten (d : Nat) (t : BTree) : Sset t = (chunk d t).flatten := by
  simp only [Sset, chunk]
  rw [← keys_cutAt d t, map_flatten', List.map_map]
  rfl

/-- The closure check of the derived set, from the chunk checks. -/
theorem closed_of_chunks {cap d : Nat} {t : BTree}
    (h : ((chunk d t).map (fun c => closedCheckK cap t c)).all id = true) :
    closedCheckK cap t (Sset t) = true := by
  rw [Sset_eq_flatten d t]
  exact closedCheckK_flatten _ h

/-! ## The two consistency facts -/

/-- The code of the state a key decodes to. -/
def encU (k : Nat) : Nat := encS (decP (Nat.unpair k))

/-- Every key of the tree is the code of the state it decodes to. -/
def keyOK (t : BTree) : Bool := (keys t).all (fun k => decide (encU k = k))

theorem keyOK_spec {t : BTree} (h : keyOK t = true) {k : Nat} (hk : k ∈ keys t) :
    encS (decP (Nat.unpair k)) = k := by
  have h1 := List.all_eq_true.mp h k hk
  exact of_decide_eq_true h1

/-- The row is in the derived set, from one lookup. -/
theorem mem_of_bmem {t : BTree} {p : St} (h1 : p.1.length ≤ 32) (h2 : p.2.length ≤ 32)
    (h : bmem (encS p) t = true) : p ∈ (Sset t).map decP := by
  have hk : encS p ∈ keys t := bmem_sound t _ h
  rw [keys_eq_map, List.mem_map] at hk
  obtain ⟨r, hr, he⟩ := hk
  rw [List.mem_map]
  exact ⟨r, hr, decP_eq he h1 h2⟩

/-- The target is absent from the derived set. -/
theorem notMem_of_all {t : BTree} {q : St} (hkey : keyOK t = true)
    (h : (keys t).all (fun k => !(decide (k = encS q))) = true) :
    q ∉ (Sset t).map decP := by
  intro hq
  rw [List.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  simp only [Sset, List.mem_map] at hr
  obtain ⟨k, hk, rfl⟩ := hr
  have h1 : encS (decP (Nat.unpair k)) = k := keyOK_spec hkey hk
  have h2 := List.all_eq_true.mp h k hk
  rw [h1] at h2
  simp at h2

/-- **The certificate format with the tree as the only data.** -/
theorem not_reach_of_treeD {cap : Nat} {t : BTree} {p q : St}
    (hcap : cap ≤ 31) (hkey : keyOK t = true)
    (hnq : (keys t).all (fun k => !(decide (k = encS q))) = true)
    (hchk : closedCheckK cap t (Sset t) = true)
    (hp1 : p.1.length ≤ 32) (hp2 : p.2.length ≤ 32)
    (hp : bmem (encS p) t = true) :
    ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run p (ts.take i)) ≤ cap) ∧
        run p ts = q :=
  ACKeys.not_reach_of_treeK hcap (keys_eq_map t) hchk
    (mem_of_bmem hp1 hp2 hp) (notMem_of_all hkey hnq)

end ACTree
