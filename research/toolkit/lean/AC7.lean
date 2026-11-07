/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-!
# Andrews-Curtis moves, part 7: Metzler's pair and the family of 14 in the kernel

Round 6 (`directions/qdouble-star/m9/round6-m6.md`) found an explicit certificate of **44 Q\*\*-moves**

  `<x,y | x^5, y^5, [x,y]>  ->  <x,y | x^5, y^5, [x^2,y]>`,

replaying Barmak's quotation of Metzler's 1976 example (Barmak, Algebr. Geom. Topol. 25 (2025)
345-355, Section 1), together with 14 instances of a one-parameter family
`<x,y | x^k, y^m, [x,y]> ~ <x,y | x^k, y^m, [x^j,y]>` for odd `k >= 3`, `m >= 1`, `t | k-1`,
`j = (k-1)/t`.  Round 6's verification was five Python replayers and GAP.  This file puts both into
the Lean 4 kernel.

## Contents

* (i) the Q\*\* machinery of `toolkit/lean/AC5.lean`, copied mechanically (line range recorded in
  `gen_ac7.py`), with the namespace renamed `AC7`: `QPres`, `QMove`, `QMove.apply`, `replay`,
  `checkCert`, `checkCert_append`, and the self-tests;
* (ii) the 15 certificates, each replayed by `decide` in blocks of at most two moves and glued with
  `checkCert_append`, so the 44-move Metzler certificate and the 14 family certificates of 44 to 64
  moves are kernel-checked;
* (iii) the algebra that round 6 wrote as Lemmas 1 to 3, now kernel theorems for **all**
  parameters, not only the 14 instances:
  * `conjProd` — the inductive predicate "is a finite product of conjugates of `R` and `R⁻¹`", the
    exact form a Q-multiplication by conjugates of a relator needs;
  * `conjProd_conj`, `conjProd_mul`, `conjProd_inv` — the closure of that predicate that the
    telescoping induction uses;
  * `lemma3` — for every group homomorphism `σ` with `σ x = W⁻¹` and `R = x * W`, the element
    `V * (σ V)⁻¹` is a product of conjugates of `R` for **every** word `V` (round 6's Lemma 3);
  * `powerProd` and `powerProd_spec`, `powerProd_cert` — the closed form of stage 2 of the
    certificate: the product of `j` conjugates of the defining relator `a x⁻ᵗ` is `x⁻ᵗʲ aʲ`, and
    `x^(1+tj)` times it is `x a^j`, for all `t j` (round 6's "the product never has to be found by
    a search");
  * `family_algebra` — the substitution `x ↦ a⁻ʲ` carries `a x⁻ᵗ` to `a^(1+tj)` and `[x,y]` to
    `[a⁻ʲ,y]`, so the endpoint of the recipe is the stated one.

Nothing in this file proves or disproves the Andrews-Curtis conjecture.  Both presentations of
Metzler's pair present the abelian group `Z/5 x Z/5`, not the trivial group; the content is the
coarseness of the Q\*\*-move calculus.  The general recipe for the family is kernel-checked as
algebra (iii) and as 14 explicit move lists; the statement "for every `k, t, m` the recipe's move
list replays" is *not* formalized as one theorem over symbolic parameters, because `replay` needs
the concrete letter lists.  That gap is stated in the report as well.
-/

namespace AC7

/-- A word in the free group on `n` generators. -/
abbrev Word (n : Nat) : Type := FreeGroup (Fin n)

/-- A presentation: rank `n`, `m` relators, and the relators themselves.  The Q\*\*-move set does
not preserve balance, and the certificates of `directions/qdouble-star/m9/certs/` are unbalanced
(rank two with one relator, raised to rank three with two relators by the prolongation), so `m` is
kept separate from `n`.  Every Q\*\*-move keeps `n - m` fixed. -/
structure QPres where
  /-- the number of generators -/
  n : Nat
  /-- the number of relators -/
  m : Nat
  /-- the relators -/
  rels : Fin m → Word n

instance : DecidableEq QPres := fun P Q => by
  rcases P with ⟨n, m, r⟩
  rcases Q with ⟨n', m', s⟩
  by_cases h : n = n'
  · subst h
    by_cases h2 : m = m'
    · subst h2
      by_cases h3 : r = s
      · exact isTrue (by rw [h3])
      · exact isFalse (by intro h4; exact h3 (by injection h4))
    · exact isFalse (by intro h4; exact h2 (by injection h4))
  · exact isFalse (by intro h4; exact h (by injection h4))

/-! ## Letter lists, index arithmetic, and the two rank-changing moves -/

/-- The letters of a recorded word, as `(generator index, sign)` pairs, mapped into `Fin n`.
Following `directions/qdouble-star/m9/certs/`, generators are numbered from zero, `true` is the
generator and `false` its inverse.  `none` if a letter is out of range. -/
def mapLetters (n : Nat) : List (Nat × Bool) → Option (List (Fin n × Bool))
  | [] => some []
  | (a, b) :: t =>
    match (if h : a < n then some (⟨a, h⟩, b) else none), mapLetters n t with
    | some x, some l => some (x :: l)
    | _, _ => none

/-- A word of the free group from a recorded letter list, if every letter is in range. -/
def mkWordOpt (n : Nat) (l : List (Nat × Bool)) : Option (Word n) :=
  (mapLetters n l).map FreeGroup.mk

/-- The index in `Fin n` of the `k`-th generator that survives the deletion of `j`: the increasing
bijection `Fin (n-1) → Fin n` whose range is the complement of `{j}`. -/
def skipEmb {n : Nat} (j : Fin n) (k : Fin (n - 1)) : Fin n :=
  if h : k.val < j.val then ⟨k.val, by have hj := j.isLt; omega⟩
  else ⟨k.val + 1, by have hk := k.isLt; have hj := j.isLt; omega⟩

/-- The position of the generator `k` among the survivors of the deletion of `i`; the hypothesis
`k ≠ i` is what makes the value well defined. -/
def skipIndex {n : Nat} (i : Fin n) (k : Fin n) (hk : k ≠ i) : Fin (n - 1) :=
  if h : k.val < i.val then ⟨k.val, by have hi := i.isLt; omega⟩
  else ⟨k.val - 1, by
    have hkk := k.isLt
    have hik : i.val < k.val := by
      rcases Nat.lt_or_ge k.val i.val with hlt | hge
      · exact absurd hlt h
      · rcases Nat.lt_or_eq_of_le hge with hlt | heq
        · exact hlt
        · exact absurd (Fin.ext heq.symm) hk
    omega⟩

/-- Replace the `i`-th relator by `v`. -/
def setRel (P : QPres) (i : Fin P.m) (v : Word P.n) : QPres :=
  ⟨P.n, P.m, fun k => if k = i then v else P.rels k⟩

/-- Apply a letter substitution to every relator.  This is move (iv) for the Nielsen moves. -/
def substRel (P : QPres) (σ : Fin P.n → Word P.n) : QPres :=
  ⟨P.n, P.m, fun k => FreeGroup.lift σ (P.rels k)⟩

/-! ## The Q\*\*-moves -/

/-- One recorded Q\*\*-move.  Indices are zero-based and letter lists are as in the certificate
files of `directions/qdouble-star/m9/certs/`.  Move (vi) carries the conjugating word, which the
converter `gen_ac5.py` reads off the state by cyclic reduction; the checker of the round-4
certificates `directions/qdouble-star/m9/qverify.py` computes the same word, so the information
content of the two formats is the same. -/
inductive QMove where
  /-- (ii) invert a relator -/
  | inv (i : Nat)
  /-- (i) multiply a relator by another on the right, `r_i ↦ r_i r_j` -/
  | mul (i j : Nat)
  /-- (iii) conjugate a relator, `r_i ↦ w r_i w⁻¹` -/
  | conj (i : Nat) (w : List (Nat × Bool))
  /-- (iii) then (i): left multiplication, `r_i ↦ r_j r_i` -/
  | lmul (i j : Nat)
  /-- (iv) `x_i ↦ x_i⁻¹` -/
  | neg (i : Nat)
  /-- (iv) `x_i ↦ x_i x_j` -/
  | nij (i j : Nat)
  /-- (iv) `x_i ↦ x_j x_i` -/
  | nji (i j : Nat)
  /-- (iv) `x_i ↦ x_i x_j⁻¹` -/
  | nijinv (i j : Nat)
  /-- (iv) `x_i ↦ x_j⁻¹ x_i` -/
  | njiinv (i j : Nat)
  /-- (iv) exchange two generators -/
  | swap (i j : Nat)
  /-- (v) adjoin a new generator together with the relator equal to it -/
  | prolong
  /-- (vi) delete the generator `i`, whose relator sits at position `j` and is a conjugate
  `w x_i w⁻¹` -/
  | delete (i j : Nat) (w : List (Nat × Bool))

/-- Apply one recorded move; `none` when the move does not apply to the state.  Every guard is
checked: indices in range, distinct relators for multiplication, letters in range for
conjugation, and for deletion the conjugacy of the deleted relator to the deleted generator. -/
def QMove.apply (m : QMove) (P : QPres) : Option QPres :=
  match m with
  | .inv i =>
    if h : i < P.m then some (setRel P ⟨i, h⟩ (P.rels ⟨i, h⟩)⁻¹) else none
  | .mul i j =>
    if hi : i < P.m then if hj : j < P.m then
      if _hij : i ≠ j then
        some (setRel P ⟨i, hi⟩ (P.rels ⟨i, hi⟩ * P.rels ⟨j, hj⟩)) else none
      else none else none
  | .conj i w =>
    if h : i < P.m then
      match mkWordOpt P.n w with
      | none => none
      | some wk => some (setRel P ⟨i, h⟩ (wk * P.rels ⟨i, h⟩ * wk⁻¹))
    else none
  | .lmul i j =>
    if hi : i < P.m then if hj : j < P.m then
      if _hij : i ≠ j then
        some (setRel P ⟨i, hi⟩ (P.rels ⟨j, hj⟩ * P.rels ⟨i, hi⟩)) else none
      else none else none
  | .neg i =>
    if h : i < P.n then
      let I : Fin P.n := ⟨i, h⟩
      some (substRel P (fun k => if k = I then (FreeGroup.of k)⁻¹ else FreeGroup.of k))
    else none
  | .nij i j =>
    if hi : i < P.n then if hj : j < P.n then
      let I : Fin P.n := ⟨i, hi⟩
      let J : Fin P.n := ⟨j, hj⟩
      some (substRel P (fun k => if k = I then FreeGroup.of k * FreeGroup.of J else FreeGroup.of k))
      else none else none
  | .nji i j =>
    if hi : i < P.n then if hj : j < P.n then
      let I : Fin P.n := ⟨i, hi⟩
      let J : Fin P.n := ⟨j, hj⟩
      some (substRel P (fun k => if k = I then FreeGroup.of J * FreeGroup.of k else FreeGroup.of k))
      else none else none
  | .nijinv i j =>
    if hi : i < P.n then if hj : j < P.n then
      let I : Fin P.n := ⟨i, hi⟩
      let J : Fin P.n := ⟨j, hj⟩
      some (substRel P (fun k => if k = I then FreeGroup.of k * (FreeGroup.of J)⁻¹ else FreeGroup.of k))
      else none else none
  | .njiinv i j =>
    if hi : i < P.n then if hj : j < P.n then
      let I : Fin P.n := ⟨i, hi⟩
      let J : Fin P.n := ⟨j, hj⟩
      some (substRel P (fun k => if k = I then (FreeGroup.of J)⁻¹ * FreeGroup.of k else FreeGroup.of k))
      else none else none
  | .swap i j =>
    if hi : i < P.n then if hj : j < P.n then
      let I : Fin P.n := ⟨i, hi⟩
      let J : Fin P.n := ⟨j, hj⟩
      some (substRel P (fun k => if k = I then FreeGroup.of J else if k = J then FreeGroup.of I else FreeGroup.of k))
      else none else none
  | .prolong =>
    some ⟨P.n + 1, P.m + 1, fun k =>
      Fin.lastCases (FreeGroup.of (Fin.last P.n)) (fun t => FreeGroup.map Fin.castSucc (P.rels t)) k⟩
  | .delete i j w =>
    if hi : i < P.n then if hj : j < P.m then
      let I : Fin P.n := ⟨i, hi⟩
      let J : Fin P.m := ⟨j, hj⟩
      match mkWordOpt P.n w with
      | none => none
      | some wk =>
        if P.rels J = wk * FreeGroup.of I * wk⁻¹ ∨ P.rels J = wk * (FreeGroup.of I)⁻¹ * wk⁻¹ then
          some ⟨P.n - 1, P.m - 1, fun k => FreeGroup.lift
            (fun t => if h : t = I then 1 else FreeGroup.of (skipIndex I t h))
            (P.rels (skipEmb J k))⟩
        else none
    else none else none

/-! ## Replay, the checker, and composition of certificates -/

/-- Replay a list of recorded moves. -/
def replay : List QMove → QPres → Option QPres
  | [], P => some P
  | m :: ms, P => (m.apply P).bind (replay ms)

/-- The certificate checker: replay from the recorded start tuple and compare with the recorded
finish tuple.  This is a `Bool` computed by `decide` in the kernel. -/
def checkCert (ms : List QMove) (start finish : QPres) : Bool :=
  decide (replay ms start = some finish)

/-- Replaying a concatenation: the first block reaches an intermediate tuple and the second
carries on from it. -/
theorem replay_append : ∀ (ms₁ ms₂ : List QMove) (P R : QPres),
    replay ms₁ P = some R → replay (ms₁ ++ ms₂) P = replay ms₂ R
  | [], ms₂, P, R, h => by
      have h' : P = R := by simpa [replay] using h
      rw [h']
      rfl
  | m :: ms₁, ms₂, P, R, h => by
      cases hstep : m.apply P with
      | none => simp [replay, hstep] at h
      | some P' =>
          have hrest : replay ms₁ P' = some R := by simpa [replay, hstep] using h
          rw [List.cons_append, replay, hstep]
          exact replay_append ms₁ ms₂ P' R hrest

/-- Two consecutive replays compose: the composite move list replays from the first start to the
last finish. -/
theorem replay_concat : ∀ (ms₁ ms₂ : List QMove) (P R S : QPres),
    replay ms₁ P = some R → replay ms₂ R = some S → replay (ms₁ ++ ms₂) P = some S
  | [], ms₂, P, R, S, h₁, h₂ => by
      have h : P = R := by simpa [replay] using h₁
      rw [h]
      exact h₂
  | m :: ms₁, ms₂, P, R, S, h₁, h₂ => by
      cases hstep : m.apply P with
      | none => simp [replay, hstep] at h₁
      | some P' =>
          have hrest : replay ms₁ P' = some R := by simpa [replay, hstep] using h₁
          rw [List.cons_append, replay, hstep]
          exact replay_concat ms₁ ms₂ P' R S hrest h₂

/-- **Certificates compose.**  A block checked from `start` to `mid` and a block checked from
`mid` to `finish` give a certificate for the concatenation.  This is what lets a long chain be
checked as several kernel computations, each of them a separate `decide`. -/
theorem checkCert_append {ms₁ ms₂ : List QMove} {start mid finish : QPres}
    (h₁ : checkCert ms₁ start mid = true) (h₂ : checkCert ms₂ mid finish = true) :
    checkCert (ms₁ ++ ms₂) start finish = true := by
  have h₁' : replay ms₁ start = some mid := of_decide_eq_true h₁
  have h₂' : replay ms₂ mid = some finish := of_decide_eq_true h₂
  have h3 : replay (ms₁ ++ ms₂) start = replay ms₂ mid := replay_append ms₁ ms₂ start mid h₁'
  have h4 : replay (ms₁ ++ ms₂) start = some finish := by rw [h3, h₂']
  rw [checkCert, h4]
  simp

/-- A presentation from a list of recorded relators; a missing entry is the empty relator. -/
def mkQPres (n m : Nat) (l : List (List (Nat × Bool))) : QPres :=
  ⟨n, m, fun i => (mkWordOpt n (l.getD i.val [])).getD 1⟩

/-! ## Quick self-tests of the move set -/

/-- `<x,y | x>` -/
def test1 : QPres := mkQPres 2 1 [[(0, true)]]
/-- `<x,y,z | x, z>` -/
def test2 : QPres := mkQPres 3 2 [[(0, true)], [(2, true)]]

example : checkCert [.prolong] test1 test2 = true := by decide
example : checkCert [.delete 2 1 []] test2 test1 = true := by decide
example : checkCert [.delete 2 1 [(0, true)]] test2 test1 = false := by decide
example : checkCert [.inv 0, .inv 0] test1 test1 = true := by decide
example : checkCert [.mul 0 0] test1 test1 = false := by decide



/-! ## (ii) The presentation `metz`, in the notation of the theorem

Every certificate below is a byte-level tuple of relator words.  To say what the certificates
*state*, the presentation `<x,y | x^k, y^m, [x^j,y]>` is defined here once, and each certificate's
endpoints are identified with an instance of it by a `decide`-checked equation. -/

/-- The free group on two generators, written `x` and `a` (`y` in the presentations). -/
abbrev F2 := FreeGroup (Fin 2)

/-- The first generator `x`. -/
def gx : F2 := FreeGroup.of 0

/-- The second generator `a`, which is `y` in the presentation `<x,y | ...>`. -/
def ga : F2 := FreeGroup.of 1

/-- The presentation `<x,y | x^k, y^m, [x^j,y]>`. -/
def metz (k m j : Nat) : QPres :=
  ⟨2, 3, fun i =>
    if i = 0 then gx ^ k
    else if i = 1 then ga ^ m
    else gx ^ j * ga * (gx ^ j)⁻¹ * ga⁻¹⟩

/-! ### `metzler_pair_qstar_gap.cert`: Metzler's pair  <x,y | x^5, y^5, [x,y]>  ->  <x,y | x^5, y^5, [x^2,y]>. -/

/-- The start tuple of `metzler_pair_qstar_gap.cert` (44 Q**-moves to the end tuple). -/
def ac7_metzler_pair_qstar_gap_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_metzler_pair_qstar_gap_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_metzler_pair_qstar_gap_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true)]]
def ac7_metzler_pair_qstar_gap_i3 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_metzler_pair_qstar_gap_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (2, true)]]
def ac7_metzler_pair_qstar_gap_i5 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_metzler_pair_qstar_gap_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true)]]
def ac7_metzler_pair_qstar_gap_i7 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_metzler_pair_qstar_gap_i8 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_metzler_pair_qstar_gap_i9 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_metzler_pair_qstar_gap_i10 : QPres := mkQPres 3 4 [[(2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_metzler_pair_qstar_gap_i11 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_metzler_pair_qstar_gap_i12 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (0, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_metzler_pair_qstar_gap_i13 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (0, true), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_metzler_pair_qstar_gap_i14 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_metzler_pair_qstar_gap_i15 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_metzler_pair_qstar_gap_i16 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_metzler_pair_qstar_gap_i17 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_metzler_pair_qstar_gap_i18 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_metzler_pair_qstar_gap_i19 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (1, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_metzler_pair_qstar_gap_i20 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_metzler_pair_qstar_gap_i21 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_metzler_pair_qstar_gap_i22 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]
def ac7_metzler_pair_qstar_gap_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]

def ac7_metzler_pair_qstar_gap_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_metzler_pair_qstar_gap_c2 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false)] ]
def ac7_metzler_pair_qstar_gap_c3 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true)] ]
def ac7_metzler_pair_qstar_gap_c4 : List QMove :=
  [ .conj 3 [(0, false), (0, false)],
    .mul 0 3 ]
def ac7_metzler_pair_qstar_gap_c5 : List QMove :=
  [ .conj 3 [(0, true), (0, true)],
    .conj 0 [(2, true), (0, false), (2, true), (2, true)] ]
def ac7_metzler_pair_qstar_gap_c6 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (0, true), (2, false)] ]
def ac7_metzler_pair_qstar_gap_c7 : List QMove :=
  [ .conj 0 [(2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_metzler_pair_qstar_gap_c8 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false)],
    .conj 0 [(0, true), (1, true), (2, true), (2, true)] ]
def ac7_metzler_pair_qstar_gap_c9 : List QMove :=
  [ .lmul 2 0,
    .conj 0 [(2, false), (2, false), (1, false), (0, false)] ]
def ac7_metzler_pair_qstar_gap_c10 : List QMove :=
  [ .inv 0,
    .lmul 2 0 ]
def ac7_metzler_pair_qstar_gap_c11 : List QMove :=
  [ .inv 0,
    .nijinv 0 2 ]
def ac7_metzler_pair_qstar_gap_c12 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_metzler_pair_qstar_gap_c13 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true)] ]
def ac7_metzler_pair_qstar_gap_c14 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_metzler_pair_qstar_gap_c15 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_metzler_pair_qstar_gap_c16 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_metzler_pair_qstar_gap_c17 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_metzler_pair_qstar_gap_c18 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false)] ]
def ac7_metzler_pair_qstar_gap_c19 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_metzler_pair_qstar_gap_c20 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_metzler_pair_qstar_gap_c21 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)] ]
def ac7_metzler_pair_qstar_gap_c22 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b1 :
    replay ac7_metzler_pair_qstar_gap_c1 ac7_metzler_pair_qstar_gap_s = some ac7_metzler_pair_qstar_gap_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b2 :
    replay ac7_metzler_pair_qstar_gap_c2 ac7_metzler_pair_qstar_gap_i1 = some ac7_metzler_pair_qstar_gap_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b3 :
    replay ac7_metzler_pair_qstar_gap_c3 ac7_metzler_pair_qstar_gap_i2 = some ac7_metzler_pair_qstar_gap_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b4 :
    replay ac7_metzler_pair_qstar_gap_c4 ac7_metzler_pair_qstar_gap_i3 = some ac7_metzler_pair_qstar_gap_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b5 :
    replay ac7_metzler_pair_qstar_gap_c5 ac7_metzler_pair_qstar_gap_i4 = some ac7_metzler_pair_qstar_gap_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b6 :
    replay ac7_metzler_pair_qstar_gap_c6 ac7_metzler_pair_qstar_gap_i5 = some ac7_metzler_pair_qstar_gap_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b7 :
    replay ac7_metzler_pair_qstar_gap_c7 ac7_metzler_pair_qstar_gap_i6 = some ac7_metzler_pair_qstar_gap_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b8 :
    replay ac7_metzler_pair_qstar_gap_c8 ac7_metzler_pair_qstar_gap_i7 = some ac7_metzler_pair_qstar_gap_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b9 :
    replay ac7_metzler_pair_qstar_gap_c9 ac7_metzler_pair_qstar_gap_i8 = some ac7_metzler_pair_qstar_gap_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b10 :
    replay ac7_metzler_pair_qstar_gap_c10 ac7_metzler_pair_qstar_gap_i9 = some ac7_metzler_pair_qstar_gap_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b11 :
    replay ac7_metzler_pair_qstar_gap_c11 ac7_metzler_pair_qstar_gap_i10 = some ac7_metzler_pair_qstar_gap_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b12 :
    replay ac7_metzler_pair_qstar_gap_c12 ac7_metzler_pair_qstar_gap_i11 = some ac7_metzler_pair_qstar_gap_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b13 :
    replay ac7_metzler_pair_qstar_gap_c13 ac7_metzler_pair_qstar_gap_i12 = some ac7_metzler_pair_qstar_gap_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b14 :
    replay ac7_metzler_pair_qstar_gap_c14 ac7_metzler_pair_qstar_gap_i13 = some ac7_metzler_pair_qstar_gap_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b15 :
    replay ac7_metzler_pair_qstar_gap_c15 ac7_metzler_pair_qstar_gap_i14 = some ac7_metzler_pair_qstar_gap_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b16 :
    replay ac7_metzler_pair_qstar_gap_c16 ac7_metzler_pair_qstar_gap_i15 = some ac7_metzler_pair_qstar_gap_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b17 :
    replay ac7_metzler_pair_qstar_gap_c17 ac7_metzler_pair_qstar_gap_i16 = some ac7_metzler_pair_qstar_gap_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b18 :
    replay ac7_metzler_pair_qstar_gap_c18 ac7_metzler_pair_qstar_gap_i17 = some ac7_metzler_pair_qstar_gap_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b19 :
    replay ac7_metzler_pair_qstar_gap_c19 ac7_metzler_pair_qstar_gap_i18 = some ac7_metzler_pair_qstar_gap_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b20 :
    replay ac7_metzler_pair_qstar_gap_c20 ac7_metzler_pair_qstar_gap_i19 = some ac7_metzler_pair_qstar_gap_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b21 :
    replay ac7_metzler_pair_qstar_gap_c21 ac7_metzler_pair_qstar_gap_i20 = some ac7_metzler_pair_qstar_gap_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_metzler_pair_qstar_gap_b22 :
    replay ac7_metzler_pair_qstar_gap_c22 ac7_metzler_pair_qstar_gap_i21 = some ac7_metzler_pair_qstar_gap_i22 := by decide

theorem ac7_metzler_pair_qstar_gap_k0_2 : replay (ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ac7_metzler_pair_qstar_gap_s = some ac7_metzler_pair_qstar_gap_i2 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c1) (ms₂ := ac7_metzler_pair_qstar_gap_c2) (P := ac7_metzler_pair_qstar_gap_s) (R := ac7_metzler_pair_qstar_gap_i1) (S := ac7_metzler_pair_qstar_gap_i2) ac7_metzler_pair_qstar_gap_b1 ac7_metzler_pair_qstar_gap_b2
theorem ac7_metzler_pair_qstar_gap_k3_5 : replay (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5) ac7_metzler_pair_qstar_gap_i3 = some ac7_metzler_pair_qstar_gap_i5 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c4) (ms₂ := ac7_metzler_pair_qstar_gap_c5) (P := ac7_metzler_pair_qstar_gap_i3) (R := ac7_metzler_pair_qstar_gap_i4) (S := ac7_metzler_pair_qstar_gap_i5) ac7_metzler_pair_qstar_gap_b4 ac7_metzler_pair_qstar_gap_b5
theorem ac7_metzler_pair_qstar_gap_k2_5 : replay (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5)) ac7_metzler_pair_qstar_gap_i2 = some ac7_metzler_pair_qstar_gap_i5 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c3) (ms₂ := (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5)) (P := ac7_metzler_pair_qstar_gap_i2) (R := ac7_metzler_pair_qstar_gap_i3) (S := ac7_metzler_pair_qstar_gap_i5) ac7_metzler_pair_qstar_gap_b3 ac7_metzler_pair_qstar_gap_k3_5
theorem ac7_metzler_pair_qstar_gap_k0_5 : replay ((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) ac7_metzler_pair_qstar_gap_s = some ac7_metzler_pair_qstar_gap_i5 :=
  replay_concat (ms₁ := (ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2)) (ms₂ := (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) (P := ac7_metzler_pair_qstar_gap_s) (R := ac7_metzler_pair_qstar_gap_i2) (S := ac7_metzler_pair_qstar_gap_i5) ac7_metzler_pair_qstar_gap_k0_2 ac7_metzler_pair_qstar_gap_k2_5
theorem ac7_metzler_pair_qstar_gap_k6_8 : replay (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8) ac7_metzler_pair_qstar_gap_i6 = some ac7_metzler_pair_qstar_gap_i8 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c7) (ms₂ := ac7_metzler_pair_qstar_gap_c8) (P := ac7_metzler_pair_qstar_gap_i6) (R := ac7_metzler_pair_qstar_gap_i7) (S := ac7_metzler_pair_qstar_gap_i8) ac7_metzler_pair_qstar_gap_b7 ac7_metzler_pair_qstar_gap_b8
theorem ac7_metzler_pair_qstar_gap_k5_8 : replay (ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ac7_metzler_pair_qstar_gap_i5 = some ac7_metzler_pair_qstar_gap_i8 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c6) (ms₂ := (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) (P := ac7_metzler_pair_qstar_gap_i5) (R := ac7_metzler_pair_qstar_gap_i6) (S := ac7_metzler_pair_qstar_gap_i8) ac7_metzler_pair_qstar_gap_b6 ac7_metzler_pair_qstar_gap_k6_8
theorem ac7_metzler_pair_qstar_gap_k9_11 : replay (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11) ac7_metzler_pair_qstar_gap_i9 = some ac7_metzler_pair_qstar_gap_i11 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c10) (ms₂ := ac7_metzler_pair_qstar_gap_c11) (P := ac7_metzler_pair_qstar_gap_i9) (R := ac7_metzler_pair_qstar_gap_i10) (S := ac7_metzler_pair_qstar_gap_i11) ac7_metzler_pair_qstar_gap_b10 ac7_metzler_pair_qstar_gap_b11
theorem ac7_metzler_pair_qstar_gap_k8_11 : replay (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)) ac7_metzler_pair_qstar_gap_i8 = some ac7_metzler_pair_qstar_gap_i11 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c9) (ms₂ := (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)) (P := ac7_metzler_pair_qstar_gap_i8) (R := ac7_metzler_pair_qstar_gap_i9) (S := ac7_metzler_pair_qstar_gap_i11) ac7_metzler_pair_qstar_gap_b9 ac7_metzler_pair_qstar_gap_k9_11
theorem ac7_metzler_pair_qstar_gap_k5_11 : replay ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11))) ac7_metzler_pair_qstar_gap_i5 = some ac7_metzler_pair_qstar_gap_i11 :=
  replay_concat (ms₁ := (ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8))) (ms₂ := (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11))) (P := ac7_metzler_pair_qstar_gap_i5) (R := ac7_metzler_pair_qstar_gap_i8) (S := ac7_metzler_pair_qstar_gap_i11) ac7_metzler_pair_qstar_gap_k5_8 ac7_metzler_pair_qstar_gap_k8_11
theorem ac7_metzler_pair_qstar_gap_k0_11 : replay (((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) ++ ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)))) ac7_metzler_pair_qstar_gap_s = some ac7_metzler_pair_qstar_gap_i11 :=
  replay_concat (ms₁ := ((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5)))) (ms₂ := ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)))) (P := ac7_metzler_pair_qstar_gap_s) (R := ac7_metzler_pair_qstar_gap_i5) (S := ac7_metzler_pair_qstar_gap_i11) ac7_metzler_pair_qstar_gap_k0_5 ac7_metzler_pair_qstar_gap_k5_11
theorem ac7_metzler_pair_qstar_gap_k11_13 : replay (ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ac7_metzler_pair_qstar_gap_i11 = some ac7_metzler_pair_qstar_gap_i13 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c12) (ms₂ := ac7_metzler_pair_qstar_gap_c13) (P := ac7_metzler_pair_qstar_gap_i11) (R := ac7_metzler_pair_qstar_gap_i12) (S := ac7_metzler_pair_qstar_gap_i13) ac7_metzler_pair_qstar_gap_b12 ac7_metzler_pair_qstar_gap_b13
theorem ac7_metzler_pair_qstar_gap_k14_16 : replay (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16) ac7_metzler_pair_qstar_gap_i14 = some ac7_metzler_pair_qstar_gap_i16 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c15) (ms₂ := ac7_metzler_pair_qstar_gap_c16) (P := ac7_metzler_pair_qstar_gap_i14) (R := ac7_metzler_pair_qstar_gap_i15) (S := ac7_metzler_pair_qstar_gap_i16) ac7_metzler_pair_qstar_gap_b15 ac7_metzler_pair_qstar_gap_b16
theorem ac7_metzler_pair_qstar_gap_k13_16 : replay (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16)) ac7_metzler_pair_qstar_gap_i13 = some ac7_metzler_pair_qstar_gap_i16 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c14) (ms₂ := (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16)) (P := ac7_metzler_pair_qstar_gap_i13) (R := ac7_metzler_pair_qstar_gap_i14) (S := ac7_metzler_pair_qstar_gap_i16) ac7_metzler_pair_qstar_gap_b14 ac7_metzler_pair_qstar_gap_k14_16
theorem ac7_metzler_pair_qstar_gap_k11_16 : replay ((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) ac7_metzler_pair_qstar_gap_i11 = some ac7_metzler_pair_qstar_gap_i16 :=
  replay_concat (ms₁ := (ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13)) (ms₂ := (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) (P := ac7_metzler_pair_qstar_gap_i11) (R := ac7_metzler_pair_qstar_gap_i13) (S := ac7_metzler_pair_qstar_gap_i16) ac7_metzler_pair_qstar_gap_k11_13 ac7_metzler_pair_qstar_gap_k13_16
theorem ac7_metzler_pair_qstar_gap_k17_19 : replay (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19) ac7_metzler_pair_qstar_gap_i17 = some ac7_metzler_pair_qstar_gap_i19 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c18) (ms₂ := ac7_metzler_pair_qstar_gap_c19) (P := ac7_metzler_pair_qstar_gap_i17) (R := ac7_metzler_pair_qstar_gap_i18) (S := ac7_metzler_pair_qstar_gap_i19) ac7_metzler_pair_qstar_gap_b18 ac7_metzler_pair_qstar_gap_b19
theorem ac7_metzler_pair_qstar_gap_k16_19 : replay (ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ac7_metzler_pair_qstar_gap_i16 = some ac7_metzler_pair_qstar_gap_i19 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c17) (ms₂ := (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) (P := ac7_metzler_pair_qstar_gap_i16) (R := ac7_metzler_pair_qstar_gap_i17) (S := ac7_metzler_pair_qstar_gap_i19) ac7_metzler_pair_qstar_gap_b17 ac7_metzler_pair_qstar_gap_k17_19
theorem ac7_metzler_pair_qstar_gap_k20_22 : replay (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22) ac7_metzler_pair_qstar_gap_i20 = some ac7_metzler_pair_qstar_gap_i22 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c21) (ms₂ := ac7_metzler_pair_qstar_gap_c22) (P := ac7_metzler_pair_qstar_gap_i20) (R := ac7_metzler_pair_qstar_gap_i21) (S := ac7_metzler_pair_qstar_gap_i22) ac7_metzler_pair_qstar_gap_b21 ac7_metzler_pair_qstar_gap_b22
theorem ac7_metzler_pair_qstar_gap_k19_22 : replay (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22)) ac7_metzler_pair_qstar_gap_i19 = some ac7_metzler_pair_qstar_gap_i22 :=
  replay_concat (ms₁ := ac7_metzler_pair_qstar_gap_c20) (ms₂ := (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22)) (P := ac7_metzler_pair_qstar_gap_i19) (R := ac7_metzler_pair_qstar_gap_i20) (S := ac7_metzler_pair_qstar_gap_i22) ac7_metzler_pair_qstar_gap_b20 ac7_metzler_pair_qstar_gap_k20_22
theorem ac7_metzler_pair_qstar_gap_k16_22 : replay ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22))) ac7_metzler_pair_qstar_gap_i16 = some ac7_metzler_pair_qstar_gap_i22 :=
  replay_concat (ms₁ := (ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19))) (ms₂ := (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22))) (P := ac7_metzler_pair_qstar_gap_i16) (R := ac7_metzler_pair_qstar_gap_i19) (S := ac7_metzler_pair_qstar_gap_i22) ac7_metzler_pair_qstar_gap_k16_19 ac7_metzler_pair_qstar_gap_k19_22
theorem ac7_metzler_pair_qstar_gap_k11_22 : replay (((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) ++ ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22)))) ac7_metzler_pair_qstar_gap_i11 = some ac7_metzler_pair_qstar_gap_i22 :=
  replay_concat (ms₁ := ((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16)))) (ms₂ := ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22)))) (P := ac7_metzler_pair_qstar_gap_i11) (R := ac7_metzler_pair_qstar_gap_i16) (S := ac7_metzler_pair_qstar_gap_i22) ac7_metzler_pair_qstar_gap_k11_16 ac7_metzler_pair_qstar_gap_k16_22
theorem ac7_metzler_pair_qstar_gap_k0_22 : replay ((((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) ++ ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)))) ++ (((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) ++ ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22))))) ac7_metzler_pair_qstar_gap_s = some ac7_metzler_pair_qstar_gap_i22 :=
  replay_concat (ms₁ := (((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) ++ ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11))))) (ms₂ := (((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) ++ ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22))))) (P := ac7_metzler_pair_qstar_gap_s) (R := ac7_metzler_pair_qstar_gap_i11) (S := ac7_metzler_pair_qstar_gap_i22) ac7_metzler_pair_qstar_gap_k0_11 ac7_metzler_pair_qstar_gap_k11_22

/-- `metzler_pair_qstar_gap.cert` checked: replaying its 44 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_metzler_pair_qstar_gap_replay : replay ((((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) ++ ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)))) ++ (((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) ++ ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22))))) ac7_metzler_pair_qstar_gap_s = some ac7_metzler_pair_qstar_gap_i22 := ac7_metzler_pair_qstar_gap_k0_22

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_metzler_pair_qstar_gap_checked : checkCert ((((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) ++ ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)))) ++ (((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) ++ ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22))))) ac7_metzler_pair_qstar_gap_s ac7_metzler_pair_qstar_gap_i22 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_metzler_pair_qstar_gap_replay

/-- The endpoints of `metzler_pair_qstar_gap.cert` are the presentations `<x,y | x^5, y^5, [x^1,y]>`
    and `<x,y | x^5, y^5, [x^2,y]>` of the statement. -/
theorem ac7_metzler_pair_qstar_gap_endpoints :
    metz 5 5 1 = ac7_metzler_pair_qstar_gap_s ∧ metz 5 5 2 = ac7_metzler_pair_qstar_gap_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 44-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_metzler_pair_qstar_gap_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 5 5 1) = some (metz 5 5 2) := by
  refine ⟨((((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) ++ ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)))) ++ (((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) ++ ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22))))), ?_⟩
  calc replay ((((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) ++ ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)))) ++ (((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) ++ ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22))))) (metz 5 5 1) = replay ((((ac7_metzler_pair_qstar_gap_c1 ++ ac7_metzler_pair_qstar_gap_c2) ++ (ac7_metzler_pair_qstar_gap_c3 ++ (ac7_metzler_pair_qstar_gap_c4 ++ ac7_metzler_pair_qstar_gap_c5))) ++ ((ac7_metzler_pair_qstar_gap_c6 ++ (ac7_metzler_pair_qstar_gap_c7 ++ ac7_metzler_pair_qstar_gap_c8)) ++ (ac7_metzler_pair_qstar_gap_c9 ++ (ac7_metzler_pair_qstar_gap_c10 ++ ac7_metzler_pair_qstar_gap_c11)))) ++ (((ac7_metzler_pair_qstar_gap_c12 ++ ac7_metzler_pair_qstar_gap_c13) ++ (ac7_metzler_pair_qstar_gap_c14 ++ (ac7_metzler_pair_qstar_gap_c15 ++ ac7_metzler_pair_qstar_gap_c16))) ++ ((ac7_metzler_pair_qstar_gap_c17 ++ (ac7_metzler_pair_qstar_gap_c18 ++ ac7_metzler_pair_qstar_gap_c19)) ++ (ac7_metzler_pair_qstar_gap_c20 ++ (ac7_metzler_pair_qstar_gap_c21 ++ ac7_metzler_pair_qstar_gap_c22))))) ac7_metzler_pair_qstar_gap_s := by rw [ac7_metzler_pair_qstar_gap_endpoints.1]
    _ = some ac7_metzler_pair_qstar_gap_e := ac7_metzler_pair_qstar_gap_replay
    _ = some (metz 5 5 2) := by rw [ac7_metzler_pair_qstar_gap_endpoints.2]

/-! ### `fam_k11_t2_m5.cert`: Metzler family, k=11 t=2 m=5  <x,y | x^11, y^5, [x,y]>  ->  <x,y | x^11, y^5, [x^5,y]>. -/

/-- The start tuple of `fam_k11_t2_m5.cert` (56 Q**-moves to the end tuple). -/
def ac7_fam_k11_t2_m5_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k11_t2_m5_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k11_t2_m5_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k11_t2_m5_i3 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k11_t2_m5_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k11_t2_m5_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k11_t2_m5_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k11_t2_m5_i7 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true)]]
def ac7_fam_k11_t2_m5_i8 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (2, true)]]
def ac7_fam_k11_t2_m5_i9 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k11_t2_m5_i10 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t2_m5_i11 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t2_m5_i12 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t2_m5_i13 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t2_m5_i14 : QPres := mkQPres 3 4 [[(2, false), (2, false), (2, false), (2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t2_m5_i15 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t2_m5_i16 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t2_m5_i17 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t2_m5_i18 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k11_t2_m5_i19 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k11_t2_m5_i20 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k11_t2_m5_i21 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k11_t2_m5_i22 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k11_t2_m5_i23 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k11_t2_m5_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k11_t2_m5_i25 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k11_t2_m5_i26 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k11_t2_m5_i27 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k11_t2_m5_i28 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)]]
def ac7_fam_k11_t2_m5_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)]]

def ac7_fam_k11_t2_m5_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k11_t2_m5_c2 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k11_t2_m5_c3 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k11_t2_m5_c4 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k11_t2_m5_c5 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k11_t2_m5_c6 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k11_t2_m5_c7 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k11_t2_m5_c8 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false)] ]
def ac7_fam_k11_t2_m5_c9 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true)] ]
def ac7_fam_k11_t2_m5_c10 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k11_t2_m5_c11 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false), (0, true), (2, false)],
    .conj 0 [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true)] ]
def ac7_fam_k11_t2_m5_c12 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false)] ]
def ac7_fam_k11_t2_m5_c13 : List QMove :=
  [ .conj 0 [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true)],
    .lmul 2 0 ]
def ac7_fam_k11_t2_m5_c14 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false), (1, false), (0, false)],
    .inv 0 ]
def ac7_fam_k11_t2_m5_c15 : List QMove :=
  [ .lmul 2 0,
    .inv 0 ]
def ac7_fam_k11_t2_m5_c16 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k11_t2_m5_c17 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k11_t2_m5_c18 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k11_t2_m5_c19 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true), (1, true), (1, true), (1, true)] ]
def ac7_fam_k11_t2_m5_c20 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k11_t2_m5_c21 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k11_t2_m5_c22 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k11_t2_m5_c23 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k11_t2_m5_c24 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false)] ]
def ac7_fam_k11_t2_m5_c25 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k11_t2_m5_c26 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k11_t2_m5_c27 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k11_t2_m5_c28 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b1 :
    replay ac7_fam_k11_t2_m5_c1 ac7_fam_k11_t2_m5_s = some ac7_fam_k11_t2_m5_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b2 :
    replay ac7_fam_k11_t2_m5_c2 ac7_fam_k11_t2_m5_i1 = some ac7_fam_k11_t2_m5_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b3 :
    replay ac7_fam_k11_t2_m5_c3 ac7_fam_k11_t2_m5_i2 = some ac7_fam_k11_t2_m5_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b4 :
    replay ac7_fam_k11_t2_m5_c4 ac7_fam_k11_t2_m5_i3 = some ac7_fam_k11_t2_m5_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b5 :
    replay ac7_fam_k11_t2_m5_c5 ac7_fam_k11_t2_m5_i4 = some ac7_fam_k11_t2_m5_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b6 :
    replay ac7_fam_k11_t2_m5_c6 ac7_fam_k11_t2_m5_i5 = some ac7_fam_k11_t2_m5_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b7 :
    replay ac7_fam_k11_t2_m5_c7 ac7_fam_k11_t2_m5_i6 = some ac7_fam_k11_t2_m5_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b8 :
    replay ac7_fam_k11_t2_m5_c8 ac7_fam_k11_t2_m5_i7 = some ac7_fam_k11_t2_m5_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b9 :
    replay ac7_fam_k11_t2_m5_c9 ac7_fam_k11_t2_m5_i8 = some ac7_fam_k11_t2_m5_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b10 :
    replay ac7_fam_k11_t2_m5_c10 ac7_fam_k11_t2_m5_i9 = some ac7_fam_k11_t2_m5_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b11 :
    replay ac7_fam_k11_t2_m5_c11 ac7_fam_k11_t2_m5_i10 = some ac7_fam_k11_t2_m5_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b12 :
    replay ac7_fam_k11_t2_m5_c12 ac7_fam_k11_t2_m5_i11 = some ac7_fam_k11_t2_m5_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b13 :
    replay ac7_fam_k11_t2_m5_c13 ac7_fam_k11_t2_m5_i12 = some ac7_fam_k11_t2_m5_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b14 :
    replay ac7_fam_k11_t2_m5_c14 ac7_fam_k11_t2_m5_i13 = some ac7_fam_k11_t2_m5_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b15 :
    replay ac7_fam_k11_t2_m5_c15 ac7_fam_k11_t2_m5_i14 = some ac7_fam_k11_t2_m5_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b16 :
    replay ac7_fam_k11_t2_m5_c16 ac7_fam_k11_t2_m5_i15 = some ac7_fam_k11_t2_m5_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b17 :
    replay ac7_fam_k11_t2_m5_c17 ac7_fam_k11_t2_m5_i16 = some ac7_fam_k11_t2_m5_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b18 :
    replay ac7_fam_k11_t2_m5_c18 ac7_fam_k11_t2_m5_i17 = some ac7_fam_k11_t2_m5_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b19 :
    replay ac7_fam_k11_t2_m5_c19 ac7_fam_k11_t2_m5_i18 = some ac7_fam_k11_t2_m5_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b20 :
    replay ac7_fam_k11_t2_m5_c20 ac7_fam_k11_t2_m5_i19 = some ac7_fam_k11_t2_m5_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b21 :
    replay ac7_fam_k11_t2_m5_c21 ac7_fam_k11_t2_m5_i20 = some ac7_fam_k11_t2_m5_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b22 :
    replay ac7_fam_k11_t2_m5_c22 ac7_fam_k11_t2_m5_i21 = some ac7_fam_k11_t2_m5_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b23 :
    replay ac7_fam_k11_t2_m5_c23 ac7_fam_k11_t2_m5_i22 = some ac7_fam_k11_t2_m5_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b24 :
    replay ac7_fam_k11_t2_m5_c24 ac7_fam_k11_t2_m5_i23 = some ac7_fam_k11_t2_m5_i24 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b25 :
    replay ac7_fam_k11_t2_m5_c25 ac7_fam_k11_t2_m5_i24 = some ac7_fam_k11_t2_m5_i25 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b26 :
    replay ac7_fam_k11_t2_m5_c26 ac7_fam_k11_t2_m5_i25 = some ac7_fam_k11_t2_m5_i26 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b27 :
    replay ac7_fam_k11_t2_m5_c27 ac7_fam_k11_t2_m5_i26 = some ac7_fam_k11_t2_m5_i27 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t2_m5_b28 :
    replay ac7_fam_k11_t2_m5_c28 ac7_fam_k11_t2_m5_i27 = some ac7_fam_k11_t2_m5_i28 := by decide

theorem ac7_fam_k11_t2_m5_k1_3 : replay (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3) ac7_fam_k11_t2_m5_i1 = some ac7_fam_k11_t2_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c2) (ms₂ := ac7_fam_k11_t2_m5_c3) (P := ac7_fam_k11_t2_m5_i1) (R := ac7_fam_k11_t2_m5_i2) (S := ac7_fam_k11_t2_m5_i3) ac7_fam_k11_t2_m5_b2 ac7_fam_k11_t2_m5_b3
theorem ac7_fam_k11_t2_m5_k0_3 : replay (ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ac7_fam_k11_t2_m5_s = some ac7_fam_k11_t2_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c1) (ms₂ := (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) (P := ac7_fam_k11_t2_m5_s) (R := ac7_fam_k11_t2_m5_i1) (S := ac7_fam_k11_t2_m5_i3) ac7_fam_k11_t2_m5_b1 ac7_fam_k11_t2_m5_k1_3
theorem ac7_fam_k11_t2_m5_k3_5 : replay (ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ac7_fam_k11_t2_m5_i3 = some ac7_fam_k11_t2_m5_i5 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c4) (ms₂ := ac7_fam_k11_t2_m5_c5) (P := ac7_fam_k11_t2_m5_i3) (R := ac7_fam_k11_t2_m5_i4) (S := ac7_fam_k11_t2_m5_i5) ac7_fam_k11_t2_m5_b4 ac7_fam_k11_t2_m5_b5
theorem ac7_fam_k11_t2_m5_k5_7 : replay (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7) ac7_fam_k11_t2_m5_i5 = some ac7_fam_k11_t2_m5_i7 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c6) (ms₂ := ac7_fam_k11_t2_m5_c7) (P := ac7_fam_k11_t2_m5_i5) (R := ac7_fam_k11_t2_m5_i6) (S := ac7_fam_k11_t2_m5_i7) ac7_fam_k11_t2_m5_b6 ac7_fam_k11_t2_m5_b7
theorem ac7_fam_k11_t2_m5_k3_7 : replay ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7)) ac7_fam_k11_t2_m5_i3 = some ac7_fam_k11_t2_m5_i7 :=
  replay_concat (ms₁ := (ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5)) (ms₂ := (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7)) (P := ac7_fam_k11_t2_m5_i3) (R := ac7_fam_k11_t2_m5_i5) (S := ac7_fam_k11_t2_m5_i7) ac7_fam_k11_t2_m5_k3_5 ac7_fam_k11_t2_m5_k5_7
theorem ac7_fam_k11_t2_m5_k0_7 : replay ((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) ac7_fam_k11_t2_m5_s = some ac7_fam_k11_t2_m5_i7 :=
  replay_concat (ms₁ := (ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3))) (ms₂ := ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) (P := ac7_fam_k11_t2_m5_s) (R := ac7_fam_k11_t2_m5_i3) (S := ac7_fam_k11_t2_m5_i7) ac7_fam_k11_t2_m5_k0_3 ac7_fam_k11_t2_m5_k3_7
theorem ac7_fam_k11_t2_m5_k8_10 : replay (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10) ac7_fam_k11_t2_m5_i8 = some ac7_fam_k11_t2_m5_i10 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c9) (ms₂ := ac7_fam_k11_t2_m5_c10) (P := ac7_fam_k11_t2_m5_i8) (R := ac7_fam_k11_t2_m5_i9) (S := ac7_fam_k11_t2_m5_i10) ac7_fam_k11_t2_m5_b9 ac7_fam_k11_t2_m5_b10
theorem ac7_fam_k11_t2_m5_k7_10 : replay (ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ac7_fam_k11_t2_m5_i7 = some ac7_fam_k11_t2_m5_i10 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c8) (ms₂ := (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) (P := ac7_fam_k11_t2_m5_i7) (R := ac7_fam_k11_t2_m5_i8) (S := ac7_fam_k11_t2_m5_i10) ac7_fam_k11_t2_m5_b8 ac7_fam_k11_t2_m5_k8_10
theorem ac7_fam_k11_t2_m5_k10_12 : replay (ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ac7_fam_k11_t2_m5_i10 = some ac7_fam_k11_t2_m5_i12 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c11) (ms₂ := ac7_fam_k11_t2_m5_c12) (P := ac7_fam_k11_t2_m5_i10) (R := ac7_fam_k11_t2_m5_i11) (S := ac7_fam_k11_t2_m5_i12) ac7_fam_k11_t2_m5_b11 ac7_fam_k11_t2_m5_b12
theorem ac7_fam_k11_t2_m5_k12_14 : replay (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14) ac7_fam_k11_t2_m5_i12 = some ac7_fam_k11_t2_m5_i14 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c13) (ms₂ := ac7_fam_k11_t2_m5_c14) (P := ac7_fam_k11_t2_m5_i12) (R := ac7_fam_k11_t2_m5_i13) (S := ac7_fam_k11_t2_m5_i14) ac7_fam_k11_t2_m5_b13 ac7_fam_k11_t2_m5_b14
theorem ac7_fam_k11_t2_m5_k10_14 : replay ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)) ac7_fam_k11_t2_m5_i10 = some ac7_fam_k11_t2_m5_i14 :=
  replay_concat (ms₁ := (ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12)) (ms₂ := (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)) (P := ac7_fam_k11_t2_m5_i10) (R := ac7_fam_k11_t2_m5_i12) (S := ac7_fam_k11_t2_m5_i14) ac7_fam_k11_t2_m5_k10_12 ac7_fam_k11_t2_m5_k12_14
theorem ac7_fam_k11_t2_m5_k7_14 : replay ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14))) ac7_fam_k11_t2_m5_i7 = some ac7_fam_k11_t2_m5_i14 :=
  replay_concat (ms₁ := (ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10))) (ms₂ := ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14))) (P := ac7_fam_k11_t2_m5_i7) (R := ac7_fam_k11_t2_m5_i10) (S := ac7_fam_k11_t2_m5_i14) ac7_fam_k11_t2_m5_k7_10 ac7_fam_k11_t2_m5_k10_14
theorem ac7_fam_k11_t2_m5_k0_14 : replay (((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) ++ ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)))) ac7_fam_k11_t2_m5_s = some ac7_fam_k11_t2_m5_i14 :=
  replay_concat (ms₁ := ((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7)))) (ms₂ := ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)))) (P := ac7_fam_k11_t2_m5_s) (R := ac7_fam_k11_t2_m5_i7) (S := ac7_fam_k11_t2_m5_i14) ac7_fam_k11_t2_m5_k0_7 ac7_fam_k11_t2_m5_k7_14
theorem ac7_fam_k11_t2_m5_k15_17 : replay (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17) ac7_fam_k11_t2_m5_i15 = some ac7_fam_k11_t2_m5_i17 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c16) (ms₂ := ac7_fam_k11_t2_m5_c17) (P := ac7_fam_k11_t2_m5_i15) (R := ac7_fam_k11_t2_m5_i16) (S := ac7_fam_k11_t2_m5_i17) ac7_fam_k11_t2_m5_b16 ac7_fam_k11_t2_m5_b17
theorem ac7_fam_k11_t2_m5_k14_17 : replay (ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ac7_fam_k11_t2_m5_i14 = some ac7_fam_k11_t2_m5_i17 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c15) (ms₂ := (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) (P := ac7_fam_k11_t2_m5_i14) (R := ac7_fam_k11_t2_m5_i15) (S := ac7_fam_k11_t2_m5_i17) ac7_fam_k11_t2_m5_b15 ac7_fam_k11_t2_m5_k15_17
theorem ac7_fam_k11_t2_m5_k17_19 : replay (ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ac7_fam_k11_t2_m5_i17 = some ac7_fam_k11_t2_m5_i19 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c18) (ms₂ := ac7_fam_k11_t2_m5_c19) (P := ac7_fam_k11_t2_m5_i17) (R := ac7_fam_k11_t2_m5_i18) (S := ac7_fam_k11_t2_m5_i19) ac7_fam_k11_t2_m5_b18 ac7_fam_k11_t2_m5_b19
theorem ac7_fam_k11_t2_m5_k19_21 : replay (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21) ac7_fam_k11_t2_m5_i19 = some ac7_fam_k11_t2_m5_i21 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c20) (ms₂ := ac7_fam_k11_t2_m5_c21) (P := ac7_fam_k11_t2_m5_i19) (R := ac7_fam_k11_t2_m5_i20) (S := ac7_fam_k11_t2_m5_i21) ac7_fam_k11_t2_m5_b20 ac7_fam_k11_t2_m5_b21
theorem ac7_fam_k11_t2_m5_k17_21 : replay ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21)) ac7_fam_k11_t2_m5_i17 = some ac7_fam_k11_t2_m5_i21 :=
  replay_concat (ms₁ := (ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19)) (ms₂ := (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21)) (P := ac7_fam_k11_t2_m5_i17) (R := ac7_fam_k11_t2_m5_i19) (S := ac7_fam_k11_t2_m5_i21) ac7_fam_k11_t2_m5_k17_19 ac7_fam_k11_t2_m5_k19_21
theorem ac7_fam_k11_t2_m5_k14_21 : replay ((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) ac7_fam_k11_t2_m5_i14 = some ac7_fam_k11_t2_m5_i21 :=
  replay_concat (ms₁ := (ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17))) (ms₂ := ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) (P := ac7_fam_k11_t2_m5_i14) (R := ac7_fam_k11_t2_m5_i17) (S := ac7_fam_k11_t2_m5_i21) ac7_fam_k11_t2_m5_k14_17 ac7_fam_k11_t2_m5_k17_21
theorem ac7_fam_k11_t2_m5_k22_24 : replay (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24) ac7_fam_k11_t2_m5_i22 = some ac7_fam_k11_t2_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c23) (ms₂ := ac7_fam_k11_t2_m5_c24) (P := ac7_fam_k11_t2_m5_i22) (R := ac7_fam_k11_t2_m5_i23) (S := ac7_fam_k11_t2_m5_i24) ac7_fam_k11_t2_m5_b23 ac7_fam_k11_t2_m5_b24
theorem ac7_fam_k11_t2_m5_k21_24 : replay (ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ac7_fam_k11_t2_m5_i21 = some ac7_fam_k11_t2_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c22) (ms₂ := (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) (P := ac7_fam_k11_t2_m5_i21) (R := ac7_fam_k11_t2_m5_i22) (S := ac7_fam_k11_t2_m5_i24) ac7_fam_k11_t2_m5_b22 ac7_fam_k11_t2_m5_k22_24
theorem ac7_fam_k11_t2_m5_k24_26 : replay (ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ac7_fam_k11_t2_m5_i24 = some ac7_fam_k11_t2_m5_i26 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c25) (ms₂ := ac7_fam_k11_t2_m5_c26) (P := ac7_fam_k11_t2_m5_i24) (R := ac7_fam_k11_t2_m5_i25) (S := ac7_fam_k11_t2_m5_i26) ac7_fam_k11_t2_m5_b25 ac7_fam_k11_t2_m5_b26
theorem ac7_fam_k11_t2_m5_k26_28 : replay (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28) ac7_fam_k11_t2_m5_i26 = some ac7_fam_k11_t2_m5_i28 :=
  replay_concat (ms₁ := ac7_fam_k11_t2_m5_c27) (ms₂ := ac7_fam_k11_t2_m5_c28) (P := ac7_fam_k11_t2_m5_i26) (R := ac7_fam_k11_t2_m5_i27) (S := ac7_fam_k11_t2_m5_i28) ac7_fam_k11_t2_m5_b27 ac7_fam_k11_t2_m5_b28
theorem ac7_fam_k11_t2_m5_k24_28 : replay ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28)) ac7_fam_k11_t2_m5_i24 = some ac7_fam_k11_t2_m5_i28 :=
  replay_concat (ms₁ := (ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26)) (ms₂ := (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28)) (P := ac7_fam_k11_t2_m5_i24) (R := ac7_fam_k11_t2_m5_i26) (S := ac7_fam_k11_t2_m5_i28) ac7_fam_k11_t2_m5_k24_26 ac7_fam_k11_t2_m5_k26_28
theorem ac7_fam_k11_t2_m5_k21_28 : replay ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28))) ac7_fam_k11_t2_m5_i21 = some ac7_fam_k11_t2_m5_i28 :=
  replay_concat (ms₁ := (ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24))) (ms₂ := ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28))) (P := ac7_fam_k11_t2_m5_i21) (R := ac7_fam_k11_t2_m5_i24) (S := ac7_fam_k11_t2_m5_i28) ac7_fam_k11_t2_m5_k21_24 ac7_fam_k11_t2_m5_k24_28
theorem ac7_fam_k11_t2_m5_k14_28 : replay (((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) ++ ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28)))) ac7_fam_k11_t2_m5_i14 = some ac7_fam_k11_t2_m5_i28 :=
  replay_concat (ms₁ := ((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21)))) (ms₂ := ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28)))) (P := ac7_fam_k11_t2_m5_i14) (R := ac7_fam_k11_t2_m5_i21) (S := ac7_fam_k11_t2_m5_i28) ac7_fam_k11_t2_m5_k14_21 ac7_fam_k11_t2_m5_k21_28
theorem ac7_fam_k11_t2_m5_k0_28 : replay ((((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) ++ ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)))) ++ (((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) ++ ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28))))) ac7_fam_k11_t2_m5_s = some ac7_fam_k11_t2_m5_i28 :=
  replay_concat (ms₁ := (((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) ++ ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14))))) (ms₂ := (((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) ++ ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28))))) (P := ac7_fam_k11_t2_m5_s) (R := ac7_fam_k11_t2_m5_i14) (S := ac7_fam_k11_t2_m5_i28) ac7_fam_k11_t2_m5_k0_14 ac7_fam_k11_t2_m5_k14_28

/-- `fam_k11_t2_m5.cert` checked: replaying its 56 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k11_t2_m5_replay : replay ((((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) ++ ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)))) ++ (((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) ++ ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28))))) ac7_fam_k11_t2_m5_s = some ac7_fam_k11_t2_m5_i28 := ac7_fam_k11_t2_m5_k0_28

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k11_t2_m5_checked : checkCert ((((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) ++ ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)))) ++ (((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) ++ ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28))))) ac7_fam_k11_t2_m5_s ac7_fam_k11_t2_m5_i28 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k11_t2_m5_replay

/-- The endpoints of `fam_k11_t2_m5.cert` are the presentations `<x,y | x^11, y^5, [x^1,y]>`
    and `<x,y | x^11, y^5, [x^5,y]>` of the statement. -/
theorem ac7_fam_k11_t2_m5_endpoints :
    metz 11 5 1 = ac7_fam_k11_t2_m5_s ∧ metz 11 5 5 = ac7_fam_k11_t2_m5_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 56-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k11_t2_m5_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 11 5 1) = some (metz 11 5 5) := by
  refine ⟨((((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) ++ ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)))) ++ (((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) ++ ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28))))), ?_⟩
  calc replay ((((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) ++ ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)))) ++ (((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) ++ ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28))))) (metz 11 5 1) = replay ((((ac7_fam_k11_t2_m5_c1 ++ (ac7_fam_k11_t2_m5_c2 ++ ac7_fam_k11_t2_m5_c3)) ++ ((ac7_fam_k11_t2_m5_c4 ++ ac7_fam_k11_t2_m5_c5) ++ (ac7_fam_k11_t2_m5_c6 ++ ac7_fam_k11_t2_m5_c7))) ++ ((ac7_fam_k11_t2_m5_c8 ++ (ac7_fam_k11_t2_m5_c9 ++ ac7_fam_k11_t2_m5_c10)) ++ ((ac7_fam_k11_t2_m5_c11 ++ ac7_fam_k11_t2_m5_c12) ++ (ac7_fam_k11_t2_m5_c13 ++ ac7_fam_k11_t2_m5_c14)))) ++ (((ac7_fam_k11_t2_m5_c15 ++ (ac7_fam_k11_t2_m5_c16 ++ ac7_fam_k11_t2_m5_c17)) ++ ((ac7_fam_k11_t2_m5_c18 ++ ac7_fam_k11_t2_m5_c19) ++ (ac7_fam_k11_t2_m5_c20 ++ ac7_fam_k11_t2_m5_c21))) ++ ((ac7_fam_k11_t2_m5_c22 ++ (ac7_fam_k11_t2_m5_c23 ++ ac7_fam_k11_t2_m5_c24)) ++ ((ac7_fam_k11_t2_m5_c25 ++ ac7_fam_k11_t2_m5_c26) ++ (ac7_fam_k11_t2_m5_c27 ++ ac7_fam_k11_t2_m5_c28))))) ac7_fam_k11_t2_m5_s := by rw [ac7_fam_k11_t2_m5_endpoints.1]
    _ = some ac7_fam_k11_t2_m5_e := ac7_fam_k11_t2_m5_replay
    _ = some (metz 11 5 5) := by rw [ac7_fam_k11_t2_m5_endpoints.2]

/-! ### `fam_k11_t5_m5.cert`: Metzler family, k=11 t=5 m=5  <x,y | x^11, y^5, [x,y]>  ->  <x,y | x^11, y^5, [x^2,y]>. -/

/-- The start tuple of `fam_k11_t5_m5.cert` (56 Q**-moves to the end tuple). -/
def ac7_fam_k11_t5_m5_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k11_t5_m5_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k11_t5_m5_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false)]]
def ac7_fam_k11_t5_m5_i3 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k11_t5_m5_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k11_t5_m5_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k11_t5_m5_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k11_t5_m5_i7 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (0, false), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i8 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i9 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i10 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (2, true), (2, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i11 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i12 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i13 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i14 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i15 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i16 : QPres := mkQPres 3 4 [[(2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i17 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k11_t5_m5_i18 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (0, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k11_t5_m5_i19 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (0, true), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k11_t5_m5_i20 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k11_t5_m5_i21 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k11_t5_m5_i22 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k11_t5_m5_i23 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k11_t5_m5_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k11_t5_m5_i25 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (1, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k11_t5_m5_i26 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_fam_k11_t5_m5_i27 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_fam_k11_t5_m5_i28 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]
def ac7_fam_k11_t5_m5_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]

def ac7_fam_k11_t5_m5_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k11_t5_m5_c2 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k11_t5_m5_c3 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k11_t5_m5_c4 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k11_t5_m5_c5 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k11_t5_m5_c6 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k11_t5_m5_c7 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (0, false), (0, false), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k11_t5_m5_c8 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (0, true), (0, true), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true)] ]
def ac7_fam_k11_t5_m5_c9 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (0, true), (0, true), (0, true), (2, false)] ]
def ac7_fam_k11_t5_m5_c10 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k11_t5_m5_c11 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (2, true), (2, true)] ]
def ac7_fam_k11_t5_m5_c12 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (0, true), (2, false)] ]
def ac7_fam_k11_t5_m5_c13 : List QMove :=
  [ .conj 0 [(2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k11_t5_m5_c14 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false)],
    .conj 0 [(0, true), (1, true), (2, true), (2, true)] ]
def ac7_fam_k11_t5_m5_c15 : List QMove :=
  [ .lmul 2 0,
    .conj 0 [(2, false), (2, false), (1, false), (0, false)] ]
def ac7_fam_k11_t5_m5_c16 : List QMove :=
  [ .inv 0,
    .lmul 2 0 ]
def ac7_fam_k11_t5_m5_c17 : List QMove :=
  [ .inv 0,
    .nijinv 0 2 ]
def ac7_fam_k11_t5_m5_c18 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k11_t5_m5_c19 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true)] ]
def ac7_fam_k11_t5_m5_c20 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k11_t5_m5_c21 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k11_t5_m5_c22 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k11_t5_m5_c23 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k11_t5_m5_c24 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false)] ]
def ac7_fam_k11_t5_m5_c25 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k11_t5_m5_c26 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k11_t5_m5_c27 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)] ]
def ac7_fam_k11_t5_m5_c28 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b1 :
    replay ac7_fam_k11_t5_m5_c1 ac7_fam_k11_t5_m5_s = some ac7_fam_k11_t5_m5_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b2 :
    replay ac7_fam_k11_t5_m5_c2 ac7_fam_k11_t5_m5_i1 = some ac7_fam_k11_t5_m5_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b3 :
    replay ac7_fam_k11_t5_m5_c3 ac7_fam_k11_t5_m5_i2 = some ac7_fam_k11_t5_m5_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b4 :
    replay ac7_fam_k11_t5_m5_c4 ac7_fam_k11_t5_m5_i3 = some ac7_fam_k11_t5_m5_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b5 :
    replay ac7_fam_k11_t5_m5_c5 ac7_fam_k11_t5_m5_i4 = some ac7_fam_k11_t5_m5_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b6 :
    replay ac7_fam_k11_t5_m5_c6 ac7_fam_k11_t5_m5_i5 = some ac7_fam_k11_t5_m5_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b7 :
    replay ac7_fam_k11_t5_m5_c7 ac7_fam_k11_t5_m5_i6 = some ac7_fam_k11_t5_m5_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b8 :
    replay ac7_fam_k11_t5_m5_c8 ac7_fam_k11_t5_m5_i7 = some ac7_fam_k11_t5_m5_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b9 :
    replay ac7_fam_k11_t5_m5_c9 ac7_fam_k11_t5_m5_i8 = some ac7_fam_k11_t5_m5_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b10 :
    replay ac7_fam_k11_t5_m5_c10 ac7_fam_k11_t5_m5_i9 = some ac7_fam_k11_t5_m5_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b11 :
    replay ac7_fam_k11_t5_m5_c11 ac7_fam_k11_t5_m5_i10 = some ac7_fam_k11_t5_m5_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b12 :
    replay ac7_fam_k11_t5_m5_c12 ac7_fam_k11_t5_m5_i11 = some ac7_fam_k11_t5_m5_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b13 :
    replay ac7_fam_k11_t5_m5_c13 ac7_fam_k11_t5_m5_i12 = some ac7_fam_k11_t5_m5_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b14 :
    replay ac7_fam_k11_t5_m5_c14 ac7_fam_k11_t5_m5_i13 = some ac7_fam_k11_t5_m5_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b15 :
    replay ac7_fam_k11_t5_m5_c15 ac7_fam_k11_t5_m5_i14 = some ac7_fam_k11_t5_m5_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b16 :
    replay ac7_fam_k11_t5_m5_c16 ac7_fam_k11_t5_m5_i15 = some ac7_fam_k11_t5_m5_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b17 :
    replay ac7_fam_k11_t5_m5_c17 ac7_fam_k11_t5_m5_i16 = some ac7_fam_k11_t5_m5_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b18 :
    replay ac7_fam_k11_t5_m5_c18 ac7_fam_k11_t5_m5_i17 = some ac7_fam_k11_t5_m5_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b19 :
    replay ac7_fam_k11_t5_m5_c19 ac7_fam_k11_t5_m5_i18 = some ac7_fam_k11_t5_m5_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b20 :
    replay ac7_fam_k11_t5_m5_c20 ac7_fam_k11_t5_m5_i19 = some ac7_fam_k11_t5_m5_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b21 :
    replay ac7_fam_k11_t5_m5_c21 ac7_fam_k11_t5_m5_i20 = some ac7_fam_k11_t5_m5_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b22 :
    replay ac7_fam_k11_t5_m5_c22 ac7_fam_k11_t5_m5_i21 = some ac7_fam_k11_t5_m5_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b23 :
    replay ac7_fam_k11_t5_m5_c23 ac7_fam_k11_t5_m5_i22 = some ac7_fam_k11_t5_m5_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b24 :
    replay ac7_fam_k11_t5_m5_c24 ac7_fam_k11_t5_m5_i23 = some ac7_fam_k11_t5_m5_i24 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b25 :
    replay ac7_fam_k11_t5_m5_c25 ac7_fam_k11_t5_m5_i24 = some ac7_fam_k11_t5_m5_i25 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b26 :
    replay ac7_fam_k11_t5_m5_c26 ac7_fam_k11_t5_m5_i25 = some ac7_fam_k11_t5_m5_i26 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b27 :
    replay ac7_fam_k11_t5_m5_c27 ac7_fam_k11_t5_m5_i26 = some ac7_fam_k11_t5_m5_i27 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k11_t5_m5_b28 :
    replay ac7_fam_k11_t5_m5_c28 ac7_fam_k11_t5_m5_i27 = some ac7_fam_k11_t5_m5_i28 := by decide

theorem ac7_fam_k11_t5_m5_k1_3 : replay (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3) ac7_fam_k11_t5_m5_i1 = some ac7_fam_k11_t5_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c2) (ms₂ := ac7_fam_k11_t5_m5_c3) (P := ac7_fam_k11_t5_m5_i1) (R := ac7_fam_k11_t5_m5_i2) (S := ac7_fam_k11_t5_m5_i3) ac7_fam_k11_t5_m5_b2 ac7_fam_k11_t5_m5_b3
theorem ac7_fam_k11_t5_m5_k0_3 : replay (ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ac7_fam_k11_t5_m5_s = some ac7_fam_k11_t5_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c1) (ms₂ := (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) (P := ac7_fam_k11_t5_m5_s) (R := ac7_fam_k11_t5_m5_i1) (S := ac7_fam_k11_t5_m5_i3) ac7_fam_k11_t5_m5_b1 ac7_fam_k11_t5_m5_k1_3
theorem ac7_fam_k11_t5_m5_k3_5 : replay (ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ac7_fam_k11_t5_m5_i3 = some ac7_fam_k11_t5_m5_i5 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c4) (ms₂ := ac7_fam_k11_t5_m5_c5) (P := ac7_fam_k11_t5_m5_i3) (R := ac7_fam_k11_t5_m5_i4) (S := ac7_fam_k11_t5_m5_i5) ac7_fam_k11_t5_m5_b4 ac7_fam_k11_t5_m5_b5
theorem ac7_fam_k11_t5_m5_k5_7 : replay (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7) ac7_fam_k11_t5_m5_i5 = some ac7_fam_k11_t5_m5_i7 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c6) (ms₂ := ac7_fam_k11_t5_m5_c7) (P := ac7_fam_k11_t5_m5_i5) (R := ac7_fam_k11_t5_m5_i6) (S := ac7_fam_k11_t5_m5_i7) ac7_fam_k11_t5_m5_b6 ac7_fam_k11_t5_m5_b7
theorem ac7_fam_k11_t5_m5_k3_7 : replay ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7)) ac7_fam_k11_t5_m5_i3 = some ac7_fam_k11_t5_m5_i7 :=
  replay_concat (ms₁ := (ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5)) (ms₂ := (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7)) (P := ac7_fam_k11_t5_m5_i3) (R := ac7_fam_k11_t5_m5_i5) (S := ac7_fam_k11_t5_m5_i7) ac7_fam_k11_t5_m5_k3_5 ac7_fam_k11_t5_m5_k5_7
theorem ac7_fam_k11_t5_m5_k0_7 : replay ((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) ac7_fam_k11_t5_m5_s = some ac7_fam_k11_t5_m5_i7 :=
  replay_concat (ms₁ := (ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3))) (ms₂ := ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) (P := ac7_fam_k11_t5_m5_s) (R := ac7_fam_k11_t5_m5_i3) (S := ac7_fam_k11_t5_m5_i7) ac7_fam_k11_t5_m5_k0_3 ac7_fam_k11_t5_m5_k3_7
theorem ac7_fam_k11_t5_m5_k8_10 : replay (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10) ac7_fam_k11_t5_m5_i8 = some ac7_fam_k11_t5_m5_i10 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c9) (ms₂ := ac7_fam_k11_t5_m5_c10) (P := ac7_fam_k11_t5_m5_i8) (R := ac7_fam_k11_t5_m5_i9) (S := ac7_fam_k11_t5_m5_i10) ac7_fam_k11_t5_m5_b9 ac7_fam_k11_t5_m5_b10
theorem ac7_fam_k11_t5_m5_k7_10 : replay (ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ac7_fam_k11_t5_m5_i7 = some ac7_fam_k11_t5_m5_i10 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c8) (ms₂ := (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) (P := ac7_fam_k11_t5_m5_i7) (R := ac7_fam_k11_t5_m5_i8) (S := ac7_fam_k11_t5_m5_i10) ac7_fam_k11_t5_m5_b8 ac7_fam_k11_t5_m5_k8_10
theorem ac7_fam_k11_t5_m5_k10_12 : replay (ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ac7_fam_k11_t5_m5_i10 = some ac7_fam_k11_t5_m5_i12 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c11) (ms₂ := ac7_fam_k11_t5_m5_c12) (P := ac7_fam_k11_t5_m5_i10) (R := ac7_fam_k11_t5_m5_i11) (S := ac7_fam_k11_t5_m5_i12) ac7_fam_k11_t5_m5_b11 ac7_fam_k11_t5_m5_b12
theorem ac7_fam_k11_t5_m5_k12_14 : replay (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14) ac7_fam_k11_t5_m5_i12 = some ac7_fam_k11_t5_m5_i14 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c13) (ms₂ := ac7_fam_k11_t5_m5_c14) (P := ac7_fam_k11_t5_m5_i12) (R := ac7_fam_k11_t5_m5_i13) (S := ac7_fam_k11_t5_m5_i14) ac7_fam_k11_t5_m5_b13 ac7_fam_k11_t5_m5_b14
theorem ac7_fam_k11_t5_m5_k10_14 : replay ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)) ac7_fam_k11_t5_m5_i10 = some ac7_fam_k11_t5_m5_i14 :=
  replay_concat (ms₁ := (ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12)) (ms₂ := (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)) (P := ac7_fam_k11_t5_m5_i10) (R := ac7_fam_k11_t5_m5_i12) (S := ac7_fam_k11_t5_m5_i14) ac7_fam_k11_t5_m5_k10_12 ac7_fam_k11_t5_m5_k12_14
theorem ac7_fam_k11_t5_m5_k7_14 : replay ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14))) ac7_fam_k11_t5_m5_i7 = some ac7_fam_k11_t5_m5_i14 :=
  replay_concat (ms₁ := (ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10))) (ms₂ := ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14))) (P := ac7_fam_k11_t5_m5_i7) (R := ac7_fam_k11_t5_m5_i10) (S := ac7_fam_k11_t5_m5_i14) ac7_fam_k11_t5_m5_k7_10 ac7_fam_k11_t5_m5_k10_14
theorem ac7_fam_k11_t5_m5_k0_14 : replay (((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) ++ ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)))) ac7_fam_k11_t5_m5_s = some ac7_fam_k11_t5_m5_i14 :=
  replay_concat (ms₁ := ((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7)))) (ms₂ := ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)))) (P := ac7_fam_k11_t5_m5_s) (R := ac7_fam_k11_t5_m5_i7) (S := ac7_fam_k11_t5_m5_i14) ac7_fam_k11_t5_m5_k0_7 ac7_fam_k11_t5_m5_k7_14
theorem ac7_fam_k11_t5_m5_k15_17 : replay (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17) ac7_fam_k11_t5_m5_i15 = some ac7_fam_k11_t5_m5_i17 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c16) (ms₂ := ac7_fam_k11_t5_m5_c17) (P := ac7_fam_k11_t5_m5_i15) (R := ac7_fam_k11_t5_m5_i16) (S := ac7_fam_k11_t5_m5_i17) ac7_fam_k11_t5_m5_b16 ac7_fam_k11_t5_m5_b17
theorem ac7_fam_k11_t5_m5_k14_17 : replay (ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ac7_fam_k11_t5_m5_i14 = some ac7_fam_k11_t5_m5_i17 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c15) (ms₂ := (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) (P := ac7_fam_k11_t5_m5_i14) (R := ac7_fam_k11_t5_m5_i15) (S := ac7_fam_k11_t5_m5_i17) ac7_fam_k11_t5_m5_b15 ac7_fam_k11_t5_m5_k15_17
theorem ac7_fam_k11_t5_m5_k17_19 : replay (ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ac7_fam_k11_t5_m5_i17 = some ac7_fam_k11_t5_m5_i19 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c18) (ms₂ := ac7_fam_k11_t5_m5_c19) (P := ac7_fam_k11_t5_m5_i17) (R := ac7_fam_k11_t5_m5_i18) (S := ac7_fam_k11_t5_m5_i19) ac7_fam_k11_t5_m5_b18 ac7_fam_k11_t5_m5_b19
theorem ac7_fam_k11_t5_m5_k19_21 : replay (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21) ac7_fam_k11_t5_m5_i19 = some ac7_fam_k11_t5_m5_i21 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c20) (ms₂ := ac7_fam_k11_t5_m5_c21) (P := ac7_fam_k11_t5_m5_i19) (R := ac7_fam_k11_t5_m5_i20) (S := ac7_fam_k11_t5_m5_i21) ac7_fam_k11_t5_m5_b20 ac7_fam_k11_t5_m5_b21
theorem ac7_fam_k11_t5_m5_k17_21 : replay ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21)) ac7_fam_k11_t5_m5_i17 = some ac7_fam_k11_t5_m5_i21 :=
  replay_concat (ms₁ := (ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19)) (ms₂ := (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21)) (P := ac7_fam_k11_t5_m5_i17) (R := ac7_fam_k11_t5_m5_i19) (S := ac7_fam_k11_t5_m5_i21) ac7_fam_k11_t5_m5_k17_19 ac7_fam_k11_t5_m5_k19_21
theorem ac7_fam_k11_t5_m5_k14_21 : replay ((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) ac7_fam_k11_t5_m5_i14 = some ac7_fam_k11_t5_m5_i21 :=
  replay_concat (ms₁ := (ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17))) (ms₂ := ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) (P := ac7_fam_k11_t5_m5_i14) (R := ac7_fam_k11_t5_m5_i17) (S := ac7_fam_k11_t5_m5_i21) ac7_fam_k11_t5_m5_k14_17 ac7_fam_k11_t5_m5_k17_21
theorem ac7_fam_k11_t5_m5_k22_24 : replay (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24) ac7_fam_k11_t5_m5_i22 = some ac7_fam_k11_t5_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c23) (ms₂ := ac7_fam_k11_t5_m5_c24) (P := ac7_fam_k11_t5_m5_i22) (R := ac7_fam_k11_t5_m5_i23) (S := ac7_fam_k11_t5_m5_i24) ac7_fam_k11_t5_m5_b23 ac7_fam_k11_t5_m5_b24
theorem ac7_fam_k11_t5_m5_k21_24 : replay (ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ac7_fam_k11_t5_m5_i21 = some ac7_fam_k11_t5_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c22) (ms₂ := (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) (P := ac7_fam_k11_t5_m5_i21) (R := ac7_fam_k11_t5_m5_i22) (S := ac7_fam_k11_t5_m5_i24) ac7_fam_k11_t5_m5_b22 ac7_fam_k11_t5_m5_k22_24
theorem ac7_fam_k11_t5_m5_k24_26 : replay (ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ac7_fam_k11_t5_m5_i24 = some ac7_fam_k11_t5_m5_i26 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c25) (ms₂ := ac7_fam_k11_t5_m5_c26) (P := ac7_fam_k11_t5_m5_i24) (R := ac7_fam_k11_t5_m5_i25) (S := ac7_fam_k11_t5_m5_i26) ac7_fam_k11_t5_m5_b25 ac7_fam_k11_t5_m5_b26
theorem ac7_fam_k11_t5_m5_k26_28 : replay (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28) ac7_fam_k11_t5_m5_i26 = some ac7_fam_k11_t5_m5_i28 :=
  replay_concat (ms₁ := ac7_fam_k11_t5_m5_c27) (ms₂ := ac7_fam_k11_t5_m5_c28) (P := ac7_fam_k11_t5_m5_i26) (R := ac7_fam_k11_t5_m5_i27) (S := ac7_fam_k11_t5_m5_i28) ac7_fam_k11_t5_m5_b27 ac7_fam_k11_t5_m5_b28
theorem ac7_fam_k11_t5_m5_k24_28 : replay ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28)) ac7_fam_k11_t5_m5_i24 = some ac7_fam_k11_t5_m5_i28 :=
  replay_concat (ms₁ := (ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26)) (ms₂ := (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28)) (P := ac7_fam_k11_t5_m5_i24) (R := ac7_fam_k11_t5_m5_i26) (S := ac7_fam_k11_t5_m5_i28) ac7_fam_k11_t5_m5_k24_26 ac7_fam_k11_t5_m5_k26_28
theorem ac7_fam_k11_t5_m5_k21_28 : replay ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28))) ac7_fam_k11_t5_m5_i21 = some ac7_fam_k11_t5_m5_i28 :=
  replay_concat (ms₁ := (ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24))) (ms₂ := ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28))) (P := ac7_fam_k11_t5_m5_i21) (R := ac7_fam_k11_t5_m5_i24) (S := ac7_fam_k11_t5_m5_i28) ac7_fam_k11_t5_m5_k21_24 ac7_fam_k11_t5_m5_k24_28
theorem ac7_fam_k11_t5_m5_k14_28 : replay (((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) ++ ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28)))) ac7_fam_k11_t5_m5_i14 = some ac7_fam_k11_t5_m5_i28 :=
  replay_concat (ms₁ := ((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21)))) (ms₂ := ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28)))) (P := ac7_fam_k11_t5_m5_i14) (R := ac7_fam_k11_t5_m5_i21) (S := ac7_fam_k11_t5_m5_i28) ac7_fam_k11_t5_m5_k14_21 ac7_fam_k11_t5_m5_k21_28
theorem ac7_fam_k11_t5_m5_k0_28 : replay ((((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) ++ ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)))) ++ (((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) ++ ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28))))) ac7_fam_k11_t5_m5_s = some ac7_fam_k11_t5_m5_i28 :=
  replay_concat (ms₁ := (((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) ++ ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14))))) (ms₂ := (((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) ++ ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28))))) (P := ac7_fam_k11_t5_m5_s) (R := ac7_fam_k11_t5_m5_i14) (S := ac7_fam_k11_t5_m5_i28) ac7_fam_k11_t5_m5_k0_14 ac7_fam_k11_t5_m5_k14_28

/-- `fam_k11_t5_m5.cert` checked: replaying its 56 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k11_t5_m5_replay : replay ((((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) ++ ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)))) ++ (((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) ++ ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28))))) ac7_fam_k11_t5_m5_s = some ac7_fam_k11_t5_m5_i28 := ac7_fam_k11_t5_m5_k0_28

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k11_t5_m5_checked : checkCert ((((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) ++ ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)))) ++ (((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) ++ ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28))))) ac7_fam_k11_t5_m5_s ac7_fam_k11_t5_m5_i28 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k11_t5_m5_replay

/-- The endpoints of `fam_k11_t5_m5.cert` are the presentations `<x,y | x^11, y^5, [x^1,y]>`
    and `<x,y | x^11, y^5, [x^2,y]>` of the statement. -/
theorem ac7_fam_k11_t5_m5_endpoints :
    metz 11 5 1 = ac7_fam_k11_t5_m5_s ∧ metz 11 5 2 = ac7_fam_k11_t5_m5_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 56-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k11_t5_m5_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 11 5 1) = some (metz 11 5 2) := by
  refine ⟨((((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) ++ ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)))) ++ (((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) ++ ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28))))), ?_⟩
  calc replay ((((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) ++ ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)))) ++ (((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) ++ ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28))))) (metz 11 5 1) = replay ((((ac7_fam_k11_t5_m5_c1 ++ (ac7_fam_k11_t5_m5_c2 ++ ac7_fam_k11_t5_m5_c3)) ++ ((ac7_fam_k11_t5_m5_c4 ++ ac7_fam_k11_t5_m5_c5) ++ (ac7_fam_k11_t5_m5_c6 ++ ac7_fam_k11_t5_m5_c7))) ++ ((ac7_fam_k11_t5_m5_c8 ++ (ac7_fam_k11_t5_m5_c9 ++ ac7_fam_k11_t5_m5_c10)) ++ ((ac7_fam_k11_t5_m5_c11 ++ ac7_fam_k11_t5_m5_c12) ++ (ac7_fam_k11_t5_m5_c13 ++ ac7_fam_k11_t5_m5_c14)))) ++ (((ac7_fam_k11_t5_m5_c15 ++ (ac7_fam_k11_t5_m5_c16 ++ ac7_fam_k11_t5_m5_c17)) ++ ((ac7_fam_k11_t5_m5_c18 ++ ac7_fam_k11_t5_m5_c19) ++ (ac7_fam_k11_t5_m5_c20 ++ ac7_fam_k11_t5_m5_c21))) ++ ((ac7_fam_k11_t5_m5_c22 ++ (ac7_fam_k11_t5_m5_c23 ++ ac7_fam_k11_t5_m5_c24)) ++ ((ac7_fam_k11_t5_m5_c25 ++ ac7_fam_k11_t5_m5_c26) ++ (ac7_fam_k11_t5_m5_c27 ++ ac7_fam_k11_t5_m5_c28))))) ac7_fam_k11_t5_m5_s := by rw [ac7_fam_k11_t5_m5_endpoints.1]
    _ = some ac7_fam_k11_t5_m5_e := ac7_fam_k11_t5_m5_replay
    _ = some (metz 11 5 2) := by rw [ac7_fam_k11_t5_m5_endpoints.2]

/-! ### `fam_k13_t2_m5.cert`: Metzler family, k=13 t=2 m=5  <x,y | x^13, y^5, [x,y]>  ->  <x,y | x^13, y^5, [x^6,y]>. -/

/-- The start tuple of `fam_k13_t2_m5.cert` (60 Q**-moves to the end tuple). -/
def ac7_fam_k13_t2_m5_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k13_t2_m5_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k13_t2_m5_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t2_m5_i3 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k13_t2_m5_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t2_m5_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t2_m5_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k13_t2_m5_i7 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t2_m5_i8 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true)]]
def ac7_fam_k13_t2_m5_i9 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k13_t2_m5_i10 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (2, true)]]
def ac7_fam_k13_t2_m5_i11 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k13_t2_m5_i12 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t2_m5_i13 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t2_m5_i14 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t2_m5_i15 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t2_m5_i16 : QPres := mkQPres 3 4 [[(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t2_m5_i17 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t2_m5_i18 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t2_m5_i19 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t2_m5_i20 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k13_t2_m5_i21 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k13_t2_m5_i22 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k13_t2_m5_i23 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t2_m5_i24 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t2_m5_i25 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k13_t2_m5_i26 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k13_t2_m5_i27 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k13_t2_m5_i28 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k13_t2_m5_i29 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k13_t2_m5_i30 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)]]
def ac7_fam_k13_t2_m5_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)]]

def ac7_fam_k13_t2_m5_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k13_t2_m5_c2 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k13_t2_m5_c3 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k13_t2_m5_c4 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k13_t2_m5_c5 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k13_t2_m5_c6 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k13_t2_m5_c7 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k13_t2_m5_c8 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k13_t2_m5_c9 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k13_t2_m5_c10 : List QMove :=
  [ .conj 3 [(0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k13_t2_m5_c11 : List QMove :=
  [ .conj 3 [(0, true), (0, true)],
    .conj 0 [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)] ]
def ac7_fam_k13_t2_m5_c12 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (0, true), (2, false)] ]
def ac7_fam_k13_t2_m5_c13 : List QMove :=
  [ .conj 0 [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k13_t2_m5_c14 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (2, false)],
    .conj 0 [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)] ]
def ac7_fam_k13_t2_m5_c15 : List QMove :=
  [ .lmul 2 0,
    .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, false), (0, false)] ]
def ac7_fam_k13_t2_m5_c16 : List QMove :=
  [ .inv 0,
    .lmul 2 0 ]
def ac7_fam_k13_t2_m5_c17 : List QMove :=
  [ .inv 0,
    .nijinv 0 2 ]
def ac7_fam_k13_t2_m5_c18 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k13_t2_m5_c19 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k13_t2_m5_c20 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k13_t2_m5_c21 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true)] ]
def ac7_fam_k13_t2_m5_c22 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k13_t2_m5_c23 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k13_t2_m5_c24 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k13_t2_m5_c25 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k13_t2_m5_c26 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false)] ]
def ac7_fam_k13_t2_m5_c27 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k13_t2_m5_c28 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k13_t2_m5_c29 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k13_t2_m5_c30 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b1 :
    replay ac7_fam_k13_t2_m5_c1 ac7_fam_k13_t2_m5_s = some ac7_fam_k13_t2_m5_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b2 :
    replay ac7_fam_k13_t2_m5_c2 ac7_fam_k13_t2_m5_i1 = some ac7_fam_k13_t2_m5_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b3 :
    replay ac7_fam_k13_t2_m5_c3 ac7_fam_k13_t2_m5_i2 = some ac7_fam_k13_t2_m5_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b4 :
    replay ac7_fam_k13_t2_m5_c4 ac7_fam_k13_t2_m5_i3 = some ac7_fam_k13_t2_m5_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b5 :
    replay ac7_fam_k13_t2_m5_c5 ac7_fam_k13_t2_m5_i4 = some ac7_fam_k13_t2_m5_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b6 :
    replay ac7_fam_k13_t2_m5_c6 ac7_fam_k13_t2_m5_i5 = some ac7_fam_k13_t2_m5_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b7 :
    replay ac7_fam_k13_t2_m5_c7 ac7_fam_k13_t2_m5_i6 = some ac7_fam_k13_t2_m5_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b8 :
    replay ac7_fam_k13_t2_m5_c8 ac7_fam_k13_t2_m5_i7 = some ac7_fam_k13_t2_m5_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b9 :
    replay ac7_fam_k13_t2_m5_c9 ac7_fam_k13_t2_m5_i8 = some ac7_fam_k13_t2_m5_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b10 :
    replay ac7_fam_k13_t2_m5_c10 ac7_fam_k13_t2_m5_i9 = some ac7_fam_k13_t2_m5_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b11 :
    replay ac7_fam_k13_t2_m5_c11 ac7_fam_k13_t2_m5_i10 = some ac7_fam_k13_t2_m5_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b12 :
    replay ac7_fam_k13_t2_m5_c12 ac7_fam_k13_t2_m5_i11 = some ac7_fam_k13_t2_m5_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b13 :
    replay ac7_fam_k13_t2_m5_c13 ac7_fam_k13_t2_m5_i12 = some ac7_fam_k13_t2_m5_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b14 :
    replay ac7_fam_k13_t2_m5_c14 ac7_fam_k13_t2_m5_i13 = some ac7_fam_k13_t2_m5_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b15 :
    replay ac7_fam_k13_t2_m5_c15 ac7_fam_k13_t2_m5_i14 = some ac7_fam_k13_t2_m5_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b16 :
    replay ac7_fam_k13_t2_m5_c16 ac7_fam_k13_t2_m5_i15 = some ac7_fam_k13_t2_m5_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b17 :
    replay ac7_fam_k13_t2_m5_c17 ac7_fam_k13_t2_m5_i16 = some ac7_fam_k13_t2_m5_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b18 :
    replay ac7_fam_k13_t2_m5_c18 ac7_fam_k13_t2_m5_i17 = some ac7_fam_k13_t2_m5_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b19 :
    replay ac7_fam_k13_t2_m5_c19 ac7_fam_k13_t2_m5_i18 = some ac7_fam_k13_t2_m5_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b20 :
    replay ac7_fam_k13_t2_m5_c20 ac7_fam_k13_t2_m5_i19 = some ac7_fam_k13_t2_m5_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b21 :
    replay ac7_fam_k13_t2_m5_c21 ac7_fam_k13_t2_m5_i20 = some ac7_fam_k13_t2_m5_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b22 :
    replay ac7_fam_k13_t2_m5_c22 ac7_fam_k13_t2_m5_i21 = some ac7_fam_k13_t2_m5_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b23 :
    replay ac7_fam_k13_t2_m5_c23 ac7_fam_k13_t2_m5_i22 = some ac7_fam_k13_t2_m5_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b24 :
    replay ac7_fam_k13_t2_m5_c24 ac7_fam_k13_t2_m5_i23 = some ac7_fam_k13_t2_m5_i24 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b25 :
    replay ac7_fam_k13_t2_m5_c25 ac7_fam_k13_t2_m5_i24 = some ac7_fam_k13_t2_m5_i25 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b26 :
    replay ac7_fam_k13_t2_m5_c26 ac7_fam_k13_t2_m5_i25 = some ac7_fam_k13_t2_m5_i26 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b27 :
    replay ac7_fam_k13_t2_m5_c27 ac7_fam_k13_t2_m5_i26 = some ac7_fam_k13_t2_m5_i27 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b28 :
    replay ac7_fam_k13_t2_m5_c28 ac7_fam_k13_t2_m5_i27 = some ac7_fam_k13_t2_m5_i28 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b29 :
    replay ac7_fam_k13_t2_m5_c29 ac7_fam_k13_t2_m5_i28 = some ac7_fam_k13_t2_m5_i29 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t2_m5_b30 :
    replay ac7_fam_k13_t2_m5_c30 ac7_fam_k13_t2_m5_i29 = some ac7_fam_k13_t2_m5_i30 := by decide

theorem ac7_fam_k13_t2_m5_k1_3 : replay (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3) ac7_fam_k13_t2_m5_i1 = some ac7_fam_k13_t2_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c2) (ms₂ := ac7_fam_k13_t2_m5_c3) (P := ac7_fam_k13_t2_m5_i1) (R := ac7_fam_k13_t2_m5_i2) (S := ac7_fam_k13_t2_m5_i3) ac7_fam_k13_t2_m5_b2 ac7_fam_k13_t2_m5_b3
theorem ac7_fam_k13_t2_m5_k0_3 : replay (ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ac7_fam_k13_t2_m5_s = some ac7_fam_k13_t2_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c1) (ms₂ := (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) (P := ac7_fam_k13_t2_m5_s) (R := ac7_fam_k13_t2_m5_i1) (S := ac7_fam_k13_t2_m5_i3) ac7_fam_k13_t2_m5_b1 ac7_fam_k13_t2_m5_k1_3
theorem ac7_fam_k13_t2_m5_k3_5 : replay (ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ac7_fam_k13_t2_m5_i3 = some ac7_fam_k13_t2_m5_i5 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c4) (ms₂ := ac7_fam_k13_t2_m5_c5) (P := ac7_fam_k13_t2_m5_i3) (R := ac7_fam_k13_t2_m5_i4) (S := ac7_fam_k13_t2_m5_i5) ac7_fam_k13_t2_m5_b4 ac7_fam_k13_t2_m5_b5
theorem ac7_fam_k13_t2_m5_k5_7 : replay (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7) ac7_fam_k13_t2_m5_i5 = some ac7_fam_k13_t2_m5_i7 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c6) (ms₂ := ac7_fam_k13_t2_m5_c7) (P := ac7_fam_k13_t2_m5_i5) (R := ac7_fam_k13_t2_m5_i6) (S := ac7_fam_k13_t2_m5_i7) ac7_fam_k13_t2_m5_b6 ac7_fam_k13_t2_m5_b7
theorem ac7_fam_k13_t2_m5_k3_7 : replay ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7)) ac7_fam_k13_t2_m5_i3 = some ac7_fam_k13_t2_m5_i7 :=
  replay_concat (ms₁ := (ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5)) (ms₂ := (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7)) (P := ac7_fam_k13_t2_m5_i3) (R := ac7_fam_k13_t2_m5_i5) (S := ac7_fam_k13_t2_m5_i7) ac7_fam_k13_t2_m5_k3_5 ac7_fam_k13_t2_m5_k5_7
theorem ac7_fam_k13_t2_m5_k0_7 : replay ((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) ac7_fam_k13_t2_m5_s = some ac7_fam_k13_t2_m5_i7 :=
  replay_concat (ms₁ := (ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3))) (ms₂ := ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) (P := ac7_fam_k13_t2_m5_s) (R := ac7_fam_k13_t2_m5_i3) (S := ac7_fam_k13_t2_m5_i7) ac7_fam_k13_t2_m5_k0_3 ac7_fam_k13_t2_m5_k3_7
theorem ac7_fam_k13_t2_m5_k7_9 : replay (ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ac7_fam_k13_t2_m5_i7 = some ac7_fam_k13_t2_m5_i9 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c8) (ms₂ := ac7_fam_k13_t2_m5_c9) (P := ac7_fam_k13_t2_m5_i7) (R := ac7_fam_k13_t2_m5_i8) (S := ac7_fam_k13_t2_m5_i9) ac7_fam_k13_t2_m5_b8 ac7_fam_k13_t2_m5_b9
theorem ac7_fam_k13_t2_m5_k9_11 : replay (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11) ac7_fam_k13_t2_m5_i9 = some ac7_fam_k13_t2_m5_i11 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c10) (ms₂ := ac7_fam_k13_t2_m5_c11) (P := ac7_fam_k13_t2_m5_i9) (R := ac7_fam_k13_t2_m5_i10) (S := ac7_fam_k13_t2_m5_i11) ac7_fam_k13_t2_m5_b10 ac7_fam_k13_t2_m5_b11
theorem ac7_fam_k13_t2_m5_k7_11 : replay ((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ac7_fam_k13_t2_m5_i7 = some ac7_fam_k13_t2_m5_i11 :=
  replay_concat (ms₁ := (ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9)) (ms₂ := (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) (P := ac7_fam_k13_t2_m5_i7) (R := ac7_fam_k13_t2_m5_i9) (S := ac7_fam_k13_t2_m5_i11) ac7_fam_k13_t2_m5_k7_9 ac7_fam_k13_t2_m5_k9_11
theorem ac7_fam_k13_t2_m5_k11_13 : replay (ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ac7_fam_k13_t2_m5_i11 = some ac7_fam_k13_t2_m5_i13 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c12) (ms₂ := ac7_fam_k13_t2_m5_c13) (P := ac7_fam_k13_t2_m5_i11) (R := ac7_fam_k13_t2_m5_i12) (S := ac7_fam_k13_t2_m5_i13) ac7_fam_k13_t2_m5_b12 ac7_fam_k13_t2_m5_b13
theorem ac7_fam_k13_t2_m5_k13_15 : replay (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15) ac7_fam_k13_t2_m5_i13 = some ac7_fam_k13_t2_m5_i15 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c14) (ms₂ := ac7_fam_k13_t2_m5_c15) (P := ac7_fam_k13_t2_m5_i13) (R := ac7_fam_k13_t2_m5_i14) (S := ac7_fam_k13_t2_m5_i15) ac7_fam_k13_t2_m5_b14 ac7_fam_k13_t2_m5_b15
theorem ac7_fam_k13_t2_m5_k11_15 : replay ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)) ac7_fam_k13_t2_m5_i11 = some ac7_fam_k13_t2_m5_i15 :=
  replay_concat (ms₁ := (ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13)) (ms₂ := (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)) (P := ac7_fam_k13_t2_m5_i11) (R := ac7_fam_k13_t2_m5_i13) (S := ac7_fam_k13_t2_m5_i15) ac7_fam_k13_t2_m5_k11_13 ac7_fam_k13_t2_m5_k13_15
theorem ac7_fam_k13_t2_m5_k7_15 : replay (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15))) ac7_fam_k13_t2_m5_i7 = some ac7_fam_k13_t2_m5_i15 :=
  replay_concat (ms₁ := ((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11))) (ms₂ := ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15))) (P := ac7_fam_k13_t2_m5_i7) (R := ac7_fam_k13_t2_m5_i11) (S := ac7_fam_k13_t2_m5_i15) ac7_fam_k13_t2_m5_k7_11 ac7_fam_k13_t2_m5_k11_15
theorem ac7_fam_k13_t2_m5_k0_15 : replay (((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) ++ (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)))) ac7_fam_k13_t2_m5_s = some ac7_fam_k13_t2_m5_i15 :=
  replay_concat (ms₁ := ((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7)))) (ms₂ := (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)))) (P := ac7_fam_k13_t2_m5_s) (R := ac7_fam_k13_t2_m5_i7) (S := ac7_fam_k13_t2_m5_i15) ac7_fam_k13_t2_m5_k0_7 ac7_fam_k13_t2_m5_k7_15
theorem ac7_fam_k13_t2_m5_k16_18 : replay (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18) ac7_fam_k13_t2_m5_i16 = some ac7_fam_k13_t2_m5_i18 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c17) (ms₂ := ac7_fam_k13_t2_m5_c18) (P := ac7_fam_k13_t2_m5_i16) (R := ac7_fam_k13_t2_m5_i17) (S := ac7_fam_k13_t2_m5_i18) ac7_fam_k13_t2_m5_b17 ac7_fam_k13_t2_m5_b18
theorem ac7_fam_k13_t2_m5_k15_18 : replay (ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ac7_fam_k13_t2_m5_i15 = some ac7_fam_k13_t2_m5_i18 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c16) (ms₂ := (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) (P := ac7_fam_k13_t2_m5_i15) (R := ac7_fam_k13_t2_m5_i16) (S := ac7_fam_k13_t2_m5_i18) ac7_fam_k13_t2_m5_b16 ac7_fam_k13_t2_m5_k16_18
theorem ac7_fam_k13_t2_m5_k18_20 : replay (ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ac7_fam_k13_t2_m5_i18 = some ac7_fam_k13_t2_m5_i20 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c19) (ms₂ := ac7_fam_k13_t2_m5_c20) (P := ac7_fam_k13_t2_m5_i18) (R := ac7_fam_k13_t2_m5_i19) (S := ac7_fam_k13_t2_m5_i20) ac7_fam_k13_t2_m5_b19 ac7_fam_k13_t2_m5_b20
theorem ac7_fam_k13_t2_m5_k20_22 : replay (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22) ac7_fam_k13_t2_m5_i20 = some ac7_fam_k13_t2_m5_i22 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c21) (ms₂ := ac7_fam_k13_t2_m5_c22) (P := ac7_fam_k13_t2_m5_i20) (R := ac7_fam_k13_t2_m5_i21) (S := ac7_fam_k13_t2_m5_i22) ac7_fam_k13_t2_m5_b21 ac7_fam_k13_t2_m5_b22
theorem ac7_fam_k13_t2_m5_k18_22 : replay ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22)) ac7_fam_k13_t2_m5_i18 = some ac7_fam_k13_t2_m5_i22 :=
  replay_concat (ms₁ := (ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20)) (ms₂ := (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22)) (P := ac7_fam_k13_t2_m5_i18) (R := ac7_fam_k13_t2_m5_i20) (S := ac7_fam_k13_t2_m5_i22) ac7_fam_k13_t2_m5_k18_20 ac7_fam_k13_t2_m5_k20_22
theorem ac7_fam_k13_t2_m5_k15_22 : replay ((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) ac7_fam_k13_t2_m5_i15 = some ac7_fam_k13_t2_m5_i22 :=
  replay_concat (ms₁ := (ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18))) (ms₂ := ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) (P := ac7_fam_k13_t2_m5_i15) (R := ac7_fam_k13_t2_m5_i18) (S := ac7_fam_k13_t2_m5_i22) ac7_fam_k13_t2_m5_k15_18 ac7_fam_k13_t2_m5_k18_22
theorem ac7_fam_k13_t2_m5_k22_24 : replay (ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ac7_fam_k13_t2_m5_i22 = some ac7_fam_k13_t2_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c23) (ms₂ := ac7_fam_k13_t2_m5_c24) (P := ac7_fam_k13_t2_m5_i22) (R := ac7_fam_k13_t2_m5_i23) (S := ac7_fam_k13_t2_m5_i24) ac7_fam_k13_t2_m5_b23 ac7_fam_k13_t2_m5_b24
theorem ac7_fam_k13_t2_m5_k24_26 : replay (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26) ac7_fam_k13_t2_m5_i24 = some ac7_fam_k13_t2_m5_i26 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c25) (ms₂ := ac7_fam_k13_t2_m5_c26) (P := ac7_fam_k13_t2_m5_i24) (R := ac7_fam_k13_t2_m5_i25) (S := ac7_fam_k13_t2_m5_i26) ac7_fam_k13_t2_m5_b25 ac7_fam_k13_t2_m5_b26
theorem ac7_fam_k13_t2_m5_k22_26 : replay ((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ac7_fam_k13_t2_m5_i22 = some ac7_fam_k13_t2_m5_i26 :=
  replay_concat (ms₁ := (ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24)) (ms₂ := (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) (P := ac7_fam_k13_t2_m5_i22) (R := ac7_fam_k13_t2_m5_i24) (S := ac7_fam_k13_t2_m5_i26) ac7_fam_k13_t2_m5_k22_24 ac7_fam_k13_t2_m5_k24_26
theorem ac7_fam_k13_t2_m5_k26_28 : replay (ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ac7_fam_k13_t2_m5_i26 = some ac7_fam_k13_t2_m5_i28 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c27) (ms₂ := ac7_fam_k13_t2_m5_c28) (P := ac7_fam_k13_t2_m5_i26) (R := ac7_fam_k13_t2_m5_i27) (S := ac7_fam_k13_t2_m5_i28) ac7_fam_k13_t2_m5_b27 ac7_fam_k13_t2_m5_b28
theorem ac7_fam_k13_t2_m5_k28_30 : replay (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30) ac7_fam_k13_t2_m5_i28 = some ac7_fam_k13_t2_m5_i30 :=
  replay_concat (ms₁ := ac7_fam_k13_t2_m5_c29) (ms₂ := ac7_fam_k13_t2_m5_c30) (P := ac7_fam_k13_t2_m5_i28) (R := ac7_fam_k13_t2_m5_i29) (S := ac7_fam_k13_t2_m5_i30) ac7_fam_k13_t2_m5_b29 ac7_fam_k13_t2_m5_b30
theorem ac7_fam_k13_t2_m5_k26_30 : replay ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30)) ac7_fam_k13_t2_m5_i26 = some ac7_fam_k13_t2_m5_i30 :=
  replay_concat (ms₁ := (ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28)) (ms₂ := (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30)) (P := ac7_fam_k13_t2_m5_i26) (R := ac7_fam_k13_t2_m5_i28) (S := ac7_fam_k13_t2_m5_i30) ac7_fam_k13_t2_m5_k26_28 ac7_fam_k13_t2_m5_k28_30
theorem ac7_fam_k13_t2_m5_k22_30 : replay (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30))) ac7_fam_k13_t2_m5_i22 = some ac7_fam_k13_t2_m5_i30 :=
  replay_concat (ms₁ := ((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26))) (ms₂ := ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30))) (P := ac7_fam_k13_t2_m5_i22) (R := ac7_fam_k13_t2_m5_i26) (S := ac7_fam_k13_t2_m5_i30) ac7_fam_k13_t2_m5_k22_26 ac7_fam_k13_t2_m5_k26_30
theorem ac7_fam_k13_t2_m5_k15_30 : replay (((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) ++ (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30)))) ac7_fam_k13_t2_m5_i15 = some ac7_fam_k13_t2_m5_i30 :=
  replay_concat (ms₁ := ((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22)))) (ms₂ := (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30)))) (P := ac7_fam_k13_t2_m5_i15) (R := ac7_fam_k13_t2_m5_i22) (S := ac7_fam_k13_t2_m5_i30) ac7_fam_k13_t2_m5_k15_22 ac7_fam_k13_t2_m5_k22_30
theorem ac7_fam_k13_t2_m5_k0_30 : replay ((((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) ++ (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)))) ++ (((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) ++ (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30))))) ac7_fam_k13_t2_m5_s = some ac7_fam_k13_t2_m5_i30 :=
  replay_concat (ms₁ := (((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) ++ (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15))))) (ms₂ := (((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) ++ (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30))))) (P := ac7_fam_k13_t2_m5_s) (R := ac7_fam_k13_t2_m5_i15) (S := ac7_fam_k13_t2_m5_i30) ac7_fam_k13_t2_m5_k0_15 ac7_fam_k13_t2_m5_k15_30

/-- `fam_k13_t2_m5.cert` checked: replaying its 60 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k13_t2_m5_replay : replay ((((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) ++ (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)))) ++ (((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) ++ (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30))))) ac7_fam_k13_t2_m5_s = some ac7_fam_k13_t2_m5_i30 := ac7_fam_k13_t2_m5_k0_30

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k13_t2_m5_checked : checkCert ((((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) ++ (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)))) ++ (((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) ++ (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30))))) ac7_fam_k13_t2_m5_s ac7_fam_k13_t2_m5_i30 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k13_t2_m5_replay

/-- The endpoints of `fam_k13_t2_m5.cert` are the presentations `<x,y | x^13, y^5, [x^1,y]>`
    and `<x,y | x^13, y^5, [x^6,y]>` of the statement. -/
theorem ac7_fam_k13_t2_m5_endpoints :
    metz 13 5 1 = ac7_fam_k13_t2_m5_s ∧ metz 13 5 6 = ac7_fam_k13_t2_m5_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 60-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k13_t2_m5_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 13 5 1) = some (metz 13 5 6) := by
  refine ⟨((((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) ++ (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)))) ++ (((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) ++ (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30))))), ?_⟩
  calc replay ((((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) ++ (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)))) ++ (((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) ++ (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30))))) (metz 13 5 1) = replay ((((ac7_fam_k13_t2_m5_c1 ++ (ac7_fam_k13_t2_m5_c2 ++ ac7_fam_k13_t2_m5_c3)) ++ ((ac7_fam_k13_t2_m5_c4 ++ ac7_fam_k13_t2_m5_c5) ++ (ac7_fam_k13_t2_m5_c6 ++ ac7_fam_k13_t2_m5_c7))) ++ (((ac7_fam_k13_t2_m5_c8 ++ ac7_fam_k13_t2_m5_c9) ++ (ac7_fam_k13_t2_m5_c10 ++ ac7_fam_k13_t2_m5_c11)) ++ ((ac7_fam_k13_t2_m5_c12 ++ ac7_fam_k13_t2_m5_c13) ++ (ac7_fam_k13_t2_m5_c14 ++ ac7_fam_k13_t2_m5_c15)))) ++ (((ac7_fam_k13_t2_m5_c16 ++ (ac7_fam_k13_t2_m5_c17 ++ ac7_fam_k13_t2_m5_c18)) ++ ((ac7_fam_k13_t2_m5_c19 ++ ac7_fam_k13_t2_m5_c20) ++ (ac7_fam_k13_t2_m5_c21 ++ ac7_fam_k13_t2_m5_c22))) ++ (((ac7_fam_k13_t2_m5_c23 ++ ac7_fam_k13_t2_m5_c24) ++ (ac7_fam_k13_t2_m5_c25 ++ ac7_fam_k13_t2_m5_c26)) ++ ((ac7_fam_k13_t2_m5_c27 ++ ac7_fam_k13_t2_m5_c28) ++ (ac7_fam_k13_t2_m5_c29 ++ ac7_fam_k13_t2_m5_c30))))) ac7_fam_k13_t2_m5_s := by rw [ac7_fam_k13_t2_m5_endpoints.1]
    _ = some ac7_fam_k13_t2_m5_e := ac7_fam_k13_t2_m5_replay
    _ = some (metz 13 5 6) := by rw [ac7_fam_k13_t2_m5_endpoints.2]

/-! ### `fam_k13_t4_m7.cert`: Metzler family, k=13 t=4 m=7  <x,y | x^13, y^7, [x,y]>  ->  <x,y | x^13, y^7, [x^3,y]>. -/

/-- The start tuple of `fam_k13_t4_m7.cert` (56 Q**-moves to the end tuple). -/
def ac7_fam_k13_t4_m7_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k13_t4_m7_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k13_t4_m7_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false)]]
def ac7_fam_k13_t4_m7_i3 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t4_m7_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k13_t4_m7_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t4_m7_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k13_t4_m7_i7 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k13_t4_m7_i8 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i9 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (2, true), (2, true), (2, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i10 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i11 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i12 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i13 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i14 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i15 : QPres := mkQPres 3 4 [[(2, false), (2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i16 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i17 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k13_t4_m7_i18 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k13_t4_m7_i19 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k13_t4_m7_i20 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k13_t4_m7_i21 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t4_m7_i22 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k13_t4_m7_i23 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k13_t4_m7_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k13_t4_m7_i25 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k13_t4_m7_i26 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k13_t4_m7_i27 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k13_t4_m7_i28 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)]]
def ac7_fam_k13_t4_m7_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)]]

def ac7_fam_k13_t4_m7_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k13_t4_m7_c2 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k13_t4_m7_c3 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k13_t4_m7_c4 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k13_t4_m7_c5 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k13_t4_m7_c6 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k13_t4_m7_c7 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k13_t4_m7_c8 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k13_t4_m7_c9 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (0, true), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (0, false), (2, true), (2, true), (2, true)] ]
def ac7_fam_k13_t4_m7_c10 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (2, false), (0, true), (0, true), (2, false)] ]
def ac7_fam_k13_t4_m7_c11 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k13_t4_m7_c12 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (0, true), (2, false)],
    .conj 0 [(2, true), (2, true), (2, true), (2, true)] ]
def ac7_fam_k13_t4_m7_c13 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (2, false), (2, false)] ]
def ac7_fam_k13_t4_m7_c14 : List QMove :=
  [ .conj 0 [(0, true), (1, true), (2, true), (2, true), (2, true)],
    .lmul 2 0 ]
def ac7_fam_k13_t4_m7_c15 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (1, false), (0, false)],
    .inv 0 ]
def ac7_fam_k13_t4_m7_c16 : List QMove :=
  [ .lmul 2 0,
    .inv 0 ]
def ac7_fam_k13_t4_m7_c17 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k13_t4_m7_c18 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k13_t4_m7_c19 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true), (1, true)] ]
def ac7_fam_k13_t4_m7_c20 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k13_t4_m7_c21 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k13_t4_m7_c22 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k13_t4_m7_c23 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k13_t4_m7_c24 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)] ]
def ac7_fam_k13_t4_m7_c25 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k13_t4_m7_c26 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k13_t4_m7_c27 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k13_t4_m7_c28 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b1 :
    replay ac7_fam_k13_t4_m7_c1 ac7_fam_k13_t4_m7_s = some ac7_fam_k13_t4_m7_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b2 :
    replay ac7_fam_k13_t4_m7_c2 ac7_fam_k13_t4_m7_i1 = some ac7_fam_k13_t4_m7_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b3 :
    replay ac7_fam_k13_t4_m7_c3 ac7_fam_k13_t4_m7_i2 = some ac7_fam_k13_t4_m7_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b4 :
    replay ac7_fam_k13_t4_m7_c4 ac7_fam_k13_t4_m7_i3 = some ac7_fam_k13_t4_m7_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b5 :
    replay ac7_fam_k13_t4_m7_c5 ac7_fam_k13_t4_m7_i4 = some ac7_fam_k13_t4_m7_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b6 :
    replay ac7_fam_k13_t4_m7_c6 ac7_fam_k13_t4_m7_i5 = some ac7_fam_k13_t4_m7_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b7 :
    replay ac7_fam_k13_t4_m7_c7 ac7_fam_k13_t4_m7_i6 = some ac7_fam_k13_t4_m7_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b8 :
    replay ac7_fam_k13_t4_m7_c8 ac7_fam_k13_t4_m7_i7 = some ac7_fam_k13_t4_m7_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b9 :
    replay ac7_fam_k13_t4_m7_c9 ac7_fam_k13_t4_m7_i8 = some ac7_fam_k13_t4_m7_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b10 :
    replay ac7_fam_k13_t4_m7_c10 ac7_fam_k13_t4_m7_i9 = some ac7_fam_k13_t4_m7_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b11 :
    replay ac7_fam_k13_t4_m7_c11 ac7_fam_k13_t4_m7_i10 = some ac7_fam_k13_t4_m7_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b12 :
    replay ac7_fam_k13_t4_m7_c12 ac7_fam_k13_t4_m7_i11 = some ac7_fam_k13_t4_m7_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b13 :
    replay ac7_fam_k13_t4_m7_c13 ac7_fam_k13_t4_m7_i12 = some ac7_fam_k13_t4_m7_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b14 :
    replay ac7_fam_k13_t4_m7_c14 ac7_fam_k13_t4_m7_i13 = some ac7_fam_k13_t4_m7_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b15 :
    replay ac7_fam_k13_t4_m7_c15 ac7_fam_k13_t4_m7_i14 = some ac7_fam_k13_t4_m7_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b16 :
    replay ac7_fam_k13_t4_m7_c16 ac7_fam_k13_t4_m7_i15 = some ac7_fam_k13_t4_m7_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b17 :
    replay ac7_fam_k13_t4_m7_c17 ac7_fam_k13_t4_m7_i16 = some ac7_fam_k13_t4_m7_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b18 :
    replay ac7_fam_k13_t4_m7_c18 ac7_fam_k13_t4_m7_i17 = some ac7_fam_k13_t4_m7_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b19 :
    replay ac7_fam_k13_t4_m7_c19 ac7_fam_k13_t4_m7_i18 = some ac7_fam_k13_t4_m7_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b20 :
    replay ac7_fam_k13_t4_m7_c20 ac7_fam_k13_t4_m7_i19 = some ac7_fam_k13_t4_m7_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b21 :
    replay ac7_fam_k13_t4_m7_c21 ac7_fam_k13_t4_m7_i20 = some ac7_fam_k13_t4_m7_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b22 :
    replay ac7_fam_k13_t4_m7_c22 ac7_fam_k13_t4_m7_i21 = some ac7_fam_k13_t4_m7_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b23 :
    replay ac7_fam_k13_t4_m7_c23 ac7_fam_k13_t4_m7_i22 = some ac7_fam_k13_t4_m7_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b24 :
    replay ac7_fam_k13_t4_m7_c24 ac7_fam_k13_t4_m7_i23 = some ac7_fam_k13_t4_m7_i24 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b25 :
    replay ac7_fam_k13_t4_m7_c25 ac7_fam_k13_t4_m7_i24 = some ac7_fam_k13_t4_m7_i25 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b26 :
    replay ac7_fam_k13_t4_m7_c26 ac7_fam_k13_t4_m7_i25 = some ac7_fam_k13_t4_m7_i26 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b27 :
    replay ac7_fam_k13_t4_m7_c27 ac7_fam_k13_t4_m7_i26 = some ac7_fam_k13_t4_m7_i27 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k13_t4_m7_b28 :
    replay ac7_fam_k13_t4_m7_c28 ac7_fam_k13_t4_m7_i27 = some ac7_fam_k13_t4_m7_i28 := by decide

theorem ac7_fam_k13_t4_m7_k1_3 : replay (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3) ac7_fam_k13_t4_m7_i1 = some ac7_fam_k13_t4_m7_i3 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c2) (ms₂ := ac7_fam_k13_t4_m7_c3) (P := ac7_fam_k13_t4_m7_i1) (R := ac7_fam_k13_t4_m7_i2) (S := ac7_fam_k13_t4_m7_i3) ac7_fam_k13_t4_m7_b2 ac7_fam_k13_t4_m7_b3
theorem ac7_fam_k13_t4_m7_k0_3 : replay (ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ac7_fam_k13_t4_m7_s = some ac7_fam_k13_t4_m7_i3 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c1) (ms₂ := (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) (P := ac7_fam_k13_t4_m7_s) (R := ac7_fam_k13_t4_m7_i1) (S := ac7_fam_k13_t4_m7_i3) ac7_fam_k13_t4_m7_b1 ac7_fam_k13_t4_m7_k1_3
theorem ac7_fam_k13_t4_m7_k3_5 : replay (ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ac7_fam_k13_t4_m7_i3 = some ac7_fam_k13_t4_m7_i5 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c4) (ms₂ := ac7_fam_k13_t4_m7_c5) (P := ac7_fam_k13_t4_m7_i3) (R := ac7_fam_k13_t4_m7_i4) (S := ac7_fam_k13_t4_m7_i5) ac7_fam_k13_t4_m7_b4 ac7_fam_k13_t4_m7_b5
theorem ac7_fam_k13_t4_m7_k5_7 : replay (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7) ac7_fam_k13_t4_m7_i5 = some ac7_fam_k13_t4_m7_i7 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c6) (ms₂ := ac7_fam_k13_t4_m7_c7) (P := ac7_fam_k13_t4_m7_i5) (R := ac7_fam_k13_t4_m7_i6) (S := ac7_fam_k13_t4_m7_i7) ac7_fam_k13_t4_m7_b6 ac7_fam_k13_t4_m7_b7
theorem ac7_fam_k13_t4_m7_k3_7 : replay ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7)) ac7_fam_k13_t4_m7_i3 = some ac7_fam_k13_t4_m7_i7 :=
  replay_concat (ms₁ := (ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5)) (ms₂ := (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7)) (P := ac7_fam_k13_t4_m7_i3) (R := ac7_fam_k13_t4_m7_i5) (S := ac7_fam_k13_t4_m7_i7) ac7_fam_k13_t4_m7_k3_5 ac7_fam_k13_t4_m7_k5_7
theorem ac7_fam_k13_t4_m7_k0_7 : replay ((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) ac7_fam_k13_t4_m7_s = some ac7_fam_k13_t4_m7_i7 :=
  replay_concat (ms₁ := (ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3))) (ms₂ := ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) (P := ac7_fam_k13_t4_m7_s) (R := ac7_fam_k13_t4_m7_i3) (S := ac7_fam_k13_t4_m7_i7) ac7_fam_k13_t4_m7_k0_3 ac7_fam_k13_t4_m7_k3_7
theorem ac7_fam_k13_t4_m7_k8_10 : replay (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10) ac7_fam_k13_t4_m7_i8 = some ac7_fam_k13_t4_m7_i10 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c9) (ms₂ := ac7_fam_k13_t4_m7_c10) (P := ac7_fam_k13_t4_m7_i8) (R := ac7_fam_k13_t4_m7_i9) (S := ac7_fam_k13_t4_m7_i10) ac7_fam_k13_t4_m7_b9 ac7_fam_k13_t4_m7_b10
theorem ac7_fam_k13_t4_m7_k7_10 : replay (ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ac7_fam_k13_t4_m7_i7 = some ac7_fam_k13_t4_m7_i10 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c8) (ms₂ := (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) (P := ac7_fam_k13_t4_m7_i7) (R := ac7_fam_k13_t4_m7_i8) (S := ac7_fam_k13_t4_m7_i10) ac7_fam_k13_t4_m7_b8 ac7_fam_k13_t4_m7_k8_10
theorem ac7_fam_k13_t4_m7_k10_12 : replay (ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ac7_fam_k13_t4_m7_i10 = some ac7_fam_k13_t4_m7_i12 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c11) (ms₂ := ac7_fam_k13_t4_m7_c12) (P := ac7_fam_k13_t4_m7_i10) (R := ac7_fam_k13_t4_m7_i11) (S := ac7_fam_k13_t4_m7_i12) ac7_fam_k13_t4_m7_b11 ac7_fam_k13_t4_m7_b12
theorem ac7_fam_k13_t4_m7_k12_14 : replay (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14) ac7_fam_k13_t4_m7_i12 = some ac7_fam_k13_t4_m7_i14 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c13) (ms₂ := ac7_fam_k13_t4_m7_c14) (P := ac7_fam_k13_t4_m7_i12) (R := ac7_fam_k13_t4_m7_i13) (S := ac7_fam_k13_t4_m7_i14) ac7_fam_k13_t4_m7_b13 ac7_fam_k13_t4_m7_b14
theorem ac7_fam_k13_t4_m7_k10_14 : replay ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)) ac7_fam_k13_t4_m7_i10 = some ac7_fam_k13_t4_m7_i14 :=
  replay_concat (ms₁ := (ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12)) (ms₂ := (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)) (P := ac7_fam_k13_t4_m7_i10) (R := ac7_fam_k13_t4_m7_i12) (S := ac7_fam_k13_t4_m7_i14) ac7_fam_k13_t4_m7_k10_12 ac7_fam_k13_t4_m7_k12_14
theorem ac7_fam_k13_t4_m7_k7_14 : replay ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14))) ac7_fam_k13_t4_m7_i7 = some ac7_fam_k13_t4_m7_i14 :=
  replay_concat (ms₁ := (ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10))) (ms₂ := ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14))) (P := ac7_fam_k13_t4_m7_i7) (R := ac7_fam_k13_t4_m7_i10) (S := ac7_fam_k13_t4_m7_i14) ac7_fam_k13_t4_m7_k7_10 ac7_fam_k13_t4_m7_k10_14
theorem ac7_fam_k13_t4_m7_k0_14 : replay (((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) ++ ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)))) ac7_fam_k13_t4_m7_s = some ac7_fam_k13_t4_m7_i14 :=
  replay_concat (ms₁ := ((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7)))) (ms₂ := ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)))) (P := ac7_fam_k13_t4_m7_s) (R := ac7_fam_k13_t4_m7_i7) (S := ac7_fam_k13_t4_m7_i14) ac7_fam_k13_t4_m7_k0_7 ac7_fam_k13_t4_m7_k7_14
theorem ac7_fam_k13_t4_m7_k15_17 : replay (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17) ac7_fam_k13_t4_m7_i15 = some ac7_fam_k13_t4_m7_i17 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c16) (ms₂ := ac7_fam_k13_t4_m7_c17) (P := ac7_fam_k13_t4_m7_i15) (R := ac7_fam_k13_t4_m7_i16) (S := ac7_fam_k13_t4_m7_i17) ac7_fam_k13_t4_m7_b16 ac7_fam_k13_t4_m7_b17
theorem ac7_fam_k13_t4_m7_k14_17 : replay (ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ac7_fam_k13_t4_m7_i14 = some ac7_fam_k13_t4_m7_i17 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c15) (ms₂ := (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) (P := ac7_fam_k13_t4_m7_i14) (R := ac7_fam_k13_t4_m7_i15) (S := ac7_fam_k13_t4_m7_i17) ac7_fam_k13_t4_m7_b15 ac7_fam_k13_t4_m7_k15_17
theorem ac7_fam_k13_t4_m7_k17_19 : replay (ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ac7_fam_k13_t4_m7_i17 = some ac7_fam_k13_t4_m7_i19 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c18) (ms₂ := ac7_fam_k13_t4_m7_c19) (P := ac7_fam_k13_t4_m7_i17) (R := ac7_fam_k13_t4_m7_i18) (S := ac7_fam_k13_t4_m7_i19) ac7_fam_k13_t4_m7_b18 ac7_fam_k13_t4_m7_b19
theorem ac7_fam_k13_t4_m7_k19_21 : replay (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21) ac7_fam_k13_t4_m7_i19 = some ac7_fam_k13_t4_m7_i21 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c20) (ms₂ := ac7_fam_k13_t4_m7_c21) (P := ac7_fam_k13_t4_m7_i19) (R := ac7_fam_k13_t4_m7_i20) (S := ac7_fam_k13_t4_m7_i21) ac7_fam_k13_t4_m7_b20 ac7_fam_k13_t4_m7_b21
theorem ac7_fam_k13_t4_m7_k17_21 : replay ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21)) ac7_fam_k13_t4_m7_i17 = some ac7_fam_k13_t4_m7_i21 :=
  replay_concat (ms₁ := (ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19)) (ms₂ := (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21)) (P := ac7_fam_k13_t4_m7_i17) (R := ac7_fam_k13_t4_m7_i19) (S := ac7_fam_k13_t4_m7_i21) ac7_fam_k13_t4_m7_k17_19 ac7_fam_k13_t4_m7_k19_21
theorem ac7_fam_k13_t4_m7_k14_21 : replay ((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) ac7_fam_k13_t4_m7_i14 = some ac7_fam_k13_t4_m7_i21 :=
  replay_concat (ms₁ := (ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17))) (ms₂ := ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) (P := ac7_fam_k13_t4_m7_i14) (R := ac7_fam_k13_t4_m7_i17) (S := ac7_fam_k13_t4_m7_i21) ac7_fam_k13_t4_m7_k14_17 ac7_fam_k13_t4_m7_k17_21
theorem ac7_fam_k13_t4_m7_k22_24 : replay (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24) ac7_fam_k13_t4_m7_i22 = some ac7_fam_k13_t4_m7_i24 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c23) (ms₂ := ac7_fam_k13_t4_m7_c24) (P := ac7_fam_k13_t4_m7_i22) (R := ac7_fam_k13_t4_m7_i23) (S := ac7_fam_k13_t4_m7_i24) ac7_fam_k13_t4_m7_b23 ac7_fam_k13_t4_m7_b24
theorem ac7_fam_k13_t4_m7_k21_24 : replay (ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ac7_fam_k13_t4_m7_i21 = some ac7_fam_k13_t4_m7_i24 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c22) (ms₂ := (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) (P := ac7_fam_k13_t4_m7_i21) (R := ac7_fam_k13_t4_m7_i22) (S := ac7_fam_k13_t4_m7_i24) ac7_fam_k13_t4_m7_b22 ac7_fam_k13_t4_m7_k22_24
theorem ac7_fam_k13_t4_m7_k24_26 : replay (ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ac7_fam_k13_t4_m7_i24 = some ac7_fam_k13_t4_m7_i26 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c25) (ms₂ := ac7_fam_k13_t4_m7_c26) (P := ac7_fam_k13_t4_m7_i24) (R := ac7_fam_k13_t4_m7_i25) (S := ac7_fam_k13_t4_m7_i26) ac7_fam_k13_t4_m7_b25 ac7_fam_k13_t4_m7_b26
theorem ac7_fam_k13_t4_m7_k26_28 : replay (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28) ac7_fam_k13_t4_m7_i26 = some ac7_fam_k13_t4_m7_i28 :=
  replay_concat (ms₁ := ac7_fam_k13_t4_m7_c27) (ms₂ := ac7_fam_k13_t4_m7_c28) (P := ac7_fam_k13_t4_m7_i26) (R := ac7_fam_k13_t4_m7_i27) (S := ac7_fam_k13_t4_m7_i28) ac7_fam_k13_t4_m7_b27 ac7_fam_k13_t4_m7_b28
theorem ac7_fam_k13_t4_m7_k24_28 : replay ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28)) ac7_fam_k13_t4_m7_i24 = some ac7_fam_k13_t4_m7_i28 :=
  replay_concat (ms₁ := (ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26)) (ms₂ := (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28)) (P := ac7_fam_k13_t4_m7_i24) (R := ac7_fam_k13_t4_m7_i26) (S := ac7_fam_k13_t4_m7_i28) ac7_fam_k13_t4_m7_k24_26 ac7_fam_k13_t4_m7_k26_28
theorem ac7_fam_k13_t4_m7_k21_28 : replay ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28))) ac7_fam_k13_t4_m7_i21 = some ac7_fam_k13_t4_m7_i28 :=
  replay_concat (ms₁ := (ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24))) (ms₂ := ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28))) (P := ac7_fam_k13_t4_m7_i21) (R := ac7_fam_k13_t4_m7_i24) (S := ac7_fam_k13_t4_m7_i28) ac7_fam_k13_t4_m7_k21_24 ac7_fam_k13_t4_m7_k24_28
theorem ac7_fam_k13_t4_m7_k14_28 : replay (((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) ++ ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28)))) ac7_fam_k13_t4_m7_i14 = some ac7_fam_k13_t4_m7_i28 :=
  replay_concat (ms₁ := ((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21)))) (ms₂ := ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28)))) (P := ac7_fam_k13_t4_m7_i14) (R := ac7_fam_k13_t4_m7_i21) (S := ac7_fam_k13_t4_m7_i28) ac7_fam_k13_t4_m7_k14_21 ac7_fam_k13_t4_m7_k21_28
theorem ac7_fam_k13_t4_m7_k0_28 : replay ((((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) ++ ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)))) ++ (((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) ++ ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28))))) ac7_fam_k13_t4_m7_s = some ac7_fam_k13_t4_m7_i28 :=
  replay_concat (ms₁ := (((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) ++ ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14))))) (ms₂ := (((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) ++ ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28))))) (P := ac7_fam_k13_t4_m7_s) (R := ac7_fam_k13_t4_m7_i14) (S := ac7_fam_k13_t4_m7_i28) ac7_fam_k13_t4_m7_k0_14 ac7_fam_k13_t4_m7_k14_28

/-- `fam_k13_t4_m7.cert` checked: replaying its 56 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k13_t4_m7_replay : replay ((((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) ++ ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)))) ++ (((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) ++ ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28))))) ac7_fam_k13_t4_m7_s = some ac7_fam_k13_t4_m7_i28 := ac7_fam_k13_t4_m7_k0_28

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k13_t4_m7_checked : checkCert ((((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) ++ ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)))) ++ (((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) ++ ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28))))) ac7_fam_k13_t4_m7_s ac7_fam_k13_t4_m7_i28 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k13_t4_m7_replay

/-- The endpoints of `fam_k13_t4_m7.cert` are the presentations `<x,y | x^13, y^7, [x^1,y]>`
    and `<x,y | x^13, y^7, [x^3,y]>` of the statement. -/
theorem ac7_fam_k13_t4_m7_endpoints :
    metz 13 7 1 = ac7_fam_k13_t4_m7_s ∧ metz 13 7 3 = ac7_fam_k13_t4_m7_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 56-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k13_t4_m7_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 13 7 1) = some (metz 13 7 3) := by
  refine ⟨((((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) ++ ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)))) ++ (((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) ++ ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28))))), ?_⟩
  calc replay ((((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) ++ ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)))) ++ (((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) ++ ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28))))) (metz 13 7 1) = replay ((((ac7_fam_k13_t4_m7_c1 ++ (ac7_fam_k13_t4_m7_c2 ++ ac7_fam_k13_t4_m7_c3)) ++ ((ac7_fam_k13_t4_m7_c4 ++ ac7_fam_k13_t4_m7_c5) ++ (ac7_fam_k13_t4_m7_c6 ++ ac7_fam_k13_t4_m7_c7))) ++ ((ac7_fam_k13_t4_m7_c8 ++ (ac7_fam_k13_t4_m7_c9 ++ ac7_fam_k13_t4_m7_c10)) ++ ((ac7_fam_k13_t4_m7_c11 ++ ac7_fam_k13_t4_m7_c12) ++ (ac7_fam_k13_t4_m7_c13 ++ ac7_fam_k13_t4_m7_c14)))) ++ (((ac7_fam_k13_t4_m7_c15 ++ (ac7_fam_k13_t4_m7_c16 ++ ac7_fam_k13_t4_m7_c17)) ++ ((ac7_fam_k13_t4_m7_c18 ++ ac7_fam_k13_t4_m7_c19) ++ (ac7_fam_k13_t4_m7_c20 ++ ac7_fam_k13_t4_m7_c21))) ++ ((ac7_fam_k13_t4_m7_c22 ++ (ac7_fam_k13_t4_m7_c23 ++ ac7_fam_k13_t4_m7_c24)) ++ ((ac7_fam_k13_t4_m7_c25 ++ ac7_fam_k13_t4_m7_c26) ++ (ac7_fam_k13_t4_m7_c27 ++ ac7_fam_k13_t4_m7_c28))))) ac7_fam_k13_t4_m7_s := by rw [ac7_fam_k13_t4_m7_endpoints.1]
    _ = some ac7_fam_k13_t4_m7_e := ac7_fam_k13_t4_m7_replay
    _ = some (metz 13 7 3) := by rw [ac7_fam_k13_t4_m7_endpoints.2]

/-! ### `fam_k5_t1_m5.cert`: Metzler family, k=5 t=1 m=5  <x,y | x^5, y^5, [x,y]>  ->  <x,y | x^5, y^5, [x^4,y]>. -/

/-- The start tuple of `fam_k5_t1_m5.cert` (48 Q**-moves to the end tuple). -/
def ac7_fam_k5_t1_m5_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k5_t1_m5_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k5_t1_m5_i2 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k5_t1_m5_i3 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (2, true), (0, true), (0, true)]]
def ac7_fam_k5_t1_m5_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k5_t1_m5_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (2, true), (0, true)]]
def ac7_fam_k5_t1_m5_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (2, true)]]
def ac7_fam_k5_t1_m5_i7 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k5_t1_m5_i8 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t1_m5_i9 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t1_m5_i10 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t1_m5_i11 : QPres := mkQPres 3 4 [[(2, false), (2, false), (2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t1_m5_i12 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t1_m5_i13 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t1_m5_i14 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k5_t1_m5_i15 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k5_t1_m5_i16 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k5_t1_m5_i17 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k5_t1_m5_i18 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k5_t1_m5_i19 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k5_t1_m5_i20 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k5_t1_m5_i21 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k5_t1_m5_i22 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k5_t1_m5_i23 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k5_t1_m5_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)]]
def ac7_fam_k5_t1_m5_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)]]

def ac7_fam_k5_t1_m5_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k5_t1_m5_c2 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k5_t1_m5_c3 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false)] ]
def ac7_fam_k5_t1_m5_c4 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true)] ]
def ac7_fam_k5_t1_m5_c5 : List QMove :=
  [ .conj 3 [(0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k5_t1_m5_c6 : List QMove :=
  [ .conj 3 [(0, true), (0, true)],
    .conj 3 [(0, false)] ]
def ac7_fam_k5_t1_m5_c7 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true)] ]
def ac7_fam_k5_t1_m5_c8 : List QMove :=
  [ .conj 0 [(2, true), (2, true), (2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k5_t1_m5_c9 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false)],
    .conj 0 [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true)] ]
def ac7_fam_k5_t1_m5_c10 : List QMove :=
  [ .lmul 2 0,
    .conj 0 [(2, false), (2, false), (2, false), (2, false), (1, false), (0, false)] ]
def ac7_fam_k5_t1_m5_c11 : List QMove :=
  [ .inv 0,
    .lmul 2 0 ]
def ac7_fam_k5_t1_m5_c12 : List QMove :=
  [ .inv 0,
    .nijinv 0 2 ]
def ac7_fam_k5_t1_m5_c13 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k5_t1_m5_c14 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k5_t1_m5_c15 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true), (1, true), (1, true)] ]
def ac7_fam_k5_t1_m5_c16 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k5_t1_m5_c17 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k5_t1_m5_c18 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k5_t1_m5_c19 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k5_t1_m5_c20 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false)] ]
def ac7_fam_k5_t1_m5_c21 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k5_t1_m5_c22 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k5_t1_m5_c23 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k5_t1_m5_c24 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b1 :
    replay ac7_fam_k5_t1_m5_c1 ac7_fam_k5_t1_m5_s = some ac7_fam_k5_t1_m5_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b2 :
    replay ac7_fam_k5_t1_m5_c2 ac7_fam_k5_t1_m5_i1 = some ac7_fam_k5_t1_m5_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b3 :
    replay ac7_fam_k5_t1_m5_c3 ac7_fam_k5_t1_m5_i2 = some ac7_fam_k5_t1_m5_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b4 :
    replay ac7_fam_k5_t1_m5_c4 ac7_fam_k5_t1_m5_i3 = some ac7_fam_k5_t1_m5_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b5 :
    replay ac7_fam_k5_t1_m5_c5 ac7_fam_k5_t1_m5_i4 = some ac7_fam_k5_t1_m5_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b6 :
    replay ac7_fam_k5_t1_m5_c6 ac7_fam_k5_t1_m5_i5 = some ac7_fam_k5_t1_m5_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b7 :
    replay ac7_fam_k5_t1_m5_c7 ac7_fam_k5_t1_m5_i6 = some ac7_fam_k5_t1_m5_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b8 :
    replay ac7_fam_k5_t1_m5_c8 ac7_fam_k5_t1_m5_i7 = some ac7_fam_k5_t1_m5_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b9 :
    replay ac7_fam_k5_t1_m5_c9 ac7_fam_k5_t1_m5_i8 = some ac7_fam_k5_t1_m5_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b10 :
    replay ac7_fam_k5_t1_m5_c10 ac7_fam_k5_t1_m5_i9 = some ac7_fam_k5_t1_m5_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b11 :
    replay ac7_fam_k5_t1_m5_c11 ac7_fam_k5_t1_m5_i10 = some ac7_fam_k5_t1_m5_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b12 :
    replay ac7_fam_k5_t1_m5_c12 ac7_fam_k5_t1_m5_i11 = some ac7_fam_k5_t1_m5_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b13 :
    replay ac7_fam_k5_t1_m5_c13 ac7_fam_k5_t1_m5_i12 = some ac7_fam_k5_t1_m5_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b14 :
    replay ac7_fam_k5_t1_m5_c14 ac7_fam_k5_t1_m5_i13 = some ac7_fam_k5_t1_m5_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b15 :
    replay ac7_fam_k5_t1_m5_c15 ac7_fam_k5_t1_m5_i14 = some ac7_fam_k5_t1_m5_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b16 :
    replay ac7_fam_k5_t1_m5_c16 ac7_fam_k5_t1_m5_i15 = some ac7_fam_k5_t1_m5_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b17 :
    replay ac7_fam_k5_t1_m5_c17 ac7_fam_k5_t1_m5_i16 = some ac7_fam_k5_t1_m5_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b18 :
    replay ac7_fam_k5_t1_m5_c18 ac7_fam_k5_t1_m5_i17 = some ac7_fam_k5_t1_m5_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b19 :
    replay ac7_fam_k5_t1_m5_c19 ac7_fam_k5_t1_m5_i18 = some ac7_fam_k5_t1_m5_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b20 :
    replay ac7_fam_k5_t1_m5_c20 ac7_fam_k5_t1_m5_i19 = some ac7_fam_k5_t1_m5_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b21 :
    replay ac7_fam_k5_t1_m5_c21 ac7_fam_k5_t1_m5_i20 = some ac7_fam_k5_t1_m5_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b22 :
    replay ac7_fam_k5_t1_m5_c22 ac7_fam_k5_t1_m5_i21 = some ac7_fam_k5_t1_m5_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b23 :
    replay ac7_fam_k5_t1_m5_c23 ac7_fam_k5_t1_m5_i22 = some ac7_fam_k5_t1_m5_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t1_m5_b24 :
    replay ac7_fam_k5_t1_m5_c24 ac7_fam_k5_t1_m5_i23 = some ac7_fam_k5_t1_m5_i24 := by decide

theorem ac7_fam_k5_t1_m5_k1_3 : replay (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3) ac7_fam_k5_t1_m5_i1 = some ac7_fam_k5_t1_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c2) (ms₂ := ac7_fam_k5_t1_m5_c3) (P := ac7_fam_k5_t1_m5_i1) (R := ac7_fam_k5_t1_m5_i2) (S := ac7_fam_k5_t1_m5_i3) ac7_fam_k5_t1_m5_b2 ac7_fam_k5_t1_m5_b3
theorem ac7_fam_k5_t1_m5_k0_3 : replay (ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ac7_fam_k5_t1_m5_s = some ac7_fam_k5_t1_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c1) (ms₂ := (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) (P := ac7_fam_k5_t1_m5_s) (R := ac7_fam_k5_t1_m5_i1) (S := ac7_fam_k5_t1_m5_i3) ac7_fam_k5_t1_m5_b1 ac7_fam_k5_t1_m5_k1_3
theorem ac7_fam_k5_t1_m5_k4_6 : replay (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6) ac7_fam_k5_t1_m5_i4 = some ac7_fam_k5_t1_m5_i6 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c5) (ms₂ := ac7_fam_k5_t1_m5_c6) (P := ac7_fam_k5_t1_m5_i4) (R := ac7_fam_k5_t1_m5_i5) (S := ac7_fam_k5_t1_m5_i6) ac7_fam_k5_t1_m5_b5 ac7_fam_k5_t1_m5_b6
theorem ac7_fam_k5_t1_m5_k3_6 : replay (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6)) ac7_fam_k5_t1_m5_i3 = some ac7_fam_k5_t1_m5_i6 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c4) (ms₂ := (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6)) (P := ac7_fam_k5_t1_m5_i3) (R := ac7_fam_k5_t1_m5_i4) (S := ac7_fam_k5_t1_m5_i6) ac7_fam_k5_t1_m5_b4 ac7_fam_k5_t1_m5_k4_6
theorem ac7_fam_k5_t1_m5_k0_6 : replay ((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) ac7_fam_k5_t1_m5_s = some ac7_fam_k5_t1_m5_i6 :=
  replay_concat (ms₁ := (ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3))) (ms₂ := (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) (P := ac7_fam_k5_t1_m5_s) (R := ac7_fam_k5_t1_m5_i3) (S := ac7_fam_k5_t1_m5_i6) ac7_fam_k5_t1_m5_k0_3 ac7_fam_k5_t1_m5_k3_6
theorem ac7_fam_k5_t1_m5_k7_9 : replay (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9) ac7_fam_k5_t1_m5_i7 = some ac7_fam_k5_t1_m5_i9 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c8) (ms₂ := ac7_fam_k5_t1_m5_c9) (P := ac7_fam_k5_t1_m5_i7) (R := ac7_fam_k5_t1_m5_i8) (S := ac7_fam_k5_t1_m5_i9) ac7_fam_k5_t1_m5_b8 ac7_fam_k5_t1_m5_b9
theorem ac7_fam_k5_t1_m5_k6_9 : replay (ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ac7_fam_k5_t1_m5_i6 = some ac7_fam_k5_t1_m5_i9 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c7) (ms₂ := (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) (P := ac7_fam_k5_t1_m5_i6) (R := ac7_fam_k5_t1_m5_i7) (S := ac7_fam_k5_t1_m5_i9) ac7_fam_k5_t1_m5_b7 ac7_fam_k5_t1_m5_k7_9
theorem ac7_fam_k5_t1_m5_k10_12 : replay (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12) ac7_fam_k5_t1_m5_i10 = some ac7_fam_k5_t1_m5_i12 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c11) (ms₂ := ac7_fam_k5_t1_m5_c12) (P := ac7_fam_k5_t1_m5_i10) (R := ac7_fam_k5_t1_m5_i11) (S := ac7_fam_k5_t1_m5_i12) ac7_fam_k5_t1_m5_b11 ac7_fam_k5_t1_m5_b12
theorem ac7_fam_k5_t1_m5_k9_12 : replay (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)) ac7_fam_k5_t1_m5_i9 = some ac7_fam_k5_t1_m5_i12 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c10) (ms₂ := (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)) (P := ac7_fam_k5_t1_m5_i9) (R := ac7_fam_k5_t1_m5_i10) (S := ac7_fam_k5_t1_m5_i12) ac7_fam_k5_t1_m5_b10 ac7_fam_k5_t1_m5_k10_12
theorem ac7_fam_k5_t1_m5_k6_12 : replay ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12))) ac7_fam_k5_t1_m5_i6 = some ac7_fam_k5_t1_m5_i12 :=
  replay_concat (ms₁ := (ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9))) (ms₂ := (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12))) (P := ac7_fam_k5_t1_m5_i6) (R := ac7_fam_k5_t1_m5_i9) (S := ac7_fam_k5_t1_m5_i12) ac7_fam_k5_t1_m5_k6_9 ac7_fam_k5_t1_m5_k9_12
theorem ac7_fam_k5_t1_m5_k0_12 : replay (((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) ++ ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)))) ac7_fam_k5_t1_m5_s = some ac7_fam_k5_t1_m5_i12 :=
  replay_concat (ms₁ := ((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6)))) (ms₂ := ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)))) (P := ac7_fam_k5_t1_m5_s) (R := ac7_fam_k5_t1_m5_i6) (S := ac7_fam_k5_t1_m5_i12) ac7_fam_k5_t1_m5_k0_6 ac7_fam_k5_t1_m5_k6_12
theorem ac7_fam_k5_t1_m5_k13_15 : replay (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15) ac7_fam_k5_t1_m5_i13 = some ac7_fam_k5_t1_m5_i15 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c14) (ms₂ := ac7_fam_k5_t1_m5_c15) (P := ac7_fam_k5_t1_m5_i13) (R := ac7_fam_k5_t1_m5_i14) (S := ac7_fam_k5_t1_m5_i15) ac7_fam_k5_t1_m5_b14 ac7_fam_k5_t1_m5_b15
theorem ac7_fam_k5_t1_m5_k12_15 : replay (ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ac7_fam_k5_t1_m5_i12 = some ac7_fam_k5_t1_m5_i15 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c13) (ms₂ := (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) (P := ac7_fam_k5_t1_m5_i12) (R := ac7_fam_k5_t1_m5_i13) (S := ac7_fam_k5_t1_m5_i15) ac7_fam_k5_t1_m5_b13 ac7_fam_k5_t1_m5_k13_15
theorem ac7_fam_k5_t1_m5_k16_18 : replay (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18) ac7_fam_k5_t1_m5_i16 = some ac7_fam_k5_t1_m5_i18 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c17) (ms₂ := ac7_fam_k5_t1_m5_c18) (P := ac7_fam_k5_t1_m5_i16) (R := ac7_fam_k5_t1_m5_i17) (S := ac7_fam_k5_t1_m5_i18) ac7_fam_k5_t1_m5_b17 ac7_fam_k5_t1_m5_b18
theorem ac7_fam_k5_t1_m5_k15_18 : replay (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18)) ac7_fam_k5_t1_m5_i15 = some ac7_fam_k5_t1_m5_i18 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c16) (ms₂ := (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18)) (P := ac7_fam_k5_t1_m5_i15) (R := ac7_fam_k5_t1_m5_i16) (S := ac7_fam_k5_t1_m5_i18) ac7_fam_k5_t1_m5_b16 ac7_fam_k5_t1_m5_k16_18
theorem ac7_fam_k5_t1_m5_k12_18 : replay ((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) ac7_fam_k5_t1_m5_i12 = some ac7_fam_k5_t1_m5_i18 :=
  replay_concat (ms₁ := (ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15))) (ms₂ := (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) (P := ac7_fam_k5_t1_m5_i12) (R := ac7_fam_k5_t1_m5_i15) (S := ac7_fam_k5_t1_m5_i18) ac7_fam_k5_t1_m5_k12_15 ac7_fam_k5_t1_m5_k15_18
theorem ac7_fam_k5_t1_m5_k19_21 : replay (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21) ac7_fam_k5_t1_m5_i19 = some ac7_fam_k5_t1_m5_i21 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c20) (ms₂ := ac7_fam_k5_t1_m5_c21) (P := ac7_fam_k5_t1_m5_i19) (R := ac7_fam_k5_t1_m5_i20) (S := ac7_fam_k5_t1_m5_i21) ac7_fam_k5_t1_m5_b20 ac7_fam_k5_t1_m5_b21
theorem ac7_fam_k5_t1_m5_k18_21 : replay (ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ac7_fam_k5_t1_m5_i18 = some ac7_fam_k5_t1_m5_i21 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c19) (ms₂ := (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) (P := ac7_fam_k5_t1_m5_i18) (R := ac7_fam_k5_t1_m5_i19) (S := ac7_fam_k5_t1_m5_i21) ac7_fam_k5_t1_m5_b19 ac7_fam_k5_t1_m5_k19_21
theorem ac7_fam_k5_t1_m5_k22_24 : replay (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24) ac7_fam_k5_t1_m5_i22 = some ac7_fam_k5_t1_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c23) (ms₂ := ac7_fam_k5_t1_m5_c24) (P := ac7_fam_k5_t1_m5_i22) (R := ac7_fam_k5_t1_m5_i23) (S := ac7_fam_k5_t1_m5_i24) ac7_fam_k5_t1_m5_b23 ac7_fam_k5_t1_m5_b24
theorem ac7_fam_k5_t1_m5_k21_24 : replay (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24)) ac7_fam_k5_t1_m5_i21 = some ac7_fam_k5_t1_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k5_t1_m5_c22) (ms₂ := (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24)) (P := ac7_fam_k5_t1_m5_i21) (R := ac7_fam_k5_t1_m5_i22) (S := ac7_fam_k5_t1_m5_i24) ac7_fam_k5_t1_m5_b22 ac7_fam_k5_t1_m5_k22_24
theorem ac7_fam_k5_t1_m5_k18_24 : replay ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24))) ac7_fam_k5_t1_m5_i18 = some ac7_fam_k5_t1_m5_i24 :=
  replay_concat (ms₁ := (ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21))) (ms₂ := (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24))) (P := ac7_fam_k5_t1_m5_i18) (R := ac7_fam_k5_t1_m5_i21) (S := ac7_fam_k5_t1_m5_i24) ac7_fam_k5_t1_m5_k18_21 ac7_fam_k5_t1_m5_k21_24
theorem ac7_fam_k5_t1_m5_k12_24 : replay (((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) ++ ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24)))) ac7_fam_k5_t1_m5_i12 = some ac7_fam_k5_t1_m5_i24 :=
  replay_concat (ms₁ := ((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18)))) (ms₂ := ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24)))) (P := ac7_fam_k5_t1_m5_i12) (R := ac7_fam_k5_t1_m5_i18) (S := ac7_fam_k5_t1_m5_i24) ac7_fam_k5_t1_m5_k12_18 ac7_fam_k5_t1_m5_k18_24
theorem ac7_fam_k5_t1_m5_k0_24 : replay ((((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) ++ ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)))) ++ (((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) ++ ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24))))) ac7_fam_k5_t1_m5_s = some ac7_fam_k5_t1_m5_i24 :=
  replay_concat (ms₁ := (((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) ++ ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12))))) (ms₂ := (((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) ++ ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24))))) (P := ac7_fam_k5_t1_m5_s) (R := ac7_fam_k5_t1_m5_i12) (S := ac7_fam_k5_t1_m5_i24) ac7_fam_k5_t1_m5_k0_12 ac7_fam_k5_t1_m5_k12_24

/-- `fam_k5_t1_m5.cert` checked: replaying its 48 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k5_t1_m5_replay : replay ((((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) ++ ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)))) ++ (((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) ++ ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24))))) ac7_fam_k5_t1_m5_s = some ac7_fam_k5_t1_m5_i24 := ac7_fam_k5_t1_m5_k0_24

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k5_t1_m5_checked : checkCert ((((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) ++ ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)))) ++ (((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) ++ ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24))))) ac7_fam_k5_t1_m5_s ac7_fam_k5_t1_m5_i24 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k5_t1_m5_replay

/-- The endpoints of `fam_k5_t1_m5.cert` are the presentations `<x,y | x^5, y^5, [x^1,y]>`
    and `<x,y | x^5, y^5, [x^4,y]>` of the statement. -/
theorem ac7_fam_k5_t1_m5_endpoints :
    metz 5 5 1 = ac7_fam_k5_t1_m5_s ∧ metz 5 5 4 = ac7_fam_k5_t1_m5_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 48-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k5_t1_m5_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 5 5 1) = some (metz 5 5 4) := by
  refine ⟨((((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) ++ ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)))) ++ (((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) ++ ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24))))), ?_⟩
  calc replay ((((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) ++ ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)))) ++ (((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) ++ ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24))))) (metz 5 5 1) = replay ((((ac7_fam_k5_t1_m5_c1 ++ (ac7_fam_k5_t1_m5_c2 ++ ac7_fam_k5_t1_m5_c3)) ++ (ac7_fam_k5_t1_m5_c4 ++ (ac7_fam_k5_t1_m5_c5 ++ ac7_fam_k5_t1_m5_c6))) ++ ((ac7_fam_k5_t1_m5_c7 ++ (ac7_fam_k5_t1_m5_c8 ++ ac7_fam_k5_t1_m5_c9)) ++ (ac7_fam_k5_t1_m5_c10 ++ (ac7_fam_k5_t1_m5_c11 ++ ac7_fam_k5_t1_m5_c12)))) ++ (((ac7_fam_k5_t1_m5_c13 ++ (ac7_fam_k5_t1_m5_c14 ++ ac7_fam_k5_t1_m5_c15)) ++ (ac7_fam_k5_t1_m5_c16 ++ (ac7_fam_k5_t1_m5_c17 ++ ac7_fam_k5_t1_m5_c18))) ++ ((ac7_fam_k5_t1_m5_c19 ++ (ac7_fam_k5_t1_m5_c20 ++ ac7_fam_k5_t1_m5_c21)) ++ (ac7_fam_k5_t1_m5_c22 ++ (ac7_fam_k5_t1_m5_c23 ++ ac7_fam_k5_t1_m5_c24))))) ac7_fam_k5_t1_m5_s := by rw [ac7_fam_k5_t1_m5_endpoints.1]
    _ = some ac7_fam_k5_t1_m5_e := ac7_fam_k5_t1_m5_replay
    _ = some (metz 5 5 4) := by rw [ac7_fam_k5_t1_m5_endpoints.2]

/-! ### `fam_k5_t2_m5.cert`: Metzler family, k=5 t=2 m=5  <x,y | x^5, y^5, [x,y]>  ->  <x,y | x^5, y^5, [x^2,y]>. -/

/-- The start tuple of `fam_k5_t2_m5.cert` (44 Q**-moves to the end tuple). -/
def ac7_fam_k5_t2_m5_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k5_t2_m5_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k5_t2_m5_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true)]]
def ac7_fam_k5_t2_m5_i3 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k5_t2_m5_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (2, true)]]
def ac7_fam_k5_t2_m5_i5 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k5_t2_m5_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true)]]
def ac7_fam_k5_t2_m5_i7 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t2_m5_i8 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t2_m5_i9 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t2_m5_i10 : QPres := mkQPres 3 4 [[(2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t2_m5_i11 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t2_m5_i12 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (0, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k5_t2_m5_i13 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (0, true), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k5_t2_m5_i14 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k5_t2_m5_i15 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k5_t2_m5_i16 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k5_t2_m5_i17 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k5_t2_m5_i18 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k5_t2_m5_i19 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (1, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k5_t2_m5_i20 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_fam_k5_t2_m5_i21 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_fam_k5_t2_m5_i22 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]
def ac7_fam_k5_t2_m5_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]

def ac7_fam_k5_t2_m5_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k5_t2_m5_c2 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k5_t2_m5_c3 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k5_t2_m5_c4 : List QMove :=
  [ .conj 3 [(0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k5_t2_m5_c5 : List QMove :=
  [ .conj 3 [(0, true), (0, true)],
    .conj 0 [(2, true), (0, false), (2, true), (2, true)] ]
def ac7_fam_k5_t2_m5_c6 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (0, true), (2, false)] ]
def ac7_fam_k5_t2_m5_c7 : List QMove :=
  [ .conj 0 [(2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k5_t2_m5_c8 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false)],
    .conj 0 [(0, true), (1, true), (2, true), (2, true)] ]
def ac7_fam_k5_t2_m5_c9 : List QMove :=
  [ .lmul 2 0,
    .conj 0 [(2, false), (2, false), (1, false), (0, false)] ]
def ac7_fam_k5_t2_m5_c10 : List QMove :=
  [ .inv 0,
    .lmul 2 0 ]
def ac7_fam_k5_t2_m5_c11 : List QMove :=
  [ .inv 0,
    .nijinv 0 2 ]
def ac7_fam_k5_t2_m5_c12 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k5_t2_m5_c13 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true)] ]
def ac7_fam_k5_t2_m5_c14 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k5_t2_m5_c15 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k5_t2_m5_c16 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k5_t2_m5_c17 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k5_t2_m5_c18 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false)] ]
def ac7_fam_k5_t2_m5_c19 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k5_t2_m5_c20 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k5_t2_m5_c21 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)] ]
def ac7_fam_k5_t2_m5_c22 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b1 :
    replay ac7_fam_k5_t2_m5_c1 ac7_fam_k5_t2_m5_s = some ac7_fam_k5_t2_m5_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b2 :
    replay ac7_fam_k5_t2_m5_c2 ac7_fam_k5_t2_m5_i1 = some ac7_fam_k5_t2_m5_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b3 :
    replay ac7_fam_k5_t2_m5_c3 ac7_fam_k5_t2_m5_i2 = some ac7_fam_k5_t2_m5_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b4 :
    replay ac7_fam_k5_t2_m5_c4 ac7_fam_k5_t2_m5_i3 = some ac7_fam_k5_t2_m5_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b5 :
    replay ac7_fam_k5_t2_m5_c5 ac7_fam_k5_t2_m5_i4 = some ac7_fam_k5_t2_m5_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b6 :
    replay ac7_fam_k5_t2_m5_c6 ac7_fam_k5_t2_m5_i5 = some ac7_fam_k5_t2_m5_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b7 :
    replay ac7_fam_k5_t2_m5_c7 ac7_fam_k5_t2_m5_i6 = some ac7_fam_k5_t2_m5_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b8 :
    replay ac7_fam_k5_t2_m5_c8 ac7_fam_k5_t2_m5_i7 = some ac7_fam_k5_t2_m5_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b9 :
    replay ac7_fam_k5_t2_m5_c9 ac7_fam_k5_t2_m5_i8 = some ac7_fam_k5_t2_m5_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b10 :
    replay ac7_fam_k5_t2_m5_c10 ac7_fam_k5_t2_m5_i9 = some ac7_fam_k5_t2_m5_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b11 :
    replay ac7_fam_k5_t2_m5_c11 ac7_fam_k5_t2_m5_i10 = some ac7_fam_k5_t2_m5_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b12 :
    replay ac7_fam_k5_t2_m5_c12 ac7_fam_k5_t2_m5_i11 = some ac7_fam_k5_t2_m5_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b13 :
    replay ac7_fam_k5_t2_m5_c13 ac7_fam_k5_t2_m5_i12 = some ac7_fam_k5_t2_m5_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b14 :
    replay ac7_fam_k5_t2_m5_c14 ac7_fam_k5_t2_m5_i13 = some ac7_fam_k5_t2_m5_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b15 :
    replay ac7_fam_k5_t2_m5_c15 ac7_fam_k5_t2_m5_i14 = some ac7_fam_k5_t2_m5_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b16 :
    replay ac7_fam_k5_t2_m5_c16 ac7_fam_k5_t2_m5_i15 = some ac7_fam_k5_t2_m5_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b17 :
    replay ac7_fam_k5_t2_m5_c17 ac7_fam_k5_t2_m5_i16 = some ac7_fam_k5_t2_m5_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b18 :
    replay ac7_fam_k5_t2_m5_c18 ac7_fam_k5_t2_m5_i17 = some ac7_fam_k5_t2_m5_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b19 :
    replay ac7_fam_k5_t2_m5_c19 ac7_fam_k5_t2_m5_i18 = some ac7_fam_k5_t2_m5_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b20 :
    replay ac7_fam_k5_t2_m5_c20 ac7_fam_k5_t2_m5_i19 = some ac7_fam_k5_t2_m5_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b21 :
    replay ac7_fam_k5_t2_m5_c21 ac7_fam_k5_t2_m5_i20 = some ac7_fam_k5_t2_m5_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t2_m5_b22 :
    replay ac7_fam_k5_t2_m5_c22 ac7_fam_k5_t2_m5_i21 = some ac7_fam_k5_t2_m5_i22 := by decide

theorem ac7_fam_k5_t2_m5_k0_2 : replay (ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ac7_fam_k5_t2_m5_s = some ac7_fam_k5_t2_m5_i2 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c1) (ms₂ := ac7_fam_k5_t2_m5_c2) (P := ac7_fam_k5_t2_m5_s) (R := ac7_fam_k5_t2_m5_i1) (S := ac7_fam_k5_t2_m5_i2) ac7_fam_k5_t2_m5_b1 ac7_fam_k5_t2_m5_b2
theorem ac7_fam_k5_t2_m5_k3_5 : replay (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5) ac7_fam_k5_t2_m5_i3 = some ac7_fam_k5_t2_m5_i5 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c4) (ms₂ := ac7_fam_k5_t2_m5_c5) (P := ac7_fam_k5_t2_m5_i3) (R := ac7_fam_k5_t2_m5_i4) (S := ac7_fam_k5_t2_m5_i5) ac7_fam_k5_t2_m5_b4 ac7_fam_k5_t2_m5_b5
theorem ac7_fam_k5_t2_m5_k2_5 : replay (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5)) ac7_fam_k5_t2_m5_i2 = some ac7_fam_k5_t2_m5_i5 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c3) (ms₂ := (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5)) (P := ac7_fam_k5_t2_m5_i2) (R := ac7_fam_k5_t2_m5_i3) (S := ac7_fam_k5_t2_m5_i5) ac7_fam_k5_t2_m5_b3 ac7_fam_k5_t2_m5_k3_5
theorem ac7_fam_k5_t2_m5_k0_5 : replay ((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) ac7_fam_k5_t2_m5_s = some ac7_fam_k5_t2_m5_i5 :=
  replay_concat (ms₁ := (ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2)) (ms₂ := (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) (P := ac7_fam_k5_t2_m5_s) (R := ac7_fam_k5_t2_m5_i2) (S := ac7_fam_k5_t2_m5_i5) ac7_fam_k5_t2_m5_k0_2 ac7_fam_k5_t2_m5_k2_5
theorem ac7_fam_k5_t2_m5_k6_8 : replay (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8) ac7_fam_k5_t2_m5_i6 = some ac7_fam_k5_t2_m5_i8 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c7) (ms₂ := ac7_fam_k5_t2_m5_c8) (P := ac7_fam_k5_t2_m5_i6) (R := ac7_fam_k5_t2_m5_i7) (S := ac7_fam_k5_t2_m5_i8) ac7_fam_k5_t2_m5_b7 ac7_fam_k5_t2_m5_b8
theorem ac7_fam_k5_t2_m5_k5_8 : replay (ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ac7_fam_k5_t2_m5_i5 = some ac7_fam_k5_t2_m5_i8 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c6) (ms₂ := (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) (P := ac7_fam_k5_t2_m5_i5) (R := ac7_fam_k5_t2_m5_i6) (S := ac7_fam_k5_t2_m5_i8) ac7_fam_k5_t2_m5_b6 ac7_fam_k5_t2_m5_k6_8
theorem ac7_fam_k5_t2_m5_k9_11 : replay (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11) ac7_fam_k5_t2_m5_i9 = some ac7_fam_k5_t2_m5_i11 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c10) (ms₂ := ac7_fam_k5_t2_m5_c11) (P := ac7_fam_k5_t2_m5_i9) (R := ac7_fam_k5_t2_m5_i10) (S := ac7_fam_k5_t2_m5_i11) ac7_fam_k5_t2_m5_b10 ac7_fam_k5_t2_m5_b11
theorem ac7_fam_k5_t2_m5_k8_11 : replay (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)) ac7_fam_k5_t2_m5_i8 = some ac7_fam_k5_t2_m5_i11 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c9) (ms₂ := (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)) (P := ac7_fam_k5_t2_m5_i8) (R := ac7_fam_k5_t2_m5_i9) (S := ac7_fam_k5_t2_m5_i11) ac7_fam_k5_t2_m5_b9 ac7_fam_k5_t2_m5_k9_11
theorem ac7_fam_k5_t2_m5_k5_11 : replay ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11))) ac7_fam_k5_t2_m5_i5 = some ac7_fam_k5_t2_m5_i11 :=
  replay_concat (ms₁ := (ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8))) (ms₂ := (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11))) (P := ac7_fam_k5_t2_m5_i5) (R := ac7_fam_k5_t2_m5_i8) (S := ac7_fam_k5_t2_m5_i11) ac7_fam_k5_t2_m5_k5_8 ac7_fam_k5_t2_m5_k8_11
theorem ac7_fam_k5_t2_m5_k0_11 : replay (((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) ++ ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)))) ac7_fam_k5_t2_m5_s = some ac7_fam_k5_t2_m5_i11 :=
  replay_concat (ms₁ := ((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5)))) (ms₂ := ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)))) (P := ac7_fam_k5_t2_m5_s) (R := ac7_fam_k5_t2_m5_i5) (S := ac7_fam_k5_t2_m5_i11) ac7_fam_k5_t2_m5_k0_5 ac7_fam_k5_t2_m5_k5_11
theorem ac7_fam_k5_t2_m5_k11_13 : replay (ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ac7_fam_k5_t2_m5_i11 = some ac7_fam_k5_t2_m5_i13 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c12) (ms₂ := ac7_fam_k5_t2_m5_c13) (P := ac7_fam_k5_t2_m5_i11) (R := ac7_fam_k5_t2_m5_i12) (S := ac7_fam_k5_t2_m5_i13) ac7_fam_k5_t2_m5_b12 ac7_fam_k5_t2_m5_b13
theorem ac7_fam_k5_t2_m5_k14_16 : replay (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16) ac7_fam_k5_t2_m5_i14 = some ac7_fam_k5_t2_m5_i16 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c15) (ms₂ := ac7_fam_k5_t2_m5_c16) (P := ac7_fam_k5_t2_m5_i14) (R := ac7_fam_k5_t2_m5_i15) (S := ac7_fam_k5_t2_m5_i16) ac7_fam_k5_t2_m5_b15 ac7_fam_k5_t2_m5_b16
theorem ac7_fam_k5_t2_m5_k13_16 : replay (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16)) ac7_fam_k5_t2_m5_i13 = some ac7_fam_k5_t2_m5_i16 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c14) (ms₂ := (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16)) (P := ac7_fam_k5_t2_m5_i13) (R := ac7_fam_k5_t2_m5_i14) (S := ac7_fam_k5_t2_m5_i16) ac7_fam_k5_t2_m5_b14 ac7_fam_k5_t2_m5_k14_16
theorem ac7_fam_k5_t2_m5_k11_16 : replay ((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) ac7_fam_k5_t2_m5_i11 = some ac7_fam_k5_t2_m5_i16 :=
  replay_concat (ms₁ := (ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13)) (ms₂ := (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) (P := ac7_fam_k5_t2_m5_i11) (R := ac7_fam_k5_t2_m5_i13) (S := ac7_fam_k5_t2_m5_i16) ac7_fam_k5_t2_m5_k11_13 ac7_fam_k5_t2_m5_k13_16
theorem ac7_fam_k5_t2_m5_k17_19 : replay (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19) ac7_fam_k5_t2_m5_i17 = some ac7_fam_k5_t2_m5_i19 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c18) (ms₂ := ac7_fam_k5_t2_m5_c19) (P := ac7_fam_k5_t2_m5_i17) (R := ac7_fam_k5_t2_m5_i18) (S := ac7_fam_k5_t2_m5_i19) ac7_fam_k5_t2_m5_b18 ac7_fam_k5_t2_m5_b19
theorem ac7_fam_k5_t2_m5_k16_19 : replay (ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ac7_fam_k5_t2_m5_i16 = some ac7_fam_k5_t2_m5_i19 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c17) (ms₂ := (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) (P := ac7_fam_k5_t2_m5_i16) (R := ac7_fam_k5_t2_m5_i17) (S := ac7_fam_k5_t2_m5_i19) ac7_fam_k5_t2_m5_b17 ac7_fam_k5_t2_m5_k17_19
theorem ac7_fam_k5_t2_m5_k20_22 : replay (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22) ac7_fam_k5_t2_m5_i20 = some ac7_fam_k5_t2_m5_i22 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c21) (ms₂ := ac7_fam_k5_t2_m5_c22) (P := ac7_fam_k5_t2_m5_i20) (R := ac7_fam_k5_t2_m5_i21) (S := ac7_fam_k5_t2_m5_i22) ac7_fam_k5_t2_m5_b21 ac7_fam_k5_t2_m5_b22
theorem ac7_fam_k5_t2_m5_k19_22 : replay (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22)) ac7_fam_k5_t2_m5_i19 = some ac7_fam_k5_t2_m5_i22 :=
  replay_concat (ms₁ := ac7_fam_k5_t2_m5_c20) (ms₂ := (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22)) (P := ac7_fam_k5_t2_m5_i19) (R := ac7_fam_k5_t2_m5_i20) (S := ac7_fam_k5_t2_m5_i22) ac7_fam_k5_t2_m5_b20 ac7_fam_k5_t2_m5_k20_22
theorem ac7_fam_k5_t2_m5_k16_22 : replay ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22))) ac7_fam_k5_t2_m5_i16 = some ac7_fam_k5_t2_m5_i22 :=
  replay_concat (ms₁ := (ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19))) (ms₂ := (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22))) (P := ac7_fam_k5_t2_m5_i16) (R := ac7_fam_k5_t2_m5_i19) (S := ac7_fam_k5_t2_m5_i22) ac7_fam_k5_t2_m5_k16_19 ac7_fam_k5_t2_m5_k19_22
theorem ac7_fam_k5_t2_m5_k11_22 : replay (((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) ++ ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22)))) ac7_fam_k5_t2_m5_i11 = some ac7_fam_k5_t2_m5_i22 :=
  replay_concat (ms₁ := ((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16)))) (ms₂ := ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22)))) (P := ac7_fam_k5_t2_m5_i11) (R := ac7_fam_k5_t2_m5_i16) (S := ac7_fam_k5_t2_m5_i22) ac7_fam_k5_t2_m5_k11_16 ac7_fam_k5_t2_m5_k16_22
theorem ac7_fam_k5_t2_m5_k0_22 : replay ((((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) ++ ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)))) ++ (((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) ++ ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22))))) ac7_fam_k5_t2_m5_s = some ac7_fam_k5_t2_m5_i22 :=
  replay_concat (ms₁ := (((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) ++ ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11))))) (ms₂ := (((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) ++ ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22))))) (P := ac7_fam_k5_t2_m5_s) (R := ac7_fam_k5_t2_m5_i11) (S := ac7_fam_k5_t2_m5_i22) ac7_fam_k5_t2_m5_k0_11 ac7_fam_k5_t2_m5_k11_22

/-- `fam_k5_t2_m5.cert` checked: replaying its 44 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k5_t2_m5_replay : replay ((((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) ++ ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)))) ++ (((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) ++ ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22))))) ac7_fam_k5_t2_m5_s = some ac7_fam_k5_t2_m5_i22 := ac7_fam_k5_t2_m5_k0_22

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k5_t2_m5_checked : checkCert ((((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) ++ ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)))) ++ (((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) ++ ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22))))) ac7_fam_k5_t2_m5_s ac7_fam_k5_t2_m5_i22 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k5_t2_m5_replay

/-- The endpoints of `fam_k5_t2_m5.cert` are the presentations `<x,y | x^5, y^5, [x^1,y]>`
    and `<x,y | x^5, y^5, [x^2,y]>` of the statement. -/
theorem ac7_fam_k5_t2_m5_endpoints :
    metz 5 5 1 = ac7_fam_k5_t2_m5_s ∧ metz 5 5 2 = ac7_fam_k5_t2_m5_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 44-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k5_t2_m5_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 5 5 1) = some (metz 5 5 2) := by
  refine ⟨((((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) ++ ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)))) ++ (((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) ++ ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22))))), ?_⟩
  calc replay ((((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) ++ ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)))) ++ (((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) ++ ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22))))) (metz 5 5 1) = replay ((((ac7_fam_k5_t2_m5_c1 ++ ac7_fam_k5_t2_m5_c2) ++ (ac7_fam_k5_t2_m5_c3 ++ (ac7_fam_k5_t2_m5_c4 ++ ac7_fam_k5_t2_m5_c5))) ++ ((ac7_fam_k5_t2_m5_c6 ++ (ac7_fam_k5_t2_m5_c7 ++ ac7_fam_k5_t2_m5_c8)) ++ (ac7_fam_k5_t2_m5_c9 ++ (ac7_fam_k5_t2_m5_c10 ++ ac7_fam_k5_t2_m5_c11)))) ++ (((ac7_fam_k5_t2_m5_c12 ++ ac7_fam_k5_t2_m5_c13) ++ (ac7_fam_k5_t2_m5_c14 ++ (ac7_fam_k5_t2_m5_c15 ++ ac7_fam_k5_t2_m5_c16))) ++ ((ac7_fam_k5_t2_m5_c17 ++ (ac7_fam_k5_t2_m5_c18 ++ ac7_fam_k5_t2_m5_c19)) ++ (ac7_fam_k5_t2_m5_c20 ++ (ac7_fam_k5_t2_m5_c21 ++ ac7_fam_k5_t2_m5_c22))))) ac7_fam_k5_t2_m5_s := by rw [ac7_fam_k5_t2_m5_endpoints.1]
    _ = some ac7_fam_k5_t2_m5_e := ac7_fam_k5_t2_m5_replay
    _ = some (metz 5 5 2) := by rw [ac7_fam_k5_t2_m5_endpoints.2]

/-! ### `fam_k5_t4_m3.cert`: Metzler family, k=5 t=4 m=3  <x,y | x^5, y^3, [x,y]>  ->  <x,y | x^5, y^3, [x^1,y]>. -/

/-- The start tuple of `fam_k5_t4_m3.cert` (48 Q**-moves to the end tuple). -/
def ac7_fam_k5_t4_m3_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k5_t4_m3_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k5_t4_m3_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false)]]
def ac7_fam_k5_t4_m3_i3 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k5_t4_m3_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k5_t4_m3_i5 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k5_t4_m3_i6 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k5_t4_m3_i7 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true)]]
def ac7_fam_k5_t4_m3_i8 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t4_m3_i9 : QPres := mkQPres 3 4 [[(2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t4_m3_i10 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t4_m3_i11 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t4_m3_i12 : QPres := mkQPres 3 4 [[(2, false), (0, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t4_m3_i13 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true)], [(2, false), (1, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k5_t4_m3_i14 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true)], [(1, false), (0, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k5_t4_m3_i15 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true)], [(1, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k5_t4_m3_i16 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (0, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k5_t4_m3_i17 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k5_t4_m3_i18 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false)], [(0, true), (1, true), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k5_t4_m3_i19 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (1, true), (0, false), (1, false)], [(1, false), (1, false), (1, false)]]
def ac7_fam_k5_t4_m3_i20 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (1, true), (0, false), (1, false)], [(1, false), (1, false), (1, false)]]
def ac7_fam_k5_t4_m3_i21 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (0, false)], [(1, false), (1, false), (1, false)]]
def ac7_fam_k5_t4_m3_i22 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (1, true), (0, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (1, false), (0, false)]]
def ac7_fam_k5_t4_m3_i23 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false)], [(1, true), (0, true), (1, false), (0, false)]]
def ac7_fam_k5_t4_m3_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k5_t4_m3_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]

def ac7_fam_k5_t4_m3_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k5_t4_m3_c2 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k5_t4_m3_c3 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k5_t4_m3_c4 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k5_t4_m3_c5 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (0, false), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k5_t4_m3_c6 : List QMove :=
  [ .conj 0 [(2, false), (0, true), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (0, false), (2, true)] ]
def ac7_fam_k5_t4_m3_c7 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (0, true), (0, true), (2, false)] ]
def ac7_fam_k5_t4_m3_c8 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k5_t4_m3_c9 : List QMove :=
  [ .conj 0 [(2, false), (0, true), (2, false)],
    .conj 0 [(2, true), (2, true)] ]
def ac7_fam_k5_t4_m3_c10 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false)] ]
def ac7_fam_k5_t4_m3_c11 : List QMove :=
  [ .conj 0 [(0, true), (1, true), (2, true)],
    .lmul 2 0 ]
def ac7_fam_k5_t4_m3_c12 : List QMove :=
  [ .conj 0 [(2, false), (1, false), (0, false)],
    .inv 0 ]
def ac7_fam_k5_t4_m3_c13 : List QMove :=
  [ .lmul 2 0,
    .inv 0 ]
def ac7_fam_k5_t4_m3_c14 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k5_t4_m3_c15 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true)] ]
def ac7_fam_k5_t4_m3_c16 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k5_t4_m3_c17 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k5_t4_m3_c18 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k5_t4_m3_c19 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k5_t4_m3_c20 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false)] ]
def ac7_fam_k5_t4_m3_c21 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k5_t4_m3_c22 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k5_t4_m3_c23 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (1, false), (0, false)] ]
def ac7_fam_k5_t4_m3_c24 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b1 :
    replay ac7_fam_k5_t4_m3_c1 ac7_fam_k5_t4_m3_s = some ac7_fam_k5_t4_m3_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b2 :
    replay ac7_fam_k5_t4_m3_c2 ac7_fam_k5_t4_m3_i1 = some ac7_fam_k5_t4_m3_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b3 :
    replay ac7_fam_k5_t4_m3_c3 ac7_fam_k5_t4_m3_i2 = some ac7_fam_k5_t4_m3_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b4 :
    replay ac7_fam_k5_t4_m3_c4 ac7_fam_k5_t4_m3_i3 = some ac7_fam_k5_t4_m3_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b5 :
    replay ac7_fam_k5_t4_m3_c5 ac7_fam_k5_t4_m3_i4 = some ac7_fam_k5_t4_m3_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b6 :
    replay ac7_fam_k5_t4_m3_c6 ac7_fam_k5_t4_m3_i5 = some ac7_fam_k5_t4_m3_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b7 :
    replay ac7_fam_k5_t4_m3_c7 ac7_fam_k5_t4_m3_i6 = some ac7_fam_k5_t4_m3_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b8 :
    replay ac7_fam_k5_t4_m3_c8 ac7_fam_k5_t4_m3_i7 = some ac7_fam_k5_t4_m3_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b9 :
    replay ac7_fam_k5_t4_m3_c9 ac7_fam_k5_t4_m3_i8 = some ac7_fam_k5_t4_m3_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b10 :
    replay ac7_fam_k5_t4_m3_c10 ac7_fam_k5_t4_m3_i9 = some ac7_fam_k5_t4_m3_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b11 :
    replay ac7_fam_k5_t4_m3_c11 ac7_fam_k5_t4_m3_i10 = some ac7_fam_k5_t4_m3_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b12 :
    replay ac7_fam_k5_t4_m3_c12 ac7_fam_k5_t4_m3_i11 = some ac7_fam_k5_t4_m3_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b13 :
    replay ac7_fam_k5_t4_m3_c13 ac7_fam_k5_t4_m3_i12 = some ac7_fam_k5_t4_m3_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b14 :
    replay ac7_fam_k5_t4_m3_c14 ac7_fam_k5_t4_m3_i13 = some ac7_fam_k5_t4_m3_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b15 :
    replay ac7_fam_k5_t4_m3_c15 ac7_fam_k5_t4_m3_i14 = some ac7_fam_k5_t4_m3_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b16 :
    replay ac7_fam_k5_t4_m3_c16 ac7_fam_k5_t4_m3_i15 = some ac7_fam_k5_t4_m3_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b17 :
    replay ac7_fam_k5_t4_m3_c17 ac7_fam_k5_t4_m3_i16 = some ac7_fam_k5_t4_m3_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b18 :
    replay ac7_fam_k5_t4_m3_c18 ac7_fam_k5_t4_m3_i17 = some ac7_fam_k5_t4_m3_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b19 :
    replay ac7_fam_k5_t4_m3_c19 ac7_fam_k5_t4_m3_i18 = some ac7_fam_k5_t4_m3_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b20 :
    replay ac7_fam_k5_t4_m3_c20 ac7_fam_k5_t4_m3_i19 = some ac7_fam_k5_t4_m3_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b21 :
    replay ac7_fam_k5_t4_m3_c21 ac7_fam_k5_t4_m3_i20 = some ac7_fam_k5_t4_m3_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b22 :
    replay ac7_fam_k5_t4_m3_c22 ac7_fam_k5_t4_m3_i21 = some ac7_fam_k5_t4_m3_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b23 :
    replay ac7_fam_k5_t4_m3_c23 ac7_fam_k5_t4_m3_i22 = some ac7_fam_k5_t4_m3_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k5_t4_m3_b24 :
    replay ac7_fam_k5_t4_m3_c24 ac7_fam_k5_t4_m3_i23 = some ac7_fam_k5_t4_m3_i24 := by decide

theorem ac7_fam_k5_t4_m3_k1_3 : replay (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3) ac7_fam_k5_t4_m3_i1 = some ac7_fam_k5_t4_m3_i3 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c2) (ms₂ := ac7_fam_k5_t4_m3_c3) (P := ac7_fam_k5_t4_m3_i1) (R := ac7_fam_k5_t4_m3_i2) (S := ac7_fam_k5_t4_m3_i3) ac7_fam_k5_t4_m3_b2 ac7_fam_k5_t4_m3_b3
theorem ac7_fam_k5_t4_m3_k0_3 : replay (ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ac7_fam_k5_t4_m3_s = some ac7_fam_k5_t4_m3_i3 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c1) (ms₂ := (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) (P := ac7_fam_k5_t4_m3_s) (R := ac7_fam_k5_t4_m3_i1) (S := ac7_fam_k5_t4_m3_i3) ac7_fam_k5_t4_m3_b1 ac7_fam_k5_t4_m3_k1_3
theorem ac7_fam_k5_t4_m3_k4_6 : replay (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6) ac7_fam_k5_t4_m3_i4 = some ac7_fam_k5_t4_m3_i6 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c5) (ms₂ := ac7_fam_k5_t4_m3_c6) (P := ac7_fam_k5_t4_m3_i4) (R := ac7_fam_k5_t4_m3_i5) (S := ac7_fam_k5_t4_m3_i6) ac7_fam_k5_t4_m3_b5 ac7_fam_k5_t4_m3_b6
theorem ac7_fam_k5_t4_m3_k3_6 : replay (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6)) ac7_fam_k5_t4_m3_i3 = some ac7_fam_k5_t4_m3_i6 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c4) (ms₂ := (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6)) (P := ac7_fam_k5_t4_m3_i3) (R := ac7_fam_k5_t4_m3_i4) (S := ac7_fam_k5_t4_m3_i6) ac7_fam_k5_t4_m3_b4 ac7_fam_k5_t4_m3_k4_6
theorem ac7_fam_k5_t4_m3_k0_6 : replay ((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) ac7_fam_k5_t4_m3_s = some ac7_fam_k5_t4_m3_i6 :=
  replay_concat (ms₁ := (ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3))) (ms₂ := (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) (P := ac7_fam_k5_t4_m3_s) (R := ac7_fam_k5_t4_m3_i3) (S := ac7_fam_k5_t4_m3_i6) ac7_fam_k5_t4_m3_k0_3 ac7_fam_k5_t4_m3_k3_6
theorem ac7_fam_k5_t4_m3_k7_9 : replay (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9) ac7_fam_k5_t4_m3_i7 = some ac7_fam_k5_t4_m3_i9 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c8) (ms₂ := ac7_fam_k5_t4_m3_c9) (P := ac7_fam_k5_t4_m3_i7) (R := ac7_fam_k5_t4_m3_i8) (S := ac7_fam_k5_t4_m3_i9) ac7_fam_k5_t4_m3_b8 ac7_fam_k5_t4_m3_b9
theorem ac7_fam_k5_t4_m3_k6_9 : replay (ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ac7_fam_k5_t4_m3_i6 = some ac7_fam_k5_t4_m3_i9 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c7) (ms₂ := (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) (P := ac7_fam_k5_t4_m3_i6) (R := ac7_fam_k5_t4_m3_i7) (S := ac7_fam_k5_t4_m3_i9) ac7_fam_k5_t4_m3_b7 ac7_fam_k5_t4_m3_k7_9
theorem ac7_fam_k5_t4_m3_k10_12 : replay (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12) ac7_fam_k5_t4_m3_i10 = some ac7_fam_k5_t4_m3_i12 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c11) (ms₂ := ac7_fam_k5_t4_m3_c12) (P := ac7_fam_k5_t4_m3_i10) (R := ac7_fam_k5_t4_m3_i11) (S := ac7_fam_k5_t4_m3_i12) ac7_fam_k5_t4_m3_b11 ac7_fam_k5_t4_m3_b12
theorem ac7_fam_k5_t4_m3_k9_12 : replay (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)) ac7_fam_k5_t4_m3_i9 = some ac7_fam_k5_t4_m3_i12 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c10) (ms₂ := (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)) (P := ac7_fam_k5_t4_m3_i9) (R := ac7_fam_k5_t4_m3_i10) (S := ac7_fam_k5_t4_m3_i12) ac7_fam_k5_t4_m3_b10 ac7_fam_k5_t4_m3_k10_12
theorem ac7_fam_k5_t4_m3_k6_12 : replay ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12))) ac7_fam_k5_t4_m3_i6 = some ac7_fam_k5_t4_m3_i12 :=
  replay_concat (ms₁ := (ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9))) (ms₂ := (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12))) (P := ac7_fam_k5_t4_m3_i6) (R := ac7_fam_k5_t4_m3_i9) (S := ac7_fam_k5_t4_m3_i12) ac7_fam_k5_t4_m3_k6_9 ac7_fam_k5_t4_m3_k9_12
theorem ac7_fam_k5_t4_m3_k0_12 : replay (((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) ++ ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)))) ac7_fam_k5_t4_m3_s = some ac7_fam_k5_t4_m3_i12 :=
  replay_concat (ms₁ := ((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6)))) (ms₂ := ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)))) (P := ac7_fam_k5_t4_m3_s) (R := ac7_fam_k5_t4_m3_i6) (S := ac7_fam_k5_t4_m3_i12) ac7_fam_k5_t4_m3_k0_6 ac7_fam_k5_t4_m3_k6_12
theorem ac7_fam_k5_t4_m3_k13_15 : replay (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15) ac7_fam_k5_t4_m3_i13 = some ac7_fam_k5_t4_m3_i15 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c14) (ms₂ := ac7_fam_k5_t4_m3_c15) (P := ac7_fam_k5_t4_m3_i13) (R := ac7_fam_k5_t4_m3_i14) (S := ac7_fam_k5_t4_m3_i15) ac7_fam_k5_t4_m3_b14 ac7_fam_k5_t4_m3_b15
theorem ac7_fam_k5_t4_m3_k12_15 : replay (ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ac7_fam_k5_t4_m3_i12 = some ac7_fam_k5_t4_m3_i15 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c13) (ms₂ := (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) (P := ac7_fam_k5_t4_m3_i12) (R := ac7_fam_k5_t4_m3_i13) (S := ac7_fam_k5_t4_m3_i15) ac7_fam_k5_t4_m3_b13 ac7_fam_k5_t4_m3_k13_15
theorem ac7_fam_k5_t4_m3_k16_18 : replay (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18) ac7_fam_k5_t4_m3_i16 = some ac7_fam_k5_t4_m3_i18 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c17) (ms₂ := ac7_fam_k5_t4_m3_c18) (P := ac7_fam_k5_t4_m3_i16) (R := ac7_fam_k5_t4_m3_i17) (S := ac7_fam_k5_t4_m3_i18) ac7_fam_k5_t4_m3_b17 ac7_fam_k5_t4_m3_b18
theorem ac7_fam_k5_t4_m3_k15_18 : replay (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18)) ac7_fam_k5_t4_m3_i15 = some ac7_fam_k5_t4_m3_i18 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c16) (ms₂ := (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18)) (P := ac7_fam_k5_t4_m3_i15) (R := ac7_fam_k5_t4_m3_i16) (S := ac7_fam_k5_t4_m3_i18) ac7_fam_k5_t4_m3_b16 ac7_fam_k5_t4_m3_k16_18
theorem ac7_fam_k5_t4_m3_k12_18 : replay ((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) ac7_fam_k5_t4_m3_i12 = some ac7_fam_k5_t4_m3_i18 :=
  replay_concat (ms₁ := (ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15))) (ms₂ := (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) (P := ac7_fam_k5_t4_m3_i12) (R := ac7_fam_k5_t4_m3_i15) (S := ac7_fam_k5_t4_m3_i18) ac7_fam_k5_t4_m3_k12_15 ac7_fam_k5_t4_m3_k15_18
theorem ac7_fam_k5_t4_m3_k19_21 : replay (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21) ac7_fam_k5_t4_m3_i19 = some ac7_fam_k5_t4_m3_i21 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c20) (ms₂ := ac7_fam_k5_t4_m3_c21) (P := ac7_fam_k5_t4_m3_i19) (R := ac7_fam_k5_t4_m3_i20) (S := ac7_fam_k5_t4_m3_i21) ac7_fam_k5_t4_m3_b20 ac7_fam_k5_t4_m3_b21
theorem ac7_fam_k5_t4_m3_k18_21 : replay (ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ac7_fam_k5_t4_m3_i18 = some ac7_fam_k5_t4_m3_i21 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c19) (ms₂ := (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) (P := ac7_fam_k5_t4_m3_i18) (R := ac7_fam_k5_t4_m3_i19) (S := ac7_fam_k5_t4_m3_i21) ac7_fam_k5_t4_m3_b19 ac7_fam_k5_t4_m3_k19_21
theorem ac7_fam_k5_t4_m3_k22_24 : replay (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24) ac7_fam_k5_t4_m3_i22 = some ac7_fam_k5_t4_m3_i24 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c23) (ms₂ := ac7_fam_k5_t4_m3_c24) (P := ac7_fam_k5_t4_m3_i22) (R := ac7_fam_k5_t4_m3_i23) (S := ac7_fam_k5_t4_m3_i24) ac7_fam_k5_t4_m3_b23 ac7_fam_k5_t4_m3_b24
theorem ac7_fam_k5_t4_m3_k21_24 : replay (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24)) ac7_fam_k5_t4_m3_i21 = some ac7_fam_k5_t4_m3_i24 :=
  replay_concat (ms₁ := ac7_fam_k5_t4_m3_c22) (ms₂ := (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24)) (P := ac7_fam_k5_t4_m3_i21) (R := ac7_fam_k5_t4_m3_i22) (S := ac7_fam_k5_t4_m3_i24) ac7_fam_k5_t4_m3_b22 ac7_fam_k5_t4_m3_k22_24
theorem ac7_fam_k5_t4_m3_k18_24 : replay ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24))) ac7_fam_k5_t4_m3_i18 = some ac7_fam_k5_t4_m3_i24 :=
  replay_concat (ms₁ := (ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21))) (ms₂ := (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24))) (P := ac7_fam_k5_t4_m3_i18) (R := ac7_fam_k5_t4_m3_i21) (S := ac7_fam_k5_t4_m3_i24) ac7_fam_k5_t4_m3_k18_21 ac7_fam_k5_t4_m3_k21_24
theorem ac7_fam_k5_t4_m3_k12_24 : replay (((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) ++ ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24)))) ac7_fam_k5_t4_m3_i12 = some ac7_fam_k5_t4_m3_i24 :=
  replay_concat (ms₁ := ((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18)))) (ms₂ := ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24)))) (P := ac7_fam_k5_t4_m3_i12) (R := ac7_fam_k5_t4_m3_i18) (S := ac7_fam_k5_t4_m3_i24) ac7_fam_k5_t4_m3_k12_18 ac7_fam_k5_t4_m3_k18_24
theorem ac7_fam_k5_t4_m3_k0_24 : replay ((((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) ++ ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)))) ++ (((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) ++ ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24))))) ac7_fam_k5_t4_m3_s = some ac7_fam_k5_t4_m3_i24 :=
  replay_concat (ms₁ := (((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) ++ ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12))))) (ms₂ := (((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) ++ ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24))))) (P := ac7_fam_k5_t4_m3_s) (R := ac7_fam_k5_t4_m3_i12) (S := ac7_fam_k5_t4_m3_i24) ac7_fam_k5_t4_m3_k0_12 ac7_fam_k5_t4_m3_k12_24

/-- `fam_k5_t4_m3.cert` checked: replaying its 48 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k5_t4_m3_replay : replay ((((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) ++ ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)))) ++ (((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) ++ ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24))))) ac7_fam_k5_t4_m3_s = some ac7_fam_k5_t4_m3_i24 := ac7_fam_k5_t4_m3_k0_24

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k5_t4_m3_checked : checkCert ((((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) ++ ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)))) ++ (((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) ++ ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24))))) ac7_fam_k5_t4_m3_s ac7_fam_k5_t4_m3_i24 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k5_t4_m3_replay

/-- The endpoints of `fam_k5_t4_m3.cert` are the presentations `<x,y | x^5, y^3, [x^1,y]>`
    and `<x,y | x^5, y^3, [x^1,y]>` of the statement. -/
theorem ac7_fam_k5_t4_m3_endpoints :
    metz 5 3 1 = ac7_fam_k5_t4_m3_s ∧ metz 5 3 1 = ac7_fam_k5_t4_m3_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 48-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k5_t4_m3_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 5 3 1) = some (metz 5 3 1) := by
  refine ⟨((((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) ++ ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)))) ++ (((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) ++ ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24))))), ?_⟩
  calc replay ((((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) ++ ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)))) ++ (((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) ++ ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24))))) (metz 5 3 1) = replay ((((ac7_fam_k5_t4_m3_c1 ++ (ac7_fam_k5_t4_m3_c2 ++ ac7_fam_k5_t4_m3_c3)) ++ (ac7_fam_k5_t4_m3_c4 ++ (ac7_fam_k5_t4_m3_c5 ++ ac7_fam_k5_t4_m3_c6))) ++ ((ac7_fam_k5_t4_m3_c7 ++ (ac7_fam_k5_t4_m3_c8 ++ ac7_fam_k5_t4_m3_c9)) ++ (ac7_fam_k5_t4_m3_c10 ++ (ac7_fam_k5_t4_m3_c11 ++ ac7_fam_k5_t4_m3_c12)))) ++ (((ac7_fam_k5_t4_m3_c13 ++ (ac7_fam_k5_t4_m3_c14 ++ ac7_fam_k5_t4_m3_c15)) ++ (ac7_fam_k5_t4_m3_c16 ++ (ac7_fam_k5_t4_m3_c17 ++ ac7_fam_k5_t4_m3_c18))) ++ ((ac7_fam_k5_t4_m3_c19 ++ (ac7_fam_k5_t4_m3_c20 ++ ac7_fam_k5_t4_m3_c21)) ++ (ac7_fam_k5_t4_m3_c22 ++ (ac7_fam_k5_t4_m3_c23 ++ ac7_fam_k5_t4_m3_c24))))) ac7_fam_k5_t4_m3_s := by rw [ac7_fam_k5_t4_m3_endpoints.1]
    _ = some ac7_fam_k5_t4_m3_e := ac7_fam_k5_t4_m3_replay
    _ = some (metz 5 3 1) := by rw [ac7_fam_k5_t4_m3_endpoints.2]

/-! ### `fam_k7_t1_m4.cert`: Metzler family, k=7 t=1 m=4  <x,y | x^7, y^4, [x,y]>  ->  <x,y | x^7, y^4, [x^6,y]>. -/

/-- The start tuple of `fam_k7_t1_m4.cert` (56 Q**-moves to the end tuple). -/
def ac7_fam_k7_t1_m4_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k7_t1_m4_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k7_t1_m4_i2 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t1_m4_i3 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t1_m4_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k7_t1_m4_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t1_m4_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (2, true), (0, true), (0, true)]]
def ac7_fam_k7_t1_m4_i7 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k7_t1_m4_i8 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (2, true), (0, true)]]
def ac7_fam_k7_t1_m4_i9 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (2, true)]]
def ac7_fam_k7_t1_m4_i10 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k7_t1_m4_i11 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t1_m4_i12 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t1_m4_i13 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t1_m4_i14 : QPres := mkQPres 3 4 [[(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t1_m4_i15 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t1_m4_i16 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t1_m4_i17 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t1_m4_i18 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t1_m4_i19 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t1_m4_i20 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t1_m4_i21 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t1_m4_i22 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t1_m4_i23 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k7_t1_m4_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k7_t1_m4_i25 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k7_t1_m4_i26 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k7_t1_m4_i27 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k7_t1_m4_i28 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)]]
def ac7_fam_k7_t1_m4_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)]]

def ac7_fam_k7_t1_m4_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k7_t1_m4_c2 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k7_t1_m4_c3 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k7_t1_m4_c4 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k7_t1_m4_c5 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k7_t1_m4_c6 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false)] ]
def ac7_fam_k7_t1_m4_c7 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true)] ]
def ac7_fam_k7_t1_m4_c8 : List QMove :=
  [ .conj 3 [(0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k7_t1_m4_c9 : List QMove :=
  [ .conj 3 [(0, true), (0, true)],
    .conj 3 [(0, false)] ]
def ac7_fam_k7_t1_m4_c10 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true)] ]
def ac7_fam_k7_t1_m4_c11 : List QMove :=
  [ .conj 0 [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k7_t1_m4_c12 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (2, false)],
    .conj 0 [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)] ]
def ac7_fam_k7_t1_m4_c13 : List QMove :=
  [ .lmul 2 0,
    .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false), (2, false), (1, false), (0, false)] ]
def ac7_fam_k7_t1_m4_c14 : List QMove :=
  [ .inv 0,
    .lmul 2 0 ]
def ac7_fam_k7_t1_m4_c15 : List QMove :=
  [ .inv 0,
    .nijinv 0 2 ]
def ac7_fam_k7_t1_m4_c16 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k7_t1_m4_c17 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k7_t1_m4_c18 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k7_t1_m4_c19 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true)] ]
def ac7_fam_k7_t1_m4_c20 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k7_t1_m4_c21 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k7_t1_m4_c22 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k7_t1_m4_c23 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k7_t1_m4_c24 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false)] ]
def ac7_fam_k7_t1_m4_c25 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k7_t1_m4_c26 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k7_t1_m4_c27 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k7_t1_m4_c28 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b1 :
    replay ac7_fam_k7_t1_m4_c1 ac7_fam_k7_t1_m4_s = some ac7_fam_k7_t1_m4_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b2 :
    replay ac7_fam_k7_t1_m4_c2 ac7_fam_k7_t1_m4_i1 = some ac7_fam_k7_t1_m4_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b3 :
    replay ac7_fam_k7_t1_m4_c3 ac7_fam_k7_t1_m4_i2 = some ac7_fam_k7_t1_m4_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b4 :
    replay ac7_fam_k7_t1_m4_c4 ac7_fam_k7_t1_m4_i3 = some ac7_fam_k7_t1_m4_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b5 :
    replay ac7_fam_k7_t1_m4_c5 ac7_fam_k7_t1_m4_i4 = some ac7_fam_k7_t1_m4_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b6 :
    replay ac7_fam_k7_t1_m4_c6 ac7_fam_k7_t1_m4_i5 = some ac7_fam_k7_t1_m4_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b7 :
    replay ac7_fam_k7_t1_m4_c7 ac7_fam_k7_t1_m4_i6 = some ac7_fam_k7_t1_m4_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b8 :
    replay ac7_fam_k7_t1_m4_c8 ac7_fam_k7_t1_m4_i7 = some ac7_fam_k7_t1_m4_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b9 :
    replay ac7_fam_k7_t1_m4_c9 ac7_fam_k7_t1_m4_i8 = some ac7_fam_k7_t1_m4_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b10 :
    replay ac7_fam_k7_t1_m4_c10 ac7_fam_k7_t1_m4_i9 = some ac7_fam_k7_t1_m4_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b11 :
    replay ac7_fam_k7_t1_m4_c11 ac7_fam_k7_t1_m4_i10 = some ac7_fam_k7_t1_m4_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b12 :
    replay ac7_fam_k7_t1_m4_c12 ac7_fam_k7_t1_m4_i11 = some ac7_fam_k7_t1_m4_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b13 :
    replay ac7_fam_k7_t1_m4_c13 ac7_fam_k7_t1_m4_i12 = some ac7_fam_k7_t1_m4_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b14 :
    replay ac7_fam_k7_t1_m4_c14 ac7_fam_k7_t1_m4_i13 = some ac7_fam_k7_t1_m4_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b15 :
    replay ac7_fam_k7_t1_m4_c15 ac7_fam_k7_t1_m4_i14 = some ac7_fam_k7_t1_m4_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b16 :
    replay ac7_fam_k7_t1_m4_c16 ac7_fam_k7_t1_m4_i15 = some ac7_fam_k7_t1_m4_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b17 :
    replay ac7_fam_k7_t1_m4_c17 ac7_fam_k7_t1_m4_i16 = some ac7_fam_k7_t1_m4_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b18 :
    replay ac7_fam_k7_t1_m4_c18 ac7_fam_k7_t1_m4_i17 = some ac7_fam_k7_t1_m4_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b19 :
    replay ac7_fam_k7_t1_m4_c19 ac7_fam_k7_t1_m4_i18 = some ac7_fam_k7_t1_m4_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b20 :
    replay ac7_fam_k7_t1_m4_c20 ac7_fam_k7_t1_m4_i19 = some ac7_fam_k7_t1_m4_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b21 :
    replay ac7_fam_k7_t1_m4_c21 ac7_fam_k7_t1_m4_i20 = some ac7_fam_k7_t1_m4_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b22 :
    replay ac7_fam_k7_t1_m4_c22 ac7_fam_k7_t1_m4_i21 = some ac7_fam_k7_t1_m4_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b23 :
    replay ac7_fam_k7_t1_m4_c23 ac7_fam_k7_t1_m4_i22 = some ac7_fam_k7_t1_m4_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b24 :
    replay ac7_fam_k7_t1_m4_c24 ac7_fam_k7_t1_m4_i23 = some ac7_fam_k7_t1_m4_i24 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b25 :
    replay ac7_fam_k7_t1_m4_c25 ac7_fam_k7_t1_m4_i24 = some ac7_fam_k7_t1_m4_i25 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b26 :
    replay ac7_fam_k7_t1_m4_c26 ac7_fam_k7_t1_m4_i25 = some ac7_fam_k7_t1_m4_i26 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b27 :
    replay ac7_fam_k7_t1_m4_c27 ac7_fam_k7_t1_m4_i26 = some ac7_fam_k7_t1_m4_i27 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t1_m4_b28 :
    replay ac7_fam_k7_t1_m4_c28 ac7_fam_k7_t1_m4_i27 = some ac7_fam_k7_t1_m4_i28 := by decide

theorem ac7_fam_k7_t1_m4_k1_3 : replay (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3) ac7_fam_k7_t1_m4_i1 = some ac7_fam_k7_t1_m4_i3 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c2) (ms₂ := ac7_fam_k7_t1_m4_c3) (P := ac7_fam_k7_t1_m4_i1) (R := ac7_fam_k7_t1_m4_i2) (S := ac7_fam_k7_t1_m4_i3) ac7_fam_k7_t1_m4_b2 ac7_fam_k7_t1_m4_b3
theorem ac7_fam_k7_t1_m4_k0_3 : replay (ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ac7_fam_k7_t1_m4_s = some ac7_fam_k7_t1_m4_i3 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c1) (ms₂ := (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) (P := ac7_fam_k7_t1_m4_s) (R := ac7_fam_k7_t1_m4_i1) (S := ac7_fam_k7_t1_m4_i3) ac7_fam_k7_t1_m4_b1 ac7_fam_k7_t1_m4_k1_3
theorem ac7_fam_k7_t1_m4_k3_5 : replay (ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ac7_fam_k7_t1_m4_i3 = some ac7_fam_k7_t1_m4_i5 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c4) (ms₂ := ac7_fam_k7_t1_m4_c5) (P := ac7_fam_k7_t1_m4_i3) (R := ac7_fam_k7_t1_m4_i4) (S := ac7_fam_k7_t1_m4_i5) ac7_fam_k7_t1_m4_b4 ac7_fam_k7_t1_m4_b5
theorem ac7_fam_k7_t1_m4_k5_7 : replay (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7) ac7_fam_k7_t1_m4_i5 = some ac7_fam_k7_t1_m4_i7 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c6) (ms₂ := ac7_fam_k7_t1_m4_c7) (P := ac7_fam_k7_t1_m4_i5) (R := ac7_fam_k7_t1_m4_i6) (S := ac7_fam_k7_t1_m4_i7) ac7_fam_k7_t1_m4_b6 ac7_fam_k7_t1_m4_b7
theorem ac7_fam_k7_t1_m4_k3_7 : replay ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7)) ac7_fam_k7_t1_m4_i3 = some ac7_fam_k7_t1_m4_i7 :=
  replay_concat (ms₁ := (ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5)) (ms₂ := (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7)) (P := ac7_fam_k7_t1_m4_i3) (R := ac7_fam_k7_t1_m4_i5) (S := ac7_fam_k7_t1_m4_i7) ac7_fam_k7_t1_m4_k3_5 ac7_fam_k7_t1_m4_k5_7
theorem ac7_fam_k7_t1_m4_k0_7 : replay ((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) ac7_fam_k7_t1_m4_s = some ac7_fam_k7_t1_m4_i7 :=
  replay_concat (ms₁ := (ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3))) (ms₂ := ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) (P := ac7_fam_k7_t1_m4_s) (R := ac7_fam_k7_t1_m4_i3) (S := ac7_fam_k7_t1_m4_i7) ac7_fam_k7_t1_m4_k0_3 ac7_fam_k7_t1_m4_k3_7
theorem ac7_fam_k7_t1_m4_k8_10 : replay (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10) ac7_fam_k7_t1_m4_i8 = some ac7_fam_k7_t1_m4_i10 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c9) (ms₂ := ac7_fam_k7_t1_m4_c10) (P := ac7_fam_k7_t1_m4_i8) (R := ac7_fam_k7_t1_m4_i9) (S := ac7_fam_k7_t1_m4_i10) ac7_fam_k7_t1_m4_b9 ac7_fam_k7_t1_m4_b10
theorem ac7_fam_k7_t1_m4_k7_10 : replay (ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ac7_fam_k7_t1_m4_i7 = some ac7_fam_k7_t1_m4_i10 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c8) (ms₂ := (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) (P := ac7_fam_k7_t1_m4_i7) (R := ac7_fam_k7_t1_m4_i8) (S := ac7_fam_k7_t1_m4_i10) ac7_fam_k7_t1_m4_b8 ac7_fam_k7_t1_m4_k8_10
theorem ac7_fam_k7_t1_m4_k10_12 : replay (ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ac7_fam_k7_t1_m4_i10 = some ac7_fam_k7_t1_m4_i12 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c11) (ms₂ := ac7_fam_k7_t1_m4_c12) (P := ac7_fam_k7_t1_m4_i10) (R := ac7_fam_k7_t1_m4_i11) (S := ac7_fam_k7_t1_m4_i12) ac7_fam_k7_t1_m4_b11 ac7_fam_k7_t1_m4_b12
theorem ac7_fam_k7_t1_m4_k12_14 : replay (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14) ac7_fam_k7_t1_m4_i12 = some ac7_fam_k7_t1_m4_i14 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c13) (ms₂ := ac7_fam_k7_t1_m4_c14) (P := ac7_fam_k7_t1_m4_i12) (R := ac7_fam_k7_t1_m4_i13) (S := ac7_fam_k7_t1_m4_i14) ac7_fam_k7_t1_m4_b13 ac7_fam_k7_t1_m4_b14
theorem ac7_fam_k7_t1_m4_k10_14 : replay ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)) ac7_fam_k7_t1_m4_i10 = some ac7_fam_k7_t1_m4_i14 :=
  replay_concat (ms₁ := (ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12)) (ms₂ := (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)) (P := ac7_fam_k7_t1_m4_i10) (R := ac7_fam_k7_t1_m4_i12) (S := ac7_fam_k7_t1_m4_i14) ac7_fam_k7_t1_m4_k10_12 ac7_fam_k7_t1_m4_k12_14
theorem ac7_fam_k7_t1_m4_k7_14 : replay ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14))) ac7_fam_k7_t1_m4_i7 = some ac7_fam_k7_t1_m4_i14 :=
  replay_concat (ms₁ := (ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10))) (ms₂ := ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14))) (P := ac7_fam_k7_t1_m4_i7) (R := ac7_fam_k7_t1_m4_i10) (S := ac7_fam_k7_t1_m4_i14) ac7_fam_k7_t1_m4_k7_10 ac7_fam_k7_t1_m4_k10_14
theorem ac7_fam_k7_t1_m4_k0_14 : replay (((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) ++ ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)))) ac7_fam_k7_t1_m4_s = some ac7_fam_k7_t1_m4_i14 :=
  replay_concat (ms₁ := ((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7)))) (ms₂ := ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)))) (P := ac7_fam_k7_t1_m4_s) (R := ac7_fam_k7_t1_m4_i7) (S := ac7_fam_k7_t1_m4_i14) ac7_fam_k7_t1_m4_k0_7 ac7_fam_k7_t1_m4_k7_14
theorem ac7_fam_k7_t1_m4_k15_17 : replay (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17) ac7_fam_k7_t1_m4_i15 = some ac7_fam_k7_t1_m4_i17 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c16) (ms₂ := ac7_fam_k7_t1_m4_c17) (P := ac7_fam_k7_t1_m4_i15) (R := ac7_fam_k7_t1_m4_i16) (S := ac7_fam_k7_t1_m4_i17) ac7_fam_k7_t1_m4_b16 ac7_fam_k7_t1_m4_b17
theorem ac7_fam_k7_t1_m4_k14_17 : replay (ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ac7_fam_k7_t1_m4_i14 = some ac7_fam_k7_t1_m4_i17 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c15) (ms₂ := (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) (P := ac7_fam_k7_t1_m4_i14) (R := ac7_fam_k7_t1_m4_i15) (S := ac7_fam_k7_t1_m4_i17) ac7_fam_k7_t1_m4_b15 ac7_fam_k7_t1_m4_k15_17
theorem ac7_fam_k7_t1_m4_k17_19 : replay (ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ac7_fam_k7_t1_m4_i17 = some ac7_fam_k7_t1_m4_i19 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c18) (ms₂ := ac7_fam_k7_t1_m4_c19) (P := ac7_fam_k7_t1_m4_i17) (R := ac7_fam_k7_t1_m4_i18) (S := ac7_fam_k7_t1_m4_i19) ac7_fam_k7_t1_m4_b18 ac7_fam_k7_t1_m4_b19
theorem ac7_fam_k7_t1_m4_k19_21 : replay (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21) ac7_fam_k7_t1_m4_i19 = some ac7_fam_k7_t1_m4_i21 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c20) (ms₂ := ac7_fam_k7_t1_m4_c21) (P := ac7_fam_k7_t1_m4_i19) (R := ac7_fam_k7_t1_m4_i20) (S := ac7_fam_k7_t1_m4_i21) ac7_fam_k7_t1_m4_b20 ac7_fam_k7_t1_m4_b21
theorem ac7_fam_k7_t1_m4_k17_21 : replay ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21)) ac7_fam_k7_t1_m4_i17 = some ac7_fam_k7_t1_m4_i21 :=
  replay_concat (ms₁ := (ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19)) (ms₂ := (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21)) (P := ac7_fam_k7_t1_m4_i17) (R := ac7_fam_k7_t1_m4_i19) (S := ac7_fam_k7_t1_m4_i21) ac7_fam_k7_t1_m4_k17_19 ac7_fam_k7_t1_m4_k19_21
theorem ac7_fam_k7_t1_m4_k14_21 : replay ((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) ac7_fam_k7_t1_m4_i14 = some ac7_fam_k7_t1_m4_i21 :=
  replay_concat (ms₁ := (ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17))) (ms₂ := ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) (P := ac7_fam_k7_t1_m4_i14) (R := ac7_fam_k7_t1_m4_i17) (S := ac7_fam_k7_t1_m4_i21) ac7_fam_k7_t1_m4_k14_17 ac7_fam_k7_t1_m4_k17_21
theorem ac7_fam_k7_t1_m4_k22_24 : replay (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24) ac7_fam_k7_t1_m4_i22 = some ac7_fam_k7_t1_m4_i24 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c23) (ms₂ := ac7_fam_k7_t1_m4_c24) (P := ac7_fam_k7_t1_m4_i22) (R := ac7_fam_k7_t1_m4_i23) (S := ac7_fam_k7_t1_m4_i24) ac7_fam_k7_t1_m4_b23 ac7_fam_k7_t1_m4_b24
theorem ac7_fam_k7_t1_m4_k21_24 : replay (ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ac7_fam_k7_t1_m4_i21 = some ac7_fam_k7_t1_m4_i24 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c22) (ms₂ := (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) (P := ac7_fam_k7_t1_m4_i21) (R := ac7_fam_k7_t1_m4_i22) (S := ac7_fam_k7_t1_m4_i24) ac7_fam_k7_t1_m4_b22 ac7_fam_k7_t1_m4_k22_24
theorem ac7_fam_k7_t1_m4_k24_26 : replay (ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ac7_fam_k7_t1_m4_i24 = some ac7_fam_k7_t1_m4_i26 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c25) (ms₂ := ac7_fam_k7_t1_m4_c26) (P := ac7_fam_k7_t1_m4_i24) (R := ac7_fam_k7_t1_m4_i25) (S := ac7_fam_k7_t1_m4_i26) ac7_fam_k7_t1_m4_b25 ac7_fam_k7_t1_m4_b26
theorem ac7_fam_k7_t1_m4_k26_28 : replay (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28) ac7_fam_k7_t1_m4_i26 = some ac7_fam_k7_t1_m4_i28 :=
  replay_concat (ms₁ := ac7_fam_k7_t1_m4_c27) (ms₂ := ac7_fam_k7_t1_m4_c28) (P := ac7_fam_k7_t1_m4_i26) (R := ac7_fam_k7_t1_m4_i27) (S := ac7_fam_k7_t1_m4_i28) ac7_fam_k7_t1_m4_b27 ac7_fam_k7_t1_m4_b28
theorem ac7_fam_k7_t1_m4_k24_28 : replay ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28)) ac7_fam_k7_t1_m4_i24 = some ac7_fam_k7_t1_m4_i28 :=
  replay_concat (ms₁ := (ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26)) (ms₂ := (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28)) (P := ac7_fam_k7_t1_m4_i24) (R := ac7_fam_k7_t1_m4_i26) (S := ac7_fam_k7_t1_m4_i28) ac7_fam_k7_t1_m4_k24_26 ac7_fam_k7_t1_m4_k26_28
theorem ac7_fam_k7_t1_m4_k21_28 : replay ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28))) ac7_fam_k7_t1_m4_i21 = some ac7_fam_k7_t1_m4_i28 :=
  replay_concat (ms₁ := (ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24))) (ms₂ := ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28))) (P := ac7_fam_k7_t1_m4_i21) (R := ac7_fam_k7_t1_m4_i24) (S := ac7_fam_k7_t1_m4_i28) ac7_fam_k7_t1_m4_k21_24 ac7_fam_k7_t1_m4_k24_28
theorem ac7_fam_k7_t1_m4_k14_28 : replay (((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) ++ ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28)))) ac7_fam_k7_t1_m4_i14 = some ac7_fam_k7_t1_m4_i28 :=
  replay_concat (ms₁ := ((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21)))) (ms₂ := ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28)))) (P := ac7_fam_k7_t1_m4_i14) (R := ac7_fam_k7_t1_m4_i21) (S := ac7_fam_k7_t1_m4_i28) ac7_fam_k7_t1_m4_k14_21 ac7_fam_k7_t1_m4_k21_28
theorem ac7_fam_k7_t1_m4_k0_28 : replay ((((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) ++ ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)))) ++ (((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) ++ ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28))))) ac7_fam_k7_t1_m4_s = some ac7_fam_k7_t1_m4_i28 :=
  replay_concat (ms₁ := (((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) ++ ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14))))) (ms₂ := (((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) ++ ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28))))) (P := ac7_fam_k7_t1_m4_s) (R := ac7_fam_k7_t1_m4_i14) (S := ac7_fam_k7_t1_m4_i28) ac7_fam_k7_t1_m4_k0_14 ac7_fam_k7_t1_m4_k14_28

/-- `fam_k7_t1_m4.cert` checked: replaying its 56 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k7_t1_m4_replay : replay ((((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) ++ ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)))) ++ (((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) ++ ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28))))) ac7_fam_k7_t1_m4_s = some ac7_fam_k7_t1_m4_i28 := ac7_fam_k7_t1_m4_k0_28

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k7_t1_m4_checked : checkCert ((((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) ++ ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)))) ++ (((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) ++ ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28))))) ac7_fam_k7_t1_m4_s ac7_fam_k7_t1_m4_i28 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k7_t1_m4_replay

/-- The endpoints of `fam_k7_t1_m4.cert` are the presentations `<x,y | x^7, y^4, [x^1,y]>`
    and `<x,y | x^7, y^4, [x^6,y]>` of the statement. -/
theorem ac7_fam_k7_t1_m4_endpoints :
    metz 7 4 1 = ac7_fam_k7_t1_m4_s ∧ metz 7 4 6 = ac7_fam_k7_t1_m4_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 56-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k7_t1_m4_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 7 4 1) = some (metz 7 4 6) := by
  refine ⟨((((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) ++ ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)))) ++ (((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) ++ ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28))))), ?_⟩
  calc replay ((((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) ++ ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)))) ++ (((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) ++ ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28))))) (metz 7 4 1) = replay ((((ac7_fam_k7_t1_m4_c1 ++ (ac7_fam_k7_t1_m4_c2 ++ ac7_fam_k7_t1_m4_c3)) ++ ((ac7_fam_k7_t1_m4_c4 ++ ac7_fam_k7_t1_m4_c5) ++ (ac7_fam_k7_t1_m4_c6 ++ ac7_fam_k7_t1_m4_c7))) ++ ((ac7_fam_k7_t1_m4_c8 ++ (ac7_fam_k7_t1_m4_c9 ++ ac7_fam_k7_t1_m4_c10)) ++ ((ac7_fam_k7_t1_m4_c11 ++ ac7_fam_k7_t1_m4_c12) ++ (ac7_fam_k7_t1_m4_c13 ++ ac7_fam_k7_t1_m4_c14)))) ++ (((ac7_fam_k7_t1_m4_c15 ++ (ac7_fam_k7_t1_m4_c16 ++ ac7_fam_k7_t1_m4_c17)) ++ ((ac7_fam_k7_t1_m4_c18 ++ ac7_fam_k7_t1_m4_c19) ++ (ac7_fam_k7_t1_m4_c20 ++ ac7_fam_k7_t1_m4_c21))) ++ ((ac7_fam_k7_t1_m4_c22 ++ (ac7_fam_k7_t1_m4_c23 ++ ac7_fam_k7_t1_m4_c24)) ++ ((ac7_fam_k7_t1_m4_c25 ++ ac7_fam_k7_t1_m4_c26) ++ (ac7_fam_k7_t1_m4_c27 ++ ac7_fam_k7_t1_m4_c28))))) ac7_fam_k7_t1_m4_s := by rw [ac7_fam_k7_t1_m4_endpoints.1]
    _ = some ac7_fam_k7_t1_m4_e := ac7_fam_k7_t1_m4_replay
    _ = some (metz 7 4 6) := by rw [ac7_fam_k7_t1_m4_endpoints.2]

/-! ### `fam_k7_t2_m2.cert`: Metzler family, k=7 t=2 m=2  <x,y | x^7, y^2, [x,y]>  ->  <x,y | x^7, y^2, [x^3,y]>. -/

/-- The start tuple of `fam_k7_t2_m2.cert` (48 Q**-moves to the end tuple). -/
def ac7_fam_k7_t2_m2_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k7_t2_m2_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k7_t2_m2_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t2_m2_i3 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k7_t2_m2_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true)]]
def ac7_fam_k7_t2_m2_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (2, true)]]
def ac7_fam_k7_t2_m2_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k7_t2_m2_i7 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t2_m2_i8 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t2_m2_i9 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t2_m2_i10 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t2_m2_i11 : QPres := mkQPres 3 4 [[(2, false), (2, false), (2, false), (0, false)], [(1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t2_m2_i12 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true)], [(2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t2_m2_i13 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true)], [(2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t2_m2_i14 : QPres := mkQPres 2 3 [[(0, true), (0, true)], [(1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t2_m2_i15 : QPres := mkQPres 2 3 [[(0, true), (0, true)], [(1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t2_m2_i16 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t2_m2_i17 : QPres := mkQPres 2 3 [[(1, true), (1, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t2_m2_i18 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t2_m2_i19 : QPres := mkQPres 2 3 [[(1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false)]]
def ac7_fam_k7_t2_m2_i20 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false)]]
def ac7_fam_k7_t2_m2_i21 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)], [(1, false), (1, false)]]
def ac7_fam_k7_t2_m2_i22 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k7_t2_m2_i23 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k7_t2_m2_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)]]
def ac7_fam_k7_t2_m2_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)]]

def ac7_fam_k7_t2_m2_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k7_t2_m2_c2 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k7_t2_m2_c3 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k7_t2_m2_c4 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k7_t2_m2_c5 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false)] ]
def ac7_fam_k7_t2_m2_c6 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true)] ]
def ac7_fam_k7_t2_m2_c7 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k7_t2_m2_c8 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (0, true), (2, false)],
    .conj 0 [(2, true), (2, true), (2, true), (2, true)] ]
def ac7_fam_k7_t2_m2_c9 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (2, false), (2, false)] ]
def ac7_fam_k7_t2_m2_c10 : List QMove :=
  [ .conj 0 [(0, true), (1, true), (2, true), (2, true), (2, true)],
    .lmul 2 0 ]
def ac7_fam_k7_t2_m2_c11 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (1, false), (0, false)],
    .inv 0 ]
def ac7_fam_k7_t2_m2_c12 : List QMove :=
  [ .lmul 2 0,
    .inv 0 ]
def ac7_fam_k7_t2_m2_c13 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k7_t2_m2_c14 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k7_t2_m2_c15 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true), (1, true)] ]
def ac7_fam_k7_t2_m2_c16 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k7_t2_m2_c17 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k7_t2_m2_c18 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k7_t2_m2_c19 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k7_t2_m2_c20 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false)] ]
def ac7_fam_k7_t2_m2_c21 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k7_t2_m2_c22 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k7_t2_m2_c23 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k7_t2_m2_c24 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b1 :
    replay ac7_fam_k7_t2_m2_c1 ac7_fam_k7_t2_m2_s = some ac7_fam_k7_t2_m2_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b2 :
    replay ac7_fam_k7_t2_m2_c2 ac7_fam_k7_t2_m2_i1 = some ac7_fam_k7_t2_m2_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b3 :
    replay ac7_fam_k7_t2_m2_c3 ac7_fam_k7_t2_m2_i2 = some ac7_fam_k7_t2_m2_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b4 :
    replay ac7_fam_k7_t2_m2_c4 ac7_fam_k7_t2_m2_i3 = some ac7_fam_k7_t2_m2_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b5 :
    replay ac7_fam_k7_t2_m2_c5 ac7_fam_k7_t2_m2_i4 = some ac7_fam_k7_t2_m2_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b6 :
    replay ac7_fam_k7_t2_m2_c6 ac7_fam_k7_t2_m2_i5 = some ac7_fam_k7_t2_m2_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b7 :
    replay ac7_fam_k7_t2_m2_c7 ac7_fam_k7_t2_m2_i6 = some ac7_fam_k7_t2_m2_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b8 :
    replay ac7_fam_k7_t2_m2_c8 ac7_fam_k7_t2_m2_i7 = some ac7_fam_k7_t2_m2_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b9 :
    replay ac7_fam_k7_t2_m2_c9 ac7_fam_k7_t2_m2_i8 = some ac7_fam_k7_t2_m2_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b10 :
    replay ac7_fam_k7_t2_m2_c10 ac7_fam_k7_t2_m2_i9 = some ac7_fam_k7_t2_m2_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b11 :
    replay ac7_fam_k7_t2_m2_c11 ac7_fam_k7_t2_m2_i10 = some ac7_fam_k7_t2_m2_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b12 :
    replay ac7_fam_k7_t2_m2_c12 ac7_fam_k7_t2_m2_i11 = some ac7_fam_k7_t2_m2_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b13 :
    replay ac7_fam_k7_t2_m2_c13 ac7_fam_k7_t2_m2_i12 = some ac7_fam_k7_t2_m2_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b14 :
    replay ac7_fam_k7_t2_m2_c14 ac7_fam_k7_t2_m2_i13 = some ac7_fam_k7_t2_m2_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b15 :
    replay ac7_fam_k7_t2_m2_c15 ac7_fam_k7_t2_m2_i14 = some ac7_fam_k7_t2_m2_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b16 :
    replay ac7_fam_k7_t2_m2_c16 ac7_fam_k7_t2_m2_i15 = some ac7_fam_k7_t2_m2_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b17 :
    replay ac7_fam_k7_t2_m2_c17 ac7_fam_k7_t2_m2_i16 = some ac7_fam_k7_t2_m2_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b18 :
    replay ac7_fam_k7_t2_m2_c18 ac7_fam_k7_t2_m2_i17 = some ac7_fam_k7_t2_m2_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b19 :
    replay ac7_fam_k7_t2_m2_c19 ac7_fam_k7_t2_m2_i18 = some ac7_fam_k7_t2_m2_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b20 :
    replay ac7_fam_k7_t2_m2_c20 ac7_fam_k7_t2_m2_i19 = some ac7_fam_k7_t2_m2_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b21 :
    replay ac7_fam_k7_t2_m2_c21 ac7_fam_k7_t2_m2_i20 = some ac7_fam_k7_t2_m2_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b22 :
    replay ac7_fam_k7_t2_m2_c22 ac7_fam_k7_t2_m2_i21 = some ac7_fam_k7_t2_m2_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b23 :
    replay ac7_fam_k7_t2_m2_c23 ac7_fam_k7_t2_m2_i22 = some ac7_fam_k7_t2_m2_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t2_m2_b24 :
    replay ac7_fam_k7_t2_m2_c24 ac7_fam_k7_t2_m2_i23 = some ac7_fam_k7_t2_m2_i24 := by decide

theorem ac7_fam_k7_t2_m2_k1_3 : replay (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3) ac7_fam_k7_t2_m2_i1 = some ac7_fam_k7_t2_m2_i3 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c2) (ms₂ := ac7_fam_k7_t2_m2_c3) (P := ac7_fam_k7_t2_m2_i1) (R := ac7_fam_k7_t2_m2_i2) (S := ac7_fam_k7_t2_m2_i3) ac7_fam_k7_t2_m2_b2 ac7_fam_k7_t2_m2_b3
theorem ac7_fam_k7_t2_m2_k0_3 : replay (ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ac7_fam_k7_t2_m2_s = some ac7_fam_k7_t2_m2_i3 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c1) (ms₂ := (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) (P := ac7_fam_k7_t2_m2_s) (R := ac7_fam_k7_t2_m2_i1) (S := ac7_fam_k7_t2_m2_i3) ac7_fam_k7_t2_m2_b1 ac7_fam_k7_t2_m2_k1_3
theorem ac7_fam_k7_t2_m2_k4_6 : replay (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6) ac7_fam_k7_t2_m2_i4 = some ac7_fam_k7_t2_m2_i6 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c5) (ms₂ := ac7_fam_k7_t2_m2_c6) (P := ac7_fam_k7_t2_m2_i4) (R := ac7_fam_k7_t2_m2_i5) (S := ac7_fam_k7_t2_m2_i6) ac7_fam_k7_t2_m2_b5 ac7_fam_k7_t2_m2_b6
theorem ac7_fam_k7_t2_m2_k3_6 : replay (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6)) ac7_fam_k7_t2_m2_i3 = some ac7_fam_k7_t2_m2_i6 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c4) (ms₂ := (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6)) (P := ac7_fam_k7_t2_m2_i3) (R := ac7_fam_k7_t2_m2_i4) (S := ac7_fam_k7_t2_m2_i6) ac7_fam_k7_t2_m2_b4 ac7_fam_k7_t2_m2_k4_6
theorem ac7_fam_k7_t2_m2_k0_6 : replay ((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) ac7_fam_k7_t2_m2_s = some ac7_fam_k7_t2_m2_i6 :=
  replay_concat (ms₁ := (ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3))) (ms₂ := (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) (P := ac7_fam_k7_t2_m2_s) (R := ac7_fam_k7_t2_m2_i3) (S := ac7_fam_k7_t2_m2_i6) ac7_fam_k7_t2_m2_k0_3 ac7_fam_k7_t2_m2_k3_6
theorem ac7_fam_k7_t2_m2_k7_9 : replay (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9) ac7_fam_k7_t2_m2_i7 = some ac7_fam_k7_t2_m2_i9 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c8) (ms₂ := ac7_fam_k7_t2_m2_c9) (P := ac7_fam_k7_t2_m2_i7) (R := ac7_fam_k7_t2_m2_i8) (S := ac7_fam_k7_t2_m2_i9) ac7_fam_k7_t2_m2_b8 ac7_fam_k7_t2_m2_b9
theorem ac7_fam_k7_t2_m2_k6_9 : replay (ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ac7_fam_k7_t2_m2_i6 = some ac7_fam_k7_t2_m2_i9 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c7) (ms₂ := (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) (P := ac7_fam_k7_t2_m2_i6) (R := ac7_fam_k7_t2_m2_i7) (S := ac7_fam_k7_t2_m2_i9) ac7_fam_k7_t2_m2_b7 ac7_fam_k7_t2_m2_k7_9
theorem ac7_fam_k7_t2_m2_k10_12 : replay (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12) ac7_fam_k7_t2_m2_i10 = some ac7_fam_k7_t2_m2_i12 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c11) (ms₂ := ac7_fam_k7_t2_m2_c12) (P := ac7_fam_k7_t2_m2_i10) (R := ac7_fam_k7_t2_m2_i11) (S := ac7_fam_k7_t2_m2_i12) ac7_fam_k7_t2_m2_b11 ac7_fam_k7_t2_m2_b12
theorem ac7_fam_k7_t2_m2_k9_12 : replay (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)) ac7_fam_k7_t2_m2_i9 = some ac7_fam_k7_t2_m2_i12 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c10) (ms₂ := (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)) (P := ac7_fam_k7_t2_m2_i9) (R := ac7_fam_k7_t2_m2_i10) (S := ac7_fam_k7_t2_m2_i12) ac7_fam_k7_t2_m2_b10 ac7_fam_k7_t2_m2_k10_12
theorem ac7_fam_k7_t2_m2_k6_12 : replay ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12))) ac7_fam_k7_t2_m2_i6 = some ac7_fam_k7_t2_m2_i12 :=
  replay_concat (ms₁ := (ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9))) (ms₂ := (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12))) (P := ac7_fam_k7_t2_m2_i6) (R := ac7_fam_k7_t2_m2_i9) (S := ac7_fam_k7_t2_m2_i12) ac7_fam_k7_t2_m2_k6_9 ac7_fam_k7_t2_m2_k9_12
theorem ac7_fam_k7_t2_m2_k0_12 : replay (((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) ++ ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)))) ac7_fam_k7_t2_m2_s = some ac7_fam_k7_t2_m2_i12 :=
  replay_concat (ms₁ := ((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6)))) (ms₂ := ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)))) (P := ac7_fam_k7_t2_m2_s) (R := ac7_fam_k7_t2_m2_i6) (S := ac7_fam_k7_t2_m2_i12) ac7_fam_k7_t2_m2_k0_6 ac7_fam_k7_t2_m2_k6_12
theorem ac7_fam_k7_t2_m2_k13_15 : replay (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15) ac7_fam_k7_t2_m2_i13 = some ac7_fam_k7_t2_m2_i15 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c14) (ms₂ := ac7_fam_k7_t2_m2_c15) (P := ac7_fam_k7_t2_m2_i13) (R := ac7_fam_k7_t2_m2_i14) (S := ac7_fam_k7_t2_m2_i15) ac7_fam_k7_t2_m2_b14 ac7_fam_k7_t2_m2_b15
theorem ac7_fam_k7_t2_m2_k12_15 : replay (ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ac7_fam_k7_t2_m2_i12 = some ac7_fam_k7_t2_m2_i15 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c13) (ms₂ := (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) (P := ac7_fam_k7_t2_m2_i12) (R := ac7_fam_k7_t2_m2_i13) (S := ac7_fam_k7_t2_m2_i15) ac7_fam_k7_t2_m2_b13 ac7_fam_k7_t2_m2_k13_15
theorem ac7_fam_k7_t2_m2_k16_18 : replay (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18) ac7_fam_k7_t2_m2_i16 = some ac7_fam_k7_t2_m2_i18 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c17) (ms₂ := ac7_fam_k7_t2_m2_c18) (P := ac7_fam_k7_t2_m2_i16) (R := ac7_fam_k7_t2_m2_i17) (S := ac7_fam_k7_t2_m2_i18) ac7_fam_k7_t2_m2_b17 ac7_fam_k7_t2_m2_b18
theorem ac7_fam_k7_t2_m2_k15_18 : replay (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18)) ac7_fam_k7_t2_m2_i15 = some ac7_fam_k7_t2_m2_i18 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c16) (ms₂ := (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18)) (P := ac7_fam_k7_t2_m2_i15) (R := ac7_fam_k7_t2_m2_i16) (S := ac7_fam_k7_t2_m2_i18) ac7_fam_k7_t2_m2_b16 ac7_fam_k7_t2_m2_k16_18
theorem ac7_fam_k7_t2_m2_k12_18 : replay ((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) ac7_fam_k7_t2_m2_i12 = some ac7_fam_k7_t2_m2_i18 :=
  replay_concat (ms₁ := (ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15))) (ms₂ := (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) (P := ac7_fam_k7_t2_m2_i12) (R := ac7_fam_k7_t2_m2_i15) (S := ac7_fam_k7_t2_m2_i18) ac7_fam_k7_t2_m2_k12_15 ac7_fam_k7_t2_m2_k15_18
theorem ac7_fam_k7_t2_m2_k19_21 : replay (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21) ac7_fam_k7_t2_m2_i19 = some ac7_fam_k7_t2_m2_i21 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c20) (ms₂ := ac7_fam_k7_t2_m2_c21) (P := ac7_fam_k7_t2_m2_i19) (R := ac7_fam_k7_t2_m2_i20) (S := ac7_fam_k7_t2_m2_i21) ac7_fam_k7_t2_m2_b20 ac7_fam_k7_t2_m2_b21
theorem ac7_fam_k7_t2_m2_k18_21 : replay (ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ac7_fam_k7_t2_m2_i18 = some ac7_fam_k7_t2_m2_i21 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c19) (ms₂ := (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) (P := ac7_fam_k7_t2_m2_i18) (R := ac7_fam_k7_t2_m2_i19) (S := ac7_fam_k7_t2_m2_i21) ac7_fam_k7_t2_m2_b19 ac7_fam_k7_t2_m2_k19_21
theorem ac7_fam_k7_t2_m2_k22_24 : replay (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24) ac7_fam_k7_t2_m2_i22 = some ac7_fam_k7_t2_m2_i24 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c23) (ms₂ := ac7_fam_k7_t2_m2_c24) (P := ac7_fam_k7_t2_m2_i22) (R := ac7_fam_k7_t2_m2_i23) (S := ac7_fam_k7_t2_m2_i24) ac7_fam_k7_t2_m2_b23 ac7_fam_k7_t2_m2_b24
theorem ac7_fam_k7_t2_m2_k21_24 : replay (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24)) ac7_fam_k7_t2_m2_i21 = some ac7_fam_k7_t2_m2_i24 :=
  replay_concat (ms₁ := ac7_fam_k7_t2_m2_c22) (ms₂ := (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24)) (P := ac7_fam_k7_t2_m2_i21) (R := ac7_fam_k7_t2_m2_i22) (S := ac7_fam_k7_t2_m2_i24) ac7_fam_k7_t2_m2_b22 ac7_fam_k7_t2_m2_k22_24
theorem ac7_fam_k7_t2_m2_k18_24 : replay ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24))) ac7_fam_k7_t2_m2_i18 = some ac7_fam_k7_t2_m2_i24 :=
  replay_concat (ms₁ := (ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21))) (ms₂ := (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24))) (P := ac7_fam_k7_t2_m2_i18) (R := ac7_fam_k7_t2_m2_i21) (S := ac7_fam_k7_t2_m2_i24) ac7_fam_k7_t2_m2_k18_21 ac7_fam_k7_t2_m2_k21_24
theorem ac7_fam_k7_t2_m2_k12_24 : replay (((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) ++ ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24)))) ac7_fam_k7_t2_m2_i12 = some ac7_fam_k7_t2_m2_i24 :=
  replay_concat (ms₁ := ((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18)))) (ms₂ := ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24)))) (P := ac7_fam_k7_t2_m2_i12) (R := ac7_fam_k7_t2_m2_i18) (S := ac7_fam_k7_t2_m2_i24) ac7_fam_k7_t2_m2_k12_18 ac7_fam_k7_t2_m2_k18_24
theorem ac7_fam_k7_t2_m2_k0_24 : replay ((((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) ++ ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)))) ++ (((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) ++ ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24))))) ac7_fam_k7_t2_m2_s = some ac7_fam_k7_t2_m2_i24 :=
  replay_concat (ms₁ := (((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) ++ ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12))))) (ms₂ := (((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) ++ ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24))))) (P := ac7_fam_k7_t2_m2_s) (R := ac7_fam_k7_t2_m2_i12) (S := ac7_fam_k7_t2_m2_i24) ac7_fam_k7_t2_m2_k0_12 ac7_fam_k7_t2_m2_k12_24

/-- `fam_k7_t2_m2.cert` checked: replaying its 48 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k7_t2_m2_replay : replay ((((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) ++ ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)))) ++ (((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) ++ ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24))))) ac7_fam_k7_t2_m2_s = some ac7_fam_k7_t2_m2_i24 := ac7_fam_k7_t2_m2_k0_24

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k7_t2_m2_checked : checkCert ((((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) ++ ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)))) ++ (((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) ++ ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24))))) ac7_fam_k7_t2_m2_s ac7_fam_k7_t2_m2_i24 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k7_t2_m2_replay

/-- The endpoints of `fam_k7_t2_m2.cert` are the presentations `<x,y | x^7, y^2, [x^1,y]>`
    and `<x,y | x^7, y^2, [x^3,y]>` of the statement. -/
theorem ac7_fam_k7_t2_m2_endpoints :
    metz 7 2 1 = ac7_fam_k7_t2_m2_s ∧ metz 7 2 3 = ac7_fam_k7_t2_m2_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 48-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k7_t2_m2_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 7 2 1) = some (metz 7 2 3) := by
  refine ⟨((((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) ++ ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)))) ++ (((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) ++ ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24))))), ?_⟩
  calc replay ((((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) ++ ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)))) ++ (((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) ++ ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24))))) (metz 7 2 1) = replay ((((ac7_fam_k7_t2_m2_c1 ++ (ac7_fam_k7_t2_m2_c2 ++ ac7_fam_k7_t2_m2_c3)) ++ (ac7_fam_k7_t2_m2_c4 ++ (ac7_fam_k7_t2_m2_c5 ++ ac7_fam_k7_t2_m2_c6))) ++ ((ac7_fam_k7_t2_m2_c7 ++ (ac7_fam_k7_t2_m2_c8 ++ ac7_fam_k7_t2_m2_c9)) ++ (ac7_fam_k7_t2_m2_c10 ++ (ac7_fam_k7_t2_m2_c11 ++ ac7_fam_k7_t2_m2_c12)))) ++ (((ac7_fam_k7_t2_m2_c13 ++ (ac7_fam_k7_t2_m2_c14 ++ ac7_fam_k7_t2_m2_c15)) ++ (ac7_fam_k7_t2_m2_c16 ++ (ac7_fam_k7_t2_m2_c17 ++ ac7_fam_k7_t2_m2_c18))) ++ ((ac7_fam_k7_t2_m2_c19 ++ (ac7_fam_k7_t2_m2_c20 ++ ac7_fam_k7_t2_m2_c21)) ++ (ac7_fam_k7_t2_m2_c22 ++ (ac7_fam_k7_t2_m2_c23 ++ ac7_fam_k7_t2_m2_c24))))) ac7_fam_k7_t2_m2_s := by rw [ac7_fam_k7_t2_m2_endpoints.1]
    _ = some ac7_fam_k7_t2_m2_e := ac7_fam_k7_t2_m2_replay
    _ = some (metz 7 2 3) := by rw [ac7_fam_k7_t2_m2_endpoints.2]

/-! ### `fam_k7_t3_m5.cert`: Metzler family, k=7 t=3 m=5  <x,y | x^7, y^5, [x,y]>  ->  <x,y | x^7, y^5, [x^2,y]>. -/

/-- The start tuple of `fam_k7_t3_m5.cert` (48 Q**-moves to the end tuple). -/
def ac7_fam_k7_t3_m5_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k7_t3_m5_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k7_t3_m5_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false)]]
def ac7_fam_k7_t3_m5_i3 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t3_m5_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k7_t3_m5_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false)]]
def ac7_fam_k7_t3_m5_i6 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (2, true), (2, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true)]]
def ac7_fam_k7_t3_m5_i7 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true)]]
def ac7_fam_k7_t3_m5_i8 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t3_m5_i9 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t3_m5_i10 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t3_m5_i11 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t3_m5_i12 : QPres := mkQPres 3 4 [[(2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t3_m5_i13 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t3_m5_i14 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (0, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t3_m5_i15 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (0, true), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t3_m5_i16 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t3_m5_i17 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t3_m5_i18 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t3_m5_i19 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k7_t3_m5_i20 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k7_t3_m5_i21 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (1, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k7_t3_m5_i22 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_fam_k7_t3_m5_i23 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_fam_k7_t3_m5_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]
def ac7_fam_k7_t3_m5_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]

def ac7_fam_k7_t3_m5_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k7_t3_m5_c2 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k7_t3_m5_c3 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k7_t3_m5_c4 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false)] ]
def ac7_fam_k7_t3_m5_c5 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true)] ]
def ac7_fam_k7_t3_m5_c6 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k7_t3_m5_c7 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (2, true), (2, true)] ]
def ac7_fam_k7_t3_m5_c8 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (0, true), (2, false)] ]
def ac7_fam_k7_t3_m5_c9 : List QMove :=
  [ .conj 0 [(2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k7_t3_m5_c10 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false)],
    .conj 0 [(0, true), (1, true), (2, true), (2, true)] ]
def ac7_fam_k7_t3_m5_c11 : List QMove :=
  [ .lmul 2 0,
    .conj 0 [(2, false), (2, false), (1, false), (0, false)] ]
def ac7_fam_k7_t3_m5_c12 : List QMove :=
  [ .inv 0,
    .lmul 2 0 ]
def ac7_fam_k7_t3_m5_c13 : List QMove :=
  [ .inv 0,
    .nijinv 0 2 ]
def ac7_fam_k7_t3_m5_c14 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k7_t3_m5_c15 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true)] ]
def ac7_fam_k7_t3_m5_c16 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k7_t3_m5_c17 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k7_t3_m5_c18 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k7_t3_m5_c19 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k7_t3_m5_c20 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false)] ]
def ac7_fam_k7_t3_m5_c21 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k7_t3_m5_c22 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k7_t3_m5_c23 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)] ]
def ac7_fam_k7_t3_m5_c24 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b1 :
    replay ac7_fam_k7_t3_m5_c1 ac7_fam_k7_t3_m5_s = some ac7_fam_k7_t3_m5_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b2 :
    replay ac7_fam_k7_t3_m5_c2 ac7_fam_k7_t3_m5_i1 = some ac7_fam_k7_t3_m5_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b3 :
    replay ac7_fam_k7_t3_m5_c3 ac7_fam_k7_t3_m5_i2 = some ac7_fam_k7_t3_m5_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b4 :
    replay ac7_fam_k7_t3_m5_c4 ac7_fam_k7_t3_m5_i3 = some ac7_fam_k7_t3_m5_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b5 :
    replay ac7_fam_k7_t3_m5_c5 ac7_fam_k7_t3_m5_i4 = some ac7_fam_k7_t3_m5_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b6 :
    replay ac7_fam_k7_t3_m5_c6 ac7_fam_k7_t3_m5_i5 = some ac7_fam_k7_t3_m5_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b7 :
    replay ac7_fam_k7_t3_m5_c7 ac7_fam_k7_t3_m5_i6 = some ac7_fam_k7_t3_m5_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b8 :
    replay ac7_fam_k7_t3_m5_c8 ac7_fam_k7_t3_m5_i7 = some ac7_fam_k7_t3_m5_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b9 :
    replay ac7_fam_k7_t3_m5_c9 ac7_fam_k7_t3_m5_i8 = some ac7_fam_k7_t3_m5_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b10 :
    replay ac7_fam_k7_t3_m5_c10 ac7_fam_k7_t3_m5_i9 = some ac7_fam_k7_t3_m5_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b11 :
    replay ac7_fam_k7_t3_m5_c11 ac7_fam_k7_t3_m5_i10 = some ac7_fam_k7_t3_m5_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b12 :
    replay ac7_fam_k7_t3_m5_c12 ac7_fam_k7_t3_m5_i11 = some ac7_fam_k7_t3_m5_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b13 :
    replay ac7_fam_k7_t3_m5_c13 ac7_fam_k7_t3_m5_i12 = some ac7_fam_k7_t3_m5_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b14 :
    replay ac7_fam_k7_t3_m5_c14 ac7_fam_k7_t3_m5_i13 = some ac7_fam_k7_t3_m5_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b15 :
    replay ac7_fam_k7_t3_m5_c15 ac7_fam_k7_t3_m5_i14 = some ac7_fam_k7_t3_m5_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b16 :
    replay ac7_fam_k7_t3_m5_c16 ac7_fam_k7_t3_m5_i15 = some ac7_fam_k7_t3_m5_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b17 :
    replay ac7_fam_k7_t3_m5_c17 ac7_fam_k7_t3_m5_i16 = some ac7_fam_k7_t3_m5_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b18 :
    replay ac7_fam_k7_t3_m5_c18 ac7_fam_k7_t3_m5_i17 = some ac7_fam_k7_t3_m5_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b19 :
    replay ac7_fam_k7_t3_m5_c19 ac7_fam_k7_t3_m5_i18 = some ac7_fam_k7_t3_m5_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b20 :
    replay ac7_fam_k7_t3_m5_c20 ac7_fam_k7_t3_m5_i19 = some ac7_fam_k7_t3_m5_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b21 :
    replay ac7_fam_k7_t3_m5_c21 ac7_fam_k7_t3_m5_i20 = some ac7_fam_k7_t3_m5_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b22 :
    replay ac7_fam_k7_t3_m5_c22 ac7_fam_k7_t3_m5_i21 = some ac7_fam_k7_t3_m5_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b23 :
    replay ac7_fam_k7_t3_m5_c23 ac7_fam_k7_t3_m5_i22 = some ac7_fam_k7_t3_m5_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t3_m5_b24 :
    replay ac7_fam_k7_t3_m5_c24 ac7_fam_k7_t3_m5_i23 = some ac7_fam_k7_t3_m5_i24 := by decide

theorem ac7_fam_k7_t3_m5_k1_3 : replay (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3) ac7_fam_k7_t3_m5_i1 = some ac7_fam_k7_t3_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c2) (ms₂ := ac7_fam_k7_t3_m5_c3) (P := ac7_fam_k7_t3_m5_i1) (R := ac7_fam_k7_t3_m5_i2) (S := ac7_fam_k7_t3_m5_i3) ac7_fam_k7_t3_m5_b2 ac7_fam_k7_t3_m5_b3
theorem ac7_fam_k7_t3_m5_k0_3 : replay (ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ac7_fam_k7_t3_m5_s = some ac7_fam_k7_t3_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c1) (ms₂ := (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) (P := ac7_fam_k7_t3_m5_s) (R := ac7_fam_k7_t3_m5_i1) (S := ac7_fam_k7_t3_m5_i3) ac7_fam_k7_t3_m5_b1 ac7_fam_k7_t3_m5_k1_3
theorem ac7_fam_k7_t3_m5_k4_6 : replay (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6) ac7_fam_k7_t3_m5_i4 = some ac7_fam_k7_t3_m5_i6 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c5) (ms₂ := ac7_fam_k7_t3_m5_c6) (P := ac7_fam_k7_t3_m5_i4) (R := ac7_fam_k7_t3_m5_i5) (S := ac7_fam_k7_t3_m5_i6) ac7_fam_k7_t3_m5_b5 ac7_fam_k7_t3_m5_b6
theorem ac7_fam_k7_t3_m5_k3_6 : replay (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6)) ac7_fam_k7_t3_m5_i3 = some ac7_fam_k7_t3_m5_i6 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c4) (ms₂ := (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6)) (P := ac7_fam_k7_t3_m5_i3) (R := ac7_fam_k7_t3_m5_i4) (S := ac7_fam_k7_t3_m5_i6) ac7_fam_k7_t3_m5_b4 ac7_fam_k7_t3_m5_k4_6
theorem ac7_fam_k7_t3_m5_k0_6 : replay ((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) ac7_fam_k7_t3_m5_s = some ac7_fam_k7_t3_m5_i6 :=
  replay_concat (ms₁ := (ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3))) (ms₂ := (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) (P := ac7_fam_k7_t3_m5_s) (R := ac7_fam_k7_t3_m5_i3) (S := ac7_fam_k7_t3_m5_i6) ac7_fam_k7_t3_m5_k0_3 ac7_fam_k7_t3_m5_k3_6
theorem ac7_fam_k7_t3_m5_k7_9 : replay (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9) ac7_fam_k7_t3_m5_i7 = some ac7_fam_k7_t3_m5_i9 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c8) (ms₂ := ac7_fam_k7_t3_m5_c9) (P := ac7_fam_k7_t3_m5_i7) (R := ac7_fam_k7_t3_m5_i8) (S := ac7_fam_k7_t3_m5_i9) ac7_fam_k7_t3_m5_b8 ac7_fam_k7_t3_m5_b9
theorem ac7_fam_k7_t3_m5_k6_9 : replay (ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ac7_fam_k7_t3_m5_i6 = some ac7_fam_k7_t3_m5_i9 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c7) (ms₂ := (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) (P := ac7_fam_k7_t3_m5_i6) (R := ac7_fam_k7_t3_m5_i7) (S := ac7_fam_k7_t3_m5_i9) ac7_fam_k7_t3_m5_b7 ac7_fam_k7_t3_m5_k7_9
theorem ac7_fam_k7_t3_m5_k10_12 : replay (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12) ac7_fam_k7_t3_m5_i10 = some ac7_fam_k7_t3_m5_i12 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c11) (ms₂ := ac7_fam_k7_t3_m5_c12) (P := ac7_fam_k7_t3_m5_i10) (R := ac7_fam_k7_t3_m5_i11) (S := ac7_fam_k7_t3_m5_i12) ac7_fam_k7_t3_m5_b11 ac7_fam_k7_t3_m5_b12
theorem ac7_fam_k7_t3_m5_k9_12 : replay (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)) ac7_fam_k7_t3_m5_i9 = some ac7_fam_k7_t3_m5_i12 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c10) (ms₂ := (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)) (P := ac7_fam_k7_t3_m5_i9) (R := ac7_fam_k7_t3_m5_i10) (S := ac7_fam_k7_t3_m5_i12) ac7_fam_k7_t3_m5_b10 ac7_fam_k7_t3_m5_k10_12
theorem ac7_fam_k7_t3_m5_k6_12 : replay ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12))) ac7_fam_k7_t3_m5_i6 = some ac7_fam_k7_t3_m5_i12 :=
  replay_concat (ms₁ := (ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9))) (ms₂ := (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12))) (P := ac7_fam_k7_t3_m5_i6) (R := ac7_fam_k7_t3_m5_i9) (S := ac7_fam_k7_t3_m5_i12) ac7_fam_k7_t3_m5_k6_9 ac7_fam_k7_t3_m5_k9_12
theorem ac7_fam_k7_t3_m5_k0_12 : replay (((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) ++ ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)))) ac7_fam_k7_t3_m5_s = some ac7_fam_k7_t3_m5_i12 :=
  replay_concat (ms₁ := ((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6)))) (ms₂ := ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)))) (P := ac7_fam_k7_t3_m5_s) (R := ac7_fam_k7_t3_m5_i6) (S := ac7_fam_k7_t3_m5_i12) ac7_fam_k7_t3_m5_k0_6 ac7_fam_k7_t3_m5_k6_12
theorem ac7_fam_k7_t3_m5_k13_15 : replay (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15) ac7_fam_k7_t3_m5_i13 = some ac7_fam_k7_t3_m5_i15 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c14) (ms₂ := ac7_fam_k7_t3_m5_c15) (P := ac7_fam_k7_t3_m5_i13) (R := ac7_fam_k7_t3_m5_i14) (S := ac7_fam_k7_t3_m5_i15) ac7_fam_k7_t3_m5_b14 ac7_fam_k7_t3_m5_b15
theorem ac7_fam_k7_t3_m5_k12_15 : replay (ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ac7_fam_k7_t3_m5_i12 = some ac7_fam_k7_t3_m5_i15 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c13) (ms₂ := (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) (P := ac7_fam_k7_t3_m5_i12) (R := ac7_fam_k7_t3_m5_i13) (S := ac7_fam_k7_t3_m5_i15) ac7_fam_k7_t3_m5_b13 ac7_fam_k7_t3_m5_k13_15
theorem ac7_fam_k7_t3_m5_k16_18 : replay (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18) ac7_fam_k7_t3_m5_i16 = some ac7_fam_k7_t3_m5_i18 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c17) (ms₂ := ac7_fam_k7_t3_m5_c18) (P := ac7_fam_k7_t3_m5_i16) (R := ac7_fam_k7_t3_m5_i17) (S := ac7_fam_k7_t3_m5_i18) ac7_fam_k7_t3_m5_b17 ac7_fam_k7_t3_m5_b18
theorem ac7_fam_k7_t3_m5_k15_18 : replay (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18)) ac7_fam_k7_t3_m5_i15 = some ac7_fam_k7_t3_m5_i18 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c16) (ms₂ := (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18)) (P := ac7_fam_k7_t3_m5_i15) (R := ac7_fam_k7_t3_m5_i16) (S := ac7_fam_k7_t3_m5_i18) ac7_fam_k7_t3_m5_b16 ac7_fam_k7_t3_m5_k16_18
theorem ac7_fam_k7_t3_m5_k12_18 : replay ((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) ac7_fam_k7_t3_m5_i12 = some ac7_fam_k7_t3_m5_i18 :=
  replay_concat (ms₁ := (ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15))) (ms₂ := (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) (P := ac7_fam_k7_t3_m5_i12) (R := ac7_fam_k7_t3_m5_i15) (S := ac7_fam_k7_t3_m5_i18) ac7_fam_k7_t3_m5_k12_15 ac7_fam_k7_t3_m5_k15_18
theorem ac7_fam_k7_t3_m5_k19_21 : replay (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21) ac7_fam_k7_t3_m5_i19 = some ac7_fam_k7_t3_m5_i21 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c20) (ms₂ := ac7_fam_k7_t3_m5_c21) (P := ac7_fam_k7_t3_m5_i19) (R := ac7_fam_k7_t3_m5_i20) (S := ac7_fam_k7_t3_m5_i21) ac7_fam_k7_t3_m5_b20 ac7_fam_k7_t3_m5_b21
theorem ac7_fam_k7_t3_m5_k18_21 : replay (ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ac7_fam_k7_t3_m5_i18 = some ac7_fam_k7_t3_m5_i21 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c19) (ms₂ := (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) (P := ac7_fam_k7_t3_m5_i18) (R := ac7_fam_k7_t3_m5_i19) (S := ac7_fam_k7_t3_m5_i21) ac7_fam_k7_t3_m5_b19 ac7_fam_k7_t3_m5_k19_21
theorem ac7_fam_k7_t3_m5_k22_24 : replay (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24) ac7_fam_k7_t3_m5_i22 = some ac7_fam_k7_t3_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c23) (ms₂ := ac7_fam_k7_t3_m5_c24) (P := ac7_fam_k7_t3_m5_i22) (R := ac7_fam_k7_t3_m5_i23) (S := ac7_fam_k7_t3_m5_i24) ac7_fam_k7_t3_m5_b23 ac7_fam_k7_t3_m5_b24
theorem ac7_fam_k7_t3_m5_k21_24 : replay (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24)) ac7_fam_k7_t3_m5_i21 = some ac7_fam_k7_t3_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k7_t3_m5_c22) (ms₂ := (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24)) (P := ac7_fam_k7_t3_m5_i21) (R := ac7_fam_k7_t3_m5_i22) (S := ac7_fam_k7_t3_m5_i24) ac7_fam_k7_t3_m5_b22 ac7_fam_k7_t3_m5_k22_24
theorem ac7_fam_k7_t3_m5_k18_24 : replay ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24))) ac7_fam_k7_t3_m5_i18 = some ac7_fam_k7_t3_m5_i24 :=
  replay_concat (ms₁ := (ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21))) (ms₂ := (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24))) (P := ac7_fam_k7_t3_m5_i18) (R := ac7_fam_k7_t3_m5_i21) (S := ac7_fam_k7_t3_m5_i24) ac7_fam_k7_t3_m5_k18_21 ac7_fam_k7_t3_m5_k21_24
theorem ac7_fam_k7_t3_m5_k12_24 : replay (((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) ++ ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24)))) ac7_fam_k7_t3_m5_i12 = some ac7_fam_k7_t3_m5_i24 :=
  replay_concat (ms₁ := ((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18)))) (ms₂ := ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24)))) (P := ac7_fam_k7_t3_m5_i12) (R := ac7_fam_k7_t3_m5_i18) (S := ac7_fam_k7_t3_m5_i24) ac7_fam_k7_t3_m5_k12_18 ac7_fam_k7_t3_m5_k18_24
theorem ac7_fam_k7_t3_m5_k0_24 : replay ((((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) ++ ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)))) ++ (((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) ++ ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24))))) ac7_fam_k7_t3_m5_s = some ac7_fam_k7_t3_m5_i24 :=
  replay_concat (ms₁ := (((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) ++ ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12))))) (ms₂ := (((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) ++ ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24))))) (P := ac7_fam_k7_t3_m5_s) (R := ac7_fam_k7_t3_m5_i12) (S := ac7_fam_k7_t3_m5_i24) ac7_fam_k7_t3_m5_k0_12 ac7_fam_k7_t3_m5_k12_24

/-- `fam_k7_t3_m5.cert` checked: replaying its 48 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k7_t3_m5_replay : replay ((((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) ++ ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)))) ++ (((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) ++ ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24))))) ac7_fam_k7_t3_m5_s = some ac7_fam_k7_t3_m5_i24 := ac7_fam_k7_t3_m5_k0_24

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k7_t3_m5_checked : checkCert ((((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) ++ ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)))) ++ (((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) ++ ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24))))) ac7_fam_k7_t3_m5_s ac7_fam_k7_t3_m5_i24 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k7_t3_m5_replay

/-- The endpoints of `fam_k7_t3_m5.cert` are the presentations `<x,y | x^7, y^5, [x^1,y]>`
    and `<x,y | x^7, y^5, [x^2,y]>` of the statement. -/
theorem ac7_fam_k7_t3_m5_endpoints :
    metz 7 5 1 = ac7_fam_k7_t3_m5_s ∧ metz 7 5 2 = ac7_fam_k7_t3_m5_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 48-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k7_t3_m5_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 7 5 1) = some (metz 7 5 2) := by
  refine ⟨((((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) ++ ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)))) ++ (((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) ++ ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24))))), ?_⟩
  calc replay ((((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) ++ ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)))) ++ (((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) ++ ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24))))) (metz 7 5 1) = replay ((((ac7_fam_k7_t3_m5_c1 ++ (ac7_fam_k7_t3_m5_c2 ++ ac7_fam_k7_t3_m5_c3)) ++ (ac7_fam_k7_t3_m5_c4 ++ (ac7_fam_k7_t3_m5_c5 ++ ac7_fam_k7_t3_m5_c6))) ++ ((ac7_fam_k7_t3_m5_c7 ++ (ac7_fam_k7_t3_m5_c8 ++ ac7_fam_k7_t3_m5_c9)) ++ (ac7_fam_k7_t3_m5_c10 ++ (ac7_fam_k7_t3_m5_c11 ++ ac7_fam_k7_t3_m5_c12)))) ++ (((ac7_fam_k7_t3_m5_c13 ++ (ac7_fam_k7_t3_m5_c14 ++ ac7_fam_k7_t3_m5_c15)) ++ (ac7_fam_k7_t3_m5_c16 ++ (ac7_fam_k7_t3_m5_c17 ++ ac7_fam_k7_t3_m5_c18))) ++ ((ac7_fam_k7_t3_m5_c19 ++ (ac7_fam_k7_t3_m5_c20 ++ ac7_fam_k7_t3_m5_c21)) ++ (ac7_fam_k7_t3_m5_c22 ++ (ac7_fam_k7_t3_m5_c23 ++ ac7_fam_k7_t3_m5_c24))))) ac7_fam_k7_t3_m5_s := by rw [ac7_fam_k7_t3_m5_endpoints.1]
    _ = some ac7_fam_k7_t3_m5_e := ac7_fam_k7_t3_m5_replay
    _ = some (metz 7 5 2) := by rw [ac7_fam_k7_t3_m5_endpoints.2]

/-! ### `fam_k7_t6_m1.cert`: Metzler family, k=7 t=6 m=1  <x,y | x^7, y^1, [x,y]>  ->  <x,y | x^7, y^1, [x^1,y]>. -/

/-- The start tuple of `fam_k7_t6_m1.cert` (56 Q**-moves to the end tuple). -/
def ac7_fam_k7_t6_m1_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k7_t6_m1_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k7_t6_m1_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false)]]
def ac7_fam_k7_t6_m1_i3 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k7_t6_m1_i4 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k7_t6_m1_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k7_t6_m1_i6 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k7_t6_m1_i7 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k7_t6_m1_i8 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i9 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i10 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (2, false)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i11 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i12 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (0, true), (0, true), (2, false)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i13 : QPres := mkQPres 3 4 [[(2, true), (2, true), (0, true), (2, false)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i14 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i15 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (0, true), (1, false), (0, false)], [(1, true)], [(0, true), (1, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i16 : QPres := mkQPres 3 4 [[(2, false), (0, false)], [(1, true)], [(0, true), (1, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i17 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true)], [(2, false), (1, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k7_t6_m1_i18 : QPres := mkQPres 2 3 [[(0, true)], [(1, false), (0, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t6_m1_i19 : QPres := mkQPres 2 3 [[(0, true)], [(1, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t6_m1_i20 : QPres := mkQPres 2 3 [[(1, true), (0, false)], [(1, true), (1, true), (0, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k7_t6_m1_i21 : QPres := mkQPres 2 3 [[(1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t6_m1_i22 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (1, true), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k7_t6_m1_i23 : QPres := mkQPres 2 3 [[(1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (1, true), (0, false), (1, false)], [(1, false)]]
def ac7_fam_k7_t6_m1_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (1, true), (0, false), (1, false)], [(1, false)]]
def ac7_fam_k7_t6_m1_i25 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (0, true), (1, false), (0, false)], [(1, false)]]
def ac7_fam_k7_t6_m1_i26 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (1, true), (0, false), (1, false), (1, false)], [(1, true), (0, true), (1, false), (0, false)]]
def ac7_fam_k7_t6_m1_i27 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false)], [(1, true), (0, true), (1, false), (0, false)]]
def ac7_fam_k7_t6_m1_i28 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k7_t6_m1_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true)], [(0, true), (1, true), (0, false), (1, false)]]

def ac7_fam_k7_t6_m1_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k7_t6_m1_c2 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k7_t6_m1_c3 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k7_t6_m1_c4 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k7_t6_m1_c5 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k7_t6_m1_c6 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k7_t6_m1_c7 : List QMove :=
  [ .conj 0 [(2, false), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (0, false), (0, false), (0, false), (2, true)] ]
def ac7_fam_k7_t6_m1_c8 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (0, true), (0, true), (0, true), (0, true), (2, false)] ]
def ac7_fam_k7_t6_m1_c9 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (0, false), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k7_t6_m1_c10 : List QMove :=
  [ .conj 0 [(2, false), (0, true), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (0, false), (2, true)] ]
def ac7_fam_k7_t6_m1_c11 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (0, true), (0, true), (2, false)] ]
def ac7_fam_k7_t6_m1_c12 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k7_t6_m1_c13 : List QMove :=
  [ .conj 0 [(2, false), (0, true), (2, false)],
    .conj 0 [(2, true), (2, true)] ]
def ac7_fam_k7_t6_m1_c14 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false)] ]
def ac7_fam_k7_t6_m1_c15 : List QMove :=
  [ .conj 0 [(0, true), (1, true), (2, true)],
    .lmul 2 0 ]
def ac7_fam_k7_t6_m1_c16 : List QMove :=
  [ .conj 0 [(2, false), (1, false), (0, false)],
    .inv 0 ]
def ac7_fam_k7_t6_m1_c17 : List QMove :=
  [ .lmul 2 0,
    .inv 0 ]
def ac7_fam_k7_t6_m1_c18 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k7_t6_m1_c19 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true)] ]
def ac7_fam_k7_t6_m1_c20 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k7_t6_m1_c21 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k7_t6_m1_c22 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k7_t6_m1_c23 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k7_t6_m1_c24 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false)] ]
def ac7_fam_k7_t6_m1_c25 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k7_t6_m1_c26 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k7_t6_m1_c27 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (1, false), (0, false)] ]
def ac7_fam_k7_t6_m1_c28 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b1 :
    replay ac7_fam_k7_t6_m1_c1 ac7_fam_k7_t6_m1_s = some ac7_fam_k7_t6_m1_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b2 :
    replay ac7_fam_k7_t6_m1_c2 ac7_fam_k7_t6_m1_i1 = some ac7_fam_k7_t6_m1_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b3 :
    replay ac7_fam_k7_t6_m1_c3 ac7_fam_k7_t6_m1_i2 = some ac7_fam_k7_t6_m1_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b4 :
    replay ac7_fam_k7_t6_m1_c4 ac7_fam_k7_t6_m1_i3 = some ac7_fam_k7_t6_m1_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b5 :
    replay ac7_fam_k7_t6_m1_c5 ac7_fam_k7_t6_m1_i4 = some ac7_fam_k7_t6_m1_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b6 :
    replay ac7_fam_k7_t6_m1_c6 ac7_fam_k7_t6_m1_i5 = some ac7_fam_k7_t6_m1_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b7 :
    replay ac7_fam_k7_t6_m1_c7 ac7_fam_k7_t6_m1_i6 = some ac7_fam_k7_t6_m1_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b8 :
    replay ac7_fam_k7_t6_m1_c8 ac7_fam_k7_t6_m1_i7 = some ac7_fam_k7_t6_m1_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b9 :
    replay ac7_fam_k7_t6_m1_c9 ac7_fam_k7_t6_m1_i8 = some ac7_fam_k7_t6_m1_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b10 :
    replay ac7_fam_k7_t6_m1_c10 ac7_fam_k7_t6_m1_i9 = some ac7_fam_k7_t6_m1_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b11 :
    replay ac7_fam_k7_t6_m1_c11 ac7_fam_k7_t6_m1_i10 = some ac7_fam_k7_t6_m1_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b12 :
    replay ac7_fam_k7_t6_m1_c12 ac7_fam_k7_t6_m1_i11 = some ac7_fam_k7_t6_m1_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b13 :
    replay ac7_fam_k7_t6_m1_c13 ac7_fam_k7_t6_m1_i12 = some ac7_fam_k7_t6_m1_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b14 :
    replay ac7_fam_k7_t6_m1_c14 ac7_fam_k7_t6_m1_i13 = some ac7_fam_k7_t6_m1_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b15 :
    replay ac7_fam_k7_t6_m1_c15 ac7_fam_k7_t6_m1_i14 = some ac7_fam_k7_t6_m1_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b16 :
    replay ac7_fam_k7_t6_m1_c16 ac7_fam_k7_t6_m1_i15 = some ac7_fam_k7_t6_m1_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b17 :
    replay ac7_fam_k7_t6_m1_c17 ac7_fam_k7_t6_m1_i16 = some ac7_fam_k7_t6_m1_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b18 :
    replay ac7_fam_k7_t6_m1_c18 ac7_fam_k7_t6_m1_i17 = some ac7_fam_k7_t6_m1_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b19 :
    replay ac7_fam_k7_t6_m1_c19 ac7_fam_k7_t6_m1_i18 = some ac7_fam_k7_t6_m1_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b20 :
    replay ac7_fam_k7_t6_m1_c20 ac7_fam_k7_t6_m1_i19 = some ac7_fam_k7_t6_m1_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b21 :
    replay ac7_fam_k7_t6_m1_c21 ac7_fam_k7_t6_m1_i20 = some ac7_fam_k7_t6_m1_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b22 :
    replay ac7_fam_k7_t6_m1_c22 ac7_fam_k7_t6_m1_i21 = some ac7_fam_k7_t6_m1_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b23 :
    replay ac7_fam_k7_t6_m1_c23 ac7_fam_k7_t6_m1_i22 = some ac7_fam_k7_t6_m1_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b24 :
    replay ac7_fam_k7_t6_m1_c24 ac7_fam_k7_t6_m1_i23 = some ac7_fam_k7_t6_m1_i24 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b25 :
    replay ac7_fam_k7_t6_m1_c25 ac7_fam_k7_t6_m1_i24 = some ac7_fam_k7_t6_m1_i25 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b26 :
    replay ac7_fam_k7_t6_m1_c26 ac7_fam_k7_t6_m1_i25 = some ac7_fam_k7_t6_m1_i26 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b27 :
    replay ac7_fam_k7_t6_m1_c27 ac7_fam_k7_t6_m1_i26 = some ac7_fam_k7_t6_m1_i27 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k7_t6_m1_b28 :
    replay ac7_fam_k7_t6_m1_c28 ac7_fam_k7_t6_m1_i27 = some ac7_fam_k7_t6_m1_i28 := by decide

theorem ac7_fam_k7_t6_m1_k1_3 : replay (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3) ac7_fam_k7_t6_m1_i1 = some ac7_fam_k7_t6_m1_i3 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c2) (ms₂ := ac7_fam_k7_t6_m1_c3) (P := ac7_fam_k7_t6_m1_i1) (R := ac7_fam_k7_t6_m1_i2) (S := ac7_fam_k7_t6_m1_i3) ac7_fam_k7_t6_m1_b2 ac7_fam_k7_t6_m1_b3
theorem ac7_fam_k7_t6_m1_k0_3 : replay (ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ac7_fam_k7_t6_m1_s = some ac7_fam_k7_t6_m1_i3 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c1) (ms₂ := (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) (P := ac7_fam_k7_t6_m1_s) (R := ac7_fam_k7_t6_m1_i1) (S := ac7_fam_k7_t6_m1_i3) ac7_fam_k7_t6_m1_b1 ac7_fam_k7_t6_m1_k1_3
theorem ac7_fam_k7_t6_m1_k3_5 : replay (ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ac7_fam_k7_t6_m1_i3 = some ac7_fam_k7_t6_m1_i5 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c4) (ms₂ := ac7_fam_k7_t6_m1_c5) (P := ac7_fam_k7_t6_m1_i3) (R := ac7_fam_k7_t6_m1_i4) (S := ac7_fam_k7_t6_m1_i5) ac7_fam_k7_t6_m1_b4 ac7_fam_k7_t6_m1_b5
theorem ac7_fam_k7_t6_m1_k5_7 : replay (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7) ac7_fam_k7_t6_m1_i5 = some ac7_fam_k7_t6_m1_i7 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c6) (ms₂ := ac7_fam_k7_t6_m1_c7) (P := ac7_fam_k7_t6_m1_i5) (R := ac7_fam_k7_t6_m1_i6) (S := ac7_fam_k7_t6_m1_i7) ac7_fam_k7_t6_m1_b6 ac7_fam_k7_t6_m1_b7
theorem ac7_fam_k7_t6_m1_k3_7 : replay ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7)) ac7_fam_k7_t6_m1_i3 = some ac7_fam_k7_t6_m1_i7 :=
  replay_concat (ms₁ := (ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5)) (ms₂ := (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7)) (P := ac7_fam_k7_t6_m1_i3) (R := ac7_fam_k7_t6_m1_i5) (S := ac7_fam_k7_t6_m1_i7) ac7_fam_k7_t6_m1_k3_5 ac7_fam_k7_t6_m1_k5_7
theorem ac7_fam_k7_t6_m1_k0_7 : replay ((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) ac7_fam_k7_t6_m1_s = some ac7_fam_k7_t6_m1_i7 :=
  replay_concat (ms₁ := (ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3))) (ms₂ := ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) (P := ac7_fam_k7_t6_m1_s) (R := ac7_fam_k7_t6_m1_i3) (S := ac7_fam_k7_t6_m1_i7) ac7_fam_k7_t6_m1_k0_3 ac7_fam_k7_t6_m1_k3_7
theorem ac7_fam_k7_t6_m1_k8_10 : replay (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10) ac7_fam_k7_t6_m1_i8 = some ac7_fam_k7_t6_m1_i10 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c9) (ms₂ := ac7_fam_k7_t6_m1_c10) (P := ac7_fam_k7_t6_m1_i8) (R := ac7_fam_k7_t6_m1_i9) (S := ac7_fam_k7_t6_m1_i10) ac7_fam_k7_t6_m1_b9 ac7_fam_k7_t6_m1_b10
theorem ac7_fam_k7_t6_m1_k7_10 : replay (ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ac7_fam_k7_t6_m1_i7 = some ac7_fam_k7_t6_m1_i10 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c8) (ms₂ := (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) (P := ac7_fam_k7_t6_m1_i7) (R := ac7_fam_k7_t6_m1_i8) (S := ac7_fam_k7_t6_m1_i10) ac7_fam_k7_t6_m1_b8 ac7_fam_k7_t6_m1_k8_10
theorem ac7_fam_k7_t6_m1_k10_12 : replay (ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ac7_fam_k7_t6_m1_i10 = some ac7_fam_k7_t6_m1_i12 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c11) (ms₂ := ac7_fam_k7_t6_m1_c12) (P := ac7_fam_k7_t6_m1_i10) (R := ac7_fam_k7_t6_m1_i11) (S := ac7_fam_k7_t6_m1_i12) ac7_fam_k7_t6_m1_b11 ac7_fam_k7_t6_m1_b12
theorem ac7_fam_k7_t6_m1_k12_14 : replay (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14) ac7_fam_k7_t6_m1_i12 = some ac7_fam_k7_t6_m1_i14 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c13) (ms₂ := ac7_fam_k7_t6_m1_c14) (P := ac7_fam_k7_t6_m1_i12) (R := ac7_fam_k7_t6_m1_i13) (S := ac7_fam_k7_t6_m1_i14) ac7_fam_k7_t6_m1_b13 ac7_fam_k7_t6_m1_b14
theorem ac7_fam_k7_t6_m1_k10_14 : replay ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)) ac7_fam_k7_t6_m1_i10 = some ac7_fam_k7_t6_m1_i14 :=
  replay_concat (ms₁ := (ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12)) (ms₂ := (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)) (P := ac7_fam_k7_t6_m1_i10) (R := ac7_fam_k7_t6_m1_i12) (S := ac7_fam_k7_t6_m1_i14) ac7_fam_k7_t6_m1_k10_12 ac7_fam_k7_t6_m1_k12_14
theorem ac7_fam_k7_t6_m1_k7_14 : replay ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14))) ac7_fam_k7_t6_m1_i7 = some ac7_fam_k7_t6_m1_i14 :=
  replay_concat (ms₁ := (ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10))) (ms₂ := ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14))) (P := ac7_fam_k7_t6_m1_i7) (R := ac7_fam_k7_t6_m1_i10) (S := ac7_fam_k7_t6_m1_i14) ac7_fam_k7_t6_m1_k7_10 ac7_fam_k7_t6_m1_k10_14
theorem ac7_fam_k7_t6_m1_k0_14 : replay (((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) ++ ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)))) ac7_fam_k7_t6_m1_s = some ac7_fam_k7_t6_m1_i14 :=
  replay_concat (ms₁ := ((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7)))) (ms₂ := ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)))) (P := ac7_fam_k7_t6_m1_s) (R := ac7_fam_k7_t6_m1_i7) (S := ac7_fam_k7_t6_m1_i14) ac7_fam_k7_t6_m1_k0_7 ac7_fam_k7_t6_m1_k7_14
theorem ac7_fam_k7_t6_m1_k15_17 : replay (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17) ac7_fam_k7_t6_m1_i15 = some ac7_fam_k7_t6_m1_i17 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c16) (ms₂ := ac7_fam_k7_t6_m1_c17) (P := ac7_fam_k7_t6_m1_i15) (R := ac7_fam_k7_t6_m1_i16) (S := ac7_fam_k7_t6_m1_i17) ac7_fam_k7_t6_m1_b16 ac7_fam_k7_t6_m1_b17
theorem ac7_fam_k7_t6_m1_k14_17 : replay (ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ac7_fam_k7_t6_m1_i14 = some ac7_fam_k7_t6_m1_i17 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c15) (ms₂ := (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) (P := ac7_fam_k7_t6_m1_i14) (R := ac7_fam_k7_t6_m1_i15) (S := ac7_fam_k7_t6_m1_i17) ac7_fam_k7_t6_m1_b15 ac7_fam_k7_t6_m1_k15_17
theorem ac7_fam_k7_t6_m1_k17_19 : replay (ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ac7_fam_k7_t6_m1_i17 = some ac7_fam_k7_t6_m1_i19 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c18) (ms₂ := ac7_fam_k7_t6_m1_c19) (P := ac7_fam_k7_t6_m1_i17) (R := ac7_fam_k7_t6_m1_i18) (S := ac7_fam_k7_t6_m1_i19) ac7_fam_k7_t6_m1_b18 ac7_fam_k7_t6_m1_b19
theorem ac7_fam_k7_t6_m1_k19_21 : replay (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21) ac7_fam_k7_t6_m1_i19 = some ac7_fam_k7_t6_m1_i21 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c20) (ms₂ := ac7_fam_k7_t6_m1_c21) (P := ac7_fam_k7_t6_m1_i19) (R := ac7_fam_k7_t6_m1_i20) (S := ac7_fam_k7_t6_m1_i21) ac7_fam_k7_t6_m1_b20 ac7_fam_k7_t6_m1_b21
theorem ac7_fam_k7_t6_m1_k17_21 : replay ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21)) ac7_fam_k7_t6_m1_i17 = some ac7_fam_k7_t6_m1_i21 :=
  replay_concat (ms₁ := (ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19)) (ms₂ := (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21)) (P := ac7_fam_k7_t6_m1_i17) (R := ac7_fam_k7_t6_m1_i19) (S := ac7_fam_k7_t6_m1_i21) ac7_fam_k7_t6_m1_k17_19 ac7_fam_k7_t6_m1_k19_21
theorem ac7_fam_k7_t6_m1_k14_21 : replay ((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) ac7_fam_k7_t6_m1_i14 = some ac7_fam_k7_t6_m1_i21 :=
  replay_concat (ms₁ := (ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17))) (ms₂ := ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) (P := ac7_fam_k7_t6_m1_i14) (R := ac7_fam_k7_t6_m1_i17) (S := ac7_fam_k7_t6_m1_i21) ac7_fam_k7_t6_m1_k14_17 ac7_fam_k7_t6_m1_k17_21
theorem ac7_fam_k7_t6_m1_k22_24 : replay (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24) ac7_fam_k7_t6_m1_i22 = some ac7_fam_k7_t6_m1_i24 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c23) (ms₂ := ac7_fam_k7_t6_m1_c24) (P := ac7_fam_k7_t6_m1_i22) (R := ac7_fam_k7_t6_m1_i23) (S := ac7_fam_k7_t6_m1_i24) ac7_fam_k7_t6_m1_b23 ac7_fam_k7_t6_m1_b24
theorem ac7_fam_k7_t6_m1_k21_24 : replay (ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ac7_fam_k7_t6_m1_i21 = some ac7_fam_k7_t6_m1_i24 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c22) (ms₂ := (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) (P := ac7_fam_k7_t6_m1_i21) (R := ac7_fam_k7_t6_m1_i22) (S := ac7_fam_k7_t6_m1_i24) ac7_fam_k7_t6_m1_b22 ac7_fam_k7_t6_m1_k22_24
theorem ac7_fam_k7_t6_m1_k24_26 : replay (ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ac7_fam_k7_t6_m1_i24 = some ac7_fam_k7_t6_m1_i26 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c25) (ms₂ := ac7_fam_k7_t6_m1_c26) (P := ac7_fam_k7_t6_m1_i24) (R := ac7_fam_k7_t6_m1_i25) (S := ac7_fam_k7_t6_m1_i26) ac7_fam_k7_t6_m1_b25 ac7_fam_k7_t6_m1_b26
theorem ac7_fam_k7_t6_m1_k26_28 : replay (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28) ac7_fam_k7_t6_m1_i26 = some ac7_fam_k7_t6_m1_i28 :=
  replay_concat (ms₁ := ac7_fam_k7_t6_m1_c27) (ms₂ := ac7_fam_k7_t6_m1_c28) (P := ac7_fam_k7_t6_m1_i26) (R := ac7_fam_k7_t6_m1_i27) (S := ac7_fam_k7_t6_m1_i28) ac7_fam_k7_t6_m1_b27 ac7_fam_k7_t6_m1_b28
theorem ac7_fam_k7_t6_m1_k24_28 : replay ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28)) ac7_fam_k7_t6_m1_i24 = some ac7_fam_k7_t6_m1_i28 :=
  replay_concat (ms₁ := (ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26)) (ms₂ := (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28)) (P := ac7_fam_k7_t6_m1_i24) (R := ac7_fam_k7_t6_m1_i26) (S := ac7_fam_k7_t6_m1_i28) ac7_fam_k7_t6_m1_k24_26 ac7_fam_k7_t6_m1_k26_28
theorem ac7_fam_k7_t6_m1_k21_28 : replay ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28))) ac7_fam_k7_t6_m1_i21 = some ac7_fam_k7_t6_m1_i28 :=
  replay_concat (ms₁ := (ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24))) (ms₂ := ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28))) (P := ac7_fam_k7_t6_m1_i21) (R := ac7_fam_k7_t6_m1_i24) (S := ac7_fam_k7_t6_m1_i28) ac7_fam_k7_t6_m1_k21_24 ac7_fam_k7_t6_m1_k24_28
theorem ac7_fam_k7_t6_m1_k14_28 : replay (((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) ++ ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28)))) ac7_fam_k7_t6_m1_i14 = some ac7_fam_k7_t6_m1_i28 :=
  replay_concat (ms₁ := ((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21)))) (ms₂ := ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28)))) (P := ac7_fam_k7_t6_m1_i14) (R := ac7_fam_k7_t6_m1_i21) (S := ac7_fam_k7_t6_m1_i28) ac7_fam_k7_t6_m1_k14_21 ac7_fam_k7_t6_m1_k21_28
theorem ac7_fam_k7_t6_m1_k0_28 : replay ((((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) ++ ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)))) ++ (((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) ++ ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28))))) ac7_fam_k7_t6_m1_s = some ac7_fam_k7_t6_m1_i28 :=
  replay_concat (ms₁ := (((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) ++ ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14))))) (ms₂ := (((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) ++ ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28))))) (P := ac7_fam_k7_t6_m1_s) (R := ac7_fam_k7_t6_m1_i14) (S := ac7_fam_k7_t6_m1_i28) ac7_fam_k7_t6_m1_k0_14 ac7_fam_k7_t6_m1_k14_28

/-- `fam_k7_t6_m1.cert` checked: replaying its 56 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k7_t6_m1_replay : replay ((((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) ++ ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)))) ++ (((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) ++ ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28))))) ac7_fam_k7_t6_m1_s = some ac7_fam_k7_t6_m1_i28 := ac7_fam_k7_t6_m1_k0_28

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k7_t6_m1_checked : checkCert ((((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) ++ ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)))) ++ (((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) ++ ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28))))) ac7_fam_k7_t6_m1_s ac7_fam_k7_t6_m1_i28 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k7_t6_m1_replay

/-- The endpoints of `fam_k7_t6_m1.cert` are the presentations `<x,y | x^7, y^1, [x^1,y]>`
    and `<x,y | x^7, y^1, [x^1,y]>` of the statement. -/
theorem ac7_fam_k7_t6_m1_endpoints :
    metz 7 1 1 = ac7_fam_k7_t6_m1_s ∧ metz 7 1 1 = ac7_fam_k7_t6_m1_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 56-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k7_t6_m1_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 7 1 1) = some (metz 7 1 1) := by
  refine ⟨((((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) ++ ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)))) ++ (((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) ++ ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28))))), ?_⟩
  calc replay ((((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) ++ ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)))) ++ (((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) ++ ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28))))) (metz 7 1 1) = replay ((((ac7_fam_k7_t6_m1_c1 ++ (ac7_fam_k7_t6_m1_c2 ++ ac7_fam_k7_t6_m1_c3)) ++ ((ac7_fam_k7_t6_m1_c4 ++ ac7_fam_k7_t6_m1_c5) ++ (ac7_fam_k7_t6_m1_c6 ++ ac7_fam_k7_t6_m1_c7))) ++ ((ac7_fam_k7_t6_m1_c8 ++ (ac7_fam_k7_t6_m1_c9 ++ ac7_fam_k7_t6_m1_c10)) ++ ((ac7_fam_k7_t6_m1_c11 ++ ac7_fam_k7_t6_m1_c12) ++ (ac7_fam_k7_t6_m1_c13 ++ ac7_fam_k7_t6_m1_c14)))) ++ (((ac7_fam_k7_t6_m1_c15 ++ (ac7_fam_k7_t6_m1_c16 ++ ac7_fam_k7_t6_m1_c17)) ++ ((ac7_fam_k7_t6_m1_c18 ++ ac7_fam_k7_t6_m1_c19) ++ (ac7_fam_k7_t6_m1_c20 ++ ac7_fam_k7_t6_m1_c21))) ++ ((ac7_fam_k7_t6_m1_c22 ++ (ac7_fam_k7_t6_m1_c23 ++ ac7_fam_k7_t6_m1_c24)) ++ ((ac7_fam_k7_t6_m1_c25 ++ ac7_fam_k7_t6_m1_c26) ++ (ac7_fam_k7_t6_m1_c27 ++ ac7_fam_k7_t6_m1_c28))))) ac7_fam_k7_t6_m1_s := by rw [ac7_fam_k7_t6_m1_endpoints.1]
    _ = some ac7_fam_k7_t6_m1_e := ac7_fam_k7_t6_m1_replay
    _ = some (metz 7 1 1) := by rw [ac7_fam_k7_t6_m1_endpoints.2]

/-! ### `fam_k9_t2_m5.cert`: Metzler family, k=9 t=2 m=5  <x,y | x^9, y^5, [x,y]>  ->  <x,y | x^9, y^5, [x^4,y]>. -/

/-- The start tuple of `fam_k9_t2_m5.cert` (52 Q**-moves to the end tuple). -/
def ac7_fam_k9_t2_m5_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k9_t2_m5_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k9_t2_m5_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k9_t2_m5_i3 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k9_t2_m5_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k9_t2_m5_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true)]]
def ac7_fam_k9_t2_m5_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k9_t2_m5_i7 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (2, true)]]
def ac7_fam_k9_t2_m5_i8 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false)]]
def ac7_fam_k9_t2_m5_i9 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t2_m5_i10 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t2_m5_i11 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t2_m5_i12 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t2_m5_i13 : QPres := mkQPres 3 4 [[(2, false), (2, false), (2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t2_m5_i14 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t2_m5_i15 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(2, false), (2, false), (2, false), (2, false), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t2_m5_i16 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k9_t2_m5_i17 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k9_t2_m5_i18 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k9_t2_m5_i19 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k9_t2_m5_i20 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k9_t2_m5_i21 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k9_t2_m5_i22 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k9_t2_m5_i23 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false)], [(1, false), (1, false), (1, false), (1, false), (1, false)]]
def ac7_fam_k9_t2_m5_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k9_t2_m5_i25 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k9_t2_m5_i26 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)]]
def ac7_fam_k9_t2_m5_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true)], [(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (0, false), (1, false)]]

def ac7_fam_k9_t2_m5_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k9_t2_m5_c2 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k9_t2_m5_c3 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k9_t2_m5_c4 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k9_t2_m5_c5 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true)],
    .conj 3 [(0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k9_t2_m5_c6 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k9_t2_m5_c7 : List QMove :=
  [ .conj 3 [(0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k9_t2_m5_c8 : List QMove :=
  [ .conj 3 [(0, true), (0, true)],
    .conj 0 [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true)] ]
def ac7_fam_k9_t2_m5_c9 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (2, false), (2, false), (0, true), (2, false)] ]
def ac7_fam_k9_t2_m5_c10 : List QMove :=
  [ .conj 0 [(2, true), (2, true), (2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k9_t2_m5_c11 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false), (2, false), (2, false)],
    .conj 0 [(0, true), (1, true), (2, true), (2, true), (2, true), (2, true)] ]
def ac7_fam_k9_t2_m5_c12 : List QMove :=
  [ .lmul 2 0,
    .conj 0 [(2, false), (2, false), (2, false), (2, false), (1, false), (0, false)] ]
def ac7_fam_k9_t2_m5_c13 : List QMove :=
  [ .inv 0,
    .lmul 2 0 ]
def ac7_fam_k9_t2_m5_c14 : List QMove :=
  [ .inv 0,
    .nijinv 0 2 ]
def ac7_fam_k9_t2_m5_c15 : List QMove :=
  [ .nijinv 0 2,
    .nijinv 0 2 ]
def ac7_fam_k9_t2_m5_c16 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k9_t2_m5_c17 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true), (1, true), (1, true)] ]
def ac7_fam_k9_t2_m5_c18 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k9_t2_m5_c19 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k9_t2_m5_c20 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k9_t2_m5_c21 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k9_t2_m5_c22 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false), (1, false), (1, false)] ]
def ac7_fam_k9_t2_m5_c23 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k9_t2_m5_c24 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k9_t2_m5_c25 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k9_t2_m5_c26 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b1 :
    replay ac7_fam_k9_t2_m5_c1 ac7_fam_k9_t2_m5_s = some ac7_fam_k9_t2_m5_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b2 :
    replay ac7_fam_k9_t2_m5_c2 ac7_fam_k9_t2_m5_i1 = some ac7_fam_k9_t2_m5_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b3 :
    replay ac7_fam_k9_t2_m5_c3 ac7_fam_k9_t2_m5_i2 = some ac7_fam_k9_t2_m5_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b4 :
    replay ac7_fam_k9_t2_m5_c4 ac7_fam_k9_t2_m5_i3 = some ac7_fam_k9_t2_m5_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b5 :
    replay ac7_fam_k9_t2_m5_c5 ac7_fam_k9_t2_m5_i4 = some ac7_fam_k9_t2_m5_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b6 :
    replay ac7_fam_k9_t2_m5_c6 ac7_fam_k9_t2_m5_i5 = some ac7_fam_k9_t2_m5_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b7 :
    replay ac7_fam_k9_t2_m5_c7 ac7_fam_k9_t2_m5_i6 = some ac7_fam_k9_t2_m5_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b8 :
    replay ac7_fam_k9_t2_m5_c8 ac7_fam_k9_t2_m5_i7 = some ac7_fam_k9_t2_m5_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b9 :
    replay ac7_fam_k9_t2_m5_c9 ac7_fam_k9_t2_m5_i8 = some ac7_fam_k9_t2_m5_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b10 :
    replay ac7_fam_k9_t2_m5_c10 ac7_fam_k9_t2_m5_i9 = some ac7_fam_k9_t2_m5_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b11 :
    replay ac7_fam_k9_t2_m5_c11 ac7_fam_k9_t2_m5_i10 = some ac7_fam_k9_t2_m5_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b12 :
    replay ac7_fam_k9_t2_m5_c12 ac7_fam_k9_t2_m5_i11 = some ac7_fam_k9_t2_m5_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b13 :
    replay ac7_fam_k9_t2_m5_c13 ac7_fam_k9_t2_m5_i12 = some ac7_fam_k9_t2_m5_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b14 :
    replay ac7_fam_k9_t2_m5_c14 ac7_fam_k9_t2_m5_i13 = some ac7_fam_k9_t2_m5_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b15 :
    replay ac7_fam_k9_t2_m5_c15 ac7_fam_k9_t2_m5_i14 = some ac7_fam_k9_t2_m5_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b16 :
    replay ac7_fam_k9_t2_m5_c16 ac7_fam_k9_t2_m5_i15 = some ac7_fam_k9_t2_m5_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b17 :
    replay ac7_fam_k9_t2_m5_c17 ac7_fam_k9_t2_m5_i16 = some ac7_fam_k9_t2_m5_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b18 :
    replay ac7_fam_k9_t2_m5_c18 ac7_fam_k9_t2_m5_i17 = some ac7_fam_k9_t2_m5_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b19 :
    replay ac7_fam_k9_t2_m5_c19 ac7_fam_k9_t2_m5_i18 = some ac7_fam_k9_t2_m5_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b20 :
    replay ac7_fam_k9_t2_m5_c20 ac7_fam_k9_t2_m5_i19 = some ac7_fam_k9_t2_m5_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b21 :
    replay ac7_fam_k9_t2_m5_c21 ac7_fam_k9_t2_m5_i20 = some ac7_fam_k9_t2_m5_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b22 :
    replay ac7_fam_k9_t2_m5_c22 ac7_fam_k9_t2_m5_i21 = some ac7_fam_k9_t2_m5_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b23 :
    replay ac7_fam_k9_t2_m5_c23 ac7_fam_k9_t2_m5_i22 = some ac7_fam_k9_t2_m5_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b24 :
    replay ac7_fam_k9_t2_m5_c24 ac7_fam_k9_t2_m5_i23 = some ac7_fam_k9_t2_m5_i24 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b25 :
    replay ac7_fam_k9_t2_m5_c25 ac7_fam_k9_t2_m5_i24 = some ac7_fam_k9_t2_m5_i25 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t2_m5_b26 :
    replay ac7_fam_k9_t2_m5_c26 ac7_fam_k9_t2_m5_i25 = some ac7_fam_k9_t2_m5_i26 := by decide

theorem ac7_fam_k9_t2_m5_k1_3 : replay (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3) ac7_fam_k9_t2_m5_i1 = some ac7_fam_k9_t2_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c2) (ms₂ := ac7_fam_k9_t2_m5_c3) (P := ac7_fam_k9_t2_m5_i1) (R := ac7_fam_k9_t2_m5_i2) (S := ac7_fam_k9_t2_m5_i3) ac7_fam_k9_t2_m5_b2 ac7_fam_k9_t2_m5_b3
theorem ac7_fam_k9_t2_m5_k0_3 : replay (ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ac7_fam_k9_t2_m5_s = some ac7_fam_k9_t2_m5_i3 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c1) (ms₂ := (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) (P := ac7_fam_k9_t2_m5_s) (R := ac7_fam_k9_t2_m5_i1) (S := ac7_fam_k9_t2_m5_i3) ac7_fam_k9_t2_m5_b1 ac7_fam_k9_t2_m5_k1_3
theorem ac7_fam_k9_t2_m5_k4_6 : replay (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6) ac7_fam_k9_t2_m5_i4 = some ac7_fam_k9_t2_m5_i6 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c5) (ms₂ := ac7_fam_k9_t2_m5_c6) (P := ac7_fam_k9_t2_m5_i4) (R := ac7_fam_k9_t2_m5_i5) (S := ac7_fam_k9_t2_m5_i6) ac7_fam_k9_t2_m5_b5 ac7_fam_k9_t2_m5_b6
theorem ac7_fam_k9_t2_m5_k3_6 : replay (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6)) ac7_fam_k9_t2_m5_i3 = some ac7_fam_k9_t2_m5_i6 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c4) (ms₂ := (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6)) (P := ac7_fam_k9_t2_m5_i3) (R := ac7_fam_k9_t2_m5_i4) (S := ac7_fam_k9_t2_m5_i6) ac7_fam_k9_t2_m5_b4 ac7_fam_k9_t2_m5_k4_6
theorem ac7_fam_k9_t2_m5_k0_6 : replay ((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) ac7_fam_k9_t2_m5_s = some ac7_fam_k9_t2_m5_i6 :=
  replay_concat (ms₁ := (ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3))) (ms₂ := (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) (P := ac7_fam_k9_t2_m5_s) (R := ac7_fam_k9_t2_m5_i3) (S := ac7_fam_k9_t2_m5_i6) ac7_fam_k9_t2_m5_k0_3 ac7_fam_k9_t2_m5_k3_6
theorem ac7_fam_k9_t2_m5_k7_9 : replay (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9) ac7_fam_k9_t2_m5_i7 = some ac7_fam_k9_t2_m5_i9 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c8) (ms₂ := ac7_fam_k9_t2_m5_c9) (P := ac7_fam_k9_t2_m5_i7) (R := ac7_fam_k9_t2_m5_i8) (S := ac7_fam_k9_t2_m5_i9) ac7_fam_k9_t2_m5_b8 ac7_fam_k9_t2_m5_b9
theorem ac7_fam_k9_t2_m5_k6_9 : replay (ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ac7_fam_k9_t2_m5_i6 = some ac7_fam_k9_t2_m5_i9 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c7) (ms₂ := (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) (P := ac7_fam_k9_t2_m5_i6) (R := ac7_fam_k9_t2_m5_i7) (S := ac7_fam_k9_t2_m5_i9) ac7_fam_k9_t2_m5_b7 ac7_fam_k9_t2_m5_k7_9
theorem ac7_fam_k9_t2_m5_k9_11 : replay (ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ac7_fam_k9_t2_m5_i9 = some ac7_fam_k9_t2_m5_i11 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c10) (ms₂ := ac7_fam_k9_t2_m5_c11) (P := ac7_fam_k9_t2_m5_i9) (R := ac7_fam_k9_t2_m5_i10) (S := ac7_fam_k9_t2_m5_i11) ac7_fam_k9_t2_m5_b10 ac7_fam_k9_t2_m5_b11
theorem ac7_fam_k9_t2_m5_k11_13 : replay (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13) ac7_fam_k9_t2_m5_i11 = some ac7_fam_k9_t2_m5_i13 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c12) (ms₂ := ac7_fam_k9_t2_m5_c13) (P := ac7_fam_k9_t2_m5_i11) (R := ac7_fam_k9_t2_m5_i12) (S := ac7_fam_k9_t2_m5_i13) ac7_fam_k9_t2_m5_b12 ac7_fam_k9_t2_m5_b13
theorem ac7_fam_k9_t2_m5_k9_13 : replay ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)) ac7_fam_k9_t2_m5_i9 = some ac7_fam_k9_t2_m5_i13 :=
  replay_concat (ms₁ := (ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11)) (ms₂ := (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)) (P := ac7_fam_k9_t2_m5_i9) (R := ac7_fam_k9_t2_m5_i11) (S := ac7_fam_k9_t2_m5_i13) ac7_fam_k9_t2_m5_k9_11 ac7_fam_k9_t2_m5_k11_13
theorem ac7_fam_k9_t2_m5_k6_13 : replay ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13))) ac7_fam_k9_t2_m5_i6 = some ac7_fam_k9_t2_m5_i13 :=
  replay_concat (ms₁ := (ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9))) (ms₂ := ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13))) (P := ac7_fam_k9_t2_m5_i6) (R := ac7_fam_k9_t2_m5_i9) (S := ac7_fam_k9_t2_m5_i13) ac7_fam_k9_t2_m5_k6_9 ac7_fam_k9_t2_m5_k9_13
theorem ac7_fam_k9_t2_m5_k0_13 : replay (((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) ++ ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)))) ac7_fam_k9_t2_m5_s = some ac7_fam_k9_t2_m5_i13 :=
  replay_concat (ms₁ := ((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6)))) (ms₂ := ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)))) (P := ac7_fam_k9_t2_m5_s) (R := ac7_fam_k9_t2_m5_i6) (S := ac7_fam_k9_t2_m5_i13) ac7_fam_k9_t2_m5_k0_6 ac7_fam_k9_t2_m5_k6_13
theorem ac7_fam_k9_t2_m5_k14_16 : replay (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16) ac7_fam_k9_t2_m5_i14 = some ac7_fam_k9_t2_m5_i16 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c15) (ms₂ := ac7_fam_k9_t2_m5_c16) (P := ac7_fam_k9_t2_m5_i14) (R := ac7_fam_k9_t2_m5_i15) (S := ac7_fam_k9_t2_m5_i16) ac7_fam_k9_t2_m5_b15 ac7_fam_k9_t2_m5_b16
theorem ac7_fam_k9_t2_m5_k13_16 : replay (ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ac7_fam_k9_t2_m5_i13 = some ac7_fam_k9_t2_m5_i16 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c14) (ms₂ := (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) (P := ac7_fam_k9_t2_m5_i13) (R := ac7_fam_k9_t2_m5_i14) (S := ac7_fam_k9_t2_m5_i16) ac7_fam_k9_t2_m5_b14 ac7_fam_k9_t2_m5_k14_16
theorem ac7_fam_k9_t2_m5_k17_19 : replay (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19) ac7_fam_k9_t2_m5_i17 = some ac7_fam_k9_t2_m5_i19 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c18) (ms₂ := ac7_fam_k9_t2_m5_c19) (P := ac7_fam_k9_t2_m5_i17) (R := ac7_fam_k9_t2_m5_i18) (S := ac7_fam_k9_t2_m5_i19) ac7_fam_k9_t2_m5_b18 ac7_fam_k9_t2_m5_b19
theorem ac7_fam_k9_t2_m5_k16_19 : replay (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19)) ac7_fam_k9_t2_m5_i16 = some ac7_fam_k9_t2_m5_i19 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c17) (ms₂ := (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19)) (P := ac7_fam_k9_t2_m5_i16) (R := ac7_fam_k9_t2_m5_i17) (S := ac7_fam_k9_t2_m5_i19) ac7_fam_k9_t2_m5_b17 ac7_fam_k9_t2_m5_k17_19
theorem ac7_fam_k9_t2_m5_k13_19 : replay ((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) ac7_fam_k9_t2_m5_i13 = some ac7_fam_k9_t2_m5_i19 :=
  replay_concat (ms₁ := (ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16))) (ms₂ := (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) (P := ac7_fam_k9_t2_m5_i13) (R := ac7_fam_k9_t2_m5_i16) (S := ac7_fam_k9_t2_m5_i19) ac7_fam_k9_t2_m5_k13_16 ac7_fam_k9_t2_m5_k16_19
theorem ac7_fam_k9_t2_m5_k20_22 : replay (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22) ac7_fam_k9_t2_m5_i20 = some ac7_fam_k9_t2_m5_i22 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c21) (ms₂ := ac7_fam_k9_t2_m5_c22) (P := ac7_fam_k9_t2_m5_i20) (R := ac7_fam_k9_t2_m5_i21) (S := ac7_fam_k9_t2_m5_i22) ac7_fam_k9_t2_m5_b21 ac7_fam_k9_t2_m5_b22
theorem ac7_fam_k9_t2_m5_k19_22 : replay (ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ac7_fam_k9_t2_m5_i19 = some ac7_fam_k9_t2_m5_i22 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c20) (ms₂ := (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) (P := ac7_fam_k9_t2_m5_i19) (R := ac7_fam_k9_t2_m5_i20) (S := ac7_fam_k9_t2_m5_i22) ac7_fam_k9_t2_m5_b20 ac7_fam_k9_t2_m5_k20_22
theorem ac7_fam_k9_t2_m5_k22_24 : replay (ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ac7_fam_k9_t2_m5_i22 = some ac7_fam_k9_t2_m5_i24 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c23) (ms₂ := ac7_fam_k9_t2_m5_c24) (P := ac7_fam_k9_t2_m5_i22) (R := ac7_fam_k9_t2_m5_i23) (S := ac7_fam_k9_t2_m5_i24) ac7_fam_k9_t2_m5_b23 ac7_fam_k9_t2_m5_b24
theorem ac7_fam_k9_t2_m5_k24_26 : replay (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26) ac7_fam_k9_t2_m5_i24 = some ac7_fam_k9_t2_m5_i26 :=
  replay_concat (ms₁ := ac7_fam_k9_t2_m5_c25) (ms₂ := ac7_fam_k9_t2_m5_c26) (P := ac7_fam_k9_t2_m5_i24) (R := ac7_fam_k9_t2_m5_i25) (S := ac7_fam_k9_t2_m5_i26) ac7_fam_k9_t2_m5_b25 ac7_fam_k9_t2_m5_b26
theorem ac7_fam_k9_t2_m5_k22_26 : replay ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26)) ac7_fam_k9_t2_m5_i22 = some ac7_fam_k9_t2_m5_i26 :=
  replay_concat (ms₁ := (ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24)) (ms₂ := (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26)) (P := ac7_fam_k9_t2_m5_i22) (R := ac7_fam_k9_t2_m5_i24) (S := ac7_fam_k9_t2_m5_i26) ac7_fam_k9_t2_m5_k22_24 ac7_fam_k9_t2_m5_k24_26
theorem ac7_fam_k9_t2_m5_k19_26 : replay ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26))) ac7_fam_k9_t2_m5_i19 = some ac7_fam_k9_t2_m5_i26 :=
  replay_concat (ms₁ := (ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22))) (ms₂ := ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26))) (P := ac7_fam_k9_t2_m5_i19) (R := ac7_fam_k9_t2_m5_i22) (S := ac7_fam_k9_t2_m5_i26) ac7_fam_k9_t2_m5_k19_22 ac7_fam_k9_t2_m5_k22_26
theorem ac7_fam_k9_t2_m5_k13_26 : replay (((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) ++ ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26)))) ac7_fam_k9_t2_m5_i13 = some ac7_fam_k9_t2_m5_i26 :=
  replay_concat (ms₁ := ((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19)))) (ms₂ := ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26)))) (P := ac7_fam_k9_t2_m5_i13) (R := ac7_fam_k9_t2_m5_i19) (S := ac7_fam_k9_t2_m5_i26) ac7_fam_k9_t2_m5_k13_19 ac7_fam_k9_t2_m5_k19_26
theorem ac7_fam_k9_t2_m5_k0_26 : replay ((((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) ++ ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)))) ++ (((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) ++ ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26))))) ac7_fam_k9_t2_m5_s = some ac7_fam_k9_t2_m5_i26 :=
  replay_concat (ms₁ := (((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) ++ ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13))))) (ms₂ := (((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) ++ ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26))))) (P := ac7_fam_k9_t2_m5_s) (R := ac7_fam_k9_t2_m5_i13) (S := ac7_fam_k9_t2_m5_i26) ac7_fam_k9_t2_m5_k0_13 ac7_fam_k9_t2_m5_k13_26

/-- `fam_k9_t2_m5.cert` checked: replaying its 52 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k9_t2_m5_replay : replay ((((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) ++ ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)))) ++ (((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) ++ ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26))))) ac7_fam_k9_t2_m5_s = some ac7_fam_k9_t2_m5_i26 := ac7_fam_k9_t2_m5_k0_26

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k9_t2_m5_checked : checkCert ((((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) ++ ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)))) ++ (((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) ++ ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26))))) ac7_fam_k9_t2_m5_s ac7_fam_k9_t2_m5_i26 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k9_t2_m5_replay

/-- The endpoints of `fam_k9_t2_m5.cert` are the presentations `<x,y | x^9, y^5, [x^1,y]>`
    and `<x,y | x^9, y^5, [x^4,y]>` of the statement. -/
theorem ac7_fam_k9_t2_m5_endpoints :
    metz 9 5 1 = ac7_fam_k9_t2_m5_s ∧ metz 9 5 4 = ac7_fam_k9_t2_m5_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 52-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k9_t2_m5_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 9 5 1) = some (metz 9 5 4) := by
  refine ⟨((((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) ++ ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)))) ++ (((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) ++ ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26))))), ?_⟩
  calc replay ((((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) ++ ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)))) ++ (((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) ++ ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26))))) (metz 9 5 1) = replay ((((ac7_fam_k9_t2_m5_c1 ++ (ac7_fam_k9_t2_m5_c2 ++ ac7_fam_k9_t2_m5_c3)) ++ (ac7_fam_k9_t2_m5_c4 ++ (ac7_fam_k9_t2_m5_c5 ++ ac7_fam_k9_t2_m5_c6))) ++ ((ac7_fam_k9_t2_m5_c7 ++ (ac7_fam_k9_t2_m5_c8 ++ ac7_fam_k9_t2_m5_c9)) ++ ((ac7_fam_k9_t2_m5_c10 ++ ac7_fam_k9_t2_m5_c11) ++ (ac7_fam_k9_t2_m5_c12 ++ ac7_fam_k9_t2_m5_c13)))) ++ (((ac7_fam_k9_t2_m5_c14 ++ (ac7_fam_k9_t2_m5_c15 ++ ac7_fam_k9_t2_m5_c16)) ++ (ac7_fam_k9_t2_m5_c17 ++ (ac7_fam_k9_t2_m5_c18 ++ ac7_fam_k9_t2_m5_c19))) ++ ((ac7_fam_k9_t2_m5_c20 ++ (ac7_fam_k9_t2_m5_c21 ++ ac7_fam_k9_t2_m5_c22)) ++ ((ac7_fam_k9_t2_m5_c23 ++ ac7_fam_k9_t2_m5_c24) ++ (ac7_fam_k9_t2_m5_c25 ++ ac7_fam_k9_t2_m5_c26))))) ac7_fam_k9_t2_m5_s := by rw [ac7_fam_k9_t2_m5_endpoints.1]
    _ = some ac7_fam_k9_t2_m5_e := ac7_fam_k9_t2_m5_replay
    _ = some (metz 9 5 4) := by rw [ac7_fam_k9_t2_m5_endpoints.2]

/-! ### `fam_k9_t4_m3.cert`: Metzler family, k=9 t=4 m=3  <x,y | x^9, y^3, [x,y]>  ->  <x,y | x^9, y^3, [x^2,y]>. -/

/-- The start tuple of `fam_k9_t4_m3.cert` (52 Q**-moves to the end tuple). -/
def ac7_fam_k9_t4_m3_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k9_t4_m3_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k9_t4_m3_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false)]]
def ac7_fam_k9_t4_m3_i3 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k9_t4_m3_i4 : QPres := mkQPres 3 4 [[(0, true), (2, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k9_t4_m3_i5 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k9_t4_m3_i6 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k9_t4_m3_i7 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true)]]
def ac7_fam_k9_t4_m3_i8 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (2, true), (2, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t4_m3_i9 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t4_m3_i10 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t4_m3_i11 : QPres := mkQPres 3 4 [[(2, true), (2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t4_m3_i12 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t4_m3_i13 : QPres := mkQPres 3 4 [[(0, true), (2, true), (2, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t4_m3_i14 : QPres := mkQPres 3 4 [[(2, false), (2, false), (0, false)], [(1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t4_m3_i15 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true), (1, true)], [(2, false), (2, false), (1, true), (2, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t4_m3_i16 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true)], [(1, false), (1, false), (0, true), (1, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k9_t4_m3_i17 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true)], [(1, true), (1, true), (0, true), (1, false), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k9_t4_m3_i18 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k9_t4_m3_i19 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k9_t4_m3_i20 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false), (1, false)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k9_t4_m3_i21 : QPres := mkQPres 2 3 [[(1, true), (1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false)]]
def ac7_fam_k9_t4_m3_i22 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], [(1, false), (1, false), (1, false)]]
def ac7_fam_k9_t4_m3_i23 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (0, true), (0, true), (1, false), (0, false), (0, false)], [(1, false), (1, false), (1, false)]]
def ac7_fam_k9_t4_m3_i24 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_fam_k9_t4_m3_i25 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false), (1, false)], [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)]]
def ac7_fam_k9_t4_m3_i26 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]
def ac7_fam_k9_t4_m3_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]]

def ac7_fam_k9_t4_m3_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k9_t4_m3_c2 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k9_t4_m3_c3 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k9_t4_m3_c4 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k9_t4_m3_c5 : List QMove :=
  [ .conj 3 [(0, false), (0, false), (0, false), (0, false)],
    .mul 0 3 ]
def ac7_fam_k9_t4_m3_c6 : List QMove :=
  [ .conj 3 [(0, true), (0, true), (0, true), (0, true)],
    .conj 0 [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true)] ]
def ac7_fam_k9_t4_m3_c7 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (0, true), (0, true), (0, true), (2, false)] ]
def ac7_fam_k9_t4_m3_c8 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k9_t4_m3_c9 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (2, true), (2, true)] ]
def ac7_fam_k9_t4_m3_c10 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false), (0, true), (2, false)] ]
def ac7_fam_k9_t4_m3_c11 : List QMove :=
  [ .conj 0 [(2, true), (2, true), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k9_t4_m3_c12 : List QMove :=
  [ .conj 0 [(2, false), (2, false), (2, false)],
    .conj 0 [(0, true), (1, true), (2, true), (2, true)] ]
def ac7_fam_k9_t4_m3_c13 : List QMove :=
  [ .lmul 2 0,
    .conj 0 [(2, false), (2, false), (1, false), (0, false)] ]
def ac7_fam_k9_t4_m3_c14 : List QMove :=
  [ .inv 0,
    .lmul 2 0 ]
def ac7_fam_k9_t4_m3_c15 : List QMove :=
  [ .inv 0,
    .nijinv 0 2 ]
def ac7_fam_k9_t4_m3_c16 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k9_t4_m3_c17 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true), (1, true)] ]
def ac7_fam_k9_t4_m3_c18 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k9_t4_m3_c19 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k9_t4_m3_c20 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k9_t4_m3_c21 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k9_t4_m3_c22 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false), (1, false)] ]
def ac7_fam_k9_t4_m3_c23 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k9_t4_m3_c24 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k9_t4_m3_c25 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false)] ]
def ac7_fam_k9_t4_m3_c26 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b1 :
    replay ac7_fam_k9_t4_m3_c1 ac7_fam_k9_t4_m3_s = some ac7_fam_k9_t4_m3_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b2 :
    replay ac7_fam_k9_t4_m3_c2 ac7_fam_k9_t4_m3_i1 = some ac7_fam_k9_t4_m3_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b3 :
    replay ac7_fam_k9_t4_m3_c3 ac7_fam_k9_t4_m3_i2 = some ac7_fam_k9_t4_m3_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b4 :
    replay ac7_fam_k9_t4_m3_c4 ac7_fam_k9_t4_m3_i3 = some ac7_fam_k9_t4_m3_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b5 :
    replay ac7_fam_k9_t4_m3_c5 ac7_fam_k9_t4_m3_i4 = some ac7_fam_k9_t4_m3_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b6 :
    replay ac7_fam_k9_t4_m3_c6 ac7_fam_k9_t4_m3_i5 = some ac7_fam_k9_t4_m3_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b7 :
    replay ac7_fam_k9_t4_m3_c7 ac7_fam_k9_t4_m3_i6 = some ac7_fam_k9_t4_m3_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b8 :
    replay ac7_fam_k9_t4_m3_c8 ac7_fam_k9_t4_m3_i7 = some ac7_fam_k9_t4_m3_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b9 :
    replay ac7_fam_k9_t4_m3_c9 ac7_fam_k9_t4_m3_i8 = some ac7_fam_k9_t4_m3_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b10 :
    replay ac7_fam_k9_t4_m3_c10 ac7_fam_k9_t4_m3_i9 = some ac7_fam_k9_t4_m3_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b11 :
    replay ac7_fam_k9_t4_m3_c11 ac7_fam_k9_t4_m3_i10 = some ac7_fam_k9_t4_m3_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b12 :
    replay ac7_fam_k9_t4_m3_c12 ac7_fam_k9_t4_m3_i11 = some ac7_fam_k9_t4_m3_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b13 :
    replay ac7_fam_k9_t4_m3_c13 ac7_fam_k9_t4_m3_i12 = some ac7_fam_k9_t4_m3_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b14 :
    replay ac7_fam_k9_t4_m3_c14 ac7_fam_k9_t4_m3_i13 = some ac7_fam_k9_t4_m3_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b15 :
    replay ac7_fam_k9_t4_m3_c15 ac7_fam_k9_t4_m3_i14 = some ac7_fam_k9_t4_m3_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b16 :
    replay ac7_fam_k9_t4_m3_c16 ac7_fam_k9_t4_m3_i15 = some ac7_fam_k9_t4_m3_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b17 :
    replay ac7_fam_k9_t4_m3_c17 ac7_fam_k9_t4_m3_i16 = some ac7_fam_k9_t4_m3_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b18 :
    replay ac7_fam_k9_t4_m3_c18 ac7_fam_k9_t4_m3_i17 = some ac7_fam_k9_t4_m3_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b19 :
    replay ac7_fam_k9_t4_m3_c19 ac7_fam_k9_t4_m3_i18 = some ac7_fam_k9_t4_m3_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b20 :
    replay ac7_fam_k9_t4_m3_c20 ac7_fam_k9_t4_m3_i19 = some ac7_fam_k9_t4_m3_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b21 :
    replay ac7_fam_k9_t4_m3_c21 ac7_fam_k9_t4_m3_i20 = some ac7_fam_k9_t4_m3_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b22 :
    replay ac7_fam_k9_t4_m3_c22 ac7_fam_k9_t4_m3_i21 = some ac7_fam_k9_t4_m3_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b23 :
    replay ac7_fam_k9_t4_m3_c23 ac7_fam_k9_t4_m3_i22 = some ac7_fam_k9_t4_m3_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b24 :
    replay ac7_fam_k9_t4_m3_c24 ac7_fam_k9_t4_m3_i23 = some ac7_fam_k9_t4_m3_i24 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b25 :
    replay ac7_fam_k9_t4_m3_c25 ac7_fam_k9_t4_m3_i24 = some ac7_fam_k9_t4_m3_i25 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t4_m3_b26 :
    replay ac7_fam_k9_t4_m3_c26 ac7_fam_k9_t4_m3_i25 = some ac7_fam_k9_t4_m3_i26 := by decide

theorem ac7_fam_k9_t4_m3_k1_3 : replay (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3) ac7_fam_k9_t4_m3_i1 = some ac7_fam_k9_t4_m3_i3 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c2) (ms₂ := ac7_fam_k9_t4_m3_c3) (P := ac7_fam_k9_t4_m3_i1) (R := ac7_fam_k9_t4_m3_i2) (S := ac7_fam_k9_t4_m3_i3) ac7_fam_k9_t4_m3_b2 ac7_fam_k9_t4_m3_b3
theorem ac7_fam_k9_t4_m3_k0_3 : replay (ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ac7_fam_k9_t4_m3_s = some ac7_fam_k9_t4_m3_i3 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c1) (ms₂ := (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) (P := ac7_fam_k9_t4_m3_s) (R := ac7_fam_k9_t4_m3_i1) (S := ac7_fam_k9_t4_m3_i3) ac7_fam_k9_t4_m3_b1 ac7_fam_k9_t4_m3_k1_3
theorem ac7_fam_k9_t4_m3_k4_6 : replay (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6) ac7_fam_k9_t4_m3_i4 = some ac7_fam_k9_t4_m3_i6 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c5) (ms₂ := ac7_fam_k9_t4_m3_c6) (P := ac7_fam_k9_t4_m3_i4) (R := ac7_fam_k9_t4_m3_i5) (S := ac7_fam_k9_t4_m3_i6) ac7_fam_k9_t4_m3_b5 ac7_fam_k9_t4_m3_b6
theorem ac7_fam_k9_t4_m3_k3_6 : replay (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6)) ac7_fam_k9_t4_m3_i3 = some ac7_fam_k9_t4_m3_i6 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c4) (ms₂ := (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6)) (P := ac7_fam_k9_t4_m3_i3) (R := ac7_fam_k9_t4_m3_i4) (S := ac7_fam_k9_t4_m3_i6) ac7_fam_k9_t4_m3_b4 ac7_fam_k9_t4_m3_k4_6
theorem ac7_fam_k9_t4_m3_k0_6 : replay ((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) ac7_fam_k9_t4_m3_s = some ac7_fam_k9_t4_m3_i6 :=
  replay_concat (ms₁ := (ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3))) (ms₂ := (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) (P := ac7_fam_k9_t4_m3_s) (R := ac7_fam_k9_t4_m3_i3) (S := ac7_fam_k9_t4_m3_i6) ac7_fam_k9_t4_m3_k0_3 ac7_fam_k9_t4_m3_k3_6
theorem ac7_fam_k9_t4_m3_k7_9 : replay (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9) ac7_fam_k9_t4_m3_i7 = some ac7_fam_k9_t4_m3_i9 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c8) (ms₂ := ac7_fam_k9_t4_m3_c9) (P := ac7_fam_k9_t4_m3_i7) (R := ac7_fam_k9_t4_m3_i8) (S := ac7_fam_k9_t4_m3_i9) ac7_fam_k9_t4_m3_b8 ac7_fam_k9_t4_m3_b9
theorem ac7_fam_k9_t4_m3_k6_9 : replay (ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ac7_fam_k9_t4_m3_i6 = some ac7_fam_k9_t4_m3_i9 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c7) (ms₂ := (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) (P := ac7_fam_k9_t4_m3_i6) (R := ac7_fam_k9_t4_m3_i7) (S := ac7_fam_k9_t4_m3_i9) ac7_fam_k9_t4_m3_b7 ac7_fam_k9_t4_m3_k7_9
theorem ac7_fam_k9_t4_m3_k9_11 : replay (ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ac7_fam_k9_t4_m3_i9 = some ac7_fam_k9_t4_m3_i11 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c10) (ms₂ := ac7_fam_k9_t4_m3_c11) (P := ac7_fam_k9_t4_m3_i9) (R := ac7_fam_k9_t4_m3_i10) (S := ac7_fam_k9_t4_m3_i11) ac7_fam_k9_t4_m3_b10 ac7_fam_k9_t4_m3_b11
theorem ac7_fam_k9_t4_m3_k11_13 : replay (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13) ac7_fam_k9_t4_m3_i11 = some ac7_fam_k9_t4_m3_i13 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c12) (ms₂ := ac7_fam_k9_t4_m3_c13) (P := ac7_fam_k9_t4_m3_i11) (R := ac7_fam_k9_t4_m3_i12) (S := ac7_fam_k9_t4_m3_i13) ac7_fam_k9_t4_m3_b12 ac7_fam_k9_t4_m3_b13
theorem ac7_fam_k9_t4_m3_k9_13 : replay ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)) ac7_fam_k9_t4_m3_i9 = some ac7_fam_k9_t4_m3_i13 :=
  replay_concat (ms₁ := (ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11)) (ms₂ := (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)) (P := ac7_fam_k9_t4_m3_i9) (R := ac7_fam_k9_t4_m3_i11) (S := ac7_fam_k9_t4_m3_i13) ac7_fam_k9_t4_m3_k9_11 ac7_fam_k9_t4_m3_k11_13
theorem ac7_fam_k9_t4_m3_k6_13 : replay ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13))) ac7_fam_k9_t4_m3_i6 = some ac7_fam_k9_t4_m3_i13 :=
  replay_concat (ms₁ := (ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9))) (ms₂ := ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13))) (P := ac7_fam_k9_t4_m3_i6) (R := ac7_fam_k9_t4_m3_i9) (S := ac7_fam_k9_t4_m3_i13) ac7_fam_k9_t4_m3_k6_9 ac7_fam_k9_t4_m3_k9_13
theorem ac7_fam_k9_t4_m3_k0_13 : replay (((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) ++ ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)))) ac7_fam_k9_t4_m3_s = some ac7_fam_k9_t4_m3_i13 :=
  replay_concat (ms₁ := ((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6)))) (ms₂ := ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)))) (P := ac7_fam_k9_t4_m3_s) (R := ac7_fam_k9_t4_m3_i6) (S := ac7_fam_k9_t4_m3_i13) ac7_fam_k9_t4_m3_k0_6 ac7_fam_k9_t4_m3_k6_13
theorem ac7_fam_k9_t4_m3_k14_16 : replay (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16) ac7_fam_k9_t4_m3_i14 = some ac7_fam_k9_t4_m3_i16 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c15) (ms₂ := ac7_fam_k9_t4_m3_c16) (P := ac7_fam_k9_t4_m3_i14) (R := ac7_fam_k9_t4_m3_i15) (S := ac7_fam_k9_t4_m3_i16) ac7_fam_k9_t4_m3_b15 ac7_fam_k9_t4_m3_b16
theorem ac7_fam_k9_t4_m3_k13_16 : replay (ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ac7_fam_k9_t4_m3_i13 = some ac7_fam_k9_t4_m3_i16 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c14) (ms₂ := (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) (P := ac7_fam_k9_t4_m3_i13) (R := ac7_fam_k9_t4_m3_i14) (S := ac7_fam_k9_t4_m3_i16) ac7_fam_k9_t4_m3_b14 ac7_fam_k9_t4_m3_k14_16
theorem ac7_fam_k9_t4_m3_k17_19 : replay (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19) ac7_fam_k9_t4_m3_i17 = some ac7_fam_k9_t4_m3_i19 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c18) (ms₂ := ac7_fam_k9_t4_m3_c19) (P := ac7_fam_k9_t4_m3_i17) (R := ac7_fam_k9_t4_m3_i18) (S := ac7_fam_k9_t4_m3_i19) ac7_fam_k9_t4_m3_b18 ac7_fam_k9_t4_m3_b19
theorem ac7_fam_k9_t4_m3_k16_19 : replay (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19)) ac7_fam_k9_t4_m3_i16 = some ac7_fam_k9_t4_m3_i19 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c17) (ms₂ := (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19)) (P := ac7_fam_k9_t4_m3_i16) (R := ac7_fam_k9_t4_m3_i17) (S := ac7_fam_k9_t4_m3_i19) ac7_fam_k9_t4_m3_b17 ac7_fam_k9_t4_m3_k17_19
theorem ac7_fam_k9_t4_m3_k13_19 : replay ((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) ac7_fam_k9_t4_m3_i13 = some ac7_fam_k9_t4_m3_i19 :=
  replay_concat (ms₁ := (ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16))) (ms₂ := (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) (P := ac7_fam_k9_t4_m3_i13) (R := ac7_fam_k9_t4_m3_i16) (S := ac7_fam_k9_t4_m3_i19) ac7_fam_k9_t4_m3_k13_16 ac7_fam_k9_t4_m3_k16_19
theorem ac7_fam_k9_t4_m3_k20_22 : replay (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22) ac7_fam_k9_t4_m3_i20 = some ac7_fam_k9_t4_m3_i22 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c21) (ms₂ := ac7_fam_k9_t4_m3_c22) (P := ac7_fam_k9_t4_m3_i20) (R := ac7_fam_k9_t4_m3_i21) (S := ac7_fam_k9_t4_m3_i22) ac7_fam_k9_t4_m3_b21 ac7_fam_k9_t4_m3_b22
theorem ac7_fam_k9_t4_m3_k19_22 : replay (ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ac7_fam_k9_t4_m3_i19 = some ac7_fam_k9_t4_m3_i22 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c20) (ms₂ := (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) (P := ac7_fam_k9_t4_m3_i19) (R := ac7_fam_k9_t4_m3_i20) (S := ac7_fam_k9_t4_m3_i22) ac7_fam_k9_t4_m3_b20 ac7_fam_k9_t4_m3_k20_22
theorem ac7_fam_k9_t4_m3_k22_24 : replay (ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ac7_fam_k9_t4_m3_i22 = some ac7_fam_k9_t4_m3_i24 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c23) (ms₂ := ac7_fam_k9_t4_m3_c24) (P := ac7_fam_k9_t4_m3_i22) (R := ac7_fam_k9_t4_m3_i23) (S := ac7_fam_k9_t4_m3_i24) ac7_fam_k9_t4_m3_b23 ac7_fam_k9_t4_m3_b24
theorem ac7_fam_k9_t4_m3_k24_26 : replay (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26) ac7_fam_k9_t4_m3_i24 = some ac7_fam_k9_t4_m3_i26 :=
  replay_concat (ms₁ := ac7_fam_k9_t4_m3_c25) (ms₂ := ac7_fam_k9_t4_m3_c26) (P := ac7_fam_k9_t4_m3_i24) (R := ac7_fam_k9_t4_m3_i25) (S := ac7_fam_k9_t4_m3_i26) ac7_fam_k9_t4_m3_b25 ac7_fam_k9_t4_m3_b26
theorem ac7_fam_k9_t4_m3_k22_26 : replay ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26)) ac7_fam_k9_t4_m3_i22 = some ac7_fam_k9_t4_m3_i26 :=
  replay_concat (ms₁ := (ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24)) (ms₂ := (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26)) (P := ac7_fam_k9_t4_m3_i22) (R := ac7_fam_k9_t4_m3_i24) (S := ac7_fam_k9_t4_m3_i26) ac7_fam_k9_t4_m3_k22_24 ac7_fam_k9_t4_m3_k24_26
theorem ac7_fam_k9_t4_m3_k19_26 : replay ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26))) ac7_fam_k9_t4_m3_i19 = some ac7_fam_k9_t4_m3_i26 :=
  replay_concat (ms₁ := (ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22))) (ms₂ := ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26))) (P := ac7_fam_k9_t4_m3_i19) (R := ac7_fam_k9_t4_m3_i22) (S := ac7_fam_k9_t4_m3_i26) ac7_fam_k9_t4_m3_k19_22 ac7_fam_k9_t4_m3_k22_26
theorem ac7_fam_k9_t4_m3_k13_26 : replay (((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) ++ ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26)))) ac7_fam_k9_t4_m3_i13 = some ac7_fam_k9_t4_m3_i26 :=
  replay_concat (ms₁ := ((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19)))) (ms₂ := ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26)))) (P := ac7_fam_k9_t4_m3_i13) (R := ac7_fam_k9_t4_m3_i19) (S := ac7_fam_k9_t4_m3_i26) ac7_fam_k9_t4_m3_k13_19 ac7_fam_k9_t4_m3_k19_26
theorem ac7_fam_k9_t4_m3_k0_26 : replay ((((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) ++ ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)))) ++ (((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) ++ ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26))))) ac7_fam_k9_t4_m3_s = some ac7_fam_k9_t4_m3_i26 :=
  replay_concat (ms₁ := (((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) ++ ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13))))) (ms₂ := (((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) ++ ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26))))) (P := ac7_fam_k9_t4_m3_s) (R := ac7_fam_k9_t4_m3_i13) (S := ac7_fam_k9_t4_m3_i26) ac7_fam_k9_t4_m3_k0_13 ac7_fam_k9_t4_m3_k13_26

/-- `fam_k9_t4_m3.cert` checked: replaying its 52 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k9_t4_m3_replay : replay ((((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) ++ ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)))) ++ (((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) ++ ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26))))) ac7_fam_k9_t4_m3_s = some ac7_fam_k9_t4_m3_i26 := ac7_fam_k9_t4_m3_k0_26

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k9_t4_m3_checked : checkCert ((((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) ++ ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)))) ++ (((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) ++ ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26))))) ac7_fam_k9_t4_m3_s ac7_fam_k9_t4_m3_i26 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k9_t4_m3_replay

/-- The endpoints of `fam_k9_t4_m3.cert` are the presentations `<x,y | x^9, y^3, [x^1,y]>`
    and `<x,y | x^9, y^3, [x^2,y]>` of the statement. -/
theorem ac7_fam_k9_t4_m3_endpoints :
    metz 9 3 1 = ac7_fam_k9_t4_m3_s ∧ metz 9 3 2 = ac7_fam_k9_t4_m3_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 52-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k9_t4_m3_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 9 3 1) = some (metz 9 3 2) := by
  refine ⟨((((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) ++ ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)))) ++ (((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) ++ ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26))))), ?_⟩
  calc replay ((((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) ++ ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)))) ++ (((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) ++ ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26))))) (metz 9 3 1) = replay ((((ac7_fam_k9_t4_m3_c1 ++ (ac7_fam_k9_t4_m3_c2 ++ ac7_fam_k9_t4_m3_c3)) ++ (ac7_fam_k9_t4_m3_c4 ++ (ac7_fam_k9_t4_m3_c5 ++ ac7_fam_k9_t4_m3_c6))) ++ ((ac7_fam_k9_t4_m3_c7 ++ (ac7_fam_k9_t4_m3_c8 ++ ac7_fam_k9_t4_m3_c9)) ++ ((ac7_fam_k9_t4_m3_c10 ++ ac7_fam_k9_t4_m3_c11) ++ (ac7_fam_k9_t4_m3_c12 ++ ac7_fam_k9_t4_m3_c13)))) ++ (((ac7_fam_k9_t4_m3_c14 ++ (ac7_fam_k9_t4_m3_c15 ++ ac7_fam_k9_t4_m3_c16)) ++ (ac7_fam_k9_t4_m3_c17 ++ (ac7_fam_k9_t4_m3_c18 ++ ac7_fam_k9_t4_m3_c19))) ++ ((ac7_fam_k9_t4_m3_c20 ++ (ac7_fam_k9_t4_m3_c21 ++ ac7_fam_k9_t4_m3_c22)) ++ ((ac7_fam_k9_t4_m3_c23 ++ ac7_fam_k9_t4_m3_c24) ++ (ac7_fam_k9_t4_m3_c25 ++ ac7_fam_k9_t4_m3_c26))))) ac7_fam_k9_t4_m3_s := by rw [ac7_fam_k9_t4_m3_endpoints.1]
    _ = some ac7_fam_k9_t4_m3_e := ac7_fam_k9_t4_m3_replay
    _ = some (metz 9 3 2) := by rw [ac7_fam_k9_t4_m3_endpoints.2]

/-! ### `fam_k9_t8_m2.cert`: Metzler family, k=9 t=8 m=2  <x,y | x^9, y^2, [x,y]>  ->  <x,y | x^9, y^2, [x^1,y]>. -/

/-- The start tuple of `fam_k9_t8_m2.cert` (64 Q**-moves to the end tuple). -/
def ac7_fam_k9_t8_m2_s : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k9_t8_m2_i1 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false)]]
def ac7_fam_k9_t8_m2_i2 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false)]]
def ac7_fam_k9_t8_m2_i3 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k9_t8_m2_i4 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k9_t8_m2_i5 : QPres := mkQPres 3 4 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k9_t8_m2_i6 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)]]
def ac7_fam_k9_t8_m2_i7 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k9_t8_m2_i8 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)]]
def ac7_fam_k9_t8_m2_i9 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i10 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i11 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i12 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i13 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i14 : QPres := mkQPres 3 4 [[(2, true), (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i15 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i16 : QPres := mkQPres 3 4 [[(2, true), (0, false), (2, true), (0, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i17 : QPres := mkQPres 3 4 [[(2, true), (2, true), (0, true), (2, false)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (0, false), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i18 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i19 : QPres := mkQPres 3 4 [[(0, true), (1, true), (2, true), (0, true), (1, false), (0, false)], [(1, true), (1, true)], [(0, true), (1, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i20 : QPres := mkQPres 3 4 [[(2, false), (0, false)], [(1, true), (1, true)], [(0, true), (1, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i21 : QPres := mkQPres 3 4 [[(0, true), (2, true)], [(1, true), (1, true)], [(2, false), (1, true), (2, true), (1, false)], [(2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true), (2, true)]]
def ac7_fam_k9_t8_m2_i22 : QPres := mkQPres 2 3 [[(0, true), (0, true)], [(1, false), (0, true), (1, true), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k9_t8_m2_i23 : QPres := mkQPres 2 3 [[(0, true), (0, true)], [(1, true), (0, true), (1, false), (0, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k9_t8_m2_i24 : QPres := mkQPres 2 3 [[(1, true), (0, false), (1, true), (0, false)], [(1, true), (1, true), (0, false), (1, false), (0, true), (1, false)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]]
def ac7_fam_k9_t8_m2_i25 : QPres := mkQPres 2 3 [[(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k9_t8_m2_i26 : QPres := mkQPres 2 3 [[(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (1, false), (1, false)], [(0, true), (1, true), (0, false), (1, false)], [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)]]
def ac7_fam_k9_t8_m2_i27 : QPres := mkQPres 2 3 [[(1, true), (1, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (1, true), (0, false), (1, false)], [(1, false), (1, false)]]
def ac7_fam_k9_t8_m2_i28 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (1, true), (0, false), (1, false)], [(1, false), (1, false)]]
def ac7_fam_k9_t8_m2_i29 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true), (0, true), (1, false), (0, false)], [(1, false), (1, false)]]
def ac7_fam_k9_t8_m2_i30 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(0, true), (1, true), (0, false), (1, false), (1, false), (1, false)], [(1, true), (0, true), (1, false), (0, false)]]
def ac7_fam_k9_t8_m2_i31 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, false), (1, false)], [(1, true), (0, true), (1, false), (0, false)]]
def ac7_fam_k9_t8_m2_i32 : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]
def ac7_fam_k9_t8_m2_e : QPres := mkQPres 2 3 [[(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)], [(1, true), (1, true)], [(0, true), (1, true), (0, false), (1, false)]]

def ac7_fam_k9_t8_m2_c1 : List QMove :=
  [ .prolong,
    .nijinv 2 0 ]
def ac7_fam_k9_t8_m2_c2 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k9_t8_m2_c3 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k9_t8_m2_c4 : List QMove :=
  [ .nijinv 2 0,
    .nijinv 2 0 ]
def ac7_fam_k9_t8_m2_c5 : List QMove :=
  [ .nijinv 2 0,
    .conj 3 [(0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false)] ]
def ac7_fam_k9_t8_m2_c6 : List QMove :=
  [ .mul 0 3,
    .conj 3 [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)] ]
def ac7_fam_k9_t8_m2_c7 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k9_t8_m2_c8 : List QMove :=
  [ .conj 0 [(2, false), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)] ]
def ac7_fam_k9_t8_m2_c9 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)] ]
def ac7_fam_k9_t8_m2_c10 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (0, false), (0, false), (0, false), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k9_t8_m2_c11 : List QMove :=
  [ .conj 0 [(2, false), (0, true), (0, true), (0, true), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (0, false), (0, false), (0, false), (2, true)] ]
def ac7_fam_k9_t8_m2_c12 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (0, true), (0, true), (0, true), (0, true), (2, false)] ]
def ac7_fam_k9_t8_m2_c13 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (0, false), (0, false), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k9_t8_m2_c14 : List QMove :=
  [ .conj 0 [(2, false), (0, true), (0, true), (0, true), (2, false)],
    .conj 0 [(2, true), (0, false), (0, false), (2, true)] ]
def ac7_fam_k9_t8_m2_c15 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (0, true), (0, true), (2, false)] ]
def ac7_fam_k9_t8_m2_c16 : List QMove :=
  [ .conj 0 [(2, true), (0, false), (2, true)],
    .lmul 3 0 ]
def ac7_fam_k9_t8_m2_c17 : List QMove :=
  [ .conj 0 [(2, false), (0, true), (2, false)],
    .conj 0 [(2, true), (2, true)] ]
def ac7_fam_k9_t8_m2_c18 : List QMove :=
  [ .lmul 3 0,
    .conj 0 [(2, false), (2, false)] ]
def ac7_fam_k9_t8_m2_c19 : List QMove :=
  [ .conj 0 [(0, true), (1, true), (2, true)],
    .lmul 2 0 ]
def ac7_fam_k9_t8_m2_c20 : List QMove :=
  [ .conj 0 [(2, false), (1, false), (0, false)],
    .inv 0 ]
def ac7_fam_k9_t8_m2_c21 : List QMove :=
  [ .lmul 2 0,
    .inv 0 ]
def ac7_fam_k9_t8_m2_c22 : List QMove :=
  [ .nijinv 0 2,
    .delete 0 0 [] ]
def ac7_fam_k9_t8_m2_c23 : List QMove :=
  [ .inv 1,
    .conj 1 [(1, true)] ]
def ac7_fam_k9_t8_m2_c24 : List QMove :=
  [ .neg 0,
    .nijinv 0 1 ]
def ac7_fam_k9_t8_m2_c25 : List QMove :=
  [ .nij 1 0,
    .njiinv 0 1 ]
def ac7_fam_k9_t8_m2_c26 : List QMove :=
  [ .mul 0 2,
    .inv 0 ]
def ac7_fam_k9_t8_m2_c27 : List QMove :=
  [ .mul 2 0,
    .inv 0 ]
def ac7_fam_k9_t8_m2_c28 : List QMove :=
  [ .mul 0 2,
    .conj 0 [(1, false), (1, false)] ]
def ac7_fam_k9_t8_m2_c29 : List QMove :=
  [ .mul 1 2,
    .inv 1 ]
def ac7_fam_k9_t8_m2_c30 : List QMove :=
  [ .mul 2 1,
    .inv 1 ]
def ac7_fam_k9_t8_m2_c31 : List QMove :=
  [ .mul 1 2,
    .conj 1 [(1, true), (0, true), (1, false), (0, false)] ]
def ac7_fam_k9_t8_m2_c32 : List QMove :=
  [ .inv 1,
    .inv 2 ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b1 :
    replay ac7_fam_k9_t8_m2_c1 ac7_fam_k9_t8_m2_s = some ac7_fam_k9_t8_m2_i1 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b2 :
    replay ac7_fam_k9_t8_m2_c2 ac7_fam_k9_t8_m2_i1 = some ac7_fam_k9_t8_m2_i2 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b3 :
    replay ac7_fam_k9_t8_m2_c3 ac7_fam_k9_t8_m2_i2 = some ac7_fam_k9_t8_m2_i3 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b4 :
    replay ac7_fam_k9_t8_m2_c4 ac7_fam_k9_t8_m2_i3 = some ac7_fam_k9_t8_m2_i4 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b5 :
    replay ac7_fam_k9_t8_m2_c5 ac7_fam_k9_t8_m2_i4 = some ac7_fam_k9_t8_m2_i5 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b6 :
    replay ac7_fam_k9_t8_m2_c6 ac7_fam_k9_t8_m2_i5 = some ac7_fam_k9_t8_m2_i6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b7 :
    replay ac7_fam_k9_t8_m2_c7 ac7_fam_k9_t8_m2_i6 = some ac7_fam_k9_t8_m2_i7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b8 :
    replay ac7_fam_k9_t8_m2_c8 ac7_fam_k9_t8_m2_i7 = some ac7_fam_k9_t8_m2_i8 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b9 :
    replay ac7_fam_k9_t8_m2_c9 ac7_fam_k9_t8_m2_i8 = some ac7_fam_k9_t8_m2_i9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b10 :
    replay ac7_fam_k9_t8_m2_c10 ac7_fam_k9_t8_m2_i9 = some ac7_fam_k9_t8_m2_i10 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b11 :
    replay ac7_fam_k9_t8_m2_c11 ac7_fam_k9_t8_m2_i10 = some ac7_fam_k9_t8_m2_i11 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b12 :
    replay ac7_fam_k9_t8_m2_c12 ac7_fam_k9_t8_m2_i11 = some ac7_fam_k9_t8_m2_i12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b13 :
    replay ac7_fam_k9_t8_m2_c13 ac7_fam_k9_t8_m2_i12 = some ac7_fam_k9_t8_m2_i13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b14 :
    replay ac7_fam_k9_t8_m2_c14 ac7_fam_k9_t8_m2_i13 = some ac7_fam_k9_t8_m2_i14 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b15 :
    replay ac7_fam_k9_t8_m2_c15 ac7_fam_k9_t8_m2_i14 = some ac7_fam_k9_t8_m2_i15 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b16 :
    replay ac7_fam_k9_t8_m2_c16 ac7_fam_k9_t8_m2_i15 = some ac7_fam_k9_t8_m2_i16 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b17 :
    replay ac7_fam_k9_t8_m2_c17 ac7_fam_k9_t8_m2_i16 = some ac7_fam_k9_t8_m2_i17 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b18 :
    replay ac7_fam_k9_t8_m2_c18 ac7_fam_k9_t8_m2_i17 = some ac7_fam_k9_t8_m2_i18 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b19 :
    replay ac7_fam_k9_t8_m2_c19 ac7_fam_k9_t8_m2_i18 = some ac7_fam_k9_t8_m2_i19 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b20 :
    replay ac7_fam_k9_t8_m2_c20 ac7_fam_k9_t8_m2_i19 = some ac7_fam_k9_t8_m2_i20 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b21 :
    replay ac7_fam_k9_t8_m2_c21 ac7_fam_k9_t8_m2_i20 = some ac7_fam_k9_t8_m2_i21 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b22 :
    replay ac7_fam_k9_t8_m2_c22 ac7_fam_k9_t8_m2_i21 = some ac7_fam_k9_t8_m2_i22 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b23 :
    replay ac7_fam_k9_t8_m2_c23 ac7_fam_k9_t8_m2_i22 = some ac7_fam_k9_t8_m2_i23 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b24 :
    replay ac7_fam_k9_t8_m2_c24 ac7_fam_k9_t8_m2_i23 = some ac7_fam_k9_t8_m2_i24 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b25 :
    replay ac7_fam_k9_t8_m2_c25 ac7_fam_k9_t8_m2_i24 = some ac7_fam_k9_t8_m2_i25 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b26 :
    replay ac7_fam_k9_t8_m2_c26 ac7_fam_k9_t8_m2_i25 = some ac7_fam_k9_t8_m2_i26 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b27 :
    replay ac7_fam_k9_t8_m2_c27 ac7_fam_k9_t8_m2_i26 = some ac7_fam_k9_t8_m2_i27 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b28 :
    replay ac7_fam_k9_t8_m2_c28 ac7_fam_k9_t8_m2_i27 = some ac7_fam_k9_t8_m2_i28 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b29 :
    replay ac7_fam_k9_t8_m2_c29 ac7_fam_k9_t8_m2_i28 = some ac7_fam_k9_t8_m2_i29 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b30 :
    replay ac7_fam_k9_t8_m2_c30 ac7_fam_k9_t8_m2_i29 = some ac7_fam_k9_t8_m2_i30 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b31 :
    replay ac7_fam_k9_t8_m2_c31 ac7_fam_k9_t8_m2_i30 = some ac7_fam_k9_t8_m2_i31 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem ac7_fam_k9_t8_m2_b32 :
    replay ac7_fam_k9_t8_m2_c32 ac7_fam_k9_t8_m2_i31 = some ac7_fam_k9_t8_m2_i32 := by decide

theorem ac7_fam_k9_t8_m2_k0_2 : replay (ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ac7_fam_k9_t8_m2_s = some ac7_fam_k9_t8_m2_i2 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c1) (ms₂ := ac7_fam_k9_t8_m2_c2) (P := ac7_fam_k9_t8_m2_s) (R := ac7_fam_k9_t8_m2_i1) (S := ac7_fam_k9_t8_m2_i2) ac7_fam_k9_t8_m2_b1 ac7_fam_k9_t8_m2_b2
theorem ac7_fam_k9_t8_m2_k2_4 : replay (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4) ac7_fam_k9_t8_m2_i2 = some ac7_fam_k9_t8_m2_i4 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c3) (ms₂ := ac7_fam_k9_t8_m2_c4) (P := ac7_fam_k9_t8_m2_i2) (R := ac7_fam_k9_t8_m2_i3) (S := ac7_fam_k9_t8_m2_i4) ac7_fam_k9_t8_m2_b3 ac7_fam_k9_t8_m2_b4
theorem ac7_fam_k9_t8_m2_k0_4 : replay ((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ac7_fam_k9_t8_m2_s = some ac7_fam_k9_t8_m2_i4 :=
  replay_concat (ms₁ := (ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2)) (ms₂ := (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) (P := ac7_fam_k9_t8_m2_s) (R := ac7_fam_k9_t8_m2_i2) (S := ac7_fam_k9_t8_m2_i4) ac7_fam_k9_t8_m2_k0_2 ac7_fam_k9_t8_m2_k2_4
theorem ac7_fam_k9_t8_m2_k4_6 : replay (ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ac7_fam_k9_t8_m2_i4 = some ac7_fam_k9_t8_m2_i6 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c5) (ms₂ := ac7_fam_k9_t8_m2_c6) (P := ac7_fam_k9_t8_m2_i4) (R := ac7_fam_k9_t8_m2_i5) (S := ac7_fam_k9_t8_m2_i6) ac7_fam_k9_t8_m2_b5 ac7_fam_k9_t8_m2_b6
theorem ac7_fam_k9_t8_m2_k6_8 : replay (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8) ac7_fam_k9_t8_m2_i6 = some ac7_fam_k9_t8_m2_i8 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c7) (ms₂ := ac7_fam_k9_t8_m2_c8) (P := ac7_fam_k9_t8_m2_i6) (R := ac7_fam_k9_t8_m2_i7) (S := ac7_fam_k9_t8_m2_i8) ac7_fam_k9_t8_m2_b7 ac7_fam_k9_t8_m2_b8
theorem ac7_fam_k9_t8_m2_k4_8 : replay ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8)) ac7_fam_k9_t8_m2_i4 = some ac7_fam_k9_t8_m2_i8 :=
  replay_concat (ms₁ := (ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6)) (ms₂ := (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8)) (P := ac7_fam_k9_t8_m2_i4) (R := ac7_fam_k9_t8_m2_i6) (S := ac7_fam_k9_t8_m2_i8) ac7_fam_k9_t8_m2_k4_6 ac7_fam_k9_t8_m2_k6_8
theorem ac7_fam_k9_t8_m2_k0_8 : replay (((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) ac7_fam_k9_t8_m2_s = some ac7_fam_k9_t8_m2_i8 :=
  replay_concat (ms₁ := ((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4))) (ms₂ := ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) (P := ac7_fam_k9_t8_m2_s) (R := ac7_fam_k9_t8_m2_i4) (S := ac7_fam_k9_t8_m2_i8) ac7_fam_k9_t8_m2_k0_4 ac7_fam_k9_t8_m2_k4_8
theorem ac7_fam_k9_t8_m2_k8_10 : replay (ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ac7_fam_k9_t8_m2_i8 = some ac7_fam_k9_t8_m2_i10 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c9) (ms₂ := ac7_fam_k9_t8_m2_c10) (P := ac7_fam_k9_t8_m2_i8) (R := ac7_fam_k9_t8_m2_i9) (S := ac7_fam_k9_t8_m2_i10) ac7_fam_k9_t8_m2_b9 ac7_fam_k9_t8_m2_b10
theorem ac7_fam_k9_t8_m2_k10_12 : replay (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12) ac7_fam_k9_t8_m2_i10 = some ac7_fam_k9_t8_m2_i12 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c11) (ms₂ := ac7_fam_k9_t8_m2_c12) (P := ac7_fam_k9_t8_m2_i10) (R := ac7_fam_k9_t8_m2_i11) (S := ac7_fam_k9_t8_m2_i12) ac7_fam_k9_t8_m2_b11 ac7_fam_k9_t8_m2_b12
theorem ac7_fam_k9_t8_m2_k8_12 : replay ((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ac7_fam_k9_t8_m2_i8 = some ac7_fam_k9_t8_m2_i12 :=
  replay_concat (ms₁ := (ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10)) (ms₂ := (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) (P := ac7_fam_k9_t8_m2_i8) (R := ac7_fam_k9_t8_m2_i10) (S := ac7_fam_k9_t8_m2_i12) ac7_fam_k9_t8_m2_k8_10 ac7_fam_k9_t8_m2_k10_12
theorem ac7_fam_k9_t8_m2_k12_14 : replay (ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ac7_fam_k9_t8_m2_i12 = some ac7_fam_k9_t8_m2_i14 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c13) (ms₂ := ac7_fam_k9_t8_m2_c14) (P := ac7_fam_k9_t8_m2_i12) (R := ac7_fam_k9_t8_m2_i13) (S := ac7_fam_k9_t8_m2_i14) ac7_fam_k9_t8_m2_b13 ac7_fam_k9_t8_m2_b14
theorem ac7_fam_k9_t8_m2_k14_16 : replay (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16) ac7_fam_k9_t8_m2_i14 = some ac7_fam_k9_t8_m2_i16 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c15) (ms₂ := ac7_fam_k9_t8_m2_c16) (P := ac7_fam_k9_t8_m2_i14) (R := ac7_fam_k9_t8_m2_i15) (S := ac7_fam_k9_t8_m2_i16) ac7_fam_k9_t8_m2_b15 ac7_fam_k9_t8_m2_b16
theorem ac7_fam_k9_t8_m2_k12_16 : replay ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)) ac7_fam_k9_t8_m2_i12 = some ac7_fam_k9_t8_m2_i16 :=
  replay_concat (ms₁ := (ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14)) (ms₂ := (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)) (P := ac7_fam_k9_t8_m2_i12) (R := ac7_fam_k9_t8_m2_i14) (S := ac7_fam_k9_t8_m2_i16) ac7_fam_k9_t8_m2_k12_14 ac7_fam_k9_t8_m2_k14_16
theorem ac7_fam_k9_t8_m2_k8_16 : replay (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16))) ac7_fam_k9_t8_m2_i8 = some ac7_fam_k9_t8_m2_i16 :=
  replay_concat (ms₁ := ((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12))) (ms₂ := ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16))) (P := ac7_fam_k9_t8_m2_i8) (R := ac7_fam_k9_t8_m2_i12) (S := ac7_fam_k9_t8_m2_i16) ac7_fam_k9_t8_m2_k8_12 ac7_fam_k9_t8_m2_k12_16
theorem ac7_fam_k9_t8_m2_k0_16 : replay ((((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) ++ (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)))) ac7_fam_k9_t8_m2_s = some ac7_fam_k9_t8_m2_i16 :=
  replay_concat (ms₁ := (((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8)))) (ms₂ := (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)))) (P := ac7_fam_k9_t8_m2_s) (R := ac7_fam_k9_t8_m2_i8) (S := ac7_fam_k9_t8_m2_i16) ac7_fam_k9_t8_m2_k0_8 ac7_fam_k9_t8_m2_k8_16
theorem ac7_fam_k9_t8_m2_k16_18 : replay (ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ac7_fam_k9_t8_m2_i16 = some ac7_fam_k9_t8_m2_i18 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c17) (ms₂ := ac7_fam_k9_t8_m2_c18) (P := ac7_fam_k9_t8_m2_i16) (R := ac7_fam_k9_t8_m2_i17) (S := ac7_fam_k9_t8_m2_i18) ac7_fam_k9_t8_m2_b17 ac7_fam_k9_t8_m2_b18
theorem ac7_fam_k9_t8_m2_k18_20 : replay (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20) ac7_fam_k9_t8_m2_i18 = some ac7_fam_k9_t8_m2_i20 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c19) (ms₂ := ac7_fam_k9_t8_m2_c20) (P := ac7_fam_k9_t8_m2_i18) (R := ac7_fam_k9_t8_m2_i19) (S := ac7_fam_k9_t8_m2_i20) ac7_fam_k9_t8_m2_b19 ac7_fam_k9_t8_m2_b20
theorem ac7_fam_k9_t8_m2_k16_20 : replay ((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ac7_fam_k9_t8_m2_i16 = some ac7_fam_k9_t8_m2_i20 :=
  replay_concat (ms₁ := (ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18)) (ms₂ := (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) (P := ac7_fam_k9_t8_m2_i16) (R := ac7_fam_k9_t8_m2_i18) (S := ac7_fam_k9_t8_m2_i20) ac7_fam_k9_t8_m2_k16_18 ac7_fam_k9_t8_m2_k18_20
theorem ac7_fam_k9_t8_m2_k20_22 : replay (ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ac7_fam_k9_t8_m2_i20 = some ac7_fam_k9_t8_m2_i22 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c21) (ms₂ := ac7_fam_k9_t8_m2_c22) (P := ac7_fam_k9_t8_m2_i20) (R := ac7_fam_k9_t8_m2_i21) (S := ac7_fam_k9_t8_m2_i22) ac7_fam_k9_t8_m2_b21 ac7_fam_k9_t8_m2_b22
theorem ac7_fam_k9_t8_m2_k22_24 : replay (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24) ac7_fam_k9_t8_m2_i22 = some ac7_fam_k9_t8_m2_i24 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c23) (ms₂ := ac7_fam_k9_t8_m2_c24) (P := ac7_fam_k9_t8_m2_i22) (R := ac7_fam_k9_t8_m2_i23) (S := ac7_fam_k9_t8_m2_i24) ac7_fam_k9_t8_m2_b23 ac7_fam_k9_t8_m2_b24
theorem ac7_fam_k9_t8_m2_k20_24 : replay ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24)) ac7_fam_k9_t8_m2_i20 = some ac7_fam_k9_t8_m2_i24 :=
  replay_concat (ms₁ := (ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22)) (ms₂ := (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24)) (P := ac7_fam_k9_t8_m2_i20) (R := ac7_fam_k9_t8_m2_i22) (S := ac7_fam_k9_t8_m2_i24) ac7_fam_k9_t8_m2_k20_22 ac7_fam_k9_t8_m2_k22_24
theorem ac7_fam_k9_t8_m2_k16_24 : replay (((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) ac7_fam_k9_t8_m2_i16 = some ac7_fam_k9_t8_m2_i24 :=
  replay_concat (ms₁ := ((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20))) (ms₂ := ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) (P := ac7_fam_k9_t8_m2_i16) (R := ac7_fam_k9_t8_m2_i20) (S := ac7_fam_k9_t8_m2_i24) ac7_fam_k9_t8_m2_k16_20 ac7_fam_k9_t8_m2_k20_24
theorem ac7_fam_k9_t8_m2_k24_26 : replay (ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ac7_fam_k9_t8_m2_i24 = some ac7_fam_k9_t8_m2_i26 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c25) (ms₂ := ac7_fam_k9_t8_m2_c26) (P := ac7_fam_k9_t8_m2_i24) (R := ac7_fam_k9_t8_m2_i25) (S := ac7_fam_k9_t8_m2_i26) ac7_fam_k9_t8_m2_b25 ac7_fam_k9_t8_m2_b26
theorem ac7_fam_k9_t8_m2_k26_28 : replay (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28) ac7_fam_k9_t8_m2_i26 = some ac7_fam_k9_t8_m2_i28 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c27) (ms₂ := ac7_fam_k9_t8_m2_c28) (P := ac7_fam_k9_t8_m2_i26) (R := ac7_fam_k9_t8_m2_i27) (S := ac7_fam_k9_t8_m2_i28) ac7_fam_k9_t8_m2_b27 ac7_fam_k9_t8_m2_b28
theorem ac7_fam_k9_t8_m2_k24_28 : replay ((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ac7_fam_k9_t8_m2_i24 = some ac7_fam_k9_t8_m2_i28 :=
  replay_concat (ms₁ := (ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26)) (ms₂ := (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) (P := ac7_fam_k9_t8_m2_i24) (R := ac7_fam_k9_t8_m2_i26) (S := ac7_fam_k9_t8_m2_i28) ac7_fam_k9_t8_m2_k24_26 ac7_fam_k9_t8_m2_k26_28
theorem ac7_fam_k9_t8_m2_k28_30 : replay (ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ac7_fam_k9_t8_m2_i28 = some ac7_fam_k9_t8_m2_i30 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c29) (ms₂ := ac7_fam_k9_t8_m2_c30) (P := ac7_fam_k9_t8_m2_i28) (R := ac7_fam_k9_t8_m2_i29) (S := ac7_fam_k9_t8_m2_i30) ac7_fam_k9_t8_m2_b29 ac7_fam_k9_t8_m2_b30
theorem ac7_fam_k9_t8_m2_k30_32 : replay (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32) ac7_fam_k9_t8_m2_i30 = some ac7_fam_k9_t8_m2_i32 :=
  replay_concat (ms₁ := ac7_fam_k9_t8_m2_c31) (ms₂ := ac7_fam_k9_t8_m2_c32) (P := ac7_fam_k9_t8_m2_i30) (R := ac7_fam_k9_t8_m2_i31) (S := ac7_fam_k9_t8_m2_i32) ac7_fam_k9_t8_m2_b31 ac7_fam_k9_t8_m2_b32
theorem ac7_fam_k9_t8_m2_k28_32 : replay ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32)) ac7_fam_k9_t8_m2_i28 = some ac7_fam_k9_t8_m2_i32 :=
  replay_concat (ms₁ := (ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30)) (ms₂ := (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32)) (P := ac7_fam_k9_t8_m2_i28) (R := ac7_fam_k9_t8_m2_i30) (S := ac7_fam_k9_t8_m2_i32) ac7_fam_k9_t8_m2_k28_30 ac7_fam_k9_t8_m2_k30_32
theorem ac7_fam_k9_t8_m2_k24_32 : replay (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32))) ac7_fam_k9_t8_m2_i24 = some ac7_fam_k9_t8_m2_i32 :=
  replay_concat (ms₁ := ((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28))) (ms₂ := ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32))) (P := ac7_fam_k9_t8_m2_i24) (R := ac7_fam_k9_t8_m2_i28) (S := ac7_fam_k9_t8_m2_i32) ac7_fam_k9_t8_m2_k24_28 ac7_fam_k9_t8_m2_k28_32
theorem ac7_fam_k9_t8_m2_k16_32 : replay ((((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) ++ (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32)))) ac7_fam_k9_t8_m2_i16 = some ac7_fam_k9_t8_m2_i32 :=
  replay_concat (ms₁ := (((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24)))) (ms₂ := (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32)))) (P := ac7_fam_k9_t8_m2_i16) (R := ac7_fam_k9_t8_m2_i24) (S := ac7_fam_k9_t8_m2_i32) ac7_fam_k9_t8_m2_k16_24 ac7_fam_k9_t8_m2_k24_32
theorem ac7_fam_k9_t8_m2_k0_32 : replay (((((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) ++ (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)))) ++ ((((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) ++ (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32))))) ac7_fam_k9_t8_m2_s = some ac7_fam_k9_t8_m2_i32 :=
  replay_concat (ms₁ := ((((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) ++ (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16))))) (ms₂ := ((((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) ++ (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32))))) (P := ac7_fam_k9_t8_m2_s) (R := ac7_fam_k9_t8_m2_i16) (S := ac7_fam_k9_t8_m2_i32) ac7_fam_k9_t8_m2_k0_16 ac7_fam_k9_t8_m2_k16_32

/-- `fam_k9_t8_m2.cert` checked: replaying its 64 Q**-moves from the recorded start tuple
    reaches the recorded end tuple. -/
theorem ac7_fam_k9_t8_m2_replay : replay (((((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) ++ (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)))) ++ ((((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) ++ (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32))))) ac7_fam_k9_t8_m2_s = some ac7_fam_k9_t8_m2_i32 := ac7_fam_k9_t8_m2_k0_32

/-- The same in the form of the `checkCert` checker. -/
theorem ac7_fam_k9_t8_m2_checked : checkCert (((((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) ++ (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)))) ++ ((((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) ++ (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32))))) ac7_fam_k9_t8_m2_s ac7_fam_k9_t8_m2_i32 = true := by
  rw [checkCert]
  exact decide_eq_true_eq.mpr ac7_fam_k9_t8_m2_replay

/-- The endpoints of `fam_k9_t8_m2.cert` are the presentations `<x,y | x^9, y^2, [x^1,y]>`
    and `<x,y | x^9, y^2, [x^1,y]>` of the statement. -/
theorem ac7_fam_k9_t8_m2_endpoints :
    metz 9 2 1 = ac7_fam_k9_t8_m2_s ∧ metz 9 2 1 = ac7_fam_k9_t8_m2_e := by
  constructor <;> decide

/-- **The Q**-equivalence itself**, as an existential over move lists: the 64-move
    certificate proves it.  For the `j = 1` rows the two presentations are identical and
    the statement is trivial; the certificate is the recipe's, not the trivial one. -/
theorem ac7_fam_k9_t8_m2_qstar_equiv :
    ∃ ms : List QMove, replay ms (metz 9 2 1) = some (metz 9 2 1) := by
  refine ⟨(((((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) ++ (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)))) ++ ((((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) ++ (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32))))), ?_⟩
  calc replay (((((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) ++ (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)))) ++ ((((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) ++ (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32))))) (metz 9 2 1) = replay (((((ac7_fam_k9_t8_m2_c1 ++ ac7_fam_k9_t8_m2_c2) ++ (ac7_fam_k9_t8_m2_c3 ++ ac7_fam_k9_t8_m2_c4)) ++ ((ac7_fam_k9_t8_m2_c5 ++ ac7_fam_k9_t8_m2_c6) ++ (ac7_fam_k9_t8_m2_c7 ++ ac7_fam_k9_t8_m2_c8))) ++ (((ac7_fam_k9_t8_m2_c9 ++ ac7_fam_k9_t8_m2_c10) ++ (ac7_fam_k9_t8_m2_c11 ++ ac7_fam_k9_t8_m2_c12)) ++ ((ac7_fam_k9_t8_m2_c13 ++ ac7_fam_k9_t8_m2_c14) ++ (ac7_fam_k9_t8_m2_c15 ++ ac7_fam_k9_t8_m2_c16)))) ++ ((((ac7_fam_k9_t8_m2_c17 ++ ac7_fam_k9_t8_m2_c18) ++ (ac7_fam_k9_t8_m2_c19 ++ ac7_fam_k9_t8_m2_c20)) ++ ((ac7_fam_k9_t8_m2_c21 ++ ac7_fam_k9_t8_m2_c22) ++ (ac7_fam_k9_t8_m2_c23 ++ ac7_fam_k9_t8_m2_c24))) ++ (((ac7_fam_k9_t8_m2_c25 ++ ac7_fam_k9_t8_m2_c26) ++ (ac7_fam_k9_t8_m2_c27 ++ ac7_fam_k9_t8_m2_c28)) ++ ((ac7_fam_k9_t8_m2_c29 ++ ac7_fam_k9_t8_m2_c30) ++ (ac7_fam_k9_t8_m2_c31 ++ ac7_fam_k9_t8_m2_c32))))) ac7_fam_k9_t8_m2_s := by rw [ac7_fam_k9_t8_m2_endpoints.1]
    _ = some ac7_fam_k9_t8_m2_e := ac7_fam_k9_t8_m2_replay
    _ = some (metz 9 2 1) := by rw [ac7_fam_k9_t8_m2_endpoints.2]


/-! ## (iii) The algebra of the recipe, for all parameters -/

section Algebra

variable {G : Type*} [Group G]

/-- A finite product of conjugates of `R` and of `R⁻¹`.  This is the shape in which a
Q-multiplication appears: a single Q-move multiplies a relator by a conjugate of a *different*
relator (round 6's Lemma 1), so a multiplier that is a product of conjugates of one relator is
exactly what a run of Q-multiplications can supply. -/
inductive ConjProd (R : G) : G → Prop
  /-- the empty product -/
  | one : ConjProd R 1
  /-- the product of two -/
  | mul (a b : G) : ConjProd R a → ConjProd R b → ConjProd R (a * b)
  /-- a conjugate of `R` -/
  | base (g : G) : ConjProd R (g * R * g⁻¹)
  /-- a conjugate of `R⁻¹` -/
  | baseInv (g : G) : ConjProd R (g * R⁻¹ * g⁻¹)

variable {R : G}

/-- Conjugating a product of conjugates again gives a product of conjugates.  This is the step
that lets the telescoping induction run: the factor `u (L σ(L)⁻¹) u⁻¹` of the identity
`V σ(V)⁻¹ = (u (L σ(L)⁻¹) u⁻¹) · (u σ(u)⁻¹)` is of this form. -/
theorem conjProd_conj {X : G} (h : ConjProd R X) (g : G) : ConjProd R (g * X * g⁻¹) := by
  induction h with
  | one => simpa using ConjProd.one (R := R)
  | mul a b ha hb iha ihb =>
    have h' : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [h']
    exact ConjProd.mul (g * a * g⁻¹) (g * b * g⁻¹) iha ihb
  | base u =>
    have h' : g * (u * R * u⁻¹) * g⁻¹ = (g * u) * R * (g * u)⁻¹ := by group
    rw [h']
    exact ConjProd.base (g * u)
  | baseInv u =>
    have h' : g * (u * R⁻¹ * u⁻¹) * g⁻¹ = (g * u) * R⁻¹ * (g * u)⁻¹ := by group
    rw [h']
    exact ConjProd.baseInv (g * u)

/-- The inverse of a product of conjugates is a product of conjugates. -/
theorem conjProd_inv {X : G} (h : ConjProd R X) : ConjProd R X⁻¹ := by
  induction h with
  | one => simpa using ConjProd.one (R := R)
  | mul a b ha hb iha ihb =>
    have h' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    rw [h']
    exact ConjProd.mul b⁻¹ a⁻¹ ihb iha
  | base u =>
    have h' : (u * R * u⁻¹)⁻¹ = u * R⁻¹ * u⁻¹ := by group
    rw [h']
    exact ConjProd.baseInv u
  | baseInv u =>
    have h' : (u * R⁻¹ * u⁻¹)⁻¹ = u * R * u⁻¹ := by group
    rw [h']
    exact ConjProd.base u

/-- A product of conjugates of `R` lies in the normal closure of `R`: the invariant reading of a
Q-multiplication by conjugates of one relator. -/
theorem conjProd_mem_normalClosure {X : G} (h : ConjProd R X) :
    X ∈ Subgroup.normalClosure ({R} : Set G) := by
  have hR : R ∈ Subgroup.normalClosure ({R} : Set G) :=
    Subgroup.subset_normalClosure (by simp)
  have hRinv : R⁻¹ ∈ Subgroup.normalClosure ({R} : Set G) := Subgroup.inv_mem _ hR
  induction h with
  | one => exact Subgroup.one_mem _
  | mul a b ha hb iha ihb => exact Subgroup.mul_mem _ iha ihb
  | base u => simpa using (Subgroup.normalClosure_normal (s := ({R} : Set G))).conj_mem R hR u
  | baseInv u =>
    simpa using (Subgroup.normalClosure_normal (s := ({R} : Set G))).conj_mem R⁻¹ hRinv u

end Algebra

section Lemma3

/-- **Round 6's Lemma 3, product form, for all words.**  Let `σ` be an endomorphism of the free
group on `Fin n` that carries `x = of i₀` to `W⁻¹` and fixes every other generator, and put
`R = x * W` — the defining relator `x W`.  Then for every word `V` the difference
`V * (σ V)⁻¹` is a finite product of conjugates of `R` and `R⁻¹`: the multiplier that replaces the
relator `V` by its image `σ V` is a product of conjugates of the single defining relator, and it has
one factor per occurrence of `x` in `V`.  This is the content of round 6's telescoping identity,
with the induction written out. -/
theorem conjProd_of_subst {n : Nat} (i₀ : Fin n) (W : FreeGroup (Fin n))
    (σ : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hσ : σ (FreeGroup.of i₀) = W⁻¹)
    (hσ' : ∀ i : Fin n, i ≠ i₀ → σ (FreeGroup.of i) = FreeGroup.of i)
    (V : FreeGroup (Fin n)) :
    ConjProd (FreeGroup.of i₀ * W) (V * (σ V)⁻¹) := by
  have hx : ConjProd (FreeGroup.of i₀ * W) (FreeGroup.of i₀ * (σ (FreeGroup.of i₀))⁻¹) := by
    rw [hσ, inv_inv]
    simpa using ConjProd.base (1 : FreeGroup (Fin n))
  have hxin : ConjProd (FreeGroup.of i₀ * W)
      ((FreeGroup.of i₀)⁻¹ * (σ ((FreeGroup.of i₀)⁻¹))⁻¹) := by
    rw [map_inv, hσ, inv_inv]
    have h' : ((FreeGroup.of i₀)⁻¹ * W⁻¹) =
        W * (FreeGroup.of i₀ * W)⁻¹ * W⁻¹ := by group
    rw [h']
    exact ConjProd.baseInv W
  refine FreeGroup.induction_on V ?_ ?_ ?_ ?_
  · simpa using ConjProd.one (R := FreeGroup.of i₀ * W)
  · intro i
    by_cases hi : i = i₀
    · subst hi; exact hx
    · rw [hσ' i hi]
      simpa using ConjProd.one (R := FreeGroup.of i₀ * W)
  · intro i ih
    by_cases hi : i = i₀
    · subst hi; exact hxin
    · rw [map_inv, hσ' i hi]
      simpa using ConjProd.one (R := FreeGroup.of i₀ * W)
  · intro a b iha ihb
    have h' : a * b * (σ (a * b))⁻¹ = (a * (b * (σ b)⁻¹) * a⁻¹) * (a * (σ a)⁻¹) := by
      rw [map_mul, mul_inv_rev]
      group
    rw [h']
    exact ConjProd.mul _ _ (conjProd_conj ihb a) iha

/-- The instantiation the recipe uses: `σ` is the endomorphism `x ↦ W⁻¹` that fixes the other
generators.  This is `conjProd_of_subst` with the hypotheses discharged. -/
theorem conjProd_of_lift {n : Nat} (i₀ : Fin n) (W : FreeGroup (Fin n))
    (V : FreeGroup (Fin n)) :
    ConjProd (FreeGroup.of i₀ * W)
      (V * (FreeGroup.lift (fun i => if i = i₀ then W⁻¹ else FreeGroup.of i) V)⁻¹) := by
  refine conjProd_of_subst i₀ W
    (FreeGroup.lift (fun i => if i = i₀ then W⁻¹ else FreeGroup.of i)) ?_ ?_ V
  · simp
  · intro i hi
    simp [hi]

end Lemma3

section Power

/-- The product of the `j` conjugates of the defining relator `a x⁻ᵗ` used in stage 2 of the
certificate: the `i`-th factor is `x⁻ᵗ⁽ⁱ⁺¹⁾ (a x⁻ᵗ) xᵗ⁽ⁱ⁺¹⁾ = x⁻ᵗ⁽ⁱ⁺¹⁾ a xᵗⁱ`, and the factors
telescope. -/
def powerProd (t : Nat) : Nat → F2
  | 0 => 1
  | (j + 1) => (gx ^ (-(t * (j + 1) : Int)) * ga * gx ^ (t * j : Int)) * powerProd t j

/-- **The telescoping identity.**  The product of `powerProd t j` is `x⁻ᵗʲ aʲ`, for all `t` and
`j`. -/
theorem powerProd_spec (t j : Nat) : powerProd t j = gx ^ (-(t * j : Int)) * ga ^ (j : Int) := by
  induction j with
  | zero => simp [powerProd]
  | succ k ih =>
    rw [powerProd, ih]
    have h2 : (t * (k : Nat) : Int) = (t * k : Int) := by ring
    have h1 : (-(t * ((k : Nat) + 1) : Int)) = -(t * (k : Nat) : Int) + -(t : Int) := by ring
    rw [h1, h2]
    group

/-- **Stage 2 of the certificate, closed form, for all parameters.**  `x^(1+tj)` times the product
of the `j` conjugates of the defining relator `a x⁻ᵗ` is `x a^j`.  With `k = 1 + t j` this says that
the relator `x^k` can be multiplied by a product of conjugates of `a x⁻ᵗ` to become `x a^j`, for
every pair `(t, j)` — the step round 4 recorded as "the product therefore has to be found by a
genuine search". -/
theorem powerProd_cert (t j : Nat) :
    gx ^ (1 + (t * j : Int)) * powerProd t j = gx * ga ^ (j : Int) := by
  rw [powerProd_spec]
  group

/-- Each factor of `powerProd` is a conjugate of the defining relator `a x⁻ᵗ`, which is what makes
every multiplication in stage 2 a legal Q-move. -/
theorem powerProd_factor_is_conj (t i : Nat) :
    gx ^ (-(t * (i + 1) : Int)) * ga * gx ^ (t * i : Int) =
      gx ^ (-(t * (i + 1) : Int)) * (ga * gx ^ (-(t : Int))) *
        (gx ^ (-(t * (i + 1) : Int)))⁻¹ := by
  group

/-- The substitution `x ↦ a⁻ʲ` used in stage 3, on the defining relator: it carries `a x⁻ᵗ` to
`a^(1+tj)`. -/
theorem subst_defining (t j : Nat) :
    ga * (ga ^ (-(j : Int))) ^ (-(t : Int)) = ga ^ (1 + (t * j : Int)) := by
  rw [← zpow_mul]
  have h : (-(j : Int)) * (-(t : Int)) = (t * j : Int) := by ring
  rw [h]
  group

end Power

/-! ## (iv) The family table -/

/-- The theorem of round 6 for the 14 rows of its table: for each row the presentation
`<x,y | x^k, y^m, [x,y]>` is Q\*\*-equivalent to `<x,y | x^k, y^m, [x^j,y]>`.  The three `j = 1`
rows are trivial statements (the two presentations coincide); they are kept because round 6's
recipe produces a certificate for them too.  Kernel-checked: each conjunct comes from the
`_qstar_equiv` theorem of its certificate. -/
theorem family_table :
    (∃ ms : List QMove, replay ms (metz 5 5 1) = some (metz 5 5 2)) ∧
    (∃ ms : List QMove, replay ms (metz 5 5 1) = some (metz 5 5 4)) ∧
    (∃ ms : List QMove, replay ms (metz 5 3 1) = some (metz 5 3 1)) ∧
    (∃ ms : List QMove, replay ms (metz 7 5 1) = some (metz 7 5 2)) ∧
    (∃ ms : List QMove, replay ms (metz 7 2 1) = some (metz 7 2 3)) ∧
    (∃ ms : List QMove, replay ms (metz 7 4 1) = some (metz 7 4 6)) ∧
    (∃ ms : List QMove, replay ms (metz 7 1 1) = some (metz 7 1 1)) ∧
    (∃ ms : List QMove, replay ms (metz 9 5 1) = some (metz 9 5 4)) ∧
    (∃ ms : List QMove, replay ms (metz 9 3 1) = some (metz 9 3 2)) ∧
    (∃ ms : List QMove, replay ms (metz 9 2 1) = some (metz 9 2 1)) ∧
    (∃ ms : List QMove, replay ms (metz 11 5 1) = some (metz 11 5 2)) ∧
    (∃ ms : List QMove, replay ms (metz 11 5 1) = some (metz 11 5 5)) ∧
    (∃ ms : List QMove, replay ms (metz 13 5 1) = some (metz 13 5 6)) ∧
    (∃ ms : List QMove, replay ms (metz 13 7 1) = some (metz 13 7 3)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ac7_metzler_pair_qstar_gap_qstar_equiv
  · exact ac7_fam_k5_t1_m5_qstar_equiv
  · exact ac7_fam_k5_t4_m3_qstar_equiv
  · exact ac7_fam_k7_t3_m5_qstar_equiv
  · exact ac7_fam_k7_t2_m2_qstar_equiv
  · exact ac7_fam_k7_t1_m4_qstar_equiv
  · exact ac7_fam_k7_t6_m1_qstar_equiv
  · exact ac7_fam_k9_t2_m5_qstar_equiv
  · exact ac7_fam_k9_t4_m3_qstar_equiv
  · exact ac7_fam_k9_t8_m2_qstar_equiv
  · exact ac7_fam_k11_t5_m5_qstar_equiv
  · exact ac7_fam_k11_t2_m5_qstar_equiv
  · exact ac7_fam_k13_t2_m5_qstar_equiv
  · exact ac7_fam_k13_t4_m7_qstar_equiv

/-! Note: `ac7_fam_k5_t2_m5` is the same 44-move certificate as Metzler's own (`diff` of the two
move lists is empty), so the table has 14 rows and 15 certificates. -/

/-! ## Axiom audit -/

#print axioms ac7_metzler_pair_qstar_gap_checked
#print axioms ac7_metzler_pair_qstar_gap_qstar_equiv
#print axioms ac7_fam_k11_t2_m5_checked
#print axioms ac7_fam_k11_t2_m5_qstar_equiv
#print axioms ac7_fam_k11_t5_m5_checked
#print axioms ac7_fam_k11_t5_m5_qstar_equiv
#print axioms ac7_fam_k13_t2_m5_checked
#print axioms ac7_fam_k13_t2_m5_qstar_equiv
#print axioms ac7_fam_k13_t4_m7_checked
#print axioms ac7_fam_k13_t4_m7_qstar_equiv
#print axioms ac7_fam_k5_t1_m5_checked
#print axioms ac7_fam_k5_t1_m5_qstar_equiv
#print axioms ac7_fam_k5_t2_m5_checked
#print axioms ac7_fam_k5_t2_m5_qstar_equiv
#print axioms ac7_fam_k5_t4_m3_checked
#print axioms ac7_fam_k5_t4_m3_qstar_equiv
#print axioms ac7_fam_k7_t1_m4_checked
#print axioms ac7_fam_k7_t1_m4_qstar_equiv
#print axioms ac7_fam_k7_t2_m2_checked
#print axioms ac7_fam_k7_t2_m2_qstar_equiv
#print axioms ac7_fam_k7_t3_m5_checked
#print axioms ac7_fam_k7_t3_m5_qstar_equiv
#print axioms ac7_fam_k7_t6_m1_checked
#print axioms ac7_fam_k7_t6_m1_qstar_equiv
#print axioms ac7_fam_k9_t2_m5_checked
#print axioms ac7_fam_k9_t2_m5_qstar_equiv
#print axioms ac7_fam_k9_t4_m3_checked
#print axioms ac7_fam_k9_t4_m3_qstar_equiv
#print axioms ac7_fam_k9_t8_m2_checked
#print axioms ac7_fam_k9_t8_m2_qstar_equiv
#print axioms family_table
#print axioms conjProd_conj
#print axioms conjProd_inv
#print axioms conjProd_mem_normalClosure
#print axioms conjProd_of_subst
#print axioms conjProd_of_lift
#print axioms powerProd_spec
#print axioms powerProd_cert
#print axioms powerProd_factor_is_conj
#print axioms subst_defining

end AC7
