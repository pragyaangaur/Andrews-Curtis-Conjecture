/-
# The Metzler recipe's parameter boundary, transferred to the campaign's Q** layer

`MetzlerSharp.lean` proves the group-theoretic obstruction for the Metzler family.  This file
re-states it for the campaign's own objects — `AC5.QPres`, `AC5.checkCert`, `AC5.CheckWF` and
`QSound`'s `QEquiv` — so the sharpness result is a statement about the shipped checker, not only
about an isomorphic copy of it.

Main results:

* `not_qEquiv_four_two_two` : `metz 4 2 1` and `metz 4 2 2` are NOT `Q**`-equivalent.
* `not_qEquiv_four_even` : for every even `m` and `j`, `metz 4 m 1` and `metz 4 m j` are not
  `Q**`-equivalent.  Since the recipe's hypothesis at `k = 4` is `j ∣ 3`, every even `j` is
  outside it: the recipe cannot be extended to those parameters by ANY move list.
* `no_checkCert_four_two_two` : every `AC5` certificate between them is rejected — for every
  admissible move list `ms` the checker returns `false`.  This is what a search engine needs:
  the failure is not a bound on the engine, it is a theorem about the move set.
* `no_checkCert_four_even` : the same for the whole even family.
* `metzQ_rels_eq` : the `AC5` presentations used here have literally the same relator lists as
  `AC8.metz`, `AC8.lean`'s presentations.

Nothing here proves or disproves the Andrews-Curtis conjecture.
-/
import MetzlerSharp
import QSound
import AC8

namespace MetzlerSharpBridge

open AC5

/-- `AC8.metz k m j` as an `AC5.QPres`: the same relator list `<x,y | y^m, [x^j,y], x^k>`,
with `AC8`'s relator order. -/
def metzQ (k m j : Nat) : QPres :=
  ⟨2, 3, MetzlerSharp.metzRels k m j⟩

/-- The `AC5` presentation has the relator list of `AC8.metz`. -/
theorem metzQ_rels_eq (k m j : Nat) : (metzQ k m j).rels = (AC8.metz k m j).rels := by
  funext i
  fin_cases i <;> rfl

/-- **The Metzler pair `(4,2,1)` vs `(4,2,2)` is not `Q**`-equivalent.** -/
theorem not_qEquiv_four_two_two : ¬ QEquiv (metzQ 4 2 1) (metzQ 4 2 2) :=
  MetzlerSharp.not_mulEquiv_four_two_two

/-- **The whole even family at `k = 4`**: `metz 4 m 1` and `metz 4 m j` (m, j even) are not
`Q**`-equivalent, hence not related by any group-preserving move list at all. -/
theorem not_qEquiv_four_even (m j : Nat) (hm : Even m) (hj : Even j) :
    ¬ QEquiv (metzQ 4 m 1) (metzQ 4 m j) :=
  MetzlerSharp.not_mulEquiv_four_even m j hm hj

/-- **The checker corollary**: for every admissible move list the `AC5` `Q**` checker rejects
the pair outright.  (The checker is a decision procedure; the theorem is that the answer is
`false`, not that a particular engine failed to find a certificate.) -/
theorem no_checkCert_four_two_two (ms : List QMove) (hwf : CheckWF ms = true) :
    checkCert ms (metzQ 4 2 1) (metzQ 4 2 2) = false := by
  cases hh : checkCert ms (metzQ 4 2 1) (metzQ 4 2 2) with
  | false => rfl
  | true => exact absurd (checkCert_sound hh hwf) not_qEquiv_four_two_two

/-- No admissible certificate between the pair exists, as an existential negation. -/
theorem no_certificate_four_two_two :
    ¬ ∃ ms : List QMove, CheckWF ms = true ∧ checkCert ms (metzQ 4 2 1) (metzQ 4 2 2) = true := by
  rintro ⟨ms, hwf, hc⟩
  exact not_qEquiv_four_two_two (checkCert_sound hc hwf)

/-- The checker corollary for the whole even family. -/
theorem no_checkCert_four_even (m j : Nat) (hm : Even m) (hj : Even j) (ms : List QMove)
    (hwf : CheckWF ms = true) : checkCert ms (metzQ 4 m 1) (metzQ 4 m j) = false := by
  cases hh : checkCert ms (metzQ 4 m 1) (metzQ 4 m j) with
  | false => rfl
  | true => exact absurd (checkCert_sound hh hwf) (not_qEquiv_four_even m j hm hj)

/-- **The general obstruction at the checker level**: for even `m`, `k ≥ 3` and `k ∣ 2 j`,
no admissible `Q**` certificate joins `metz k m 1` and `metz k m j`. -/
theorem not_qEquiv_general (k m j : Nat) (hk : 3 ≤ k) (hm : Even m) (hdvd : k ∣ 2 * j) :
    ¬ QEquiv (metzQ k m 1) (metzQ k m j) :=
  MetzlerSharp.not_mulEquiv_dihedral k m j hk hm hdvd

/-- The checker corollary in the general family. -/
theorem no_checkCert_general (k m j : Nat) (hk : 3 ≤ k) (hm : Even m) (hdvd : k ∣ 2 * j)
    (ms : List QMove) (hwf : CheckWF ms = true) :
    checkCert ms (metzQ k m 1) (metzQ k m j) = false := by
  cases hh : checkCert ms (metzQ k m 1) (metzQ k m j) with
  | false => rfl
  | true => exact absurd (checkCert_sound hh hwf) (not_qEquiv_general k m j hk hm hdvd)

/-- The 7-move shift of `MetzlerShift.lean`, in `AC5`'s certificate format. -/
def shiftMsAC5 (C : List (Nat × Bool)) : List QMove :=
  [.conj 1 C, .mul 1 2, .inv 2, .conj 2 [(1, true)], .mul 1 2, .conj 2 [(1, false)], .inv 2]

/-- The checker accepts the shift `(4,2,1) -> (4,2,5)` (`x^4` written as its four letters):
`j = 5` is outside the recipe's hypothesis at `k = 4` (`5 ∤ 3`) and yet is reachable, so the
recipe's hypothesis is not necessary. -/
theorem checkCert_shift_four_two_one_five :
    checkCert (shiftMsAC5 [(0, true), (0, true), (0, true), (0, true)])
      (metzQ 4 2 1) (metzQ 4 2 5) = true := by decide

/-- One further shift: `(4,2,5) -> (4,2,9)`, again accepted by the checker. -/
theorem checkCert_shift_four_two_five_nine :
    checkCert (shiftMsAC5 [(0, true), (0, true), (0, true), (0, true)])
      (metzQ 4 2 5) (metzQ 4 2 9) = true := by decide

/- Axiom audit. -/
#print axioms metzQ_rels_eq
#print axioms not_qEquiv_four_two_two
#print axioms not_qEquiv_four_even
#print axioms no_checkCert_four_two_two
#print axioms no_certificate_four_two_two
#print axioms no_checkCert_four_even
#print axioms checkCert_shift_four_two_one_five
#print axioms checkCert_shift_four_two_five_nine
#print axioms not_qEquiv_general
#print axioms no_checkCert_general

end MetzlerSharpBridge
