# The stage-2 move sequence for symbolic `t, j`: where the formalization stops

This is the record of an attempt made after the main deliverable (`AC7.lean`) was already
verified. It did **not** succeed. The point is recorded because the remaining gap between round 6's
`[Argument, with 14 instances Verified]` and a kernel theorem for all parameters is here, and the
obstacle is technical rather than conceptual.

## What was attempted

A theorem of the shape

```
theorem powerMoves_spec (t : Nat) (j : Nat) (V : FreeGroup (Fin 3)) :
    replay (powerMoves t j) (pstate t V) = some (pstate t (V * powerProd3 t j))
```

with `pstate t V = ⟨3, 2, fun i => if i = 0 then V else A3 * X3 ^ (-(t:ℤ))⟩` (relator 0 is the one
being multiplied, relator 1 is the defining relator `a x⁻ᵗ`),
`factorMoves t i = [.conj 1 (replicate (t*i) (0,false)), .mul 0 1, .conj 1 (replicate (t*i) (0,true))]`
and `powerMoves t (j+1) = factorMoves t (j+1) ++ powerMoves t j`. The induction itself is available
and was written: after one factor the relator is `V * (x⁻ᵗⁱ (a x⁻ᵗ) xᵗⁱ)` and the defining relator is
restored, so the induction hypothesis applies with `V` replaced by `V * (x⁻ᵗⁱ(a x⁻ᵗ)xᵗⁱ)`; the word
identity that closes it is `cfac_eq`, which is `powerProd_cert` rearranged.

## The exact point of failure

Once the permutations of the state are written with `setRel`, Lean gives

```
error: Tactic `rfl` failed: The left-hand side
  some { n := (step2 t i V).n, m := (step2 t i V).m, rels := fun k => if k = ⟨1,·⟩ then … else … }
is not definitionally equal to the right-hand side
  some { n := 3, m := 2, rels := fun k => if k = ⟨1,·⟩ then … else … }
```

`setRel P i v` is `⟨P.n, P.m, fun k => if k = i then v else P.rels k⟩`, so a state produced by a move
carries `P.n` and `P.m` as *projections* of the previous state, while a state written down as a
structure literal carries the numerals `3` and `2`. The two `QPres` values are propositionally equal
(`(pstate t V).n` reduces to `3` by unfolding the definition) but not *syntactically* equal, and that
matters twice:

* the `if k = ⟨1, …⟩` in `setRel` is an `ite` over `Fin P.m`, and the `DecidableEq (Fin P.m)`
  instance in the two states is not the same term, so the `ite`s do not line up definitionally;
* `setRel`'s third argument has type `Word P.n`, so a product that mixes a rank-3 word (`x ^ (-(t*i))`)
  with a relator of the moved state needs `HMul (FreeGroup (Fin 3)) (FreeGroup (Fin (step2 …).n))`,
  and instance synthesis does not close that up to defeq either.

Three workarounds were tried and each only moved the failure one step: ascribing the relators to
`FreeGroup (Fin 3)`, defining a rank-generic `xpow {n} (h : 0 < n) (k : ℤ) : FreeGroup (Fin n)`, and
defining the intermediate states explicitly as structure literals. With the third, the two `apply`
steps for `.conj` and the step for `.mul` go through (they are proved, `apply_conj` and `apply_mul` in
the attempt below), and the failure lands on `step3_apply`'s `rfl` with the error above. The clean
route, which I did not have the budget to complete, is to state the theorem directly about the
`setRel` terms that `apply` produces and to prove a single extensionality lemma at the end
(`QPres.n`, `QPres.m` and `QPres.rels` componentwise) rather than trying to make the two
presentations of each state definitionally identical.

## File

`stage2_attempt.lean.txt` is the last attempt, kept as evidence. **It does not compile** (it has
errors at the `step3_apply` `rfl`, and `sorry`s in the parts that were never reached). It is not part
of the deliverable and must not be read as a proof of anything. The verified deliverable is
`AC7.lean`; the kernel content it has for all parameters is the algebra (`conjProd_of_subst`,
`powerProd_spec`, `powerProd_cert`, `powerProd_factor_is_conj`, `subst_defining`).
