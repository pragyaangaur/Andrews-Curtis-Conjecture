# The Metzler certificate and the family of 14, in the Lean 4 kernel

Round 7, direction **J5**. Member m10. Files in `.ultramath/smw48or9f/m10/`.

Labels: **[Verified]** a machine check anyone can rerun with the stated command; **[Computed]** a
number from a stated run; **[Argument]** a proof written out but not machine-checked; **[Quoted]**
taken from a source, not replayed; **[Open]** not settled here.

Nothing in this file is a claim for or against the Andrews-Curtis conjecture. Both presentations of
Metzler's pair present the abelian group $\mathbb{Z}/5\times\mathbb{Z}/5$, not the trivial group.

## 0. Summary

1. **[Verified] Round 6's 44-move Q\*\*-certificate for Metzler's pair, and the 14 certificates of
   its family, are now checked in the Lean 4 kernel.** `AC7.lean` replays all 15 certificates
   (788 Q\*\*-moves, 394 block decisions) and proves, for each, the reached endpoint, the
   identification of the endpoints with the presentations
   $\langle x,y \mid x^k, y^m, [x^j,y]\rangle$, and the Q\*\*-equivalence itself as an existential
   over move lists. `lean AC7.lean` exits 0; 40 `#print axioms` lines, every one inside Lean's
   standard set `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `native_decide`.
2. **[Verified] An independent replayer, written from Barmak's move list, confirms all 15
   certificates** (`replay7.py`, 15 of 15, 0 failures), and recomputes round 6's length claims:
   Metzler's certificate is 44 moves, its peak total relator length is **26**, its longest relator
   15; the per-row longest relators of round 6's table are reproduced in all 14 rows.
3. **[Verified] The algebra of the recipe is in the kernel for all parameters, not only the 14
   instances**: round 6's Lemma 3 in product form for every word (`conjProd_of_subst`,
   `conjProd_of_lift`), and the closed-form telescoping identity behind stage 2 for every
   $t,j$ (`powerProd_spec`, `powerProd_cert`, `powerProd_factor_is_conj`), plus the substitution
   identity of stage 3 (`subst_defining`).
4. **[Verified, correction] Round 6's proof sketch of the family has the inverse in the wrong
   place.** `directions/qdouble-star/m9/round6-m6.md` section 5 prints the multiplier as
   $(x^{-tj}a^j)^{-1}$; the identity that holds, and that the certificate uses, is
   $x^k\cdot x^{-tj}a^j = x a^j$ with $k=1+tj$. Checked by exact free-group arithmetic in 36 of 36
   cases $(1\le t,j\le 6)$ for the corrected form and **0 of 36** for the printed one. The kernel
   theorem `powerProd_cert` states the corrected form. This does not affect any of round 6's
   certificates, which are correct as files; it is an error in the prose proof only.
5. **[Verified] The kernel is not vacuous here.** Two one-letter tamperings of a copy of `AC7.lean`
   — a shortened conjugator in a move, and a wrong end tuple — are both rejected, by different
   theorems (`tamper_test.sh`, section 2.5).
6. **[Open] Not formalized: the recipe as one theorem over symbolic $k,t,j,m$.** What is missing is
   the composition of the recipe's move lists with symbolic relators; see section 6 for the exact
   point where that stops.

## 1. Files

| file | what it is |
| --- | --- |
| `AC7.lean` | 5,021 lines. AC5's Q\*\* machinery (namespace renamed `AC7`), the 15 certificates, the endpoint identifications, the family table, the algebra of the recipe. |
| `gen_ac7.py` | generates `AC7.lean` from `AC5.lean` plus `certs/*.cert`; records the exact line range copied from AC5 (lines 31–287) |
| `replay7.py` | this member's own Q\*\* replayer, written from Barmak's move list; shares no code with `metzler_gen.py`, `qverify.py`, `check_qstar.py` or the round-5 certificate algebra |
| `verify_claims.py` | certificate statistics (peak total relator length), the power identity check, round 6's table compared row for row, and the move census |
| `tamper_test.sh` | the negative controls of section 2.5: two one-letter tamperings of a copy of `AC7.lean`, both of which must be rejected |
| `check_ac7.sh` | runs the checks end to end: the kernel run with the axiom audit, my replayer, `verify_claims.py`, and the campaign's two replayers |
| `groupcheck.g` | GAP: the 14 pairs of presentations present the same abelian group |
| `certs/` | the 15 certificate files, byte copies of `directions/qdouble-star/m9/certs/metzler_pair_qstar_gap.cert` and `directions/qdouble-star/m9/fam_certs/fam_*.cert` (sha256 in section 2.4); `cmp` clean against the originals |
| `AC5.lean` | a byte copy of `toolkit/lean/AC5.lean`, the input of `gen_ac7.py` (`cmp` clean), so the machinery copy is reproducible from this directory alone |
| `stage2_attempt.md`, `stage2_attempt.lean.txt` | the record of the unfinished extension to symbolic parameters; the `.txt` does **not** compile and is not part of the deliverable |

`gen_ac7.py` is deterministic: `BLOCK=2 python3 gen_ac7.py X.lean; cmp X.lean AC7.lean` is clean, so
the file can be regenerated from `AC5.lean` and `certs/` and compared byte for byte.

**Install (the coordinator's step; I did not write outside my directory):**

```
cp .ultramath/smw48or9f/m10/AC7.lean toolkit/lean/AC7.lean
```

`AC7.lean` imports only `Mathlib.Data.Fintype.Basic`, `Mathlib.GroupTheory.FreeGroup.Reduce`,
`Mathlib.GroupTheory.Commutator.Basic` and `Mathlib.Tactic.Group`, not all of Mathlib: the AC5
machinery needs exactly these, and the smaller import is what makes the check cheap — peak resident
memory 1.9 GB instead of the 5.1 GB that `import Mathlib` alone costs on this VM, and 1.5 minutes
instead of 4 to 8. This is the one respect in which AC7 differs from AC5/AC6 beyond its content; the
machinery itself is AC5's, copied mechanically (the generator prints the line range).

## 2. The checks, and their output

All commands are run from `.ultramath/smw48or9f/m10/`. The script does all four steps:

```
$ ./check_ac7.sh
== 1. lean AC7.lean
lean exit status: 0   (log: .../ac7.run.log)
axiom lines: 40 (expected 40: 15 certificates + 15 equivalences + family_table + 9 algebra)
axiom lines mentioning neither propext nor Quot.sound: 0 (expected 0)
sorryAx / native_decide mentions: 0 (expected 0)
== 2. python3 replay7.py certs/*.cert (independent replayer)
certificates checked = 15, failures = 0
== 3. python3 verify_claims.py
highest peak total relator length: 58 (fam_k13_t2_m5.cert)
t, j in 1..6: corrected identity holds in all 36 cases: yes
printed formula x^k (x^-tj a^j)^-1 = x a^j holds in: 0 of 36 cases
worked instance t=2 j=2: x^5 * x^-4 a^2 = x a^2, i.e. (1, 3, 3)
rows matching: 13 of 13
  44 moves: conj 13, delete 1, inv 9, lmul 4, mul 8, neg 1, nij 1, nijinv 5, njiinv 1, prolong 1
== 4. the campaign's own replayers on the same 15 files (if present)
checked 15, failures 0
certificates checked = 15, failures = 0
ALL CHECKS PASS
```

The two lines of step 4 are `qverify.py` (round 4) and `check_qstar.py` (round 3).

Wall clock for the whole script was 1 min 36 s at load average about 10 on 4 CPUs and 7 min 30 s at
load average 16 (31 to 42 s of user time in the Lean run; the rest is waiting for a CPU). Peak
resident memory of the Lean run: 1.9 GB.

### 2.1 the kernel content

`lean AC7.lean` proves, for every certificate file, three things: the replay reaches the recorded
end tuple (`*_replay`, `*_checked`), the endpoints are the presentations of the statement
(`*_endpoints`, a `decide`-checked equation against `metz k m j`), and the equivalence as an
existential over move lists (`*_qstar_equiv`). The block structure follows AC5: blocks of at most
two moves, glued with `replay_concat`, one `decide` per block.

Then `family_table` states round 6's 14 rows as 14 conjoined existentials over the presentations
`metz k m j = <x,y | x^k, y^m, [x^j,y]>`, each discharged by the corresponding certificate. The
three `j = 1` rows are trivial statements (both presentations are `metz k m 1`); they are in round
6's table because the recipe produces a certificate there too, and the kernel checks that
certificate as well. The 15th certificate, `fam_k5_t2_m5`, is move-for-move Metzler's own
(`diff` of the two move lists is empty), so round 6's 14 rows correspond to 15 certificates.

### 2.2 the algebra

These are theorems about all parameters, not instances:

* `ConjProd` — the inductive predicate "is a finite product of conjugates of $R$ and $R^{-1}$",
  with closure under conjugation, multiplication and inverse, and membership in the normal closure
  of $R$ (`conjProd_mem_normalClosure`). This is the form a Q-multiplication by conjugates of one
  relator has, and it is exactly what Lemma 1 of round 6 says a single Q-move can supply.
* `conjProd_of_subst` — **round 6's Lemma 3**, for every word $V$: if $\sigma$ carries the
  generator $x$ to $W^{-1}$ and fixes the other generators, then $V\cdot(\sigma V)^{-1}$ is a
  product of conjugates of $R = xW$. `conjProd_of_lift` is the same with the endomorphism written
  as `FreeGroup.lift` and its two hypotheses discharged, so the statement needs no side conditions.
* `powerProd_spec`, `powerProd_cert`, `powerProd_factor_is_conj` — the closed form of stage 2:
  the product of $j$ conjugates of the defining relator $a x^{-t}$ is $x^{-tj}a^j$, hence
  $x^{1+tj}$ times it is $x a^j$, and every factor is a conjugate of $a x^{-t}$.
* `subst_defining` — the substitution $x\mapsto a^{-j}$ of stage 3 carries $a x^{-t}$ to
  $a^{1+tj}$.

### 2.3 certificate statistics (round 6's length claims recomputed)

```
certificate                   moves peak total  longest  endpoint
fam_k11_t2_m5                    56         50       27  <2 | 2 xxxxxxxxxxx;yyyyy;xxxxxyXXXXXY>
fam_k11_t5_m5                    56         37       22  <2 | 2 xxxxxxxxxxx;yyyyy;xxyXXY>
fam_k13_t2_m5                    60         58       31  <2 | 2 xxxxxxxxxxxxx;yyyyy;xxxxxxyXXXXXXY>
fam_k13_t4_m7                    56         47       27  <2 | 2 xxxxxxxxxxxxx;yyyyyyy;xxxyXXXY>
fam_k5_t1_m5                     48         38       23  <2 | 2 xxxxx;yyyyy;xxxxyXXXXY>
fam_k5_t2_m5                     44         26       15  <2 | 2 xxxxx;yyyyy;xxyXXY>
fam_k5_t4_m3                     48         22       11  <2 | 2 xxxxx;yyy;xyXY>
fam_k7_t1_m4                     56         51       30  <2 | 2 xxxxxxx;yyyy;xxxxxxyXXXXXXY>
fam_k7_t2_m2                     48         31       16  <2 | 2 xxxxxxx;yy;xxxyXXXY>
fam_k7_t3_m5                     48         29       17  <2 | 2 xxxxxxx;yyyyy;xxyXXY>
fam_k7_t6_m1                     56         26       14  <2 | 2 xxxxxxx;y;xyXY>
fam_k9_t2_m5                     52         42       23  <2 | 2 xxxxxxxxx;yyyyy;xxxxyXXXXY>
fam_k9_t4_m3                     52         31       18  <2 | 2 xxxxxxxxx;yyy;xxyXXY>
fam_k9_t8_m2                     64         33       18  <2 | 2 xxxxxxxxx;yy;xyXY>
metzler_pair_qstar_gap           44         26       15  <2 | 2 xxxxx;yyyyy;xxyXXY>
```

Round 6 says Metzler's certificate has 44 moves, longest relator 15, peak total length 26, start
length 14 — reproduced. Its move census (prolong 1, nijinv 5, nij 1, njiinv 1, neg 1, conj 13,
mul 8, lmul 4, inv 9, delete 1) is reproduced exactly. Its table of 14 rows gives a "peak relator
length" column; `python3 verify_claims.py --table` parses that table out of
`directions/qdouble-star/m9/round6-m6.md` and compares it row for row with the recomputation: all
13 family rows match on both the move count and the longest relator; the 14th row of the table is
Metzler's own, matched separately (44 moves, longest 15). The highest peak *total* length over all
15 paths is 58, not 26 — 26 is Metzler's own.

### 2.4 the certificate files

```
$ sha256sum certs/metzler_pair_qstar_gap.cert
10566d02f2dec919695414e39bb9c4c3045599f7d85a123e0eb0edbef4d9bd63
```
which is the value round 6 records for its certificate. The 14 family files are byte copies of
`directions/qdouble-star/m9/fam_certs/*.cert` (`cmp` clean).

### 2.5 negative controls: the kernel rejects a tampered certificate

`./tamper_test.sh` rewrites two things in a copy of `AC7.lean`, one letter each, and runs Lean on
each copy:

```
$ ./tamper_test.sh
wrote the two tampered files
== tampering: tamper_move
   lean exit status: 1, error lines: 1
   .../tamper_move.lean:436:114: error: Tactic `decide` proved that the proposition
== tampering: tamper_end
   lean exit status: 1, error lines: 2
   .../tamper_end.lean:574:18: error: Tactic `decide` proved that the proposition
   .../tamper_end.lean:583:45: error: Type mismatch
BOTH TAMPERINGS CAUGHT
```

The two tamperings are (1) the conjugating word of the second move of block 2 of Metzler's
certificate, `x⁻⁴` shortened to `x⁻³`: the block theorem `ac7_metzler_pair_qstar_gap_b2` fails, and
downstream the equivalence theorem acquires `sorryAx` in its axiom list, which is visible in the
same log; (2) the last relator of the end tuple, `x²yx⁻²y⁻¹` with one `x` dropped: both the replay
theorem and the endpoint identification fail, i.e. the two kernel checks are independent in the way
they should be. So the checker is not vacuous: it is not a function that returns `true`.

### 2.6 the group orders

`gap -q -b groupcheck.g` prints, for all 14 rows, the order and abelian-ness of the start and the
end presentation: 25/25, 25/25, 15/15, 35/35, 14/14, 28/28, 7/7, 45/45, 27/27, 18/18, 55/55,
55/55, 65/65, 91/91, all abelian, start = end in every row. This matches round 6's GAP spot checks
(k = 5, m = 5 gives 25; 7,5 gives 35; 9,5 gives 45; 13,7 gives 91; 5,3 gives 15) and extends them
to all 14 rows.

## 3. The correction to round 6's proof sketch

`directions/qdouble-star/m9/round6-m6.md`, section 5, derives the family as follows:

> Then $x^k = x\,(x^t)^j$, so
> $x^k \cdot (x^{-tj}a^j)^{-1} = x\,(x^t)^j x^{-tj} a^j = x a^j$

The value of $(x^{-tj}a^j)^{-1}$ is $a^{-j}x^{tj}$, so the left-hand side is
$x^{1+tj}a^{-j}x^{tj}$, which is not $x a^j$; the second equality is wrong. The identity that is
true, and that the certificates implement, is

$$x^{1+tj}\cdot x^{-tj}a^j = x\,a^j,$$

and $x^{-tj}a^j$ is the product of the $j$ conjugates
$\prod_{i=j}^{1} x^{-ti}\,(a x^{-t})\,x^{ti}$ of the defining relator. `verify_claims.py` checks
both forms by exact free-group arithmetic for $1\le t,j\le 6$: the corrected identity holds in
36 of 36 cases, the printed one in 0 of 36. The kernel theorem `powerProd_cert` states the
corrected form for all $t,j$.

Scope of the correction: it is in the prose of the proof sketch only. Every certificate file
replays (15 of 15, and the kernel agrees), and round 6's conclusions about the family stand.

## 4. What I verified, and how

* **[Verified]** `lean AC7.lean` from `.ultramath/smw48or9f/m10/`: exit 0, 40 axiom lines, all in
  `[propext, Classical.choice, Quot.sound]`, no `sorry`, no `native_decide`. This is an
  independent transcription in a different system from round 6's five Python replayers and GAP: the
  file was generated from the certificate files by `gen_ac7.py`, and every move is checked by the
  kernel's own evaluation of `QMove.apply`.
* **[Verified]** `python3 replay7.py certs/*.cert`: 15 certificates, 0 failures. My replayer was
  written from Barmak's move list before reading any of the campaign's replayers, and it agrees
  with all of them on all 15 files: `qverify.py` (round 4) prints `checked 15, failures 0` and
  `check_qstar.py` (round 3) prints `certificates checked = 15, failures = 0` on the same files
  (`./check_ac7.sh` runs both as its step 4); it also agrees with the kernel, which is a third independent
  implementation of the same move set (the kernel's `QMove.apply` is AC5's, so this is a
  cross-check between the campaign's Lean move set and its Python move sets at these 15 paths).
* **[Verified]** the statistics of section 2.3 and the peak-26 claim, the endpoint identifications
  (`decide`), and the family table.
* **[Verified]** the algebra theorems of section 2.2, as kernel theorems with no hypotheses beyond
  the ones stated.
* **[Argument, not machine-checked]** round 6's Lemma 1 (a single Q-move never multiplies a relator
  by a conjugate of *itself*) and Lemma 2 (no Q-certificate keeps $x^5$ and $y^5$ fixed). I did not
  formalize either; see section 6.
* **[Quoted, not replayed]** Barmak's quotation of Metzler's 1976 Q\*-inequivalence, and the
  attribution of the example. Nothing here bears on Q\*-inequivalence, and nothing on the
  Andrews-Curtis conjecture.

## 5. What I could not verify

* **Q\*-inequivalence of Metzler's pair.** Quoted from Barmak, citing Metzler 1976; I did not
  reproduce an invariant. The certificate found here needs prolongation and its inverse, so it is
  not a Q\* certificate, but that proves nothing.
* **The general recipe as a single kernel theorem over $(k,t,j,m)$.** Section 6.
* **Barmak's other pair** ($\langle x,y\mid [x,y],1\rangle$ against Fernandez's presentation) is
  untouched: it is not of the shape this technique handles.
* **Three of round 6's five replayers were not run by me**: `metzler_gen.py`, the round-5
  certificate algebra, and round 6's GAP script. I ran my own replayer, `qverify.py`,
  `check_qstar.py` and the kernel — four implementations — on the same 15 files. The GAP run here
  is a different script of mine (`groupcheck.g`), which checks group orders, not the moves.

## 6. The gap, exactly

Round 6 states the family as an **[Argument, with 14 instances Verified]**. That is still the
status after this work, sharpened: the *algebra* of the recipe is now a theorem for all parameters,
and the *move lists* are kernel-checked for the 15 files; what is not formalized is the statement

> for every odd $k\ge 3$, every $m\ge 1$ and every $t\mid k-1$ with $j=(k-1)/t$, the recipe's move
> list replays from $\langle x,y\mid x^k,y^m,[x,y]\rangle$ to $\langle x,y\mid x^k,y^m,[x^j,y]\rangle$.

The obstruction is structural rather than conceptual: `replay` is a function on *concrete* letter
lists, and the recipe's letter lists have length $t$, $k-1$, $tj$ — symbolic. A proof would have to
(a) compute the state after each stage as a `QPres` whose relators are symbolic words, which means
proving equalities of `QPres` values by extensionality over `Fin m` and then group identities, and
(b) compose up to $k$ blocks, which needs an induction in which the relator being multiplied is a
parameter `V` (the identity `V * (x^{-ti}a x^{t(i-1)}) * powerProd t (i-1)` does telescope, so the
induction is available — the work is in (a), the `QMove.apply` unfolding of `conj`/`mul` at
symbolic words with `mkWordOpt` of `List.replicate`). What is done here is the algebra side of it:
`powerProd_cert` is exactly the word identity the induction would use, and `conjProd_of_subst` is
the whole of Lemma 3 in the form the composition consumes.

I attempted this after the main deliverable was verified and did not finish it. The obstacle is
recorded exactly in `stage2_attempt.md`, with the last attempt kept as `stage2_attempt.lean.txt`
(it does not compile; it is not part of the deliverable). In one sentence: `setRel P i v` keeps
`P.n` and `P.m` as *projections*, so a state produced by a move and the same state written as a
structure literal `⟨3, 2, ·⟩` are propositionally but not syntactically equal, and the `ite` over
`Fin P.m` and the `HMul` at rank `P.n` both refuse the defeq step. The three `.apply` steps up to
that point are proved (`apply_conj`, `apply_mul`), and the failure lands on `step3_apply`'s `rfl`.
The clean route is to state the theorem about the `setRel` terms that `apply` produces and to
separate the extensionality collapse into one lemma; I did not have the calls left to finish it, and
I preferred to submit a verified partial result over an unverified whole.

## 7. Nothing about the conjecture

Both presentations present $\mathbb{Z}/5\times\mathbb{Z}/5$ (section 2.6), so the Q\*\*-equivalence
proved here is a statement about the coarseness of the move calculus, not about
$\langle x,y\mid x,y\rangle$. No claim for or against the Andrews-Curtis conjecture is made.
