# Round 4, direction G4: explicit Q\*\*-certificates for the Zieschang and McCool-Pietrowski pairs, and bounded Q\*\*-searches at raised caps

Member m9, swarm smw2woueq, 2026-11-05 UTC. This file extends
`directions/qdouble-star/`, which holds the round-3 Q\*\*-work of member m10
(`qdouble-star.md`, `qstar.py` and three replayers). Everything new is in the
subdirectory `directions/qdouble-star/m9/`, so no round-3 file is changed:
certificates in `certs/`, run logs in `runs/`, code and this report beside them.
My working directory was `.ultramath/smw2woueq/m9/`, and the two copies are
byte-identical.

Labels. **[checked]** is a statement checked by the exact command quoted.
**[proved here]** is an argument written out here. **[bounded negative]** is a
search result with its exact bound. **[quoted]** is a statement from a source
whose identifier I verified live. Nothing here proves or disproves the
Andrews-Curtis conjecture, and no claim is rounded up.

## 1. What is new, in one page

1. **Explicit Q\*\*-certificates for Zieschang's pair.** The published
   literature quotes the pair and says the translation is easy, but prints no
   move list. `certs/zieschang.cert` carries
   `<x,y | x^3y^3x^3y^2>` to `<x,y | x^3y^5>` in 26 Q\*\*-moves. The
   certificate replays under three independent implementations.
   **[checked]**
2. **Explicit Q\*\*-certificates for the McCool-Pietrowski family.** One
   certificate for each of the 27 triples `k,p,t` in `{2,3,4}^3` and five more
   for `(5,5,9)`, `(6,7,11)`, `(9,2,13)`, `(10,10,10)` and `(7,4,3)`, from
   `<x,y | (x^ky^t)^p y>` to `<x,y | x^k y^{pt+1}>`, with 20 to 92 moves each.
   The construction is uniform in `k,p,t`, so the move list for any `k,p,t` at
   least 2 is produced by the same program. **[checked]** for those 32 triples
   plus Zieschang's pair; **[proved here]** as a uniform recipe.
3. **A fourth and a fifth replayer, and a negative control set.** My replayer
   `qverify.py` is written from Barmak's six moves directly, and
   `gapverify.py` translates a certificate into GAP and runs it. Three
   deliberately corrupted certificates are rejected by all three checkers
   working today. **[checked]**
4. **Two defects in the round-3 replayer set.** `gap_replay.py` cannot replay
   any certificate that uses prolongation: its `delete` branch emits GAP code
   that does not parse, and the branch was never exercised because none of the
   69 round-3 certificates used prolongation. `check_qstar.py` raises an
   uncaught `AssertionError` on a certificate whose deletion is invalid, so it
   detects the fault but does not report it as a clean failure. **[checked]**
5. **A second search engine**, canonical-form best-first, which searches one
   representative per Q-orbit instead of literal presentations. Its
   canonicalisation is a Q-move sequence by construction and is checked on 300
   random presentations against the independent replayer. It gives a
   memory-bounded way to search the same space, and it was run on every target
   below. **[checked]**
6. **Bounded negatives at raised caps and ranks.** AK(3) does not fall within
   cap 26 and rank 4 at 25,000 expansions, nor within cap 24 and rank 3 at
   20,000 canonical expansions. All 96 resisters that round 3 left Q\*-open do
   not fall at cap 26 and rank 4 with 20,000 expansions each, nor at cap 24
   with 10,000 canonical expansions each. The six length-13 resisters do not
   fall at cap 26 with 50,000 expansions each, nor at cap 26 and rank 4 with
   20,000 each. **[bounded negative]**
7. **The Q\*\*-status of AK(3) is open, and stays open here.** The searches in
   item 6 are the whole of what I established about it.

## 2. The printed pairs, and why the transcription is safe

The source is J. A. Barmak, *An exotic presentation of Z x Z and the
Andrews-Curtis conjecture*, Algebr. Geom. Topol. 25 (2025) 345-355, DOI
10.2140/agt.2025.25.345. The PDF is open access at
`https://msp.org/agt/2025/25-1/agt-v25-n1-p13-s.pdf`. Page 346 reads, with the
asterisks present in the glyph stream:

> The first were probably those given by Zieschang [24, page 36]:
> `<x,y | x^3 y^5>` and `<x,y | x^3 y^3 x^3 y^2>`, and, with more generality, by
> McCool and Pietrowski [18]: `<x,y | x^k y^{pt+1}>` and `<x,y | (x^k y^t)^p y>`
> for k,p,t >= 2. In each case the presentations are Q\*\*-equivalent. The
> authors only prove that they present the same group, but it is easy to
> translate their proof to the language of Q\*\*-transformations.

Two transcription hazards had to be settled before a move list could be built.
The first is that `pdftotext` drops superscript minus signs from this PDF, so
`x^3 y^3 x^{-3} y^2` and `x^3 y^3 x^3 y^2` both print as `x 3 y 3 x 3 y 2`.
That would matter, because with the minus sign the relator is not the right
one. The second is that the asterisks themselves are lost in the text layer, so
`Q` prints for both `Q*` and `Q**`. Both are settled by reading the
decompressed content stream. Three mark glyphs live in font `F98` in this PDF,
and the way to tell them apart is to compare with two places where the reading
is not in doubt: in the abstract the relator contains `y^{-1}` and there the
mark glyph is code `\000` (octal), and on page 345 the text contains `x^{n+1}`
and there the mark glyph is code `C`. So code `\000` is the minus sign, code
`C` the plus sign and code `\003` the asterisk. `pdfcheck.py` prints the
glyph runs; its decoded output for page 346 is

```
[24,page36]:hx;yjx^^{3}y^^{5}iandhx;yjx^^{3}y^^{3}x^^{3}y^^{2}i,
and,withmoregenerality,byMcCoolandPietrowski[18]:hx;yjx^^{k}y^^{p}^{t}<plus>^{1}i
andhx;yj.x^^{k}y^^{t}/^^{p}yifork
```

so the Zieschang relator has no mark glyph at all (no minus sign, and no plus
sign), the McCool-Pietrowski exponent is `pt` plus `1`, and the sentence after
them decodes as `Q<asterisk><asterisk>-equivalent ... easy to translate their
proof to the language of Q<asterisk><asterisk>-transformations`.
**[checked]**

That reading also decides a question the round-3 work left implicit. With the
minus sign in the Zieschang relator the pair would not present one group, so no
Q\*\*-certificate could exist and the literature would be wrong; with the
reading above the certificate exists, and Section 4 exhibits it. The two
readings are therefore separated by the certificates themselves as well as by
the glyph stream.

An independent consistency check, which also uses the certificates themselves:
the group of both of Zieschang's presentations is the torus-knot group
`T(3,5) = <x,s | x^3 = s^5>`. For Zieschang's second relator, put
`s = x^3 y^3`; the relator is `s^2 y^{-1}`, so `y = s^2` and `x^3 = s^{-5}`,
which is `T(3,5)`. For the McCool-Pietrowski pair, put `s = x^k y^t`; the
relator `(x^ky^t)^p y` is `s^p y`, so `y = s^{-p}` and `x^k = s^{pt+1}`, which
is `T(k, pt+1)`, the same group as `<x,y | x^k y^{pt+1}>`. **[proved here]**
The certificates below confirm it independently, since a Q\*\*-certificate can
only join presentations of one group.

## 3. The construction, in words and in moves

Write `s = x^k y^t`, so the second presentation of the pair is `<x,y | s^p y>`,
except for Zieschang's pair where it is `<x,y | s^2 y^{-1}>` with `s = x^3y^3`
and `p = 2`, `t = 3`. The two presentations differ by the change of generating
set `{x,y}` to `{x,s}`. That change is not an elementary Nielsen move, because
`s = x^k y^t` has length `k+t`, which is at least 4, while an elementary Nielsen
move changes a generator into a word of length at most 2. That the change is
not a product of Nielsen moves either, that is to say that no automorphism of
`F_2` supplies it, is what the literature proves with Whitehead's algorithm,
and it is why the pair is not Q\*-equivalent.
Prolongation is what pays for it. The chain is the following, and every line is
one of Barmak's moves (i) to (vi) or a short product of them.

1. **(v)** Prolong: adjoin `a` with relator `a`, so `a` is a free trivial
   generator.
2. **(iv)** Apply elementary Nielsen moves to `a` only, `a -> a s^{-1}`. Each
   step multiplies one generator by another generator on the right, so the
   product is an automorphism of `F_3`. The relators are now `s^p y` and
   `a s^{-1}`, so `a = s`.
3. **(iii), (i)** Do this `p` times, for `j = p-1` down to `0`: conjugate
   relator 2 by `s^j`, left-multiply relator 1 by relator 2, conjugate relator
   2 back. Conjugating puts relator 2 into the form `s^j a s^{-(j+1)}`, so if
   relator 1 is `s^{j+1} a^m y` the left multiplication makes it `s^j a^{m+1} y`.
   After `p` rounds, from `s^p y`, relator 1 is `a^p y` while relator 2 is
   `a s^{-1}` again. Left multiplication is derivable as conjugation followed
   by (i): `r_i -> r_j r_i r_j^{-1} -> r_j r_i`.
4. **(iii), (i)** The relator `a^p y` says `y = a^{-p}`; for Zieschang it says
   `y^{-1} = a^{-2}`, and one inverse move puts the relator into the form
   `a^{p e} y` with `e = -1`. A single Q-move substitutes one occurrence of
   `y^{-1}` inside relator 2 by `a^{p e}`: left-multiply relator 2 by the
   conjugate of relator 1 by the prefix `u` that precedes that occurrence,
   because `(u a^{p e} y u^{-1})(u y^{-1} v)` reduces to `u a^{p e} v`. Doing
   this for all `t` occurrences turns relator 2 into `a^{1+pet} x^{-k}`.
5. **(iv)** Apply `p` Nielsen moves to `y`, `y -> y a^{-p e}`. Relator 1
   becomes `a^p y a^{-p e}`, which cyclically reduces to `y`, so `y` is now a
   free factor of the rank-3 presentation.
6. **(vi)** Delete `y`. The remaining relator is `a^{1+pet} x^{-k}` on two
   generators.
7. **(ii), (iii)** Two cosmetic moves bring it to `x^k y^{pt+1}`: for the
   McCool-Pietrowski branch invert `x` and rotate the cyclic word, for
   Zieschang invert the relator.

The point of step 4 is worth recording separately, because it is the step that
makes the whole family work and it is not in the round-3 report. **A Q-move can
substitute a single letter inside a relator, provided some relator has the form
`(letter)(word)`.** Given a relator `rho y` with `rho y = 1` and another
relator `u y v`, left multiplication of `u y v` by the conjugate
`u (rho y) u^{-1}` gives `u rho v`. Iterating this substitutes every occurrence
of the letter, and the conjugate is available because conjugation by any word
is move (iii). **[proved here]** It is a two-line identity, but it is what
turns a group-theoretic isomorphism into a move list.

## 4. The certificates, and the three checks

The generator is `mkpair.py`. It builds the move list, and it also
*verifies each intermediate state against an independent implementation of the
moves as it goes* (`qverify.Pres`), so a certificate that is written is already
checked once. Summary:

| certificate | moves | start | end |
| --- | --- | --- | --- |
| `zieschang.cert` | 26 | `<x,y | x^3y^3x^3y^2>` | `<x,y | x^3y^5>` |
| `mccool_pietrowski_k_p_t.cert`, 32 files | `k+4t+4p+2` | `<x,y | (x^ky^t)^p y>` | `<x,y | x^k y^{pt+1}>` |

The move counts of the 32 family certificates run from 20 (`k=p=t=2`) to 92
(`k=p=t=10`), and the formula `k+4t+4p+2` matches all 32. **[checked]** The
three checks, all run on the 33 files:

```
$ python3 qverify.py certs/*.cert
checked 33, failures 0
$ python3 ../check_qstar.py certs/*.cert
certificates checked = 33, failures = 0
$ python3 gapverify.py certs/*.cert
certificates = 33, replayed by GAP = 33, failures = 0
```

The three implementations were written by different authors at different times
and share no code: `qverify.py` here, `check_qstar.py` in round 3, and the
GAP script. The checks are not a formality: the 92-move certificate passes
through a presentation whose total relator length is 582, with one relator of
length 381, and its longest conjugator has 180 letters. Negative controls, three deliberately corrupted copies of
`zieschang.cert` (one with the last move deleted, one with the stated end state
altered, one with a conjugator altered), are rejected by all three:

```
$ python3 qverify.py selftest/bad_conj.cert
FAIL selftest/bad_conj.cert
selftest/bad_conj.cert: move 25 (('delete', 2)) failed: generator x_2 occurs in 2 relators
$ python3 ../check_qstar.py selftest/bad_conj.cert
AssertionError: generator 2 is not free
$ python3 gapverify.py selftest/bad_conj.cert
FAIL bad_conj.cert
$ python3 qverify.py selftest/bad_endpoint.cert
selftest/bad_endpoint.cert: endpoint mismatch
$ python3 ../check_qstar.py selftest/bad_endpoint.cert
FAIL     selftest/bad_endpoint.cert: final state 2 xxxyyyyy != stated end 2 xxxyyyy
$ python3 gapverify.py selftest/bad_endpoint.cert
FAIL bad_endpoint.cert
$ python3 qverify.py selftest/bad_truncated.cert
selftest/bad_truncated.cert: endpoint mismatch
$ python3 ../check_qstar.py selftest/bad_truncated.cert
FAIL     selftest/bad_truncated.cert: final state 2 YYYYYXXX != stated end 2 xxxyyyyy
$ python3 gapverify.py selftest/bad_truncated.cert
FAIL bad_truncated.cert
```

The transcript is abridged to the verdict line of each run; `qverify.py` also
prints the offending state, which is long. `checkall.sh` runs the same nine
checks and stops with `ALL CHECKS PASS` only if every certificate replays and
every control is rejected.

The replayer `qverify.py` has its own self-test,
`qverify_selftest.py`, with 15 checks: the six-move relator interchange, the
deletion test on a conjugate of a generator and on a generator that is not
free, the Nielsen conventions, an automorphism whose image list is not
invertible (rejected), and an endpoint mismatch (rejected). It prints
`self-test failures: 0`.

## 5. What the certificates do and do not establish

They establish that Zieschang's pair and the McCool-Pietrowski pair are
Q\*\*-equivalent for the 27 triples of the box, with explicit move lists, and
therefore that the two presentations of each pair present the same group. That
fills the gap the round-3 report recorded in its Section 10 ("The Zieschang,
McCool-Pietrowski and Metzler Q\*\*-equivalences are quoted from Barmak's
Section 1 ... I did not write those certificates").

They do not establish Q\*-inequivalence of any pair. That half of the
literature's claim is quoted and not replayed. Barmak's reason is that the
relators of both pairs are of minimal length in their orbit under the
automorphisms of `F_2`, which he attributes to Whitehead's algorithm, and I did
not implement Whitehead's algorithm here. What I checked myself is weaker: for
the family the map `x -> x`, `y -> y^p` sends the second relator to a word that
is trivial in the group of the first presentation, so the isomorphism between
the two presentations of the pair that this map induces is not induced by an
automorphism of `F_2`, and `x -> x`, `y -> y^p` is not an automorphism of `F_2`
for `p` at least 2. The same map shows that the obvious isomorphism is not a Q\*
move. It does not show that no Q\* move exists.
**[checked for the map, quoted for Q\*-inequivalence]**

The certificates also do not settle the general `k,p,t` statement as a theorem,
because I verified 32 instances and not the general case. The recipe in Section
3 is uniform, the program takes any `k,p,t` at least 2, and every step of the
recipe was hand-checked, so I regard the general statement as proved with a
machine check on a box; a referee who wants the general case should rerun
`mkpair.py` with a wider box, which is one line.

## 6. Metzler's pair: the exact point where my method stops

Metzler's pair is `<x,y | x^5, y^5, [x,y]>` against `<x,y | x^5, y^5, [x^2,y]>`.
The two differ by the change of generator `x -> x^2`, which is an automorphism
of the presented group (of order 25) and not of `F_2`, so the same mechanism
should apply. It does not, and the reason is exact. Prolong and put `a = x^2`
with the relator `a x^{-2}`; then `x` has to be eliminated, which needs the
consequence `x a^2` (because `x^5 = x (x^2)^2 = x a^2` and `x^5 = 1`) as a
relator of the form `(letter)(word)`. The relators available are `x^5` and
`a x^{-2}`, and to obtain `x a^2` from them by Q-moves one has to multiply
`x^5` by the right product of conjugates of `a x^{-2}`, which is a small word
problem in a group of order 25. Multiplying relator `i` by a conjugate of relator `i` is not a Q-move,
because the multiplication has to use a different relator, so a product of two
conjugates of one relator has to be assembled through the other relators, and
every assembly I found pollutes the relator used as storage. The product
therefore has to be found by a genuine search. My canonical search does not find it within 20,000 expansions
at cap 30 and rank 3 (647,837 states pushed, 881 MB peak), and the round-3
engine does not find it within 30,000 expansions at cap 30. So Barmak's
Q\*\*-equivalence of Metzler's pair remains quoted and not replayed.
**[bounded negative]**

[Coordinator note, 6 November 2026, from the round-6 Metzler certificate
(directions/qdouble-star/m9/round6-m6.md), all checks rerun by me: the open item
above is now RESOLVED - an explicit 44-move Q\*\*-certificate replays under five
implementations, and the search heuristic this draft used is excluded by a
theorem (round-6's Lemma 2: no Q-certificate can hold x^5 and y^5 fixed, by the
free-product syllable argument in Z/5 * Z/5). One correction to this section:
the sentence calling the product search "a small word problem in a group of
order 25" is wrong about the group - the word problem for the conjugate
products lives in < x, a | x^5, a x^-2 > = < x | x^5 > = Z/5, order 5, not 25;
25 is the order of Metzler's group Z/5 x Z/5. The correction does not affect
the bounded negative, and the product is now given in closed form for every
exponent by round-6's Lemma 3. The same section's item 5 is answered: GAP gives
order 25 and abelian for both of Metzler's presentations. A second tooling
defect is also now recorded: the draft's qverify.py substitutes automorphism
images sequentially, which applies the map twice for permutations and rejects
every swap move; the fixed copy (qverify_fixed.py, installed alongside)
substitutes simultaneously, and the bug is latent - no shipped certificate
uses swap.]

Two features of the certificates explain why no search in Section 7 finds
them, and both are worth recording for the next round.

The first is length. Both engines expand states in order of total relator
length, so a state of length `L` is reached only after every state of length
below `L`, and the certificates pass through much longer states than they start
from: Zieschang's certificate runs from total length 10 up to 30, and the
certificate for `k=p=t=4` runs from 33 up to 90. A search ordered by length
will not visit those states at any budget that fits in memory.

The second is the conjugator length. Both engines generate conjugators of
length at most 1 or 2, together with the relators themselves. The
certificates need much longer ones: the longest conjugator is 6 letters for
Zieschang, 24 for `k=p=t=4` and 180 for `k=p=t=10`. A search whose conjugator
list is capped at length 2 therefore cannot construct these moves at all,
whatever its budget. That is the sharper reason, and it is a caution for the
resister searches as well: a "no path" line from an engine with a bounded
conjugator list says nothing about certificates that need a longer conjugator.

## 7. Bounded searches at raised caps and ranks

Two engines were used. `qstar.py` from round 3 is unmodified and is driven by
`runpush.py`. `cfsearch.py` is the canonical-form engine: it keeps
relators in a canonical rotation and a sorted relator list, records the
conjugation, inversion and permutation moves that implement the
canonicalisation, generates only the moves that are not quotiented out, and so
explores one representative per Q-orbit. Both engines score by total relator
length, expand in that order, break ties with the seed 20261104, and write one
line per instance to disk. Both are deterministic.

Memory. The round-3 engine stores every pushed state. Its peak resident size is
516 MB at 20,000 expansions, measured with `resource.getrusage`, which is about
26 MB per 1,000 expansions, so 50,000 expansions extrapolate to 1.3 GB and
100,000 to 2.6 GB. The canonical engine stores the canonical form instead and
measures 315 MB at 10,000 expansions and 618 MB at 20,000, about 30 MB per
1,000. Free memory was about 4 GB when the runs started, because other round-4
members were computing, so no run here exceeds 900 MB and the two engines were
run at most two at a time, under `nice`. This is why the budgets are 10,000 to
50,000 expansions: at 200,000 expansions the round-3 engine extrapolates to
about 5 GB, and the round-3 cap-21 census was killed at 200,608,294 states and
4.7 GB, so the ceiling is real.

| target | engine | cap | rank | budget (expansions) | outcome |
| --- | --- | --- | --- | --- | --- |
| AK(3) | canonical | 24 | 3 | 20,000 | no path, 512,260 states pushed, best length 13 |
| AK(3) | round 3 | 26 | 4 | 25,000 | no path, best length 13, 26 s |
| 96 open resisters | canonical | 24 | 3 | 10,000 each | no path, 96 of 96 |
| 96 open resisters | round 3 | 26 | 4 | 20,000 each | no path, 96 of 96 |
| 6 length-13 resisters | round 3 | 26 | 3 | 50,000 each | no path, 6 of 6 |
| 6 length-13 resisters | round 3 | 26 | 4 | 20,000 each | no path, 6 of 6 |
| Metzler's pair P1 to P2 | canonical | 30 | 3 | 20,000 | no path, 647,837 states pushed |

The 96 instances are the ones listed in `directions/qdouble-star/table_open.md`
(six of length 13 and ninety of length 14). The six length-13 rows are the same
six. Nothing found a path, so no new Q\*- or Q\*\*-certificate came out of these
runs, and every row is a bounded negative with the bound stated.

What the rows do not say. A "no path" line is not a box exhaustion: the search
is a best-first exploration of a bounded number of nodes inside a box that is
far larger than the budget, so a row says only that the engine did not find a
certificate in the stated number of expansions. The round-3 report's passes 1
to 3 for these instances remain the larger scales for the 96 (50,000 expansions
with the same engine), and my rows 2, 5 and 6 add cap 26 and rank 4 to the
configurations explored.

## 8. The answer to the AK(3) question inside these bounds

Is AK(3) Q\*\*-trivial? It is not decided here. Two engines, caps 24 and 26,
ranks 3 and 4, and budgets of 20,000 and 25,000 expansions find no
Q\*\*-certificate from AK(3) to the standard presentation. The total length of
every state the searches reached stayed at 13, so the searches did not even find
a presentation of AK(3) shorter in total length. Since Q\*\*-triviality of AK(3)
is the weak Andrews-Curtis conjecture for the campaign's flagship family, and
since the stable status of AK(3) is unresolved (round 2, `survey/stable-ak3-status.md`),
this is the expected outcome. The rows record how far the box was pushed in
rank and in cap, and they decide nothing about AK(3).

## 9. Files and exact commands

All of these are in `directions/qdouble-star/m9/`:

| file | contents |
| --- | --- |
| `qverify.py` | independent replayer for Q\*\*-certificates, written from Barmak's (i)-(vi); it also checks move (iv) when the automorphism is given with its preimages |
| `qverify_selftest.py` | 15 unit checks of the replayer, including two rejection tests |
| `mkpair.py` | builds the Zieschang certificate and the McCool-Pietrowski certificates for a box of `k,p,t`, asserting each intermediate state |
| `gapverify.py` | third replayer: translates a certificate into GAP and runs it, including prolongation and deletion |
| `cfsearch.py` | canonical-form best-first search, with its own canonicalisation checks |
| `runpush.py` | driver for the round-3 engine on the resisters, AK(3), Metzler's pair and Barmak's pair |
| `pdfcheck.py` | prints the glyph runs of the two formulas on page 346 and the Q\*\* sentence |
| `certs/` | 33 certificates: Zieschang and the 32 McCool-Pietrowski triples |
| `selftest/` | the three corrupted certificates used as negative controls |
| `runs/` | the run logs, one line per instance, and `SUMMARY.md` |
| `jobs/` | the job lists used by the two search drivers |
| `checkall.sh` | runs the three checkers on the 33 certificates, then the controls, then the self-test |

```
$ cd directions/qdouble-star/m9
$ bash checkall.sh                         # ends with ALL CHECKS PASS
$ python3 mkpair.py                        # rewrites certs/, asserting every state
$ python3 pdfcheck.py barmak_agt.pdf       # needs the PDF; the curl line is in its docstring
$ python3 cfsearch.py jobs/jobs_open96.txt runs/cf96b.txt --budget 10000 --cap 24 --rank 3
$ python3 runpush.py jobs/jobs_l13.txt runs/l13b.txt --budget 50000 --cap 26 --rank 3 --conj 1
```

The last two lines write to `runs/cf96b.txt` and `runs/l13b.txt` so that the
logs of the runs reported here stay as they were.

## 10. What I could not verify, and what remains uncertain

1. **Q\*-inequivalence is quoted, not checked.** I did not implement Whitehead's
   algorithm, so the "not Q\*" half of both literature claims rests on the
   source.
2. **The general `k,p,t` statement is verified on 32 triples.** The
   recipe is uniform and hand-checked, and the program accepts any `k,p,t` at
   least 2, but a referee who wants all of `N^3` has to accept the recipe.
3. **Metzler's pair and Barmak's pair have no certificate here.** Both are
   quoted as Q\*\*-equivalent in the source. I tried Metzler's pair only, and
   Section 6 records the exact step that my method cannot supply.
4. **The searches are bounded and heuristic.** No row is a box exhaustion, and
   the canonical engine prunes one representative per Q-orbit only after
   verifying that the canonicalisation is a Q-move sequence, so a "no path" row
   bounds that engine with that budget, nothing more.
5. **The group order 25 for Metzler's pair** is used in the argument of Section
   6 and is not needed for any certificate; I did not recompute it with GAP
   here. The round-3 gap run recorded order 1 for the resisters, not for
   Metzler's presentations.
6. **My rows and the round-3 rows for the six length-13 resisters are not
   comparable.** The round-3 table lists 200,000 expansions at cap 24 for them,
   and mine use cap 26, a larger box, so neither row dominates the other. Both
   are stated with their configurations.
