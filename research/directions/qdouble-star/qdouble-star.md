# Q\*\*-equivalence: Barmak's pair, the smallest open pairs, and 68 new Q\*-certificates

COORDINATOR NOTE, 2026-11-05 (round 4, from member m9 of swarm smw2woueq, who
ended without submitting; the work is coordinator-verified where checkable and
lives in the subdirectory m9/ of this directory). Two defects in this
round-3 tooling, both reproduced by the coordinator with direct tests, neither
affecting any round-3 result: (1) gap_replay.py's delete branch emits GAP code
that does not parse (the expression `g = 2 and (g in ...)` inside a ForAny),
so it cannot replay any certificate that uses deletion; the branch was never
exercised because none of the 69 round-3 certificates used deletion, and the
69/69 round-3 record stands (those certificates use no deletion). The
replacement m9/gapverify.py handles prolongation and deletion. (2)
check_qstar.py raises an uncaught AssertionError ("generator N is not free")
on a certificate whose deletion is invalid, so a batch runner gets a traceback
instead of a FAIL line; it detects the fault but does not report it cleanly.
Also recorded there: 33 new explicit Q**-certificates (Zieschang's pair in 26
moves; the McCool-Pietrowski family for 33 triples, 20 to 92 moves), all
replaying under three checkers; the caution that both campaign search engines
cap conjugators at length 1 or 2, while the new certificates need conjugators
of length up to 180 and pass through far longer states, so a bounded engine's
"no path" bounds only that engine's move set; and the exact stopping point for
Metzler's pair, which remains quoted and not replayed.

Member m10, swarm smw2opo0o, direction F7 (d10). Written 2026-11-05 UTC.
Working directory `.ultramath/smw2opo0o/m10/`; this directory holds the same
files plus the run logs.

Labels used below. **[proved here]** is an argument written out here or a
statement checked by the exact command quoted. **[computed here]** is a
deterministic computation with the command and its output quoted. **[quoted]**
is a statement taken from a source whose identifier I checked live.
**[bounded negative]** is a search result with its exact bounds. Nothing below
proves or disproves the Andrews-Curtis conjecture, and no claim here is rounded
up.

## 1. Results in one page

1. **Barmak's pair is Q\*\*-equivalent, and the proof is refereed.** Barmak,
   *An exotic presentation of Z x Z and the Andrews-Curtis conjecture*,
   Algebr. Geom. Topol. 25 (2025) 345-355, DOI 10.2140/agt.2025.25.345, writes on
   page 347 of the published version: "After the first version of this paper was
   finished, X Fernandez [10] proved that the presentations P and Q are in fact
   Q\*\*-equivalent", with [10] = X. Fernandez, *Morse theory for group
   presentations*, Trans. Amer. Math. Soc. 377 (2024) 2495-2523,
   DOI 10.1090/tran/8958. Fernandez's Example 3.4 states the result directly:
   "We produce an acyclic matching M in X(K_{B2'}) such that the associated Morse
   presentation is greedily transformed into B1 via the reduction algorithm (see
   Appendix A). By Theorem 2.9 and Remark 3.1, we conclude that B1 ~_{Q\*\*} B2".
   The 2018 first version (arXiv:1806.11493v1) said the opposite, "We do not know
   whether these presentations are Q\*\*-equivalent or not". **[quoted, read in
   the published AGT PDF and in the arXiv v3 PDF of Fernandez]**
2. **Q\* is strictly finer than Q\*\* for a trivial reason at the bottom of the
   scale.** Q\* preserves the number of generators and Q\*\* does not. The pair
   <x | x> and <x, y | x, y> has total relator length 1 and 2, is Q\*\*-equivalent
   by a single prolongation, and is not Q\*-equivalent. **[proved here, with a
   machine-checked certificate]**
3. **The smallest pairs whose Q\*\*-equivalence is open are at relator length
   13.** Every pair of balanced presentations of the trivial group with total
   relator length at most 12 is settled by the round-1 census and by
   `directions/c14/final_classes.txt`. At length 13 the open cases are the 14
   resisters and the 6 presentations that are Q\*-equivalent to AK(3), whose
   Q\*\*-status is open. **[proved here from the two censuses, whose own
   completeness checks I cite rather than rerun]**
4. **68 of the 164 resisters of `directions/c14/` are Q\*-equivalent to the
   standard presentation, with explicit certificates.** 8 of the 14 length-13
   resisters and 60 of the 150 length-14 ones. The certificates have 26 to 55
   moves, never leave rank 2, and never exceed the total relator length of their
   start by more than one. **[computed here, replayed by three independent
   implementations, two in Python and one in GAP]**
5. **The essential ingredient is the Nielsen move, which the c14 move system
   omits.** The same search with the Nielsen moves removed solves 0 of those 68
   within 20000 expansions each, and solves 20 of 20 randomly sampled
   c14-certified AC-trivial presentations at length 13 within 38 expansions
   each. **[computed here]**
6. **All 164 resisters present the trivial group.** GAP 4.14 returns group order
   1 for every one of them, each in about a second and each under the 8 second
   per-process limit that I used. **[computed here]**
7. **Bounded negatives with exact bounds.** The other 96 resisters, AK(3),
   Metzler's pair and Barmak's pair do not fall to the search inside the stated
   bounds. **[bounded negative]**

## 2. The four move systems, and which one each result uses

All definitions are from Barmak's Section 1, which agrees with
Hog-Angeloni-Metzler, LMS Lecture Notes 197 (1993), Chapter I, (26) to (28).

* **Q** (called AC in `charter.md`): replace a relator by its inverse, by a
  conjugate, or by its product with another relator.
* **Q\***: Q plus the elementary Nielsen transformations of the generators,
  that is, replace a generator by its inverse, by its product with another
  generator on either side, or permute generators, throughout all relators.
  Barmak states the move as "change each relator by an automorphism of the free
  group", so any automorphism of $F_n$ is one Q\*-move.
* **Q\*\***: Q\* plus prolongation, namely adjoining a new generator together
  with the relator equal to it, and its inverse.
* **stable AC** in `charter.md` is Q plus prolongation. It contains Q and is
  contained in Q\*\*, it is not Q\* (it has no Nielsen moves), and Q\* does not
  contain it (prolongation is not a Q\* move).

The distinction matters for reading the campaign's data. The toolkit, the
round-1 census, `directions/c14/` and `directions/pu-enumeration/` all work in
Q, and c14 works in a twelve-move restriction of Q in which a relator is
conjugated by one generator at a time. Conjugating by a word is a succession of
those, so the restriction is harmless for Q; it is not harmless with respect to
the Nielsen moves, which c14 does not have at all. A certificate that uses only
Q moves is an AC certificate in the sense of `charter.md`; a certificate that
uses Nielsen moves is a Q\* certificate and is not.

## 3. The engine and what checks it

* `qstar.py` implements Q, Q\* and Q\*\* moves as tags, plus a best-first search
  in order of total relator length and a certificate file format.
* `check_qstar.py` is an independent replay checker. It shares no code with
  `qstar.py`; it re-implements free reduction, the substitutions, the Q moves
  and prolongation from the definitions, and it validates the freeness condition
  of a deletion.
* `crosscheck_c14.py` converts every line of `directions/c14/certs_all.txt` into
  the tag language and replays it twice, once through each implementation:

```
$ python3 crosscheck_c14.py
lines replayed = 53866, reached the standard presentation = 53866, failures = 0
longest move list = 141, relator lengths seen = [1, 2, ..., 13]
```

  53,840 of the lines reach the standard presentation and the other 26 reach
  AK(3) = `(abaBAB, aaaBBBB)`, which is what c14's file states. This is the
  calibration of my move semantics against an independent body of 53,866 known
  certificates. **[computed here]**

* `gap_replay.py` is the third implementation. It translates each certificate
  into a GAP script that rebuilds the presentation in a free group of rank 8 and
  applies every move with GAP's `MappedWord`:

```
$ python3 gap_replay.py out/*.cert
certificates = 69, replayed by GAP = 69, failures = 0
```

* `search.py selftest` runs eleven unit checks of the engine, among them that
  the six-move derivation which interchanges two relators really interchanges
  them, and that prolongation followed by deletion returns the start.
* `winding_check.py` checks that the two relators I attribute to Barmak's
  presentation Q are the printed ones, by recomputing his winding invariant from
  its definition:

```
$ python3 winding_check.py
winding of [x,y]                                     PASS   got 1
relator lengths of Barmak's Q: (20, 16)
winding of r1 against Barmak's printed value         PASS   got (-2*X + Y + 2)/Y
winding of r2 against Barmak's printed value         PASS   got (-X**2 + 2*X - 1)/Y
OVERALL PASS
```

  The two printed values are $1-2(X-1)Y^{-1}$ and $-(X-1)^2Y^{-1}$, and the
  computation reproduces both, together with $\Lambda(P)=(1,0)$ for
  $P=\langle x,y \mid [x,y], 1\rangle$. **[computed here]**

## 4. Why the first open pairs sit at relator length 13

Write $\ell(P)$ for the total relator length of a balanced presentation. Every
balanced presentation of the trivial group has a contractible standard complex
(Lemma 1 of `survey/q-transformations.md`), and the Whitehead group of the
trivial group vanishes, so any two of those complexes are simple homotopy
equivalent. The pairs the direction asks about are therefore exactly the pairs
of balanced presentations of the trivial group, and the question is which of
those pairs are settled.

* At $\ell \le 11$ the round-1 census is complete: 26,182 canonical
  presentations, 3,697 AC-trivial with certificates, 0 unresolved
  (`survey/computational`, `python3 census.py 11 13 certs_r11_c13.txt`). Every
  one of them is Q-trivial, so every pair at that length is settled.
* At $\ell = 12$, `directions/c14/final_classes.txt` lists 4,396
  determinant-passing presentations: 4,392 AC-trivial with certificates and 4
  with an $A_5$ quotient. There is no unresolved case.
* At $\ell = 13$ it lists 18,116: 18,076 AC-trivial, 20 with an $A_5$ quotient,
  6 Q\*-equivalent to AK(3), and 14 resisting. The 20 with an $A_5$ quotient are
  not presentations of the trivial group, so their standard complexes are not
  homotopy equivalent to a point and they drop out of the question. The
  remaining 20 are open for Q\*\*: the 14 resisters because their status is
  unknown, and the 6 AK(3)-class members because the Q\*\*-triviality of AK(3)
  is open.
* At $\ell = 14$ the same file lists 31,556, of which 150 resist.

Two refinements follow. First, the eight length-13 resisters that Section 6
settles are no longer open, so after this work the shortest open cases inside
the census are the 6 remaining length-13 resisters (all four-word ones such as
`BAbABa,BBBAAAA`) together with the 6 AK(3)-class members at the same length.
Second, this ordering depends on the c14 census being complete at lengths 12, 13
and 14. That completeness rests on the pruning steps of its Section 7 and on
reproducing the published list sizes; I quote it, I did not rerun the
366,819-candidate enumeration.

A remark on the other end. If one does not fix the rank or the deficiency, the
smallest Q\*\*-but-not-Q\*-equivalent pair is $\langle x \mid x\rangle$ against
$\langle x,y \mid x,y\rangle$, of total relator length 1 and 2, because Q\*
preserves the number of generators and one prolongation connects them. The
smallest pair in which both presentations have the same rank, the same
deficiency and different Q\*-classes is Metzler's, quoted by Barmak: the
presentations $\langle x,y \mid x^5, y^5, [x,y]\rangle$ and
$\langle x,y \mid x^5, y^5, [x^2,y]\rangle$ are Q\*\*-equivalent and not
Q\*-equivalent, and they have total relator length 14 and 16 at rank 2. Barmak's
pair has relator lengths 4 and 36, so it is larger than Metzler's in this
measure. Barmak introduces it because it sits one above the minimal Euler
characteristic and because its obstruction to Q\*-equivalence is Evans's matrix
over $\mathbb{Z}[X^{\pm1},Y^{\pm1}]$ rather than the length of a relator; its two
relator sets also have the same normal closure, as do Metzler's.
**[quoted for the equivalences, computed here for the lengths]**

## 5. A certificate for the smallest Q\*\*-but-not-Q\*-equivalent pair

`out/smallest_qstar_gap.cert` holds the single prolongation that carries
$\langle x \mid x\rangle$ to $\langle x,y \mid x,y\rangle$:

```
$ python3 check_qstar.py out/smallest_qstar_gap.cert
OK     out/smallest_qstar_gap.cert: 2 x;y (1 moves)
```

Since Q\* moves never change the number of generators, the two presentations are
not Q\*-equivalent, and this single move is the smallest possible witness of the
strictness of the inclusion Q\* inside Q\*\*. **[proved here]**

## 6. 68 resisters of directions/c14 fall to Q\*

Search: best-first in order of total relator length, rank at most 3, states of
total relator length at most 24, conjugators of length at most 1 together with
the two relators themselves, Nielsen moves included, budget 20,000 expansions in
the first pass and 50,000 in the second. The seed is fixed at 20261104 and the
run is deterministic.

| pass | budget | instances | solved |
| --- | --- | --- | --- |
| 1 | 20,000 | all 164 | 44 |
| 2 | 50,000 | the 120 not solved in pass 1 | 24 |
| 3 | 50,000, extended Nielsen set | the same 120 | 24 (the same ones) |

The table of the 68 is `table_solved.md`; the table of the 96 that remain is
`table_open.md`. `out/` holds 69 certificates: the 68 resister certificates and
the one-move certificate of Section 5, which the table script skips. Summary of
the 68 resister certificates:

* 8 of the 14 length-13 resisters and 60 of the 150 length-14 ones.
* 26 to 55 moves, mean 38.4.
* Every path stays at rank 2, so these are Q\* certificates and not Q\*\*
  certificates: no prolongation is used.
* Every path stays within the start's total relator length plus one, so all
  intermediate presentations lie inside the search boxes that c14 reports as
  exhausted.
* Move counts by kind over all 68: conjugation 1,088, left multiplication 300,
  right multiplication 269, `nji` 327, `nij` 336, inversion 184, `neg` 108.

What the certificates establish. Each presentation is Q\*-equivalent to the
standard one, therefore it presents the trivial group, and it satisfies the weak
Andrews-Curtis conjecture, that is, it is Q\*\*-trivial. The group triviality is
independently confirmed by GAP for all 164 resisters:

```
$ for each presentation: gap -q with Size(F/[r1,r2])
164 of 164 return 1
```

What they do not establish. They do not give AC-triviality in the sense of
`charter.md`, because the Nielsen moves are not Q moves. Whether those 68 are
AC-trivial (Q-trivial) or stably AC-trivial remains open.

Why the Nielsen moves are the essential addition. I reran the same search with
the Nielsen moves removed, keeping left multiplication and the same conjugator
list, on each of the 68 certificates' start presentations:

```
$ python3 -u control_nielsen.py
Q-only (no Nielsen moves), 20000 expansions each: solved 0 of 68 in 246 s
```

So the 68 are not reached by relator moves within 20,000 expansions each, while
all 68 are reached in 4,000 to 35,000 expansions when the Nielsen moves are
allowed. One structural remark explains why a substitution on the generators
should matter this much. A relator move replaces one relator by $w r^{\pm1} w^{-1}$,
by $r s$ or by $s r$ with $s$ a different relator, and it leaves all other
relators alone; consequently no relator move can multiply a relator by a
conjugate of itself. A Nielsen move rewrites every relator simultaneously, so it
changes the way both relators are spelled in the generators, and that is what
these presentations need. Metzler's example is the cleanest instance: the two
relators differ exactly by a self-multiplication,
$[x^2,y] = (x[x,y]x^{-1})\cdot[x,y]$, which no relator-only sequence can supply,
and that is why a Q\*\* certificate for it has to use prolongation.
**[argument for the structural remarks, computations for the counts]**

## 7. Bounded negatives, with the bounds

All four runs use the same engine, rank at most 3, conjugators of length at most
1 plus the relators, seed 20261104, and a heap cap that cannot change the answer
(the heap only stores the frontier).

| instance | start length | cap | budget | outcome | best length reached | wall clock |
| --- | --- | --- | --- | --- | --- | --- |
| 96 remaining resisters | 13 or 14 | 24 | 50,000 each | no path | 13 or 14 | 20 to 40 s each |
| 6 remaining length-13 resisters | 13 | 24 | 200,000 each | no path | 13 | 448 to 662 s each |
| AK(3) | 13 | 24 | 30,000 | no path | 13 | 27 s |
| Metzler's pair, P1 to P2 | 14 | 24 | 30,000 | no path | 14 | 56 s |
| Barmak's Q to P | 36 | 44 | 30,000 | no path | 30 | 22 s |

The run behind the second row is `out/l13A.txt`. Two further configurations of
it, one with rank at most 4 and one with conjugators of length at most 2, were
started and cut off by the session's time limit before their first instance
finished, so I report no verdict for them.

The calibration that makes these negatives readable is a positive run on cases
whose answer is known. A systematic sample of 20 of the length-13 presentations
that c14 certifies as AC-trivial was handed to the same search with a budget of
5,000 expansions:

```
$ python3 calibrate_sample.py
calibration: solved 20 of 20, mean path 9.9, 0.1 s total
```

Every one was solved in at most 38 expansions, and the paths have 6 to 13 moves.
So the search finds short certificates immediately when they exist at that size,
and the failures in the table above are not an artefact of a toothless search.
They are still not proofs: the caps, the conjugator list and the budget are
finite. **[bounded negative]**

## 8. Corrections to the campaign record

1. `survey/q-transformations.md` Section 5 attributes the Q\*\*-equivalence of
   Barmak's pair to Fernandez, "quoted: Barmak 2025, Section 1, citing Fernandez
   2024". That attribution is correct for the published AGT version, which
   credits Fernandez on page 347, and the direction statement's word
   "unrefereed" should be dropped: Fernandez's paper appeared in the Transactions
   of the AMS in 2024. Two details are worth adding to the survey. The 2018 first
   version of Barmak's paper says he does not know whether the pair is
   Q\*\*-equivalent, so the survey should cite the published version. The same
   published introduction also says that "Our presentations P and Q are above
   minimal Euler characteristic and become Q\*-equivalent after one
   stabilization", which is a weaker statement than the added sentence about
   Fernandez and sits two paragraphs earlier; the asterisks are lost in the text
   layer of the PDF I read, so the reading of that sentence as Q\*\* rests on the
   surrounding text.
2. **The 164 resisters are resisters for Q, not for Q\*.** 68 of them are
   Q\*-trivial with explicit certificates whose intermediates lie inside c14's
   own length caps. c14's own Section 9.5 and the Round-3 coordinator note in
   `directions/c14/c14.md` already record that its certificates and its negative
   bounds live in a twelve-move system; the missing moves there are the Nielsen
   moves, and my control run shows that they are what matters.
3. **All 164 resisters present the trivial group** (GAP, verified here for every
   one). The word "resisting" in `final_classes.txt` means "no AC certificate and
   no nontrivial quotient", and it should not be read as "possibly a
   counterexample to the triviality of the group".
4. For the open questions list: a new precise question is whether AK(3) is
   Q\*\*-trivial. It is the Q\*\*-status of the 6 length-13 AK(3)-class members
   and of the whole AK(3) class, it is equivalent to the weak Andrews-Curtis
   conjecture for the campaign's flagship family, and the literature quoted in
   `survey/stable-ak3-status.md` settles only the Q\* leg.

## 9. Files and exact commands

Code, all deterministic, standard Python 3 plus sympy for the winding check:

| file | contents |
| --- | --- |
| `qstar.py` | Q, Q\*, Q\*\* moves, certificate format, best-first and beam search |
| `check_qstar.py` | independent replay checker for certificates |
| `search.py` | named instances, unit self test (`python3 search.py selftest`) |
| `run_batch.py` | batch driver, one line of output per instance |
| `crosscheck_c14.py` | replays all 53,866 c14 certificates through both implementations |
| `make_tables.py` | builds `table_solved.md` and `table_open.md` from the logs |
| `summarise_certs.py` | rank trace, intermediate lengths and move kinds per certificate |
| `calibrate_sample.py` | the 20 of 20 positive calibration |
| `control_nielsen.py` | the 0 of 68 control without Nielsen moves |
| `winding_check.py` | transcription check of Barmak's relators |
| `gap_replay.py` | third replay implementation, in GAP |
| `out/*.cert` | 69 certificates: the 68 Q\* certificates and the one-move smallest-gap certificate |
| `out/*.txt` | the run logs, one line per instance |
| `gap/sizes.txt` | GAP group order 1 for all 164 resisters |

The commands behind the headline numbers:

```
python3 search.py selftest
python3 crosscheck_c14.py
python3 winding_check.py
python3 run_batch.py jobs_all0.txt out/all_0.txt --budget 20000 --cap 24 --rank 3 --conj 1
python3 check_qstar.py out/*.cert
python3 gap_replay.py out/*.cert
python3 summarise_certs.py out/*.cert
python3 make_tables.py
python3 calibrate_sample.py
python3 control_nielsen.py
```

## 10. What I could not do or verify

* No explicit Q\*\* certificate for Barmak's pair, and none for Metzler's pair.
  Fernandez's proof is computer-assisted through discrete Morse theory and prints
  a matching, not a move sequence; my 30,000-expansion search finds nothing at
  those sizes. The Q\*\*-equivalence of both pairs is quoted, not replayed.
* The published AGT PDF loses the asterisk characters in its text layer, so my
  reading of its "Q\*" and "Q\*\*" sentences uses the context and the reference
  list rather than the glyphs. The sentence that credits Fernandez, quoted in
  Section 1, is unambiguous in that respect.
* No proof that any of the 96 open resisters is not Q\*\*-trivial. The negative is
  a search with stated caps and budget. The rank-4 and conjugator-length-2
  variants of the search on the 6 length-13 resisters were cut off by the time
  limit and have no verdict.
* The completeness of the c14 census at relator length 12, 13 and 14 is quoted
  from `directions/c14/`; I did not rerun the enumeration.
* The Zieschang, McCool-Pietrowski and Metzler Q\*\*-equivalences are quoted from
  Barmak's Section 1. Barmak writes that the translation to Q\*\*-moves is easy
  for the first two families; I did not write those certificates.
* The claim in Section 6 that no relator move can multiply a relator by a
  conjugate of itself is an argument about the move list, not a computation. It
  is the reason I expect Nielsen moves to be essential in these examples; the
  control run is the evidence for the 68 instances themselves.
