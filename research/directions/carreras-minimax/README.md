# An independent audit of the minimax, classification-table and AC-19 claims of arXiv:2607.23611

Direction H10 of round 5, member m2, swarm smw38010i. Written 2026-11-05.

## 1. What was audited

The target is J. Carreras, *Machine-checkable equivalence certificates at the length-14 Andrews-Curtis frontier*, arXiv:2607.23611v1 (math.GR, submitted 26 July 2026, 10 pages, artifact at `github.com/joe-carr-data/ac-certificates` and DOI `10.5281/zenodo.21499081`). I fetched the abstract page, the e-print source (`manuscript.tex`) and the five certificate JSON files on 2026-11-05 and read Sections 2, 3, 5, 6, 7 and 8 in full.

Two further primary sources are needed for the claims about third-party data. The first is arXiv:2606.21611v1 (L. Fagan, M. Tarquini, A. Shehper, M. Manko, A. Gruen, C. Huang, G. Butbaia, D. Passaro, S. Gukov, *The Two-Hump Problem*, ICML 2026, submitted 19 June 2026). Its Tables 2 and 3 are the classification table under discussion. They are present in the e-print as `classification_table.tex` and `counterexamples_table.tex`. The second is the AC-19 dataset in `github.com/Math-AI-Caltech/ACSolverX`, files `data/AC19.txt`, `data/AC19_extended.txt` and `data/1190MS.txt`.

The paper states that the Two-Hump table records no classification algorithm and no connecting paths. Everything below about that table is therefore re-derived from the published rows alone, with my own parser, my own canonical form and my own union-find.

## 2. Verdicts

| id | claim (section of the paper) | verdict |
|---|---|---|
| C1 | `d_GS(MS(3, yx^2y), AK(3)) = 19` exactly (§5, Theorem 5) | VERIFIED, both bounds |
| C2 | `d_GS(P1, AK(3)) >= 27`, `d_GS(P2, AK(3)) >= 27`, `d_GS(P1, P2) >= 27` (§5) | VERIFIED by exhaustion |
| C3 | the nine published state counts of §5 (all but the two budget-stop partials) | VERIFIED, all nine exactly |
| C4 | the three blocks are pairwise disjoint below total length 25 and 26 (§5) | VERIFIED |
| C5 | the structural reading of first neighbourhoods (§5) | VERIFIED, and it pins the move set |
| C6 | the §3 table of moves, classical moves and peaks for the five certificates | VERIFIED, all fifteen numbers |
| C7 | 170 rows, 550 labelled cells, 261 classes, all occurrence counts; 550 H1 keys, 275 H2 keys, 275 H3 keys; 275 sigma-pairs; 61 intra-class and 214 cross-class; 133 components (§7) | VERIFIED |
| C8 | 0/550 length changes under cyclic reduction; 354/550 shorter class labels; class 14_2 has six members and three H2 keys (§7) | VERIFIED |
| C9 | all six benchmark presentations and AK(3) are absent from AC-19 (140,535 rows) and from the extended release (156,762 rows) (§8) | VERIFIED |
| C10 | the capacity-28 budget stop and its partial counts 5,640,276 and 1,987,856 (§5) | NOT CHECKED |
| C11 | the Prover9 and E negative results (§6) | NOT CHECKED, neither prover is installed |
| C12 | the ten shortest cross-label sigma-pairs exhaust their bounded components (§7) | NOT CHECKED, their engine, engine-relative |
| C13 | "The length-14 stratum as a whole has never been exhaustively classified" (§4) | CROSS-REFERENCE, see F5 |

Six findings beyond the claims are recorded in Section 8. The sharpest is F1: AC-19 contains 44 rows of our own resister ledger, and 3 of them are still undecided at round 4 with cap-25 bounds.

## 3. Method

### 3.1 The graph

Vertices are canonical states: a pair of relators, each replaced by the lexicographic minimum over its cyclic rotations and the rotations of its inverse, then the two relators sorted lexicographically. This is Definition (Canonical Form) of arXiv:2606.21611 Appendix A and the Sigma-orbit convention of arXiv:2607.23611 Section 2.

Edges are substitution moves. The parameters are `(i, j, k1, k2)` in `{1,2} x {-1,1} x Z x Z`, and the move replaces relator `r_i` by `rot^k1(r_i) . rot^k2(r_{3-i}^j)`, admitted only when the last letter of the first factor is the inverse of the first letter of the second factor (Definition (Substitution Move), arXiv:2606.21611 Section 3.2). I free-reduce and then cyclically reduce the product. The energy of a vertex is the total length of its two cyclically reduced relators. Throughout, cap `c` means total length at most `c`, and the paper's "exclusive cap C" means at most C - 1, so its exclusive cap 25 is my cap 24. For a path, the bottleneck is the maximum energy on it, and `d_GS` is the minimum bottleneck over directed paths.

The definition has `i` ranging over both relators. Reading Appendix A's remark literally, that only appending `r_2` to `r_1` is needed, gives a different graph. From `MS(3, yx^2y)` the one-sided generator produces first-move energies `{19, 21}`, and the two-sided generator produces `{15, 17, 19, 21}`. Only the two-sided generator reproduces the paper's structural sentence and its nine state counts, so the published numbers pin the move set to the two-sided definition. This is worth recording because the remark in the source, as written, is not invariant under the sigma-quotient.

### 3.2 Three implementations

`gs2.py` is the Python reference. It runs a bottleneck Dijkstra (a priority queue keyed by the current peak, with optimal termination at the first settled target) and exact peak-bounded reachability. `gsbox.c` is an independent C port used for the large enumerations, with an exact open-addressing table over full state records and no hash-only identity. `verify_path.py` is a second checker that shares no search code: for each consecutive pair of states on a recorded path it enumerates every parameter tuple, applies the move from the definition, canonicalises, and confirms that one tuple produces the next recorded state. It also expands the path into packaged elementary moves in the JSON format of the audited paper.

Every expansion is replayed by `directions/c14/carreras/replay_carreras.py`, the verifier member m8 wrote in round 3 from the JSON format alone, independently of this audit.

### 3.3 Engine cross-checks

The C port and the Python reference agree exactly on peak-bounded reachable set sizes from `AK(3)`: 1,000 at cap 17, 2,128 at cap 18, 38,612 at cap 20. Both then reproduce all nine state counts that the paper publishes at caps 24, 25 and 26, which is a much sharper check: a wrong move set, a wrong energy convention or a wrong canonical form would change those counts.

## 4. C1: the bottleneck distance is exactly 19

Peak-bounded reachable sets from the two sources, computed exactly (run log in `outputs/sublevel_and_bottleneck.txt`):

| cap | `R(AK(3))` | `R(MS(3, yx^2y))` | intersection |
|---|---|---|---|
| 13 | 1 | 0 | 0 |
| 14 | 1 | 1 | 0 |
| 15 | 26 | 5 | 0 |
| 16 | 40 | 31 | 0 |
| 17 | 1,000 | 98 | 0 |
| 18 | 2,128 | 292 | 0 |
| 19 | 19,604 | 19,604 | 19,604 |

The lower bound is the row at cap 18. A directed GS path from `AK(3)` to `MS(3, yx^2y)` of bottleneck at most 18 would place the target in both reachable sets, and the sets are disjoint. So `d_GS >= 19`.

The upper bound is a path of 35 states whose energy sequence is 13, 15, 15, 15, 15, 15, 15, 16, 17, 17, 17, 17, 15, 15, 16, 15, 17, 18, 19, 18, 19, 18, 15, 17, 17, 17, 19, 17, 19, 17, 17, 15, 18, 19, 14. Its maximum is 19 and its last state is the canonical form of `MS(3, yx^2y)`, which has energy 14. The path is in `path_19.json`, each of its 34 steps passes the brute-force checker, and the expanded certificate of 266 packaged elementary moves passes the campaign verifier, including the check that the endpoint lies in the Sigma-orbit of the target. The elementary peak of that expansion is 26 with a single-relator peak of 17, which is comparable to the 24 and 15 the paper reports for its own 66-move certificate.

At cap 19 the two reachable sets coincide, so both presentations lie in one peak-19 component of 19,604 states. That is consistent with the paper's account of a collision at barrier 19.

## 5. C2 and C3: the lower bounds 27 and the nine counts

`gsbox.c` at caps 24, 25 and 26 with the three sources `AK(3)`, `P1 = MS(2, x^-2 y^-1 x^2 y)` and `P2 = MS(2, x^-2 y^-1 x^2 y^-1)` (logs in `outputs/gsbox_cap24.txt`, `gsbox_cap25.txt`, `gsbox_cap26.txt`):

| cap | `R(AK(3))` | `R(P1)` | `R(P2)` | union | pairwise intersections |
|---|---|---|---|---|---|
| 24 | 1,532,732 | 135,892 | 168,304 | 1,836,928 | 0, 0, 0 |
| 25 | 5,431,780 | 356,836 | 424,352 | 6,212,968 | 0, 0, 0 |
| 26 | 10,118,636 | 851,836 | 2,534,472 | 13,504,944 | 0, 0, 0 |

The paper prints 1,532,732, 135,892, 168,304, 356,836, 424,352, 851,836, 2,534,472, 6,212,968 and 13,504,944, which is nine numbers. Every one of them reproduces exactly. The two further counts that §5 prints, 5,640,276 and 1,987,856, come from the budget-stopped cap-28 run and are not verified here. The `AK(3)`-side figures at caps 25 and 26 are not printed in the paper; they are the differences implied by its printed union totals, and they come out to 5,431,780 and 10,118,636 as required.

The intersection columns are all zero, so no directed GS path of bottleneck at most 26 joins any two of the three sources. This is exactly the paper's exclusion of bottleneck at most 26, and with the cap-25 run it also reproduces its exclusion of bottleneck at most 25. C2 and C4 follow.

The growth ratios of the paper also follow from the same table: `P2` goes from 424,352 to 2,534,472, a factor of 5.97, and `P1` from 356,836 to 851,836, a factor of 2.39.

Memory for the cap-26 run was 792 MB peak against 16 GB, and wall clock was 1,959 s on one core. The cap-25 run took 967 s at 541 MB.

## 6. C5: the structural reading

From `MS(3, yx^2y)`, whose relator split is 9 + 5 and whose energy is 14, the first GS moves give 32 successors and their energies are 15 (four of them), 17 (twelve), 19 (four) and 21 (twelve). The minimum is 15, one unit above the start, which is what the paper says. From each of `P1`, `P2`, `P5` and `P6`, whose split is 7 + 7, there are 32 first moves, eight at energy 17 and twenty-four at energy 19, and nothing else. All four MS(2) forms behave the same way, so the asymmetry between the two families is a first-neighbourhood fact, which is the reading the paper gives it.

## 7. C6, C7 and C8: certificates and the Two-Hump table

### 7.1 The certificate table

My own replayer (`cert_table.py`), written from Section 2's description of the four move types and the "classical" accounting rule, reproduces the whole of the paper's verification table:

| certificate | packaged | classical | peak total / single |
|---|---|---|---|
| `cert_sym_equiv_orphan1.json` | 36 | 58 | 27 / 17 |
| `cert_idx0_equiv_mirror.json` | 85 | 155 | 33 / 21 |
| `bottleneck_ak_f3_cert.json` | 66 | 101 | 24 / 15 |
| `cert_ms3_yx2y_equiv_ak3.json` | 71 | 106 | 22 / 15 |
| `cert_ms3_yinvx2yinv_equiv_ak3.json` | 13 | 22 | 23 / 14 |

All five endpoints agree with the recorded `reached` state and all five lie in the Sigma-orbit of their declared target. The "classical" count is computed by the rule the paper states, with the rotation cost `min(k, L-k)` evaluated against the relator length at the time of the move.

### 7.2 The table

`parse_table.py` reads `classification_table.tex` and `counterexamples_table.tex` with a LaTeX word parser. It finds 170 rows and 1,190 cells, of which 640 are marked trivial and 550 carry a class label, and 261 distinct labels. All 261 per-class occurrence counts in Table 3 agree with the counts recomputed from Table 2, and the occurrences total exactly 550.

`sigma_pairs.py` rebuilds the 550 presentations as `MS(n, w) = <x,y | x^-1 y^n x y^-(n+1), x^-1 w>` from the row and column indices, and applies sigma, which sends x to x and y to y^-1. The image of every one of the 550 is again one of the 550 up to canonical form, so sigma acts as an involution with 550 images, 275 pairs and no fixed point. Of the 275 pairs, 61 join two members of one class and 214 join different classes. A union-find over the 261 class labels with the 214 cross-class edges gives exactly 133 components.

A note on the order of work. I wrote this computation from the table rows before reading the artifact's own `reverse261.py`. That script does the same three things differently in one respect: it runs the union-find over the 550 presentations, including the 61 intra-class sigma-pairs, and counts the components of that graph, where I run it over the 261 class labels with the 214 cross-class edges only. Both give 133, which is a consistency check on the two formulations rather than a shared computation.

The ladder of quotients also reproduces: 550 distinct keys under rotation, inversion and swap (H1), 275 under the addition of generator inversions (H2), and 275 under all signed permutations (H3).

### 7.3 The fingerprints

No relator of the 550 changes under cyclic reduction. Class-label length is strictly smaller than the presentation's own cyclically reduced length for 354 of the 550 members. Class `14_2` has six members and exactly three distinct H2 keys. On the partition question, the H1 keys refine the table's partition (no H1 key meets two classes and 64 classes carry more than one H1 key), while the H3 keys both split and merge it (214 H3 keys meet more than one class and 64 classes carry more than one H3 key). That is the paper's conclusion that none of the three tested quotients reproduces the partition.

## 8. C9 and six findings about the data

### 8.1 The membership audit

`AC19.txt` has 140,535 rows and `AC19_extended.txt` has 156,762 rows, so both figures printed by the paper are the row counts of the released files. I canonicalised every row with the Fagan canonical form and tested the seven presentations. All seven are absent from both files: `MS(2, x^-2y^-1x^2y)`, `MS(2, x^-2y^-1x^2y^-1)`, `MS(3, yx^2y)`, `MS(3, y^-1x^2y^-1)`, `MS(2, yx^2yx^-2)`, `MS(2, yx^2y^-1x^-2)` and `AK(3)`. The paper's audit claim is confirmed.

### 8.2 F1: AC-19 contains 44 rows of our own resister ledger

Our length-14 classification table `directions/c14/final_classes.txt` has 54,068 rows, and 164 of them are labelled resisting with bounds. I matched all 54,068 canonical keys against the 140,535 canonical keys of `AC19.txt`. Exactly 44 of the resisting rows are AC-19 members: 6 at total length 13 and 38 at total length 14.

This is not a contradiction of anything in the paper, and it is the most useful thing the audit produced. The campaign has since decided 41 of the 44: rounds 3 and 4 produced certificates for them, which independently confirms that AC-19's inclusion of those rows was correct. The remaining three are still undecided at round 4 and sit in the cap-25 component of 38,286,952 states that round 4 exhausted without a hit:

| pair as printed in `final_classes.txt` | round-3 bound | round-4 bound |
|---|---|---|
| `BBAAbaa,BBabABA` | 23 | 25 |
| `BBABAba,BBaabAA` | 22 | 25 |
| `BBAbbaa,BAAbAba` | 22 | 25 |

AC-19 is described in its own paper as a dataset of AC-trivial presentations, so membership is that paper's assertion that the row is AC-trivial. The assertion rests on how the dataset was generated rather than on a per-row certificate, since the dataset also contains rows their own solver did not solve. Even so, 41 of the 44 inclusions in our ledger have already been confirmed by our own searches, so the evidence favours AC-19 here too. If so, the reason our engine misses them is the gap that round 4 named in Section 8 of `directions/resisters`: the twelve-move system excludes left multiplication `x_i -> x_j x_i` and multiplication by an inverse relator `x_i -> x_i x_j^-1`, which are reachable only through longer intermediates. These three rows are the natural first targets for direction H3, and each of them is a single explicit certificate away from settling.

### 8.3 F2 and F3: two documentation discrepancies in the third-party data

`AC19_extended.txt` has 156,762 rows but only 156,753 distinct canonical forms, so nine rows are Sigma-duplicates of other rows. The paper's figure of 156,762 is the row count and is correct as a row count.

The abstract and Section 3 of arXiv:2606.21611 say that AC-19 consists of 125,192 presentations. The released `AC19.txt` has 140,535 rows, so the figure in the paper under audit is the one that matches the released file, and the difference is inside the primary source.

There is a second, smaller documentation discrepancy. `AC19_extended.txt` contains 140,874 rows of length at most 19, and 510 of those are among its first 634 benchmark lines. The ACSolverX README says that `AC19.txt` is the extended file with the first 634 lines removed and then filtered to length at most 19, which would leave 140,364 rows. The released file has 140,535 rows, which is 171 more. The audit uses the file as released, and its conclusion is unaffected.

### 8.4 F4: the move set is pinned by the counts

The substitution definition admits `i` in both relators, and Appendix A of arXiv:2606.21611 remarks that with the canonical form only appending `r_2` to `r_1` is needed. Read literally with the canonical form, the one-sided generator loses moves. From `AK(3)` the one-sided generator gives first-move energies of 16 and 18 and 19 successors, where the two-sided generator gives 15, 16, 17 and 18 and 38 successors. The published counts are reproduced only by the two-sided generator, which is the one in the definition.

### 8.5 F5: the exhaustiveness of our own table

At total length 12 our table has 4,392 AC-trivial Sigma-classes, at 13 it has 18,076 and at 14 it has 31,372. AC-19 has 329, 1,273 and 1,525 rows at those lengths, and 3,127 of our 54,068 rows in total appear in AC-19. So AC-19 is a selected subset of the AC-trivial presentations of length at most 19 and not the whole of them. The phrase "exhaustive enumeration" in the source has to be read relative to whatever normalisation their generator used, and the same holds for the paper's sentence that the length-14 stratum has never been exhaustively classified: that sentence is true of the public record and false with respect to `directions/c14/final_classes.txt`, which is ours and unpublished at the paper's date.

### 8.6 F6: the standard tuple is a sink of the GS graph, and the three rows are one automorphism orbit

Two structural facts came out of trying to use the GS graph on the three rows of F1.

First, the canonical standard tuple `((-2,), (-1,))` has no outgoing substitution move at all, so its peak-bounded reachable set is a single state at every cap. The reason is elementary: the two relators are single letters, a substitution replaces one by a product whose junction is that letter against the other, and a letter is never the inverse of a different letter, so the cancellation condition fails. Consequently a GS search for a trivialisation must land on the standard tuple exactly, and the paper is right to present its §5 theorem as a statement about the substitution graph and not as a bound on trivialisation distance.

Second, the three undecided rows of F1 are three distinct Sigma-classes but one orbit under signed permutations of the generators, which is why their peak-bounded components have identical sizes (31, 73, 162 and 340 states at caps 18, 19, 20 and 21). None of the three reaches the standard tuple in the GS graph at peak 21 or below, which is a bounded negative about a graph much sparser than the AC graph and is not comparable with the campaign's twelve-move bounds of 22 and 23.

## 9. What I could not verify, and what remains uncertain

The Prover9 and E negative results in Section 6 were not checked, because neither prover is installed and the paper's own logs are the only evidence.

The sigma-pilot sweep in Section 7 was not rerun. It is stated in the paper as engine-relative, and the paper itself says the full sweep is future work.

The capacity-28 budget stop and its partial counts of 5,640,276 and 1,987,856 were not reproduced. The paper reports that its own run reached a 40-million-state budget without finishing, and I did not attempt that level.

The engine-relative character of the theorem is load-bearing and the paper states it clearly. These are statements about the substitution graph, not about elementary AC paths. In particular the 19 does not bound elementary peaks: my own barrier-19 path expands to an elementary peak of 26, and the paper's expands to 24.

My C enumerator identifies states by exact stored bytes, so no hash collision can merge two states. The numbers are therefore exact counts of the graph I generate, and the agreement with nine independently published state counts is the evidence that my graph is the paper's graph.

The 44 overlaps in F1 are exact set intersections under the canonical form, and I checked one of them by hand: our row `BABaba,BBBaBaa` is the pair (y^-1 x^-1 y^-1 x y x, y^-3 x y^-1 x^2), and the AC-19 row with 0-based index 106191 is the same pair in the other order. What remains uncertain is the direction of the inference: whether AC-19 is right about the three undecided rows, and if it is, whether the missing move forms or a higher cap is what closes them.

## 10. Exact commands

Third-party inputs are fetched by `fetch_sources.sh`, which downloads the two e-prints from arXiv and three files from the ACSolverX repository into `sources/twohump`, `sources/audited` and `sources/ac19`. The sha256 values I used are recorded below.

    python3 sublevel.py                       # caps 13 to 19, then the bottleneck path
    python3 verify_path.py path_19.json       # second checker, then elementary expansion
    python3 ../c14/carreras/replay_carreras.py gs19_elementary_cert.json
    python3 parse_table.py
    python3 sigma_pairs.py
    python3 fingerprints.py
    python3 cert_table.py
    python3 ac19_audit_mine.py
    python3 crosscheck.py          # needs AC19_DIR and OUR_TABLE_DIR (defaults: ../sources/ac19, ../c14)
    python3 resisters_in_ac19.py   # same two variables
    gcc -O2 -o gsbox gsbox.c
    ./gsbox 24 3 111YYYY:121YXY X221YYY:XXXY112 X221YYY:XXXY11Y      # 210 s,  389 MB
    ./gsbox 25 3 111YYYY:121YXY X221YYY:XXXY112 X221YYY:XXXY11Y      # 967 s,  541 MB
    ./gsbox 26 3 111YYYY:121YXY X221YYY:XXXY112 X221YYY:XXXY11Y      # 1959 s, 792 MB

The `gsbox` words use `1` for x, `2` for y, `X` for x^-1 and `Y` for y^-1. `run_all.sh` runs the cheap checks and, with the argument `big`, the three enumerations.

Recorded sha256 values (2026-11-05):

    AC19.txt                   f72df134e4deca4cb9c040099b6e09b2b45516f9aa460fc460a120669f1f1e19
    AC19_extended.txt          d028cd4d54f9204be8b2d811f9b6d428bc2920fa83a0e2143a32ad52f55660c0
    1190MS.txt                 81323166e956b35e3c816fccdcad3507e7978d6291da13bfda6a45de5763cdf2

## 11. Where this lives and how to rerun it

The deliverable is the directory `directions/carreras-minimax/` of this repository. Run `sh run_all.sh` there for every check that takes less than a minute in total, and `sh run_all.sh big` to add the three enumerations at caps 24, 25 and 26 (about 52 minutes of single-core time, 792 MB peak). `sh fetch_sources.sh` downloads the third-party inputs into `sources/` and prints the hashes recorded in `sources/PROVENANCE.md`. The two AC-19 data files are 22 MB and 25 MB, so they are fetched rather than stored; the two table sources from the Two-Hump e-print are stored, because they are small and the sigma-program check depends on them.

## 12. Files

`gs.py`, `gs2.py`: words, canonical forms, the GS graph, bottleneck Dijkstra and peak-bounded reachability.
`gsbox.c`: the C enumerator.
`verify_path.py`: the brute-force second checker and the expansion to elementary moves.
`sublevel.py`, `cert_table.py`, `parse_table.py`, `sigma_pairs.py`, `fingerprints.py`, `ac19_audit_mine.py`, `crosscheck.py`, `resisters_in_ac19.py`, `sink_and_orbits.py`: the audit scripts.
`path_19.json`: the barrier-19 path.
`gs19_elementary_cert.json`: the 266-move elementary certificate derived from it.
`outputs/`: the run logs quoted above.
`resisters_in_ac19.txt`: the 44-row overlap list, with the 0-based row index of the matching `AC19.txt` row.
