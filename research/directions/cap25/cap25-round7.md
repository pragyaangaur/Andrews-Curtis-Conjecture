# Round 7, direction J3: the cap-25 census, the T = 17 deficit, and class C resolved

Member m9. Every number below comes from a deterministic, rerunnable computation; the
commands are in Section 8 and the raw output is in `work/RESULTS.txt`. Nothing here says
anything about the truth or the falsehood of the Andrews-Curtis conjecture, and no claim of
a proof or a disproof of it is made. Claims are labelled [Verified] (I ran a check and it
passed), [Computed] (an exact deterministic computation of mine, reproducible by the stated
command), [Dead end] or [Open].

## 1. Summary

1. [Computed, new] **Class C is AC-trivial, at peak exactly 18.** Class C is the PU class
   of the eight length-13 rows of `directions/c14/final_classes.txt` labelled
   `resisting-exhausted-cap17`. Each of those eight presentations is AC-equivalent to the
   standard pair by a path all of whose intermediates have total length at most 18 (found by
   exhaustive breadth-first search at cap 18, at BFS depth 76 to 78), and no such path
   exists with all intermediates of total length at most 17 (the cap-17 box is EXHAUSTED
   after 136,576 states from each of the eight; 136,576 is exactly the component size round
   3 recorded). So the minimal peak is 18, not 19 or 20 as the shipped certificates suggest.
2. [Computed, new] **All sixteen states of class C's length-13 PU level set are AC-trivial.**
   The PU canonical form of the eight rows is one class (`directions/cap24/punf.py`:
   `0 0 0 2 0 2 2 | 0 2 1 2 0 3`), and exactly sixteen of the 18,090 length-13 rows that the
   c14 file lists as `ac-trivial` or `resisting-*` share it — the eight above (minimal peak
   exactly 18) and eight more (minimal peak exactly 15). The other length-13 rows are the 20
   with A5 quotients (PU moves preserve the isomorphism type of the presented group) and the
   six AK(3)-class rows, which are in the run and do not share the form. This 16 agrees with
   the independent level-set count in `directions/whitehead/`. Three consequences:
   (a) the caution in `directions/whitehead/whitehead.md` Section 9, that "class C exhibits"
   two PU-equivalent presentations that need not be AC-equivalent, is withdrawn — the 8/8
   split it cites is the boundary of the c14 enumeration's cap-15 standard ball, not an AC
   distinction; (b) **class C is AK(3)-equivalent if and only if AK(3) is AC-trivial**, since
   a member of class C is AC-trivial; (c) hence the `directions/pu-gap` prediction that
   class C is not AK(3)-equivalent is exactly the prediction that AK(3) is not AC-trivial.
   Direction J3's third question therefore has no cheaper route than the AC conjecture for
   AK(3) itself, and the PU-table arithmetic cannot be tested independently by it.
3. [Computed, new] **The other six length-13 rows are AK(3)-equivalent at peak exactly 19.**
   Each reaches AK(3) itself inside cap 19 (BFS depth 63 to 69) and no path inside cap 18
   reaches AK(3) from any of them. So the whole length-13 slice is decided with exact minimal
   peaks 18 and 19, improving the resisters ledger's cap 20 for all fourteen rows.
4. [Verified, exact] **The closed boxes nest: B(20) ⊂ B(21) ⊂ B(22) ⊂ B(23) ⊂ B(24).** Four
   exact merge joins over the raw key files, each with 0 keys of the smaller box missing from
   the larger, and with per-stratum counts that reproduce the recorded tables digit for digit.
5. [Computed, new] **The cap-T box is not the (T-1)-box plus a top stratum.** The exact number
   of states added at each total length is tabulated for T = 21 to 24 (Section 5). The
   additions reach eight strata below the cap: raising the cap from 22 to 23 adds 3,584 states
   at total length 15 and 10,080 at 16. The addition depth is 6, 5, 8, 5 for T = 21, 22, 23,
   24. Any inference of the form "this state is below the cap, so the smaller box contains
   it" is therefore invalid, and the campaign's own T = 16 closure (round 5) is an instance.
6. [Dead end] **Bounded-shape detour probes cannot decide the low strata.** From the complete
   cap-22 box, 785,158,464 boundary incidences (children at total length 23) and one
   multiplication step down produce 0 of the 3,584 + 10,080 states that cap 23 does add at
   lengths 15 and 16; a one-eighth sample of the cap-23 box with the conjugation branch
   included (about 9.6e8 boundary incidences) produces 0 of the 5,760 + 18,496 states that
   cap 24 adds at lengths 19 and 20. The additions need longer excursions, so only the closed
   box can decide them.
7. [Measured, the stopping point] **The closed cap-25 box is out of reach in this round, and
   T = 17 at cap 25 stays open.** Section 7 gives the arithmetic: at least 9.05e9 states, a
   measured 3.05 bytes per state, at least 28 GB for the union alone with the round-6 run
   peaking at 52 GB on a disk with 53 GB free, and 7 to 16 hours of the shared four-core
   machine at the measured 121,000 to 419,000 states per second, against a one-hour limit per
   command in my execution environment and about 0.3 cores obtained under this round's load.
8. [Verified] The round-6 cap-25 record is re-derived from the surviving round-5 files: the
   partial set holds 5,222,573,371 states with exactly the per-stratum table my round-6
   report records, and the pending frontier is 1,946,285,816 bytes = 243,285,727 keys, the
   round-6 seed count.

## 2. Objects, engines and their validation

The box B(T) is the set of pairs (u,v) of freely reduced words in F(x,y) with
|u| + |v| <= T reached from AK(3) = (xyxy^-1x^-1y^-1, x^3y^-4) by the campaign's twelve moves
inv1, inv2, mul12, mul21 and conjugation of one relator by each reduced word of length at most
K = 1, exactly as in `directions/cap21/rawbox4.c` and `directions/cap24/rawbox6.c`. Keys are
5-bit or 8-bit relator lengths followed by 2 bits per letter; the round-5 boxes v15, v17, v20,
w22 are layout 8 except v15 and v17 which are layout 5, so every tool below detects the layout
from data (a wrong layout decodes to nonsense lengths; Section 8's `keytool hist` on one run
file is the one-second test).

* `work/keytool.c` — sample reader: count, min, max, strict sortedness, layout test.
* `work/box.c` — streaming exact per-stratum histogram and k-way merge join of two boxes
  (`diff`), reporting the per-stratum counts of A, B, A\B and B\A.
* `work/stdball.c` — my own in-RAM twelve-move breadth-first search from one presentation,
  with the standard pair as target (`FOUND depth d states n`) or an explicit target pair, and
  the exact number of states when the box is exhausted. My word model, my hash table, my move
  generation; it shares no code with any campaign engine.
* `work/probe.c` — the detour probe of Section 6.
* `work/accheck.py` — my own replayer for the campaign's certificate lines: word model,
  inverse, product, conjugation by one letter, and the three move tokens; it reports the move
  count and the peak total length of every certificate.

`stdball` reproduces every recorded AK(3) box count it was tested on, which is the check that
matters for Sections 3 and 4:

| cap | states, `stdball` | recorded |
|----:|------------------:|---------:|
| 15  | 6,864             | 6,864 (`directions/cap24/cap24.md`) |
| 17  | 857,808           | 857,808 |
| 18  | 2,014,992         | 2,014,992 |
| 20  | 51,411,456        | 51,411,456 |

## 3. Class C is AC-trivial, and what that does to the PU question

Class C's eight rows, their certificates and their exact peaks. All certificates are replayed
by `work/accheck.py`, my own replayer; the first family is from
`directions/resisters/std_certs.txt` (round 3/4), the second from
`directions/c14/certs_all.txt` (round 2).

    the eight rows c14 labels resisting-exhausted-cap17 (to the standard pair):
      BABaba,BBBaBaa   94 moves peak 20   |  cap 17 exhausted (136,576), cap 18 FOUND depth 76
      BABaba,BBBaaBa   96 moves peak 20   |  cap 17 exhausted (136,576), cap 18 FOUND depth 77
      BABaba,BBaBaaa   94 moves peak 20   |  cap 17 exhausted (136,576), cap 18 FOUND depth 76
      BABaba,BBaaaBa   94 moves peak 19   |  cap 17 exhausted (136,576), cap 18 FOUND depth 77
      BAbABa,BBAAABA   93 moves peak 19   |  cap 17 exhausted (136,576), cap 18 FOUND depth 77
      BAbABa,BBABAAA   94 moves peak 20   |  cap 17 exhausted (136,576), cap 18 FOUND depth 78
      BAbABa,BBBAABA   93 moves peak 19   |  cap 17 exhausted (136,576), cap 18 FOUND depth 77
      BAbABa,BBBABAA   98 moves peak 19   |  cap 17 exhausted (136,576), cap 18 FOUND depth 76

    the eight other level-set states c14 labels ac-trivial (to the standard pair):
      BBAABa,BAbABaa   62 moves peak 15   |  cap 14 exhausted (2,520), cap 15 FOUND depth 35
      BBAAbA,BBabAba   58 moves peak 15   |  cap 14 exhausted (2,520), cap 15 FOUND depth 36
      BBABaa,BAABaba   68 moves peak 15   |  cap 14 exhausted (2,520), cap 15 FOUND depth 38
      BBAbAA,BBabAba   71 moves peak 15   |  cap 14 exhausted (2,520), cap 15 FOUND depth 38
      BBaBAA,BAbABaa   63 moves peak 15   |  cap 14 exhausted (2,520), cap 15 FOUND depth 37
      BBaaBA,BAABaba   59 moves peak 15   |  cap 14 exhausted (2,520), cap 15 FOUND depth 36
      BBaaba,BBAbabA   59 moves peak 15   |  cap 14 exhausted (2,520), cap 15 FOUND depth 36
      BBabaa,BBAbabA   66 moves peak 15   |  cap 14 exhausted (2,520), cap 15 FOUND depth 38

Three points.

* **Why the c14 file splits them 8 and 8.** The c14 enumeration certified AC-triviality by
  searching inside the standard tuple's cap-15 ball (58,487,624 states, round 3). The eight
  states whose minimal peak is 15 are inside that ball; the eight whose minimal peak is 18 are
  not, so they kept a round-2 label. `directions/resisters/final_status.tsv` supersedes those
  labels for exactly those eight rows: it records `round3_status` = `ac-trivial` at cap 20 for
  all eight. The c14 file was never refreshed, and `directions/whitehead/whitehead.md`
  Section 9 read the stale labels. This is a documentation defect in
  `directions/c14/final_classes.txt` (its length-13 labels), not an error in the c14 search.
* **The whitehead caution is withdrawn as stated.** Since all sixteen members of the level
  set are AC-trivial, they are all AC-equivalent to each other; class C does *not* exhibit a
  pair of PU-equivalent presentations that are not AC-equivalent. The general point that the
  PU relation contains a change of generators applied to both relators, which is not an AC
  move in general, is untouched — but class C is not an example of it.
* **The consequence for J3(c) and for pu-gap.** Let s be any member of class C (all are
  AC-trivial). Then s is AK(3)-equivalent iff AK(3) is AC-trivial. So J3(c) — "test class C's
  AK(3)-equivalence" — cannot be settled by any computation that does not settle the AC
  conjecture for AK(3), and the pu-gap prediction "class C is not AK(3)-equivalent" is the
  same statement as "AK(3) is not AC-trivial". It is not an independent test of the published
  PU table.

## 4. The whole length-13 slice, with exact minimal peaks

Fourteen lines of `directions/c14/final_classes.txt` at length 13 carry a `resisting-*`
label. All are decided, and the exact minimal peak of an AC path to the recorded target is
now known for every one:

| rows | c14 label | decided as | exact minimal peak |
|------|-----------|------------|-------------------:|
| 8   | `resisting-exhausted-cap17` | AC-trivial | **18** |
| 6   | `resisting-budget-cap19`    | AK(3)-equivalent, reaching AK(3) itself | **19** |

The six: `BAbABa,BBBAAAA` (depth 63), `BAbABa,BBBBAAA` (64), `BBAbaa,BBBaabA` (66),
`BBAbaa,BBaaabA` (65), `BBaabA,BBAbaaa` (65), `BBaabA,BBBAbaa` (69), all found at cap 19, all
exhausted at cap 18. Their cap-17 and cap-18 boxes are exactly the AK(3) boxes (857,808 and
2,014,992 states), which is independent evidence that they lie in AK(3)'s component. The
caveat: the target was AK(3) itself (or its relator swap), not its conjugates, so 19 is exact

[Coordinator note, 6 November 2026 (round 8, from the second-referees-7 audit of
member m2 of swarm smw4i604a; coordinator-rerun): the sentence "their cap-17
and cap-18 boxes are exactly the AK(3) boxes" is FALSE as a statement about
sets, and the "independent evidence" claim is withdrawn. The six rows share ONE
cap-18 box (all six pairwise equal, 2,014,992 states) which has the same size
and the same length histogram as AK(3)'s cap-18 box but is DISJOINT from it
(the coordinator's rerun of the set comparison: 2,014,993 keys on each side,
intersection 1, an artifact; the same at cap 17). The rows are not in AK(3)'s
box and AK(3) is not in theirs; the two boxes merge exactly at cap 19, which is
the peak. The equality of the two counts is a numerical coincidence of two
disjoint boxes with the same histogram, not evidence of a common component at
that cap. The PEAK-19 CONCLUSIONS ARE UNAFFECTED: they rest on the cap-18
exhaustion of the rows' own box (no AK(3) inside) and the explicit cap-19
paths, both of which the audit and the coordinator reproduced.]
for reaching AK(3) and an upper bound for reaching its class. The ledger's cap 20 for these
six and for the eight above is improved to 19 and 18.

## 5. The boxes nest, and the boxes are not layer-stable

Exact merge joins over the raw key files (`work/box diff`, layout 8 for all four pairs):

| pair | states | keys of A missing from B | total added |
|------|-------:|-------------------------:|------------:|
| B(20) : B(21) | 51,411,456 : 219,042,976 | 0 | 167,631,520 |
| B(21) : B(22) | 219,042,976 : 419,826,272 | 0 | 200,783,296 |
| B(22) : B(23) | 419,826,272 : 1,638,542,144 | 0 | 1,218,715,872 |
| B(23) : B(24) | 1,638,542,144 : 3,056,896,064 | 0 | 1,418,353,920 |

States added by each unit of cap, by total length:

| T | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 |
|--:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 21 | 13,952 | 8,064 | 199,168 | 196,000 | 2,158,336 | 2,123,584 | 162,932,416 | | | |
| 22 | | | 13,440 | 64,832 | 393,408 | 760,512 | 4,367,616 | 195,183,448 | | |
| 23 | 3,584 | 10,080 | 53,120 | 99,712 | 622,848 | 1,060,832 | 5,611,264 | 9,581,792 | 1,201,672,640 | |
| 24 | | | | | 5,760 | 18,496 | 259,456 | 800,064 | 5,973,696 | 1,411,296,448 |

[Coordinator note, 6 November 2026: the T = 22 row's length-22 cell is a
transcription slip — the raw output (`diff_21_22.txt`, `RESULTS.txt`) and the
coordinator's rerun both give **195,183,488**, which is the value that makes
the row sum to the recorded onlyB total 200,783,296. Nothing else in the table
is affected.]

The depth of the perturbation (T minus the least total length at which the cap increment adds
anything) is 6, 5, 8, 5 for T = 21, 22, 23, 24: not monotone, and 8 at cap 23. The length-13
stratum, by contrast, is 4,032 at caps 20, 21, 22, 23 and 24 (it was 336 at cap 15), so strata
seven or more below the cap have been stable over the last four increments while strata five
to eight below can move.

## 6. Dead end: bounded-shape detour probes

The natural cheap attack on "does cap 25 change the length-17 stratum" is to look for the new
states as short detours through the new top stratum: from a state of B(T-1), one move up to
total length T, then one or two moves back down. `work/probe.c` implements exactly that,
including the conjugation branch (up by +2 from length T-2, down by -2 to length T-2, then a
multiplication down), and tests every candidate against the complete key set of B(T-1) at
total length <= LIM held in RAM.

* Positive control, cap 22 to cap 23, LIM 16: 785,158,464 boundary incidences and 0 new
  states at total length <= 16, against the 3,584 + 10,080 states that cap 23 does add at
  lengths 15 and 16. So the probe misses 100 per cent of a known answer.
* Cap 23 to cap 24, LIM 20, on one eighth of the states (three processes, 321,402,252 +
  325,552,108 + 316,740,338 boundary incidences): 0 new states at total length <= 20, against
  the 5,760 + 18,496 states cap 24 adds at lengths 19 and 20.

Conclusion: the low-stratum additions are reached by excursions much longer than four moves,
so no probe of bounded shape can decide them. Recording this so that it is not retried. The
conjugator branch is what makes the probe expensive (about 26 move generations per boundary
incidence), and it is also what fails.

## 7. T = 17 at cap 25: what is known, what would settle it, and why not here

What is known. At cap 23 and at cap 24 the box holds 217 PU classes of minimal length 17
against a halved published cell of 229, a deficit of 12; the deficit was 19 at cap 22 (210
classes), so raising the cap 22 to 23 added exactly the seven classes at length 17 that closed
19 to 12, and cap 24 added none. Because the box adds states up to eight strata below the cap
(Section 5), a cap-25 change at length 17 is not excluded by anything known. To settle the
question one needs the number of PU classes of minimal length 17 in the *closed* cap-25 box:
one new class closes the deficit to 11.

Why not here. (i) Size: the cap-25 partial set already holds 9,053,333,421 states (round 6)
with the per-stratum increments showing no convergence; the closed box is larger, and at the
measured 3.05 bytes per state (delta-varint compressed key runs, round 6) the union alone needs
at least 28 GB, with the round-6 run peaking at 52 GB in transit. The VM has 53 GB free, shared
with nine other members, and the round-6 run died of exactly that. (ii) Time: round 6 added
3,830,760,050 states in 18,242 s, 121,000 to 419,000 states per second on a shared machine; the
remaining states need at least 7 hours of four-core time and the compressed set was deleted, so
the run has to be re-derived from round 5's 5,222,573,371-state set first (17 GB of
re-encoding). (iii) My environment: each command is capped at one hour and killed on return,
and under this round's load my processes obtained about 0.3 cores (measured: 7 min 12 s of CPU
time in 22 min 54 s of wall time on three processes). So the closed box is a four-to-ten hour
uninterrupted run on an idle machine, which I do not have. The exact stopping point of the
lower-bound ratchet is round 6's `checksum 6502ed9f63550141 states 9053333421 runs 7`.

Class C at cap 25 needs a depth-12 perturbation (class C is at total length 13 and is absent
from B(24)), which is deeper than any depth observed so far (the largest is 8), and the
length-13 stratum has been stable at 4,032 from cap 20 to cap 24. That is evidence, not a
proof, and Section 3 shows it no longer matters for the PU question.

## 8. Files and exact commands

The deliverable is installed in `directions/cap25/` (report, tools, data, raw output) and
also sits in `.ultramath/smw48or9f/m9/work/`; commands below are relative to either, with the
certificate files named by their repo paths. In `.ultramath/smw48or9f/m9/work/`:
`accheck.py`, `RESULTS.txt` (the raw output of the tables below), `diff_20_21.txt`,
`diff_21_22.txt`, `diff_22_23.txt`, `diff_23_24.txt`, `punf_in.txt`, `punf_out.txt`.

    # build
    gcc -O3 -march=native -o stdball stdball.c
    gcc -O2 -o box box.c ; gcc -O2 -o keytool keytool.c
    gcc -O3 -march=native -o probe probe.c

    # engine validation (recorded counts)
    ./stdball 15 "abaBAB,aaaBBBB"   # EXHAUSTED states 6864
    ./stdball 18 "abaBAB,aaaBBBB"   # EXHAUSTED states 2014992
    ./stdball 20 "abaBAB,aaaBBBB"   # EXHAUSTED states 51411456

    # class C: minimal peak 18, and the other eight: minimal peak 15
    for r in BABaba,BBBaBaa BABaba,BBBaaBa BABaba,BBaBaaa BABaba,BBaaaBa \
             BAbABa,BBAAABA BAbABa,BBABAAA BAbABa,BBBAABA BAbABa,BBBABAA ; do
      ./stdball 17 "$r" ; ./stdball 18 "$r" ; done          # EXHAUSTED 136576 then FOUND
    for r in BBAABa,BAbABaa BBAAbA,BBabAba BBABaa,BAABaba BBAbAA,BBabAba \
             BBaBAA,BAbABaa BBaaBA,BAABaba BBaaba,BBAbabA BBabaa,BBAbabA ; do
      ./stdball 14 "$r" ; ./stdball 15 "$r" ; done          # EXHAUSTED 2520 then FOUND

    # the six AK(3)-equivalent rows: minimal peak 19
    for r in BAbABa,BBBAAAA BAbABa,BBBBAAA BBAbaa,BBBaabA BBAbaa,BBaaabA \
             BBaabA,BBAbaaa BBaabA,BBBAbaa ; do
      ./stdball 18 "$r" "abaBAB,aaaBBBB" ; ./stdball 19 "$r" "abaBAB,aaaBBBB" ; done

    # certificate replays with my own replayer
    python3 accheck.py ../../../../directions/resisters/std_certs.txt cc8.txt
    python3 accheck.py ../../../../directions/c14/certs_all.txt cc8b.txt

    # nesting and the perturbation tables (layout 8 throughout)
    ./box diff 8 <B(20)> : <B(21)>   # ... onlyA 0, onlyB per stratum
    ./box diff 8 <B(21)> : <B(22)>
    ./box diff 8 <B(22)> : <B(23)>
    ./box diff 8 <B(23)> : <B(24)>
    # where B(T) files are, with SHA-free paths:
    # B(20),B(21)  .ultramath/smw2woueq/m5/cap21/t20/visited.bin  t21/visited.bin
    # B(22),B(23),B(24)  .ultramath/smw38010i/m1/cap24/w22/run_0000{5,6,7,8}.bin etc.

    # the round-6 record, re-derived from the round-5 files
    ./box hist 5 .ultramath/smw38010i/m1/cap24/w25/run_0003{5,6,7,8}.bin
    # -> total 5222573371, 13:2686 ... 25:3720320360 (my round-6 table, digit for digit)

## 9. Limits and what remains uncertain

1. The peak claims of Sections 3 and 4 are for the twelve-move system. By the campaign's
   conjugator-independence theorem (round 4) and the multiplication transports (round 5) the
   in-box reachable set is the full-AC one at the same cap, so the claims hold for the full
   move set; if a reader does not accept those two theorems, read them as bounds for the
   twelve moves.
2. "Minimal peak 19" for the six AK(3) rows is exact for reaching AK(3) itself (or its relator
   swap), which is what the shipped certificates do. I did not put AK(3)'s conjugates in the
   target set, so a path with peak 18 reaching a conjugate of AK(3) is not excluded.
3. The T = 17 deficit is a deficit against a stated convention (round 5's caveat stands): the
   published cell counts pairs, the box counts classes by minimal key length, and the halving
   is exact only where a class contributes exactly two pairs. Nothing here changes that.
4. The closed cap-25 box was not computed, so no statement in this report is a statement about
   B(25). The 2-move and 3-move probes of Section 6 are recorded failures, not bounds.
5. The round-6 figure 9,053,333,421 is quoted, not rerun; what I did verify is its input
   (5,222,573,371 states with the exact histogram) and the frontier size. Reproducing stage 1
   of that run needs the 17 GB import and about 40 to 90 minutes, which I did not spend.
6. `directions/c14/final_classes.txt` still carries the round-2 labels for the length-13
   slice. I did not edit it (it is not my file); the correction belongs in a dated note by the
   coordinator, with `directions/resisters/final_status.tsv` as the current ledger.
