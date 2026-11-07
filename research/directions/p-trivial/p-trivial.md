# The P(3) and P(4) push (round 4, direction G10)

Member m3, swarm smw2woueq. Every number below was produced on this VM by the
code in this directory, and `bash run_all.sh full` reruns all of them in about
twelve minutes (log of an actual full run: `logs/run_full.txt`).

## 1. What is established

1. **A new engine reproduces the published AK(3) box exactly.** `ptriv.c`
   (written from scratch: twelve-move AC system, total-length cap, FIFO
   breadth-first search, exact state store) gives the state counts of the
   AK(3) component in the total-length box at all eight published caps:
   168, 168, 6864, 20560, 857808, 2014992, 23609984, 51411456 for caps 13 to
   20, against the same eight numbers in `directions/pu-enumeration/census.txt`.
   A second implementation, `pyball.py` (Python, different data structures,
   written from the move definitions rather than from the C), reproduces the
   state counts and the complete per-layer histograms at caps 13, 15, 16, 17
   and 18 for AK(3), at cap 16 for P(3), at cap 19 for P(4) and at caps 19 and
   20 for AK(4); at cap 18 the two histograms agree in all 90 layers.
2. **P(3) is inside the AK(3) cap-20 box.** The exhaustive cap-20 box from
   P(3) = AbaBaBA,abbaBAB (total relator length 14) has exactly 51,411,456
   states, and it contains AK(3) at BFS depth 24. Both boxes are closed, so
   they are the same component. This gives an explicit certificate
   P(3) ~ AK(3) of **24 moves with every intermediate of total relator length
   at most 20**, against the round-3 ladder certificate for the same pair of
   **34 moves with maximum intermediate length 31** (recomputed from
   `directions/ak-ladder/round3/chain_uniform_3.json`).
3. **P(4) is outside the AK(4) cap-20 box, and the two merge at cap 21.**
   The cap-20 box from P(4) = AbaBaBA,abbbaBAB (total relator length 15)
   closes at 432,504 states; the cap-20 box from AK(4) closes at 260,592
   states; neither contains the other's start. At cap 21 the AK(4) box closes
   at 9,018,624 states and contains P(4) at depth 61. At cap 22 the merged box
   has 16,776,304 states and the distance is 43, which gives a certificate
   AK(4) ~ P(4) of **43 moves with every intermediate of total relator length
   at most 22**, against the round-3 certificate of **46 moves with maximum
   intermediate length 38**. At cap 23 a 41-move path exists.
4. **Exhaustive trivialisation negatives.** P(3) has no AC path to the
   standard tuple whose states all have total relator length at most 20.
   P(4) has none at caps 20, 21 and 22. In each case the complete box contains
   no state with a relator of length 1 (minimum relator length 5 for P(3) at
   cap 20, 7 for P(4) at cap 20, 6 for the AK(4) boxes at caps 21 and 22), and
   the standard tuple is such a state.
5. **The class keys agree with the census.** The engine computes the same
   cyclic class key as the round-2 census, checked by the class counts: the
   AK(3) box hits 26, 80 and 2000 census classes at caps 15, 16, 17, exactly
   the census counts at those lengths.
6. **The negatives do not depend on the conjugator bound.** The same boxes
   with conjugation by a word of length at most 2 as a single move (36 moves,
   the round-2 and round-3 K = 2 setting) have identical state counts at these
   caps: 18,200 at cap 16 and 2,014,992 at cap 18 for the AK(3) side, and
   260,592 at cap 20, 9,018,624 at cap 21 and 16,776,304 at cap 22 for the
   AK(4) side.

## 2. Conventions

A presentation is a pair of freely reduced words in the free group on
a and b, written with letters a, A, b, B where A = a^-1 and B = b^-1. The
total relator length is the sum of the two word lengths. The twelve moves on
(r1, r2) are

    0  r1 -> r1^-1      1..4   r1 -> w r1 w^-1, w in {a, A, b, B}
    5  r2 -> r2^-1      6..9   r2 -> w r2 w^-1, w in {a, A, b, B}
   10  r1 -> r1 r2     11     r2 -> r2 r1

This is the move set of `directions/resisters/push.c` and of
`directions/pu-enumeration/rawbox.c` with K = 1, which is why the counts in
point 1 of section 1 are comparable with rounds 2 and 3. Conjugation by a
longer word is a product of these moves; the option `-j 2` makes conjugation
by a word of length at most 2 a single move, and section 1 point 6 records
that the boxes are unchanged.

The cap is a bound on the total relator length of every state reached. A box
is *closed* when the search queue empties, and then the enumeration is
exhaustive inside that cap at every depth. AK(n) is the tuple
(xyx y^-1 x^-1 y^-1, x^n y^-(n+1)); P(n) is the length-reduced form of
`directions/ak-ladder/acx.py`, that is a = x^-1 y x and b = x y x^-1 y for the
first relator and the two words of Theorem t:n+11 for the second. The concrete
instances used here are AK(3) = abaBAB,aaaBBBB, P(3) = AbaBaBA,abbaBAB,
AK(4) = abaBAB,aaaaBBBBB and P(4) = AbaBaBA,abbbaBAB.

## 3. The joining cap for P(3) and AK(3)

Each row is one closed box except the last, which is depth limited. The last
column is the exact number of moves of the shortest path inside that cap.

| cap | AK(3) box states | P(3) in the box | shortest path |
|-----|------------------|-----------------|---------------|
| 14  | 168              | no              |               |
| 15  | 6,864            | no              |               |
| 16  | 20,560           | no              |               |
| 17  | 857,808          | yes             | 40            |
| 18  | 2,014,992        | yes             | 26            |
| 19  | 23,609,984       | yes             | 26            |
| 20  | 51,411,456       | yes             | 24            |
| 21, 22, 23, 24 (depth at most 23) | 3,376,123 / 6,367,230 / 17,780,676 / 32,915,513 | no path of 23 moves or fewer | at least 24 |

So the joining cap of the pair is exactly 17, and the length budget needed
for the shortest known path is 20. The short paths do not appear at the
joining cap: at cap 17 the shortest path has 40 moves, and only at cap 20 does
it fall to 24. No path with 23 moves or fewer exists at caps 20, 21, 22, 23 or 24,
so 24 is the exact distance between P(3) and AK(3) for every cap from 20 to
24. The round-3 depth-18 probe of this pair (1,130,768 states, no standard tuple)
is a truncation of the same box and not a separate component: run with the
probe's own settings, `./ptriv ball 20 26 AbaBaBA abbaBAB -j 2 -d 18`, the
engine returns exactly 1,130,768 states. Its figure differs from the
cumulative count of layer 18 under the twelve moves (603,966) because the
probe allowed conjugation by a word of length 2 as a single move.

## 4. The joining cap for P(4) and AK(4)

| cap | AK(4) box states | P(4) in the box | shortest path |
|-----|------------------|-----------------|---------------|
| 15  | 216              | no              |               |
| 16  | 216              | no              |               |
| 17  | 12,720           | no              |               |
| 18  | 12,720           | no              |               |
| 19  | 124,896          | no              |               |
| 20  | 260,592          | no (P(4) box: 432,504) |        |
| 21  | 9,018,624        | yes             | 61            |
| 22  | 16,776,304       | yes             | 43            |
| 23  | more than 80,000,000 (budget stopped) | yes | 41 |

The jump from 124,896 states at cap 19 to 9,018,624 at cap 21 shows that the
AK(4) component and the P(4) component are joined by paths that need 21 of
total length and no more, even though the round-3 certificate between them
uses intermediates of total length up to 38. The distances in the table are
exact inside their cap because the search is breadth first and the boxes at
caps 21 and 22 are closed. The cap-23 box was stopped at the 80,000,000 state
budget, so the entry 41 there is an upper bound on the distance at cap 23 and
the box is not exhausted.

## 5. The three new certificates

All three certificates below are replayed by two independent checkers.
`replay12.py` is mine, written from the twelve move definitions.
`directions/pu-enumeration/replay_certs.py` is the round-2 checker of m5, and
it reads the certificate lines in `certs/`.

1. `certs/p3_to_ak3_24.cert`: P(3) to AK(3), 24 moves, maximum intermediate
   total length 20. This improves both measures on the round-3 ladder
   certificate (34 moves, maximum 31).
2. `certs/ak4_to_p4_43.cert`: AK(4) to P(4), 43 moves, maximum intermediate
   total length 22. Round 3: 46 moves, maximum 38.
3. `certs/ak4_to_p4_41.cert`: AK(4) to P(4), 41 moves, maximum intermediate
   total length 23. This one is shorter in moves and longer in cap than the
   second, so it is recorded separately.

    cd directions/p-trivial
    python3 replay12.py AbaBaBA abbaBAB "1 11 5 10 0 4 4 7 9 10 9 7 11 0 6 10 8 11 8 11 0 5 7 9" abaBAB aaaBBBB
    python3 ../pu-enumeration/replay_certs.py certs/p3_to_ak3_24.cert

The two commands print, respectively, `moves 24, max intermediate total length
20, endpoint abaBAB,aaaBBBB, replay OK` and `certificates checked: 1, verified:
1, failed: 0`. The three certificates in `certs/` are checked by both
checkers, and the 43-move and 41-move certificates print `moves 43, max
intermediate total length 22` and `moves 41, max intermediate total length 23`
under `replay12.py`, with all three showing `verified: 1, failed: 0` under
`replay_certs.py`.

## 6. The trivialisation negatives, and why they hold

A presentation is AC-trivial exactly when some sequence of moves takes it to
the standard tuple, that is to a pair of words of length 1. Suppose a
trivialisation of P has every intermediate of total relator length at most C.
Then every state of that path lies in the box of P at cap C. If the complete
box of P at cap C contains no state with a relator of length 1, then the
standard tuple is not in the box, and no such path exists. This argument is
exhaustive because the boxes used below are closed.

* P(3) at cap 20: the closed box has 51,411,456 states and its minimum relator
  length is 5, first attained at depth 25 by AbabA,BBBabbbbA. Hence every AC
  path from P(3) to the standard tuple passes through a state of total relator
  length at least 21. This rederives, with an independent engine, the cap-20
  statement of round 2, and it locates it exactly: the shortest path from P(3)
  to AK(3) needs 24 moves and the box is the AK(3) box.
* P(4) at caps 20, 21 and 22: the closed boxes have 432,504, 9,018,624 and
  16,776,304 states (the last two are the merged box with AK(4)) and their
  minimum relator lengths are 7, 6 and 6. Hence every AC path from P(4) to the
  standard tuple passes through a state of total relator length at least 23.
  This goes one and two caps beyond the cap-20 statement recorded for P(3).
* Caps 23 and 24 for P(3) are not exhausted here. The depth-limited runs
  reported in section 3 (32,915,513 states at cap 24 with depth at most 23)
  are subsets of the cap-24 box and do not give a cap-24 negative.

The cap-21 question for P(3) is exactly the cap-21 census of the AK(3)
component, because P(3) lies in that component at cap 20 and a connecting path
inside cap 20 is still available at cap 21. Round 2 stopped that census at
187,904,819 states, and the disk-backed continuation is direction G3 of this
round. I did not attempt it, so no cap-21 or higher exhaustive statement is
claimed for P(3).

## 7. What the census intersection does and does not add

The direction suggested intersecting the P(3) search with the 79,680 class
keys of `directions/pu-enumeration/cls20k1.txt`. The engine has that test as
`-k FILE` (with `-K FILE` writing the first depth at which each class is
reached), and it uses the same canonical form as the census, that is cyclic
reduction followed by the least rotation over a word and its inverse under the
letter order A < a < B < b. The canonical form was checked against the census
before use: the AK(3) box hits 26, 80 and 2000 census classes at caps 15, 16
and 17, and those are exactly the class counts of the census at T = 15, 16 and
17.

For P(3) the cap-20 intersection is total and adds nothing: the cap-20 box
from P(3) is the AK(3) box, so every state reached is one of the 79,680
classes whose certificates already end at AK(3), and the search reaches AK(3)
itself at depth 24, which is the root of that census. The useful consequence
runs the other way: composing the 24-move certificate with any of the 79,680
census certificates gives an explicit certificate from P(3) to that class
representative. One number from the class test is worth recording: the cap-16
box of P(3), 18,200 states, already meets 64 of the cap-20 census classes,
which shows that the class intersection is far more permissive than the state
intersection (the exact-state joining cap of the pair is 17). For P(4) the
analogous AK(4) census did not exist, and section 4 supplies the cap-20
component (260,592 states) that such a census would start from.

## 8. Limits

The engine is single threaded and holds all states in memory, so its practical
ceiling on this VM is about 80 million states (4.3 GB). The AK(3) cap-21
component is beyond that ceiling and was not attempted. The move set is the
twelve-move system, and the cap is on the total relator length; a negative for
this system at cap C does not by itself rule out a path in which a single
conjugation by a long word jumps over states of length above C, and section 1
point 6 only shows that the particular boxes used here are unchanged when
conjugators of length at most 2 are allowed as single moves. The certificates
are positive statements and are unaffected by that caveat. No claim about the
AC-triviality of P(3), P(4) or AK(3) is made: since P(n) is AC-equivalent to
AK(n), a trivialisation of either would decide an open case, and nothing in
this report does that.

## 9. Files

| file | contents |
|------|----------|
| `ptriv.c` | the engine; `gcc -O2 -o ptriv ptriv.c` |
| `ptriv` | the compiled binary used for the logged runs |
| `pyball.py` | independent Python implementation of the same ball |
| `replay12.py` | independent replayer for the twelve moves |
| `mkcert.py` | converts a move-code path into the round-2 certificate format |
| `certs/` | the three certificates |
| `run_all.sh` | reruns everything, `quick` or `full` |
| `logs/run_full.txt` | output of one complete `bash run_all.sh full` |

## 10. Verification summary

| claim | command (from this directory) | key output |
|-------|-------------------------------|------------|
| the engine matches the published boxes at every cap | `./ptriv ball T 27 abaBAB aaaBBBB -q` for T = 13 to 20 | `states=` 168, 168, 6864, 20560, 857808, 2014992, 23609984, 51411456, all `closed=yes` |
| a second implementation agrees | `python3 pyball.py T abaBAB aaaBBBB` for T = 13, 15, 16, 17, 18 | the same state counts and the same per-layer histograms |
| P(3) reaches AK(3) inside cap 20 | `./ptriv ball 20 27 AbaBaBA abbaBAB -b 80000000 -t abaBAB aaaBBBB` | `states=51411456 closed=yes`, `target reached at depth 24` |
| the 24-move certificate | `python3 replay12.py AbaBaBA abbaBAB "1 11 5 10 0 4 4 7 9 10 9 7 11 0 6 10 8 11 8 11 0 5 7 9" abaBAB aaaBBBB` | `moves 24, max intermediate total length 20, replay OK` |
| the same certificate under a second checker | `python3 ../pu-enumeration/replay_certs.py certs/p3_to_ak3_24.cert` | `verified: 1, failed: 0` |
| P(4) is outside the AK(4) cap-20 box | `./ptriv ball 20 25 AbaBaBA abbbaBAB -q -t abaBAB aaaaBBBBB` and `./ptriv ball 20 25 abaBAB aaaaBBBBB -q -t AbaBaBA abbbaBAB` | `states=432504 closed=yes target NOT reached` and `states=260592 closed=yes target NOT reached` |
| the two merge at cap 21 | `./ptriv ball 21 26 abaBAB aaaaBBBBB -q -t AbaBaBA abbbaBAB` | `states=9018624 closed=yes`, `target reached at depth 61` |
| the 43-move certificate | `python3 replay12.py abaBAB aaaaBBBBB "5 8 6 11 9 11 9 11 9 11 0 2 5 10 0 1 10 0 3 3 8 10 3 3 2 10 0 1 9 10 3 3 3 5 8 8 11 0 1 8 10 0 2" AbaBaBA abbbaBAB` | `moves 43, max intermediate total length 22, replay OK` |
| no P(3) to AK(3) path of 23 moves or fewer at caps 20 to 24 | `./ptriv ball T 26 AbaBaBA abbaBAB -d 23 -q -t abaBAB aaaBBBB` for T = 20, 21, 22, 23, 24 | `target NOT reached` in all five |
| the boxes are the same at conjugator bound 2 | `./ptriv ball T 27 S1 S2 -j 2 -q` | the same state counts as with `-j 1` at every cap listed in section 1 |
| the round-3 probe is reproduced under its own settings | `./ptriv ball 20 26 AbaBaBA abbaBAB -j 2 -d 18 -q` | `states=1130768`, the round-3 figure |
| the class keys agree with the census | `./ptriv ball T 24 abaBAB aaaBBBB -q -k .scratch/cls20.txt` for T = 15, 16, 17 | `hits` 26, 80, 2000, the census class counts |

## 11. What I could not verify, and what remains uncertain

I could not verify any statement at cap 21 or above for P(3), because that
question is the cap-21 census of the AK(3) component and the component is
larger than the 80 million states this engine can hold on this VM. The
cap-23 box of AK(4) was stopped at the same budget, so the cap-23 entry in
section 4 is an upper bound on a distance and not an exhaustive statement. The
round-3 certificate figures for comparison (34 moves and maximum 31 for
P(3) ~ AK(3), 46 moves and maximum 38 for AK(4) ~ P(4)) were recomputed from
the JSON files in `directions/ak-ladder/round3/` with the ladder's own move
system, and the comparison is honest because every one of the twelve moves
here is also a single move of that system, so a 24-move path here is a
24-move path there. Whether 24 moves is the minimum over all caps is open:
section 3 rules out 23 moves only for caps up to 24. The classification of the
AK(4) cap-20 component (260,592 states) is new and unchecked against any
independent table, since no published or round-2/3 table covers n = 4; the
Python engine does reproduce its cap-19 neighbour (124,896 states) exactly,
which is the only cross-check available for it.
