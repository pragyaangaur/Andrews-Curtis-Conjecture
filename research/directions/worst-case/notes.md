# The 91-move worst case: a shorter certificate, exact minima, and the census answer

Direction G9 of round 4 (member m2). Every claim below carries a label.
**VERIFIED** means a command in this directory replays it and the output is
quoted in Section 10. **COMPUTED** means a computation of this direction whose
code is here (wbfs.c, wcase.py, checkball.py, keycheck.py, analyze.py) and
whose output is quoted. **ARGUMENT** means a deduction from stated facts, with
the facts named. No claim about the truth of the Andrews-Curtis conjecture is
made anywhere in this file, and no partial result is rounded up.

## 0. Summary

1. All four 91-move certificates in the round-2 and round-3 archive replay
   against an independent checker, with 0 failures. The two that belong to the
   52,744-case sample of `directions/c14` have peak total length 14 and
   l-increase exactly 0; the other two come from the cap-18 meet-in-the-middle
   stage and have peak 18 and l-increase 4. **VERIFIED**
2. The 91-move certificates are not shortest. For both named presentations I
   give a 50-move certificate that never leaves total length 14 and a 44-move
   certificate that never leaves total length 15. Both replay under my checker
   and under `directions/c14/replay14.py`. **VERIFIED**
3. The 44 is exact. A breadth-first search in the reverse move system, run
   inside total length 15, finds the standard pair at distance exactly 44 from
   `BBabA,BBABAbaaa`; inside total length 14 the exact value is 50. The two
   balls have 58,487,624 and 14,399,816 states, which are the round-3 numbers
   for the standard ball, and at cap 12 my state set equals the set of the
   independent engine `directions/resisters/push.c` exactly. **VERIFIED**
4. The same search gives the exact minimum number of moves for every one of
   the 52,744 solved length-12, length-13 and length-14 presentations, at caps
   14 and 15 (files `min_cap14.txt` and `min_cap15.txt`). At cap 15 the worst
   case is `BBabA,BBAAAbaBa` with 45 moves, and the two named presentations sit
   at 44 with five others. At cap 14 the maximum is 50 and is shared by four
   presentations, the two named ones among them. **VERIFIED**
5. The exact l-increase of the sample is 0 for 52,680 presentations and 1 for
   64 presentations, all of total length 12. Every length-13 and every
   length-14 presentation has l-increase exactly 0. The round-3 table of
   bounds is correct as a table of bounds attached to its certificates, and it
   is not the value of the invariant: its rows at bounds 2 to 6, 9,484 cases,
   are strictly weaker than the truth. **VERIFIED** for the membership facts,
   **ARGUMENT** for the reading of the round-3 table.
6. The presentation is not in the cap-20 AK(3) class list of
   `directions/pu-enumeration`: its class key is absent from all 79,680 keys.
   The absence is forced, because a 91-move certificate and my 44-move
   certificate both stay inside total length 14, and no state of the cap-20
   AK(3) component has total length below 13. So no census intersection with
   AK(3) exists for this presentation, and the trick cannot shorten anything
   here. **VERIFIED** for the key absence and for the class-key lengths,
   **ARGUMENT** for the forcing.
7. What the 91 measures is the number of relator multiplications a shortest
   path needs, each of them paid at three moves by the round-3 descent. The
   depth of the presentation from the standard pair is 43 and 91 = 43 + 2*24,
   so the archive's certificate pays 24 inverse multiplications. Reimplementing
   the same descent rule gives 77 and 78 moves for the two named presentations,
   so the 91 is one search's output. The two named presentations need exactly
   17 multiplications in a shortest path, the maximum over all 52,744 cases,
   and only 16 presentations reach that maximum. All 16 need at least 40 moves
   and all 16 have a relator of length 5. The l-increase of the presentation is
   0, and it is 0 for 99.9 percent of the sample, so the l-increase cannot
   explain this case. **COMPUTED** and **ARGUMENT**

## 1. Conventions and the two move systems

The rank-2 free group is on `a` and `b`. Letters are `1 = a`, `-1 = A`,
`2 = b`, `-2 = B`; a word is freely reduced. A presentation is a pair of words.
The twelve moves of `directions/c14` and of `directions/resisters/push.c` are
inversion of one relator, conjugation of one relator by one generator or its
inverse (four conjugators for each relator), and multiplication of one relator
on the right by the other. `wbfs.c` uses exactly these twelve moves in the
order of push.c (inv0, c0a, c0A, c0b, c0B, inv1, c1a, c1A, c1b, c1B, m0, m1).

The twelve moves are not symmetric. The inverse of a conjugation or of an
inversion is one of the twelve moves, and the inverse of a multiplication is
not. The inverse relation therefore has its own twelve-move description: the
multiplication `r0 -> r0 r1` is replaced by `r0 -> r0 r1^-1`. `wbfs.c` runs
with `WREV=1` in that reverse system, and a complete reverse search from the
standard pair gives, for every state `t` of the component, the exact minimum
number of forward moves from `t` to the standard pair inside the cap. This is
the quantity that a certificate line of `directions/c14` counts, because such
a line lists forward moves from the presentation to the standard pair.

Two comments fix the scope. First, all exact statements below hold inside this
twelve-move system, which is where the round-2 and round-3 certificates and
negative bounds live; a full Andrews-Curtis move that conjugates a relator by a
long word is not in it. Second, a shortest path by move count and a shortest
path by peak length are different objects, and Section 5 keeps them apart.

## 2. The four 91-move certificates replay

`certs91_original.txt` holds the four 91-move lines of the archive: two from
`directions/c14/certs_14.txt` and two from `directions/c14/certs_mitm18.txt`.
`wcase.py` replays each of them with its own word model, which shares no code
with `directions/c14`.

| start | moves | peak total length | l-increase | move kinds |
| --- | ---: | ---: | ---: | --- |
| `BBabA,BBABAbaaa` | 91 | 14 | 0 | 32 c, 42 i, 17 m |
| `BBAba,BBaBabAAA` | 91 | 14 | 0 | 31 c, 43 i, 17 m |
| `BBabABA,BABAbaa` | 91 | 18 | 4 | 33 c, 38 i, 20 m |
| `BBAbaba,BABAAba` | 91 | 18 | 4 | 30 c, 41 i, 20 m |

All four end exactly at `(a,b)` and all four replay with 0 failures
(**VERIFIED**, Section 10.1). The first two are the 91-move cases of the
52,744-case sample; the other two are the cap-18 meet-in-the-middle cases,
which explains their peak of 18. Note the composition: 42 and 43 inversion
moves against 17 multiplications, which is the signature analysed in Section 7.

## 3. New certificates: 50 moves inside total length 14, 44 inside 15

`new_certs.txt` holds four new certificates, produced by a breadth-first
search from the presentation to the standard pair and then checked, never the
other way round.

| start | moves | peak | l-increase | move kinds |
| --- | ---: | ---: | ---: | --- |
| `BBabA,BBABAbaaa` | 50 | 14 | 0 | 25 c, 8 i, 17 m |
| `BBabA,BBABAbaaa` | 44 | 15 | 1 | 21 c, 6 i, 17 m |
| `BBAba,BBaBabAAA` | 50 | 14 | 0 | 24 c, 9 i, 17 m |
| `BBAba,BBaBabAAA` | 44 | 15 | 1 | 22 c, 5 i, 17 m |

The trade-off is explicit. Inside total length 14 the best I find is 50 moves,
which keeps the l-increase at 0; inside total length 15 it drops to 44 moves
and the peak rises to 15, so the l-increase of that certificate is 1 (the
l-increase of the presentation itself is 0, by Section 5).

The 50-move and the 44-move certificates replay under `wcase.py` and under
`directions/c14/replay14.py`, the second checker being the one written for the
length-14 census (**VERIFIED**, Section 10.2). The 50-move lines are minimal
for their cap, because the exact value at cap 14 is also 50 (Section 4).

Two features of the 44-move certificate illustrate the mechanics without
proving anything. Its length profile is 14,14,14,14,15,15,15,14,...,15,15,15,
15,8,7,6,5,4,3,2, so the path climbs to 15 three times and then collapses
through the containment region at the end. The 17 multiplications are the only
length increases, and each of them is later undone by a containment-style
collapse.

## 4. Exact minimality: the reverse system and the complete ball

The claim "44 is exact" needs an exhaustive search, and the search has to be
in the direction of the certificate, that is from the presentation to the
standard pair. Running a forward search from each of 52,744 presentations is
too expensive, so I search once from the standard pair in the reverse system
of Section 1; a path of length d in the reverse tree is a forward certificate
of length d, and the reverse search is complete because each reverse move is
the inverse of a forward move.

The engine is `wbfs.c`. It packs a state into a 64-bit word (5 bits per relator
length and 2 bits per letter), stores states in breadth-first order, keeps a
separate depth byte, and in the dumping mode keeps parent and move bytes so
that the certificate of every target can be read off. Its state counts match
the round-3 record at every cap where the record exists
(**VERIFIED**, Section 10.3):

| cap | states in the standard ball | round-3 record |
| ---: | ---: | ---: |
| 11 | 700,712 | 700,712 |
| 12 | 1,582,280 | 1,582,280 |
| 13 | 6,476,104 | 6,476,104 |
| 14 | 14,399,816 | 14,399,816 |
| 15 | 58,487,624 | 58,487,624 |

The forward ball and the reverse ball agree at every cap, and at cap 12 the
two state sets are literally equal: I decoded my reverse-search dump and the
dump of `push.c` and compared them, 1,582,280 states on each side, symmetric
difference empty (**VERIFIED**, Section 10.4). The reverse moves are therefore
the inverses of the twelve forward moves and the reverse ball is the component
of the standard pair.

With the search complete, the exact minimum number of forward moves from
`BBabA,BBABAbaaa` to `(a,b)` is 44 inside total length 15 and 50 inside total
length 14, and the same holds for `BBAba,BBaBabAAA` (**VERIFIED**). The two
values also come out of a second, forward, complete search rooted at the
presentation itself, which is the direction of the certificate, so the number
is cross-checked by two searches whose root and direction differ. Shorter
certificates at larger caps are not excluded, and Section 8 says so.

## 5. The exact minimum for all 52,744 solved cases, and the l-increase correction

The same reverse search with the full target list writes one minimal
certificate per presentation: `min_cap14.txt` and `min_cap15.txt`, 52,744
lines each, one line per start presentation of `directions/c14/certs_12.txt`,
`certs_13.txt` and `certs_14.txt`. All 52,744 lines of each file replay with 0
failures under `wcase.py` and under `directions/c14/replay14.py`, whose longest
accepted line is 50 moves in the cap-14 file and 45 in the cap-15 file
(**VERIFIED**, Section 10.5).

| quantity | value |
| --- | --- |
| presentations | 52,744 (4,376 at length 12, 17,728 at length 13, 30,640 at length 14) |
| round-3 certificate length | max 91, mean 25.68 |
| exact minimum, cap 14 | max 50, mean 12.17 |
| exact minimum, cap 15 | max 45, mean 12.06 |
| round-3 length minus cap-14 minimum | max 42, mean 13.52 |
| cap-15 exact minimum, worst case | `BBabA,BBAAAbaBa`, 45 |
| cap-15 exact minimum, 44 | 6 presentations, the two named ones among them |
| cap-14 exact minimum, 50 | 4 presentations, the two named ones among them |

So the 91-move certificate is about twice the exact minimum for its own
presentation, and on this sample the archive's move counts are inflated by
13.5 moves on average. The number 91 is an honest upper bound from the round-3
search, and it is not the minimal certificate length of the presentation.

The l-increase needs a separate computation. For a presentation of total
length L, a certificate whose intermediates all satisfy total length at most C
shows l-increase at most C minus L, and a complete ball at cap C minus one
shows the complementary bound. Running the reverse search at caps 11, 12, 13,
14 and 15 and recording presence gives the exact value for each of the 52,744
presentations (**COMPUTED**, `data/revdep*.txt`, Section 10.6):

| start length | l-increase 0 | l-increase 1 |
| ---: | ---: | ---: |
| 12 | 4,312 | 64 |
| 13 | 17,728 | 0 |
| 14 | 30,640 | 0 |
| all | 52,680 | 64 |

The 64 exceptional presentations are absent from the cap-12 ball and present
in the cap-13 ball. I checked both facts against `push.c`'s own dumps, which
are independent of `wbfs.c`: 0 of the 64 occur among the 1,582,280 cap-12
states, 64 of the 64 occur among the 6,476,104 cap-13 states, and all 52,744
occur among the 14,399,816 cap-14 states (**VERIFIED**, Section 10.7). Since
the l-increase is a minimum of the peak length minus the start length over all
trivializations, and the start length is a lower bound for the peak, the value
0 is exact in any move system. The value 1 of the 64 is exact in the
twelve-move system, and at most 1 in the full move system.

The round-3 hardness report tabulates the bounds of its own certificates, and
its rows at bounds 2 to 6 cover 9,484 presentations. Those rows are true as
statements about those certificates and they are far above the invariant. The
correct picture on the solved sample is that the l-increase takes two values,
0 and 1. The 64 presentations with value 1 do need more moves than the rest,
16.98 on average against 12.06, so the invariant is not entirely empty; it is
nearly constant, and the presentations with the largest move counts all have
value 0.

## 6. The cap-20 AK(3) census: the presentation is not in it, and cannot be

The task asks for the class, depth and neighbours of the presentation inside
the cap-20 AK(3) census. The presentation is not in that census, and I can
show that no computation of the AK(3) component at any cap can contain it
while it has a certificate inside total length 14.

`keycheck.py` reproduces the class key of `directions/pu-enumeration/rawbox.c`
(cyclic reduction, least rotation over a word and its inverse, letter order
`A < a < B < b`, relator order kept) and tests membership. As a control it
computes the key of AK(3) itself and finds it twice in the class list, at line
1 and at line 108 of `cls20k1.txt.gz`, so the key format matches. The keys of
both named presentations are absent from all 79,680 keys (**VERIFIED**,
Section 10.8).

The absence is forced by the rest of the data. The class keys of the cap-20
list have total lengths from 13 to 20, with 24 keys at length 13 and none
shorter, so no state of the cap-20 AK(3) component has total length below 13
(**COMPUTED** from the same file, and the round-2 negative says the same). The
standard pair has total length 2, and my 44-move certificate connects it to
`BBabA,BBABAbaaa` through states of total length at most 15, all of which lie
in the cap-20 box. If the presentation were in the cap-20 AK(3) component, the
standard pair would be in it too, which the minimum total length of 13 forbids
(**ARGUMENT**). This also shows that the census-intersection trick of round 3
has nothing to offer for this presentation: its census home is the standard
component, where the exact distance is already known.

The presentation's place in the standard component is as follows
(**COMPUTED**, Section 10.9). Its distance from the standard pair is 43 in the
forward direction and 44 in the direction of the certificate, so the directed
distance is asymmetric. Of its twelve move images, exactly six stay inside
total length 15, and all six have reverse depth 43, which means that every
neighbour inside the box lies on a shortest certificate. The component itself
has radius 78 from the standard pair in the forward direction and 79 in the
reverse direction, so the presentation is far from the centre and not at the
boundary.

## 7. What the 91 measures: multiplication count, not l-increase

The round-3 descent in `directions/c14/c14search.py` walks a state down a
breadth-first tree. A step downwards is either one forward move, or, when the
tree edge is a multiplication, the three-move sequence invert, multiply,
invert that undoes it. A certificate of this kind from a state at depth d has
length d + 2k, where k is the number of steps it takes as inverse
multiplications, so it overstates the move count of the route. The depth of
`BBabA,BBABAbaaa` from the standard pair is 43 (**COMPUTED**, Section 10.9) and
91 = 43 + 2*24, so the archive's certificate pays 24 inverse multiplications
(**ARGUMENT**: k = 24 is the only solution of d + 2k = 91 with d = 43).

The length is not a function of the depth alone. I implemented the same rule,
single move first and then the three-move back-step, on my own complete depth
map at cap 15, and it produces a 77-move certificate for `BBabA,BBABAbaaa`
(26 single moves and 17 back-steps) and a 78-move certificate for
`BBAba,BBaBabAAA` (27 single moves and 17 back-steps) (**COMPUTED**,
Section 10.11). The archive's 91 therefore depends on the variant of the
presentation the descent starts from and on the order in which it tries the
moves; `c14search.py` starts from the variant of least depth among the cyclic
permutations, the inversions and the swap of the presentation. The exact
minimum is 44 in every case, so the 91 is the output of one descent and not a
property of the case.

The quantity that organises the sample is the number of multiplications. In
the 52,744 minimal certificates at cap 15 the multiplication count ranges from
1 to 17, and the total move count has rank correlation 0.55 with it
(**COMPUTED**). The presentations that need at least 40 moves are exactly 16,
and the 16 presentations with the maximum multiplication count of 17 are the
same 16; each of them has a relator of length 5:

| min relator length | cases | max moves | mean moves | max multiplications |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 37,716 | 16 | 11.83 | 12 |
| 2 | 5,028 | 16 | 11.30 | 7 |
| 3 | 4,920 | 19 | 11.65 | 8 |
| 4 | 664 | 22 | 12.37 | 9 |
| 5 | 3,168 | 45 | 15.33 | 17 |
| 6 | 720 | 29 | 14.99 | 11 |
| 7 | 528 | 29 | 16.33 | 12 |

The two named presentations are of the length-5 type, with relators of
lengths 5 and 9. The family is small, 3,168 of 52,744, and it contains every
case above 40 moves. A short relator next to a long one forces many
multiplications, and each multiplication in the certificate direction costs at
least one move and often forces inversions to bring the relator back into the
box. This is the mechanism behind the 91, and the l-increase of the case is 0.

The comparison with the AK(3) family is worth recording. AK(3) has l-increase
at least 8 by the round-3 computation and is the genuine hard object of the
programme; the 91-move case is not hard in that sense at all, and it is hard
only in the move count, where the exact value is 44. The round-3 verdict that
the l-increase does not track difficulty survives this correction and becomes
sharper, because the invariant is constant on all but 64 of the 52,744 solved
presentations.

## 8. What this direction does not settle

1. The cap-16 minimum of `BBabA,BBABAbaaa` is unknown. A reverse search at cap
   16 with a budget of 60,000,000 states reached depth 12 and was stopped
   (**COMPUTED**, Section 10.10). The cap-16 ball is much wider than the
   cap-15 ball, and the machine was carrying several other members' searches,
   so I did not run it to completion. A certificate shorter than 44 at a
   larger cap is therefore not excluded; the 44 is exact at cap 15 and 50 is
   exact at cap 14.
2. The minimality statements are inside the twelve-move system. A full
   Andrews-Curtis move that conjugates a relator by a word of length two or
   more is not among the moves, and a shorter certificate in the full system
   could exist. Round 3 records that the conjugator bound is not binding for
   the component counts at caps 13, 16 and 17, which is evidence and not a
   proof for this presentation.
3. The reading of the round-3 table in Section 5 is mine. The round-3 report
   labels its rows as certified bounds, so it makes no false statement; what I
   correct is the impression that the invariant spreads over 0 to 6 on the
   sample.
4. The minimum total length of 13 for the cap-20 AK(3) component is taken from
   the class list, which is a verified object of round 2 and round 3. I did not
   rebuild the 51,411,456-state cap-20 component.

## 9. Files

| file | content |
| --- | --- |
| `wcase.py` | independent certificate parser, word model and replayer, written from the definitions |
| `wbfs.c` | the reverse and forward breadth-first engine with depths and certificate dumping |
| `checkball.py` | membership test of a list of pairs against a `push.c` ball dump |
| `setcompare.py` | comparison of a `wbfs` state dump with a `push.c` ball dump |
| `keycheck.py` | the `rawbox.c` class key and a membership test in the cap-20 class list |
| `analyze.py` | every table above, recomputed from the files in this directory |
| `run_all.sh` | reruns everything in order |
| `certs91_original.txt` | the four 91-move certificates of rounds 2 and 3 |
| `new_certs.txt` | the four new certificates, 50 and 44 moves for each named presentation |
| `min_cap14.txt` | 52,744 minimal-length certificates inside total length 14 |
| `min_cap15.txt` | 52,744 minimal-length certificates inside total length 15 |
| `linc1_pairs.txt` | the 64 presentations of l-increase exactly 1 |
| `data/all_targets.txt`, `data/all_meta.txt` | the target list and the round-3 move counts |
| `data/revdep11.txt` to `data/revdep15.txt` | reverse depth of every target at caps 11 to 15 |
| `data/nbrs.txt` | the six move images of the presentation that stay inside total length 15 |
| `data/analyze.out` | the output of `analyze.py` |

The ball dumps of `push.c` (21 MB, 94 MB and 221 MB) are not stored in the
repository. `run_all.sh` rebuilds them.

## 10. Exact commands and key output

The commands below run from this directory with
`R=/workspace/nucleus/work/projects/p-fc9666b4f6c54fa380c9a84775ed7397/repo`.

### 10.1 The 91-move certificates
```
$ python3 wcase.py certs91_original.txt
certs91_original.txt              4 certificates, 0 failed, longest 91, mean moves 91.00
   BBabA,BBABAbaaa        start 14  moves  91  peak 14  l-increase 0  kinds {'c': 32, 'i': 42, 'm': 17}  ok True
   BBAba,BBaBabAAA        start 14  moves  91  peak 14  l-increase 0  kinds {'c': 31, 'i': 43, 'm': 17}  ok True
   BBabABA,BABAbaa        start 14  moves  91  peak 18  l-increase 4  kinds {'c': 33, 'i': 38, 'm': 20}  ok True
   BBAbaba,BABAAba        start 14  moves  91  peak 18  l-increase 4  kinds {'c': 30, 'i': 41, 'm': 20}  ok True
total 4 certificates, 0 failed
```
Control over the whole archive, same checker:
```
$ python3 wcase.py $R/directions/c14/certs_12.txt $R/directions/c14/certs_13.txt $R/directions/c14/certs_14.txt
total 52744 certificates, 0 failed
```

### 10.2 The new certificates
```
$ python3 wcase.py new_certs.txt
new_certs.txt                     4 certificates, 0 failed, longest 50, mean moves 47.00
$ python3 $R/directions/c14/replay14.py new_certs.txt
replayed 4 certificates, 0 failed, longest 50 moves
```

### 10.3 Ball sizes
```
$ ./wbfs 11 60000000 a,b all_targets.txt none     # and similarly for 12 to 15
states 700712 complete 1
states 1582280 complete 1
states 6476104 complete 1
states 14399816 complete 1
states 58487624 complete 1
```
The same five numbers with `WREV=1` (the reverse system), and
`./push build 12 ballstd_12c.bin a,b 1600000` prints
`build cap 12 start a,b: 1582280 states written`.

### 10.4 The state sets agree
```
$ WREV=1 ./wbfs 12 3000000 a,b none rev12
states 1582280 complete 1
$ python3 setcompare.py rev12 ballstd_12c.bin
mine 1582280, push.c 1582280, identical True, mine-only 0, theirs-only 0
```

### 10.5 The minimal certificates
```
$ python3 wcase.py min_cap14.txt
min_cap14.txt (cap 14)     52744 certificates, 0 failed, longest 50, mean moves 12.17
$ python3 wcase.py min_cap15.txt
min_cap15.txt (cap 15)     52744 certificates, 0 failed, longest 45, mean moves 12.06
$ python3 $R/directions/c14/replay14.py min_cap14.txt
replayed 52744 certificates, 0 failed, longest 50 moves
$ python3 $R/directions/c14/replay14.py min_cap15.txt
replayed 52744 certificates, 0 failed, longest 45 moves
```

### 10.6 The exact l-increase
```
$ for C in 11 12 13 14 15; do WREV=1 ./wbfs $C 60000000 a,b all_targets.txt none; done
   (one depth per target and cap, written to data/revdep$C.txt)
$ python3 analyze.py
   exact l-increase histogram (twelve-move system): {0: 52680, 1: 64}
   start length 12: {0: 4312, 1: 64}
   start length 13: {0: 17728}
   start length 14: {0: 30640}
```

### 10.7 Independent membership of the 64 and of the full sample
```
$ python3 checkball.py ballstd_12c.bin linc1_pairs.txt
records 1582280, wanted 64, found 0, missing 64
$ python3 checkball.py ballstd_13c.bin linc1_pairs.txt
records 6476104, wanted 64, found 64, missing 0
$ python3 checkball.py ballstd_14c.bin all_targets.txt
records 14399816, wanted 52744, found 52744, missing 0
```

### 10.8 The AK(3) census
```
$ python3 keycheck.py BBabA,BBABAbaaa $R/directions/pu-enumeration/cls20k1.txt.gz
key forward : 5 -1 -2 -2 1 2 | 9 -1 -1 -1 -2 1 2 1 2 2
class lines read: 79680
NOT FOUND {}
$ python3 keycheck.py BBAba,BBaBabAAA $R/directions/pu-enumeration/cls20k1.txt.gz
class lines read: 79680
NOT FOUND {}
$ python3 keycheck.py aaaBBBB,abaBAB $R/directions/pu-enumeration/cls20k1.txt.gz
class lines read: 79680
MATCH {'6 -1 -2 -1 2 1 2 | 7 -1 -1 -1 2 2 2 2': 1, '7 -1 -1 -1 2 2 2 2 | 6 -1 -2 -1 2 1 2': 108}
```
Class-key total lengths: 13: 24, 14: 80, 15: 1,032, 16: 1,112, 17: 5,688,
18: 6,456, 19: 31,240, 20: 34,048, total 79,680, minimum 13.

### 10.9 Depth and neighbours
```
$ ./wbfs 15 60000000 a,b all_targets.txt none        # forward
states 58487624 maxdepth 78 complete 1
target  BBabA,BBABAbaaa  43
$ WREV=1 ./wbfs 15 60000000 a,b all_targets.txt none  # reverse
states 58487624 maxdepth 79 complete 1
```
Neighbours inside total length 15 with their reverse depths, all 43:
```
i0  aBAbb,BBABAbaaa    43     i1  BBabA,AAABababb   43
c0A ABBab,BBABAbaaa    43     c0b BabAB,BBABAbaaa   43
c1a BBabA,aBBABAbaa    43     c1b BBabA,BABAbaaaB  43
```
The six move images that leave total length 15 are `c0a`, `c0B`, `c1A`,
`c1B`, `m0` and `m1`.

### 10.10 The cap-16 probe
```
$ WREV=1 ./wbfs 16 60000000 a,b all_targets.txt none
states 60000000 maxdepth 12 complete 0 time 43.36
depth_hist 0:1 1:8 ... 12:16313385
```

### 10.11 The descent of round 3 reimplemented
```
$ WDESCEND=BBabA,BBABAbaaa ./wbfs 15 60000000 a,b t.txt none
DESCEND  moves 77  single 26  backsteps 17  enddepth 0
$ WDESCEND=BBAba,BBaBabAAA ./wbfs 15 60000000 a,b t2.txt none
DESCEND  moves 78  single 27  backsteps 17  enddepth 0
```
The input files hold one line with the pair, and `t.txt` and `t2.txt` are
`BBabA,BBABAbaaa` and `BBAba,BBaBabAAA`.

### 10.12 Everything at once
```
$ bash run_all.sh
```
