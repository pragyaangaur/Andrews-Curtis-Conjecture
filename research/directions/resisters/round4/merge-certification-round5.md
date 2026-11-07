# Class-merge certification at cap 26, and eight of the 66 resisters fall

Round 5 direction H4, member m7, swarm smw38010i. This file continues
`../resisters-round4.md` and `README.md` of the same directory (round 4, member
m1) and covers the 66 presentations that round 4 left undecided at total relator
length 14. Every substantive claim is labelled **Verified**, **Computed**,
**Argument** or **Reported**. Nothing here is a claim about the truth or the
falsehood of the Andrews-Curtis conjecture, and no presentation is claimed
nontrivial.

## 0. Summary

Four things changed. Eight presentations are now proved Andrews-Curtis trivial;
three of the same-size blocks are now proved to be single Andrews-Curtis
classes, and a fourth merges a pair; and the reason the 66 split into blocks of
equal component size is explained, which removes the reason round 4 had for
expecting those blocks to merge. **Verified** for the certificates, **Computed**
for every count, with the exact commands of Section 10.

1. The bound-25 block of eight presentations, whose start is `BBAAABa,BBabABA`,
   is Andrews-Curtis trivial. Each of the eight has an explicit certificate to
   the standard pair `a,b`, of 179 to 191 moves, with peak total relator length
   26. The file `certs_round5/fall_group8.txt` holds the eight lines and both
   checkers used here replay them without a failure. Round 4's bound of 25 for
   these eight is superseded: the trivialisation needs peak 26, one above the
   cap that round 4 exhausted.
2. The bound-24 block of four presentations, the family of Solitar's candidate
   `BBBAbba,BAAbaaa`, is a single Andrews-Curtis class.
   `certs_round5/g5_all_pairs.txt` holds six pairwise certificates of 42 to 114
   moves with peaks 24 to 25. Carreras's 36-move certificate already merged one
   of the three pairs, so this block drops from three classes to one.
3. The bound-24 block of eight presentations, which contains Carreras's 85-move
   pair, is a single Andrews-Curtis class.
   `certs_round5/g1_all_pairs.txt` holds all 28 pairwise certificates, of 43 to
   363 moves, with peaks at most 26. The seven other members are met at
   distances 43, 76, 76, 78, 108, 126 and 145 from `BBBAbbA,BAAAbaa`, so this
   block drops from seven classes to one.
4. Two more blocks are complete negatives at cap 26. The component of
   `BBAABBa,BAbABaa` is exhausted at 108,428,384 states and the component of
   `BBBAbbA,BAAAABa` at 103,130,376 states, and neither contains the standard
   pair nor another member of its own block. One pair in the block of
   `BBAAbaa,BBabAbA` does merge, at 111 moves, so that block drops from eight
   classes to at most seven.
5. Two blocks are only bounded. The component of `BBAAbaa,BBaBabA` reaches
   2,378,867,882 states after 174 layers, and the component of `BBAAbaa,BBabAbA`
   reaches 1,080,302,244 states after 313 layers, with no hit beyond the one
   merge of item 4.
6. The ledger becomes 58 undecided presentations in at most 26 undecided
   classes, so the round-3 bound improves from $c(14) \le 2 + 43 = 45$ to
   $c(14) \le 2 + 26 = 28$. This is an **Argument** from the certified merges
   and the round-4 count, spelled out in Section 8.

Two structural facts support the work. The seven non-22 blocks of round 4 are
the orbits of the eight signed letter permutations of $F_2$ on conjugacy-class
keys, so their equal component sizes are forced and are no evidence of
Andrews-Curtis equivalence (Section 6, **Verified**). In small boxes those
permuted pairs are sometimes equivalent and sometimes not, which is why the
merges above had to be searched for and could not be predicted from the
symmetry (Section 7, **Verified**).

## 1. The two engines and their agreement

Two independent programs are used. `directions/resisters/round4/acx.c` is round
4's in-memory explorer and is used unchanged, compiled as `acx`. The new
`certs_round5/mergebox.c` is a disk-backed, layer-by-layer explorer that I wrote
for this direction by adapting the method of `directions/cap21/rawbox4.c`:
sorted eight-byte key files on disk, chunked radix sort, k-way merge and a
streamed anti-join, so peak memory is a fixed buffer. It differs from
`rawbox4.c` in three ways that matter here. The state encoding is six bits per
length and two bits per letter, so a total length of 26 fits in one word. It
generates exactly the twelve restricted moves of `acx.c`. It takes the start
pair from the command line, checks a file of target states at every new state,
and keeps every layer as its own file so that a hitting path can be
reconstructed backwards.

The two engines agree exactly on five component sizes, which is the check that
the move set, the encoding and the box condition all agree. **Verified** by
running both.

| pair | cap | `mergebox` | `acx count` | also in round 4's table |
| --- | --- | --- | --- | --- |
| `a,bb` | 10 | 67,768 | 67,768 | no |
| `BBAAABa,BBabABA` | 24 | 9,432,136 | 9,432,136 | 9,432,136 |
| `BBAAABa,BBabABA` | 25 | 24,781,832 | 24,781,832 | 24,781,832 |
| `BBAAbaa,BBabAbA` | 24 | 67,181,488 | 67,181,488 | 67,181,488 |
| `BBAABBa,BAbABaa` | 24 | 17,638,096 | 17,638,096 | 17,638,096 |

Three further checks were made on the path machinery. Each path is replayed by
two independent replayers: mine in `certs_round5/f2.py`, which was written from
the move table of `directions/resisters/push.c`, and
`directions/c14/replay14.py`, which round 2 wrote from scratch with its own
parser, its own free reduction and its own inverse. Both report the exact final
pair, and mine also reports the maximum total length along the path. The
backward walk uses a predecessor set with twelve members, one per move index,
and the two multiplication predecessors are unique because
$\mathrm{reduce}(u v) = w$ forces $u = \mathrm{reduce}(w v^{-1})$. As a check on
the replayer, my code replays the 21 round-3 paths of
`.ultramath/smw2opo0o/m7/work/spot22_paths.txt`, and all of them end where they
are recorded to end. **Verified.**

## 2. The eight bound-25 resisters fall

Round 4 recorded for `BBAAABa,BBabABA` and its seven companions a bound of 25,
meaning that the whole twelve-move component inside total length 25 was
explored and contains no pair of the standard ball. That bound is correct and I
reproduced it. At cap 26 the same component is a different object, because the
component joins the huge class of the standard pair. **Computed.**

The cap-26 exploration from `BBAAABa,BBabABA` ran for 37 minutes, completed 175
layers and had 1,903,690,258 states in its visited file when the machine
stopped it. The visited file was 15,229,522,064 bytes, exactly eight bytes per
state. The standard pair first appears at layer 173, as the state `b,a`. The
state file recorded `depth 176`, so the run had finished all paths of length at
most 175 when it was stopped. Its working files were deleted after the
certificate was extracted, so the numbers here are recorded from the run's own
state file and are not shipped, while the certificate that the run produced is
shipped and replays.

The certificate is 173 moves from `BBAAABa,BBabABA` to `b,a`, followed by the
six-move relator swap of `AC4.lean` that carries any rank-2 pair to the swapped
pair, giving 179 moves to `a,b`. The maximum total relator length along it is
26, and the counts of states at each length are: 3 states at length 2, 4 at 3,
2 at 4, one each at 5 to 10, one at 12, two at 14, 16 at 17, 8 at 18, 16 at 19,
17 at 20, 26 at 21, 13 at 22, 26 at 23, 3 at 24, 27 at 25 and 10 at 26.
**Verified** by both replayers.

The other seven members of the block follow by the symmetry of Section 6. If
$\sigma$ is a signed letter permutation then the same move list, read through
$\sigma$, carries $\sigma(P)$ to $\sigma$ of the standard pair, and every image
of the standard pair is the standard pair up to inverting relators. For each of
the seven I found the $\sigma$ and a short class path from the member to
$\sigma(P)$, checked the transported walk step by step against $\sigma$ of the
original walk, and replayed the composite certificate. The results are in
`certs_round5/fall_group8.txt`: 179 moves for `BBAAABa,BBabABA`, 191 for
`BBABAba,BBaBAAA`, 184 for `BBABaaa,BBaBabA`, 184 for `BBAbaBa,BBaaaBA`, 179
for `BBBAAbA,BABabAA`, 179 for `BBBAbAA,BABAAba`, 180 for `BBBaaba,BAbaaBa`
and 180 for `BBBabaa,BAAbAba`. Every peak is 26. **Verified** by both
replayers, and `replay14.py` prints `replayed 8 certificates, 0 failed, longest
191 moves`.

Because the block is one orbit and the certificates reach the standard pair,
all eight presentations lie in the trivial Andrews-Curtis class. The same
exploration shows that this class does not contain any of the other 65
presentations inside those 1,903,690,258 states: I binary searched the sorted
visited file for all 66 exact states and only the start itself was present.
That is a statement about a prefix of the component and not about the whole
component, so it decides nothing about the other 65.

## 3. The bound-24 block of four is one class

The four presentations are `BBBAbba,BAAAbaa`, `BBBAbba,BAAbaaa`,
`BBBabbA,BAAAbaa` and `BBBabbA,BAAbaaa`. Round 4 exhausted their cap-24
components at 300,941,152 states each and did not push this block to cap 25.
Carreras's certificate `cert_sym_equiv_orphan1.json`, replayed in round 3,
already merges the first with the second in 36 moves. **Reported** from
`directions/c14/carreras/`.

I explored cap 26 from `BBBAbba,BAAAbaa` for 592,692,955 states and reached the
second member at distance 43 and the third at distance 42. A second exploration
from `BBBabbA,BAAbaaa` for 475,164,169 states reached the same two at distance
43. From those four direct paths and the explicit inverse of a path, which
replaces each multiplication by two inversions and one multiplication, I built
all six pairwise certificates. They are 43, 42, 114, 113, 71 and 71 moves, with
peaks 25, 24, 25, 25, 25 and 24. **Verified**: `replay14.py` prints `replayed 6
certificates, 0 failed, longest 114 moves`, and `certs_round5/g5_all_pairs.txt`
holds them.

Two remarks on the numbers. The twelve-move search finds 43 moves for the pair
Carreras did in 36, which is consistent with his certificate using a move
outside the twelve, most likely multiplication by an inverse relator or left
multiplication. Both peaks are at most 25, so this whole merge was already
inside the cap-25 box and round 4 would have found it had it run this block at
cap 25.

## 4. The bound-24 block of eight is one class

The block is `BBBAbbA,BAAAbaa`, `BBBAbbA,BAAbaaa`, `BBBAbba,BAAABaa`,
`BBBAbba,BAABaaa`, `BBBabbA,BAAABaa`, `BBBabbA,BAABaaa`, `BBBabba,BAAAbaa` and
`BBBabba,BAAbaaa`. It contains Carreras's 85-move pair, namely
`BBBAbba,BAABaaa` with `BBBAbba,BAAABaa`. **Reported** from
`directions/c14/carreras/`.

Cap 26 from `BBBAbbA,BAAAbaa` met four members in the first 784,619,260 states,
at distances 43, 76, 76 and 78, and the three that were still missing were met
after the run was resumed, at distances 108, 126 and 145. The resumed run
reached 1,642,252,055 states after 150 layers. The standard pair is not in the
visited set, so this exploration finds no trivialisation of this block.
**Computed**, from `certs_round5/G1.log` and `certs_round5/G1b.log`.

All eight members are therefore one class, and
`certs_round5/g1_all_pairs.txt` holds all 28 pairwise certificates, from 43 to
363 moves, with peaks at most 26. **Verified**: `replay14.py` prints `replayed
28 certificates, 0 failed, longest 363 moves`. This block drops from seven
classes to one, which is the largest single improvement of this round.

## 5. A merge, two complete negatives and the budget stops at cap 26

One pair in the block of `BBAAbaa,BBabAbA` merges. The exploration from
`BBAAbaa,BBabAbA` reached `BBAbbaa,BAAbaBa` at distance 111, and that
certificate is in `certs_round5/g2_pair.txt`, 111 moves with peak 26.
**Verified** by both replayers. The six other members of that block are absent from the
visited set after three successive runs reaching 1,080,302,244 states over 313
layers, and the standard pair is absent too, so the block is at most seven
classes. **Computed**, from `certs_round5/G2.log`, `G2b.log` and `G2c.log`.

Two blocks were exhausted inside the cap-26 box, which gives a complete
negative for them. The component of `BBAABBa,BAbABaa` has 108,428,384 states
and the search ended when the frontier at depth 62 was empty. The component of
`BBBAbbA,BAAAABa` has 103,130,376 states and ended when the frontier at depth 72 was empty. Neither visited
set contains the standard pair, and neither contains another member of its own
block, so those eight presentations are neither trivial nor merged within the
cap-26 box. **Computed**, from `certs_round5/G6.log` and
`certs_round5/G7.log`.

One block is only bounded. The component of `BBAAbaa,BBaBabA` reached
2,378,867,882 states in 174 layers in 3098 seconds, and a second run of the same
start reached 1,484,691,178 states in 169 layers in 1842 seconds with the
frontier still growing by about 22 per cent per layer. Neither run met the
standard pair or another member of the block. The component of
`BBAAABa,BBabABA` was stopped by memory at 1,903,690,258 states, as described
in Section 2. **Computed**, from `certs_round5/G3.log`, `certs_round5/G3b.log`
and the shipped state files.

The cap-26 growth explains why the cap-25 bounds sat one step short. For the
falling block the component grew by a factor above 76 from cap 25 to cap 26,
because at cap 26 the component joins the giant class of the standard pair. One
further cap multiplies the state count by a similar factor, which puts cap 27
out of reach of both engines on this machine, and this is the exact point where
the cap-pushing method fails.

## 6. Why the blocks are blocks: the signed letter permutations

Let $\Sigma$ be the eight maps of $F_2$ that send $a$ and $b$ to signed
generators, so $a \mapsto a^{\pm 1}$ and $b \mapsto b^{\pm 1}$, or
$a \mapsto b^{\pm 1}$ and $b \mapsto a^{\pm 1}$. Extend each map to words letter
by letter and to a pair of relators componentwise. The twelve moves are
permuted by every element of $\Sigma$: the two inversions and the two
right multiplications are fixed, and conjugation of relator $i$ by the letter
$g$ becomes conjugation of relator $i$ by $\sigma(g)$. So
$\sigma(\mathrm{step}(P,m)) = \mathrm{step}(\sigma(P),\pi(m))$ with $\pi$ the
induced permutation of move indices, and $\sigma$ carries the twelve-move
component of $P$ isomorphically onto the component of $\sigma(P)$. Equal
component sizes, equal distance distributions and equal length histograms all
follow. **Verified**: `certs_round5/symmetry_check.py` checks the identity for
all eight maps and all twelve moves on 400 random pairs, 38,400 checks with no
failure, and again on every reduced pair of total length at most 3, 217 pairs
with no failure.

Acting on conjugacy-class keys, $\Sigma$ decomposes the 66 presentations as
follows. **Computed.**

| block | members | $\Sigma$-orbits |
| --- | --- | --- |
| bound 22, component 176,714,288 | 22 | 4, 8, 2, 8 |
| bound 24, component 375,482,496 | 8 | 8 |
| bound 24, component 67,181,488 | 8 | 8 |
| bound 25, component 38,286,952 | 8 | 8 |
| bound 25, component 24,781,832 | 8 | 8 |
| bound 24, component 300,941,152 | 4 | 4 |
| bound 25, component 50,227,344 | 4 | 4 |
| bound 25, component 43,383,880 | 4 | 4 |

The seven non-22 blocks are therefore exactly the orbits of $\Sigma$, and their
equal component sizes carry no information about Andrews-Curtis equivalence.
This is the point round 4 did not have. Round 4 read the repeated sizes as
isomorphic copies of one component shape, which they are, and the isomorphism
is the letter permutation, which is not an Andrews-Curtis move in general. The
sections above show that three of these blocks do merge and two do not, so the
symmetry neither forces nor forbids a merge.

## 7. A calibration in small boxes

Whether a signed letter permutation is realised by Andrews-Curtis moves depends
on the pair, and small cases can be settled completely. All of the following are
searched inside the full cap-14 box with the twelve moves, so an exhaustion is a
statement about every path whose intermediate pairs have total length at most
14. **Verified.**

| pair $P$ | $\sigma(P)$ | outcome |
| --- | --- | --- |
| `aab,ab` | `bba,ba` | equivalent, 6 moves `0,2,10,10,7,10` |
| `ab,abb` | `ba,baa` | equivalent, 6 moves `5,11,2,11,8,11` |
| `a,b` | `b,a` | equivalent, 6 moves `0,11,5,10,0,11` |
| `a,bb` | `b,aa` | component exhausted at 5,813,848 states, no path |
| `aa,b` | `bb,a` | component exhausted at 5,813,848 states, no path |

The two positive cases matter for the mechanism. In `aab,ab` the moves reach
`A,ab`, and one multiplication then cancels the whole word `ab` against the
letter `A`, so a cancellation between the two relators is what makes the
permuted pair reachable. Nothing in these experiments is used as evidence
about the length-14 resisters, and they are recorded because they show that the
symmetry question is a computation and not a theorem.

## 8. The ledger

The round-4 accounting is 66 undecided presentations in 43 undecided classes,
from 66 minus 21 for the block of 22, which is one certified class, and minus 2
for Carreras's two merge pairs, one of which lies in the block of four and one
in the block of eight. The certified results of this round change four of the
eight blocks. **Argument**, from the counts above.

| block | presentations | classes before | classes now | basis |
| --- | --- | --- | --- | --- |
| bound 22 | 22 | 1 | 1 | round 3 certificates |
| bound 24, 375,482,496 | 8 | 7 | 1 | all 8 in one class, Section 4 |
| bound 24, 67,181,488 | 8 | 8 | at most 7 | one pair merged, Section 5 |
| bound 25, 38,286,952 | 8 | 8 | at most 8 | no merge found, Section 5 |
| bound 25, 24,781,832 | 8 | 8 | 0 undecided | all eight trivial, Section 2 |
| bound 24, 300,941,152 | 4 | 3 | 1 | Section 3 |
| bound 25, 50,227,344 | 4 | 4 | at most 4 | exhausted, no merge |
| bound 25, 43,383,880 | 4 | 4 | at most 4 | exhausted, no merge |

Summing the last column gives at most 26 undecided classes, and the eight
presentations of the falling block now lie in the trivial class, which is one of
the two classes that the campaign's ledger already counts. So the undecided
presentation count is 58 and
$$c(14) \le 2 + 26 = 28,$$
against round 3's $c(14) \le 45$. The two classes counted separately are the
trivial class and the class of AK(3), following the convention of round 3's
ledger in `STATE.md`.

## 9. What is not claimed

1. No presentation of the 58 that remain undecided is claimed trivial or
   nontrivial, and no two of them in different blocks are claimed inequivalent.
   A merge that was not found is a bound on a search and not a separation.
2. The bounds of Section 5 for the stopped blocks are statements about paths of
   at most 174 and 313 moves whose intermediate pairs have total length at most
   26. A longer path inside the same box, or any path that leaves the box, is
   outside them.
3. The minimality of peak 26 for the falling block is a statement about the
   twelve-move system. Round 4's Section 8.2 caveat applies unchanged: the
   twelve-move simulation of a left multiplication passes through `r0 r1` and
   so can leave a box that both endpoints sit in, and a full Andrews-Curtis
   proof with every intermediate tuple inside total length 25 is therefore not
   excluded by the cap-25 exhaustion.

[Coordinator note, 6 November 2026, from the round-7 referee report
(.ultramath/smw48or9f/m2/report.md) and the round-6 falls
(.ultramath/smw3ow2dp/m1/report.md), both coordinator-rerun: item 3 above is
SUPERSEDED. The four multiplication transports of
directions/certificate-algebra/report.md section 2 (right multiplication by
r_j in 1 move, by r_j^-1 in 3; left multiplication by r_j in 5, by r_j^-1 in
3, every intermediate at most max(start,end)) are verified on 1,600 cases
with 0 failures by the round-7 referee and by the coordinator, so left
multiplication does NOT leave the box and the cap-25 exhaustion bounds the
full AC relator move set at its cap. The falling block fell at peak 26 in
round 6, referee-certified in round 7: c(14) at most 20. The same note is
placed at directions/resisters/round4/README.md item 3 of Section "What is
not claimed".]

4. The 36-move and 85-move Carreras certificates are used only as recorded by
   round 3. I did not re-run his verifier.
5. The cap-26 numbers are state counts, computed and not derived, and they
   count states rather than classes.
6. The first cap-26 run from `BBAAABa,BBabABA`, the one that found the fall,
   was stopped by the machine and its working files were deleted to make room
   for the later runs. The state counts of that run are recorded from its state
   file, and only the certificate it produced is shipped.
7. The merge of the eight-member block of Section 4 is certified as one class
   by explicit paths, and those paths are the only evidence about it. No claim
   is made that its members are trivial, and the standard pair was not reached
   at cap 26.

## 10. Files and exact commands

Files of this direction in `directions/resisters/round4/certs_round5/`.

| file | what it is |
| --- | --- |
| `mergebox.c` | the disk-backed cap-26 explorer, the twelve moves, targets, per-layer files |
| `f2.py` | words, the twelve moves, class keys, replay, path reversal |
| `enc.py` | the 62-bit state encoding of `acx.c`, for target files |
| `backwalk.py` | the twelve predecessors of a state, and binary search over a layer file |
| `reconstruct_one.py` | backward reconstruction of a path from the layer files, then replay |
| `transport.py` | the sigma-transported path, class paths, and the short path to the standard pair |
| `fall.py` | the 173-move certificate, the six-move swap, and the eight permutations |
| `groups.py`, `mkgroups.py` | the eight blocks and the target files |
| `all66plusstd.u64` | the 72 target states watched by every cap-26 run |
| `symmetry_check.py` | the machine check of the Sigma lemma and the orbit table |
| `fall_g4.txt`, `fall_group8.txt` | the falling certificates, one line `start|moves|end` |
| `g5_all_pairs.txt`, `g1_all_pairs.txt`, `g2_pair.txt` | the merge certificates, same format |
| `G1.log`, `G1b.log`, `G2.log`, `G2b.log`, `G2c.log`, `G3.log`, `G3b.log`, `G5.log`, `G5b.log`, `G6.log`, `G7.log` | the raw cap-26 runs |
| `G1_state.txt`, `G2_state.txt` | the resume files of the stopped runs |
| `g5_p1.txt` to `g5_p4.txt`, `g1_paths.txt`, `g1_paths_b.txt`, `g2_path.txt` | the reconstructed paths with their peaks |

Compile and reproduce, from `directions/resisters/round4/certs_round5/` with a
scratch directory `../w5/`:

```
gcc -O2 -o mergebox mergebox.c
gcc -O2 -o acx ../acx.c
./acx count 10 a,bb 1                                  # 67,768 states
./acx count 24 BBAAABa,BBabABA 1                       # 9,432,136
./acx count 25 BBAAABa,BBabABA 1                       # 24,781,832
./acx count 24 BBAAbaa,BBabAbA 1                       # 67,181,488
./acx count 24 BBAABBa,BAbABaa 1                       # 17,638,096
mkdir -p ../w5/g6 && ./mergebox 26 ../w5/g6 BBAABBa,BAbABaa all66plusstd.u64
                                                       # EXHAUSTED 62 108428384
mkdir -p ../w5/g7 && ./mergebox 26 ../w5/g7 BBBAbbA,BAAAABa all66plusstd.u64
                                                       # EXHAUSTED 72 103130376
cd ../../../../directions/c14
python3 replay14.py ../../resisters/round4/certs_round5/fall_g4.txt
python3 replay14.py ../../resisters/round4/certs_round5/fall_group8.txt
python3 replay14.py ../../resisters/round4/certs_round5/g5_all_pairs.txt
python3 replay14.py ../../resisters/round4/certs_round5/g1_all_pairs.txt
python3 replay14.py ../../resisters/round4/certs_round5/g2_pair.txt
```

The target file `all66plusstd.u64` holds the 66 exact states together with six
further states, of which four are the standard pair up to inverting relators,
and `mkgroups.py` shows how it was written. The five `replay14.py` lines on the certificate files print, in order,
`replayed 1 certificates, 0 failed, longest 179`, `replayed 8 certificates, 0
failed, longest 191`, `replayed 6 certificates, 0 failed, longest 114`,
`replayed 28 certificates, 0 failed, longest 363` and `replayed 1 certificates,
0 failed, longest 111`.

## 11. Sources and credit

The 66 presentations, their round-3 and round-4 bounds, the twelve-move
semantics and the two reference engines come from `directions/resisters/`
(rounds 3 and 4, members m7 and m1) and `directions/c14/` (round 2, member m4).
The disk-backed layer method is round 4's `directions/cap21/rawbox4.c` (member
m5), reused here with a different encoding. The six-move relator swap is from
`toolkit/lean/AC4.lean`, and the independent replayer `replay14.py` is round
2's. Carreras's two merge pairs are reported from `directions/c14/carreras/`,
whose source is J. Carreras, arXiv:2607.23611, artifact
`joe-carr-data/ac-certificates`. No literature claim is made in this file
beyond that reported item.
