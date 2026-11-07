# The hardness measure of Shehper et al. tested on our data

COORDINATOR NOTE, 2026-11-04 23:30 UTC: accepted as the Round 3 F10 deliverable
(swarm smw2opo0o, member m9) after fresh refereeing. Every computation was rerun
by the coordinator from this copy, including the full cap-20 barcode (states,
bars, xtab and ytab byte-identical) and the 52,744-certificate replay. The files
were copied here from the member's working directory
`.ultramath/smw2opo0o/m9/hardness/`, which remains intact; the symlinks `c14`
and `pu` here point to `../c14` and `../pu-enumeration`.

COORDINATOR UPDATE, 2026-11-05 (round 4, from directions/worst-case/, member m2
of swarm smw2woueq, accepted after fresh refereeing): the l-increase rows of
Section 4.2 are bounds attached to the round-2 certificates, and the exact
invariant is now known on the whole solved sample. A complete reverse-system
breadth-first search at caps 11 to 15 gives the exact l-increase: 0 for 52,680
of the 52,744 presentations and 1 for 64 (all of total length 12); every
length-13 and length-14 presentation has l-increase exactly 0. Section 4.2's
rows at bounds 2 to 6 (9,484 cases) are strictly weaker than the truth, exactly
as this report's own wording says they may be. The no-correlation verdict of
Section 6 is therefore sharpened: the invariant is constant on all but 64 cases
of the sample. The same computation gives exact minimal move counts (max 45 at
cap 15, mean 12.06, against the archive certificates' mean 25.68), and the
91-move worst case of Section 4.2 has exact minimum 44 at cap 15; see
directions/worst-case/notes.md.

Direction F10 of round 3, swarm smw2opo0o, member m9. This file answers Q20 of
OPEN_QUESTIONS.md with computations on our datasets. Nothing here is a claim
about the truth or falsehood of the Andrews-Curtis conjecture.

Labels. **QUOTED** means the words are in the source at the identifier given and
I read them there. **COMPUTED** means I ran code in this directory and the exact
command is in Section 7. **ARGUMENT** means reasoning of mine. **UNVERIFIED**
means I could not check it.

## 0. Summary

1. The measure of Shehper et al. is a barcode, namely the multiset of
   (birth, death) pairs of the persistent reduced homology in degree 0 of the
   length filtration of the Andrews-Curtis graph, together with the
   per-presentation invariant $\ell$-increase from which it is built
   (**QUOTED**, Section 1).
2. The published computation restricts the graph to presentations that admit a
   trivialization inside the length cap. That restriction removes every
   component whose trivializability is unknown, so the published numbers are
   computed exactly where the difficulty is already settled (**ARGUMENT** from
   the quoted definition, Section 2.1).
3. I computed the barcode exactly for the one component that contains our hard
   case, the component of AK(3), at every cap from 13 to 20 total relator length.
   At cap 20 the component has 51,411,456 states, 1,751 finite bars, and bar
   length counts $h_1 = 1360$, $h_2 = 232$, $h_3 = 86$, $h_4 = 32$, $h_5 = 40$,
   $h_6 = 1$ (**COMPUTED**, Section 3). This is new data: nobody has computed
   this barcode before, and the published approximation cannot reach this
   component at all.
4. The per-presentation invariant does not track difficulty on our solved data.
   Among 52,744 certified trivializations at total length 12 to 14, the
   $\ell$-increase is exactly $0$ for 4,780 of them, and those 4,780 include the
   case that needs the most moves in the whole sample, 91 moves. The rank
   correlation between the invariant and the number of moves is
   $+0.006$ (**COMPUTED**, Section 4.2).
5. The invariant does order the two published families correctly on the bounds
   we can certify: AK(2), which is AC-trivial in 14 moves, has
   $\ell$-increase at most $4$, while AK(3) has $\ell$-increase at least $8$
   inside the searched move set (**COMPUTED** with one move-set caveat,
   Section 4.3).
6. It does not separate the solved presentations of length 12 to 14 from the 164
   resisters: solved cases are certified at $\ell$-increase at most $6$ and
   resisters are certified at at least $4$, with overlap at 4, 5 and 6, and 22
   resisters carry no bound at all (**COMPUTED**, Section 4.4).

The short verdict for practice: $\ell$-increase and the barcode are useful as
certified bounds and as an exact description of a component, and neither is
supported by our data as a difficulty score.

## 1. The measure, from the source

Source: A. Shehper, A. M. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen,
Y. Qiu, P. Kucharski, Z. Wang, S. Gukov, *What makes math problems hard for
reinforcement learning: a case study*, arXiv:2408.15332v2 (submitted 27 August
2024, this version 11 February 2025), NeurIPS 2025 proceedings. I fetched
`https://arxiv.org/abs/2408.15332` and `https://arxiv.org/html/2408.15332v2` and
read the text; the proceedings PDF at
`https://proceedings.neurips.cc/paper_files/paper/2025/file/ea8c9cd935dc62e0288bbf33a15e65e9-Paper-Conference.pdf`
returns status 200. The extracted text I read is kept as
`source_2408.15332v2.html.txt` in this directory. The two versions have different
section numbering, so every quotation below is from version 2 of the arXiv
preprint.

**Per presentation** (**QUOTED**, Section 7, opening paragraph): "The minimum
increase in length across all possible AC-trivializations serves as an invariant
of the presentation, its $\ell$-increase, which is correlated with how hard it is
to trivialize, as depicted in Figure 5 (B)." The same section defines the
$\ell$-increase of a path $\gamma = (\pi_0,\dots,\pi_N)$ as
$\max_{i} \ell(\pi_i) - \ell(\pi_0)$.

**Globally** (**QUOTED**, Section 7.1): "We propose that the multiset consisting
of all such pairs $(\text{birth}, \text{death})$, excepting the component defined
by the trivial presentation, serves as a principled hardness measure for the AC
trivialization problem." Section 7.2 identifies it: "this multiset coincides with
a key invariant from topological data analysis: the barcode of the persistent
reduced homology in degree 0 of the associated filtered based graph", where the
filtration is $\Gamma_k$, the induced subgraph on all presentations of length at
most $k$ (Section 7.2.3). Section 7.2.3 adds that "the absence of infinite bars
in this barcode is equivalent to the AC conjecture".

**Their finite approximation** (**QUOTED**, Section 7.3): "For
$L \in \{11,\dots,16\}$ we take the induced subgraph containing all nodes
admitting a trivialization path containing only presentation of length at most
$L$." For each approximation they compute the barcode and then "count the number
$h_i$ of pairs $(b,d)$ with $d-b=i$". Their table for the AC moves reports, at
$L=11$, 350,356 nodes, 1,002,439 edges, $h_1=4$, $h_2=0$, $h_3=0$; at $L=16$,
64,623,652 nodes, 185,162,236 edges, $h_1=1034$, $h_2=88$, $h_3=20$
(**QUOTED**, their Table in Section 7.3).

## 2. What is computable on our data, and what is not

### 2.1 The published approximation removes the unresolved components

The node set of the approximation is the set of presentations admitting a
trivialization whose presentations all have length at most $L$. A presentation
in this set is, by definition, AC-trivial. So the approximation is the
length-truncated graph on the trivializable presentations, and a connected
component that is not known to be trivializable contributes no node to it
(**ARGUMENT**, directly from the quoted definition).

Consequence. AK(3) and every one of the 164 resisters of `directions/c14/` sit in
components that are not known to be trivializable, so the published computation
of the barcode assigns them nothing. The measure is exact where the difficulty is
already settled and undefined where it is not. This is the main structural
finding of this direction, and it is a fact about the definition rather than
about the conjecture.

### 2.2 What can be computed anyway

For the component of AK(3) the barcode is computable without any trivialization,
because a barcode needs the graph and the node weights only. I computed it
exactly for the component inside the total-length box, for every cap from 13 to
20. The box is the one of `directions/pu-enumeration/`: states are pairs of
reduced words in $F(x,y)$ with $|u|+|v| \le T$, moves are $\mathrm{inv}$,
$\mathrm{mul}$ and conjugation by words of length at most $K$, and the
enumeration is the connected component of AK(3). The barcode of the component is
the barcode of the same filtered graph that the paper defines, restricted to this
component, so it can be compared with the published one in construction even
though the two node sets differ.

## 3. The exact barcode of the AK(3) component

Program: `hbar.c`, written from the definitions and sharing no code with
`directions/pu-enumeration/rawbox.c`. It enumerates the component, then processes
the states in order of increasing total length and maintains connected
components with the union-find elder rule: a component with birth $b$ that merges
at level $d$ into a component of strictly smaller birth contributes the bar
$[b,d)$, and the component that never merges contributes the infinite bar
(**COMPUTED**). Per state it also records the BFS distance in moves and the
bottleneck level $\mathrm{conn}(v)$, the least $k$ such that $v$ is connected to
AK(3) inside $\Gamma_k$, so $\mathrm{conn}(v)-13$ is the analogue of
$\ell$-increase with AK(3) as the base node.

| $T$ | states | finite bars | $h_1$ | $h_2$ | $h_3$ | $h_4$ | $h_5$ | $h_6$ | components at level 13 |
|----:|-------:|------------:|------:|------:|------:|------:|------:|------:|----------------------:|
| 13 | 168 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| 14 | 168 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| 15 | 6,864 | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 2 |
| 16 | 20,560 | 11 | 8 | 2 | 1 | 0 | 0 | 0 | 4 |
| 17 | 857,808 | 167 | 112 | 44 | 7 | 4 | 0 | 0 | 12 |
| 18 | 2,014,992 | 247 | 176 | 48 | 19 | 4 | 0 | 0 | 12 |
| 19 | 23,609,984 | 1,087 | 816 | 184 | 54 | 16 | 16 | 1 | 24 |
| 20 | 51,411,456 | 1,751 | 1,360 | 232 | 86 | 32 | 40 | 1 | 24 |

Resource use. The program needs 7 bytes per state for the words, 28 bytes per
state for the union-find and bookkeeping arrays, and a hash table of 8 bytes per
slot; with the state store preallocated to the known count of 51,411,456, the
cap-20 run peaks at 3.0 GB of resident memory and takes 313 s
(**COMPUTED**). Small caps need proportionally less. The preallocation option
`-n` exists because growing the store by doubling would otherwise need about
5.9 GB at cap 20, and this VM had less than that free while other round-3
directions were running.

The surviving component is born at 13 in every case and never dies inside the
box, so it contributes the one infinite bar of the truncation. At cap 20 the
longest finite bar is $[13,19)$ and the component it kills has 4,118,519 states.
The full multiset at cap 20 is

```
(13,15):4 (13,16):10 (13,17):8 (13,19):1 (14,15):40 (14,16):20 (14,17):4
(14,19):16 (15,16):112 (15,17):112 (15,18):24 (15,19):24 (15,20):24
(16,17):184 (16,19):32 (17,18):168 (17,19):88 (17,20):16 (18,19):480
(18,20):8 (19,20):376
```

**COMPUTED**. The bar count grows with the cap, as it must, because a bigger box
contains more components that are born and killed. The published $h_1$ grows in
the same way, from 4 at $L=11$ to 1034 at $L=16$ (**QUOTED**), so the growth is a
property of the truncation and not of our component.

### 3.1 Checks on the barcode

1. **State counts against an independent enumerator.** At all eight caps my
   state counts equal the tuple counts of `directions/pu-enumeration/rawbox.c`
   as recorded in its `pu.md` table: 168, 168, 6,864, 20,560, 857,808, 2,014,992,
   23,609,984 and 51,411,456 (**COMPUTED**). `rawbox.c` follows moves forward
   only, so its count is the size of a directed reachability set. My program can
   follow moves in both directions, and the two counts agree exactly at caps 13
   to 19 and at cap 20, which means that inside the box every state reachable
   from AK(3) also reaches it and the directed and undirected components
   coincide.
2. **Bar multiset against a second implementation.** `check_barcode.py` recomputes
   the barcode from the edge list and the node weights by a different method:
   for every level it recomputes the components of the induced subgraph from
   scratch by breadth first search and then applies the merge rule. The two
   multisets agree exactly at caps 15, 16, 17 and 18: 1, 11, 167 and 247 bars,
   with bar lengths $\{2:1\}$, $\{1:8, 2:2, 3:1\}$, $\{1:112, 2:44, 3:7, 4:4\}$
   and $\{1:176, 2:48, 3:19, 4:4\}$ (**COMPUTED**). The cap-18 check reads
   12,147,792 undirected edges over 2,014,992 states.
3. **The rank identity.** For a graph filtration the number of components of
   $\Gamma_k$ equals one plus the number of bars $[b,d)$ with $b \le k < d$. This
   holds at every level from 13 to $T$ for every cap from 15 to 20
   (**COMPUTED**).
4. **Two record layouts.** The first implementation stored the two relators as
   one byte per letter, 50 bytes per state, and the final one stores two bits per
   letter, 7 bytes per state. The two agree exactly at every cap from 13 to 20 on
   the state count, the number of finite bars, the full bar length histogram and
   the component count at every level (**COMPUTED**). The second is the one
   shipped, and both are the same algorithm.
5. The first version of `hbar.c` crashed at 23 million states on a stale pointer
   into a reallocated arena pair and, after I fixed that, on a use after free in
   the hash growth path. Both were found by the checks above, in particular by
   the appearance of a phantom state of total length 0 at node 65537. The
   numbers in this report are from the fixed program, and every number in the
   table reproduces on a rerun.

## 4. Tests of the predictive claim

### 4.1 Inside the component: the relative $\ell$-increase against move distance

Data: all 51,411,456 states of the cap-20 component, with $\mathrm{conn}$ from
Section 3 and the BFS distance from AK(3) in moves (**COMPUTED**).

| pair of variables | Spearman $\rho$ | $\rho^2$ |
|---|---:|---:|
| $\mathrm{conn}$ and depth | $+0.1750$ | 0.031 |
| length and depth | $+0.0513$ | 0.003 |
| length and $\mathrm{conn}$ | $+0.8652$ | 0.749 |
| partial: $\mathrm{conn}$ and depth given length | $+0.2607$ | |

With 51 million points the permutation null of $\rho$ has standard deviation
about $1.3 \times 10^{-4}$, so every nonzero value is far outside the null and
significance carries no information. The effect sizes are what matter, and they
say the following. The relative $\ell$-increase carries more information about
move distance than length does, $\rho^2$ of 3.1 percent against 0.3 percent, and
its information is not only the length effect, since the partial correlation is
$+0.26$.

Inside a fixed length the picture is stronger:

| length | states | $\rho(\mathrm{conn},\text{depth})$ |
|---:|---:|---:|
| 13 | 4,032 | $+0.915$ |
| 14 | 15,424 | $+0.590$ |
| 15 | 241,856 | $+0.697$ |
| 16 | 336,288 | $+0.681$ |
| 17 | 2,520,832 | $+0.631$ |
| 18 | 3,280,096 | $+0.604$ |
| 19 | 20,185,152 | $+0.324$ |
| 20 | 24,827,776 | undefined, $\mathrm{conn}$ is constant 20 |

The length 13 row is the sharpest, because there the length is fixed at the
minimum and the invariant varies: 168 states connect at level 13 and have mean
depth 4.2, 168 connect at 15 with mean depth 18.1, 336 at 16 with mean 14.0, 1,344
at 17 with mean 36.7, and 2,016 at 19 with mean 59.5 (**COMPUTED**).

Mean depth also rises with length, from 44.1 at length 13 to 57.8 at length 20,
with minimum depth 0 at length 13 and minimum depth at most 2 at every other
length (**COMPUTED**). So the qualitative statement that longer presentations are harder
holds inside this component, and it holds weakly, with $\rho^2 = 0.003$.

### 4.2 Outside the component: the invariant against the number of moves

Every presentation in these datasets is a balanced two-generator presentation
whose exponent-sum determinant is $\pm 1$, so relator count and abelianisation
are constant and need no adjustment. The confound that matters is word length,
and Section 4.1 handles it by a stratified analysis and by a partial correlation
(**COMPUTED**).

Data: the 52,744 certificates of `directions/c14/certs_12.txt`,
`certs_13.txt` and `certs_14.txt`, replayed by my own checker `lincrease.py`,
which shares no code with `directions/c14/replay14.py`. All 52,744 replay with
0 failures, and for each I record the peak total length along the path, so the
$\ell$-increase is at most peak minus start length (**COMPUTED**).

| $\ell$-increase | cases | mean moves | median moves | max moves |
|---:|---:|---:|---:|---:|
| exactly 0 | 4,780 | 33.5 | 31 | 91 |
| at most 1 | 38,480 | 24.1 | 24 | 45 |
| at most 2 | 4,607 | 28.7 | 28 | 54 |
| at most 3 | 3,632 | 27.7 | 27 | 48 |
| at most 4 | 299 | 26.5 | 26 | 42 |
| at most 5 | 856 | 27.9 | 28 | 43 |
| at most 6 | 90 | 24.8 | 25 | 31 |

The first row is the exact value of the invariant, because the value $0$ is both
the certified bound and the lower bound. Every other row is the value of the
certified upper bound on that group of cases, and the exact invariant of those
cases may be smaller. The rows are not cumulative.

The bound is exactly $0$ for 4,780 presentations, because a path that never
exceeds the starting length proves $\ell$-increase $\le 0$ and the invariant is
non-negative. Those 4,780 cases need between 14 and 91 moves, and the hardest
case among the 52,744 replayed here, 91 moves, has $\ell$-increase exactly $0$. The
rank correlation between the bound and the number of moves is $+0.0060$ over all
52,744 cases (**COMPUTED**), which is no correlation. A shorter path need not
stay near the start, and a near-the-start path need not be short.

### 4.3 Known easy against known hard

| case | status | certified $\ell$-increase | source of the bound |
|---|---|---:|---|
| the 14-move AK(2) chain of Havas and Ramsay, Section 3 | AC-trivial | at most 4 | printed chain, peak length 15 from start length 11 (**COMPUTED**) |
| the 21-move AK(2) chain of Miasnikov, Section 5 | AC-trivial | at most 14 | printed chain, peak length 25 from start length 11 (**COMPUTED**) |
| AK(3) | unresolved | at least 8 | no state of the cap-20 component has total length below 13 |
| 52,744 solved at length 12 to 14 | AC-trivial | at most 6 | BFS certificates (**COMPUTED**) |
| 26 resisters at length 14 | unresolved | at least 4 | exhaustive failure at cap 17 |
| 8 resisters at length 13 and 40 at length 14 | unresolved | at least 5 | exhaustive failures at caps 17 and 18 |
| 68 resisters at length 14 | unresolved | at least 6 | exhaustive failure at cap 19 |
| 22 resisters | unresolved | no bound | search stopped by a pair budget |

Both chains start at a presentation of total relator length 11 and end at
$(b^{-1},a^{-1})$, which is the standard pair with the two relators exchanged and
inverted. My computation uses only the start length and the peak length of the
printed chain, and the attribution of the two chains to AK(2) is the published
one (**QUOTED** from the two papers as reproduced in `survey/computational.md`).

The two published families are ordered correctly: AK(2) is at most 4 and AK(3) is
at least 8, so the invariant separates the family member that is trivial in 14
moves from the member that nobody has trivialized (**COMPUTED**, with the caveat
below).

Caveat on the AK(3) bound. The cap-20 census was run with conjugating words of
length at most 1 (with 2 and 3 giving the same state and class sets at caps 18,
19 and 20), and it shows that no state reachable from AK(3) inside the box has
total length below 13. A general conjugation by a word of length $k$ is a
sequence of $k$ single letter conjugations, and those intermediate states can
exceed the endpoint lengths by up to $2k$, so the bound at least 8 is proved for
the searched move set and not for unrestricted conjugators (**ARGUMENT**). I did
not close that gap.

### 4.4 Solved against resisting at lengths 12 to 14

The certified intervals overlap. Solved presentations are certified at
$\ell$-increase at most 6, with 51,798 of them at most 4, while resisters are
certified at at least 4, 5 or 6 depending on the cap that exhausted their
component, and 22 resisters have no bound (**COMPUTED**, table in 4.3). Hence no
threshold on the certified values separates the 52,744 solved cases from the 164
resisters, and the data of `directions/c14/` cannot decide whether the invariant
would separate them if it were computed exactly.

## 5. Correlation table

| # | test | data | $n$ | $\rho$ | $\rho^2$ | null sd of $\rho$ | reading |
|--:|---|---|---:|---:|---:|---:|---|
| 1 | relative $\ell$-increase against move depth | AK(3) component, cap 20 | 51,411,456 | $+0.1750$ | 0.031 | $1.3\times10^{-4}$ | weak positive, larger than length alone |
| 2 | length against move depth | same | 51,411,456 | $+0.0513$ | 0.003 | $1.3\times10^{-4}$ | very weak positive |
| 3 | length against relative $\ell$-increase | same | 51,411,456 | $+0.8652$ | 0.749 | | the invariant is mostly length |
| 4 | certificate moves against $\ell$-increase bound | 52,744 solved cases | 52,744 | $+0.0060$ | 0.00004 | | no relation |
| 5 | class minimal length against certificate moves | the 79,680 published classes | 79,680 | $+0.0564$ | 0.003 | | very weak positive |
| 6 | start length against $\ell$-increase bound | 52,744 solved cases | 52,744 | $-0.1464$ | 0.021 | | weak negative |

Row 5 uses the class list and the class certificates of
`directions/pu-enumeration/`, whose mean certificate length is 58.240 moves and
whose lengths run from 13 to 20 (**COMPUTED**), and it reproduces the published
mean of 58.24. The shipped class file stores each class in its canonical cyclic
form, so the recorded length is the least total length of any member of the
class, and row 5 is not confounded by which member the search happened to reach
(**ARGUMENT** from the constructor of the class key in `rawbox.c`, and the two
lengths I computed, from the file and from cyclic reduction of each relator,
agree for all 79,680 classes).

The means rise monotonically with the class length, which is the same direction
as the "longer is harder" intuition:

| class minimal length | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| classes | 24 | 80 | 1,032 | 1,112 | 5,688 | 6,456 | 31,240 | 34,048 |
| mean moves | 43.7 | 47.6 | 49.8 | 54.8 | 56.1 | 57.2 | 58.0 | 59.4 |
| max moves | 63 | 81 | 131 | 126 | 136 | 136 | 139 | 142 |

So the trend is monotone in the means and negligible in the ranks, because
31,240 and 34,048 of the classes sit at lengths 19 and 20 (**COMPUTED**).

The null standard deviations in rows 1 and 2 come from 200 seeded permutations of
a 200,000-state subsample, rescaled to the full size, seed 20261104
(**COMPUTED**). At this sample size the null is useless for significance, and I
report the effect sizes instead. For rows 4 to 6 I do not give a null because the
reading is already negative: an effect of $0.006$ is negligible whatever its
significance.

## 6. Verdict on Q20

The measure is well defined, and both halves of it are computable in our setting.
The barcode is now computed exactly for the component of AK(3), which the
published approximation cannot reach, and the per-presentation invariant can be
bounded on every case where a search has succeeded or an exhaustive search has
failed.

As a predictor of search difficulty the evidence on our data is mixed and mostly
negative:

1. Within one component and at a fixed length, the relative $\ell$-increase
   predicts move distance with $\rho$ between $0.32$ and $0.92$ (**COMPUTED**,
   Section 4.1). That is real support for the intuition behind the measure.
2. Across the solved population, the published per-presentation invariant has no
   rank relation with the number of moves, and it takes its minimum value on the
   case that needs the most moves (**COMPUTED**, Section 4.2). As a score of
   individual presentations it is not supported.
3. On the cases that matter, the ones nobody has trivialized, the published
   approximation is undefined by construction, and the per-presentation invariant
   is bounded only by failed searches (**ARGUMENT** and **COMPUTED**, Sections
   2.1 and 4.4).

A defensible use of the measure on our data is the following. Report
$\ell$-increase as a certified bound, "no trivialization stays below length $c$",
and report the exact barcode of a component when the component is what is being
studied. Do not report either as a difficulty score for individual
presentations.

## 7. Exact commands

All commands run from this directory. Two symbolic links are used in the
commands: `pu` points to `directions/pu-enumeration` and `c14` to
`directions/c14` of the repository root.

```
gcc -O2 -o hbar hbar.c
./hbar 20 1 -u -n 51411456 -b bars_u_20.txt -x xtab_20.txt -y ytab_20.txt   # 313 s, 3.0 GB
for T in 13 14 15 16 17 18 19; do ./hbar $T 1 -u -b bars_u_$T.txt > out$T.txt; done
./hbar 16 1 -u -s states_16.txt -e edges_16.txt -b bars_u_16.txt
python3 check_barcode.py states_16.txt edges_16.txt bars_u_16.txt
./hbar 17 1 -u -s states_17.txt -e edges_17.txt -b bars_u_17.txt
python3 check_barcode.py states_17.txt edges_17.txt bars_u_17.txt    # needs 100 MB disk
./hbar 18 1 -u -s states_18.txt -e edges_18.txt -b bars_u_18.txt
python3 check_barcode.py states_18.txt edges_18.txt bars_u_18.txt    # needs 200 MB disk
python3 lincrease.py c14/certs_12.txt c14/certs_13.txt c14/certs_14.txt \
        --resisters c14/final_classes.txt
python3 analyze.py
python3 ak2_lincrease.py
```

`run_all.sh` runs every computation in this file, including the cap-20 run. It
takes about twelve minutes and peaks at 3.0 GB of memory. The number 51411456 in
the `-n` option is the state count, which the program itself prints; it is used
only to preallocate the store, and a wrong value costs time rather than
correctness.

## 8. What I could not verify

1. I did not reproduce the published $h_i$ table, and I did not run the authors'
   code or data. Their node set is not ours, so the two tables are not
   comparable term by term; I use their numbers only for the fact that $h_i$
   grows with the cap, which our numbers reproduce (**UNVERIFIED** for their
   table as a whole).
2. The AK(3) lower bound of 8 holds for the searched move set, as stated in
   Section 4.3. I did not prove the corresponding statement for unrestricted
   conjugating words.
3. The $\ell$-increase bounds from certificates are upper bounds. Only the value
   $0$ is exact, since the invariant is non-negative.
4. I did not compute the barcode of the conjugation class quotient, which is what
   the shipped class list of `directions/pu-enumeration/` would give most cheaply.
   Only the state-level barcode is computed here.
5. Significance statements at $n = 51$ million are meaningless, and I report
   effect sizes and seeded null standard deviations instead.
6. Nothing here says anything about the conjecture. An infinite bar in the
   truncation at cap 20 is consistent with AK(3) being non-trivial and with the
   trivialization lying above length 20.

## 9. Files

| file | what it is |
|---|---|
| `hbar.c` | the enumerator and barcode program, an independent implementation |
| `check_barcode.py` | second implementation of the barcode, level by level |
| `lincrease.py` | independent certificate replayer and $\ell$-increase bounds |
| `ak2_lincrease.py` | the two published AK(2) chains, replayed, with peak lengths |
| `analyze.py` | the correlation tests, seeded, deterministic |
| `run_all.sh` | runs the checks |
| `bars_u_T.txt`, `outT.txt`, `xtab_20.txt`, `ytab_20.txt` | computed data |
| `lincrease_dump.txt`, `analysis_results.json` | computed data |
| `source_2408.15332v2.html.txt` | the source text I quoted |
