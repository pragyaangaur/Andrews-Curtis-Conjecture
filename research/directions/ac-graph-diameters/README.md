# Exact diameters of the Andrews-Curtis graphs of finite perfect groups

Direction d11, member m6 of swarm smw2woueq, round 4. This file answers question
Q18 of `OPEN_QUESTIONS.md` in the range stated below, with exact values rather
than bounds. Every diameter in this file is the output of an exhaustive
breadth-first search over the whole graph, and section 8 lists the independent
recomputation that reproduces the smallest case exactly. Nothing in this file is
a claim about the Andrews-Curtis conjecture itself.

## 1. The result

Let $G$ be a finite perfect group, $k\ge 2$, and let $\Delta_k(G)$ be the
Andrews-Curtis graph of Borovik, Lubotzky and Myasnikov: vertices are the
normally generating $k$-tuples of $G$, and edges are the four families of
elementary AC-moves with conjugator set $S=G$ (section 2). Then:

1. $\Delta_2(G)$ is connected for all eight perfect groups of order at most 720
   and has diameter **8**, except for $G=PSL(2,8)$ where the diameter is **9**.
2. $\Delta_3(A_5)$ is connected and has diameter **9**.
3. The diameter does not grow with the order of the group in this range. It is
   the same for $A_5$ (order 60) and for $SL(2,9)=2.A_6$ (order 720).
4. In every case the diameter is attained at a $k$-tuple with a trivial entry.
   Tuples with no trivial entry have eccentricity at most 8, and for four of the
   eight groups at $k=2$ at most 7 (section 5).
5. The same diameters are obtained with the three-move set of the free case
   (inversion, right multiplication by another entry, conjugation) instead of
   the four BLM families (section 4.2). The diameter is therefore not an
   artefact of allowing left multiplication.
6. On the closely related graph of *generating* tuples (ordinary generation,
   the convention of Nielsen classes) the diameters are 5, 5, 6, 6, 6, 6, 6, 7
   (section 4.3). Insisting on normal generation, which is the free-case
   convention, raises the diameter by 2 or 3.
7. The product replacement move set alone gives a disconnected graph with many
   components, and the diameter of its components is larger than the AC
   diameter. Adding inversions and left multiplications merges the components,
   and adding conjugations shrinks the diameter. Section 6 gives the exact
   numbers for $A_5$, $SL(2,5)$ and $PSL(2,7)$.

## 2. Definitions

The definitions are those of Borovik, Lubotzky and Myasnikov, *The Finitary
Andrews-Curtis Conjecture*, Progress in Mathematics 248 (2005) 15-30,
DOI 10.1007/3-7643-7447-0_2, arXiv:1103.1295. I checked the identifier and the
abstract live on 5 November 2026; the abstract states that the paper describes
the connected components of the Andrews-Curtis graphs of finite groups. The
move list below is the list quoted in `survey/nielsen.md`, Section 2.2, from
Section 1 of that paper.

Let $G$ be a finite group and $k\ge 1$. A $k$-tuple $(x_1,\dots,x_k)$ of
elements of $G$ is *normally generating* when its normal closure is $G$. Write
$N_k(G)$ for the set of normally generating $k$-tuples. For a subset $S\subset G$
the $AC_S$-moves are

* (1) $x_i\mapsto x_i x_j^{\pm 1}$ for $i\ne j$,
* (2) $x_i\mapsto x_j^{\pm 1} x_i$ for $i\ne j$,
* (3) $x_i\mapsto x_i^{-1}$,
* (4) $x_i\mapsto w^{-1} x_i w$ for $w\in S$.

With $S=G$ these are the AC-moves, and $\Delta_k(G)$ is the graph with vertex set
$N_k(G)$ and an edge for each move. Every move preserves normal generation, so
the graph is well defined. In the free group the same moves act on the
$k$-generator $k$-relator presentations of the trivial group, and the
conjecture says that $\Delta_k(F_k)$ is connected for $k\ge 2$.

Two further conventions are computed for comparison.

* The *free-case move set* uses family (1) with the exponent $+1$ only, that is
  $x_i\mapsto x_i x_j$, together with (3) and (4). Those are exactly the three
  moves written down in `OPEN_QUESTIONS.md`, Section 1.
* The *ordinary generation convention* replaces $N_k(G)$ by the set of
  generating $k$-tuples. Moves (1) to (4) preserve generation as well, so this
  is again a graph. It is the graph whose components are the Nielsen classes
  refined by conjugation, and it is the finite analogue closest to the product
  replacement graph.

I use $N_k(G)$ as the default because it is the definition of the question.

## 3. Method, and why the values are exact

For each group the vertex set is described without enumerating tuples one at a
time. A tuple fails to be normally generating exactly when all its entries lie
in one proper normal subgroup, so a tuple is a non-vertex exactly when all its
entries lie in one maximal proper normal subgroup. The export from GAP
(`export.g`) lists those subgroups, and the vertex predicate becomes a bit-mask
test on the code of the tuple. The same construction with the maximal subgroups
in place of the maximal normal subgroups gives the ordinary generation
convention.

The search is an ordinary breadth-first search over tuple codes, vectorised
with numpy. It is exhaustive by construction, and the diameter is the number of
the last non-empty level.

The whole computation rests on one symmetry, which makes the exhaustive search
affordable. Let $H$ be the group generated by the automorphisms of $G$ acting
diagonally on $k$-tuples and the permutations of the coordinates. Both kinds of
map carry moves to moves: an automorphism of $G$ carries $x_i\mapsto x_i x_j^{\pm1}$
to $\varphi(x_i)\mapsto\varphi(x_i)\varphi(x_j)^{\pm1}$, and swapping two
coordinates exchanges families (1) and (2). So $H$ acts on $\Delta_k(G)$ by graph
automorphisms, and the eccentricity of a vertex depends only on its $H$-orbit.
One exhaustive BFS from one representative of each orbit therefore gives the
eccentricity of every vertex, and the maximum over the orbits is the diameter.
The certificate of a diameter value is the complete level decomposition of each
orbit BFS: the level sizes sum to the number of vertices of the component, and
$\sum_t t\cdot n_t = |V|^2$ for the distance distribution.

The cost of one orbit BFS is about $|V|\cdot d$ elementary steps, where $d$ is the
number of moves per vertex, $d = k(1+4(k-1)+|G|)$ for the BLM move set. For
$A_5$ at $k=2$ this is $3599\cdot 130$, and the full run over 29 orbits takes
0.2 s. For $PSL(2,11)$ at $k=2$ the same run is $435599\cdot 1330$ per orbit over
221 orbits and takes 8 minutes. Section 10 explains which groups this cost model
puts out of reach here.

## 4. Results

### 4.1 The BLM graph: normally generating tuples, moves (1) to (4) with $S=G$

| $G$ | order | $k$ | vertices | $H$-orbits | diameter | eccentricity profile (ecc: tuples) |
| --- | --- | --- | --- | --- | --- | --- |
| $A_5$ | 60 | 2 | 3599 | 29 | 8 | 5: 1200, 6: 2188, 7: 133, 8: 78 |
| $A_5$ | 60 | 3 | 215999 | 364 | 9 | 6: 1440, 7: 162368, 8: 51795, 9: 396 |
| $SL(2,5)$ | 120 | 2 | 14396 | 93 | 8 | 6: 9824, 7: 4180, 8: 392 |
| $PSL(2,7)$ | 168 | 2 | 28223 | 67 | 8 | 6: 24640, 7: 3445, 8: 138 |
| $SL(2,7)$ | 336 | 2 | 112892 | 229 | 8 | 6: 93436, 7: 18820, 8: 636 |
| $A_6$ | 360 | 2 | 129599 | 78 | 8 | 6: 107181, 7: 22078, 8: 340 |
| $PSL(2,8)$ | 504 | 2 | 254015 | 111 | 9 | 6: 236496, 7: 16392, 8: 889, 9: 238 |
| $PSL(2,11)$ | 660 | 2 | 435599 | 221 | 8 | 6: 392876, 7: 42153, 8: 570 |
| $SL(2,9)=2.A_6$ | 720 | 2 | 518396 | 248 | 8 | 6: 113076, 7: 389848, 8: 15472 |

GAP's perfect groups library contains exactly one perfect group at each of the
orders 60, 120, 168, 336, 360, 504, 660 and 720 and none at any other order up
to 720 (`perf_count.g`, which prints the list and the total 8). So the eight
groups in the table are all the perfect groups of order at most 720.

The column *eccentricity profile* gives, for each value $e$ of the eccentricity,
the number of tuples with that eccentricity. The sum of the column is the vertex
count. At $k=2$ seven of the eight groups have no tuple of eccentricity 5, only
$PSL(2,8)$ has a tuple of eccentricity 9, and the distribution is concentrated
at 6 and 7.

The complete distance distribution of $\Delta_2(A_5)$ is

| distance | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| ordered pairs | 3599 | 120364 | 1426714 | 5130012 | 5297232 | 804720 | 153840 | 13440 | 2880 |

so exactly 2880 of the $3599^2 = 12952801$ ordered pairs are at distance 8. The
distributions of the other seven groups are in `results/`, one JSON file per
run, with the same normalisation.

A consistency check on the vertex counts is available without a search. Each of
the eight groups has the property that every proper normal subgroup lies in the
centre, so the non-vertices are exactly the $k$-tuples with all entries in the
centre. The identity $|N_k(G)| = |G|^k - |Z(G)|^k$ then gives
$14396 = 120^2-2^2$ for $SL(2,5)$, $112892 = 336^2-2^2$ for $SL(2,7)$ and
$518396 = 720^2-2^2$ for $SL(2,9)$, all of which match the computed vertex
counts.

Diameter-realising tuples (element indices, identity is 0 in the tables of the
small groups) are:

| $G$ | $k$ | tuple | tuple at maximal distance |
| --- | --- | --- | --- |
| $A_5$ | 2 | $(3,0)$ | $(16,0)$ |
| $SL(2,5)$ | 2 | $(20,0)$ | $(20,2)$ |
| $PSL(2,7)$ | 2 | $(4,0)$ | $(21,0)$ |
| $SL(2,7)$ | 2 | $(42,0)$ | $(42,3)$ |
| $A_6$ | 2 | $(1,0)$ | $(64,0)$ |
| $PSL(2,8)$ | 2 | $(7,0)$ | $(63,0)$ |
| $A_5$ | 3 | $(3,0,0)$ | $(0,16,16)$ |

Every one of these tuples has a trivial entry. For $A_5$ at $k=2$ the pair
$(3,0)$, $(16,0)$ is joined by the explicit path of eight legal moves

$$(3,0)\to(3,3)\to(27,3)\to(15,3)\to(19,3)\to(19,16)\to(35,16)\to(16,16)\to(16,0),$$

which the checker replays move by move against the definition (section 8). For
$PSL(2,7)$ the pair $(4,0)$, $(21,0)$ is joined by the eight-step path

$$(4,0)\to(4,4)\to(108,4)\to(24,4)\to(24,22)\to(2,22)\to(21,22)\to(21,21)\to(21,0),$$

and for $A_6$ the pair $(1,0)$, $(64,0)$ by

$$(1,0)\to(1,1)\to(10,1)\to(8,1)\to(70,1)\to(64,1)\to(64,65)\to(64,69)\to(64,0).$$

Both are shortest by the level counts of section 4.1, and `geodesics.py`
recomputes them and checks every step (`results/geodesic-PSL2_7.txt`,
`results/geodesic-A6.txt`).

### 4.2 The free-case move set

Replacing family (1) by right multiplication only, as in the free case, does not
change any diameter:

| $G$ | order | $k$ | vertices | $H$-orbits | diameter |
| --- | --- | --- | --- | --- | --- |
| $A_5$ | 60 | 2 | 3599 | 29 | 8 |
| $A_5$ | 60 | 3 | 215999 | 364 | 9 |
| $SL(2,5)$ | 120 | 2 | 14396 | 93 | 8 |
| $PSL(2,7)$ | 168 | 2 | 28223 | 67 | 8 |
| $SL(2,7)$ | 336 | 2 | 112892 | 229 | 8 |
| $A_6$ | 360 | 2 | 129599 | 78 | 8 |
| $PSL(2,8)$ | 504 | 2 | 254015 | 111 | 9 |
| $PSL(2,11)$ | 660 | 2 | 435599 | 221 | 8 |
| $SL(2,9)=2.A_6$ | 720 | 2 | 518396 | 248 | 8 |

This is the closest finite analogue of the moves that the conjecture itself
uses, and the values coincide with section 4.1 in all nine rows.

### 4.3 Ordinary generation

With the vertex set changed to the generating tuples the graph is smaller and
the diameters drop:

| $G$ | order | vertices | $H$-orbits | diameter | eccentricity profile |
| --- | --- | --- | --- | --- | --- |
| $A_5$ | 60 | 2280 | 12 | 5 | 4: 600, 5: 1680 |
| $SL(2,5)$ | 120 | 9120 | 43 | 6 | 5: 4560, 6: 4560 |
| $PSL(2,7)$ | 168 | 19152 | 35 | 5 | 5: 19152 |
| $SL(2,7)$ | 336 | 76608 | 127 | 6 | 5: 7392, 6: 69216 |
| $A_6$ | 360 | 76320 | 32 | 6 | 5: 59040, 6: 17280 |
| $PSL(2,8)$ | 504 | 214704 | 78 | 6 | 5: 114912, 6: 99792 |
| $PSL(2,11)$ | 660 | 335280 | 146 | 6 | 5: 145200, 6: 190080 |
| $SL(2,9)=2.A_6$ | 720 | 305280 | 117 | 7 | 5: 74880, 6: 216000, 7: 14400 |

The difference between the two conventions is the reason the numbers are larger
in section 4.1. Ordinary generation forbids tuples whose entries generate a
proper subgroup, and those are exactly the tuples that make the far corners of
the normally generating graph. For $A_5$ the two vertex counts are 2280 and
3599, and $2280/3600 = 19/30$, the value usually quoted for the probability that
two random elements of $A_5$ generate it (I did not check a source for that
value, and do not rely on it).

### 4.4 Rank three

$A_5$ at $k=3$ has $60^3-1 = 215999$ vertices, 364 orbits, and diameter 9, both
for the BLM move set and for the free-case move set. One rank-three value is not
enough to state a trend in $k$. Computing $SL(2,5)$ at $k=3$ would need about
$1.7\cdot 10^6\cdot 250$ steps per orbit over a few hundred orbits, which is a
few CPU-hours and was not spent.

## 5. Why the diameter is 8 or 9: tuples with a trivial entry

**Lemma.** Let $k\ge 2$, let $G$ be a group, and let $x=(x_1,\dots,x_{k-1},1)$ be a
vertex of $\Delta_k(G)$ whose last entry is trivial. Then the neighbours of $x$
other than $x$ itself are exactly

* $(x_1,\dots,x_i^{-1},\dots,x_{k-1},1)$ for $i<k$;
* $(x_1,\dots,x_i^{w},\dots,x_{k-1},1)$ for $i<k$ and $w\in G$;
* $(x_1,\dots,x_{k-1},x_i^{\pm 1})$ for $i<k$.

Multiplying a nontrivial entry by the trivial one changes nothing, so the
trivial entry can only be replaced by a power of another entry.

*Proof.* Move (1) with $i=k$ sends the trivial entry to $1\cdot x_j^{\pm1}=x_j^{\pm1}$
and leaves the other entries alone; that is the third family. Move (1) with
$i<k$ and $j=k$ multiplies $x_i$ by $1$ and changes nothing. Move (3) inverts
one entry. Move (4) conjugates one entry, and conjugating $1$ gives $1$. Moves
(2) behave like (1) on the other side and give the same three families. $\square$

The content of the lemma is that a vertex with a trivial entry has neighbours of
three kinds: the inverses of its nontrivial entries, their conjugates, and at
most $2(k-1)$ tuples in which the trivial entry has been replaced by a power of
another entry. Inversions and conjugates keep the trivial entry, so they stay in
the cone of tuples with a trivial entry, and each of them preserves the
conjugacy classes of the other entries. Leaving the cone costs a move that
creates a tuple with no trivial entry, and coming back costs another. This is the mechanism behind
the values 8 and 9, and it is visible in the data: the maximal eccentricity
over tuples with no trivial entry is 7 for $A_5$, $PSL(2,7)$, $A_6$ and
$PSL(2,11)$, and 8 for $SL(2,5)$, $SL(2,7)$, $PSL(2,8)$ and $SL(2,9)$, while the
diameter is always attained on a tuple with a trivial entry.

I checked the lemma in the engine rather than only on paper: the neighbour list
produced by the vectorised expansion agrees with a separate tuple-level
implementation of the definitions on 200 random vertices of $\Delta_2(A_5)$ for
each of the move sets used, and the cone description was used to generate the
table of section 4.1.

## 6. The move-set ladder: product replacement, inversions, Nielsen, AC

The question notes that the AC graph sits between the product replacement graph
and its enlargement by inversions. The same machinery measures the gap on three
groups at $k=2$, with vertices the generating pairs. Each entry gives the number
of connected components and, in brackets, the diameters of those components
with their multiplicities.

| moves allowed | $A_5$ | $SL(2,5)$ | $PSL(2,7)$ |
| --- | --- | --- | --- |
| $x_i\mapsto x_i x_j^{\pm1}$ (product replacement) | 44 components, 24 of size 50 and 20 of size 54, all of diameter 6 | 44 components, 24 of size 200 and 20 of size 216, diameter 9 (24) and 8 (20) | 188 components, 48 of size 49, 56 of size 108, 84 of size 128, diameters 5 (48), 8 (98), 9 (42) |
| plus inversions | 3 components, sizes 1080, 600, 600, diameters 9, 8, 8 | 3 components, sizes 4320, 2400, 2400, diameters 10, 9, 9 | 4 components, sizes 6048, 5376, 5376, 2352, diameters 13, 12, 12, 10 |
| plus left multiplication | same 3 components, diameters 7, 6, 6 | same 3 components, diameters 8, 7, 7 | same 4 components, diameters 10, 9, 9, 7 |
| plus conjugation (the AC graph) | 1 component, diameter 5 | 1 component, diameter 6 | 1 component, diameter 5 |

So on these three groups the product replacement graph is disconnected, with 44
to 188 components, and its largest component diameter is 6 to 9. Conjugation by
all of $G$ is what makes the graph connected and small. A component of the
product replacement graph need not be a union of $H$-orbits, because an
automorphism of $G$ can permute the components, so a component can meet an orbit
in a proper part of it. The component counts in the table were therefore
computed on vertices, and the eccentricities inside a component from one BFS per
orbit that the component meets.

The three-component structure of the product-replacement-plus-inversions graph
of $A_5$ (sizes 1080, 600, 600) is reproduced exactly by the independent code of
`survey/nielsen_census.py` when conjugation is switched off, which is a check on
both implementations.

## 7. Relation to the free case, and what these numbers do not measure

The degenerate vertices that realise the diameter have no counterpart in the
free case. For $k=2$ a vertex of the form $(x,1)$ corresponds to a presentation
$\langle x,y \mid r, 1\rangle$ of the trivial group, that is to a one-relator
group $\langle x,y\mid r\rangle$. Every one-relator group with a nontrivial
relator is nontrivial: if the relator involves the generator $x$ up to
conjugacy, the Freiheitssatz of Magnus embeds the subgroup generated by $y$ and
the group is infinite, and otherwise the group has a free factor. So in any
Andrews-Curtis path that starts at a two-relator presentation of the trivial
group with both relators nontrivial, no intermediate presentation has a trivial
relator, and no vertex with a trivial entry is ever reached (argument; the step
that uses the Freiheitssatz is not machine-checked here). The finite AC graph
has a thin far corner made of exactly such vertices, and that corner is where
its diameter lives.

The conclusion I draw is a limit on what this data says. The exact diameters of
$\Delta_k(G)$ answer Q18, and they quantify how much a finite quotient can see in
the sense of the Borovik-Lubotzky-Myasnikov theorem. They do not measure the
difficulty of the free case, because the vertices responsible for the finite
diameter are not reachable there. This is the same phenomenon that round 3
recorded for the published hardness measure: the finite approximation is
undefined or irrelevant exactly where the difficulty is unknown.

## 8. Verification

All commands run from this directory. The data come from `export.g`
(GAP 4.14), the searches from `acdiam.py`, and the checks from `verify.py`.

(1) Independent move enumerator and an exhaustive from-every-vertex BFS.
`verify.py census` takes the move enumerator of `survey/nielsen_census.py`
(written by another member in round 1, with a different algorithm) and runs a
BFS from each of the 3599 vertices of $\Delta_2(A_5)$. Output:

```
{"order": 60, "nvertices": 3599, "bad_neighbours": 0, "diameter": 8,
 "distribution": {"0": 3599, "1": 120364, "2": 1426714, "3": 5130012,
 "4": 5297232, "5": 804720, "6": 153840, "7": 13440, "8": 2880},
 "orbit_prediction_mismatches": 0, "vertices_checked": 3599}
```

The whole distance distribution coincides with the one in section 4.1, and the
eccentricity of all 3599 vertices coincides with the orbit-reduced prediction.
`bad_neighbours` counts pairs (vertex, neighbour not a vertex) and is 0, which
checks the observation of Borovik, Lubotzky and Myasnikov that the AC moves
preserve normal generation.

(2) Random vertices. `verify.py random` runs a full BFS from four seeded random
vertices of $\Delta_2(PSL(2,7))$ and four of $\Delta_2(A_6)$. Each BFS covers all
vertices and its eccentricity equals the orbit prediction; the output is in
`results/verify-random.txt`.

(3) Vertex predicates. For four groups, 300 random pairs were tested both by the
subgroup mask and by direct closure of the pair, with 0 mismatches
(`results/verify-vertexcounts.txt`). The exported automorphisms were checked to be
bijective homomorphisms for all eight groups.

(4) Consistency of every run. For every orbit BFS the level sizes sum to the
number of vertices of the component, and the distance distribution sums to
$|V|^2$. `analyse2.py` recomputes both for all runs and prints them
(`results/analyse.txt`).

(5) Geodesic replay. `verify.py geodesic` extracts a diameter-realising pair of
$\Delta_2(A_5)$, recomputes a shortest path, and checks each step against the
definition; the path of section 4.1 is legal with 8 steps.

(6) A second group, with the round-1 enumerator. `verify2.py PSL2_7 3` builds the
multiplication table of $PSL(2,7)$ from `data/`, computes normal closures with
the code of `survey/nielsen_census.py`, checks the vertex predicate on 2000
random tuple codes (0 mismatches), and runs a full BFS with that code from three
seeded random vertices. For each of them the eccentricity and the complete
vector of level sizes agree with the engine, and each BFS covers all 28223
vertices. Output in `results/verify2-psl27.txt`.

The exact commands are

```
gap -q -b export.g                                  # writes data/ (about 50 s)
python3 acdiam.py --group data/A5 --k 2 --mode normal
python3 acdiam.py --group data/PSL2_11 --k 2 --mode normal --out out_PSL2_11_k2_normal.json
python3 acdiam_comp.py --group data/PSL2_7 --k 2 --mode generate --moveset prg
python3 verify.py census ; python3 verify.py random ; python3 verify.py geodesic
python3 verify2.py PSL2_7 3
python3 analyse2.py ; python3 make_tables.py
```

## 9. Conjectures

The data support two statements that I could not prove.

**C1.** For every finite group $G$ and every $k\ge 2$, the diameter of
$\Delta_k(G)$ is attained at a $k$-tuple with a trivial entry. The evidence is the
table of section 4.1, where the maximal eccentricity over tuples without a
trivial entry is strictly smaller than the diameter for five of the eight groups
and equal to it for the other three, and the lemma of section 5, which shows that
the cone of a degenerate tuple is thin. A proof would need a lower bound that
survives every choice of the non-degenerate representative, and I do not have
one.

**C2.** The diameter of $\Delta_2(G)$ is bounded by an absolute constant, and in
particular does not grow with $|G|$ for perfect $G$. The evidence is the
eight values 8, 8, 8, 8, 8, 9, 8, 8 at orders 60, 120, 168, 336, 360, 504, 660
and 720, together with the mechanism of section 5. Against this conjecture, the
published bounds grow with the order: Borovik, Khukhro and Myasnikov
(arXiv:math/0110246, Section 5) prove that $\Delta_k(G)$ is connected for finite
simple $G$ and $k>2$ with $\operatorname{diam} \Delta_k(G,G) < c\,k\log|G|$, and
modulo the Ore-Thompson conjecture $\operatorname{diam}\Delta_k(G,G)\le
8k+4\operatorname{cn}(G)$. For $A_5$ at $k=3$ with $\operatorname{cn}(A_5)=3$ that
gives 36 against the exact value 9, so the bound is off by a factor of 4 on the
smallest case. I quote their theorems as reported: I read them in the retrieved
text of the preprint and verified the preprint identifier live, without
reconstructing their proofs.

## 10. Limits, and what was not verified

* Exact diameters were computed for eight perfect groups of order at most 720 at
  $k=2$, and for $A_5$ at $k=3$. Not computed: $3.A_6$ (order 1080),
  $PSL(2,13)$ (1092), $PSL(2,11)$ at $k=3$, $PSL(2,17)$ (2448), $A_7$ (2520) and
  $A_5\times A_5$ (3600). The cost model of section 3 puts one orbit BFS for
  $A_7$ at about $6.3\cdot10^6\cdot 2\cdot 2520\approx 1.6\cdot10^{10}$ elementary
  steps, and those groups have hundreds or thousands of orbits, so their exact
  diameters are outside this run. The data for $A_7$, $PSL(2,17)$,
  $PSL(2,13)$, $3.A_6$ and $A_5\times A_5$ are exported by `export.g` and are not
  used.
* No bound is proved for any group. Every diameter in this file is an exact
  finite computation, and the conjectures of section 9 are labelled as
  conjectures.
* The product replacement component counts depend on the exact transvection
  convention. I report three conventions (right transvection only, with
  inversions, with left multiplication) and state the moves in the table.
* $k=1$ is not treated. For $k=1$ the only moves are inversion and conjugation,
  so the graph has one component per conjugacy class of normal generators and its
  diameter is at most 2.
* I did not find a published table of exact diameters to compare with. The
  published statements I found are the bounds quoted in section 9.

## 11. Files

* `README.md`, this file.
* `export.g`, GAP script that writes `data/<group>/` from the group definitions
  in the script. Deterministic; about 50 s for all thirteen groups.
* `data/` contains the eight groups used here, as multiplication tables plus
  maximal normal subgroups, maximal subgroups and generators of the
  automorphism group. The five larger groups are regenerated by `export.g`.
* `acdiam.py`, the engine: exact BFS, orbit reduction, distance distribution.
* `acdiam_comp.py`, the component-resolved driver for move sets whose graph may
  be disconnected.
* `analyse2.py`, consistency checks over all runs and the condensed table.
* `verify.py` and `verify2.py`, the independent checks of section 8.
* `make_tables.py`, builds the markdown tables of section 4 from the JSON runs.
* `cmp_census.py`, the cross-check of the component sizes of section 6 against the
  move enumerator of `survey/nielsen_census.py`.
* `perf_count.g`, the GAP count of perfect groups of order at most 720 (8).
* `geodesics.py`, explicit shortest paths for the diameter-realising pairs.
* `results/` holds one JSON file per run (vertex count, orbit count, level
  decomposition per orbit, distance distribution), the markdown tables, and the
  outputs of the checks.
