# The four PSL(2,7)-frontier groups are infinite

Direction G8 of round 4, member m10, swarm smw2woueq. Files are in this
directory, and the commands in section 8 reproduce every number below.

## 1. The answer

All four presentations of question Q22 present **infinite** groups. They are
the four length-14 rows of `directions/c14/final_classes.txt` labelled
`nontrivial-quotient-PSL27`:

| line in final_classes.txt | presentation | total length | abelian invariants of the group | verdict |
|---|---|---|---|---|
| 48397 | `BAABa,BBBBBBAbA` | 14 | none (perfect) | infinite |
| 48871 | `BABaa,BBBBBBaba` | 14 | none (perfect) | infinite |
| 50366 | `BBAbA,BAAAAAABa` | 14 | none (perfect) | infinite |
| 52990 | `BBaba,BABaaaaaa` | 14 | none (perfect) | infinite |

The convention is the one of `directions/c14/c14lib.py`: `a` and `b` are the
generators, an upper case letter is the inverse of the lower case one. Each of
the four has a unimodular exponent-sum matrix and a surjective homomorphism
onto PSL(2,7) = GL(3,2). I recount 337 pairs of images in GL(3,2) that satisfy
both relators, of which 336 have both images nontrivial and all 336 are
surjective, which reproduces the round-3 figure.

The answer to the question asked in Q22 is therefore that the length-14 census
does meet its first infinite groups. Of the 38 nontrivial length-14 rows, 34
present a group of order 120 and these 4 present infinite groups, so every one
of the 38 now has a decided group.

## 2. Why this is a proof

Let $G$ be one of the four groups. Write $a, b$ for its generators.

Step 1. A pair of permutations $P_X, P_Y$ of 28 points that satisfies both
relators defines a homomorphism $G \to \mathrm{Sym}(28)$. The action is
transitive, so the stabiliser $S$ of the first point has index 28 in $G$. Both
properties are direct checks on the data. The image is a finite group of order
9828 in each of the four cases, so the action is not faithful; the subgroup
$S$ is the full preimage of the point stabiliser of that finite image, and the
point stabiliser itself has order 351 and abelianisation $\mathbb{Z}/13$. The
free part of $S^{ab}$ maps onto that $\mathbb{Z}/13$, which is one consistency
check on the computation.

Step 2. The Reidemeister-Schreier theorem presents $S$ on the 29 nontrivial
Schreier generators $\gamma(c,g) = t_c\, g\, t_{c\cdot g}^{-1}$, where $t_c$ is
a prefix-closed transversal word for the coset $c$, subject to the 56 relators
obtained by rewriting $t_c r_i t_c^{-1}$ for each of the 28 cosets and each of
the two relators. The abelianisation is the cokernel of the $56 \times 29$
integer matrix $M$ of exponent sums.

Step 3. Over the four groups, $M$ has rank 27 and Smith normal form with
invariant factors $1$ (27 times), $2$, and two zeros. Hence
$S^{ab} \cong \mathbb{Z}^2 \oplus \mathbb{Z}/2$. A finite group has finite
abelianisation, so $S$ is infinite.

Step 4. A subgroup of finite index in a finite group is finite. Since $S$ is
infinite, $G$ is infinite.

No other ingredient is used. In particular the proof does not need the action
to be faithful, it does not need the word problem of $G$, and it does not
depend on any search bound.

## 3. The certificate in full

For each group the certificate is a pair of permutations of 28 points plus one
integer vector. The permutations are in `code/verify.py` and are printed by
`code/search.g`; here is the first group.

```
PX1 = [1,3,5,7,2,9,11,13,15,17,4,19,21,16,6,18,23,14,22,25,8,12,10,26,27,28,20,24]
PY1 = [2,4,6,8,1,10,12,14,16,18,3,20,22,15,5,17,24,13,21,26,7,11,9,25,28,27,19,23]
```

The vector `w` for the first group has four nonzero entries out of 29, so the
map $S \to \mathbb{Z}$ can be checked by hand once the 56 relators are written
down:

```
babbabaBBBABB  -> -1
babbabbABBABB  -> -1
bbabbabaBABBAB  -> +1
bbabbabbAABBAB  -> +1
```

The other three groups need four, six and four nonzero entries; `verify.py`
prints them, and in every case it checks that `M w = 0` exactly and that `w` is
nonzero. The existence of such a `w` is what makes $S^{ab}$ infinite.

The 28-point image itself is tiny compared with the group: it has order 9828,
and its point stabiliser has order 351 (`code/permimage.g`). What is infinite
is the preimage in $G$ of that finite stabiliser, not the stabiliser itself.

The smallest index at which a subgroup with infinite abelianisation occurs is
28 for each of the four groups. `code/search.g` enumerates all classes of
subgroups of index at most 40 and finds exactly one such class in each group,
at index 28, with invariants `[0,0,2]`. I also computed the full multiset of
(index, abelian invariants) pairs over the 260 classes, and it is the same
multiset for all four groups: 260 classes, with 42 of index 28, and none of
index below 28 with infinite abelianisation.

## 4. What was checked, and how

1. **Transcription.** The four presentation strings were read with the
   repository's own parser `c14lib.parse_pres`, and separately by a literal
   reading in GAP (upper case letter set equal to the inverse of the lower case
   letter). The two readings give identical words in the free group, and each
   pair has total length 5 + 9 = 14 (`work/transcribe.g`).
2. **Independent Python implementation** (`code/verify.py`, which does not use
   GAP): it checks that the permutations satisfy both relators, that the action
   is transitive, builds the transversal and the Reidemeister-Schreier matrix,
   computes the rank and the nullspace over $\mathbb{Q}$ and the Smith normal
   form over $\mathbb{Z}$ with sympy, and prints an explicit integer null
   vector. It reports rank 27 and invariants `[0,0,2]` for all four groups.
3. **GAP verification with its own code** (`code/check_gap.g`): GAP builds its
   own breadth-first transversal and its own Schreier generators, verifies that
   each one fixes the point, forms the subgroup and asks GAP for its index and
   its abelian invariants. It reports index 28 and `[0,0,2]` for all four.
4. **Second GAP route** (`work/crosscheck.g`, whose driver is `work/rs_export.py`):
   the 29 generators and 56 relators produced by the Python code were
   exported as a GAP presentation, and GAP computed its abelian invariants
   directly. It agrees: `[0,0,2]`, and the subgroup generated by the same 29
   words has index 28 in $G$.
5. **The telescoping identity.** `work/check_rows.py` checks it. The rewriting is the one place where a sign
   slip is easy. For each of the 224 rows I checked in the free group that the
   product of the Schreier factors is literally the freely reduced word
   $t_c r_i t_c^{-1}$. The first version of my code failed this check for all
   224 rows, and the failure was a real error: for a negative letter the
   Schreier generator sits at the coset *reached*, not at the coset left.
   After the fix all 224 rows pass.
6. **Controls on known groups.** The same pipeline gives the right answers on
   cases whose order GAP decides by Todd-Coxeter: the alternating group $A_5$
   with a degree-5 action (stabiliser of index 5 with abelianisation
   $\mathbb{Z}/3$, which is $A_4$), the trefoil group $\langle a,b \mid
   a^2 b^{-3}\rangle$ acting on the three cosets of the preimage of a point
   stabiliser of its $S_3$ quotient (stabiliser of index 3 with abelianisation
   $\mathbb{Z}^2$, and GAP gives the same), and the four length-12 siblings of
   the frontier rows. The siblings `BAABa,BBBBAbA`, `BABaa,BBBBaba`,
   `BBAbA,BAAAABa` and `BBaba,BABaaaa` each present a group of order 120, and
   none of them has
   a subgroup of index at most 28 with infinite abelianisation. The frontier
   rows are the same presentations with two more letters in the second
   relator, and the extra letters are what turns a group of order 120 into an
   infinite group. The order 120 for the other thirty rows labelled
   `nontrivial-quotient-A5` is the refereed round-2/round-3 record and I did
   not rerun their Todd-Coxeter enumerations.
7. **A fifth construction of the same subgroup.** `work/preimage.g` builds
   $S$ directly as the full preimage of the point stabiliser under the action
   homomorphism (GAP's `PreImage`), without any Schreier word. It gets index 28
   and abelian invariants `[0,0,2]` in all four cases, matching the four
   earlier computations.
8. **Independence of the choices.** The Reidemeister-Schreier presentation of
   $S$ depends on the transversal, so `code/robustness.py` recomputes
   everything with a depth-first transversal and with ten fixed relabellings
   of the 28 points. All twelve runs of each group give 29 generators, rank
   27 and invariants `[0,0,2]`.
9. **The PSL(2,7) count.** `code/quotients.g` recomputes 337 pairs of images
   in GL(3,2) for each row, with 336 of them nontrivial and all 336
   surjective. This reproduces the round-3 record.

## 5. Consequences

The direct consequence is that question Q22 is answered: the four frontier
presentations present infinite groups, and the length-14 census has met its
first infinite groups. The round-2 sentence that all 38 nontrivial
presentations present a group of order 120, already corrected in round 3, is
now replaced by a definite classification of those 38 rows: 34 finite of order
120 by the round-3 record, and 4 infinite by the computation here.

A second consequence concerns the AC-classes. Each of the four strikes out as
a class different from the trivial class and from the AK(3) class, since both
of those present the trivial group. That does not change the count of
undecided AC-classes among the 164 resisters, and I make no claim about
whether the four are AC-equivalent to one another. The computation does show
that no Todd-Coxeter run will ever close on them, and that a finite quotient
of order 9828 already exists, so a large finite quotient on its own says
nothing about finiteness. The round-3 record that "GAP's enumeration exceeded
4,096,000 cosets" is now explained: the index of the trivial subgroup is
infinite.

## 6. The one-parameter family (bonus)

The four rows suggest a family, $\langle a,b \mid BAABa,\ B^{2m}AbA\rangle$,
where $m = 2$ gives length 12 and $m = 3$ gives the third frontier row
`BBAbA,BAAAAAABa`. The same analysis gives:

| m | total length | abelian invariants | order or smallest index with infinite abelianisation |
|---|---|---|---|
| 1 | 10 | $\mathbb{Z}/3$ | order 24 |
| 2 | 12 | none | order 120 |
| 3 | 14 | none | infinite, index 28, invariants `[0,0,2]` |
| 4 | 16 | $\mathbb{Z}/3$ | infinite, index 9, invariants `[0,0,2,3,7]` |
| 5 | 18 | $\mathbb{Z}/5$ | infinite, index 12, invariants `[0,0,4,5]` |

So two extra letters in a relator change a group of order 120 into an infinite
group, and the same family stays infinite for the next two values of $m$. The
index-9 certificate for $m = 4$ is smaller than the index-28 one for $m = 3$.

## 7. Limits

I did not determine the isomorphism types of the four groups. They have
identical subgroup statistics up to index 40, which is evidence that they may
be pairwise isomorphic or even AC-equivalent, but no certificate for either
statement is given here and neither is claimed.

I did not run a Knuth-Bendix completion. The GAP package kbmag is not installed
on this VM, and the proof above makes it unnecessary for the question asked.

I tried a fourth implementation through sympy's finitely presented groups and
abandoned it. `sympy.combinatorics.fp_groups.FpGroup(F, [r1, r2]).abelian_invariants()`
had not returned after 200 s on the first presentation, which has two
generators and two relators, so the attempt is recorded in
`work/attempt_sympy.py` and nothing rests on it.

I did not explore the family beyond $m = 5$, and the family rows at lengths 16
and 18 are outside the length-14 census, so they carry no weight for the
census. Their infiniteness is proved by the same finite-index argument.

## 8. Exact commands and output

```
cd <this directory>
sh run_all.sh
```

The script runs nine jobs and takes about a minute. The recorded
output is `transcript.txt`. The load-bearing lines are:

```
presentation 1: BAABa,BBBBBBAbA   total relator length 14
  relator BAABa is satisfied: True
  relator BBBBBBAbA is satisfied: True
  point stabiliser S: index 28; Schreier generators 29; RS relations 56
  rank of M over Q: 27;  invariant factors of S^ab: [0, 0, 2]
  CONCLUSION: S is infinite, hence presentation 1 presents an infinite group
...
ALL FOUR GROUPS ARE INFINITE: True
```

and, from `code/check_gap.g`,

```
  index of the point stabiliser in G: 28
  GAP's abelian invariants of the stabiliser: [ 0, 0, 2 ]
  ==> the stabiliser is infinite, hence G1 is infinite
```

and from `code/search.g`, for each group,

```
  abelian invariants of G: [  ]
  classes of subgroups of index <= 40: 260
  classes with infinite abelianisation: [ [ 28, [ 0, 0, 2 ] ] ]
the four subgroup patterns up to index 40 are identical: true
```

The individual scripts are `code/verify.py` (no dependencies beyond python3
and sympy), `code/selftest.py` (the same routine on two cases with a known
answer), `code/check_gap.g`, `code/search.g`, `code/quotients.g`,
`code/permimage.g` (the order of the 28-point image and of its point
stabiliser), `code/control.g` and `code/family.g`. The construction stage is
in `work/`.
