# Round 5, direction H7: AK(3)'s Q**-status

Member m6, swarm smw38010i, 2026-11-05 UTC. This file extends
`directions/qdouble-star/`, and everything new is in
`directions/qdouble-star/m6/`, so no round-3 or round-4 file is changed. My
working directory was `.ultramath/smw38010i/m6/qb/`, and the two copies of the
code and of this report are byte-identical.

This is the second version. The first was rejected for two mathematical gaps,
both of which are closed here. Section 4 now states the conjugation bound
correctly, with a proof and a machine check; the first version bounded the
intermediates by the final presentation, which is false. Sections 2, 6 and 10
now scope every peak-bounded statement to the move set that was actually
enumerated, because move (iv) of Barmak's list is an arbitrary automorphism
while the census used the elementary Nielsen transformations. All the numbers
and all the code are unchanged.

Labels. **[checked]** is a statement checked by the exact command quoted.
**[computed here]** is a deterministic computation, rerun by the command quoted.
**[proved here]** is an argument written out here. **[bounded negative]** is a
box result with its exact bound. Nothing here proves or disproves the
Andrews-Curtis conjecture, and nothing here decides whether AK(3) is
Q**-trivial.

## 1. What is new, in one page

1. **A reduction of Q**-triviality to a one-letter target.** For a rank-2
   presentation P of the trivial group, P is Q**-trivial if and only if P is
   Q**-equivalent to a rank-2 presentation with a relator of length 1. One
   direction is constructive: from such a state, three or five Q-moves per
   letter occurrence, one deletion and the rank-1 finish write an explicit Q**
   move list to the empty presentation. `peel.py` builds those lists and
   replays them from the text, and the rank-2 phase of its certificate also
   replays under the round-2 checker
   `directions/pu-enumeration/replay_certs.py`. **[proved here, checked]**
2. **A conjugation by a long word costs nothing in a box census.** Lemma 2
   says that if a relator r is conjugated by a word w, every intermediate
   presentation of the letter-by-letter decomposition has total length at most
   the larger of the total lengths of the two endpoints. So a box whose
   endpoints are in B(T) contains the whole decomposed path, and closing a box
   under conjugations of length 1 closes it under conjugations of every length.
   The bound is not by the final presentation alone: the referee's example
   r = y^-1 x^-1 y x y with w = x y runs through relator lengths 5, 3, 1 and
   the middle one exceeds the last. The correct bound is the maximum of the two
   ends, it is proved in Section 4, and it is machine-checked on 42,250,782
   suffix instances with no violation. **[proved here, checked]**
3. **The first Q*-level census of the AK(3) class.** Adding the elementary
   Nielsen transformations to the three Andrews-Curtis moves and closing inside
   the same total-length box, the class of AK(3) has 672, 672, 241,216,
   602,176, 3,642,208, 7,513,440, 34,000,352 and 66,996,960 presentations, in
   4, 4, 1,048, 2,272, 9,576, 17,472, 60,976 and 109,072 conjugation and
   inversion classes, at total-length caps 13 to 20. The same engine reproduces
   the round-2 census exactly at all eight caps, in states and in classes, so
   the new column sits on a validated base. Every counted state carries an
   explicit path from AK(3), and 50,000 of those paths at cap 20 replay under an
   independent replayer. **[computed here, checked]**
4. **The relator-length barrier survives.** No presentation in that component
   with total length at most 20 has a relator shorter than 5, and relators of
   length 5 do occur, first at cap 15. In particular the component contains no
   presentation with a relator of length 1 and none that is the standard tuple.
   By item 1 and by the two-deletion finish, AK(3) has no trivialisation to the
   standard tuple whose intermediates all have rank 2 and total length at most
   20, whose relator moves are (i) to (iii) with conjugators of any length
   (Lemma 2) and whose generator move (iv) is one of the elementary Nielsen
   transformations. This is an exhaustion, not a budget. Item 6 records how much
   larger the tested generator move set is than the elementary one.
   **[computed here, bounded negative]**
5. **Nielsen moves shorten nothing, and what they add is above total length
   14.** The minimum total relator length in the box is 13 for the Andrews-
   Curtis class and for the Q*-class alike, and the 4,032 presentations at that
   length fall into 24 conjugation and inversion classes in both. The two
   relations part company at total length 15: the Q*-class has 21,120 more
   presentations there, and 15,585,504 more inside the cap-20 box, in 29,392
   more classes. What Nielsen moves buy is the peak: a relator of length 5 is
   reached at cap 15 instead of cap 19. **[computed here]**
6. **The census is invariant under a much larger generator move set.** At cap
   20 the component is exactly 66,996,960 presentations whether move (iv) is the
   ten elementary Nielsen transformations or all 72 automorphisms of F_2 whose
   two images have length at most 2, applied directly as single moves. At caps
   15 and 16 the same holds for all 744 automorphisms whose images have length
   at most 3. The conjugator bound likewise does not matter: K = 1 and K = 2
   give identical vertex sets, and round 2 recorded K = 1, 2, 3 identical at
   caps 18, 19 and 20. **[computed here, checked]**
7. **The rank-3 Q** box is complete at total length 14 and hits a wall at 15.**
   With prolongation and deletion added, the box at total length 14 is complete
   at 4,704 presentations, 672 of rank 2 and 4,032 of rank 3, with no target
   hit. At total length 15 the component passed 93,952,409 presentations with
   no target hit and stopped at the load limit of my hash table, 554 s and
   4.10 GB. **[computed here, bounded negative]**
8. **The one-letter pattern is the mechanism of the known Q**-certificates.**
   All 33 certificates of `directions/qdouble-star/m9/certs/` replay under a
   fourth independent implementation written here, zero failures, and each of
   them adjoins a spare generator, drives a relator to a conjugate of a
   generator, and deletes that generator. **[checked]**

The straight answer to the round-5 question is this. AK(3)'s Q**-status is open
and it stays open here. What is settled is that the census with the three
relator moves, conjugators of every length and the elementary Nielsen
transformations, which is the same component as with all 72 small automorphisms
at cap 20, contains no trivialisation below peak length 20, and that the
obstruction is the length of the shortest relator, which the Nielsen moves lower
from 6 to 5 and no further. An automorphism with longer images, used as a single
move of Barmak's full list (iv), is not excluded by any computation here.

## 2. Conventions

AK(3) is the pair `(x y x y^-1 x^-1 y^-1, x^3 y^-4)` of total length 13, the
same tuple as `directions/pu-enumeration/pu.md` Section 2. Words are freely
reduced and written as tuples of signed generator indices, 1 = x, -1 = x^-1,
2 = y, -2 = y^-1, 3 = z, -3 = z^-1. A presentation is a rank r together with r
relators, and its total length is the sum of the relator lengths.

The six Q** moves are Barmak's list (Algebr. Geom. Topol. 25 (2025) 345-355,
Section 1, quoted in `survey/q-transformations.md` Section 2): (i) replace a
relator by its product with another relator, (ii) invert a relator,
(iii) conjugate a relator by any word, (iv) apply an automorphism of the free
group, (v) adjoin a generator with that generator as its relator, (vi) the
inverse of (v). Moves (i) to (iv) are Q*.

Move (iv) has two readings. Barmak's is an arbitrary automorphism, applied in
one step. The reading of Hog-Angeloni and Metzler (quoted in
`survey/q-transformations.md` Section 2) is the elementary Nielsen
transformations, which generate all automorphisms as a group. The two readings
generate the same relation, so Lemma 1 below, which is a statement about
Q**-equivalence, does not depend on the choice. They can differ for a bounded
path, because the elementary decomposition of one large automorphism can pass
through presentations longer than both ends. Every peak-bounded statement in
this report is therefore written for the explicit move set

  M = (i) mul, (ii) inv, (iii) conj by any word, (iv') elementary Nielsen.

A box B(T) is the set of presentations of rank 2 reached from AK(3) by paths
whose every presentation has total length at most T using M. Its rank-2 part is
closed under M by construction, so a statement that no presentation in B(T) has
a property is an exhaustive statement about paths confined to B(T). Section 6
also reports the computation with the larger move set M', in which (iv') is
replaced by every automorphism whose two images have length at most 2, applied
directly, and Section 5 records the bound K on conjugators.

## 3. The one-letter lemma

**Lemma 1.** Let P be a rank-2 presentation of the trivial group. Then P is
Q**-trivial if and only if P is Q**-equivalent to a rank-2 presentation with a
relator of length 1. Moreover, in every Q**-trivialisation of any presentation,
the first deletion is preceded by a presentation with a relator of length 1.
**[proved here]**

Proof of the converse direction, from a relator of length 1. Let
Q = (x, y; r1, r2) be the rank-2 presentation with a relator of length 1, say
r1 = y after inverting it if necessary. Let r2 = u y^-1 v have a displayed
occurrence of the inverse letter. Then

    conj r1 by v^-1:   r1 becomes v^-1 y v
    mul r2 by r1:      r2 becomes u y^-1 v v^-1 y v, which reduces to u v
    conj r1 by v:      r1 becomes y again

These are three moves and they delete one letter of r2. For an occurrence of
y^+1 the same works with r1 inverted first and inverted back at the end, which
is five moves. Each round deletes one occurrence, so the loop terminates with
r2 a word in x alone and r1 still y. Now y occurs in exactly one relator and
that relator is y, so move (vi) deletes the pair. What is left is (x; w) with w
a word in x. It presents the trivial group because Q does, so w is x or x^-1.
Invert the relator if needed and apply (vi) again, and the empty presentation is
reached. **[proved here]**

Proof of the direct direction, and of the second sentence. Read a
Q**-trivialisation of P to the empty presentation and take its first deletion.
Before that deletion there is a generator g whose relator is g or g^-1 and which
occurs in no other relator, which is a relator of length 1, and every move
before that point is a Q* move or a prolongation. **[proved here]**

Two remarks fix the scope. The converse direction needs the letter state at
rank 2, because the recipe spends the balance: it deletes one generator and one
relator and then finishes at rank 1. At rank 3 the same recipe leaves a rank-2
balanced presentation of the trivial group, which is the original problem, so
nothing is gained. The direct direction is what a negative uses. A
trivialisation of a rank-2 presentation must delete a generator at rank 2 at
some point, since the rank starts at 2, decreases only by deletion, and has to
reach 0, and just before that deletion the presentation has a relator of length
1. Hence a box that is closed under the moves and contains no rank-2 state with
a relator of length 1 contains no Q**-trivialisation whose intermediates all
stay in the box. **[proved here]**

`peel.py` implements the recipe, and its `selftest` mode serialises each
certificate to text and replays it from the text with a separate function that
checks every move for legality. **[checked]**

    $ python3 peel.py selftest
    PASS y, x  (the standard pair, relators swapped)   2 moves  reachable: empty presentation
    PASS y, x y x^-1 y^-1 x                          10 moves  reachable: empty presentation
    PASS y^-1, x y x y^-1 x^-1                       11 moves  reachable: empty presentation
    PASS x, y^2 x y^-1 x^-1                          10 moves  reachable: empty presentation
    PASS y, x^2 y x^-1 y^-1                          10 moves  reachable: empty presentation
    PASS peel raised for y, x^2 y^-1 x (group of order 3) : group is not trivial: the rank-1 relator is xxx
    peel selftest failures: 0

The last line is a negative control: `(y, x^2 y^-1 x)` presents the group of
order 3, its rank-1 relator is x^3, and the builder refuses to claim a
trivialisation. The rank-2 phase of a certificate is also written in the format
of `directions/pu-enumeration/replay_certs.py`, which another member wrote and
round 2 refereed, so that phase is checked by code I did not write.
**[checked]**

    $ python3 peel.py cert "2" "1 2 1 -2 -1"
    start rank 2; y | xyxy^-1x^-1  moves 10  end rank 0 relators []
    $ python3 directions/pu-enumeration/replay_certs.py peel_rank2.cert
    certificates checked: 1, verified: 1, failed: 0

## 4. Conjugations by long words

The first version of this section claimed that every intermediate of a
letter-by-letter conjugation is no longer than the final presentation. That is
false, and the referee gave the counterexample r = y^-1 x^-1 y x y with
w = x y: the decomposition conjugates by y first and by x second, and the
relator lengths along the way are 5, 3 and 1, so the middle one exceeds the
last. The correct bound is by the larger of the two ends.

**Lemma 2.** Let r be a freely reduced word, w a freely reduced word and u a
suffix of w, possibly empty. Then

    |fred(u r u^-1)| <= max( |r| , |fred(w r w^-1)| ).

Consequently, if two presentations P and Q differ by a conjugation of one
relator by w, and both have total length at most T, then the presentation
between them produced by any single-letter step of the decomposition also has
total length at most T. **[proved here]**

Proof. For a reduced word z define three numbers, all zero when no t satisfies
the condition, and all of them at most min(|z|, |r|).

    A(z) = max t with suffix_t(z) = inverse(prefix_t(r))
    C(z) = max t with suffix_t(z) = suffix_t(r)
    B(z) = min( C(z), |r| - A(z) )

The sets over which A and C take their maxima are initial segments of t, since
dropping the first letter of both sides of an equality of suffixes preserves it.
Hence for u a suffix of w

    A(u) = min(A(w), |u|)  and  C(u) = min(C(w), |u|),                      (1)

because the valid t for u are exactly the valid t for w that are at most |u|.

Now reduce the word z r z^-1 in two steps. At the junction between z and r, the
last A(z) letters of z cancel against the first A(z) letters of r and no more.
At the junction between the remaining r and z^-1, the last B(z) letters of r
cancel against the first B(z) letters of z^-1 and no more: the first t letters
of z^-1 are the inverses of the last t letters of z, so this cancellation is by
the largest t with suffix_t(r) = suffix_t(z), which is C(z), truncated by the
length |r| - A(z) of what is left of r. What remains is

    z[0:|z|-A(z)] . r[A(z):|r|-B(z)] . inverse(z[0:|z|-B(z)]),

whose length is |r| + 2|z| - 2A(z) - 2B(z), and it is freely reduced because
both junctions are maximal. The one exception is A(z) + B(z) = |r|, where the
middle factor is empty and the two remaining factors can cancel further; there
the same count is an upper bound. So in all cases

    |fred(z r z^-1)| <= |r| + 2|z| - 2A(z) - 2B(z),                          (2)

with equality whenever A(z) + B(z) < |r|.

The claim is proved by induction on |u|. The case |u| = 0 has |fred(u r u^-1)|
= |r|. For the step, put n = |u| and A = A(w), C = C(w), B = B(w).

Case n < A. Then A(u) = n by (1), so the first junction consumes all of u and
(2) gives |fred(u r u^-1)| <= |r| - 2B(u) <= |r|, which is the claim.

Case n >= A and n >= C. Then A(u) = A and B(u) = B. If A + B < |r| then (2) is
an equality at both ends and

    |fred(u r u^-1)| = |r| + 2n - 2A - 2B <= |r| + 2|w| - 2A - 2B = |fred(w r w^-1)|.

If A + B = |r| then the middle factor of the reduction of u r u^-1 is empty, and
the remaining word is u[0:n-A] . inverse(u[0:n-B]). Suppose B <= A. Then
u[0:n-B] = u[0:n-A] . omega with omega = u[n-A:n-B], so the remaining word is
zeta . omega^-1 . zeta^-1 with zeta = u[0:n-A], a conjugate of omega^-1.
Suppose A <= B. Then u[0:n-A] = u[0:n-B] . omega with omega = u[n-B:n-A], and
the remaining word is zeta . omega . zeta^-1 with zeta = u[0:n-B]. In both
sub-cases the same computation for w gives the same omega, because w = p u and
the prefixes of w are the prefixes of u with p in front, and it gives the
conjugate by p zeta. The number |zeta| is n - max(A,B) < n, since A + B = |r|
>= 1 forces max(A,B) >= 1. So the induction hypothesis applies with relator
omega (or omega^-1) and the pair of conjugating words zeta and p zeta, and it
gives

    |fred(u r u^-1)| <= max(|omega|, |fred(w r w^-1)|) <= max(|r|, |fred(w r w^-1)|)

because |omega| = |A - B| <= |r|.

Case n >= A and n < C. Then A(u) = A and B(u) = min(n, |r| - A). If
n <= |r| - A then A(u) + B(u) < |r| unless n = |r| - A exactly, and (2) gives

    |fred(u r u^-1)| <= |r| + 2n - 2A - 2n = |r| - 2A <= |r|.

If n > |r| - A then B(u) = |r| - A and A(u) + B(u) = |r|, which is the empty
middle case again, with |zeta| = n - max(A, |r|-A) < n; the same reduction and
the induction hypothesis finish it.

That is every case, so the lemma holds. QED

Two consequences. First, the length of an intermediate is bounded by
max(|r|, |fred(w r w^-1)|), never by the final presentation alone, and the bound
is attained: the referee's example has 5, 3, 1 with max(|r|, 1) = 5. Second, if
the other relator of the presentation is unchanged, then every intermediate
presentation has total length at most the larger of the total lengths of the two
endpoints. So a box that contains both endpoints contains the whole decomposed
path, and closing under conjugations of length at most 1 closes it under
conjugations of every length. **[proved here]**

**Machine check.** `conj_bound.py` checks the statement and the formula (2) on
every suffix of every pair (r, w), exhaustively over two letters with |r| at
most 6 and |w| at most 5, exhaustively over three letters with both lengths at
most 4, at random with |r| up to 30 and |w| up to 20, and on adversarial pairs
built by gluing a terminal segment of inverse(r) to a terminal segment of r.
It also counts the failures of the false first-version statement, so the size of
the correction is on the record, and it checks the step of the proof that
matters, the reduction of the case where the two junctions consume all of r:
there the length of the intermediate must equal that of a conjugate of the
surviving middle segment omega by the shorter prefix zeta, and that identity
holds in all 1,598,693 consumed instances the check meets, with zeta the same
word for u and for w up to the prefix p on the left. **[checked]**

    $ python3 conj_bound.py
    exhaustive two letters |r|<=6 |w|<=5: suffixes tested 29800677, bound violations 0, formula violations 0, naive-statement failures 105984, consumed-case reductions 1287888, reduction failures 0
    exhaustive three letters |r|<=4 |w|<=4: suffixes tested 9480835, bound violations 0, formula violations 0, naive-statement failures 7200, consumed-case reductions 224616, reduction failures 0
    random, 200000 pairs, |r|<=30 |w|<=20: suffixes tested 1514610, bound violations 0, formula violations 0, naive-statement failures 1369, consumed-case reductions 43543, reduction failures 0
    adversarial, 200000 pairs: suffixes tested 1454660, bound violations 0, formula violations 0, naive-statement failures 14055, consumed-case reductions 42646, reduction failures 0
      referee example: r = y^-1x^-1yxy, w = xy, u = () -> |u r u^-1| = 5 (final 1, |r| 5)
      referee example: r = y^-1x^-1yxy, w = xy, u = (2,) -> |u r u^-1| = 3 (final 1, |r| 5)
      referee example: r = y^-1x^-1yxy, w = xy, u = (1, 2) -> |u r u^-1| = 1 (final 1, |r| 5)
    TOTAL: bound violations 0, formula violations 0, naive-statement failures 128608, consumed-case reductions 1598693, reduction failures 0

## 5. The census

`qbox.c` is my enumerator of the component of AK(3) in a box under a chosen move
set. I wrote it after reading the round-2 enumerator, and it shares its
architecture, an arena of records and an open-addressed hash of the record.
What makes the agreement between the two programmes meaningful is that the
counts coincide at every cap where the round-2 census is complete, in states
and in classes. **[checked]**

    $ gcc -O2 -o qbox qbox.c
    $ ./qbox 20 --classes 1 --nopar 1 --htbits 27 --arena 2048
    states 51411456 edges 309945088 time 65.46
    classes 79680 (conjugation and inversion of each relator, ordered)
    rank2_by_total 13:4032 14:15424 15:241856 16:336288 17:2520832 18:3280096 19:20185152 20:24827776
    classes_by_total 13:24 14:80 15:1032 16:1112 17:5688 18:6456 19:31240 20:34048
    targets rank2_letter 0 rank2_standard 0 rank3_letter 0 min_relator_len_rank2 5

| T  | Q states  | Q classes | Q* states  | Q* classes | round-2 states | round-2 classes |
|----|----------:|----------:|-----------:|-----------:|---------------:|----------------:|
| 13 |       168 |         1 |        672 |          4 |            168 |               1 |
| 14 |       168 |         1 |        672 |          4 |            168 |               1 |
| 15 |     6,864 |        26 |    241,216 |      1,048 |          6,864 |              26 |
| 16 |    20,560 |        80 |    602,176 |      2,272 |         20,560 |              80 |
| 17 |   857,808 |     2,000 |  3,642,208 |      9,576 |        857,808 |           2,000 |
| 18 | 2,014,992 |     4,256 |  7,513,440 |     17,472 |      2,014,992 |           4,256 |
| 19 |23,609,984 |    40,048 | 34,000,352 |     60,976 |     23,609,984 |          40,048 |
| 20 |51,411,456 |    79,680 | 66,996,960 |    109,072 |     51,411,456 |          79,680 |

The Q columns are mine with `--conj 1` and no Nielsen moves; the Q* columns add
the elementary Nielsen transformations; the round-2 columns are the record from
`directions/pu-enumeration/census.txt`. The class counts are ordered pairs of
least cyclic forms over each relator and its inverse, which is the convention of
`rawbox.c`, so the class columns are comparable. Times and memory at cap 20:
420 s and 2.77 GB peak resident without the class pass, 327 s and 3.42 GB with
it and with the path dump. **[computed here, checked]**

The per-length split at cap 20 shows where Q* is larger than Q. **[computed
here]**

| total length | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Q states | 4,032 | 15,424 | 241,856 | 336,288 | 2,520,832 | 3,280,096 | 20,185,152 | 24,827,776 |
| Q* states | 4,032 | 15,424 | 262,976 | 378,624 | 3,082,496 | 4,041,856 | 26,735,168 | 32,476,384 |
| Q classes | 24 | 80 | 1,032 | 1,112 | 5,688 | 6,456 | 31,240 | 34,048 |
| Q* classes | 24 | 80 | 1,128 | 1,280 | 7,424 | 8,352 | 44,152 | 46,632 |

So Nielsen moves add nothing at total length 13 or 14, and everything they add
lies at 15 and above.

Robustness runs. **[checked]**

* Conjugator bound: K = 1 and K = 2 give identical vertex sets at cap 15 with
  Nielsen moves (241,216 each) and at cap 13 without them (168 each). Round 2
  recorded K = 1, 2, 3 identical at caps 18, 19 and 20
  (`directions/pu-enumeration/census.txt`), and Lemma 2 explains why.
* Generator move set: at caps 15, 16, 17 the component is the same with the
  elementary Nielsen transformations and with all 72 automorphisms of F_2 whose
  images have length at most 2 applied directly (241,216; 602,176; 3,642,208),
  and at caps 15 and 16 also with all 744 automorphisms whose images have length
  at most 3 (241,216; 602,176). At cap 20 the count with all 72 direct
  automorphisms is 66,996,960, identical to the count with elementary Nielsen
  moves, and the relator-length histogram and the target counts agree as well.
  **[computed here]**
* Path certificates: `--paths` writes one explicit move path per state, and
  `qcheck_paths.py` replays them from the text with an implementation written
  from the definitions. 50,000 paths at cap 20, 20,000 at cap 18, and 4,000 at
  cap 14 with rank 3 including prolongations and deletions, all verified with
  zero failures. **[checked]**

      $ python3 qcheck_paths.py paths20.txt
      paths checked: 50000, verified: 50000, failed: 0

* Target-detector unit test: started at the standard tuple (x; y), the same
  program reports `rank2_standard 8` and `rank2_letter 79496`, and started at
  (x; y x), one move from it, it reports the same component of 169,992
  presentations at cap 10. The detector fires, and it fires on a class that has
  a letter.

## 6. Targets: the relator-length barrier

The two things the engine watches are a relator of length 1 at rank 2, which by
Lemma 1 is the premise of the peeling construction, and the standard tuple,
which is the only rank-2 presentation from which two deletions reach the empty
one. Neither occurs anywhere in the component inside the box.
**[computed here]**

| T  | Q* states  | states with a relator of length 5 | length 4 or less | standard tuple |
|----|-----------:|----------------------------------:|-----------------:|---------------:|
| 15 |    241,216 |                            17,280 |                0 |              0 |
| 16 |    602,176 |                            60,000 |                0 |              0 |
| 17 |  3,642,208 |                           215,360 |                0 |              0 |
| 18 |  7,513,440 |                           713,600 |                0 |              0 |
| 19 | 34,000,352 |                         2,357,120 |                0 |              0 |
| 20 | 66,996,960 |                         7,760,480 |                0 |              0 |

The Q component reaches a relator of length 5 later, at cap 19, with 2,314,560
such presentations, and never reaches length 4 at any cap up to 20. So Nielsen
moves pull the length-5 threshold down by four caps and leave the length-4
threshold where it was. The cap-20 run with the 72 direct automorphisms
reproduces the same histogram and the same zero target counts. **[computed
here]**

**Proposition 3.** AK(3) has no trivialisation to the standard tuple whose
intermediates all have rank 2 and total relator length at most 20, whose relator
moves are (i) to (iii) with conjugators of any length, and whose generator move
is an elementary Nielsen transformation. **[proved here from the computation]**

Proof. Suppose such a trivialisation exists. Its relator moves keep the rank at
2 and its generator moves are elementary Nielsen transformations, so by Lemma 2
and the closure of the box the whole path lies in B(20). The path deletes two
generators. Take the first of those deletions. The presentation just before it
has rank 2, one relator is the deleted generator up to sign, and the other
relator is free of that generator and becomes the relator of the rank-1
presentation that the second deletion finishes, so that other relator is the
surviving generator up to sign. The presentation is therefore the standard
tuple up to signs and up to the order of the two relators. Section 5 reports
`rank2_standard 0` at cap 20, so no such path exists. QED

The scope is exact and it is the second of the two corrections. Barmak's move
(iv) permits an arbitrary automorphism in one step. Section 5 checks that
replacing the elementary Nielsen transformations by all 72 automorphisms with
images of length at most 2, or all 744 with images of length at most 3 at caps
15 and 16, does not change the component. That is evidence and not a proof:
an automorphism with long images, used as a single step, could in principle
reach a presentation that the elementary decomposition reaches only through
longer intermediates, and substitution images compound under composition, so the
argument of Lemma 2 does not transfer. What would close it is a bound on the
intermediates of an automorphism decomposition in terms of the two ends, which I
do not have. **[checked for the enumerations, open for the general automorphism
move]**

[Coordinator note, 5 November 2026: the count 72 is right and all 72 pairs are
genuine automorphisms of F_2 (checked by Stallings folding and by GAP). The
count 744 is right for what the engine enumerates - the pairs of reduced words
of length at most 3 with unimodular abelianization - but 288 of those 744 are
NOT automorphisms: they have determinant plus or minus one and still do not
generate F_2 (GAP gives index infinity; for example (x y, x^-2 y^-1)). The
tested set is therefore a strict superset of the 456 genuine automorphisms
with images of length at most 3. The conclusion is unaffected, and holds a
fortiori: the true automorphism set contains the elementary Nielsen
transformations and is contained in the tested 744, so its closure lies between
the elementary closure and the tested closure, and those two are equal (241,216
at cap 15, 602,176 at cap 16). Read "all 744" above as "the 744 unimodular
pairs, a superset of the 456 automorphisms".]

**Proposition 4.** Inside the cap-20 box the minimum total relator length in the
class of AK(3) is 13, both for the Andrews-Curtis class and for the Q*-class,
and the 4,032 presentations at total length 13 fall into 24 conjugation and
inversion classes in both. **[computed here]**

Proof. The per-length row of Section 5 begins at 13 with 4,032 presentations,
and the class row begins at 13 with 24. The same two numbers appear in the cap-20
Q run, so the Nielsen moves add nothing at the minimal lengths. QED

The bound is a statement about the box. A presentation of total length 12 could
exist in principle if every path to it exceeded total length 20.

## 7. The rank-3 Q** box

Prolongation and deletion are what separate Q** from Q*, and both change the
rank. The engine therefore also closes the box under (v) and (vi) with the rank
allowed to reach 3, and reports the rank-2 part separately, because a rank-3
excursion can reach rank-2 presentations that no rank-2 path reaches.
**[computed here]**

| T  | rank-2 presentations | rank-3 presentations | rank-2 target hits |
|----|---------------------:|---------------------:|-------------------:|
| 13 |                  672 |                    0 |                  0 |
| 14 |                  672 |                4,032 |                  0 |
| 15 |  213,151 at the wall, run incomplete | 93,739,258 |        0 |

At total length 15 the component passed 93,952,409 presentations with no target
hit and stopped at the load limit of my hash table, at 554 s and 4.10 GB peak
resident. Every rank-3 presentation at total length 14 sits at total length
exactly 14, and every prolongation creates a relator of length 1, so a letter
test at rank 3 is uninformative; the test that matters is the rank-2 one, which
is the last column. **[checked]**

The honest reading is that the rank-3 census at cap 20, which is what a
Q**-level intersection with the round-2 census would need, is not available
here. The 241,216 rank-2 presentations of the Q* box at total length 15 go with
more than 93 million rank-3 presentations at the same total length, and the
growth from there to cap 20 is out of reach of this VM. What the table does
establish is the exact failure point and that no Q**-trivialisation is hidden at
rank 3 below total length 14.

## 8. The m9 certificates under an independent replayer

`m9check.py` is a fourth implementation of the Q** move set, written from
Barmak's list before I read
`directions/qdouble-star/m9/qverify.py`. It replays the certificate format of
the round-3 engine. **[checked]**

    $ python3 m9check.py directions/qdouble-star/m9/certs/*.cert
    ...
    certificates 33, replayed 33, failed 0

Two points came out of writing it. The deletion in that format is applied when
the generator occurs in exactly one relator and that relator cyclically reduces
to the generator, which is one conjugation away from the literal move (vi). My
first version required the relator to be the generator itself and rejected all
33 certificates, and the difference is exactly a Q-move, so this is a
documentation point about the round-3 format and not a defect, because
conjugation is available. Second, every one of the 33 certificates has the shape
Lemma 1 predicts: a generator is adjoined, used as a storage letter, a relator is
driven to a conjugate of a generator, and that generator is deleted at the end.
In Zieschang's certificate the state just before the deletion is
`(z^-2 y z^2, z^-5 x^3)`, so the deleted relator is a conjugate of the letter y
and the other relator is what remains. The one-letter mechanism is therefore not
an artificial target; it is what the literature's certificates do.

## 9. A beam search with long conjugators, and what it found

`beam.py` is a deterministic beam search that treats the substitution step of
Lemma 1 as a single macro, so conjugators of length up to 8 cost one move. Its
state score is the length of the shortest relator and then the total length, and
its target is a rank-2 presentation with a relator of length 1 whose letter is
absent from the other relator. Every macro records the primitive Q** moves it
stands for, and a hit writes a certificate in the m9 format.
**[computed here]**

On AK(3) at cap 26 with width 30 and depth 10 it reduces the shortest relator
from 6 to 5 in one move and then never below 5, ending at
`(x^2 y^-1 x^-1 y^-1, x y^-1 x y^-1 x y^5)`, which has shortest relator 5 and
total length 15. That is what the exhaustive box already says. On the control
AK(2) = (x y x y^-1 x^-1 y^-1, x^3 y^-2), which is AC-trivial by a published
19-move chain, it also stops at 5 within the same budget. So this search is
weaker than the box at cap 20 for the negative, and too weak to serve as a
control for the positive. I record it as a failure: a beam on this score is not
the right instrument, and I did not find a Q**-trivialisation of AK(3), of AK(2),
or of anything else with it.

## 10. What this decides, and what it does not

Decided. Lemma 1 reduces Q**-triviality of a rank-2 presentation of the trivial
group to reaching a relator of length 1 and gives a verified certificate builder
for the second half. Lemma 2 bounds the intermediates of a long conjugation by
the larger of the two ends, which removes the conjugator cap as an explanation
for any box-confined negative. Proposition 3 is an exhaustive statement about
AK(3) inside the move set and the box it names, and Proposition 4 is an
exhaustive statement about the minimal lengths. **[checked for all three]**

Not decided. Whether AK(3) is Q**-trivial. Two gaps remain. The first is rank 3
and above: Section 7 shows that the rank-3 box is already unaffordable at total
length 15, so a Q**-level census at cap 20 with rank 3 needs a different
definition of the box or a symmetry quotient that I did not find. The second is
Barmak's move (iv) with an automorphism whose images are longer than 3: the
component is unchanged by all automorphisms with images of length at most 2 at
cap 20 and by all with images of length at most 3 at caps 15 and 16, but that is
a check and not a proof, and no bound like Lemma 2 for automorphism
decompositions is available here.

Not verified by me. The statement that AK(3) presents the trivial group is round
3's, from `directions/ak-status/ak_trivial.lean`, and I did not replay that Lean
proof. The rank-3 counts count ordered tuples of relators and I did not add
relator permutations as a move, so a rank-3 presentation could be counted twice
if the enumeration reaches both orders; the rank-2 counts use the same
convention as the round-2 census, which was validated there.

## 11. Files and exact commands

All in `directions/qdouble-star/m6/`, byte-identical to
`.ultramath/smw38010i/m6/qb/`:

| file | what it is |
| --- | --- |
| `qbox.c` | the box enumerator: rank 2 or 3, Q or Q* or Q**, automorphism sets, class counts, target tests, path dump |
| `qcheck_paths.py` | independent replayer for the path certificates |
| `conj_bound.py` | machine check of Lemma 2 and of the junction formula |
| `peel.py` | the one-letter recipe: builds and replays Q**-trivialising certificates |
| `m9check.py` | independent replayer for the m9 certificate format |
| `beam.py` | the beam search with long-conjugator macros |
| `results.txt` | every run quoted here, one line each |
| `peel_rank2.cert`, `peel_full.cert` | the demonstration certificate of Section 3 |
| `paths20.txt` | 50,000 path certificates at cap 20 |

    $ gcc -O2 -o qbox qbox.c
    $ ./qbox 20 --classes 1 --nopar 1 --htbits 27 --arena 2048          # Q, 51,411,456 and 79,680
    $ ./qbox 20 --nielsen 1 --classes 1 --nopar 1 --paths 50000 paths20.txt \
          --htbits 27 --arena 2600                                      # Q*, 66,996,960 and 109,072
    $ ./qbox 20 --autL 2 --nopar 1 --htbits 27 --arena 2600             # 72 automorphisms, same 66,996,960
    $ ./qbox 16 --autL 3 --nopar 1 --htbits 26 --arena 2048             # 744 automorphisms, same 602,176
    $ ./qbox 15 --nielsen 1 --rank3 1 ...                               # rank-3 box, the wall
    $ ./qbox 15 --nielsen 1 --conj 2 ...                                # conjugator invariance, 241,216
    $ python3 qcheck_paths.py paths20.txt
    $ python3 conj_bound.py
    $ python3 peel.py selftest
    $ python3 peel.py cert "2" "1 2 1 -2 -1"
    $ python3 directions/pu-enumeration/replay_certs.py peel_rank2.cert
    $ python3 m9check.py directions/qdouble-star/m9/certs/*.cert
    $ python3 beam.py "1,2,1,-2,-1,-2;1,1,1,-2,-2" 26 30 10 --maxpref=6
