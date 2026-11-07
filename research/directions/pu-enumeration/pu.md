# Enumeration of the AK(3) class inside a total-length box

Round 2 direction E3 (Panteleev-Ushakov style enumeration of the Andrews-Curtis
class of AK(3)). Everything in this file is either a deterministic computation
with the exact command given, or a labelled interpretation. Nothing here says
anything about the truth or falsehood of the Andrews-Curtis conjecture, and no
claim of a proof or disproof is made.

## 1. Summary

I wrote a from-scratch breadth-first enumerator (`rawbox.c`) of the
Andrews-Curtis class of AK(3) inside an explicitly defined box, and I ran it to
the largest box this VM holds. The results:

* The census is complete at every total-length cap from 13 to 20. At cap 20 the
  box contains 51,411,456 tuples, which fall into 79,680 classes under
  conjugation and inversion of the relators, and into 2,967 classes under the
  full Panteleev-Ushakov relation of their Section 4.2.
* Every tuple carries an explicit move path from AK(3). All 79,680 class
  certificates (4,640,600 elementary AC moves) and all 20,560 state
  certificates of the cap-16 run (388,717 moves) replay exactly under an
  independent checker (`replay_certs.py`, written from the definitions, sharing
  no code with the search) and under the Round-1 toolkit (`toolkit/ac.py`).
* I did not reproduce Table 1 of Panteleev and Ushakov. My counts are below
  theirs at every total length, and the deficit does not close at the largest
  cap this VM holds. Section 6 gives both tables and the exact comparison.
* I did not reach the per-relator cap of 17 in their sense. My cap is a bound on
  the total length of an intermediate tuple. The next cap, 21, exceeded the
  memory of the VM after 187,904,819 tuples. Section 8 records this as the exact
  failure point.

## 2. The object and the box

Let F = F(x,y) and let a presentation be a pair (u,v) of reduced words. AK(3) is
the pair

    AK3 = (xyxy^-1x^-1y^-1, x^3y^-4),

of total length 13. The three Andrews-Curtis moves are

    inv i   :  r_i -> r_i^-1
    mul i j :  r_i -> r_i r_j          (i != j)
    conj i w:  r_i -> w r_i w^-1       (w any word)

A tuple is in the box B(T) when |u| + |v| <= T. The enumerator walks the graph
whose vertices are the tuples of B(T) reachable from AK3 and whose edges are the
moves that stay in B(T), with `conj` restricted to conjugating words of length at
most K. It is deterministic: the vertex set is finite, the move list at each
vertex is fixed, and no randomness is used anywhere.

Two parameters are reported with every run: the total-length cap T and the
conjugator bound K. The main table uses K = 1. Runs with K = 2 and K = 3 give
exactly the same vertex set and the same class set at every cap where they were
compared (Section 5), so the conjugator bound is not the binding constraint.

## 3. What the search guarantees

Soundness: every vertex is reached by an explicit sequence of the three moves
applied to AK3. The parent pointer of each vertex records the move that created
it, and the certificate files list those moves as elementary AC moves with the
conjugating word written out. Replaying a path with `replay_certs.py` checks the
claim from the definitions.

Completeness inside the box: the search is a breadth-first traversal of the
connected component of AK3 in the finite graph described in Section 2. It
therefore finds every tuple of B(T) that is reachable from AK3 by a path whose
intermediate tuples all lie in B(T) and whose conjugating words have length at
most K. It does not find tuples that need a longer intermediate tuple.

Invariant check: under all three moves the exponent-sum matrix of the pair
changes by an invertible integer row operation, so its determinant stays +-1.
All 79,680 classes of the cap-20 census have determinant +-1. This rules out the
possibility that an implementation error produced tuples outside the class.

## 4. Census

The command for a run is

    gcc -O2 -o rawbox rawbox.c
    ./rawbox T K -l classes.txt [-c certs.txt] [-a]

`-a` writes a certificate for every vertex; without it one certificate is
written per class. Times are wall clock on this VM (4 CPUs, 16 GB), from
`/usr/bin/time -v` and the program's own timers. The memory figures are from
runs made with a 2^27-slot hash table. The source shipped here uses the same
size, which is enough for cap 20 and for 94 million tuples in total.

| T  | raw tuples | classes (conj) | PU-classes | time  | peak RSS |
|----|-----------:|---------------:|-----------:|------:|---------:|
| 13 |        168 |              1 |          1 |  0.0s |    29 MB |
| 14 |        168 |              1 |          1 |  0.0s |    29 MB |
| 15 |      6,864 |             26 |          7 |  0.0s |    29 MB |
| 16 |     20,560 |             80 |         11 |  0.0s |    79 MB |
| 17 |    857,808 |          2,000 |        168 |  0.9s |   564 MB |
| 18 |  2,014,992 |          4,256 |        299 |  4.3s |   614 MB |
| 19 | 23,609,984 |         40,048 |      1,513 |   54s |   1.5 GB |
| 20 | 51,411,456 |         79,680 |      2,967 |  137s |   2.6 GB |
| 21 | >187,904,819 | not reached | not reached | 295s | 8.9 GB (stopped) |

"PU-classes" is the number of classes under the relation of Section 4.2 of
Panteleev and Ushakov: swap of the two relators, inversion of one relator,
conjugation of one relator, and an automorphism of the free group. The
automorphism quotient is computed with Whitehead's minimisation over the 20
Whitehead automorphisms of F(x,y), followed by the least representative among
the automorphism images of minimal total length. The implementation passes a
self-test: for a random sample of classes, applying random automorphisms and
recomputing the normal form returns the same class (0 failures in every run
reported here).

Class counts by total length at the cap-20 run, where the entry is the number of
PU-classes whose minimal total length equals the row label:

    13: 2    14: 5    15: 35    16: 40    17: 206
    18: 246  19: 1209 20: 1224

and the cumulative counts N(<=T) are 2, 7, 42, 82, 288, 534, 1743, 2967 for
T = 13, ..., 20.

## 5. Verification

Every certificate file in this directory was replayed by `replay_certs.py`,
which implements free reduction, inversion, multiplication and conjugation from
the definitions in 120 lines of Python and shares no code with the enumerator.

    python3 replay_certs.py cert16all.txt
      certificates checked: 20560, verified: 20560, failed: 0
      moves per certificate: total 388717, max 39, mean 18.91

    gunzip -c cert20k1.txt.gz | python3 replay_certs.py /dev/stdin
      certificates checked: 79680, verified: 79680, failed: 0
      moves per certificate: total 4640600, max 142, mean 58.24

A second check uses the Round-1 toolkit, whose word arithmetic is independent of
both programs above:

    python3 xcheck_toolkit.py cert16all.txt
      toolkit cross-check: 20560 lines, 20560 verified, 0 failed, 388717 elementary moves

The whole cap-20 certificate file was also replayed through the toolkit, after
gunzipping it to a temporary file:

    python3 xcheck_toolkit.py cert20_tmp.txt
      toolkit cross-check: 79680 lines, 79680 verified, 0 failed, 4640600 elementary moves

So every certificate in this directory has been checked by two independent
implementations of the moves.

The conjugator bound was tested at three values. At T = 18 the runs with K = 1,
K = 2 and K = 3 give exactly the same tuple count (2,014,992) and the same class
count (4,256). At T = 19 and T = 20 the runs with K = 1 and K = 2 agree in the
same way. So raising K from 1 to 3 changes nothing in the range covered here.

## 6. Comparison with the published table

Panteleev and Ushakov, "Conjugacy search problem and the Andrews-Curtis
conjecture", Groups Complexity Cryptology 11 (2019), no. 1, 43-60, DOI
10.1515/gcc-2019-2005, arXiv:1609.00325 (submitted 1 September 2016). The DOI,
the volume, the page range and the journal were checked against the Crossref
record; the abstract of the journal version states that the authors "enumerate
balanced presentations AC-equivalent to AK(3) with relations of lengths up to 20
(previous record was 17)".

Their Table 1 reports, in the column L = 17 (identical to the columns L = 18,
19, 20), the values

    T = 13: 4,  14: 10,  15: 70,  16: 86,
    T = 17: 458,  18: 590,  19: 3226,  20: 3356.

I read the cells as counts of normal forms of total length at most T. Their text
supports this reading: "we can conjecture that the number of normal forms of
AK(3)-equivalent presentations of total length 20 or less is 3356". If the cells
were counts of total length exactly T, the sum up to 20 would be 7,800, which
contradicts that sentence.

My cumulative counts at the cap-20 run are

    T = 13: 2,  14: 7,  15: 42,  16: 82,
    T = 17: 288,  18: 534,  19: 1743,  20: 2967.

The two sequences agree closely at some lengths (16: 82 against 86; 20: 2967
against 3356) and differ by a factor near two at others (13: 2 against 4; 19:
1743 against 3226). I did not reproduce their table, and I do not have an
explanation that I have verified. Three candidate explanations follow, labelled
as interpretations:

1. Their search allows intermediates of total length up to 2L + 2 = 36, while my
   box caps intermediates at 20. My counts do grow with the cap at the small
   lengths (N(<=15) is 7, 9, 37, 38, 39, 42 for caps 15 to 20), so a larger cap
   would raise them.
2. Their search uses ACM-moves, which they state are equivalent to AC-moves for
   AC-equivalence. Such moves can cross the class faster than the three plain
   moves, so their search can reach members that my plain-move search needs more
   box for.
3. Their normal form procedure and mine may differ in the choice of
   representative, which can change class counts if two of their stored pairs
   fall in one of my classes or the reverse.

If explanation 1 is right and their cells use the same equivalence relation as
mine, then their number 4 at T = 13 against my complete and converged count of 2
at caps 17 to 20 shows that at least two members of their class of total length
13 need an intermediate tuple of total length greater than 20. I record that as
a conditional deduction from their published number, not as an established fact.

COORDINATOR CORRECTION, 2026-11-04, from the Round 3 direction directions/pu-gap/
(member m5, swarm smw2opo0o), checked by the coordinator. The conditional
deduction above is WITHDRAWN. The cells of Table 1 of arXiv:1609.00325 count
pairs of total length EQUAL to T, not at most T: Section 6.1 and the table
caption say so, and the L = 10 column falls from 240 at T = 19 to 10 at T = 20,
which a cumulative count of one fixed run cannot do. The comparison above
therefore crossed two conventions. Under the per-length reading their cells are
exactly twice our per-length PU-class counts at T = 13, 14 and 15 (4, 10, 70
against 2, 5, 35), which is the relator-order convention, and the class bound
of at most three length-13 PU classes (conditional on AK(3) not being
AC-trivial) shows their cell of 4 is two classes entered twice, not four
classes. What survives: a third length-13 candidate class C exists, its eight
presentations lie outside the cap-20 box, and any AC path from AK(3) to one of
them needs an intermediate pair of total length at least 21. See
directions/pu-gap/pu-gap.md for the full analysis.

## 7. The shortest members found

The class has exactly two PU-classes of minimal total length 13 in the cap-20
box. Normal forms, written with x, y, X = x^-1, Y = y^-1:

    (xxxxyyy, xyXyxY)        i.e.  (x^4 y^3, x y x^-1 y x y^-1)
    (xxxyXYY, xxYYXy)        i.e.  (x^3 y x^-1 y^-2, x^2 y^-2 x^-1 y)

The first is AK3 after an automorphism and cyclic rewriting; the second is a
different member of the same class. Both have unimodular exponent-sum matrix
(+1 and -1). So AK(3) is not the only member of its class of length 13, and a
census that lists only AK(3) at the minimum length is incomplete. Panteleev and
Ushakov report four such classes at L = 17.

The two certificates are in `shortest_two.cert`: the second representative
needs 36 elementary moves from AK3, and both replay under `replay_certs.py` and
under the toolkit. The first representative is reached by the single move
`m12`, which takes AK3 to a tuple of total length 20 in the same class.

## 8. Bounded negatives and the exact failure point

Bounded negative 1. In the whole cap-20 census every relator has length at least
5; the distribution of the shorter relator of each class is 5: 19,480, 6: 14,288,
7: 29,120, 8: 6,096, 9: 10,696. The standard tuple (x, y) has total length 2, so
there is no AC path from AK3 to the standard tuple whose intermediate tuples all
have total length at most 20. This is a statement about the box only. It does
not say that AK(3) is not AC-trivial.

Bounded negative 2. The same computation shows that no tuple in the box has a
relator of length 1 or 2. A tuple one move away from the standard tuple has a
relator that is a conjugate of x or y (the inverse of an inv or conj move) or a
word such as xy^-1 (the inverse of a mul move). If the last move of a
trivialisation is an inversion, a multiplication, or a conjugation by a word of
length at most 1, then its penultimate tuple has a relator of length at most 4,
so that tuple is outside the box. The census therefore rules out every
trivialisation whose last move has conjugating word of length at most 1 with all
intermediate tuples of total length at most 20.

Exact failure point. The run at cap 21 stopped when the hash table reached
187,904,819 live tuples and 8.9 GB of resident memory. The growth factor from
cap 20 to cap 21 is above 3.6, so cap 22 would need more than 20 GB. The per
relator bound of 17 in the Panteleev-Ushakov sense (total length up to 36) is
out of reach on this VM with this implementation, and their own figure for a
comparable run is 207 CPU-days at L = 20.

## 9. What is not established

1. I did not reproduce Table 1 of Panteleev and Ushakov, and I did not verify
   their claim that the enumeration at L = 20 found no trivialisation.
2. I did not verify that ACM-moves and AC-moves generate the same equivalence;
   I only use the three plain moves.
3. The comparison in Section 6 is numerical and conditional. The three candidate
   explanations are labelled as interpretations.
4. Nothing here bears on whether AK(3) is AC-trivial, and nothing here is a step
   toward deciding the conjecture.

## 10. Files and exact commands

* `rawbox.c`, the enumerator. Build with `gcc -O2 -o rawbox rawbox.c`.
* `nf.py`, normal form under the relation of Section 4.2 (Whitehead
  minimisation plus least minimal-length representative).
* `puclass2.py`, counts PU-classes in a class file, in parallel.
* `replay_certs.py`, independent certificate replayer.
* `xcheck_toolkit.py`, cross-check against `toolkit/ac.py`.
* `shortest.py`, prints the shortest class representatives.
* `cert16all.txt`, one certificate per tuple of the cap-16 run (20,560 lines).
* `cert20k1.txt.gz`, one certificate per class of the cap-20 run (79,680 lines).
* `cls20k1.txt.gz`, the cap-20 class list.
* `census.txt`, the same numbers in plain text with the run parameters.

Rerun commands, all from this directory:

    gcc -O2 -o rawbox rawbox.c
    ./rawbox 16 1 -a -c cert16all.txt
    ./rawbox 20 1 -l cls20k1.txt -c cert20k1.txt
    python3 replay_certs.py cert16all.txt
    gunzip -c cert20k1.txt.gz | python3 replay_certs.py /dev/stdin
    python3 xcheck_toolkit.py cert16all.txt
    gunzip -c cls20k1.txt.gz | python3 puclass2.py /dev/stdin
    python3 shortest.py

The last command needs `cls20k1.txt` in the current directory and takes about
ten minutes because it canonicalises all 79,680 classes.
