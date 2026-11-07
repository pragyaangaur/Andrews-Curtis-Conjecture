# Certificate algebra: one move calculus for every stored certificate

Round 5, member m3, direction "certificate algebra". This file defines the move
systems that the repository's certificate families use, gives an exact
transport of every derived move into the three Andrews-Curtis relator moves
together with the peak total relator length of that transport, and replays every
stored certificate through one engine. Every claim is labelled **Computed**,
**Verified**, **Argument** or **Open**. Nothing here is a claim about the truth
or the falsehood of the Andrews-Curtis conjecture.

## 0. Summary

The repository stores certificates in six different formats, with three
different index conventions, and in four different move systems. One engine now
reads all of them. **Computed** with `./run_all.sh` (39, 44 and 49 s on three runs on this VM):

| quantity | value |
| --- | --- |
| certificate files read | 67 |
| certificates replayed | 259,755 |
| native moves replayed | 7,741,874 |
| certificates whose endpoint differs from the one the file declares | 0 |
| certificates that are Q-certificates (Andrews-Curtis relator moves) | 259,722 |
| certificates that need the Q** move set | 33 |

Two things in the table are new. First, every one of the 259,722 Andrews-Curtis
certificates also replays after transport into the twelve restricted moves of
the resisters engine, and the transported path never has a larger peak total
relator length than the path the file records (**Verified**, 0 violations in
259,722 certificates). Second, the four multiplication forms that round 4 named
as the remaining gap in that move set are one, three, five and three moves of
the same twelve-move set, with every intermediate inside the box of the two
endpoints (section 5, **Argument** and **Computed** exhaustively). The exact
sentence of `directions/resisters/round4/README.md` that this contradicts is
quoted in section 5.

## 1. The move systems

A state is a rank together with a tuple of relators in that rank. The number of
relators need not equal the rank, because the Q** certificates are unbalanced
single-relator presentations.

**The Q layer** is Barmak's (i) to (iii), the classical Andrews-Curtis moves on
relators, with the generators fixed:

    ('inv', i)        r_i -> r_i^{-1}
    ('mul', i, j)     r_i -> r_i r_j            (i different from j)
    ('conj', i, w)    r_i -> w r_i w^{-1}

**The twelve restricted moves** are the move set of `directions/resisters`:
the two inversions, the two right multiplications (r_1 r_2 and r_2 r_1), and
the eight conjugations by one letter. They are Q moves, so anything they prove
is an Andrews-Curtis result. The set is written out in `reslib.py` and, with a
different numbering, in `directions/p-trivial/replay12.py`.

**Q\*** adds the automorphisms of the free group, in practice the elementary
Nielsen moves `neg`, `nij`, `nji`, `nijinv`, `njiinv` and `swap`, which act by
substituting a generator image into every relator at once.

**Q\*\*** adds the stabilisation pair `prolong` (add a generator and the relator
equal to it) and `delete` (the inverse, when the generator occurs in exactly one
relator and that relator cyclically reduces to the generator).

The systems are nested, Q inside Q\* inside Q\*\*, and the twelve moves sit
inside Q. The families and the systems they actually use, as read from the
files:

| family | files | format | system | indices |
| --- | --- | --- | --- | --- |
| `directions/resisters/*_certs.txt` | 2 | `start\|moves\|target` | twelve | 0-based relators |
| `directions/c14/certs_all.txt` | 1 | `start\|moves\|target` | twelve | 0-based relators |
| `directions/worst-case/min_cap14.txt`, `min_cap15.txt`, `new_certs.txt` | 3 | `start\|moves\|target` | twelve | 0-based relators |
| `directions/pu-enumeration/cert16all.txt`, `cert20k1.txt.gz` | 2 | `class K start ... moves ... end ...` | twelve | 1-based relators |
| `directions/p-trivial/certs/*.cert` | 3 | `class K start ... moves ... end ...` | twelve | 1-based relators |
| `directions/ms-ak-certs/*.json` | 18 | JSON, words as strings | Q | 1-based relators |
| `directions/c14/carreras/*.json` | 5 | JSON, words as integer lists | Q plus rotation | 0-based relators |
| `directions/qdouble-star/m9/certs/*.cert` | 33 | `start n ...` / `move ...` / `end n ...` | Q** | 1-based, rank can change |

Three conventions differ between the formats and are worth recording, because a
reader of one file who assumes the convention of another will misread it. The
pipe format names relators from 0 and the two relator-level families name them
from 1. The pipe format abbreviates the standard pair as `std`. The
pu-enumeration files terminate a conjugation token with a comma when a token
follows the word (`c1=1,`), so tokens must be stripped before parsing.

## 2. Transports, with exact costs and peak lengths

Every derived move below is a composite of Q moves. The table gives the
composite, its length, and the bound on the peak total relator length that holds
for every state, where S is the total length before the move and E the total
length after it.

| move | effect | transport | moves | peak |
| --- | --- | --- | --- | --- |
| `inv i` | r_i -> r_i^{-1} | itself | 1 | max(S,E) |
| `mul i j` | r_i -> r_i r_j | itself | 1 | max(S,E) |
| `conj i w` | r_i -> w r_i w^{-1} | one letter conjugation per letter of w, last letter first | length of w | max(S,E) |
| `conj_letter i g` | r_i -> g r_i g^{-1} | itself | 1 | max(S,E) |
| `mul_inv i j` | r_i -> r_i r_j^{-1} | invert j, multiply, invert j | 3 | max(S,E) |
| `lmul_inv i j` | r_i -> r_j^{-1} r_i | invert i, multiply, invert i | 3 | max(S,E) |
| `lmul i j` | r_i -> r_j r_i | invert i, invert j, multiply, invert i, invert j | 5 | max(S,E) |
| `cycle i k` | left rotation of r_i by k letters | conjugate by the suffix r_i[k:] | 1 | max(S,E) |
| `neg`, `nij`, ... | generator automorphism | none | - | - |
| `prolong`, `delete` | rank change | none | - | - |

The three identities behind the table are written out as group products. For
the inverse multiplication, r_i r_j^{-1} is reached by inverting r_j, multiplying
r_i by the inverted r_j, and inverting r_j back; the peak is the end total
because inverting does not change a length. For the left multiplication, the
identity is r_j r_i = (r_i^{-1} r_j^{-1})^{-1}; the transport inverts both
relators, multiplies, and inverts both back, and the intermediate total is
|r_i^{-1} r_j^{-1}| + |r_j| = |r_j r_i| + |r_j|, which is exactly the end total.
For the left multiplication by an inverse, r_j^{-1} r_i = (r_i^{-1} r_j)^{-1},
and the transport inverts r_i, multiplies by r_j, and inverts r_i back.

The transport of `lmul` through a conjugation and a multiplication, which is the
one used in `directions/qdouble-star/m9/qverify.py`, also works but its
intermediate r_j r_i r_j^{-1} has total length up to S + 2|r_j|, which can exceed
both endpoints. That is why the five-move transport matters for a box-bounded
search. **Argument**, and checked on a resister of the round-4 ledger by
`transports_demo.py` (**Computed**):

    start BBAAbaa,BBababA, total 14
    ('mul', 1, 2)      -> BBAAbaaBBababA,BBababA    1 move,  peak 21 = max(start,end)
    ('mul_inv', 1, 2)  -> BBAAbaaaBABAbb,BBababA    3 moves, peak 21 = max(start,end)
    ('lmul', 1, 2)     -> BBababABBAAbaa,BBababA    5 moves, peak 21 = max(start,end)
    ('lmul_inv', 1, 2) -> aBABAAAbaa,BBababA        3 moves, peak 17 = max(start,end)

## 3. The transports are checked exhaustively

`selftest.py` applies every transport of section 2 to every ordered pair of
reduced words whose total length is at most 6 in F_2, and at most 5 in F_3, and
compares the transported endpoint with the direct definition of the move. It
also checks the peak bound of the table on every one of those instances.
**Computed**, `python3 selftest.py`:

    PASS transports reproduce the direct move, F_2, total length <= 6:
         11665 pairs, 303290 moves, 0 mismatches
    PASS every transport stays inside the endpoint box, F_2, total length <= 6:
         303290 moves, 0 violations, slack per kind {'inv': 0, 'conj_letter': 0,
         'conj': 0, 'mul': 0, 'mul_inv': 0, 'lmul': 0, 'lmul_inv': 0}
    PASS transports reproduce the direct move, F_3, total length <= 5:
         30469 pairs, 1035946 moves, 0 mismatches
    PASS every transport stays inside the endpoint box, F_3, total length <= 5:
         1035946 moves, 0 violations, slack per kind {'inv': 0, 'conj_letter': 0,
         'conj': 0, 'mul': 0, 'mul_inv': 0, 'lmul': 0, 'lmul_inv': 0}
    PASS a rotation of any word is one Q conjugation: 8020 rotations, 0 failures
    PASS Q* moves are outside the Q layer and act by substitution:
         33 Nielsen moves tested, 0 mismatches, all 33 classified as having no Q transport
    FAILURES: 0

The slack column is the largest excess of the transported peak over
max(S,E) for that move kind, and it is zero for every kind, so the bound in the
table is attained and never exceeded on the tested range.

One point of the `cycle` transport is worth recording because it looks like a
condition and is not one. A left rotation of a word by k letters is the
conjugation by the suffix of length |r| - k, for every word, whether or not it
is cyclically reduced: the conjugate r[k:] r r[k:]^{-1} freely reduces to
r[k:] r[:k], which is the rotation reduced. So a certificate that uses rotations
is a Q certificate without any side condition. My first implementation imposed
cyclic reduction here and refused four of the five Carreras certificates; the
self test caught it at the first run.

## 4. Every stored certificate replayed by one engine

`replay_all.py` reads all 67 certificate files, replays the native moves, and
compares the endpoint with the endpoint the file declares. It then classifies
every move as Q, Q*-only or Q**-only, and, when every move has a Q transport,
replays the transported path as well and compares peak totals.
**Computed**, `python3 replay_all.py`:

| family group | files | certs | native moves | restricted moves | Q* moves | Q** moves | failures | peak | longest |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| resisters | 2 | 98 | 11,951 | 11,951 | 0 | 0 | 0 | 22 | 184 |
| c14 `certs_all` | 1 | 53,866 | 1,420,102 | 1,420,102 | 0 | 0 | 0 | 19 | 141 |
| worst-case | 3 | 105,492 | 1,278,325 | 1,278,325 | 0 | 0 | 0 | 15 | 50 |
| pu-enumeration | 2 | 100,240 | 5,029,317 | 5,029,317 | 0 | 0 | 0 | 20 | 142 |
| p-trivial | 3 | 3 | 108 | 108 | 0 | 0 | 0 | 23 | 43 |
| ms-ak-certs | 18 | 18 | 648 | 3,774 | 0 | 0 | 0 | 75 | 73 |
| c14/carreras | 5 | 5 | 271 | 345 | 0 | 0 | 0 | 33 | 85 |
| qdouble-star/m9 | 33 | 33 | 1,152 | none | 394 | 66 | 0 | 582 | 92 |
| all | 67 | 259,755 | 7,741,874 | 7,743,922 | 394 | 66 | 0 | 582 | 184 |

The peak column is the largest total relator length reached by any transported
path in the group, and the transported peak never exceeded the native peak in
any of the 259,722 certificates that have a transport (**Verified**, the failure
count is zero).

Where the repository already recorded a total, this replay reproduces it
exactly, which is an independent check on both sides. The cap-16 pu-enumeration
file has 388,717 moves and the cap-20 file 4,640,600 (round 3 recorded both
numbers); the c14 file has 53,866 certificates with the longest certificate 141
moves (round 2 recorded both); the resisters have 98 certificates with maxima
184 and 138 (round 3 recorded both); and the three p-trivial certificates reach
peaks 23, 22 and 20, which are the caps stated in their own header comments.

A second implementation checks every certificate of the rank-2 formats without
sharing any code with the first: words are strings, reduction is a character
stack, and the moves are written out again from the token names.
**Computed**, `python3 strverify.py 1`:

    sampled 259699 certificates, 7739803 moves, 0 failures

The two engines agree on the total: the main engine's move total over the same
files is 7,741,874 minus the 2,071 moves of the 56 certificates in the three
JSON and Q** formats, which is 7,739,803, exactly the string engine's total.

## 5. What the transports say about total-length boxes, and one correction

A box is a set of states of total relator length at most C. The transports of
section 2 have this consequence. **Argument**: if a move takes s to t and both
are in the box, the transport takes s to t with every intermediate of total
length at most max(|s|,|t|), hence inside the box. So the reachable set inside
any box is the same for the twelve restricted moves and for the move set
extended by all four multiplication forms. **Computed** as a check: the
exhaustive test of section 3 finds zero violations of the peak bound, and the
replay of section 4 finds zero certificates whose transported path leaves the
peak of the path the file records.

This contradicts a sentence of the round-4 resister report, and the point
matters because round 5's direction H3 takes the sentence as its premise.
`directions/resisters/round4/README.md` lines 249 to 255 say:

> The gap that remains is the other two multiplication forms of the full
> Andrews-Curtis move set, namely left multiplication and multiplication by an
> inverse relator. The twelve-move family reaches both, but only through
> intermediate tuples that can be longer than the two endpoints, so a path that
> uses them inside the box is not excluded by these bounds.

The clause about intermediates is false as stated for relator multiplication.
Left multiplication is five moves of the twelve-move family with every
intermediate at most max(S,E), and multiplication by an inverse relator is
three moves with the same bound (**Argument** by the identities of section 2,
**Computed** exhaustively in section 3). Two consequences follow, and I state
them separately because only the first is unconditional.

First, extending an engine by these four forms cannot change any hit outcome
inside any total-length box, so a direction that extends the resisters engine by
them and searches the same caps should expect identical counts. Second, if one
takes the round-4 conjugator theorem (that conjugators longer than one letter
add nothing inside a box, `README.md` section 5) as given, then the in-box
reachable set of the twelve restricted moves equals the in-box reachable set of
the full Andrews-Curtis move set Q, since every Q move is a typed move of
section 2. I did not re-prove that conjugator theorem, and the second consequence
rests on it.

The other reading of H3, in which the notation x_i -> x_j x_i denotes a move on
generators rather than on relators, is a different matter, and the bounds say
nothing about it. A generator move is the Q* move `nij`: it substitutes one
generator image into every relator at once, it is not a Q move, and it has no Q
transport in this calculus.

## 6. What each stored certificate actually certifies

**Verified** by the replay of section 4. The certificates in the resisters, c14,
worst-case, pu-enumeration, p-trivial, ms-ak-certs and carreras families are
Andrews-Curtis certificates in the Q move set, and each of them is a certificate
in the twelve restricted moves after transport. In particular no family needs
the Q* or Q** moves, and the bounds and falls recorded in those directions rest
on Q moves alone.

The Carreras certificates use two abbreviations that are Q moves after expansion.
`mul i j -1`, multiply by an inverse, is three Q moves. `cycle i k`, a left
rotation, is one conjugation, as explained in section 3. Their native move
counts and their costs in the twelve-move system are 13 to 17, 36 to 48, 66 to
88, 71 to 97 and 85 to 95 moves, with peaks 23, 27, 24, 22 and 33, which are the
envelope of the intermediate lengths already reported for them.

The 33 Q** certificates of `directions/qdouble-star/m9/certs` are a different
kind of object, and the algebra makes the difference exact. Each of the 33 uses
exactly two moves that change the rank, one `prolong` and one `delete`, and
between 7 and 31 Nielsen moves; the remaining 692 of their 1,152 moves are Q
moves. None of the 33 is a Q certificate, and none is a Q* certificate, because
every one of them uses the stabilisation pair. Their endpoints are single-relator
presentations, so the Q calculus, which keeps the rank and the number of
relators fixed, cannot express them at all. This is the precise sense in which
the Q**-triviality of the Zieschang pair and of the McCool-Pietrowski family is
a statement about a strictly larger relation than the Andrews-Curtis relation.

**Verified** by reading the declared start and end lines of the 33 Q** files: the
endpoints are the published pairs. Zieschang's file runs from x^3 y^3 x^3 y^2 to
x^3 y^5, and each of the 32 named McCool-Pietrowski files runs from (x^k y^t)^p y
to x^k y^{pt+1} with the (k,p,t) of its file name, 32 of 32 matching.

## 7. Limits

I did not re-derive any search. The certificates are replayed, and the replay
confirms that each file's move list carries its start to its declared end; that
says nothing about whether the search that produced the file was complete.

The costs in the transport table are the lengths of the transports written here.
I do not claim that they are minimal, and a shorter transport would only
strengthen the box statement.

The box consequence of section 5 is proved for the four multiplication forms and
for conjugators of any length separately; the combination that covers all Q
paths in one step uses the round-4 conjugator theorem, which I take as an
argument from that report. The elementary part, which is the part that
contradicts the quoted sentence, does not use it.

The Q** replay validates each move against the current state and compares the
endpoint, which is the same standard the direction's own checker uses. It does
not check that the declarations in the header comments about how the pairs were
built are correct.

## 8. Exact commands and their output

From this directory, `./run_all.sh` runs everything in about 45 s and writes the logs
into `results/`. **Verified** on this VM, exit status 0, run from the installed
path `directions/certificate-algebra/`. The individual commands
are:

    python3 selftest.py          # FAILURES: 0, output in results/selftest.txt
    python3 replay_all.py        # families 67, certificates 259755, replay failures 0
    python3 strverify.py 1       # sampled 259699 certificates, 7739803 moves, 0 failures
    python3 transports_demo.py   # the four multiplication forms, section 2

The per-file table is `results/replay_table.tsv`, one row per certificate file,
with the counts, the move classifications, the peaks and the first failure, if
any. `results/replay_all.txt` holds the full per-family printout.

## 9. Files

| file | contents |
| --- | --- |
| `words.py` | free group words: reduction, inverse, product, conjugation, rotation, substitution |
| `engine.py` | states, the Q layer, the derived move layer, the transports, replays |
| `adapters.py` | readers for the six stored certificate formats |
| `selftest.py` | exhaustive transport checks, section 3 |
| `replay_all.py` | the uniform replay, section 4 |
| `strverify.py` | the second implementation, sampled |
| `transports_demo.py` | the transcript of section 2 |
| `run_all.sh` | one command for all of the above |
| `results/` | the logs and the per-file table |
