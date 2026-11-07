# Second referee report: the load bearing Round 1 artifacts

Referee: member m10, direction E10 ("second-referees"). Repository state: the
Round 2 checkout of 2026-11-04, with Round 1 accepted and Round 2 running.
Every number below was produced by a command recorded in section 7. Nothing in
this report was taken from another member's files without a rerun.

## 0. Verdicts

| target | artifact | verdict |
| --- | --- | --- |
| (a) | `directions/ak-status/ak_trivial.lean` | **SOUND** |
| (b) | `toolkit/words.py`, `toolkit/ac.py`, `toolkit/bfs.py`, and the recorded runs in `toolkit/runs/` | **SOUND**, with three notes that change no reachable statement |
| (c) | `survey/computational.md` section 8 and the code in `survey/computational/` | **SOUND** as numbers and as replayable certificates; one documentation gap (no stored certificate file for the length 11 branch) |
| (d) | the constants quoted in `survey/complexity.md` sections 2.2, 3.1 and 3.2 against the LaTeX of Bridson, arXiv:1504.04187 | **quotes SOUND, three derived claims wrong**: the printed Fibonacci bound is false as printed and the survey calls it true, the seed relator has length 9 and the survey says 8, and the recommendation to quote the additive constant 1 is backwards |

All three errors found lie in commentary and bookkeeping, and each has a repair
that keeps the load bearing conclusion. No error was found in the Lean file, in
the Python toolkit, or in the census numbers.

## 1. How this referee worked

I wrote an independent engine from the definitions, in a representation that
shares nothing with the code under review: a word is a Python string over
lowercase generator letters, the upper case of a letter is its inverse, and free
reduction is a stack that cancels `c` against `c.swapcase()`. The engine is
`.ultramath/smw2i9i4j/m10/work/myfr.py`; the drivers are `xcheck.py`,
`replay_certs.py`, `census_replay.py`, `ball.py`, `bridson_consts.py`,
`ak_def_check.lean`, `ak_gap.g`, `ak_gap2.g` and `orders_gap.g`, all in the same
directory. Determinants come from my own cofactor expansion in `myfr.py` and,
in the cross check, from `sympy`. The searches use the same move tags as the
toolkit so that the two implementations can be fed identical inputs, and every
comparison is a comparison of full vertex sets or full replay results rather
than of counts alone.

The Bridson material was read from the author's LaTeX, downloaded from
`https://arxiv.org/e-print/1504.04187`, which unpacks to `ACconjARXIV.tex`. The
arXiv abstract page for that identifier gives the title "The complexity of
balanced presentations and the Andrews-Curtis conjecture", the author
"Bridson, Martin R." and the date 2015-04-16, so the identifier is the paper the
survey cites. Line numbers below refer to `ACconjARXIV.tex`.

## 2. Target (a): `directions/ak-status/ak_trivial.lean`

### 2.1 The check that the file asks for

    $ lean directions/ak-status/ak_trivial.lean
    'AK.rel_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
    ... (11 lines, the same three axioms for each of the 11 theorems)
    exit status 0, 5.6 s wall

A text search of the file finds no `sorry`, no `admit`, no `axiom`, no
`native_decide`, no `set_option`, no `unsafe`, no `opaque`, no `partial` and no
`#eval`. The only `#` commands are the eleven `#print axioms` lines. The Round 1
report quotes 2.5 s for this run; the difference from my 5.6 s is machine load
and does not matter.

### 2.2 Definitional fidelity of `akRels`

The definition in the file is

    def akRels (n : Nat) : Set (FreeGroup (Fin 2)) :=
      {X ^ n * (Y ^ (n + 1))⁻¹, X * Y * X * Y⁻¹ * X⁻¹ * Y⁻¹}

with `X = FreeGroup.of 0` and `Y = FreeGroup.of 1`. This is exactly the relator
pair of AK(n) = <x, y | x^n = y^(n+1), xyx = yxy>: the first relator is
x^n y^-(n+1) and the second is x y x y^-1 x^-1 y^-1, which is xyx (yxy)^-1. The
same pair, in the same order, is written out in `survey/ak-status.md` line 29
("with relator pair (x^n y^-(n+1), x y x y^-1 x^-1 y^-1)"), so the file and the
survey agree.

I checked this in Lean as well, in `work/ak_def_check.lean`, which restates the
definition verbatim and states an independent transcription `refRels n` in which
the second relator is entered as the single element `(X*Y*X) * (Y*X*Y)⁻¹`:

    'Referee.second_relator' depends on axioms: [propext, Quot.sound]
    'Referee.rels_agree' depends on axioms: [propext, Quot.sound]
    'Referee.same_group' depends on axioms: [propext, Classical.choice, Quot.sound]

`rels_agree n : akRels n = refRels n` and `same_group n` transfers this to the
presented groups. The same file contains a `rfl` proof that
`PresentedGroup (akRels n)` is definitionally `FreeGroup (Fin 2)` quotiented by
`Subgroup.normalClosure (akRels n)`, so `Subsingleton (PresentedGroup (akRels n))`
is literally the statement that AK(n) presents the trivial group, and no
`PresentedGroup` convention can hide behind the statement.

### 2.3 Independent verification of the mathematical content

The proof in the file follows the printed argument of Akbulut and Kirby. I
checked the chain by hand in the presented group: from xyx = yxy one gets
y^-1 x y = x y x^-1; induction on k gives y^-1 x^k y = x y^k x^-1; at k = n the
relation x^n = y^(n+1) turns the left side into y^(n+1), so y^(n+1) = x y^n x^-1
and y^n = x^n; comparing with x^n = y^(n+1) gives y = 1 by left cancellation and
then xyx = yxy gives x^2 = x, so x = 1. Each Lean lemma in the file is that
step, and each is proved from the previous ones.

For an external check I ran GAP 4.14 on the relators transcribed from the Lean
definitions, not on any other source:

    n = 0: ExponentSums ok = true   index of trivial subgroup = 1; abelian invariants = [ ]
    n = 1: ExponentSums ok = true   index of trivial subgroup = 1; abelian invariants = [ ]
    n = 2: ExponentSums ok = true   index of trivial subgroup = 1; abelian invariants = [ ]
    n = 3: index of trivial subgroup = 1
    n = 4: index of trivial subgroup = 1
    n = 5: index of trivial subgroup = 1      (1.8 s for the three)

So the group is trivial for n = 0 to 5 by coset enumeration in a different
system. The Lean theorem covers every n, and the two statements agree on the
overlap.

### 2.4 Notes that do not affect the verdict

The file states AK(n) with the exponent n on x. The Akbulut and Kirby paper
prints <x, y | xyx = yxy, x^5 = y^4>, which is AK(4) after the two generators
are interchanged, and this convention is documented in `survey/ak-status.md`
section 2. My live check of the bibliographic record gives Topology volume 24,
issue 4, 1985, pages 375-390, so the page range in `ak_trivial.lean` is right
and the range 375-380 in the docstring of `toolkit/ac.py` is wrong. The Lean
theorem also covers n = 0, where the presentation presents the trivial group as
well; the family in the literature starts at n = 1, so this is an extra case
and not an error.

## 3. Target (b): `toolkit/words.py`, `ac.py`, `bfs.py`

### 3.1 Word arithmetic and linear algebra

`work/xcheck.py` (seed 20261104, 0 failures) compares the toolkit against my
engine on 400 random reduced words over ranks 2 and 3 for `reduce_word`,
`inverse`, `mul`, `conjugate`, `exp_sums`, `is_reduced` and the
`format_word`/`parse_word` round trip. It compares `det_int` and `is_unimodular`
against `sympy.Matrix.det` on 300 random matrices of size 1 to 4, including
singular ones, and `smith_elementary_divisors` against
`sympy.matrices.normalforms.smith_normal_form`. It compares `all_words` against
my independent enumeration for ranks 2 and 3 and lengths 0 to 5, and checks that
`count_words` agrees with the length of `all_words`.

### 3.2 The moves and the search

The same script applies 12 random moves to 200 random presentations, 2400 moves
in all, and requires my tuple and the toolkit's tuple to agree after every move.
It then compares whole breadth first searches, vertex sets and distances:

    rank 2, relator len 3, conj len 1: 744 vertices (toolkit 744)
    rank 2, relator len 4, conj len 1: 2280 vertices (toolkit 2280)
    rank 2, relator len 4, conj len 2: 2280 vertices (toolkit 2280)
    rank 3, relator len 2, conj len 1: 8112 vertices (toolkit 8112)
    rank 2, relator len 5, conj len 2: 31240 vertices (toolkit 31240)

The vertex sets are equal as sets, and the distances from the standard
presentation agree vertex by vertex. Agreement of the distances is the stronger
check, since a different exploration order would show up as a different distance
for some vertex.

The bounded box counts are also independent of the search code, and my
enumeration of the whole box gives:

    rank 2, relator length 4: box 25921, unimodular 2280
    rank 3, relator length 2: box 50653, unimodular 8112
    rank 2, relator length 5: box 235225, unimodular 32040

These are the numbers printed in `toolkit/runs/run1.txt`, `run3.txt`,
`run2.txt`, `run4.txt` and `run6.txt`. Each of them counts over the whole box,
so none of them depends on the order in which a search explores it. The same
script, `work/box_counts.py`, also prints the box at rank 2 with relator length
3, which is 2809 with 744 unimodular tuples.

Two soundness claims in the source are checkable and they hold. First, the
exponent sum matrix changes by left multiplication by an element of GL_n(Z)
under each move, so unimodularity and the Smith normal form are invariant; over
2400 random moves `work/invariants.py` found 0 violations, and a search with the
abelianisation filter switched off reaches only unimodular vertices at (2,4,2)
and (2,5,1). Second, the six move swap `mul 1 2, inv 1, mul 2 1, inv 2,
mul 1 2, inv 1` maps (r1, r2) to (r2, r1); my check over 300 random pairs found
0 mismatches, and `survey/computational/` relies on this path when it turns a
cyclic permutation of a relator into a certificate.

### 3.3 New inputs, and the recorded runs

`python3 toolkit/test_toolkit.py` prints `SUMMARY 144 passed, 0 failed,
0 skipped (10.19 s)`, which reproduces the Round 1 count. That suite is the
toolkit's own test, so the independent evidence for this target is the cross
check of sections 3.1 and 3.2.

I reran `toolkit/bfs.py --rank 2 --relator-len 4 --conj-len 2 --count-box
--box-gap --verify --find y,x` and obtained the recorded output of `run1.txt`
exactly: component 2280, box 25921 with 2280 passing the filter, (y, x) at
distance 6 with the recorded 6 move path, and every stored path replaying.

On a parameter set that is not in `toolkit/runs/`, rank 2 with relator length 3
and conjugator length 2, the toolkit reports 744 vertices, box 2809, 744
unimodular, 0 missed, and exports 744 certificates which it then replays with
0 failures. My independent replayer, which parses the file and uses only
`myfr.py`, replays the same 744 lines to their stated targets with 0 failures.
I also ran `python3 toolkit/runs/gap_check.py` and obtained component 31240,
filtered box 32040, 800 missed at length 5, none of the 800 still missed at
length 6, component 120296 at length 6 and radius 16, which is what the Round 1
report says.

### 3.4 Labelling notes

The move list of `ac.py` omits r_i -> r_j r_i and r_i -> r_i r_j^-1, and the
search of `bfs.py` restricts the conjugate to words of bounded length. Both
restrictions shrink the bounded ball, so every reachable statement the toolkit
makes is a statement about a subgraph, and the docstring of `bfs.py` says this
in as many words. `check_presentation` accepts the empty word as a relator,
which is harmless because such a presentation has determinant 0. The docstring
of `ac.py` gives the Akbulut and Kirby page range as 375-380; the correct range
is 375-390.

## 4. Target (c): the section 8 census

### 4.1 Rerunning the repository code

    $ cd survey/computational && python3 census.py 11 13        # 8 min
    ball of the standard presentation: total length <= 13, 6476104 tuples
    tuples in the ball with |exponent-sum determinant| != 1: 0
    canonical presentations with total length <= 11: 26182
      nontrivial, exponent-sum determinant not +-1 : 22485
      nontrivial, explicit finite quotient          : 0
      AC-trivial, certificate built and replayed    : 3697
      unresolved                                    : 0
    certificate lengths: min 7, max 37, mean 19.54

This reproduces `runs.txt` line by line, including the 36 entry depth histogram
of the ball. `python3 enum_check.py 13` (5 min 23 s) reproduces the canonical
list sizes 20, 104, 204, 1400 with `MATCH` on every row, the intermediate counts
6025, 16606, 46321, 129964, and the classification of the length 10, 11 and 12
lists (20 AC-trivial, 104 AC-trivial, and 184 AC-trivial with 4 nontrivial by an
A_5 witness and 16 unresolved). `python3 toolkit/runs/gap_check.py` reproduces
the 800 stragglers and their resolution at length 6. The two stored certificate
files replay, under `check_certs.py`, as recorded.

### 4.2 Independent reconstruction

I did not settle for rerunning their code. `work/ball.py` enumerates canonical
words from the definition (freely and cyclically reduced, one representative per
orbit under cyclic rotation and inversion) with its own code, then enumerates
canonical pairs, then builds its own ball of the standard presentation with the
move set of `census.py` (inversion, multiplication of one relator by the other,
conjugation by a generator or its inverse), and finally tests each presentation
for a variant inside its own ball. The output is:

    canonical words by length: 2, 4, 6, 13, 26, 66, 158, 418, 1098, 2968, 8054
    canonical presentations with total length <= 11: 26182
    nontrivial by exponent-sum determinant: 22485
    ball cap 13: 6476104 tuples (218 s, 1.96 GB resident)
    depth histogram identical to runs.txt in all 36 layers
    ball tuples with |det| != 1: 0
    reached inside the ball: 3697, not reached: 0
    certificates rebuilt from the presented tuple to the standard tuple:
      3697 checked, 0 failed

The per length counts from the same script are 83, 522, 1349, 3551, 9576,
26182 at total length 5, 7, 8, 9, 10, 11 and the determinant splits are 66, 433,
1160, 3002, 8419, 22485. This is the table of `survey/computational.md` section
8.5 in full, row by row. The column my code does not compute is the finite
quotient column, and both reruns of `census.py` give 0 there. The certificate files were replayed by `work/census_replay.py`,
which parses the `r1 r2 | i j | moves` format and uses only `myfr.py`:

    certs_r10_c13.txt: 1157 certificates replay to (a,b), 0 fail, longest 30
    certs_r8_c11.txt:  189 certificates replay to (a,b), 0 fail, longest 24

I also verified the claim of section 8.4 about the four length 12
presentations with GAP: all four have order 120, are perfect, and have trivial
abelian invariants, while <a,b | a^2, b^3, (ab)^5> has order 60. This confirms
the finding of section 9 item 4 that the identification "L_2(5), the unique
perfect group of order 120" cannot be right, and it settles the order as 120.

### 4.3 What the census assumes

The enumeration leaves out presentations with an empty relator. Such a
presentation has a zero row in the exponent sum matrix, so its determinant is 0,
and its group is infinite, so the exclusion cannot hide a presentation of the
trivial group. The claim that every presentation can be taken cyclically
reduced is correct because cyclic reduction is conjugation by a prefix and
shortens the relator. Both my enumeration and theirs use these conventions, so
my agreement with their numbers does not test them independently; I checked
them by the argument just given.

### 4.4 The gap

`census.py 11 13` was run without a certificate file, so the 3697 certificates
of the length 11 branch are not on disk; only the length 10 file is stored. The
numbers are reproducible in 8 minutes and my own reconstruction supplied
certificates for all 3697, so this is a documentation gap and not an error. A
future round should store the file.

## 5. Target (d): `survey/complexity.md` against Bridson's LaTeX

### 5.1 The quotations are accurate

Every constant the survey quotes from the paper matches the source, and so do
the statements the survey's argument depends on, including the comparison of
areas between the two presentations in the row for `l:noHat`:

| statement | source |
| --- | --- |
| Theorem A: k >= 4, relator length at most 24(n+1), bound Delta(floor(log_2 n)) with Delta(0)=2, Delta(m+1)=2^Delta(m) | `thmA`, line 228 |
| introduction: log area*_P(w) <= AC_*(P_w) + 1 | `t:If`, line 351 |
| body: log area*_P(w) <= 3 AC_*(P_w) | `t:if`, line 750 |
| area_{P_w} <= area_{tilde P_w} <= 3 area_{P_w} | `l:noHat`, line 829 |
| area_{P_w}(a_0) >= (1/3) area*_P(w) | `c:area`, line 875 |
| the proof chain ">= log area* - log 3", then "replace log 3 by 1" | lines 882 to 889 |
| two sided bound with 2 AC_*(bar P) + 2 area* + 2 sum |r|_0 | `t:main`, line 941 |
| seed words: |w_n| <= 12n, area* >= Delta_k(floor(log_2 n)) | `thmS`, line 1336 |
| V_0 = x, V_m = t V_{m-1} t^-1 x t V_{m-1}^-1 t^-1 | `d:w_n`, line 1356 |
| Corollary A: n -> AC_*(P_n) is simeq Delta(floor(log_2 n)) | `corA`, line 401 |
| t:hint: k >= 4, P_n in Lambda(Cn), not connectable inside Lambda(Delta(floor(log_2 n))) | line 1683 |
| the explicit example of section 7.4 with the bound 10^10000 | line 1729 |

The survey's remark that the logarithms are natural is also right, because the
source uses F_m < e^m. A change of base would shift the additive constants by a
fixed amount and would leave the tower bounds unchanged.

The explicit example deserves its own line because I recomputed it rather than
trusting the script. With my own free group arithmetic and the commutator
[a,b] = a b a^-1 b^-1 the four relators have lengths 9, 9, 407, 407, so the
total is 832. The 407 comes from a cancellation that a hand count is likely to
miss: writing X_3 for the three times nested inner bracket, X_3 ends in a^-1
and X_3^-1 begins with a, so the outer commutator [a, X_3] has length
2|X_3| + 2 - 2 = 404 and the relator has length 407. My first count of 409 was
wrong and the survey's 407 is right.

### 5.2 First error: the printed Fibonacci bound is false at m = 1

`complexity.md` section 2.2 quotes Bridson's Lemma `l:fib` (line 687: if P can be
trivialised by m dihedral AC moves then area_P(a_i) <= fib_m) and says that the
printed statement "is true but not sharp". The printed statement is false.
Counterexample with m = 1: let P = <x, y | x y, y>. The single dihedral move
r_1 -> r_1 r_2^-1 turns it into (x, y), so P is trivialised by one move. In P
one has x = (xy) y^-1, a product of two conjugates of relators, so area_P(x) is
at most 2. It is at least 2 because a single conjugate of a relator has exponent
sum (1,1) for x y or (0,1) for y, and neither is (1,0). Hence area_P(x) = 2,
while fib_1 = 1. The failure does not depend on the indexing convention, because
every convention has fib_1 = 1.

The survey's positive finding survives and I verified it independently. A dynamic
programme over the counter vectors, exact and not random, gives the maximum of
the conjugate counter after m moves as 1, 2, 3, 5, 8, 13, 21, 34, 55, 89 for
m = 0 to 9 and for relator counts 2, 3 and 4, that is max = fib_{m+2}. So the
sharp statement is area_P(a_i) <= fib_{m+2}, and the printed bound is off by two
indices, as the survey says.

The consequence the survey draws from this is the one that needs correcting. It
concludes that "the version with constant 3 is a correct but weaker
restatement", and that "anyone quoting a constant should quote 1". The constant
1 form is the one whose derivation uses the false bound. Substituting the true
bound fib_{m+2} < e^{m+2} into the same chain of the proof of `t:if` gives
log area*_P(w) < AC_*(P_w) + 2 + log 3, so this argument yields the additive
constant 3.1 and not the additive constant 1. The body's multiplicative form
log area*_P(w) <= 3 AC_*(P_w) follows from the additive form as soon as
AC_*(P_w) >= 2, and the cases of smaller move count are separate small checks,
so that form is not in danger. The recommendation should be reversed: quote the
body's constant 3, and do not quote the additive constant 1 of the introduction
as a consequence of this proof. Bridson's Theorem A and its tower lower bounds
are untouched by this, because a shift of 2 in the additive constant is
absorbed by Delta.

### 5.3 Second error: the seed relator has length 9, not 8

Section 3.2 derives the constant 24 by saying that the seed relator
(t x t^-1) x (t x t^-1)^-1 x^-2 has length 8, and then computes
16 + 2(12n + 3) = 24n + 22 <= 24(n+1). The relator, as written in the source at
line 1336, is t x t^-1 x t x^-1 t^-1 x^-2 with no cancellation available, so its
length is 9. The correct bookkeeping is 2*9 + 2(12n + 3) = 24n + 24 = 24(n+1),
which makes the printed constant 24 exactly tight at |w| = 12n. With Bridson's
sharper |w_n| <= 12n - 8 from Lemma `wnL` there is slack:
2*9 + 2(12n - 8 + 3) = 24n + 8 <= 24(n+1). The conclusion of the passage, that
24 is a legitimate constant, stands, and the phrase "not slack by more than 2"
should read "exactly tight at the stated bound". The check
`PASS Theorem A constant: 2*8 + 2*(12n+3) = ...` in
`survey/complexity_check.py` verifies the arithmetic with the wrong relator
length, so it does not catch this; replacing 8 by 9 makes every one of those
lines an equality rather than a strict inequality, which still passes.

## 6. What I could not verify

1. I did not verify the Havas and Ramsay printed level counts from the paper
   itself; I verified that my own implementation and the repository code both
   produce 1, 12, 101, 782, 5906, 44048, 326200 from the same start tuple, and
   took the published sequence on the survey's word.
2. I did not verify Bridson's area and seed estimates, only his constants and
   the statement of his lemmas. The correctness of Theorem A itself rests on the
   sections of his paper that I did not check line by line.
3. I did not run the 16 length 12 presentations through `deep_search.py`
   (`survey/computational.md` section 8.7); that bounded negative is unchecked
   here.
4. I did not verify the claim that the finite quotient branch (S_3, D_8, Q_8,
   A_4, S_4, A_5) coincides with the determinant branch in every row. My
   reconstruction shows that no determinant passing presentation at length at
   most 11 is outside the ball, which is consistent with the branch never being
   needed.
5. The claim in `survey/computational.md` section 8.4 that the four length 12
   presentations of order 120 match "the paper's count of four presentations of
   order 120" is a claim about the contents of Havas and Ramsay 2003; I
   confirmed the order 120 independently with GAP and did not read the paper.

## 7. Exact commands

Run from the repository root. I set `PYTHONDONTWRITEBYTECODE=1` in my own runs
so that no byte code file is written next to another member's sources. `MY` is
the absolute path of `.ultramath/smw2i9i4j/m10`.

    lean directions/ak-status/ak_trivial.lean                      # exit 0, 11 axiom lines
    lean $MY/work/ak_def_check.lean                                # exit 0, 3 axiom lines
    gap -q $MY/work/ak_gap.g                                       # n = 0,1,2 index 1
    gap -q $MY/work/ak_gap2.g                                      # n = 3,4,5 index 1
    gap -q $MY/work/orders_gap.g                                   # four orders 120, A5 order 60
    python3 toolkit/test_toolkit.py                                 # 144 passed
    python3 toolkit/bfs.py --rank 2 --relator-len 4 --conj-len 2 --count-box --box-gap --verify --find y,x
    python3 toolkit/bfs.py --rank 2 --relator-len 3 --conj-len 2 --count-box --box-gap \
        --export $MY/out/certs_r2l3.txt --verify --find y,x
    python3 toolkit/bfs.py --rank 2 --replay $MY/out/certs_r2l3.txt
    python3 toolkit/runs/gap_check.py
    (cd survey/computational && python3 census.py 11 13)           # 8 min
    (cd survey/computational && python3 enum_check.py 13)          # 5 min 23 s
    (cd survey/computational && python3 check_certs.py certs_r10_c13.txt)   # 1157 ok
    (cd survey/computational && python3 check_certs.py certs_r8_c11.txt)    # 189 ok
    python3 $MY/work/xcheck.py                                     # 0 failures
    python3 $MY/work/box_counts.py                                 # table of section 4.2
    python3 $MY/work/invariants.py                                 # 0 violations, 0 mismatches
    python3 $MY/work/levels.py                                     # 1, 12, 101, 782, 5906, 44048, 326200
    python3 $MY/work/replay_certs.py $MY/out/certs_r2l3.txt 2       # 744 ok
    python3 $MY/work/census_replay.py survey/computational/certs_r10_c13.txt   # 1157 ok
    python3 $MY/work/census_replay.py survey/computational/certs_r8_c11.txt    # 189 ok
    python3 $MY/work/ball.py 11 13 4000                            # 218 s, 1.96 GB, 3697 certificates
    python3 $MY/work/bridson_consts.py                             # seed 9, example 9,9,407,407, fib table
    python3 survey/complexity_check.py                             # all checks passed (their script)

The independent engine and its drivers live in `$MY/work/`. The saved outputs
quoted above are `$MY/out/ak_trivial_lean.txt`, `$MY/out/run1_rerun.txt`,
`$MY/out/gap_check_rerun.txt`, `$MY/out/census_L11_cap13.txt`,
`$MY/out/enum_check_13.txt`, `$MY/out/ball_L11_cap13_all.txt` and
`$MY/out/certs_r2l3.txt`.
