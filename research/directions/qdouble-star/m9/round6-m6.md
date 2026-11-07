# Metzler's pair: an explicit 44-move Q\*\*-certificate, and the family behind it

Round 6, direction I6 ("the Metzler stopping point"). Member m6.

Labels used below, following the campaign's convention: **[Verified]** a
machine check anyone can rerun with the stated command; **[Computed]** a
number produced by a stated run; **[Argument]** a proof written out, not
machine-checked; **[Quoted]** a claim taken from a source, not replayed;
**[Open]** not settled here.

Nothing in this file is a claim for or against the Andrews-Curtis conjecture.

## 0. Summary

1. **[Verified] Barmak's quotation of Metzler's example is now replayed.** There
   is an explicit certificate of **44 Q\*\*-moves** from
   $\langle x,y \mid x^5,\ y^5,\ [x,y]\rangle$ to
   $\langle x,y \mid x^5,\ y^5,\ [x^2,y]\rangle$, with every move one of
   Barmak's (i) to (vi). Five independent implementations replay it and reach
   the stated endpoint:

   | implementation | what it is | result |
   | --- | --- | --- |
   | `metzler_gen.py` | this direction's own engine, written from the definitions | 44 moves, endpoint reached |
   | `directions/qdouble-star/check_qstar.py` | round-3/4 independent replayer (shares no code with the engine) | `OK ... (44 moves)`, 0 failures |
   | `directions/qdouble-star/m9/qverify.py` | the round-4 direction's own replayer, a third Python implementation | `OK ... 44 moves`, 0 failures |
   | `directions/certificate-algebra/` engine | round-5 move calculus, written for another purpose | 44 moves replayed, 0 bad moves |
   | GAP 4.14 | free-group arithmetic inside GAP | `OK replayed 3 relators, rank 2 (44 moves by GAP arithmetic)` |

   Along the way the certificate also settles item 5 of the round-4 draft's
   limits list: GAP confirms both presentations present the group of **order
   25, abelian** ($\mathbb{Z}/5 \times \mathbb{Z}/5$).

2. **[Argument, with 14 instances Verified] The same recipe gives a family.**
   For every odd $k\ge 3$, every $m\ge 1$ and every divisor $t$ of $k-1$ with
   $j=(k-1)/t$, the
   presentations $\langle x,y \mid x^k, y^m, [x,y]\rangle$ and
   $\langle x,y \mid x^k, y^m, [x^j,y]\rangle$ are Q\*\*-equivalent. Fourteen
   instances ($k=5,7,9,11,13$) are built and replayed, 44 to 64 moves each,
   all reaching their stated endpoint.

3. **[Argument] The round-4 stopping point is explained and removed.** Section 4
   proves two lemmas and one recipe:
   * a single Q-move can multiply a relator only by a conjugate of a
     **different** relator (Lemma 1), which is why
     $[x^2,y]=[x,y]\cdot x[x,y]x^{-1}$ is out of reach of an isolated relator
     move;
   * consequently no Q-certificate from Metzler's first presentation to the
     second can keep $x^5$ and $y^5$ untouched (Lemma 2, proved with a free
     product argument);
   * the missing ingredient is a **generalised prolongation** (a new generator
     $a$ with the defining relator $a x^{-t}$, two moves in Q\*\*) together
     with a **closed-form telescoping identity** that pushes the defining
     relator into any other relator (Lemma 3). What round 4 recorded as "the
     product therefore has to be found by a genuine search" has a closed form:
     one conjugate of the defining relator per occurrence of the defined
     generator.

4. **[Quoted] Q\*-inequivalence is not established here.** Barmak states that
   Metzler's pair is Q\*-inequivalent, citing Metzler 1976. This work replays
   only the Q\*\* half. Nothing here says anything about Q\*-inequivalence, and
   nothing here bears on the Andrews-Curtis conjecture.

## 1. The statement and its source

Barmak, *An exotic presentation of $\mathbb{Z}\times\mathbb{Z}$ and the
Andrews–Curtis conjecture*, Algebr. Geom. Topol. **25** (2025) 345–355, DOI
`10.2140/agt.2025.25.345`, Section 1 (bibliographic record and abstract checked
live at `https://msp.org/agt/2025/25-1/p13.xhtml`, published 5 March 2025):

> "In [19], Metzler gives an example of a different nature. He shows that the
> presentations $\langle x,y \mid x^5, y^5, [x,y]\rangle$ and
> $\langle x,y \mid x^5, y^5, [x^2,y]\rangle$ are Q\*\*-equivalent and not
> Q\*-equivalent. In this case the normal closures of both sets of relators
> coincide."

Two caveats about the quotation. First, the PDF's text layer drops the
asterisks ("Q -equivalent" twice); the campaign recorded the same artefact
(survey/q-transformations.md section 5, round-5 correction note), and the
reading above is the one the surrounding text forces: the first occurrence is a
statement of equivalence, the second a statement of inequivalence. Second,
Barmak gives no certificate; the round-4 draft
(`directions/qdouble-star/m9/round4-m9.md`, section 6) recorded exactly this as
its open item:

> "My canonical search does not find it within 20,000 expansions at cap 30 and
> rank 3 (647,837 states pushed, 881 MB peak), and the round-3 engine does not
> find it within 30,000 expansions at cap 30. So Barmak's Q\*\*-equivalence of
> Metzler's pair remains quoted and not replayed. **[bounded negative]**"

and named two reasons: the length of the intermediates, and the conjugator
length ("Both engines generate conjugators of length at most 1 or 2 ... The
certificates need much longer ones").

The move set used here is Barmak's Section 1 verbatim, as implemented by the
campaign's engine and its independent replayer:

```
(i)   r_j -> r_j r_i  (i != j)      r_j -> r_j^{-1}      r_j -> g r_j g^{-1}
(iv)  r_j -> phi(r_j) for an automorphism phi of F_n
(v)   add a generator x_{n+1} with relator x_{n+1}
(vi)  the inverse of (v), when possible
```

`lmul` ($r_j \to r_i r_j$) is the derived form the campaign uses (Hog-Angeloni
and Metzler (26)c; derivable from (i) and (iii), see `qstar.py`'s header). Left
multiplication appears 4 times in the certificate; the round-5 certificate
algebra classifies it as a Q-move, so it costs nothing. The two moves that take
the certificate outside Q\* are the prolongation and its inverse; whether the
pair is Q\*-equivalent is a separate question, and Barmak's answer ("not
Q\*-equivalent", quoting Metzler) is not reproved here.

## 2. The certificate

`metzler_pair_qstar_gap.cert` (44 moves, sha256
`10566d02f2dec919695414e39bb9c4c3045599f7d85a123e0eb0edbef4d9bd63`):

```
start 2 xxxxx;yyyyy;xyXY
end   2 xxxxx;yyyyy;xxyXXY
```

i.e. $\langle x,y \mid x^5, y^5, xyx^{-1}y^{-1}\rangle \to
\langle x,y \mid x^5, y^5, x^2yx^{-2}y^{-1}\rangle$. Move census: `prolong` 1,
`nijinv` 5, `nij` 1, `njiinv` 1, `neg` 1, `conj` 13, `mul` 8, `lmul` 4,
`inv` 9, `delete` 1. The
longest relator at any intermediate state is 15; the peak *total* relator
length along the path is 26 (the start has 14); the conjugating words have
lengths 2, 2, 2, 3, 3, 4, 4, 4, 4, 4, 4, 5, 6.

The seven stages, in the trace `metzler_trace.txt` (produced by
`python3 metzler_gen.py --verbose`):

1. **Generalised prolongation** (moves 1–3). Add $a$ freely, then two Nielsen
   moves $a \to a x^{-1}$ give the relator $a x^{-2}$. This is Hog-Angeloni and
   Metzler's generalised prolongation (their (31), quoted in
   survey/q-transformations.md section 4), which Q\*\* has because (v) plus
   (iv) gives it in two moves. In the presented group $a = x^2$.
2. **$x^5 \to x a^2$** (moves 4–9). Two right multiplications by conjugates of
   $a x^{-2}$:
   $$x^5 \cdot (x^{-4} a x^2) \cdot (x^{-2} a) = x a^2 .$$
   Every factor is a conjugate of a *different* relator, which is what a Q-move
   needs (Lemma 1).
3. **$a x^{-2} \to a^5$** (moves 10–15) and **$[x,y] \to [a^{-2},y]$** (moves
   16–21), both by left multiplications by conjugates of $x a^2$ only, i.e.
   the substitution $x \mapsto a^{-2}$ carried out relator by relator
   (Lemma 3). After this the relators are $(x a^2,\ y^5,\ [a^{-2},y],\ a^5)$
   and $x$ occurs in exactly one relator.
4. **Eliminating $x$** (moves 22–24). Two Nielsen moves $x \to x a^{-2}$ turn
   $x a^2$ into the single letter $x$; since $x$ occurs nowhere else, (vi)
   deletes the generator. Rank 2 remains, with relators
   $(y^5,\ [a^{-2},y],\ a^5)$.
5. **$[a^{-2},y] \to [a^2,y]$** (moves 25–26). Invert and conjugate by $a^2$:
   $[a^2,y] = a^2\,[a^{-2},y]^{-1} a^{-2}$. Two Q-moves.
6. **Relabelling $a \to x$** (moves 27–30): the transposition of the two
   generators, written as four elementary Nielsen moves
   (`neg 1`, `nijinv 1 2`, `nij 2 1`, `njiinv 1 2`) rather than as the single
   automorphism `swap 1 2`. Both are Barmak's (iv); the elementary form is
   used because `qverify.py` rejects any `swap` move (section 9). Checked by
   hand: the images compose to $x_1 \mapsto x_2$, $x_2 \mapsto x_1$.
7. **Relator order** (moves 31–44): two relator permutations by Q-moves (each
   six moves, up to signs, then inversions to make the signs right).

The point of stage 2 and 3 is that both are *closed forms*: the multiplier that
turns $V$ into its image under $x \mapsto a^{-2}$ is written down in Lemma 3
with one factor per occurrence of $x$ in $V$, never a search.

## 3. Verification

All commands were run from the repository root; `$M` is this directory
`.ultramath/smw3ow2dp/m6`.

**3.1 this direction's engine.**

```
$ python3 metzler_gen.py
start  2 xxxxx;yyyyy;xyXY
end    2 xxxxx;yyyyy;xxyXXY
moves  44   conj:13 delete:1 inv:9 lmul:4 mul:8 neg:1 nij:1 nijinv:5 njiinv:1 prolong:1
written metzler_pair_qstar_gap.cert
longest relator at any intermediate state: 15
```

The generator asserts, at every stage, the exact expected relator tuple, and
`main` replays the emitted move list a second time from the emitted file.

**3.2 the campaign's independent Q\*\* replayer** (`check_qstar.py` reimplements
free reduction, the substitutions, the Q-moves, prolongation and the freeness
condition of a deletion from the definitions, sharing no code with the engine):

```
$ cd directions/qdouble-star
$ python3 check_qstar.py $M/metzler_pair_qstar_gap.cert
OK     .../metzler_pair_qstar_gap.cert: 2 xxxxx;yyyyy;xxyXXY (44 moves)
certificates checked = 1, failures = 0
```

**3.2b the qdouble-star direction's own replayer** (`directions/qdouble-star/m9/qverify.py`,
written in round 4, a third Python implementation sharing no code with the
other two):

```
$ cd directions/qdouble-star/m9
$ python3 qverify.py $M/metzler_pair_qstar_gap.cert
OK   .../metzler_pair_qstar_gap.cert  44 moves  ->  <x,y | xxxxx, yyyyy, xxyXXY>
checked 1, failures 0
```

**3.3 the round-5 certificate algebra** (`directions/certificate-algebra`,
written in round 5 to replay every family in the repository; it reads the m9
file format as one of its families):

```
$ python3 verify_with_certalg.py
certificate     : metzler_pair_qstar_gap.cert
moves           : 44
move classes    : Q 34, Q*-only 8, Q**-only 2
peak total length of the path: 26
replayed end    : 2 aaaaa;bbbbb;aabAAB
declared end    : 2 aaaaa;bbbbb;aabAAB
match           : True
```

The 8 Q\*-only moves are the Nielsen substitutions; the 2 Q\*\*-only moves are
the prolongation and the deletion. The other 34 moves are Q-moves.

**3.4 GAP**, whose free-group arithmetic is independent of every Python engine
here (`gapgen.py` translates the move list into a GAP script and runs
`gap -q`):

```
$ python3 gapgen.py
Start presentation: order 25, abelian true
OK   replayed 3 relators, rank 2 (44 moves by GAP arithmetic)
End presentation: order 25, abelian true
same group order and both abelian: true
```

This also answers item 5 of the round-4 draft's uncertainty list: the group of
both presentations is of order 25 and abelian, so $\mathbb{Z}/5\times
\mathbb{Z}/5$ as the round-4 draft's Section 6 assumed.

## 4. Why the round-4 search stopped, and what supplies the missing move

### Lemma 1 (a Q-move never self-multiplies). **[Argument]**

Let a move of type (i)–(iii) change the relator $r_i$ and leave every other
relator fixed. Then the new relator is $r_i^{-1}$, or $g r_i g^{-1}$, or
$r_i r_j^{\pm 1}$, or $r_j^{\pm 1} r_i$ with $j \neq i$. In particular the word
appended to $r_i$ is always a conjugate of a **different** relator. So
$r_i \to r_i\,(w r_i w^{-1})$ is not a Q-move, and in Metzler's pair the
identity
$$[x^2,y] \;=\; (x\,[x,y]\,x^{-1})\cdot [x,y]$$
cannot be produced by a single relator move on $[x,y]$ while $x^5$ and $y^5$
sit still. This is exactly the structural remark of
`directions/qdouble-star/qdouble-star.md` section 6, now with a proof.

### Lemma 2 (a Q-certificate must touch $x^5$ or $y^5$). **[Argument]**

*Claim.* There is no Q-move sequence from $(x^5, y^5, [x,y])$ to
$(x^5, y^5, [x^2,y])$ in which the first two relators are never changed.

*Proof.* Suppose the first two relators are $x^5$ and $y^5$ throughout and put
$K = \mathrm{ncl}\{x^5,y^5\}$, $r = [x,y]$. We show by induction on the length
of the sequence that the third relator always has the form $u\,w r^{\pm1}
w^{-1}$ with $u \in K$ and $w \in F_2$:

* initially $r = 1\cdot 1\,r\,1^{-1}$;
* inversion: with $A = w r^{\pm1}w^{-1}$, $(uA)^{-1} = A^{-1}u^{-1} =
  (A^{-1}u^{-1}A)\cdot A$, and $A^{-1}u^{-1}A \in K$ because $K$ is normal and
  $A^{-1}$ is a conjugate of $r^{\mp1}$; so the form is preserved with
  $w' = w$ and the other sign;
* conjugation by $g$: $g\,u w r^{\pm1}w^{-1}g^{-1} = (gug^{-1})\,(gw) r^{\pm1}
  (gw)^{-1}$ with $gug^{-1} \in K$;
* multiplication by $x^{\pm5}$ or $y^{\pm5}$ (the only relators available, by
  assumption): the multiplier lies in $K$, and $K$ is normal.

If the endpoint were $(x^5,y^5,[x^2,y])$, then in $F_2/K = \mathbb{Z}/5 *
\mathbb{Z}/5$ we would have $[x^2,y] = w\,[x,y]^{\pm1}\,w^{-1}$, i.e.
$[x^2,y]$ conjugate to $[x,y]^{\pm1}$. But $[x^2,y] = x^2yx^{-2}y^{-1}$ and
$[x,y]^{\pm1}$ are cyclically reduced words in the free product
$\mathbb{Z}/5 * \mathbb{Z}/5$, and conjugacy of cyclically reduced words in a
free product is cyclic permutation, so the multisets of their syllables agree.
Those multisets are $\{x^2,\ y,\ x^{-2},\ y^{-1}\}$ and
$\{x,\ y,\ x^{-1},\ y^{-1}\}$, and they differ because $x^2 \notin
\{x,x^{-1}\}$ in $\mathbb{Z}/5$. Contradiction. $\square$

So any Q-certificate has to modify $x^5$ or $y^5$ on the way; a search that
aims at the target tuple with the first two relators held fixed is doomed, and
the round-4 drafts' "search for the third relator" heuristic is excluded by a
theorem, not by a budget.

### Lemma 3 (the telescoping identity: substitution through a defining relator). **[Argument]**

Let $R = x\cdot W$ be a relator with $x$ not occurring in $W$, and let
$\sigma$ be the endomorphism of $F$ with $\sigma(x) = W^{-1}$ and $\sigma$
the identity on the other generators. Then for every word $V$ the relator $V$
can be replaced by $\sigma(V)$ using Q-moves alone, each of them a
multiplication by a conjugate of $R$.

*Proof.* Induct on the length of $V$. For $V = uL$ with $L$ a letter,
$$V\,\sigma(V)^{-1} \;=\; \big(u\,(L\,\sigma(L)^{-1})\,u^{-1}\big)\cdot
\big(u\,\sigma(u)^{-1}\big).$$
If $L \neq x^{\pm1}$ then $\sigma(L) = L$ and the first factor is empty. If
$L = x$ then $L\sigma(L)^{-1} = xW = R$. If $L = x^{-1}$ then
$L\sigma(L)^{-1} = x^{-1}W^{-1}$, and $\mathrm{conj}_{W}(R^{-1}) =
W\,(W^{-1}x^{-1})\,W^{-1} = x^{-1}W^{-1}$, so it is a conjugate of $R^{-1}$.
So each factor is a conjugate of $R^{\pm1}$, and
$u\sigma(u)^{-1}$ is a product of such factors by induction. Multiplying $V$
by the inverse of the whole product gives $\sigma(V)$; the inverse of a
product of conjugates of $R^{\pm1}$ is again one, so every step is a legal Q
multiplication by a conjugate of a different relator. $\square$

This is the constructive content of "generalised prolongation" used backwards,
and it is exactly the step the round-4 draft identified as unavailable:

> "then $x$ has to be eliminated, which needs the consequence $x a^2$ ... The
> relators available are $x^5$ and $a x^{-2}$, and to obtain $x a^2$ from them
> by Q-moves one has to multiply $x^5$ by the right product of conjugates of
> $a x^{-2}$ ... The product therefore has to be found by a genuine search."

There is no search: with $R = x a^2$, Lemma 3 gives the product immediately.
For Metzler's pair the two products used are $x^5 \to x a^2$ (from
$x^{-(k-1)}a^{(k-1)/2}$ with $k=5$, i.e. $x^{-4}a^2$) and the substitution of
$x \mapsto a^{-2}$ into $a x^{-2}$ and $[x,y]$.

The full elimination recipe, which is what the certificate uses, is three
lines:

1. generalised prolongation: add $a$ with relator $a x^{-t}$ — two moves
   (prolong, then $t$ Nielsen moves $a \to a x^{-1}$);
2. use Lemma 3 to push the defining relator into every other relator, so that
   $x$ occurs only in a relator of the form $x\cdot W$;
3. two Nielsen moves $x \to x W^{-1}$ turn that relator into the letter $x$,
   and (vi) deletes the generator.

Step 3 is the point at which Q\*\* is really needed: Q moves cannot delete a
generator at all, and Q\* moves cannot add one.

### Why the round-4 runs missed it: three concrete reasons. **[Computed]**

1. *No derived move for the substitution.* The defining relator $a x^{-2}$ is
   only two moves from the start, so both round-4 engines could reach it; what
   neither has is a move that *uses* it. Lemma 3's substitution is a detour of
   two to six moves per occurrence of $x$, and the search had to discover each
   detour move by move.
2. *The conjugations.* The round-3 engine (`qstar.py`, `conj_len = 2`) offers
   conjugating words of length at most 2 plus the current relators; **7 of the
   certificate's 13 conjugating words are outside that list** (lengths 3 and 4,
   not equal to any relator of the state they occur in). The round-4 canonical
   engine (`directions/qdouble-star/m9/cfsearch.py`) generates no conjugation
   move at all: its successor set is mul, lmul, neg, nij, nji, nijinv, njiinv,
   swap, prolong, delete, and conjugation is replaced by canonicalising each
   relator (cyclic reduction), which can only conjugate by a word that
   shortens it. The certificate's conjugations shorten nothing: they fix the
   position at which the inserted block lands inside the relator, which is what
   makes the multiplier a conjugate of the whole relator rather than material
   appended at its end. Lemma 3 says which conjugators to use — prefixes of the
   relator being substituted, times powers of the defined generator — a
   structured list of at most $|V|$ words per relator, not a blind one.
3. *The depth.* The certificate is 44 moves long, with peak total relator
   length 26. A best-first expansion in total length with 20,000 expansions
   (the round-4 budget) covers a tiny fraction of the depth-44 frontier, so no
   budget of that size reaches it whatever the move set.

### A correction to the round-4 draft. **[Computed]**

Section 6 of `directions/qdouble-star/m9/round4-m9.md` says that finding the
product of conjugates of $a x^{-2}$ that produces $x a^2$ "is a small word
problem in a group of order 25". The group in which that word problem lives is
$\langle x,a \mid x^5,\ a x^{-2}\rangle$, and since the second relator defines
$a = x^2$ it is $\langle x \mid x^5\rangle = \mathbb{Z}/5$: **order 5, not 25**.
(25 is the order of Metzler's group, $\mathbb{Z}/5\times\mathbb{Z}/5$, which is
the quotient after the third relator is added — it is not the group that
decides whether $x a^2$ is a product of conjugates of the first two relators.)
The correction does not change the draft's conclusion: its bounded negative
stands, and the product is settled here in closed form for every exponent.

The same section's item 5 is now answered: GAP gives order 25 and abelian for
both of Metzler's presentations (section 3.4).

## 5. The family

The recipe has nothing specific to $k=5$ except the arithmetic $k-1 = 2\cdot 2$.
Let $k$ be odd, $m \ge 1$, $t \mid k-1$ and $j = (k-1)/t$. Then
$$\langle x,y \mid x^k,\ y^m,\ [x,y]\rangle \;\sim_{Q^{**}}\;
  \langle x,y \mid x^k,\ y^m,\ [x^j,y]\rangle .$$

*Proof sketch.* Generalised-prolong $a = x^t$ (relator $a x^{-t}$). Then
$x^k = x\,(x^t)^j$, so
$$x^k \cdot \big(x^{-tj}a^j\big)^{-1} = x\,(x^t)^j x^{-tj} a^j = x a^j,$$
and $x^{-tj}a^j$ is a product of $j$ conjugates of $a x^{-t}$ (each
$x^{-t}a$ conjugated by a power of $x^{-t}$; the file's `power_identity`
function builds the list and multiplies it out to check it). Then Lemma 3 with
the defining relator $x a^j$ rewrites $a x^{-t} \mapsto a^{1+jt} = a^k$ and
$[x,y] \mapsto [a^{-j},y]$; the Nielsen move $x \to x a^{-j}$ makes $x a^j$
into $x$; (vi) deletes $x$; what is left is $(y^m, [a^{-j},y], a^k)$, and
$[a^j,y] = a^j [a^{-j},y]^{-1}a^{-j}$ is two Q-moves away. Relabel $a \to x$

[Coordinator note, 6 November 2026 (round 8, from the symbolic-parameter
formalization of member m10 of swarm smw4i604a; kernel- and twin-verified):
the clause "$[x,y] \mapsto [a^{-j},y]$" is a statement about the substitution
$\sigma$, and it is NOT what the move-level realization produces. The kernel
recipe's phase-4 block (eight moves using $R = x a^j$ as the scratch relator)
produces $SL_1 = a^{-j} y x a^j x^{-1} y^{-1}$, which still contains $x$
(the AC8 lemmas slot1_clean, lift_s02_slot1, lift_ph_slot1, endgame2). The
recipe survives because the later phases are insensitive to the $x$: the
Nielsen substitution fixes $SL_1$, and the deletion sends it to
$[x^{-j},y]$, which the final conjugate-and-invert turns into $[x^j,y]$. The
member's own hand derivation had predicted the x-free word; the kernel and
the Python twin both refute it. The certificate is unaffected — this corrects
the sketch's account of the intermediate state only.]

[Coordinator note, 6 November 2026 (round 7, from the Lean formalization of
member m10 of swarm smw48or9f, accepted; coordinator-rerun): the displayed
identity above has the inverse in the wrong place. Since
$(x^{-tj}a^j)^{-1} = a^{-j}x^{tj}$, the left-hand side
$x^k\cdot(x^{-tj}a^j)^{-1}$ is $x^{1+tj}a^{-j}x^{tj}$, which is not $x\,a^j$;
the identity that holds, and that the certificate files implement, is
$$x^{1+tj}\cdot x^{-tj}a^j = x\,a^j \qquad(k = 1+tj),$$
verified by exact free-group arithmetic in 36 of 36 cases $1\le t,j\le 6$ by
the member and independently by the coordinator (the printed form holds in 0
of 36), and stated for all $t,j$ as the kernel theorem `powerProd_cert` of
`toolkit/lean/AC7.lean`. The error is in this proof sketch only: every
certificate file replays (five Python implementations and the Lean kernel
agree on all 15), so the family's conclusions stand; the kernel theorem
`conjProd_of_subst` formalizes Lemma 3 and `powerProd_spec` the closed form of
the conjugate product.]
and permute relators. $\square$

**[Verified]** 14 instances built by `metzler_family.py` and replayed by
`check_qstar.py` (0 failures):

| $k$ | $t$ | $j$ | $m$ | moves | peak relator length |
| --- | --- | --- | --- | --- | --- |
| 5 | 2 | 2 | 5 | 44 | 15 | (Metzler's pair) |
| 5 | 1 | 4 | 5 | 48 | 23 |
| 5 | 4 | 1 | 3 | 48 | 11 |
| 7 | 3 | 2 | 5 | 48 | 17 |
| 7 | 2 | 3 | 2 | 48 | 16 |
| 7 | 1 | 6 | 4 | 56 | 30 |
| 7 | 6 | 1 | 1 | 56 | 14 |
| 9 | 2 | 4 | 5 | 52 | 23 |
| 9 | 4 | 2 | 3 | 52 | 18 |
| 9 | 8 | 1 | 2 | 64 | 18 |
| 11 | 5 | 2 | 5 | 56 | 22 |
| 11 | 2 | 5 | 5 | 56 | 27 |
| 13 | 2 | 6 | 5 | 60 | 31 |
| 13 | 4 | 3 | 7 | 56 | 27 |

The $k=5,t=2,m=5$ instance reproduces `metzler_pair_qstar_gap.cert` move for
move (`diff` of the two move lists is empty). All 14 also replay through
`qverify.py` (`checked 15, failures 0` with the Metzler certificate included),
through the round-5 certificate algebra (`python3 verify_with_certalg.py
fam_*.cert`: `files checked = 14, failures = 0`) and five of them through GAP,
which also confirms the group orders: $k=5,m=5$ gives 25, $k=7,m=5$ gives 35, $k=9,m=5$
gives 45, $k=13,m=7$ gives 91, $k=5,m=3$ gives 15 — all abelian, as they must
be.

For $k=5$ the neighbouring exponents are settled too. $[x^{3},y]$ is
$[x^{-2},y]$, which inverts and conjugates to $[x^{2},y]$, and
$[x^{4},y]=[x^{-1},y]$ is a conjugate of $[x,y]^{-1}$; so all four
presentations $\langle x,y \mid x^5,y^5,[x^t,y]\rangle$, $t=1,2,3,4$, are
pairwise Q\*\*-equivalent. Two of the six pairs are Q-equivalent outright by
those two moves, $(t=1,t=4)$ and $(t=2,t=3)$; the remaining four pairs pass
through the $t=2$ certificate. **[Argument, with the $t=2$ pair machine-checked
and the $t=1,4$ instances machine-checked as family members]**

## 6. What this does and does not establish

Established:

* the Q\*\*-equivalence of Metzler's pair, by explicit certificate, replayed by
  four implementations;
* the whole family of section 5, with 14 machine-checked instances;
* two lemmas (1 and 2) and a recipe (Lemma 3) that explain and remove the
  round-4 stopping point;
* the group order of Metzler's presentations (25, abelian) by GAP.

Not established:

* **Q\*-inequivalence.** Quoted from Barmak, citing Metzler 1976. I did not
  reproduce the invariant. The certificate found here is not a Q\*
  certificate (it needs prolongation and its inverse), but that proves
  nothing about Q\*-inequivalence.
* **Anything about the Andrews-Curtis conjecture.** Both presentations present
  $\mathbb{Z}/5\times\mathbb{Z}/5$, not the trivial group; they are irrelevant
  to the conjecture, and Q\*\*-equivalence of them is a statement about the
  coarseness of the move calculus only.
* **Barmak's pair** ($\langle x,y\mid [x,y],1\rangle$ against Fernandez's
  presentation) is untouched. It is *not* of the shape this technique handles:
  the two relator sets differ by a change of basis of the relation module,
  Evans's matrix over $\mathbb{Z}[X^{\pm1},Y^{\pm1}]$ which is not a product of
  elementary and diagonal matrices, so it is not reachable by one substitution
  through a defining relator. **[Open]** An explicit Q\*\* certificate for
  Barmak's pair remains un-supplied; Fernandez's proof is topological.
* **Minimality.** 44 moves is not claimed minimal, and no lower bound is
  claimed. The certificate is one explicit path.

## 7. Files and commands

In `.ultramath/smw3ow2dp/m6/` (proposed install path for the repository:
`directions/qdouble-star/m9/certs/metzler_pair_qstar_gap.cert` plus this report
as `directions/qdouble-star/m9/round6-m6.md`):

| file | what it is |
| --- | --- |
| `metzler_pair_qstar_gap.cert` | **the certificate**, 44 moves, m9 file format |
| `metzler_gen.py` | builds it, asserts the relator tuple at every stage, writes the trace |
| `metzler_trace.txt` | the 44 states, move by move |
| `metzler_family.py` | the family of section 5; builds and checks 14 certificates `fam_*.cert` |
| `verify_with_certalg.py` | replay through the round-5 certificate algebra engine |
| `gapgen.py` | replay in GAP, plus the group-order check |
| `gap_check.g` | the last emitted GAP script (regenerated by `gapgen.py`) |
| `metzler_pair_swap_variant.cert` | the same certificate in 41 moves using the single move `swap 1 2` (for the section 9 contrast) |
| `qverify_fixed.py` | the round-4 checker with the simultaneous-substitution fix of section 9 |
| `check_all.sh`, `check_all.log` | one command that reruns every check, and its log (`ALL CHECKS PASSED`, exit 0) |
| `fam_*.cert` | the 14 family certificates |

Commands, all from the repository root, `$M = .ultramath/smw3ow2dp/m6`:

```
python3 $M/metzler_gen.py                                  # rebuild + trace
cd directions/qdouble-star && python3 check_qstar.py $M/metzler_pair_qstar_gap.cert
python3 $M/verify_with_certalg.py                           # second replayer
python3 $M/gapgen.py                                        # GAP + group orders
python3 $M/metzler_family.py                                # 14 certificates
python3 $M/verify_with_certalg.py $M/fam_*.cert
cd directions/qdouble-star/m9 && python3 qverify.py $M/metzler_pair_qstar_gap.cert
bash $M/check_all.sh                                        # all of the above
```

## 8. What a next round could do

* Put the certificate into the Lean kernel (`toolkit/lean/AC6.lean`, direction
  I8): the Q\*\* move set is already formalised there (round-5 AC5.lean has all
  six Barmak moves as a guarded partial function), so this is a 44-step
  kernel-checked certificate and it would close the last un-replayed literature
  citation in the qdouble-star direction.
* Add the substitution move of Lemma 3 to the search engines as a **single
  derived move** ("replace $r_i$ by its image under the substitution read off a
  defining relator $x W$"), which is a Q-move sequence of at most $5|r_i|_x$
  moves (each factor costs at most five: invert, conjugate, multiply,
  conjugate back, invert) and which the round-4 engines lacked entirely. This is the
  general lesson: the Q\*\* certificate was not found by a bigger budget but by
  a derived move.
* Barmak's pair: the honest statement is that the technique here does not
  apply, and the obstruction (Evans's matrix) is the same one that makes the
  pair worth having.

## 9. A bug in `directions/qdouble-star/m9/qverify.py`, with a fix

This is a by-product of the work and it matters to anyone replaying a
Q\*\*-certificate with the round-4 direction's checker.

**Symptom. [Verified]** `qverify.py` rejects every `swap` move. Minimal
reproduction, on the round-4 direction's own start presentation:

```
$ cd directions/qdouble-star/m9
$ python3 -c "
import qverify as V
st = V.Pres(2, [(1,1,1,1,1),(2,2,2,2,2),(1,2,-1,-2)])
V.apply(st, ('swap', 1, 2))"
Bad: not an automorphism: phi(psi(x_2)) != x_2
```

The transposition $x_1 \leftrightarrow x_2$ is of course an automorphism of
$F_2$, and it is its own inverse.

**Diagnosis. [Verified]** `Pres.m_aut` checks $\phi\psi = \psi\phi =
\mathrm{id}$ by substituting the images **sequentially**:

```
back = preimages[i - 1]
for j in range(1, n + 1):
    back = subst(back, j, images[j - 1])
```

Substituting letter 1 and then letter 2 into a word is not applying $\phi$
once; when an image contains a letter that a later step also substitutes, the
map is applied twice. For the transposition the loop computes
$x_2 \mapsto x_1 \mapsto x_2 \mapsto x_1$, so the identity check fails. The bug
is masked for `nij`-style moves, where the later substitution finds nothing
left to change; it bites exactly for permutations, which is why no certificate
using `swap` can be replayed.

**Fix. [Verified]** substitute simultaneously. `qverify_fixed.py` in this
directory is the round-4 file with that change and nothing else:

```
def subst_all(w, images):
    out = []
    for a in w:
        img = images[abs(a) - 1]
        out.extend(img if a > 0 else inv(img))
    return red(out)
```

used as `back = subst_all(preimages[i-1], images)` and
`fwd = subst_all(images[i-1], preimages)` in `m_aut`.

**Validation. [Verified]** `metzler_pair_swap_variant.cert` is the 41-move
form of the certificate that uses the single move `swap 1 2`:

| checker | 41-move `swap` variant | shipped 44-move certificate |
| --- | --- | --- |
| `check_qstar.py` | OK, 41 moves | OK, 44 moves |
| `certificate-algebra` engine | replayed, endpoint match | replayed, endpoint match |
| `qverify.py` (round-4, unpatched) | **FAIL** at the swap (false negative) | OK, 44 moves |
| `qverify_fixed.py` | OK, 41 moves | OK, 44 moves |

`qverify_fixed.py` also accepts all 14 family certificates (`checked 14,
failures 0`).

**Scope. [Verified]** No round-4 result is affected: the 33 Q\*\*-certificates
of `directions/qdouble-star/m9/certs/` use `conj`, `lmul`, `neg`, `nij`,
`nijinv`, `inv`, `prolong` and `delete`, and **no `swap`**
(`cat m9/certs/*.cert | awk '/^move/{print $2}' | sort | uniq -c`), and so do
the 69 files in `out/`. The bug is latent, not historical.

The certificates shipped here avoid `swap` altogether (four elementary Nielsen
moves instead), so they replay under all five implementations, patched or not.
