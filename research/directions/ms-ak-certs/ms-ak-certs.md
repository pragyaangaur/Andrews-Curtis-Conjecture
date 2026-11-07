# Explicit Andrews-Curtis certificates: AK(n) is AC-equivalent to MS(n, w_1)

Direction E9 (OPEN_QUESTIONS Q8, partial). Files, certificates, code and logs are
in this directory. Nothing here claims progress on the Andrews-Curtis
conjecture itself: the certificates relate two specific presentations of the
trivial group to one another.

The labels follow the repository convention. [V] marks a statement checked by a
computation that I ran, with the exact command in Section 6. [L] marks a
statement read in a source whose identifier is in Section 7. [A] marks an
argument written out here that no machine checked.

## 1. Result

The two families are

  AK(n) = <x, y | x^n = y^(n+1), xyx = yxy>,
  MS(n, w) = <x, y | x^(-1) y^n x = y^(n+1), x = w>,   w_1 = y^(-1) x^(-1) y x y.

[V] AK(n) is Andrews-Curtis equivalent to MS(n, w_1), with explicit replayable
certificates, for every n from 2 to 10. The certificate for n = 2 has 11 moves, the
one for n = 3 has 15 moves, and in general the construction gives 4n + 3 moves
from AK(n) to MS(n, w_1). Certificates for the reverse direction, MS(n, w_1) to
AK(n), are included as well and have 7n + 3 moves.

OPEN_QUESTIONS Q8 asks whether for a fixed n every MS(n, w) is AC-equivalent to
AK(n), and what the certificates settle is one case of one subfamily, namely
w = w_1 for every n from 2 to 10. The general question of Q8 is untouched. The cases
the direction asks for are n = 2 and n = 3, and those are the two main
certificates, `cert_n2.json` and `cert_n3.json`. The statement for those n is
Proposition 1.3 of Myasnikov, Myasnikov and Shpilrain 2002 [L], whose printed
proof is a three-step sketch with one step marked "(substitution)" and no
witness written down. The contribution here is the explicit move list, checked
five independent ways, so the case k = 1 that Shehper et al. cite to that paper
no longer rests on an unexpanded sketch. Their Proposition 5 states the citation
explicitly: "For all n >= 2, AK(n) is AC-equivalent to MS(n, w_1) where
w_1 = y^(-1)x^(-1)yxy" [L, arXiv:2408.15332, Proposition 5].

| n | moves AK(n) to MS(n, w_1) | moves MS(n, w_1) to AK(n) | longest relator reached |
|---|---|---|---|
| 2 | 11 | 17 | 17 |
| 3 | 15 | 24 | 21 |
| 4 | 19 | 31 | 25 |
| 5 | 23 | 38 | 29 |
| 6 | 27 | 45 | 33 |
| 7 | 31 | 52 | 37 |
| 8 | 35 | 59 | 41 |
| 9 | 39 | 66 | 45 |
| 10 | 43 | 73 | 49 |

The last column is the largest length of a single relator anywhere in the
certificate, and it matters for other directions. The n = 3 certificate passes
through a relator of length 21, while its two ends have relators of lengths 7 and
6 (for AK(3)) and 9 and 6 (for MS(3, w_1)). A bounded search that caps relator
length at 14, or at 17, therefore cannot see this path at all.

## 2. The argument behind the certificates

Write words in the free group F = F(x, y) and put

  D  = x y x y^(-1) x^(-1) y^(-1)      (second relator of AK(n))
  C  = x^n y^(-(n+1))                  (first relator of AK(n))
  B  = x^(-1) y^(-1) x^(-1) y x y      (second relator of MS(n, w_1))
  A  = x^(-1) y^n x y^(-(n+1))         (first relator of MS(n, w_1))
  A0 = x^(-1) y x,   B0 = y x y^(-1),   W = x^(-1) D^(-1) x.

Four identities in the free group, all asserted line by line in
`free_group_checks` of `build.py` before a single move is emitted [V, and each is
a two-line hand check]:

1. W = x^(-1) D^(-1) x, which is the definition of W;
2. W = A0 B0^(-1), that is x^(-1) y x y x^(-1) y^(-1) = x^(-1) y x (y x y^(-1))^(-1);
3. the telescoping identity, for every n >= 1,

   A0^n B0^(-n) = product over k = 0, ..., n-1 of ( B0^k W B0^(-k) ),   [A]

   which follows by induction from W = A0 B0^(-1);
4. A = P_n (y C y^(-1)), where P_n is the product in identity 3. This is the
   only substantive step: P_n = x^(-1) y^n x y x^(-n) y^(-1) by identity 3, and
   multiplying by y C y^(-1) = y x^n y^(-(n+2)) cancels x^(-n) x^n and leaves
   x^(-1) y^n x y^(-(n+1)) = A. [A]

Every factor B0^k W B0^(-k) of P_n is the conjugate of D^(-1) by g_k = B0^k x^(-1),
by identity 1. So P_n is a product of conjugates of D^(-1), and multiplying a
relator by a conjugate of another relator is an AC move (a conjugation of the
second relator, a product move, and the inverse conjugation). The route is then

  (C, D)  --conj 1 y-->  (y C y^(-1), D)  --left multiply r_1 by the n factors-->  (A, D)
          --conjugate r_2-->  (A, B),

and each arrow is a list of ordinary AC moves. Left multiplication by the
current r_2 is two moves (conjugate r_1 by r_2, then multiply r_1 by r_2), and
restoring r_2 costs two more, which is where 4n + 3 comes from.

Two remarks explain why the route has this shape. First, the first relator cannot be
converted from C to A by moves that touch only r_1 and multiply by conjugates of
D: those moves preserve the conjugacy class of the image of r_1 in
F / normalClosure(D), and in that group C and A are conjugate by y while
C A^(-1) has exponent sum -1 in the abelianisation Z of that group, so the two
are different elements there. That is exactly why a conjugation of r_1 appears
at the start and a conjugation of r_2 appears at the end. Second, the second relator of MS(n, w_1)
is a cyclic rotation of D^(-1) (found by search in `findw.py`, verified as an
identity by `build.py`), so the last step is three moves.

## 3. The certificates, written out

Move tags: `inv i` replaces r_i by r_i^(-1); `mul i j` replaces r_i by r_i r_j
with i different from j; `conj i g` replaces r_i by g r_i g^(-1). Words are
printed with x, y for the generators and X, Y for their inverses, so `yxYX` is
y x^(-1) y^(-1) x^(-1). Indices are 1 and 2. These are exactly the three moves of
`toolkit/ac.py`, and they are the moves (AC1) to (AC3) of the 2002 paper, whose
text reads "(AC1) y_i is replaced by y_i y_j for some j different from i;
(AC2) y_i is replaced by y_i^(-1); (AC3) y_i is replaced by g y_i g^(-1) for some
g in F" [L, arXiv:math/0302080, Section 1].

n = 2. Start (xxYYY, xyxYXY) = (x^2 y^(-3), x y x y^(-1) x^(-1) y^(-1)) = AK(2),
end (XyyxYYY, XYXyxy) = (x^(-1) y^2 x y^(-3), x^(-1) y^(-1) x^(-1) y x y) = MS(2, w_1).

```
 1  conj 1 y
 2  inv 2
 3  conj 2 yxYX
 4  conj 1 yxYXyxyXXY
 5  mul 1 2
 6  conj 2 xyXY
 7  conj 2 X
 8  conj 1 XyxyXY
 9  mul 1 2
10  conj 2 x
11  conj 2 YXY
```

n = 3. Start (xxxYYYY, xyxYXY) = AK(3), end (XyyyxYYYY, XYXyxy) = MS(3, w_1).

```
 1  conj 1 y
 2  inv 2
 3  conj 2 yxxYX
 4  conj 1 yxxYXyxyXXXY
 5  mul 1 2
 6  conj 2 xyXXY
 7  conj 2 yxYX
 8  conj 1 yxYXyxyXXY
 9  mul 1 2
10  conj 2 xyXY
11  conj 2 X
12  conj 1 XyxyXY
13  mul 1 2
14  conj 2 x
15  conj 2 YXY
```

The JSON files carry the same lists in machine-readable form, together with the
start and end presentations as letter strings. `check.py` prints the whole
presentation after every move, so a reader can watch the relators change; that
printout is in `out/check_all.txt`.

## 4. Verification

There are six checks. The first is the builder's own assertions, checks 2 to 5
are independent replays written against four different implementations of free
group arithmetic, and the sixth is a Lean 4 proof checked by the kernel. Each
replay recomputes the two
presentations from their definitions rather than trusting the file: `check.py`
builds MS(n, w_1) as (X + y^n + x + Y^(n+1), X + Yxyxy) and AK(n) as
(x^n + Y^(n+1), xyxYXY) from the prose formulas, and then checks that the stated
start and end of the certificate equal those two lists as strings.

1. `build.py` produces the move lists from the identities of Section 2. Every
   identity is asserted before any move is written, and the builder also asserts
   after every stage that the projection of the presentation is what it should
   be.
2. `check.py` is an independent replay. It shares no code with the builder and
   no code with `toolkit/`: words are strings over x, X, y, Y, reduction is a
   stack, and the three moves are re-implemented with legality checks (indices
   in range, i different from j, conjugator reduced and nontrivial).
3. `check_all.g` replays the same certificates inside GAP 4.14, so GAP's own
   free group arithmetic performs the multiplication and reduction.
4. `replay_toolkit.py` replays the certificates through `toolkit/words.py` and
   `toolkit/ac.py` (the repository toolkit, written and refereed independently of
   this directory) and also compares the Smith normal form of the exponent-sum
   matrix at the two ends.
5. `check_sympy.py` replays them with sympy's own free group implementation
   (`sympy.combinatorics.free_groups`), which is third-party code with its own
   word representation, and checks that the two ends are the AK and MS elements
   as sympy objects.
6. `AC_certs.lean` states, for every n from 2 to 10, that running the move list
   of the certificate on AK(n) gives exactly MS(n), where AK and MS are defined
   in Lean from the same prose formulas, and proves it by `decide` (with
   `set_option maxRecDepth 1000000`, which the `decide` term needs from n = 7). It also proves
   four sanity lemmas about the reduction function (two of them cancel only
   after the tail has been reduced) and that all thirty six endpoint words, the
   AK and MS relators for n = 2 to 10, are reduced. `#print axioms` reports that every one of these theorems depends on
   no axioms at all. There is no `sorry` and no `native_decide` in the file.

## 5. What is not claimed

1. The certificates are not claimed to be shortest. I did not run a shortest-path
   search, and no lower bound on the AC-distance between AK(n) and MS(n, w_1) is
   claimed.
2. No claim is made for k different from 1 in MS(n, w_k). Here is the exact point
   where this route stops. The second relator of MS(n, w_k) is
   x^(-1) y^(-k) x^(-1) y x y, whose exponent sums are (-1, 2-k), while D and
   D^(-1) have exponent sums (1,-1) and (-1,1). Conjugates have equal exponent
   sums, so for k different from 1 that relator is not a conjugate of D or D^(-1)
   at all, and the last step of the route cannot run. That is a statement about
   this route and not about AC-equivalence, and the k different from 1 cases
   remain as Shehper et al. state them.
   A second obstruction explains why the obvious repair of the route fails. The
   second relators satisfy the word identity R2(k+1) = (x^(-1) y^(-1) x) R2(k),
   checked in `obstruction.py` for k from -4 to 4 [V], so the direct step from
   MS(n, w_k) to MS(n, w_(k+1)) that leaves the first relator alone would have to
   left multiply the second relator by x^(-1) y^(-1) x. A left multiplication by
   a word u is available from the substitution principle only when u lies in the
   normal closure of the relators that are not being changed, here N(R1). The
   word x^(-1) y^(-1) x is not in N(R1): the affine group of the rational line,
   with y a translation by 1 and x multiplication by n/(n+1), satisfies R1 and
   sends x^(-1) y^(-1) x to the translation -(n+1)/n, which is not the identity,
   and `obstruction.py` checks this in exact arithmetic for n = 1 to 10 [V]. A
   k to k+1 step therefore needs an interleaved path in which both relators
   change, and that is what the printed proof of Shehper et al. Theorem 6 does
   at the level of equations without writing the moves. Making that proof
   explicit is left to a later round.
3. The formula 4n + 3 moves for general n is a statement about the construction,
   not a machine-checked theorem for all n. What is machine checked is n = 2 to
   10, together with the free-group identity A = P_n (y C y^(-1)), which
   `build.py` checks separately for each of those n. The induction that proves
   identity 3 for all n is written out in Section 2 and is elementary, but it is
   an argument, not a computation.
4. Nothing here bears on whether AK(3) is AC-trivial, on the stable version, or
   on the conjecture. Both presentations in each certificate present the trivial
   group, which is known separately: AK(n) by the Lean theorem of m5 in
   `directions/ak-status/ak_trivial.lean`, and MS(n, w) by Miller and Schupp
   [L]. AC-equivalence of two presentations of the trivial group is consistent
   with both being non-trivialisable.
5. The certificates do not verify the citation in Shehper et al. beyond the k = 1
   statement. I verified Proposition 1.3 of the 2002 paper for every n from 2 to
   10, and the direction asked for n = 2 and n = 3. Whether Shehper et al. or
   Myasnikov, Myasnikov and Shpilrain have a proof for all k in Z is a separate
   question, and the status of the stable question is treated in
   `survey/stable-ak3-status.md` by the E1 direction of this round.

## 6. Exact commands

From this directory:

```
bash run_all.sh
```

or one at a time:

```
python3 build.py            # writes cert_n2.json ... cert_n10.json
python3 reverse.py          # writes cert_n2_rev.json ... cert_n10_rev.json
python3 check.py            # replays all eighteen certificates, prints every move
python3 gen_gap.py && gap -q check_all.g
python3 replay_toolkit.py   # needs the repository toolkit above this directory
python3 check_sympy.py
python3 gen_lean.py && lean AC_certs.lean
```

Recorded output is in `out/`. The key lines are

```
n=2: 11 moves -> cert_n2.json
n=3: 15 moves -> cert_n3.json
VERDICT cert_n2.json: certificate OK
VERDICT cert_n3.json: certificate OK
ALL CERTIFICATES PASS in GAP
toolkit replay: ALL OK
sympy replay: ALL OK
'ACMove.cert2_ok' does not depend on any axioms
'ACMove.cert3_ok' does not depend on any axioms
```

Runtimes are a few seconds for each replay and about 7 seconds for
`lean AC_certs.lean` on the campaign VM (Mathlib import included). Nothing is
random and no environment variable is needed beyond `LEAN_PATH` for Lean.

## 7. Sources

1. A. D. Myasnikov, A. G. Myasnikov, V. Shpilrain, "On the Andrews-Curtis
   equivalence", Contemporary Mathematics 296 (2002) 183-198,
   DOI 10.1090/conm/296/05074, arXiv:math/0302080 (submitted 7 February 2003;
   the arXiv metadata gives the journal reference above). I read the whole
   paper from the arXiv PDF and from the author's copy at
   shpilrain.ccny.cuny.edu/ac.pdf, which agree. Proposition 1.3 reads, in the
   paper's own typesetting: "The presentation <x, y | x^n = y^(n+1),
   xyx = yxy>, n >= 2, is AC-equivalent to <x, y | x^(-1) y^n x = y^(n+1),
   x = y^(-1) x^(-1) yxy>". The printed proof is one line: the original
   presentation, then the same with the second relator written as
   x = (y^(-1)x^(-1))y(xy), then the substitution step marked "(!)", then the
   target. The raw pdftotext line, for honesty about the extraction, is
   "Proof of Proposition 1.3. hx, y| xn = y n+1 , xyx = yxyi -→ hx, y| xn =
   y n+1 , x = (y -1 x-1 )y(xy)i -→ (substitution) hx, y| y -1 x-1 y n xy =
   y n+1 , x = (y -1 x-1 )y(xy)i(!) -→ hx, y| x-1 y n x = y n+1 , x =
   y -1 x-1 yxyi."
2. C. F. Miller III, P. E. Schupp, "Some presentations of the trivial group",
   Contemporary Mathematics 250 (1999) 113-115, DOI 10.1090/conm/250/03848. I did
   not re-read this paper for this direction; the triviality of MS(n, w) for w of
   exponent sum zero on x is quoted from `survey/ak-status.md` Section 3.2, which
   cites their Theorem 1 and Corollary 3.
3. A. Shehper, A. M. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen,
   Y. Qiu and others, "What makes math problems hard for reinforcement learning:
   a case study", arXiv:2408.15332 (submitted 27 August 2024; the copy I read is
   the version of 11 February 2025, 58 pages), NeurIPS proceedings DOI
   10.52202/085713-5348. I read Proposition 5, Theorem 6, Theorem 7 and Appendix
   F. Proposition 5 is quoted in Section 1. Theorem 6 defines w_k =
   y^(-k)x^(-1)yxy and states that for fixed n the presentations MS(n, w_k) are
   all AC-equivalent, with a proof that goes from k to k+1. Appendix F locates a
   misprint in the 13th relator of the unknot diagram of Figure 24 of the 2002
   paper, a relator printed there as x_13 = x_5 x_12 x_5^(-1), and it notes that
   the resulting presentation is not a Wirtinger presentation of any knot
   diagram. That misprint sits in the part of the 2002 paper that builds its rank
   three family, its Theorem 1.4, and it is not in Proposition 1.3. The
   certificates here confirm Proposition 1.3 for n = 2 to 6 independently of the
   printed derivation. What the misprint does to the stable status of AK(3) is the
   subject of the E1 direction of this round, not of this file.
4. `survey/ak-status.md` Section 3, which fixes the exact form of MS(n, w) and of
   w_1, and `OPEN_QUESTIONS.md` Q8.

One caution about reading the literature here. The direction asks for w_1 =
y^(-1) x^(-1) y x y, and the 2002 paper writes the same word as
(y^(-1)x^(-1))y(xy), which is the same word. The exponent attached to the first
generator in AK(n) is the other standing hazard, and this file uses
AK(n) = <x, y | x^n = y^(n+1), xyx = yxy>, which is the convention of
`survey/ak-status.md` Section 2.1.

## 8. Files

| file | contents |
|---|---|
| `cert_n2.json` ... `cert_n10.json`, and the `_rev` files | the eighteen certificates: start, end, and the move list |
| `build.py` | constructs the certificates from the identities of Section 2, asserts every identity |
| `findw.py` | the one small search that was used, which expresses the elementary substitution witness W as a conjugate of D^(-1) |
| `w.py` | the builder's word arithmetic |
| `check.py` | independent replay, independent word arithmetic, definitions recomputed |
| `reverse.py` | turns a certificate into one for the opposite direction |
| `gen_gap.py`, `check_all.g` | GAP script and its generator |
| `replay_toolkit.py` | replay through `toolkit/ac.py` |
| `check_sympy.py` | replay through sympy's free groups |
| `obstruction.py` | the two exact checks behind the k different from 1 obstruction of Section 5 |
| `gen_lean.py`, `AC_certs.lean` | the Lean 4 statement and proof of the certificates |
| `run_all.sh` | regenerates everything and runs all five checks |
| `out/` | recorded output of every command in Section 6 |
