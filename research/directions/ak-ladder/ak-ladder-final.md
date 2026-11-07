# The AK(n) ladder, completed: a uniform ladder step, end-to-end chains for n = 2 to 20, and the status of the reduced forms

Direction: m1, Round 3, swarm smw2opo0o, registered direction d5 (F1, ak-ladder completion).
Date: 2026-11-05. This note finishes the Round-2 draft `directions/ak-ladder/ak-ladder.md`
(m3, Round 2) and credits it throughout. Nothing here proves or disproves the
Andrews-Curtis conjecture. No rung of the ladder is claimed AC-trivial except
n = 1 and n = 2, where certificates already existed.

Labels used below: **PROVED** means a written argument in this note, with every
machine-checkable step machine-checked. **VERIFIED** means rerun here with an exact
command, whose output is quoted. **COMPUTED** means a finite search with its box
stated. **ARGUMENT** means a written argument that is not machine-checked in full.
Nothing is labelled PROVED unless the argument covers the whole claim.

## 1. What the direction asked and what is delivered

The direction asked for four things: rerun and verify the Round-2 draft, extend the
end-to-end chains `AK(n) ~ P(n)` to n = 6, 7, 8, attempt a trivialisation of the
length-reduced forms starting from P(3) at total length 14, and write the result up.

The main new result is that the ladder step `MS(n,w_k) ~ MS(n,w_(k+1))`, which the
draft had to find by search rung by rung and could not find for n = 6, is now an
explicit construction that works for every k and needs no search. It is a
ten-move certificate for every pair (n,k) with n at least 3 and 1 at most k at most
n-2. Composing it with the draft's two uniform templates gives an end-to-end
certificate `AK(n) ~ P(n)` of exactly 12n-2 moves for every n from 2 to 20. The
construction has no search step and no k-dependence: for fixed n the same ten moves
serve every k, and the only input is n itself.

## 2. Verification of the Round-2 draft

I copied the draft directory to my own working directory and reran its checks there,
so that no `__pycache__` or rewritten certificate lands in the draft's directory.
Every command below was run in that copy. The new code of this round is in
`directions/ak-ladder/round3/`, which imports the draft's `acx.py` and `patterns.py`
from its parent directory, so `python3 round3/check_all.py` reproduces Sections 3 and
4 from `directions/ak-ladder`.

| draft claim | command | output here | status |
|---|---|---|---|
| the Round-1 AK(1) certificate replays in the draft's independent engine | `python3 test_acx.py` | `AK(1) 19-move Round 1 certificate replayed independently: True`, `ALL OK`, 0.04 s | VERIFIED |
| Theorem 1 (no single AC move lowers the total relator length of AK(n)) checked for n at most 40 with conjugators of length at most 4 | `python3 test_acx.py` | `AK(n) strict local minima for n=1..40, conjugators up to length 4: PASS` | VERIFIED |
| the two uniform move templates, n up to 30 | `python3 patterns.py` | `template A AK(n) -> MS(n,w_1) 2n+9 moves n = 4..30: PASS`, `template B MS(n,w_(n-1)) -> P(n) 9 moves n = 3..30: PASS` | VERIFIED |
| the ladder table, the Todd-Coxeter indices, and the MS(n,w_k) triviality battery | `python3 ladder.py` | the table of Section 2 of the draft reproduced row by row, `TC(AK)=TC(P)=1` for n = 1..12, `MS(n,w_k) presents the trivial group for n = 2..12, k = 1..n-1: PASS (66 tuples)`, 7.0 s | VERIFIED |
| the stored certificates replay under two independent arithmetics (tuple arithmetic and sympy free groups) | `python3 verify_cert.py` and `python3 verify_cert.py round3/chain_uniform_*.json round3/p2_to_standard.json` | `42 certificate files, 0 failed` for the draft and `20 certificate files, 0 failed` for the new ones of Sections 4 and 5 | VERIFIED |
| the four composed chains of the draft | `python3 compose.py 2 3 4 5` | `21, 39, 56, 77` moves, `composed 4 chains, 0 failed` | VERIFIED |
| the AK(3) depth profile of Section 7 (cap 19, depth 20, 1,573,202 tuples, nothing shorter than 13) | `python3 profile.py 3 20 2 6 4000000` | rerun reproduces the stored `profile_n03.json` row by row, all 20 rows identical, last row `visited 1573202, min_total 14, best_total 13`, 127 s | VERIFIED |
| the length-(n+11) presentation of arXiv:2408.15332v2, both displays | `python3 test_acx.py` | both implemented, `n11` and `p_form`, total length n+11 for n up to 12 | VERIFIED |

Two notes on the draft, neither of which changes a theorem it states.

1. **Wording.** Theorem 1 is stated as "no single Andrews-Curtis move applied to the
   tuple of AK(n) lowers the total relator length", which is what the proof shows.
   The prose calls this "a strict local minimum". Inversion and conjugation leave the
   total length unchanged, so the correct phrase is a local minimum under the moves
   that lower it, or equivalently that every move is non-decreasing. The draft's own
   proof says this exactly. I keep the draft's statement and use the phrase
   "no move lowers" below.
2. **The "only missing link" has been removed.** Section 5 of the draft says the
   middle sequence `MS(n,w_1) -> MS(n,w_(n-1))` is certified for n = 3, 4, 5 and not
   found for n = 6 within its box. Section 3 below gives an explicit construction for
   that step for every n and k, so the n = 6 gap is closed without contradicting the
   draft's bounded negative, which remains true as a statement about its box.

The draft's Section 6 claim (a proof gap in the printed proof of Theorem t:mswk_wk1 of
arXiv:2408.15332v2, because a consequence-level derivation cannot certify an
AC-equivalence inside a presentation of the trivial group) is an ARGUMENT about a
text. I did not re-download the e-print in this round. I did verify the live arXiv
record: arXiv:2408.15332 has v1 of 27 Aug 2024 and v2 of 11 Feb 2025, and the v2
abstract says "we demonstrate the length reducibility of all but two presentations in
the Akbulut-Kirby series (1981)", which is a statement about length and not about
AC-triviality (fetched from https://arxiv.org/abs/2408.15332 on 2026-11-05). The
draft's triviality premise for the argument, that MS(n,w_k) presents the trivial
group, is VERIFIED above for n = 2..12 and all k (66 Todd-Coxeter runs).

## 3. The uniform ladder step

Write F_2 = <x,y>, A = x^-1 y^n x y^-(n+1), B_k = x^-1 y^-k x^-1 y x y, so that
`MS(n,w_k)` is the pair (A, B_k) with w_k = y^-k x^-1 y x y. Put u = x^-1 y^n x and

    c(n,k) = (u B_k u^-1)^-1 B_(k+1).

### 3.1 The mechanism

**Lemma 1 (legal block).** Let (r_1, r_2) be a pair of relators and W, p a word and a
nonzero integer. The four forward moves `conj(1,W)`, then p times `mul(2,1)`, then
`conj(1,W^-1)`, with the two extra moves `inv(1)` when p is negative, multiply r_2 on
the right by the single word W A^p W^-1 (with A^p read as |p| copies of A or of A^-1)
and leave r_1 equal to A at the end. PROVED by inspection: the conjugation moves
change only r_1, in the two directions, and the multiplication moves use the current
r_1 as the donor.

**Lemma 2 (the correction is in the normal closure).** For every n at least 2 and
every k, the word c(n,k) lies in the normal closure N(A) of A in F_2. ARGUMENT plus
finite check. The argument is that c(n,k) is trivial in the one-relator group
G = <x,y | A>, and N(A) is the kernel of F_2 -> G by definition. Triviality in G is
decided by Britton reduction, because with t = x^-1 the group is the ascending HNN
extension <y,t | t y^n t^-1 = y^(n+1)> of Z. I implemented that decision procedure
(`hnf.py`) and it returns the empty word for c(n,k) for every n from 2 to 60 and
every k (part 3 of `check_all.py`, 1711 instances). The general-n step from those
instances to all n is the part that is not written out as an induction here.

**Lemma 3 (four exact word identities).** For all n at least 2 and all q at least 1,

    (s-1,q>0)  x^-1 y^(nq) x y^(-(n+1)q)      = prod_(j<q) (y^((n+1)j) A y^(-(n+1)j))
    (s-1,q<0)  x^-1 y^(-nq) x y^((n+1)q)      = prod_(j<q) (y^(-(n+1)(j+1)) A^-1 y^((n+1)(j+1)))
    (s+1,q>0)  x y^((n+1)q) x^-1 y^(-nq)      = prod_(j<q) (y^(jn) x) A^-1 (y^(jn) x)^-1
    (s+1,q<0)  x y^(-(n+1)q) x^-1 y^(nq)      = prod_(j<q) (y^(-(j+1)n) x) A (y^(-(j+1)n) x)^-1

Each identity is an equality of reduced words, and not only of group elements.
PROVED by induction on q: the four identities are the same computation with the run
of y's placed on one side of the stable letter or the other. They are also VERIFIED
by direct computation for n = 2..30 and q = 1..10 (part 2 of `check_all.py`). The inductive step of the first identity is the word identity
h_q = A . (y^(n+1) h_(q-1) y^-(n+1)) with h_q the left hand side, which follows from
x^-1 y^(nq) x = (x^-1 y^n x)(x^-1 y^(n(q-1)) x) as words. The other three are the
same computation after moving the run of y's to the other side of the stable letter.

**Lemma 4 (factorisation).** Any word in N(A) can be factorised into conjugates of A
by reading its Britton reduction: if the leftmost redex is x^-1 y^m x with n | m,
then the word equals (P A^q P^-1) times a shorter word, with q = m/n, and if the
redex is x y^m x^-1 with (n+1) | m then Lemma 3 with q = m/(n+1) gives the same with
|q| conjugates. PROVED, conditional on Lemma 3. `ladder_template.factors_of`
implements the recursion and `factor_check` asserts that the product of the factors
equals c(n,k) exactly, for every instance it builds.

**Theorem 1 (uniform ladder step).** For every n at least 3 and every k with
1 at most k at most n-2 there is an explicit ten-move Andrews-Curtis certificate from
`MS(n,w_k)` to `MS(n,w_(k+1))`. The certificate depends on n and not on k: for every
k in range the same ten moves work, namely

    conj(2, x^-1 y^n x)
    mul(2,1)
    conj(1, y^n x^-1 y^-(n+1) x),  mul(2,1),  conj(1, x^-1 y^(n+1) x y^-n)
    conj(1, y^-1),  inv(1),  mul(2,1),  inv(1),  conj(1, y)

VERIFIED for n = 3..60 and every k (1711 instances, all replayed by exact word
arithmetic; the move list contains k nowhere), and PROVED for all n given Lemmas 1
to 4. There is no closing conjugation: the correction is applied to relator 2 on the
right after the initial conjugation. `ladder_template.uniform_moves` returns the list
and `ladder_template.check_uniform` replays it.

### 3.2 What the certificates look like

For all 1711 instances the Britton reduction of the correction has three redexes with
quotients 1, 1 and -1, and the factors are the same in shape every time: first A
itself, then the conjugate of A by y^n x^-1 y^-(n+1) x, then the conjugate of A^-1 by
y^-1. The blocks cost one, three and five moves, and with the initial conjugation the
certificate is ten moves. The largest total relator length met on the path
grows with n, because the conjugators are prefixes of the correction word; for n = 6
it is 49 against a starting length of 21. The draft's searched certificates for
n = 3, 4, 5 are shorter in moves (13 to 19 against ten) and lower on the mountain
pass, so both constructions have a use: the new one is uniform in n and k, and the
draft's searched ones are shorter and stay lower.

## 4. End-to-end chains for n = 2 to 20

Composing the draft's two templates with Theorem 1 gives `AK(n) ~ P(n)` in
2n+9 + 10(n-2) + 9 = 12n-2 moves. The chains for n = 2 to 20 are stored as
`certs/chain_uniform_N.json` in the draft's certificate format, so that
`verify_cert.py` replays them with both arithmetics. VERIFIED.

| n | total length AK(n) | total length P(n) | moves | largest total length on the path |
|---|---|---|---|---|
| 2 | 11 | 13 | 22 | 15 |
| 3 | 13 | 14 | 34 | 31 |
| 4 | 15 | 15 | 46 | 38 |
| 5 | 17 | 16 | 58 | 45 |
| 6 | 19 | 17 | 70 | 52 |
| 7 | 21 | 18 | 82 | 59 |
| 8 | 23 | 19 | 94 | 66 |
| 9 | 25 | 20 | 106 | 73 |
| 12 | 31 | 23 | 142 | 94 |
| 20 | 47 | 31 | 238 | 150 |

This answers the part of the direction that asked for n = 6, 7 and 8: those three
rungs now have explicit end-to-end certificates (70, 82 and 94 moves) instead of the
draft's search-and-fail record. The chains for n = 3, 4, 5 are longer than the draft's
(34 against 39, 46 against 56, 58 against 77) and every chain has a bigger excursion
than the draft's searched ones; both facts are consequences of the uniform
conjugator u = x^-1 y^n x.

## 5. The reduced forms and the trivialisation attempt

`P(n)` has total length n+11. For n = 2 it is AC-trivial, with the explicit
certificate `certs/p2_to_standard.json` of 51 moves (the reverse of the n = 2 chain
followed by the draft's 19-move certificate from AK(2) to the standard pair). That
certificate is VERIFIED and replays under both arithmetics. The first open case is
P(3) at total length 14, and the first thing to record is the exact equivalence:

**Proposition 2.** P(3) is AC-equivalent to AK(3) by an explicit certificate of 34
moves, and conversely. VERIFIED (table of Section 4; the certificate file
`certs/chain_uniform_3.json` replays under both arithmetics). Hence P(3) is
AC-trivial if and only if AK(3) is, and the triviality of AK(3) is open in the
literature (the draft's Section 2, citing Gilman and Myasnikov arXiv:2506.23031).

**Computed negative for P(3).** Exhaustive breadth-first search from P(3) over all
tuples of total relator length at most 20 reachable in at most 18 moves, with
conjugators of length at most 2: 1,130,768 tuples reached. The smallest relator
length met is 6, the smallest total length met is 13 (so a length-13 tuple is
reachable, and nothing shorter is), and no tuple of two length-one relators, the
standard pair, is reached. Exact command
`python3 try_trivial.py 3 20 18`, 147 s. This agrees with the Round-2 cap-20 census
of the whole AK(3) class (`directions/pu-enumeration/`), which found no relator
shorter than 5 in the box; the new box is a strict subset and is checked by different
code.

**Computed negative for P(5).** Same box, `python3 try_trivial.py 5 20 10`: 28,861
tuples, smallest relator length 7, smallest total length 16, standard pair not
reached. P(5) has no local downward move at all, so the smallest total length met is
the starting one.

**What this does not say.** These are statements about boxes. A certificate of
AC-triviality of P(3) that leaves the box (an intermediate tuple of total length 21
or more) is not excluded, and by Proposition 2 such a certificate would settle AK(3).

## 6. Cross-check against the Round-2 length-14 census

P(3) is the pair of relators (x^-1 y x y^-1 x y^-1 x^-1, x y^2 x y^-1 x^-1 y^-1). Its
canonical form in the notation of `directions/c14/` (relators freely and cyclically
reduced, minimal under rotation and inversion, ordered by length then word) computed
with that directory's own `c14lib.canon_pres` is `BBAbabA,BAAbaBa`. It appears in
`directions/c14/class_14.txt` as `resisting-trivial-group | BBAbabA,BAAbaBa` and in
`directions/c14/final_classes.txt` as `14 | ak3-equivalent | BBAbabA,BAAbaBa`.
VERIFIED by running their canonicalisation on my pair and grepping their files. So
the two directions agree: P(3) is a length-14 presentation of the trivial group, it is
in the AK(3) class, and it is one of the 26 members that the length-14 census
classifies as AK(3)-equivalent rather than AC-trivial.

## 7. Exact commands

    cd directions/ak-ladder
    python3 test_acx.py          # 0.04 s, prints PASS and ALL OK
    python3 patterns.py          # templates A and B, n up to 30
    python3 ladder.py            # table, Todd-Coxeter indices, 66-tuple battery, 7 s
    python3 verify_cert.py       # two-arithmetic replay of the draft's certificates
    PYTHONDONTWRITEBYTECODE=1 python3 verify_cert.py round3/chain_uniform_*.json round3/p2_to_standard.json
                                 # the 20 new certificates, 0 failed
    python3 compose.py 2 3 4 5   # the draft's four chains
    python3 round3/check_all.py        # Sections 3 and 4 of this note, 1.8 s
    python3 round3/check_all.py quick  # the ladder only
    python3 round3/chain_all.py 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
                                 # rebuilds the end-to-end certificates
    python3 round3/try_trivial.py 3 20 18    # the P(3) box, 147 s
    python3 round3/try_trivial.py 5 20 10    # the P(5) box, 3 s

New files of this round, in `directions/ak-ladder/round3/` (the same files sit in my
own working directory `.ultramath/smw2opo0o/m1/ak-ladder/`):

| file | contents |
|---|---|
| `hnf.py` | Britton reduction in G = <x,y | A>, a decision procedure for membership in N(A) |
| `ladder_template.py` | the uniform ladder step: correction word, factorisation, certificate, exactness assertion |
| `chain_all.py` | composes templates A and B with the ladder steps into `AK(n) ~ P(n)` |
| `check_all.py` | one entry point for every claim of Sections 3 and 4 |
| `try_trivial.py` | the boxes of Section 5 |
| `chain_uniform_N.json` | the end-to-end certificates for n = 2 to 20, in the draft's certificate format |
| `p2_to_standard.json` | P(2) to the standard pair in 51 moves, so P(2) is AC-trivial |
| `ak-ladder-final.md` | this note |

## 8. What is not established

1. AC-triviality of AK(n) for n at least 3, and of P(3), is untouched. Section 5 is a
   bounded negative.
2. Lemma 2 and Lemma 3 are machine-checked on finite ranges (n at most 60 for the
   instances, n at most 30 with q at most 10 for the identities). The passage to all n
   needs the inductions of Section 3 written out in full. I give the inductive step of
   the first identity and state that the other three are the same computation, so the
   general-n claim rests on those inductions, and every instance I actually claim is
   machine-checked.
3. The drafts Section 6 proof-gap claim is inherited as ARGUMENT. I verified the live
   arXiv record and the abstract text of version 2, not the source file
   `sec/search.tex`.
4. The excursions of the new chains are larger than those of the draft's searched
   chains, and the new certificates are not minimal in any sense. No claim of
   minimality is made.
5. The n11(n) display of the paper (the other length-(n+11) presentation) is covered
   by the draft's searched certificates for n at most 12 and is not extended here; the
   uniform construction produces the `p_form(n)` display only.
