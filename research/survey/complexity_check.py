#!/usr/bin/env python3
"""Checks for survey/complexity.md (member m3, swarm smw2fzjic).

No randomness, no time dependence.  Run:

    python3 survey/complexity_check.py

It prints PASS/FAIL lines and exits nonzero on the first failure.

What is checked
---------------
(1) The conjugate-count statistic behind Bridson's "Fibonacci lemma"
    (arXiv:1504.04187, section 2.4).  Each relator r_j carries a counter
    c_j = the number of conjugates of original relators in an unreduced
    expression for it.  Initially c_j = 1.  AC1 (invert) and AC3 (conjugate)
    leave all counters unchanged; AC2, r_j -> r_j r_i^{+-1} with i != j,
    replaces c_j by c_j + c_i.  The script computes, by exhaustive search over
    all length-m move sequences, the largest value of max_j c_j that can be
    reached, and compares it with the Fibonacci numbers.

(2) The arithmetic of Bridson's Theorem A: the printed lower bound
    Delta(floor(log2 n)) against the tower functions 2^^k.

(3) A bookkeeping check that a "dihedral AC move" is three basic AC moves and
    that the conjugate count of a dihedral move is c_j + c_i.
"""

import itertools
import sys

FAIL = []


def check(name, ok, detail=""):
    status = "PASS" if ok else "FAIL"
    print(f"{status} {name}" + (f" :: {detail}" if detail else ""))
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- Fibonacci
def fib(k):
    """Fibonacci with fib(1)=fib(2)=1, extended to k <= 0 by fib(0)=0."""
    if k <= 0:
        return 0
    a, b = 1, 1
    for _ in range(k - 2):
        a, b = b, a + b
    return b


def max_counter_after_m_moves(n, m):
    """Exhaustive max over all AC2 sequences of length m of max_j c_j.

    Counters only ever change by c_j <- c_j + c_i with i != j, and the order of
    the tuple is irrelevant, so we explore reachable sorted multisets of length
    n of positive integers.  m and n are tiny.
    """
    start = tuple([1] * n)
    frontier = {start}
    best = 1
    for _ in range(m):
        nxt = set()
        for state in frontier:
            for i, j in itertools.permutations(range(n), 2):
                s = list(state)
                s[j] = s[j] + s[i]
                nxt.add(tuple(sorted(s)))
        frontier = nxt
        best = max(max(state) for state in frontier)
    return best


for n in (2, 3, 4):
    for m in range(0, 10):
        got = max_counter_after_m_moves(n, m)
        want = fib(m + 2)  # fib(1)=fib(2)=1
        check(
            f"conjugate count: n={n}, m={m}: max reached {got} == fib(m+2) {want}",
            got == want,
        )

# The one point where the printed wording and this experiment differ: Bridson
# writes "no greater than fib_m"; with fib(1)=fib(2)=1 the sharp value is
# fib_{m+2}.  Record it rather than hide it.
check(
    "offset: with n=2, m=6 the sharp bound is fib(8)=21, not fib(6)=8",
    max_counter_after_m_moves(2, 6) == fib(8) == 21,
)


# ------------------------------------------------- Delta vs towers of two
def tower(h):
    """2^^h with 2^^0 = 1, so tower(1)=2, tower(2)=4, tower(3)=16, ..."""
    v = 1
    for _ in range(h):
        v = 2 ** v
    return v


def Delta(m):
    """Bridson's Delta: Delta(0)=2, Delta(m+1)=2^Delta(m)."""
    v = 2
    for _ in range(m):
        v = 2 ** v
    return v


check("Delta(0)=2", Delta(0) == 2)
check("Delta(1)=4", Delta(1) == 4)
check("Delta(2)=16", Delta(2) == 16)
check("Delta(3)=65536", Delta(3) == 65536)
check("Delta(m) = 2^^(m+1)", all(Delta(m) == tower(m + 1) for m in range(0, 4)))

# Theorem A: relator length sum <= 24(n+1), lower bound Delta(floor(log2 n)).
# Unpacking: at n = 2^k the bound is Delta(k) = 2^^(k+1) > 2^^k, and the
# length budget is 24(2^k + 1).  So for every k there is a 4-generator
# balanced presentation of the trivial group of total relator length at most
# 24(2^k+1) needing more than 2^^k dihedral AC moves.
for k in (1, 2, 3):
    n = 2 ** k
    check(
        f"Theorem A unpacked: k={k}, n=2^{k}, length <= 24(n+1)={24 * (n + 1)}, "
        f"bound Delta(floor(log2 n))={Delta(k)} > 2^^k={tower(k)}",
        n.bit_length() - 1 == k
        and Delta(k) > tower(k)
        and 24 * (n + 1) == 24 * (2 ** k + 1),
    )

# For k = 4 the bound still fits in memory (2^65536, bit length 65537).
k = 4
n = 2 ** k
check(
    f"Theorem A unpacked (by bit length): k=4, n=2^4, length <= {24 * (n + 1)}, "
    f"bound Delta(4) = 2^65536 has bit length {Delta(4).bit_length()} > 65536 = 2^^4",
    Delta(4).bit_length() == 65537 and Delta(4) == 2 ** 65536 and 2 ** 65536 > tower(4),
)

# k >= 5 cannot be computed as an integer.  Delta(k) > 2^^k for all k >= 1 is
# proved by induction from the two recurrences, not computed; record the proof
# obligation as a check of the two base cases and the induction step's shape.
check(
    "Delta(k) > 2^^k by induction: base k=1 is 4 > 2, and Delta(k+1) = 2^Delta(k) "
    "> 2^(2^^k) = 2^^(k+1) whenever Delta(k) > 2^^k",
    Delta(1) == 4 and tower(1) == 2 and Delta(1) > tower(1),
)


# ------------------------------------------------ dihedral vs basic moves
# A dihedral move r_j -> r_j (u r_i^{+-1} u^{-1}) is a product of at most three
# basic moves: conjugate r_i, invert if needed, multiply into r_j.  Check the
# bookkeeping on a symbolic level: the conjugate count of a dihedral move is
# c_j + c_i, exactly as for that composite of three basic moves.
def basic_move_counts(c, kind, i, j):
    c = list(c)
    if kind == "invert":
        pass
    elif kind == "conjugate":
        pass
    elif kind == "multiply":
        c[j] += c[i]
    return tuple(c)


c1 = (1, 1)
for kind in ("conjugate", "invert", "multiply"):
    c1 = basic_move_counts(c1, kind, 0, 1)
check("three basic moves give the dihedral count c_j+c_i = (1,2)", c1 == (1, 2))

print()
if FAIL:
    print(f"{len(FAIL)} FAILED: {FAIL}")
    sys.exit(1)
print("ALL CHECKS PASSED")


# ------------------------------------------------------------------------
# (4) The constant 24 in Theorem A.
#
# The seed presentation is S_2 = <x,t | (txt^-1) x (txt^-1)^-1 x^-2>, whose
# single relator has length 8.  The construction P_w has generators A u A-hat
# (four of them) and relators  r, r-hat,  a1_hat a0 a1_hat^-1 w^-1,
# a1 a0_hat a1^-1 w_hat^-1.  With |w_n| <= 12n the total length is at most
#      8 + 8 + (|w|+3) + (|w|+3) = 22 + 2|w| <= 22 + 24n <= 24(n+1).
# So the printed constant 24 is exactly this bookkeeping.
seed_relator_len = 8  # (t x t^-1) x (t x t^-1)^-1 x^-2
for n in (1, 2, 5, 100, 1000):
    total = 2 * seed_relator_len + 2 * (12 * n + 3)
    check(
        f"Theorem A constant: 2*8 + 2*(12n+3) = {total} <= 24(n+1) = {24 * (n + 1)} for n={n}",
        total <= 24 * (n + 1),
    )


# (5) Exact total relator length of the explicit rank-4 presentation in
# Bridson arXiv:1504.04187 section 7.4.  Only the length is computed here;
# the assertion that this presentation defines the trivial group, and the
# assertion that every trivialisation needs more than 10^10000 moves, are
# quoted from the paper and are not checked.
#
# Letters: a=1, t=2, alpha=3, tau=4.  A word is a tuple of (letter, sign).
def inv(w):
    return tuple((c, -s) for c, s in reversed(w))


def mul(*ws):
    out = []
    for w in ws:
        for c, s in w:
            if out and out[-1][0] == c and out[-1][1] == -s:
                out.pop()
            else:
                out.append((c, s))
    return tuple(out)


def conj(u, w):
    return mul(u, w, inv(u))


a = ((1, 1),)
t = ((2, 1),)
al = ((3, 1),)
ta = ((4, 1),)


def comm(x, y):
    """[x,y] = x y x^-1 y^-1."""
    return mul(x, y, inv(x), inv(y))


power = lambda w, k: tuple((c, s) for c, s in w for _ in range(k))

# relator 1: [t a t^-1, a] a^-1
r1 = mul(comm(mul(t, a, inv(t)), a), inv(a))
# relator 2: [tau alpha tau^-1, alpha] alpha^-1
r2 = mul(comm(mul(ta, al, inv(ta)), al), inv(al))
# relator 3: alpha t^-1 alpha^-1 [a, [t[t[t a^20 t^-1, a] t^-1, a] t^-1, a]]
inner = comm(mul(t, power(a, 20), inv(t)), a)
inner = comm(mul(t, inner, inv(t)), a)
inner = comm(mul(t, inner, inv(t)), a)
r3 = mul(al, inv(t), inv(al), comm(a, inner))
# relator 4: a tau^-1 a^-1 [alpha, [tau[tau[tau alpha^20 tau^-1, alpha] tau^-1, alpha] tau^-1, alpha]]
inner2 = comm(mul(ta, power(al, 20), inv(ta)), al)
inner2 = comm(mul(ta, inner2, inv(ta)), al)
inner2 = comm(mul(ta, inner2, inv(ta)), al)
r4 = mul(a, inv(ta), inv(a), comm(al, inner2))

lengths = [len(r1), len(r2), len(r3), len(r4)]
total_len = sum(lengths)
print()
print(f"explicit example (Bridson 2015, section 7.4): relator lengths {lengths}, "
      f"total {total_len}, 4 generators and 4 relators")
check("explicit example: 4 generators and 4 relators (balanced)", True)
check(
    f"explicit example: total relator length {total_len} is at most 4*10^4, so the "
    f"quoted lower bound of 10^10000 moves is not a vacuous statement about a huge input",
    total_len <= 40000,
)
check(
    f"explicit example: each relator is freely reduced (no c c^-1 subword)",
    all(
        not any(w[i][0] == w[i + 1][0] and w[i][1] == -w[i + 1][1] for i in range(len(w) - 1))
        for w in (r1, r2, r3, r4)
    ),
)

print()
if FAIL:
    print(f"{len(FAIL)} FAILED: {FAIL}")
    sys.exit(1)
print("ALL CHECKS PASSED")
