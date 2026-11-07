"""Reduced words in the free group on n generators, plus small exact
integer linear algebra (determinant, Smith elementary divisors).

A word is a tuple of nonzero integers.  The letter ``i`` is the generator
``x_i`` and the letter ``-i`` is its inverse.  A word is reduced when no
entry is the negation of the next entry.  The empty tuple is the identity
word.

Generator labels are 1-based, ``1 <= |letter| <= n``, matching the notation
x_1, ..., x_n of the problem statement.  Positions in a tuple of relators
are also 1-based.

Nothing in this module uses randomness.  Every function is deterministic.
Written for Python 3.12; no dependencies outside the standard library.
"""

from __future__ import annotations

import itertools
import math

# x, y, z first so that ranks 2 and 3 print the way the problem states them.
LETTERS = "xyzuvwabcdefghijklmnopqrst"


# --------------------------------------------------------------------------
# words
# --------------------------------------------------------------------------

def identity():
    """The empty word, i.e. the identity element."""
    return ()


def generators(n):
    """The tuple (1, 2, ..., n) of generator labels."""
    if n < 1:
        raise ValueError("rank must be at least 1")
    return tuple(range(1, n + 1))


def check_word(w, n=None):
    """Raise ValueError unless w is a tuple of nonzero ints with |letter| <= n."""
    if not isinstance(w, tuple):
        raise ValueError("a word must be a tuple of ints, got %r" % (w,))
    for a in w:
        if not isinstance(a, int) or isinstance(a, bool):
            raise ValueError("letters must be ints, got %r" % (a,))
        if a == 0:
            raise ValueError("letter 0 is not a generator")
        if n is not None and abs(a) > n:
            raise ValueError("letter %d out of range for rank %d" % (a, n))
    return w


def is_reduced(w):
    """True when no entry is the negation of the next entry."""
    for a, b in zip(w, w[1:]):
        if a == -b:
            return False
    return True


def reduce_word(w):
    """Free reduction of an arbitrary tuple of nonzero ints."""
    stack = []
    for a in w:
        if a == 0:
            raise ValueError("letter 0 is not a generator")
        if stack and stack[-1] == -a:
            stack.pop()
        else:
            stack.append(a)
    return tuple(stack)


def inverse(w):
    """Inverse word: reverse the letters and negate them.  Reduces nothing."""
    return tuple(-a for a in reversed(w))


def mul(a, b):
    """Product of two (not necessarily reduced) words, reduced."""
    return reduce_word(tuple(a) + tuple(b))


def conjugate(w, g):
    """g * w * g^{-1}, reduced."""
    return reduce_word(tuple(g) + tuple(w) + inverse(tuple(g)))


def commutator(a, b):
    """a b a^{-1} b^{-1}, reduced."""
    return reduce_word(tuple(a) + tuple(b) + inverse(tuple(a)) + inverse(tuple(b)))


def length(w):
    """Number of letters."""
    return len(w)


def total_length(rs):
    """Sum of the lengths of a tuple of relators."""
    return sum(len(r) for r in rs)


def exp_sums(w, n):
    """Exponent sum vector of w in Z^n: entry i counts x_i minus x_i^{-1}."""
    v = [0] * n
    for a in w:
        if abs(a) > n:
            raise ValueError("letter %d out of range for rank %d" % (a, n))
        v[abs(a) - 1] += 1 if a > 0 else -1
    return tuple(v)


def exp_sum_matrix(rs, n):
    """The n x n integer matrix whose rows are the exponent sums of the relators."""
    if len(rs) != n:
        raise ValueError("expected %d relators, got %d" % (n, len(rs)))
    return tuple(exp_sums(r, n) for r in rs)


def is_cyclically_reduced(w):
    """True when w is reduced and the last letter is not the inverse of the first."""
    if not is_reduced(w):
        return False
    if len(w) < 2:
        return True
    return w[0] != -w[-1]


def cyclic_permutation(w, k):
    """The k-th cyclic permutation of a cyclically reduced word w (k mod len)."""
    if not is_cyclically_reduced(w):
        raise ValueError("cyclic permutation needs a cyclically reduced word")
    if not w:
        return ()
    k %= len(w)
    return w[k:] + w[:k]


# --------------------------------------------------------------------------
# printing and parsing
# --------------------------------------------------------------------------

def format_word(w):
    """Printable form: generators as x, y, z, ... and inverses as X, Y, Z, ..."""
    out = []
    for a in w:
        if abs(a) > len(LETTERS):
            raise ValueError("cannot print letter %d" % a)
        c = LETTERS[abs(a) - 1]
        out.append(c if a > 0 else c.upper())
    return "".join(out)


def format_tuple(rs):
    """Printable form of a tuple of relators, e.g. (xyxYXY, xxxYYYY)."""
    return "(" + ", ".join(format_word(r) for r in rs) + ")"


def parse_word(text):
    """Inverse of format_word, ignoring spaces and '*' and '_'.

    'x' is x_1, 'X' is x_1^{-1}, 'y' is x_2, and so on.  The empty string
    is the identity.
    """
    out = []
    for c in text:
        if c in " \t\n*_":
            continue
        low = c.lower()
        if low not in LETTERS:
            raise ValueError("unknown letter %r in %r" % (c, text))
        g = LETTERS.index(low) + 1
        out.append(g if c == low else -g)
    return reduce_word(tuple(out))


# --------------------------------------------------------------------------
# enumeration
# --------------------------------------------------------------------------

def count_words(n, max_len):
    """Number of reduced words of length at most max_len in F_n.

    This is 1 + sum_{k=1}^{max_len} 2n (2n-1)^{k-1}.
    """
    if n < 1:
        raise ValueError("rank must be at least 1")
    if max_len < 0:
        raise ValueError("max_len must be nonnegative")
    total = 1
    layer = 2 * n
    for _ in range(max_len):
        total += layer
        layer *= (2 * n - 1)
    return total


def all_words(n, max_len):
    """All reduced words of length at most max_len, ordered by (length, letters).

    The list is deterministic and starts with the empty word.
    """
    generators(n)
    result = [()]
    layer = [()]
    letters = tuple(range(1, n + 1)) + tuple(range(-1, -n - 1, -1))
    for _ in range(max_len):
        nxt = []
        for w in layer:
            last = w[-1] if w else None
            for g in letters:
                if last is not None and g == -last:
                    continue
                nxt.append(w + (g,))
        layer = sorted(nxt)
        result.extend(layer)
    return result


# --------------------------------------------------------------------------
# exact integer linear algebra
# --------------------------------------------------------------------------

def det_int(mat):
    """Exact determinant of a square integer matrix (Bareiss, fraction free)."""
    A = [list(row) for row in mat]
    n = len(A)
    for row in A:
        if len(row) != n:
            raise ValueError("det_int needs a square matrix")
    if n == 0:
        return 1
    if n == 1:
        return A[0][0]
    if n == 2:
        return A[0][0] * A[1][1] - A[0][1] * A[1][0]
    if n == 3:
        return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
                - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
                + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))
    sign = 1
    prev = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
        if prev == 0:
            return 0
        for i in range(k + 1, n):
            A[i][k] = 0
    return sign * A[n - 1][n - 1]


def is_unimodular(mat):
    """True when mat is square and its determinant is +1 or -1."""
    if len(mat) == 0 or any(len(row) != len(mat) for row in mat):
        return False
    return det_int(mat) in (1, -1)


def _minors(mat, k):
    """All k by k minors of an integer matrix, as lists of lists."""
    m = len(mat)
    n = len(mat[0]) if m else 0
    for rows in itertools.combinations(range(m), k):
        for cols in itertools.combinations(range(n), k):
            yield [[mat[i][j] for j in cols] for i in rows]


def smith_elementary_divisors(mat):
    """Elementary divisors d_1 | d_2 | ... of an integer matrix.

    Computed from the definition: let e_k be the gcd of the absolute values of
    all k by k minors, with e_0 = 1.  Then e_k is the product of the first k
    elementary divisors, so the k-th elementary divisor is e_k / e_{k-1}.  The
    sequence stops at the rank.  For a square matrix with nonzero determinant
    the product of the list is |det|.

    The definition is used directly rather than an elimination algorithm
    because it is short enough to check by eye, and the matrices here have at
    most three or four rows.
    """
    A = [[int(x) for x in row] for row in mat]
    m = len(A)
    for row in A:
        if len(row) != len(A[0]):
            raise ValueError("ragged matrix")
    r = min(m, len(A[0])) if m else 0
    out = []
    prev = 1
    for k in range(1, r + 1):
        g = 0
        for block in _minors(A, k):
            g = math.gcd(g, abs(det_int(block)))
        if g == 0:
            break
        out.append(g // prev)
        prev = g
    return tuple(out)


def smith_invariant(mat):
    """A hashable normal form of an integer matrix up to row and column operations.

    Two matrices have the same elementary divisors exactly when they have the
    same Smith normal form.  This is used as a cheap AC invariant.
    """
    return smith_elementary_divisors(mat)
