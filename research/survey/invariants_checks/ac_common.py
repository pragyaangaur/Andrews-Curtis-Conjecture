"""Shared exact free-group machinery for the Andrews-Curtis invariant checks.

Words are tuples of nonzero integers.  Letter i (1 <= i <= n) is x_i and
letter -i is x_i^{-1}.  Everything here is exact integer arithmetic.
"""


def red(w):
    """Free reduction of a word."""
    out = []
    for g in w:
        if out and out[-1] == -g:
            out.pop()
        else:
            out.append(g)
    return tuple(out)


def mul(a, b):
    return red(tuple(a) + tuple(b))


def inv(a):
    return tuple(-g for g in reversed(a))


def conj(a, w):
    """w * a * w^{-1}"""
    return mul(mul(w, a), inv(w))


def power(a, k):
    if k < 0:
        a, k = inv(a), -k
    out = ()
    for _ in range(k):
        out = mul(out, a)
    return out


def exp_sums(w, n):
    """Exponent-sum vector of a word: entry j is the sum of exponents of x_{j+1}."""
    v = [0] * n
    for g in w:
        v[abs(g) - 1] += 1 if g > 0 else -1
    return tuple(v)


def exp_matrix(rels, n):
    """n x n integer matrix whose i-th row is the exponent-sum vector of rels[i]."""
    return tuple(tuple(exp_sums(r, n)) for r in rels)


# ---------------------------------------------------------------- AC moves

def move_inv(rels, i):
    out = list(rels)
    out[i] = inv(out[i])
    return tuple(out)


def move_mul(rels, i, j):
    """r_i -> r_i * r_j  (i != j)."""
    assert i != j
    out = list(rels)
    out[i] = mul(out[i], out[j])
    return tuple(out)


def move_conj(rels, i, w):
    """r_i -> w r_i w^{-1}."""
    out = list(rels)
    out[i] = conj(out[i], w)
    return tuple(out)


# ---------------------------------------------------------------- matrices

def mat_mul_int(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return tuple(
        tuple(sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p))
        for i in range(n)
    )


def det_int(M):
    """Exact determinant of an integer matrix by fraction-free elimination."""
    n = len(M)
    A = [list(map(int, row)) for row in M]
    sign = 1
    prev = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for r in range(k + 1, n):
                if A[r][k] != 0:
                    A[k], A[r] = A[r], A[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
        for i in range(k + 1, n):
            A[i][k] = 0
    return sign * A[n - 1][n - 1]


def rank_mod_p(M, p):
    A = [[x % p for x in row] for row in M]
    rows, cols = len(A), len(A[0]) if A else 0
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv_p = pow(A[r][c], p - 2, p)
        A[r] = [(x * inv_p) % p for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] % p:
                f = A[i][c]
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(cols)]
        r += 1
    return r


# ---------------------------------------------------------------- group ring

def gr_add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + v
        if out[k] == 0:
            del out[k]
    return out


def fox_derivative(w, j):
    """Fox derivative of word w with respect to letter x_j, as a group-ring element.

    Uses d(u*x)/dx_j = du/dx_j + u*[x == x_j] and
         d(u*x^{-1})/dx_j = du/dx_j - u*x^{-1}*[x == x_j].
    """
    d = {}
    prefix = ()
    for g in w:
        if abs(g) == j:
            unit = prefix if g > 0 else mul(prefix, (g,))
            d = gr_add(d, {unit: 1 if g > 0 else -1})
        prefix = mul(prefix, (g,))
    return d


def gr_evaluate(elt, powers, t):
    """Evaluate a group-ring element in Z[t^{+-1}].

    powers maps letter index (1-based) to the exponent of t assigned to it.
    """
    total = 0
    for w, c in elt.items():
        e = sum(powers[abs(g)] if g > 0 else -powers[abs(g)] for g in w)
        total += c * t ** e
    return total
