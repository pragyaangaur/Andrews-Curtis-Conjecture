"""HNN normal-form reduction for the one-relator group G = <x,y | A_n>.

A_n = x^-1 y^n x y^-(n+1).  Put t = x^-1; then t y^n t^-1 = y^(n+1), so
G = <y,t | t y^n t^-1 = y^(n+1)> is an ascending HNN extension of Z with
stable letter t, associated subgroups nZ and (n+1)Z.  Britton's lemma gives: a
freely reduced word is trivial iff it can be reduced to the empty word by the
two replacements

    x^-1 y^m x  ->  y^(m(n+1)/n)   when n divides m
    x     y^m x^-1 -> y^(m n/(n+1)) when (n+1) divides m

(m any nonzero integer).  Each replacement preserves the group element and
shortens the word, so this decides the word problem in G, hence membership in
the normal closure N(A_n) of the single relator.
"""


def reduce_free(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def inv(w):
    return tuple(-a for a in reversed(w))


def mul(a, b):
    return reduce_free(tuple(a) + tuple(b))


def reduce_G(w, n, trace=False):
    """Return the Britton-reduced form of w in G; empty tuple iff trivial."""
    w = list(reduce_free(w))
    while True:
        changed = False
        out = []
        i = 0
        while i < len(w):
            if w[i] in (1, -1):
                s = w[i]
                j = i + 1
                m = 0
                while j < len(w) and w[j] in (2, -2):
                    m += 1 if w[j] == 2 else -1
                    j += 1
                if m != 0 and j < len(w) and w[j] == -s:
                    if s == -1 and m % n == 0:
                        e = m * (n + 1) // n
                        out.extend([2 if e > 0 else -2] * abs(e))
                        i = j + 1
                        changed = True
                        if trace:
                            print("  red x^-1 y^%d x -> y^%d" % (m, e))
                        continue
                    if s == 1 and m % (n + 1) == 0:
                        e = m * n // (n + 1)
                        out.extend([2 if e > 0 else -2] * abs(e))
                        i = j + 1
                        changed = True
                        if trace:
                            print("  red x y^%d x^-1 -> y^%d" % (m, e))
                        continue
            out.append(w[i])
            i += 1
        w = list(reduce_free(out))
        if not changed:
            return tuple(w)


def trivial_in_G(w, n):
    return reduce_G(w, n) == ()


def exp_sum(w):
    return (sum(1 for a in w if a == 1) - sum(1 for a in w if a == -1),
            sum(1 for a in w if a == 2) - sum(1 for a in w if a == -2))
