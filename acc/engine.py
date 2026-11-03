"""Independent reference implementation of the ac-r2-v1 move set.

Written from the specification in competition/tools/verifier/README.md, not
from verifier/core.py, so that agreement between the two is evidence rather
than a copy.  Words are tuples of ints in {1,-1,2,-2}: 1=x, 2=y.
"""

GENS = (1, -1, 2, -2)


def free_reduce(word):
    out = []
    for a in word:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def invert(word):
    return tuple(-a for a in reversed(word))


def apply_move(state, m):
    """Apply atomic move m in 0..13. Returns the new freely reduced state."""
    if not isinstance(m, int) or isinstance(m, bool) or not (0 <= m <= 13):
        raise ValueError("bad move id %r" % (m,))
    r0, r1 = state
    if m == 0:
        return (invert(r0), r1)
    if m == 1:
        return (r0, invert(r1))
    if m == 2:
        return (free_reduce(r0 + r1), r1)
    if m == 3:
        return (free_reduce(r0 + invert(r1)), r1)
    if m == 4:
        return (r0, free_reduce(r1 + r0))
    if m == 5:
        return (r0, free_reduce(r1 + invert(r0)))
    if 6 <= m <= 13:
        g = GENS[(m - 6) % 4]
        if m < 10:
            return (free_reduce((g,) + r0 + (-g,)), r1)
        return (r0, free_reduce((g,) + r1 + (-g,)))
    raise ValueError("unreachable")


def replay(initial, moves):
    s = (tuple(initial[0]), tuple(initial[1]))
    for m in moves:
        s = apply_move(s, m)
    return s


# Shortest suffixes from the eight signed permutations of (x, y) to [[1],[2]],
# copied from the canonicalization_table documented in the verifier README.
CANON = {
    ((1,), (2,)): (),
    ((1,), (-2,)): (1,),
    ((-1,), (2,)): (0,),
    ((-1,), (-2,)): (0, 1),
    ((-2,), (1,)): (2, 5, 2, 8),
    ((2,), (-1,)): (3, 4, 3, 10),
    ((-2,), (-1,)): (2, 0, 4, 3),
    ((2,), (1,)): (0, 2, 5, 2, 8),
}


def canonical_suffix(state):
    return CANON.get((tuple(state[0]), tuple(state[1])))


def check_path(initial, moves, target=((1,), (2,))):
    s = (tuple(initial[0]), tuple(initial[1]))
    for i, m in enumerate(moves):
        s = apply_move(s, m)
    return s == target, s
