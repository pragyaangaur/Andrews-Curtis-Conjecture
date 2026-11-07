"""An explicit Andrews-Curtis trivialization of AK(1), checked move by move.

AK(1) = <x,y | x = y^2, xyx = yxy> is the n = 1 member of the Akbulut-Kirby
family.  As a relator pair in F_2 = <x,y> it is

  (x y^-2, x y x y^-1 x^-1 y^-1).

Below is a sequence of 19 elementary AC moves that carries it to (x, y).
Each step is checked independently by the verifier at the bottom: the step
must be one of
  AC1  r_i -> r_i^-1,
  AC2  r_i -> r_i r_j   or   r_i -> r_i r_j^-1   with j != i,
  AC3  r_i -> w r_i w^-1  for a word w (found by search over short w).
Words are tuples of nonzero ints: 1 = x, 2 = y, -1 = x^-1, -2 = y^-1.
"""
import itertools, sys

def red(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)

def inv(w):
    return tuple(-a for a in reversed(w))

def mul(u, v):
    return red(tuple(u) + tuple(v))

def conj(w, u):
    return mul(mul(w, u), inv(w))

def is_conjugation(a, b, maxlen=8):
    """Is b = w a w^-1 for some reduced word w with |w| <= maxlen?"""
    for k in range(0, maxlen + 1):
        for letters in itertools.product((1, 2, -1, -2), repeat=k):
            w = red(letters)
            if len(w) != k:
                continue
            if conj(w, a) == b:
                return w
    return None

def check_step(a, b):
    """Return the name and the move that takes pair a to pair b, or None."""
    if len(a) != 2 or len(b) != 2:
        return None
    changed = [i for i in (0, 1) if a[i] != b[i]]
    if len(changed) != 1:
        return None
    i = changed[0]
    j = 1 - i
    if b[j] != a[j]:
        return None
    if b[i] == inv(a[i]):
        return ("AC1", i, None)
    if b[i] == mul(a[i], a[j]):
        return ("AC2", i, "+")
    if b[i] == mul(a[i], inv(a[j])):
        return ("AC2", i, "-")
    w = is_conjugation(a[i], b[i])
    if w is not None:
        return ("AC3", i, w)
    return None

# the sequence of moves, written as (relator index, kind, data)
X, Y = (1,), (2,)
B1 = red((2, 1, -2, -1, -2))          # B  = y x y^-1 x^-1 y^-1  (r2 = x * B)
B1i = inv(B1)                          # B^-1
B2 = red((-2, -1, -2))                 # B  = y^-1 x^-1 y^-1
B2i = inv(B2)

MOVES = [
    (0, "inv", None),                  # 1  r1 -> y^2 x^-1
    (0, "conj", (-1,)),                # 2  r1 -> x^-1 y^2
    (0, "conj", B1i),                  # 3  r1 -> B^-1 x^-1 y^2 B
    (1, "mul", 0),                     # 4  r2 -> y^3 x y^-1 x^-1 y^-1
    (0, "conj", B1),                   # 5  undo 3
    (0, "conj", (1,)),                 # 6  undo 2
    (0, "inv", None),                  # 7  undo 1, r1 = x y^-2 again
    (0, "inv", None),                  # 8  r1 -> y^2 x^-1
    (0, "conj", (-1,)),                # 9  r1 -> x^-1 y^2
    (0, "conj", B2i),                  # 10 r1 -> B^-1 x^-1 y^2 B
    (1, "mul", 0),                     # 11 r2 -> y^4 x^-1 y^-1
    (0, "conj", B2),                   # 12 undo 10
    (0, "conj", (1,)),                 # 13 undo 9
    (0, "inv", None),                  # 14 undo 8, r1 = x y^-2
    (0, "conj", (2,)),                 # 15 r1 -> y x y^-3
    (1, "mul", 0),                     # 16 r2 -> y
    (0, "conj", (-2,)),                # 17 undo 15, r1 = x y^-2
    (0, "mul", 1),                     # 18 r1 -> x y^-1
    (0, "mul", 1),                     # 19 r1 -> x
]

def apply_move(state, mv):
    i, kind, data = mv
    r = list(state)
    if kind == "inv":
        r[i] = inv(r[i])
    elif kind == "conj":
        r[i] = conj(data, r[i])
    elif kind == "mul":
        r[i] = mul(r[i], r[data])
    else:
        raise ValueError(kind)
    return tuple(r)

def main():
    start = (red((1, -2, -2)), red((1, 2, 1, -2, -1, -2)))
    goal = (X, Y)
    print("start:", start)
    state = start
    ok = True
    for n, mv in enumerate(MOVES, 1):
        nxt = apply_move(state, mv)
        chk = check_step(state, nxt)
        if chk is None:
            print("  step %2d %-18s FAILS: not an elementary AC move" % (n, str(mv)))
            ok = False
            break
        print("  step %2d %-4s relator r%d %-22s -> %s" % (n, chk[0], chk[1] + 1, str(state[chk[1]]), str(nxt[chk[1]])))
        state = nxt
        if state == goal:
            print("  reached the standard presentation after %d moves" % n)
            break
    print("final:", state)
    print("total moves:", len(MOVES))
    print("CERTIFICATE OK" if (ok and state == goal) else "CERTIFICATE FAILED")
    return 0 if (ok and state == goal) else 1

if __name__ == "__main__":
    sys.exit(main())
