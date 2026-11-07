#!/usr/bin/env python3
"""Exact census of Andrews-Curtis graphs Delta_k(G) of small finite groups.

Context (survey/nielsen.md, direction D5: Nielsen equivalence and the finite
analogue of the Andrews-Curtis moves).

For a group G and k >= 1, Borovik, Lubotzky and Myasnikov ("The finitary
Andrews-Curtis conjecture", Progr. Math. 248 (2005) 15-30) define the
Andrews-Curtis graph Delta_k(G): vertices are the normally generating
k-tuples of G, and two tuples are adjacent if one is obtained from the other
by one of

  (N1)  x_i -> x_i x_j^{+-1}        (i != j)
  (N2)  x_i -> x_j^{+-1} x_i        (i != j)
  (N3)  x_i -> x_i^{-1}
  (N4)  x_i -> w^{-1} x_i w         for w in a fixed set S subset of G.

Moves (N1)-(N3) are the elementary Nielsen moves; (N1)-(N3) alone give the
Nielsen graph whose components are the T_k-systems (Nielsen classes) of G.
Adding (N4) gives the exact finite analogue of the Andrews-Curtis moves.

This script computes those components exactly, from the definitions, for a
list of small groups, and checks on them the published statements:

  * B-L-M Theorem 1.1: for finite G and k >= max{d_G(G), 2}, the components of
    Delta_k(G) are exactly the preimages of the components of Delta_k(Ab G);
  * B-L-M Corollary (their remark after Theorem 1.1): the Akbulut-Kirby pairs
    (xyx(yxy)^-1, x^3 y^-4) and (x, y) lie in the same component for every
    homomorphism into a finite group, so finite groups cannot refute the
    Andrews-Curtis conjecture this way;
  * Diaconis-Graham (Colloq. Math. 80 (1999) 31-38): for an abelian group
    Z/m_1 x ... x Z/m_n with m_n | ... | m_1, the transvection graph on
    generating n-tuples has phi(m_n) components.

The list of groups is A_5, A_4, S_3, D_8, Q_8, the Heisenberg group of order 125,
S_5 and six abelian groups.  Two conventions for "generating" are treated
separately: normal generation (the convention of the Andrews-Curtis graph of a
group) and ordinary generation (the convention of Nielsen classes and of the
product replacement graph).  For the Nielsen classes the script computes both
the Aut(F_k)-orbits and the orbits under Aut(G) as well, since Dunwoody's
T-systems use the second convention.

Everything is deterministic; the standard library is enough.
Run: python3 nielsen_census.py            (full run, a few minutes)
     python3 nielsen_census.py --fast     (skips S_5 and the k = 3 cases)
"""

import hashlib
import itertools
import json
import math
import os
import sys

# ---------------------------------------------------------------- permutations


def pcomp(p, q):
    """composition: (p o q)(i) = p[q[i]]"""
    return tuple(p[q[i]] for i in range(len(p)))


def pinv(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def pcycle(cyc, n):
    p = list(range(n))
    for i in range(len(cyc)):
        p[cyc[i]] = cyc[(i + 1) % len(cyc)]
    return tuple(p)


# ---------------------------------------------------------------------- groups


class Table(object):
    """A finite group given by its full multiplication table."""

    def __init__(self, name, elems, mul, one, perm_rep=False):
        self.name = name
        self.perm_rep = perm_rep
        self.elems = elems
        self.m = len(elems)
        self.mul = mul
        self.one = one
        self.inv = []
        for i in range(self.m):
            cand = [j for j in range(self.m)
                    if mul[i][j] == one and mul[j][i] == one]
            assert len(cand) == 1, (name, i)
            self.inv.append(cand[0])

    def order(self):
        return self.m

    def elem_str(self, x):
        """cycle notation for permutation groups, tuple notation otherwise"""
        e = self.elems[x]
        if self.perm_rep:
            n = len(e)
            seen = [False] * n
            out = []
            for i in range(n):
                if seen[i] or e[i] == i:
                    seen[i] = True
                    continue
                cyc, j = [], i
                while not seen[j]:
                    seen[j] = True
                    cyc.append(j)
                    j = e[j]
                out.append("(" + "".join(str(y + 1) for y in cyc) + ")")
            return "".join(out) if out else "e"
        return "".join(str(y) for y in e)


def table_of_permutations(name, degree, gens):
    ident = tuple(range(degree))
    elems = {ident}
    frontier = [ident]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = pcomp(x, g)
                if y not in elems:
                    elems.add(y)
                    new.append(y)
        frontier = new
    elems = sorted(elems)
    idx = {e: i for i, e in enumerate(elems)}
    mul = [[idx[pcomp(a, b)] for b in elems] for a in elems]
    return Table(name, elems, mul, idx[ident], perm_rep=True)


def table_of_abelian(name, moduli):
    elems = list(itertools.product(*[range(mm) for mm in moduli]))
    idx = {e: i for i, e in enumerate(elems)}
    m = len(elems)
    mul = [[0] * m for _ in range(m)]
    for i, a in enumerate(elems):
        for j, b in enumerate(elems):
            mul[i][j] = idx[tuple((x + y) % mm
                                  for x, y, mm in zip(a, b, moduli))]
    return Table(name, elems, mul, idx[tuple(0 for _ in moduli)])


def table_of_quaternion():
    """Q8 as pairs (a,b) = i^a j^b, a in Z/4, b in Z/2, with j^2 = i^2."""
    elems = [(a, b) for b in range(2) for a in range(4)]
    idx = {e: i for i, e in enumerate(elems)}
    def mult(x, y):
        a, b = x
        c, d = y
        a1 = (a + (c if b == 0 else -c) + (2 if (b == 1 and d == 1) else 0)) % 4
        return (a1, (b + d) % 2)
    m = len(elems)
    mul = [[idx[mult(a, b)] for b in elems] for a in elems]
    return Table("Q8", elems, mul, idx[(0, 0)])


def table_of_heisenberg(p):
    """the Heisenberg group of upper unitriangular 3x3 matrices over Z/p,
    elements (a,b,c) with (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a b'), order p^3"""
    elems = [(a, b, c) for b in range(p) for a in range(p) for c in range(p)]
    idx = {e: i for i, e in enumerate(elems)}

    def mult(x, y):
        a, b, c = x
        d, e, f = y
        return ((a + d) % p, (b + e) % p, (c + f + a * e) % p)

    mul = [[idx[mult(a, b)] for b in elems] for a in elems]
    return Table("Heis%d" % p, elems, mul, idx[(0, 0, 0)])


def check_group_axioms(t):
    m = t.m
    ok = all(t.mul[t.one][a] == a and t.mul[a][t.one] == a for a in range(m))
    for a in range(m):
        for b in range(m):
            ab = t.mul[a][b]
            for c in range(m):
                if t.mul[ab][c] != t.mul[a][t.mul[b][c]]:
                    ok = False
    for a in range(m):
        if t.mul[a][t.inv[a]] != t.one or t.mul[t.inv[a]][a] != t.one:
            ok = False
    return ok


# ------------------------------------------- subgroups, normal closures, Ab(G)


class Structure(object):
    def __init__(self, t):
        self.t = t
        self.m = t.m
        self.full = (1 << t.m) - 1
        self._cache = {}

    def bits(self, xs):
        b = 0
        for x in xs:
            b |= 1 << x
        return b

    def gen_subgroup(self, gen_bits):
        if gen_bits in self._cache:
            return self._cache[gen_bits]
        t = self.t
        gens = [i for i in range(self.m) if (gen_bits >> i) & 1]
        seen = 1 << t.one
        frontier = [t.one]
        while frontier:
            new = []
            for x in frontier:
                for g in gens:
                    y = t.mul[x][g]
                    if not (seen >> y) & 1:
                        seen |= 1 << y
                        new.append(y)
            frontier = new
        self._cache[gen_bits] = seen
        return seen

    def conj_class_bits(self, x):
        t = self.t
        return self.bits(t.mul[t.mul[h][x]][t.inv[h]] for h in range(self.m))

    def precompute(self):
        self.nc = [self.gen_subgroup(self.conj_class_bits(x)) for x in range(self.m)]

    def normal_closure(self, tup):
        b = 0
        for x in tup:
            b |= self.nc[x]
        return self.gen_subgroup(b)

    def normally_generates(self, tup):
        return self.normal_closure(tup) == self.full

    def generates(self, tup):
        return self.gen_subgroup(self.bits(tup)) == self.full

    def abelianisation(self):
        t = self.t
        comms = 0
        for a in range(self.m):
            for b in range(self.m):
                c = t.mul[t.mul[t.mul[a][b]][t.inv[a]]][t.inv[b]]
                comms |= 1 << c
        sub = self.gen_subgroup(comms)
        coset_of = [-1] * self.m
        reps = []
        for a in range(self.m):
            if coset_of[a] >= 0:
                continue
            cid = len(reps)
            reps.append(a)
            for x in range(self.m):
                if (sub >> t.mul[t.inv[a]][x]) & 1:
                    coset_of[x] = cid
        nc = len(reps)
        mul = [[coset_of[t.mul[reps[i]][reps[j]]] for j in range(nc)]
               for i in range(nc)]
        elems = list(range(nc))
        return Table(t.name + "/[G,G]", elems, mul, coset_of[t.one]), coset_of

    def minimal_normal_generators(self):
        if any(self.normally_generates((x,)) for x in range(self.m)):
            return 1
        for a in range(self.m):
            for b in range(self.m):
                if self.normally_generates((a, b)):
                    return 2
        return 3

    def generating_set(self):
        """a generating set of minimal size (kept small: it indexes Aut(G))"""
        for d in range(1, min(self.m, 4) + 1):
            for cand in itertools.combinations(range(self.m), d):
                if self.gen_subgroup(self.bits(cand)) == self.full:
                    return list(cand)
        raise RuntimeError("no generating set found")


# --------------------------------------------------------------- AC graphs


def neighbours(t, tup, k, conjugators, with_conjugation, with_inversion=True,
               with_permutations=False):
    """the neighbours of a k-tuple under the moves (N1)-(N4)

    with_permutations adds the coordinate transpositions (0 1), (1 2), ...,
    which are Nielsen transformations; with them the move group is all of
    Aut(F_k), so the classes are the Nielsen classes of McCullough-Wanderley.
    """
    out = []
    for i in range(k):
        xi = tup[i]
        if with_inversion:
            out.append(tup[:i] + (t.inv[xi],) + tup[i + 1:])
        for j in range(k):
            if i == j:
                continue
            xj = tup[j]
            xji = t.inv[xj]
            out.append(tup[:i] + (t.mul[xi][xj],) + tup[i + 1:])
            out.append(tup[:i] + (t.mul[xi][xji],) + tup[i + 1:])
            out.append(tup[:i] + (t.mul[xj][xi],) + tup[i + 1:])
            out.append(tup[:i] + (t.mul[xji][xi],) + tup[i + 1:])
        if with_conjugation:
            for w in conjugators:
                wi = t.inv[w]
                out.append(tup[:i] + (t.mul[t.mul[wi][xi]][w],) + tup[i + 1:])
    if with_permutations:
        for i in range(k - 1):
            l = list(tup)
            l[i], l[i + 1] = l[i + 1], l[i]
            out.append(tuple(l))
    return out


def encode(tup, m):
    c = 0
    for x in tup:
        c = c * m + x
    return c


def graph_components(st, k, with_conjugation=True, conjugators=None,
                     with_inversion=True, mode="normal", with_permutations=False):
    """returns (component id per vertex code, sorted component sizes, vertices)

    mode = "normal"   : vertices are the normally generating k-tuples
                        (the convention of Borovik-Lubotzky-Myasnikov);
    mode = "generate" : vertices are the generating k-tuples
                        (the convention of Nielsen classes / T_k-systems).
    """
    t = st.t
    if conjugators is None:
        conjugators = list(range(st.m))
    pred = st.normally_generates if mode == "normal" else st.generates
    verts = [v for v in itertools.product(range(st.m), repeat=k) if pred(v)]
    vertset = set(verts)
    comp = {}
    sizes = []
    cid = 0
    for v in verts:
        if encode(v, st.m) in comp:
            continue
        comp[encode(v, st.m)] = cid
        frontier = [v]
        size = 0
        while frontier:
            new = []
            for u in frontier:
                size += 1
                for w in neighbours(t, u, k, conjugators, with_conjugation,
                                    with_inversion, with_permutations):
                    if w in vertset:
                        e = encode(w, st.m)
                        if e not in comp:
                            comp[e] = cid
                            new.append(w)
            frontier = new
        sizes.append(size)
        cid += 1
    return comp, sizes, verts


def check_moves_preserve(st, k, conjugators):
    bad = 0
    for tup in itertools.product(range(st.m), repeat=k):
        if not st.normally_generates(tup):
            continue
        for w in neighbours(st.t, tup, k, conjugators, True):
            if not st.normally_generates(w):
                bad += 1
    return bad


def same_partition(compA, compB):
    """do two label maps define the same partition of their common keys?"""
    fwd, back = {}, {}
    for key in compA:
        a, b = compA[key], compB[key]
        if fwd.setdefault(a, b) != b:
            return False
        if back.setdefault(b, a) != a:
            return False
    return True


def bfs_tree(st, gens):
    """breadth first tree of G with respect to gens: order, and for each vertex
    the (previous vertex, generator index, sign) it was reached from"""
    t = st.t
    prev = {t.one: None}
    order = [t.one]
    i = 0
    while i < len(order):
        x = order[i]
        i += 1
        for gi, g in enumerate(gens):
            for s in (1, -1):
                y = t.mul[x][g] if s == 1 else t.mul[x][t.inv[g]]
                if y not in prev:
                    prev[y] = (x, gi, s)
                    order.append(y)
    assert len(order) == st.m, (st.t.name, len(order), st.m)
    return order, prev


def automorphisms(st, gens):
    """all automorphisms of G, as tuples of images of the elements of G"""
    t = st.t
    order, prev = bfs_tree(st, gens)
    auts = []
    for images in itertools.product(range(st.m), repeat=len(gens)):
        if st.gen_subgroup(st.bits(images)) != st.full:
            continue
        phi = [0] * st.m
        phi[t.one] = t.one
        good = True
        for x in order[1:]:
            px, gi, s = prev[x]
            im = images[gi] if s == 1 else t.inv[images[gi]]
            phi[x] = t.mul[phi[px]][im]
        for x in range(st.m):
            px = phi[x]
            for gi, g in enumerate(gens):
                if phi[t.mul[x][g]] != t.mul[px][phi[g]]:
                    good = False
                    break
            if not good:
                break
        if good:
            auts.append(tuple(phi))
    return auts


def merge_orbits(comp, verts, nclasses, auts, m, vertset):
    """merge Nielsen classes that are carried into each other by Aut(G)"""
    parent = list(range(nclasses))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    reps = {}
    for v in verts:
        reps.setdefault(comp[encode(v, m)], v)
    for c, v in reps.items():
        for phi in auts:
            w = tuple(phi[x] for x in v)
            assert w in vertset
            union(c, comp[encode(w, m)])
    roots = sorted({find(c) for c in range(nclasses)})
    return len(roots)


def phi(n):
    """Euler phi"""
    r, x, p = n, n, 2
    while p * p <= x:
        if n % p == 0:
            while n % p == 0:
                n //= p
            r -= r // p
        p += 1
    if n > 1:
        r -= r // n
    return r


# --------------------------------------------------------------- the groups


def small_groups(fast):
    g = []
    g.append(table_of_permutations(
        "A5", 5, [pcycle([0, 1, 2, 3, 4], 5), pcycle([0, 1, 2], 5)]))
    g.append(table_of_permutations(
        "A4", 4, [pcycle([0, 1, 2], 4),
                  pcomp(pcycle([0, 1], 4), pcycle([2, 3], 4))]))
    g.append(table_of_permutations(
        "S3", 3, [pcycle([0, 1, 2], 3), pcycle([0, 1], 3)]))
    g.append(table_of_permutations(
        "D8", 4, [pcycle([0, 1, 2, 3], 4), pcycle([1, 3], 4)]))
    g.append(table_of_quaternion())
    g.append(table_of_heisenberg(5))
    if not fast:
        g.append(table_of_permutations(
            "S5", 5, [pcycle([0, 1, 2, 3, 4], 5), pcycle([0, 1], 5)]))
    g.append(table_of_abelian("C2xC2", [2, 2]))
    g.append(table_of_abelian("C4xC4", [4, 4]))
    g.append(table_of_abelian("C2xC4", [2, 4]))
    g.append(table_of_abelian("C3xC3", [3, 3]))
    g.append(table_of_abelian("C2xC2xC2", [2, 2, 2]))
    return g


def main():
    fast = "--fast" in sys.argv
    lines = []

    def say(s):
        print(s)
        lines.append(s)

    say("Exact census of Andrews-Curtis graphs Delta_k(G) of small finite groups")
    say("deterministic, standard library only, no randomness")
    say("")

    results = {}
    groups = small_groups(fast)

    for t in groups:
        st = Structure(t)
        st.precompute()
        say("group %s, order %d" % (t.name, t.m))
        say("  group axioms hold: %s"
            % ("PASS" if check_group_axioms(t) else "FAIL"))
        dg = st.minimal_normal_generators()
        ab, coset_of = st.abelianisation()
        st_ab = Structure(ab)
        st_ab.precompute()
        say("  Ab(G) = %s, order %d; minimal number of normal generators d_G(G) = %d"
            % (ab.name, ab.m, dg))
        S = st.generating_set()
        auts = automorphisms(st, S)
        rec = {"order": t.m, "dG": dg, "ab_order": ab.m, "ab_gens": len(S),
               "aut_order": len(auts)}
        ks = [2] + ([3] if (t.m <= 60 and not fast) else [])
        for k in ks:
            if k < max(dg, 2):
                continue
            compG, sizesG, verts = graph_components(st, k)
            compS, sizesS, _ = graph_components(st, k, conjugators=S)
            compN, sizesN, _ = graph_components(st, k, with_conjugation=False)
            compA, sizesA, _ = graph_components(st_ab, k, with_conjugation=False)
            compGn, sizesGn, vertsGn = graph_components(st, k, mode="generate")
            compNn, sizesNn, _ = graph_components(st, k, with_conjugation=False,
                                                 mode="generate")
            compAn, sizesAn, _ = graph_components(st_ab, k,
                                                 with_conjugation=False,
                                                 mode="generate")
            say("  k = %d:" % k)
            say("    normally generating k-tuples: %d" % len(verts))
            say("    Delta_k(G) (B-L-M: normally generating, all moves): %d component(s), sizes %s"
                % (len(sizesG), sizesG))
            say("      conjugation by a generating set of size %d instead of all of G: %d component(s): %s"
                % (len(S), len(sizesS),
                   "PASS same partition" if same_partition(compG, compS) else "FAIL"))
            say("      Nielsen moves only, normally generating vertices: %d class(es), sizes %s"
                % (len(sizesN), sizesN))
            say("      Delta_k(Ab G) on normally generating vertices: %d component(s), sizes %s"
                % (len(sizesA), sizesA))
            ok_pre, ok_inj = True, True
            fwd, back = {}, {}
            for v in verts:
                av = tuple(coset_of[x] for x in v)
                cg = compG[encode(v, t.m)]
                if not st_ab.normally_generates(av):
                    ok_pre = False
                    continue
                ca = compA[encode(av, ab.m)]
                if fwd.setdefault(cg, ca) != ca:
                    ok_pre = False
                if back.setdefault(ca, cg) != cg:
                    ok_inj = False
            say("      B-L-M Theorem 1.1 (components = preimages of abelian components): %s"
                % ("PASS" if (ok_pre and ok_inj) else "FAIL"))
            compNp, sizesNp, _ = graph_components(st, k, with_conjugation=False,
                                                 mode="generate",
                                                 with_permutations=True)
            tksys = merge_orbits(compNp, vertsGn, len(sizesNp), auts, t.m,
                                 set(vertsGn))
            say("    generating k-tuples: %d" % len(vertsGn))
            say("      Nielsen moves (N1)-(N3), generating vertices: %d class(es), sizes %s"
                % (len(sizesNn), sizesNn))
            say("      with coordinate permutations too (Aut(F_%d)-orbits, McCullough-Wanderley): %d class(es), sizes %s"
                % (k, len(sizesNp), sizesNp))
            say("      |Aut(G)| = %d; classes modulo Aut(G) (Dunwoody T_%d-systems): %d"
                % (len(auts), k, tksys))
            say("      all AC moves, generating vertices: %d component(s), sizes %s"
                % (len(sizesGn), sizesGn))
            say("      Nielsen moves only, in Ab G, generating vertices: %d class(es), sizes %s"
                % (len(sizesAn), sizesAn))
            rec["k=%d" % k] = {
                "normally_generating_tuples": len(verts),
                "blm_components": len(sizesG),
                "blm_component_sizes": sorted(sizesG, reverse=True),
                "blm_components_generating_set_only": len(sizesS),
                "nielsen_classes_normal": len(sizesN),
                "nielsen_sizes_normal": sorted(sizesN, reverse=True),
                "abelian_components_normal": len(sizesA),
                "abelian_sizes_normal": sorted(sizesA, reverse=True),
                "blm_preimages": bool(ok_pre and ok_inj),
                "generating_tuples": len(vertsGn),
                "t_k_systems": len(sizesNn),
                "nielsen_aut_f": len(sizesNp),
                "nielsen_aut_f_sizes": sorted(sizesNp, reverse=True),
                "aut_g_order": len(auts),
                "t_k_systems_mod_aut_g": tksys,
                "t_k_sizes": sorted(sizesNn, reverse=True),
                "ac_components_generating": len(sizesGn),
                "ac_component_sizes_generating": sorted(sizesGn, reverse=True),
                "abelian_t_k_systems": len(sizesAn),
            }
            if len(sizesNn) <= 12:
                reps = {}
                for v in vertsGn:
                    reps.setdefault(compNn[encode(v, t.m)], v)
                say("      Nielsen class representatives of generating tuples: %s"
                    % "; ".join(
                        "[" + ",".join(t.elem_str(x) for x in reps[c]) + "]"
                        for c in sorted(reps)))
            if t.m <= 12:
                bad = check_moves_preserve(st, k, S)
                badg = 0
                for tup in itertools.product(range(st.m), repeat=k):
                    if not st.generates(tup):
                        continue
                    for w in neighbours(t, tup, k, S, False):
                        if not st.generates(w):
                            badg += 1
                say("      every AC move preserves normal generation: %s; every Nielsen move preserves generation: %s"
                    % ("PASS" if bad == 0 else "FAIL",
                       "PASS" if badg == 0 else "FAIL"))
        results[t.name] = rec
        say("")

    say("Diaconis-Graham check.  For A = Z/m_1 x ... x Z/m_n with")
    say("m_n | ... | m_1 the transvection graph on generating n-tuples has")
    say("phi(m_n) components (Colloq. Math. 80 (1999) 31-38, Theorem).")
    for moduli in ([2, 2], [4, 4], [2, 4], [3, 3], [5, 5], [8, 8], [6, 6],
                   [2, 2, 2], [2, 2, 4]):
        t = table_of_abelian("A", moduli)
        st = Structure(t)
        st.precompute()
        k = len(moduli)
        comp, sizes, verts = graph_components(st, k, with_conjugation=False,
                                             with_inversion=False)
        compI, sizesI, _ = graph_components(st, k, with_conjugation=False)
        mn = min(moduli)
        say("  A = Z/%s: generating %d-tuples %d, transvection components %d, phi(%d) = %d: %s"
            % (",Z/".join(map(str, moduli)), k, len(verts), len(sizes), mn,
               phi(mn), "PASS" if len(sizes) == phi(mn) else "FAIL"))
        say("        with inversion of coordinates allowed: %d component(s) %s"
            % (len(sizesI), sizesI))

    say("")
    say("Akbulut-Kirby AK(3) = <x,y | xyx = yxy, x^3 = y^4>, evaluated in")
    say("finite groups.  For u = xyx(yxy)^-1 and v_3 = x^3 y^-4, the images of")
    say("(u, v_3) and of (x, y) are AC-equivalent in every finite group (B-L-M,")
    say("corollary after Theorem 1.1), so no finite group refutes the conjecture")
    say("this way.  Rechecked here over all normally generating pairs.")
    for t in groups:
        if t.m < 6 or t.m > 120:
            continue
        st = Structure(t)
        st.precompute()
        comp, sizes, verts = graph_components(st, 2)
        if not verts:
            continue
        ok, bad = 0, 0
        for (a, b) in verts:
            u = t.mul[t.mul[a][b]][a]
            u = t.mul[u][t.inv[t.mul[t.mul[b][a]][b]]]
            cube = t.mul[t.mul[a][a]][a]
            fourth = t.mul[t.mul[t.mul[b][b]][b]][b]
            v = t.mul[cube][t.inv[fourth]]
            w = (u, v)
            if (not st.normally_generates(w)) or \
               comp[encode(w, t.m)] != comp[encode((a, b), t.m)]:
                bad += 1
            else:
                ok += 1
        say("  G = %s: normally generating pairs %d, in the same component %d, not %d: %s"
            % (t.name, len(verts), ok, bad, "PASS" if bad == 0 else "FAIL"))

    say("")
    say("Two facts about the conjugation move on ordinary generation, checked by")
    say("exhaustion over all pairs and all conjugating elements.")
    for t in groups:
        if t.name not in ("A5", "S5", "Heis5"):
            continue
        st = Structure(t)
        st.precompute()
        first = None
        destroyed = 0
        for (a, b) in itertools.product(range(t.m), repeat=2):
            if not st.generates((a, b)):
                continue
            for w in range(t.m):
                c = t.mul[t.mul[w][a]][t.inv[w]]
                if not st.generates((c, b)):
                    destroyed += 1
                    if first is None:
                        first = (a, b, w, c)
        if first is None:
            say("  G = %s: no single-entry conjugation destroys generation of a generating pair"
                % t.name)
        else:
            a, b, w, c = first
            say("  G = %s: %d of the single-entry conjugations of generating pairs fail to generate;"
                % (t.name, destroyed))
            say("        first example: a = %s, b = %s, w = %s, w a w^-1 = %s"
                % (t.elem_str(a), t.elem_str(b), t.elem_str(w), t.elem_str(c)))

    body = "\n".join(lines)
    digest = hashlib.sha256(body.encode()).hexdigest()
    say("")
    say("SHA-256 of this report: %s" % digest)
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "nielsen_census.out.txt"), "w") as f:
        f.write(body + "\n")
    with open(os.path.join(here, "nielsen_census.json"), "w") as f:
        json.dump(results, f, indent=1, sort_keys=True)
        f.write("\n")


if __name__ == "__main__":
    main()
