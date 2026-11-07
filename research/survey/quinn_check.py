#!/usr/bin/env python3
"""Exact checks for survey/quinn-tqft.md (Quinn's triangular-Hopf-algebra question).

Quinn (arXiv:hep-th/9202044, section 3) asks for a triangular Hopf algebra H over a
commutative ring R and representations V_0,...,V_n such that
  (1) each V_i carries a symmetric nondegenerate H-invariant form,
  (2) each V_i (x) V_j is a sum of copies of the V_k,
  (3) the V_i are irreducible and distinct,
  (4) the sum of the squares of their (categorical) ranks is 0.

Part A.  H = O(Z/2) over F_p, the coordinate Hopf algebra of the group of order two.
         Over F_2 this 2-dimensional semisimple commutative Hopf algebra (triangular
         with R = 1 (x) 1) has two simple modules satisfying (1)-(4): the ranks are
         1 and 1 and 1 + 1 = 0 in F_2.  Over F_p with p odd the same data give
         1 + 1 = 2, which is not 0, so (4) fails.  Conclusion: Quinn's data exist in
         characteristic 2 and not in characteristic 0.

Part B.  The Verlinde category Ver_p over F_p (Ostrik, Selecta 2020) has simples
         Lbar_1,...,Lbar_{p-1} with dim Lbar_s = s.  We check
           (i)  the explicit form beta(u,v) = tau(u iota(v)) on L_s = F_p[y]/(y^s),
                where iota(1+y) = (1+y)^(-1) and tau is the coefficient of y^(s-1),
                is invariant and nondegenerate, that beta + beta^T is a symmetric
                nondegenerate invariant form exactly when s is odd (its determinant
                over Z is 2^s), and that beta - beta^T is alternating and
                nondegenerate exactly when s is even;
           (ii) the tensor product decomposition of L_r (x) L_s agrees with
                Ostrik's published formula;
           (iii) the odd-index subcategory Ver_p^+ is closed under tensor product
                and has sum of squared dimensions (p-1)(p-2)p/6 = 0 in F_p.
         So the categorical part of Quinn's data exists in every characteristic
         p >= 5 as well, with H required to be triangular.

All arithmetic is exact in F_p.  Run: python3 quinn_check.py
"""

from itertools import product

# ------------------------------------------------------------------ F_p linalg

def mat_mul(A, B, p):
    n, m, q = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) % p for j in range(q)] for i in range(n)]

def mat_transpose(A):
    return [list(r) for r in zip(*A)]

def mat_sub(A, B, p):
    return [[(a - b) % p for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]

def mat_neg(A, p):
    return [[(-a) % p for a in r] for r in A]

def identity(n, p):
    return [[1 % p if i == j else 0 for j in range(n)] for i in range(n)]

def kron(A, B, p):
    ra, ca, rb, cb = len(A), len(A[0]), len(B), len(B[0])
    out = [[0] * (ca * cb) for _ in range(ra * rb)]
    for i in range(ra):
        for j in range(ca):
            for k in range(rb):
                for l in range(cb):
                    out[i * rb + k][j * cb + l] = A[i][j] * B[k][l] % p
    return out

def rank(A, p):
    A = [row[:] for row in A]
    rows, cols = len(A), len(A[0]) if A else 0
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i][c] % p), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], -1, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] % p:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        r += 1
        if r == rows:
            break
    return r

def kernel_basis(M, p):
    A = [row[:] for row in M]
    rows, cols = len(A), len(A[0])
    pivots, r = [], 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i][c] % p), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], -1, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] % p:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    free = [c for c in range(cols) if c not in pivots]
    basis = []
    for fc in free:
        v = [0] * cols
        v[fc] = 1
        for i, pc in enumerate(pivots):
            v[pc] = (-A[i][fc]) % p
        basis.append(v)
    return basis

# --------------------------------------------------- finite-dimensional Hopf algebra

class Hopf:
    def __init__(self, p, n, mul, com, unit, counit, anti, name=""):
        self.p, self.n, self.name = p, n, name
        self.mul, self.com, self.unit, self.counit, self.anti = mul, com, unit, counit, anti
        self.basis = [tuple(1 % p if k == i else 0 for k in range(n)) for i in range(n)]

    def mulv(self, x, y):
        out = [0] * self.n
        for a in range(self.n):
            if not x[a]:
                continue
            for b in range(self.n):
                if not y[b]:
                    continue
                coef = x[a] * y[b] % self.p
                for c in range(self.n):
                    out[c] = (out[c] + coef * self.mul[a][b][c]) % self.p
        return tuple(out)

    def comv(self, x):
        out = [[0] * self.n for _ in range(self.n)]
        for a in range(self.n):
            if not x[a]:
                continue
            for b in range(self.n):
                for c in range(self.n):
                    out[b][c] = (out[b][c] + x[a] * self.com[a][b][c]) % self.p
        return out

    def eps(self, x):
        return sum(x[i] * self.counit[i] for i in range(self.n)) % self.p

    def S(self, x):
        return tuple(x[i] * self.anti[i] % self.p for i in range(self.n))

    def check_hopf(self):
        p, n, B = self.p, self.n, self.basis
        ok = dict(assoc=True, unit=True, coassoc=True, counit_ax=True,
                  antipode=True, cocomm=True)
        for x, y, z in product(B, repeat=3):
            if self.mulv(self.mulv(x, y), z) != self.mulv(x, self.mulv(y, z)):
                ok["assoc"] = False
        u = tuple(self.unit)
        for x in B:
            if self.mulv(u, x) != x or self.mulv(x, u) != x:
                ok["unit"] = False
        for x in B:
            D = self.comv(x)
            L = [[[0] * n for _ in range(n)] for _ in range(n)]
            R = [[[0] * n for _ in range(n)] for _ in range(n)]
            for a in range(n):
                for b in range(n):
                    if not D[a][b]:
                        continue
                    Da, Db = self.comv(B[a]), self.comv(B[b])
                    for c in range(n):
                        for d in range(n):
                            L[c][d][b] = (L[c][d][b] + D[a][b] * Da[c][d]) % p
                            R[a][c][d] = (R[a][c][d] + D[a][b] * Db[c][d]) % p
            if L != R:
                ok["coassoc"] = False
            left = tuple(sum(self.eps(B[a]) * D[a][b] for a in range(n)) % p for b in range(n))
            right = tuple(sum(self.eps(B[b]) * D[a][b] for b in range(n)) % p for a in range(n))
            if left != x or right != x:
                ok["counit_ax"] = False
            acc = [0] * n
            for a in range(n):
                for b in range(n):
                    if not D[a][b]:
                        continue
                    term = self.mulv(B[a], self.S(B[b]))
                    acc = [(s + D[a][b] * t) % p for s, t in zip(acc, term)]
            if tuple(acc) != tuple(self.eps(x) * t % p for t in u):
                ok["antipode"] = False
            if any(D[a][b] != D[b][a] for a in range(n) for b in range(n)):
                ok["cocomm"] = False
        return ok

# ------------------------------------------------------ Part A: char 2 example

def o_c2(p):
    n = 2
    mul = [[[0] * n for _ in range(n)] for _ in range(n)]
    for a in range(n):
        mul[a][a][a] = 1 % p
    com = [[[0] * n for _ in range(n)] for _ in range(n)]
    for a in range(n):
        for b in range(n):
            com[a][b][(a - b) % 2] = 1 % p
    return Hopf(p, n, mul, com, [1 % p, 1 % p], [1 % p, 0], [1 % p, 1 % p], "O(Z/2)")

def module_axioms(H, lam):
    p = H.p
    for a in range(H.n):
        for b in range(H.n):
            if lam[a] * lam[b] % p != sum(H.mul[a][b][c] * lam[c] for c in range(H.n)) % p:
                return False
    return sum(H.unit[i] * lam[i] for i in range(H.n)) % p == 1

def form_invariant(H, lam, beta=1):
    p = H.p
    for a in range(H.n):
        acc = sum(H.com[a][b][c] * lam[b] * lam[c]
                  for b in range(H.n) for c in range(H.n)) % p
        if acc * beta % p != H.counit[a] * beta % p:
            return False
    return True

def part_A():
    print("=" * 78)
    print("Part A.  Quinn's conditions (1)-(4) for H = O(Z/2) over F_p")
    print("=" * 78)
    out = {}
    for p in (2, 3, 5, 7, 11):
        H = o_c2(p)
        ax = H.check_hopf()
        hopf_ok = all(ax.values())
        lams = [[1 % p if a == g else 0 for a in range(H.n)] for g in range(2)]
        mods_ok = all(module_axioms(H, lam) for lam in lams)
        forms_ok = all(form_invariant(H, lam) for lam in lams)
        fusion_ok = True
        for g in range(2):
            for h in range(2):
                act = [sum(H.com[a][b][c] * lams[g][b] * lams[h][c]
                           for b in range(H.n) for c in range(H.n)) % p for a in range(H.n)]
                if act != lams[(g + h) % 2]:
                    fusion_ok = False
        total = (1 + 1) % p
        holds = hopf_ok and mods_ok and forms_ok and fusion_ok and total == 0
        out[p] = holds
        print(f"p = {p}: Hopf axioms {ax}, cocommutative {ax['cocomm']}")
        print(f"        two simple modules V_0, V_1 of dimension 1, distinct: {mods_ok}")
        print(f"        symmetric nondegenerate invariant forms on both: {forms_ok}")
        print(f"        fusion V_g (x) V_h = V_(g+h): {fusion_ok}; ranks 1, 1")
        print(f"        sum of squared ranks in F_{p} = {total}")
        print(f"        Quinn (1)-(4) hold: {holds}")
    print()
    print("The same algebra over any field of characteristic 0 (or over Z) has")
    print("sum of squared ranks 1 + 1 = 2, which is not zero: the example is a")
    print("characteristic-2 phenomenon.")
    print()
    return out

# --------------------------------------------- Part B: Rep(C_p) and Ver_p

def Ls_action(s, p):
    M = [[0] * s for _ in range(s)]
    for i in range(s):
        M[i][i] = (M[i][i] + 1) % p
        if i + 1 < s:
            M[i + 1][i] = (M[i + 1][i] + 1) % p
    return M

def iota_coeffs(s):
    """coefficients of iota(y)^j mod y^s, where iota(y) = sum_{k>=1} (-1)^k y^k.
    iota is the algebra automorphism of k[y]/y^s sending (1+y) to (1+y)^(-1)."""
    base = [0] + [((-1) ** k) for k in range(1, s)]
    out = [[1] + [0] * (s - 1)]
    for _ in range(1, s):
        prev, new = out[-1], [0] * s
        for a in range(s):
            if prev[a] == 0:
                continue
            for b in range(s):
                if base[b] and a + b < s:
                    new[a + b] += prev[a] * base[b]
        out.append(new)
    return out

def beta_form(s, p):
    """the invariant form beta(u,v) = tau(u * iota(v)), tau(w) = [y^(s-1)]w,
    as an integer matrix reduced mod p.  beta is C_p-invariant and det(beta) = 1
    over Z."""
    ic = iota_coeffs(s)
    return [[(ic[j][s - 1 - i] if s - 1 - i >= 0 else 0) % p for j in range(s)]
            for i in range(s)]

def det_int(M):
    """exact determinant of an integer matrix (Bareiss algorithm)."""
    A = [row[:] for row in M]
    n = len(A)
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            piv = next((i for i in range(k + 1, n) if A[i][k] != 0), None)
            if piv is None:
                return 0
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
        for i in range(k + 1, n):
            A[i][k] = 0
    return sign * A[n - 1][n - 1] if n else 1

def rank_int(M):
    """exact rank over Q of an integer matrix, via sympy-free fraction-free elimination"""
    import fractions
    A = [[fractions.Fraction(x) for x in row] for row in M]
    n, m = len(A), len(A[0])
    r = 0
    for c in range(m):
        piv = next((i for i in range(r, n) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        for i in range(n):
            if i != r and A[i][c] != 0:
                f = A[i][c] / A[r][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        r += 1
    return r

def jordan_blocks(N, p):
    n = len(N)
    powers = [identity(n, p)]
    while True:
        nxt = mat_mul(powers[-1], N, p)
        powers.append(nxt)
        if rank(nxt, p) == 0 or len(powers) > n + 2:
            break
    rks = [rank(P, p) for P in powers]
    blocks = []
    for j in range(1, len(rks)):
        ge_j = rks[j - 1] - rks[j]
        ge_j1 = rks[j] - rks[j + 1] if j + 1 < len(rks) else 0
        blocks.extend([j] * (ge_j - ge_j1))
    return sorted(blocks, reverse=True)

def fuse(r, s, p):
    N = mat_sub(kron(Ls_action(r, p), Ls_action(s, p), p), identity(r * s, p), p)
    mult = {}
    for j in jordan_blocks(N, p):
        mult[j] = mult.get(j, 0) + 1
    mult.pop(p, None)          # L_p has dimension p = 0: it is negligible
    return mult

def ostrik_formula(r, s, p):
    c = min(r, s, p - r, p - s)
    mult = {}
    for i in range(1, c + 1):
        mult[abs(r - s) + 2 * i - 1] = mult.get(abs(r - s) + 2 * i - 1, 0) + 1
    return mult

def part_B():
    print("=" * 78)
    print("Part B.  Rep(F_p[C_p]) and the Verlinde category Ver_p")
    print("=" * 78)
    results = []
    for p in (3, 5, 7, 11, 13):
        print(f"--- p = {p}")
        sym_ok = {}
        for s in range(1, p):
            M = Ls_action(s, p)
            B = beta_form(s, p)
            Bt = mat_transpose(B)
            invariant = mat_mul(mat_mul(mat_transpose(M), B, p), M, p) == B
            sym_part = [[(B[i][j] + Bt[i][j]) % p for j in range(s)] for i in range(s)]
            alt_part = [[(B[i][j] - Bt[i][j]) % p for j in range(s)] for i in range(s)]
            sym_nd = rank(sym_part, p) == s
            alt_nd = rank(alt_part, p) == s
            sym_ok[s] = sym_nd
            print(f"    L_{s}: beta invariant {invariant}, det(beta) {rank(B, p) == s},"
                  f" beta+beta^T symmetric nondegenerate {sym_nd},"
                  f" beta-beta^T alternating nondegenerate {alt_nd}"
                  f"   (s odd: {s % 2 == 1})")
        print(f"    symmetric nondegenerate invariant form exists exactly for odd s:"
              f" {all(sym_ok[s] == (s % 2 == 1) for s in range(1, p))}")
        if p <= 7:
            fusion = {(r, s): fuse(r, s, p) for r in range(1, p) for s in range(1, p)}
            agree = all(fusion[(r, s)] == ostrik_formula(r, s, p)
                        for r in range(1, p) for s in range(1, p))
            print(f"    tensor products agree with Ostrik 2015 formula (4) for all r,s:"
                  f" {agree}")
        else:
            fusion = {(r, s): ostrik_formula(r, s, p)
                      for r in range(1, p) for s in range(1, p)}
            print("    tensor products from Ostrik 2015 formula (4), recomputed from"
                  " scratch for p <= 7")
        subs = [("Vec", {1}),
                ("sVec", {1, p - 1}),
                ("Ver_p^+ (odd indices)", {s for s in range(1, p) if s % 2 == 1}),
                ("Ver_p (all simples)", set(range(1, p)))]
        for name, S in subs:
            closed = all(j in S for r in S for s in S for j in fusion[(r, s)])
            allsym = all(sym_ok[s] for s in S)
            total = sum(s * s for s in S) % p
            ok = closed and allsym and total == 0
            print(f"    {name:22s}: closed {closed}, every simple has a symmetric"
                  f" nondegenerate form {allsym}, quadratic sum = {total} in F_{p},"
                  f" Quinn (1)-(4): {ok}")
            results.append((p, name, closed, allsym, total, ok))
        print(f"    global dimension (sum over all simples) ="
              f" {sum(s*s for s in range(1,p)) % p} in F_{p}")
    print()
    print("Determinants over Z of the form beta and its symmetric and alternating parts")
    print("(exact integers, independent of p; the determinant of beta+beta^T is 2^s for")
    print("odd s and of beta-beta^T is 2^s for even s, so both are nonzero in every")
    print("field of odd characteristic):")
    for s in range(1, 10):
        ic = iota_coeffs(s)
        B = [[(ic[j][s - 1 - i] if s - 1 - i >= 0 else 0) for j in range(s)] for i in range(s)]
        S = [[B[i][j] + B[j][i] for j in range(s)] for i in range(s)]
        A = [[B[i][j] - B[j][i] for j in range(s)] for i in range(s)]
        print(f"    s = {s}: det(beta) {det_int(B)}, det(beta+beta^T) {det_int(S)},"
              f" det(beta-beta^T) {det_int(A)}")
    print("    (2^s is the determinant of beta+beta^T for odd s and of beta-beta^T")
    print("     for even s, so the forms are nondegenerate over every field of odd")
    print("     characteristic.)")
    print()
    print("Candidate data sets: (p, set, closed, all forms symmetric, sum in F_p, Quinn holds)")
    for row in results:
        print("   ", row)
    print()
    good = sorted({row[0] for row in results if row[5]})
    print("characteristics in which some listed set satisfies (1)-(4):", good)
    return results

if __name__ == "__main__":
    part_A()
    part_B()
