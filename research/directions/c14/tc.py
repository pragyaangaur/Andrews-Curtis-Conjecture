#!/usr/bin/env python3
"""tc.py -- Todd-Coxeter coset enumeration of the trivial subgroup, with a coset
limit.  Returns the index (= the order of the presented group) when the
enumeration closes, and None when it exceeds the limit.  Symbols: 0=a, 1=A,
2=b, 3=B, with INV = [1,0,3,2]."""

INV = [1, 0, 3, 2]
SYM = {1: 0, -1: 1, 2: 2, -2: 3}


class Limit(Exception):
    pass


def syms(w):
    return [SYM[x] for x in w]


class Enum:
    def __init__(self, rels, limit):
        self.uf = [0]
        self.tab = [{}]
        self.limit = limit
        self.rels = [syms(r) for r in rels]

    def find(self, x):
        uf = self.uf
        while uf[x] != x:
            uf[x] = uf[uf[x]]
            x = uf[x]
        return x

    def define(self, c, s):
        if len(self.uf) >= self.limit:
            raise Limit
        new = len(self.uf)
        self.uf.append(new)
        self.tab.append({})
        self.tab[c][s] = new
        self.tab[new][INV[s]] = c
        return new

    def scan(self, rel):
        c = 0
        for s in rel:
            c = self.find(c)
            d = self.tab[c].get(s)
            if d is None:
                c = self.define(c, s)
            else:
                c = self.find(d)
        return c

    def merge(self, a, b):
        stack = [(a, b)]
        while stack:
            x, y = stack.pop()
            x = self.find(x)
            y = self.find(y)
            if x == y:
                continue
            if y == 0:
                x, y = y, x
            self.uf[y] = x
            for s, z in self.tab[y].items():
                if s in self.tab[x]:
                    stack.append((self.tab[x][s], z))
                else:
                    self.tab[x][s] = z
            self.tab[y] = {}

    def run(self):
        from collections import deque
        try:
            work = deque()
            pend = set()
            for i in range(len(self.rels)):
                work.append((i, 0))
                pend.add((i, 0))
            while work:
                i, c = work.popleft()
                c = self.find(c)
                cc = c
                for s in self.rels[i]:
                    cc = self.find(cc)
                    d = self.tab[cc].get(s)
                    if d is None:
                        new = self.define(cc, s)
                        for j in range(len(self.rels)):
                            if (j, new) not in pend:
                                pend.add((j, new))
                                work.append((j, new))
                        cc = new
                    else:
                        cc = self.find(d)
                if cc != c:
                    self.merge(cc, c)
                    for x in range(len(self.uf)):
                        if self.find(x) == x:
                            for j in range(len(self.rels)):
                                if (j, x) not in pend:
                                    pend.add((j, x))
                                    work.append((j, x))
        except Limit:
            return None
        return sum(1 for i in range(len(self.uf)) if self.find(i) == i)


def order(rels, limit=20000):
    return Enum(rels, limit).run()
