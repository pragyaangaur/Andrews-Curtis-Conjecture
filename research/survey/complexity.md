# Andrews-Curtis trivialisation: length, complexity, decidability

Member m3, swarm `smw2fzjic`, direction D3 (`survey/complexity.md`).

This file collects what is actually proved about *how long* an Andrews-Curtis
trivialisation has to be, and what is known about *deciding* whether one
exists. Each claim carries a bracketed label of one of four kinds.

* `[verified: SOURCE, loc]`: I read the statement in the source named, at the
  location given. For arXiv papers I downloaded the LaTeX e-print, so the
  statement is the authors' own TeX and not an HTML rendering.
* `[computation]`: an exact, deterministic computation with a command anyone
  can rerun. The script is `survey/complexity_check.py` in this directory.
* `[argument]`: a deduction I made myself. It is not a citation, and it is
  labelled so that it can be checked and, if wrong, discarded.
* `[reported: SOURCE]`: the statement is in the source, I quote it, and I did
  not verify it against the primary work it attributes.

Section 11 lists everything I could not verify. Nothing here claims progress on
the conjecture itself.

---

## 1. What is being counted

Andrews and Curtis introduced the moves and the conjecture in 1965
[verified: Andrews and Curtis, *Free groups and handlebodies*, Proc. Amer.
Math. Soc. **16** (1965), 192-195, DOI 10.1090/S0002-9939-1965-0173241-8].

Bridson fixes the following conventions, and all lower bounds quoted below are
stated in them [verified: Bridson, arXiv:1504.04187, section 2.1]. A balanced
presentation is written $\mathcal{P} \equiv \langle a_1,\dots,a_k \mid
r_1,\dots,r_k\rangle$, and the standard presentation is
$\mathbb{I}_k \equiv \langle a_1,\dots,a_k \mid a_1,\dots,a_k\rangle$. The
moves act on the list $(r_1,\dots,r_k)$:

* (AC1) replace some $r_i$ by $r_i^{-1}$;
* (AC2) replace $r_i$ by $r_i r_j$ with $i \neq j$;
* (AC3) replace $r_i$ by $u r_i u^{-1}$ with $u$ any word in $F(a_1,\dots,a_k)$;
* (AC4) stabilisation: append new generators $x_1,\dots,x_\ell$ and new
  relators $x_1,\dots,x_\ell$;
* (T) insertion or deletion of an empty relator, i.e. the list
  $(r_1,\dots,r_k)$ may be replaced by $(r_1,\dots,r_k,\emptyset)$.

Words are always elements of the free group, so free reduction and expansion
cost nothing. Tietze's theorem says that (AC1) to (AC4) together with (T)
suffice to trivialise every presentation of the trivial group, so the whole
content of the conjecture is the prohibition on (T).

Bridson then introduces a packaged move, which he calls a **dihedral AC move**:
the single move $r_j \mapsto r_j (u r_i^{\pm 1} u^{-1})$ with $i \neq j$. The
minimum number of dihedral AC moves needed to trivialise $\mathcal{P}$ is
written $\mathrm{AC}_*(\mathcal{P})$ [verified: Bridson, arXiv:1504.04187,
section 2.1]. This packaging matters for comparing numerical bounds, and it is
easy to get a factor of 3 wrong. One dihedral move is a composite of at most
three basic moves (conjugate $r_i$, invert if needed, multiply into $r_j$).
Hence, if $b(\mathcal{P})$ denotes the minimal number of *basic* AC moves,
$$b(\mathcal{P}) \;\geq\; \mathrm{AC}_*(\mathcal{P}) \quad\text{and}\quad
b(\mathcal{P}) \;\leq\; 3\,\mathrm{AC}_*(\mathcal{P})$$
[argument: immediate from the definitions, and the script checks the counter
bookkeeping]. So a lower bound for $\mathrm{AC}_*$ is a lower bound for the
basic move count, and an upper bound for the basic move count gives an upper
bound for $\mathrm{AC}_*$ within a factor of 3.

The second measured quantity is algebraic area. For a finite presentation
$\mathcal{P} \equiv \langle \mathcal{A} \mid \mathcal{R}\rangle$ and a word $w$
that represents the identity, $\mathrm{area}(w)$ is the least $N$ such that
there is an equality in the free group $F(\mathcal{A})$
$$w = \prod_{i=1}^{N} x_i^{-1} r_i^{\pm 1} x_i, \qquad x_i \in F(\mathcal{A}),\ r_i \in \mathcal{R}.$$
Bridson also uses $\mathrm{area}^*(w) := \min\{\mathrm{area}(w^n) : n \in \mathbb{Z},\ n \neq 0\}$
[verified: Bridson, arXiv:1504.04187, section 2.2]. The Dehn function is
$\delta(n) = \max\{\mathrm{area}(w) : |w| \le n,\ w =_\mathcal{P} 1\}$. Note
that $\mathrm{area}(a_i)$ for a generator $a_i$ makes sense here: it is the
least number of conjugates of relators whose product equals $a_i$ in the free
group. It is finite for every generator exactly when the presentation defines
the trivial group.

---

## 2. The bridge from area to move count

The mechanism behind every published lower bound on AC length is a conversion
of an area lower bound into a move-count lower bound. It has two halves.

### 2.1 Area is stable under taking powers, for aspherical presentations

**Lemma (Gersten, in Bridson's form).** Let $\langle \mathcal{A}\mid\mathcal{R}\rangle$
be an aspherical presentation and let $D$ be an embedded van Kampen diagram for
a word $w$. Then for every $n \in \mathbb{Z}$,
$\mathrm{area}(w^n) = |n|\,\mathrm{area}(D)$. In particular
$\mathrm{area}^*(w) = \mathrm{area}(D)$.
[verified: Bridson, arXiv:1504.04187, section 2.3. Bridson presents it as "a
slight variation on a result of Gersten" and cites Gersten, *Dehn functions and
$l_1$-norms of finite presentations*, in Algorithms and Classification in
Combinatorial Group Theory (Berkeley 1989), MSRI Publ. 23, Springer 1992,
195-224. I did not read Gersten's paper, so the exact form of Gersten's original
statement is unverified.]

The proof is a two-chain argument in the universal cover: for an aspherical
presentation $H_2(\widetilde K) = 0$, so the 2-chain of any diagram for $w^n$
must equal $n$ times the 2-chain of $D$, and the 2-cells of $D$ are distinct
because $D$ is embedded. This is the only place where asphericity enters, and
it is what makes the Baumslag-Gersten-type groups usable as seeds.

### 2.2 Moves can only build Fibonacci many conjugates

**Lemma (Fibonacci bound).** If $\mathcal{P} \equiv \langle \mathcal{A} \mid
r_1,\dots,r_n\rangle$ can be trivialised by $m$ dihedral AC moves, then
$\mathrm{area}_{\mathcal{P}}(a_i) \le \mathrm{fib}_m$ for $i = 1,\dots,n$,
where $\mathrm{fib}_m$ is the $m$-th Fibonacci number.
[verified: Bridson, arXiv:1504.04187, section 2.4.]

The proof tracks, for each relator in the list, the number $c_j$ of conjugates
of original relators in an unreduced expression for it. Initially $c_j = 1$.
(AC1) and (AC3) leave every $c_j$ unchanged, and (AC2) replaces $c_j$ by
$c_j + c_i$ with $i \neq j$. So the counters obey a Fibonacci recursion, and at
the end $a_i$ is a product of at most that many conjugates of relators, which
is precisely the definition of $\mathrm{area}(a_i)$.

**Computation.** I ran the counter recursion exhaustively over all AC2
sequences of length $m$ for relator counts $n \in \{2,3,4\}$ and $m \le 9$.
The sharp value of $\max_j c_j$ after $m$ moves is $\mathrm{fib}_{m+2}$ with
$\mathrm{fib}_1 = \mathrm{fib}_2 = 1$, for every such $n$ and $m$.
[computation: `python3 survey/complexity_check.py`, lines beginning
`PASS conjugate count`.] For example with $n = 2$ and $m = 6$ the maximum
reachable counter is $21 = \mathrm{fib}_8$, while $\mathrm{fib}_6 = 8$.

This is a small correction to the printed statement. Bridson writes "no greater
than $\mathrm{fib}_m$", which is true but not sharp; with the standard indexing
$\mathrm{fib}_1 = \mathrm{fib}_2 = 1$ the sharp bound is $\mathrm{fib}_{m+2}$.
The offset of 2 depends on the indexing convention and on whether one counts
the initial state as move 0, and it changes no asymptotic claim below. I record
it because a downstream calculation that chains constants would otherwise be
off by a factor of about $\varphi^2 = 2.618$.

COORDINATOR CORRECTION, 2026-11-04, from the Round 2 second referee report at directions/second-referees/referee.md section 5.2, checked by hand and by computation. Two changes to this section. First, Bridson's printed bound area <= fib_m is not merely unsharp: it is false at m = 1. The presentation <x, y | xy, y> is trivialised by the single dihedral move r_1 -> r_1 r_2^-1, and area_P(x) = 2 there, because a single conjugate of a relator has exponent sum (1,1) or (0,1) and never (1,0), while two conjugates give x = (xy) y^-1; but fib_1 = 1. Second, the passage below that recommends quoting the additive constant 1 is backwards: that derivation uses the false bound. Substituting the sharp bound fib_{m+2} < e^{m+2} into the same chain gives log area* < AC_* + 2 + log 3, so this argument yields the additive constant 3.1, and the recommendation is to quote the body's constant 3. Bridson's Theorem A and the tower lower bounds are unaffected by either change.

Two consequences are used constantly. Since $\mathrm{fib}_m < e^m$, a
trivialisation with $m$ dihedral moves forces
$\log \mathrm{area}_{\mathcal{P}}(a_i) < m$, where $\log$ is the natural
logarithm. Equivalently, a lower bound $A$ on some $\mathrm{area}(a_i)$ gives a
lower bound of about $\log A$ on the number of moves. That logarithm is the
whole reason the numbers in section 3 are as large as they are.

**Proposition (same bound with stabilisation and Tietze moves).** If
$\mathcal{P}$ can be trivialised by $m$ moves drawn from (AC1) to (AC4) and (T),
then $\mathrm{area}_{\mathcal{P}}(a_i) \le \mathrm{fib}_m$.
[verified: Bridson, arXiv:1504.04187, section 2.4, Proposition.] So the lower
bounds are insensitive to stabilisation, and Bridson states explicitly that his
results hold whether or not stabilisation is allowed.

---

## 3. Bridson's lower bounds

### 3.1 The construction and its exact statement

The construction takes a seed presentation of deficiency 1 and an extra
generator, and encodes the difficulty of a word problem into a *balanced*
presentation. The input is a presentation
$\mathcal{P} \equiv \langle a_0,a_1,\dots,a_n \mid r_1,\dots,r_n\rangle$ such
that deleting $a_0$ from every relator gives a presentation
$\bar{\mathcal{P}} \equiv \langle a_1,\dots,a_n \mid \bar r_1,\dots,\bar r_n\rangle$
of the trivial group and $a_1$ has infinite order in $|\mathcal{P}|$. For a word
$w$ in the $a_i^{\pm 1}$, where $\bar w$ means $w$ with all $a_0^{\pm 1}$
deleted, put
$$\mathcal{P}_w \equiv \langle \mathcal{A}, \hat{\mathcal{A}} \mid
\mathcal{R},\ \hat{\mathcal{R}},\ \hat a_1 a_0 \hat a_1^{-1} w^{-1},\
a_1 \hat a_0 a_1^{-1} \hat w^{-1}\rangle .$$
This has $2(n+1)$ generators and $2n+2$ relators, so it is balanced.
[verified: Bridson, arXiv:1504.04187, section 1 and section 3.]

**Theorem (lower bound).** With the input above, for every word $w$ in the
$a_i^{\pm 1}$: (1) the group $|\mathcal{P}_w|$ is trivial if $w = 1$ in
$|\mathcal{P}|$; (2) if $w = 1$ and $\bar{\mathcal{P}}$ is AC-trivialisable then
$\mathcal{P}_w$ is AC-trivialisable and
$\log \mathrm{area}^*_{\mathcal{P}}(w) \le 3\,\mathrm{AC}_*(\mathcal{P}_w)$.
[verified: Bridson, arXiv:1504.04187, section 3, the theorem labelled `t:if`.]

There are two printed forms of this inequality in the same paper, and they
differ in the constant. The introduction states
$\log \mathrm{area}^*_{\mathcal{P}}(w) \le \mathrm{AC}_*(\mathcal{P}_w) + 1$
[verified: arXiv:1504.04187, section 1, the theorem labelled `t:If`], while the
body states the version with constant 3 quoted above. The proof in the body
produces the sharper one: from the Fibonacci bound and the corollary
$\mathrm{area}_{\mathcal{P}_w}(a_0) \ge \tfrac13 \mathrm{area}^*_{\mathcal{P}}(w)$
one gets $\mathrm{AC}_*(\mathcal{P}_w) \ge \log \mathrm{area}^*_{\mathcal{P}}(w) - \log 3$,
and since the left side is an integer this gives
$\mathrm{AC}_*(\mathcal{P}_w) \ge \log \mathrm{area}^*_{\mathcal{P}}(w) - 1$
[verified: the displayed chain in the proof of `t:if`, and the corollary
labelled `c:area`]. The version with constant 3 is therefore a correct but
weaker restatement, and anyone quoting a constant should quote 1. A related
point: the logarithm is natural, because the argument uses
$\mathrm{fib}_m < e^m$.

**Theorem (two-sided).** Under the additional hypotheses that $\langle a_0\rangle$
and $\langle a_1\rangle$ are infinite and intersect trivially in
$|\mathcal{P}|$, and that $\langle w\rangle$ is trivial or infinite and meets
$\langle a_1\rangle$ trivially, one has (1) $|\mathcal{P}_w|$ is trivial if and
only if $w = 1$ in $|\mathcal{P}|$, and (2), when $w = 1$ and
$\bar{\mathcal{P}}$ is AC-trivialisable,
$$\log \mathrm{area}^*_{\mathcal{P}}(w) - 1 \;\le\; \mathrm{AC}_*(\mathcal{P}_w)
\;\le\; 2\,\mathrm{AC}_*(\bar{\mathcal{P}}) + 2\,\mathrm{area}^*_{\mathcal{P}}(w)
+ 2\sum_{r \in \mathcal{R}} |r|_0,$$
where $|r|_0$ is the number of occurrences of $a_0$ in $r$.
[verified: Bridson, arXiv:1504.04187, section 5, the theorem labelled `t:main`.]
The point of the two-sided bound is that the move count really is a function of
the word-problem difficulty, and not merely bounded below by something one
cannot control.

### 3.2 The seed group and the final numbers

The seed is the one-relator group
$S_k = \langle x,t \mid (txt^{-1})\,x\,(txt^{-1})^{-1} = x^k\rangle$ for
$k \ge 2$, with $\Delta_k(0) = k$ and $\Delta_k(m+1) = k^{\Delta_k(m)}$.
[verified: Bridson, arXiv:1504.04187, section 6.1.] For $k = 2$ this is the
Baumslag-Gersten group, the same group that Lishak writes as
$\langle x,y,t \mid y^{-1}xy = x^2,\ y = t^{-1}xt\rangle$, and whose Dehn
function is a tower of 2's of height proportional to $\log_2$ of the argument.
[verified for the identification with Lishak's group: Lishak,
arXiv:1504.00418v2, section 2. Bridson attributes the isoperimetric study of
$S_2$ to Gersten and to Platonov, and I did not check those attributions
against the primary papers.]

**Theorem (seed).** There is a sequence of words $w_n \in F(x,t)$ with
$|w_n| \le 12n$ such that $w_n = 1$ in $S_k$ and
$\mathrm{area}^*_{S_k}(w_n) \ge \Delta_k(\lfloor \log_2 n\rfloor)$.
[verified: Bridson, arXiv:1504.04187, section 6.1, the theorem labelled `thmS`.]
The words are explicit: for $n = 2^m$, $w_n = x V_m x^{-1} V_m^{-1}$ with
$V_0 = x$ and $V_m = t V_{m-1} t^{-1} x\, t V_{m-1}^{-1} t^{-1}$
[verified: section 6.1, the definition labelled `d:w_n`]. Feeding these into the
construction with the natural presentation of $S_2$ gives the headline result.

**Theorem A (Bridson).** For $k \ge 4$ one can construct explicit sequences of
$k$-generator balanced presentations $\mathcal{P}_n$ of the trivial group so
that (1) the $\mathcal{P}_n$ are AC-trivialisable; (2) the sum of the lengths of
the relators in $\mathcal{P}_n$ is at most $24(n+1)$; (3) the number of
dihedral AC moves required to trivialise $\mathcal{P}_n$ is bounded below by
$\Delta(\lfloor \log_2 n\rfloor)$, where $\Delta(0) = 2$ and
$\Delta(m+1) = 2^{\Delta(m)}$.
[verified: Bridson, arXiv:1504.04187, section 1, Theorem A.]

So the bound is $\Delta = \Delta_2$, a tower of 2's, and the presentations have
4 generators. Since the length budget is $24(n+1)$ and the bound is
$\Delta(\lfloor \log_2 n\rfloor) = 2{\uparrow\uparrow}(\lfloor\log_2 n\rfloor + 1)$,
Bridson's remark that the number of moves grows faster than any tower of
exponentials of fixed height is correct as a statement about the dependence on
the length budget $L \le 24(n+1)$.

**Computation.** $\Delta(0) = 2$, $\Delta(1) = 4$, $\Delta(2) = 16$,
$\Delta(3) = 65536$, $\Delta(4) = 2^{65536}$, and
$\Delta(m) = 2{\uparrow\uparrow}(m+1)$. Taking $n = 2^j$ the bound
$\Delta(j) = 2{\uparrow\uparrow}(j+1)$ exceeds $2{\uparrow\uparrow}j$ while the
total relator length is at most $24(2^j + 1)$. At $j = 4$ that is a total
relator length of at most 408 forcing more than $2^{65536}$ dihedral moves.
[computation: the `PASS Theorem A unpacked` and `PASS Delta` lines of
`survey/complexity_check.py`.]

**Computation (the constant 24 is checkable bookkeeping).** The seed relator
$(txt^{-1}) x (txt^{-1})^{-1} x^{-2}$ has length 8. The construction produces
four relators, namely $r$, $\hat r$ of length 8 each, and the two relators
$\hat a_1 a_0 \hat a_1^{-1} w^{-1}$ and $a_1 \hat a_0 a_1^{-1}\hat w^{-1}$ of
length $|w| + 3$ each. With $|w_n| \le 12n$ the total is
$16 + 2(12n+3) = 24n + 22 \le 24(n+1)$.

COORDINATOR CORRECTION, 2026-11-04, from the same referee report, section 5.3, checked by computation and by hand. The seed relator $(t x t^{-1}) x (t x t^{-1})^{-1} x^{-2}$ has length 9, not 8: it is $t x t^{-1} x t x^{-1} t^{-1} x^{-2}$ with no cancellation available. The correct bookkeeping is $2 \cdot 9 + 2(12n+3) = 24n + 24 = 24(n+1)$, so the printed constant 24 is exactly tight at $|w| = 12n$ and not slack by 2. With Bridson's sharper $|w_n| \leq 12n - 8$ there is slack: $2 \cdot 9 + 2(12n - 8 + 3) = 24n + 8 \leq 24(n+1)$. The conclusion that 24 is a legitimate constant stands, and the arithmetic lines of survey/complexity_check.py verify the equality with the corrected length.
[computation: the `PASS Theorem A constant` lines of
`survey/complexity_check.py`.] So the printed constant 24 is not slack by more
than 2, and the reader can reproduce it.

**Corollary A.** One can construct the $\mathcal{P}_n$ so that
$n \mapsto \mathrm{AC}_*(\mathcal{P}_n)$ is $\simeq$-equivalent to
$\Delta(\lfloor \log_2 n\rfloor)$, where $f \simeq g$ means each is bounded by
the other up to a multiplicative constant and a shift of argument.
[verified: Bridson, arXiv:1504.04187, section 1, Corollary A.]

### 3.3 The explicit small example

Bridson closes with one written-out presentation, "a balanced presentation of
the trivial group that requires more than $10^{10000}$ AC-moves to trivialise
it", with generators $a, t, \alpha, \tau$ and relators
$$[tat^{-1},a]a^{-1},\quad [\tau\alpha\tau^{-1},\alpha]\alpha^{-1},$$
$$\alpha t^{-1}\alpha^{-1}\,[a,[t[t[ta^{20}t^{-1},a]t^{-1},a]t^{-1},a]],$$
$$a\tau^{-1}a^{-1}\,[\alpha,[\tau[\tau[\tau\alpha^{20}\tau^{-1},\alpha]\tau^{-1},\alpha]\tau^{-1},\alpha]],$$
where $[x,y] = xyx^{-1}y^{-1}$.
[verified: Bridson, arXiv:1504.04187, section 7.4. The attribution "more than
$10^{10000}$" is Bridson's and I do not reproduce his construction.]

**Computation (the input is small).** I parsed the four relators as free-group
words over the four letters and freely reduced them. Their lengths are
$9, 9, 407, 407$, so the total relator length is $832$ and the presentation is
balanced with 4 generators and 4 relators.
[computation: the `explicit example` lines of `survey/complexity_check.py`.]
The count convention is free-group word length, so a power such as $a^{20}$
counts as 20 letters. What this settles is that the quoted lower bound is a
claim about a presentation of total length 832, and therefore that the gap
between searchable inputs and provably hard inputs is real at human scale. What
it does not settle is triviality of the presented group or the lower bound
itself; both are part of Bridson's theorem.

### 3.4 The AC graph reading

Bridson defines, for each $k$, a graph $\mathcal{AC}_k$ whose vertices are the
balanced presentations of the trivial group considered as quotients of a fixed
$F_k$, with edges for (AC1) to (AC3), and $\mathcal{AC}_\infty$ as the union
after allowing (AC4). With $\lambda$ the sum of relator lengths and
$\Lambda(m) = \lambda^{-1}[0,m]$, the conjecture says $\mathcal{AC}_k$ is
connected and the stable conjecture says $\mathcal{AC}_\infty$ is connected.
His Theorem `t:hint` states: for $k \ge 4$ there is a constant $C$ and a
sequence of vertices $P_n \in \Lambda(Cn)$, all in the path component of
$\mathcal{AC}_k$ containing $\mathbb{I}_k$, such that $P_n$ cannot be connected
to $\mathbb{I}_k$ by a path inside $\Lambda(\Delta(\lfloor\log_2 n\rfloor))$.
[verified: Bridson, arXiv:1504.04187, section 7.1.]

This is the precise sense in which the Andrews-Curtis graph is not coarsely
connected with respect to the length function, and it is the statement to cite
when someone claims that a bounded-length search "supports" the conjecture.

---

## 4. The 2006 announcement, and what changed by 2015

The lower bounds were proved in 2003, announced in the ICM survey of 2006, and
posted with full details in 2015 [verified for the chronology: Bridson,
arXiv:1504.04187, the closing paragraph of section 1, "I proved the results
described in this paper in 2003 and presented them at the Arkansas Spring
Lecture Series".] The ICM survey states: the main construction of Bridson's
preprint
associates a balanced presentation $\mathcal{P}_w$ to each word $w$ in the
generators of a group $B$ satisfying a deletion condition; $\mathcal{P}_w$
presents the trivial group if and only if $w = 1$ in $B$; and if $\mathcal{P}_w$
presents $\{1\}$ then it is AC-trivialisable "but the number of elementary
moves required to trivialise it is bounded below by $\log \mathrm{Area}^*_B(w)$".
For $B = \langle a,t \mid [tat^{-1},a] = a^{r-1}\rangle$ one has
$\delta_B(n) \simeq \Delta_r\lfloor\log_2 n\rfloor$ with $\Delta_r(1) := r$ and
$\Delta_r(m+1) := r^{\Delta_r(m)}$, and then $\mathcal{P}_w$ has 4 generators
and relations of total length $2(10+|w|+r)$.
[verified: Bridson, *Non-positive curvature and complexity for finitely
presented groups*, ICM 2006, Vol. II, 961-987, section 4.4. The PDF from the
author's page is the source I read; the pagination there places the passage on
page 17 of the offprint, and Lishak cites it as page 977 of the proceedings.]

Three differences from the 2015 paper are worth recording, since a reader who
cites the ICM version and a reader who cites the arXiv version will otherwise
disagree. First, the announcement states the move-count bound as
$\log \mathrm{Area}^*_B(w)$ with no constant, while the 2015 body proves the
sharper $+1$ version and also prints a $3$. Second, the announcement runs the
construction over $S_{r-1}$ in the family $S_k$, while the 2015 paper
specialises to $S_2$ and gets $\Delta = \Delta_2$. Third, the length accounting
$2(10+|w|+r)$ in the announcement and $24(n+1)$ in Theorem A are different
normalisations of the same bookkeeping and should not be compared directly.
[argument: a comparison of the two texts, both of which I read.]

---

## 5. The rank 2 case: Lishak's tower bounds

Bridson's method does not reach rank 2, and rank 2 is where the standard
suspects live. The gap was closed by a different method.

Lishak works with presentations $\mu_i = (\{x,y,t\}, \{x^y x^{-2},\ x^t y^{-1},\ a_i\})$
for $i \in \{5,6,7,\dots\}$ with $l(a_i) < 100 \cdot 2^i$, where $x^y$ denotes
$y^{-1}xy$, and with $E_n$ defined by $E_0 = 1$ and $E_{n+1} = 2^{E_n}$.

**Theorem (Lishak, first).** There exist presentations of the trivial group
$\mu_i$ as above, with $l(a_i) < 100\cdot 2^i$, such that the minimal number of
elementary Tietze transformations required to bring $\mu_i$ to the empty
presentation is at least $E_{i-2}$.
[verified: Lishak, arXiv:1504.00418v2, section 2, the theorem labelled `main`.]

**Theorem (Lishak, second).** The same presentations satisfy
$\mathrm{Area}_{\mu_i}(x) > E_{i-1}$.
[verified: Lishak, arXiv:1504.00418v2, section 2, the theorem labelled
`second`.] Lishak reports that the first follows from the second.

Lishak's elementary Tietze transformations are his operations $Op_1$ to $Op_5$:
free insertion and deletion of $x_j^{\epsilon}x_j^{-\epsilon}$ inside a
relator, cyclic permutation of a relator, inversion, multiplication by another
relator, and adjoining a new generator together with the relator equal to it.
[verified: arXiv:1504.00418v2, section 2, the definition of elementary Tietze
transformations.] So his move count includes free expansions, which Bridson's
area does not, and includes stabilisation. The presence of free expansions means
his count and Bridson's $\mathrm{AC}_*$ differ by a factor that is not a
constant, so the two families of results are not directly comparable move for
move.

There is nevertheless a consistency check available, and it passes. If
$\mathrm{Area}_{\mu_i}(x) > E_{i-1}$ then by the Fibonacci bridge any
trivialisation needs more than $\log E_{i-1} = E_{i-2}\log 2$ moves, which
matches the stated lower bound $E_{i-2}$ up to the factor $\log 2$.
[argument: applying the two lemmas of section 2 to Lishak's area bound. Note
that the $\log$ is natural, so $E_{i-1} = 2^{E_{i-2}}$ gives
$\log E_{i-1} = E_{i-2}\log 2$.] This is evidence that the two papers are
counting comparable quantities even though they state their bounds in different
currencies.

**Proof mechanism.** Lishak kills the Baumslag-Gersten group
$G = \langle x,y,t \mid y^{-1}xy = x^2,\ y = t^{-1}xt\rangle$, whose Dehn
function is a tower of 2's of height proportional to $\log_2$, by adding one
long relator $a_i$ that equates $t$ with a word of huge area in $G$. The
difficulty is that the resulting group is trivial, so no covering-space or
normal-form argument is available. He develops a small cancellation theory over
HNN extensions in which "reduced" is weakened to "$N$-reduced", meaning that a
pinch is allowed only when it is witnessed by a $t$-band of length at least $N$,
and then uses contiguity subdiagrams to prove that a van Kampen diagram for $x$
over $\mu_i$ containing fewer than $N$ $t$-cells cannot exist.
[verified: arXiv:1504.00418v2, sections 1 and 3, including the definition of
$N$-reduced, the $N$-symmetrized set, the condition $C'(\tfrac16,N)$, and the
theorem labelled `small`.]

**One discrepancy to record.** The abstract and the introduction of
arXiv:1504.00418v2 say "two generators and two relators", and the introduction
says one relator is the same for all members of the sequence. The theorems as
displayed in the same file have three generators $\{x,y,t\}$ and three
relators. I record the displayed form. I did not access the published version
(DOI 10.1142/S1793525317500182, Journal of Topology and Analysis), so I cannot
say whether the published statement is the two-generator one or the
three-generator one. Anyone quoting "rank 2" for this result should check the
published text first.

---

## 6. The geometric sequel

Lishak and Nabutovsky turn the area bounds into statements about triangulations
and moduli spaces in dimension 4. The arXiv record is
arXiv:1504.05927, "Balanced presentations of the trivial group and
four-dimensional geometry", with DOI 10.1142/S1793525317500042.
[verified: arXiv API metadata for 1504.05927: authors Boris Lishak and
Alexander Nabutovsky, submitted 22 April 2015, related DOI as stated.] I read
the abstract and search excerpts only, and I did not verify any of its theorems.
The relevant claim for this survey is only that the complexity lower bounds
have a topological reading, in which a sequence of triangulations of $S^4$ with
$N$ simplices cannot be connected by fewer than a tower of exponentials of
bistellar moves. That belongs to the topology direction and I do not develop it
here.

---

## 7. Decidability

### 7.1 The general case is undecidable

The triviality problem for finite presentations is undecidable, by Adian and by
Rabin [verified: Rabin, *Recursive unsolvability of group theoretic problems*,
Ann. of Math. (2) **67** (1958), 172-194, DOI 10.2307/1969933. I did not read
Adian's 1955 paper.] The undecidability is witnessed by presentations that are
not balanced, so it says nothing directly about the balanced case.

### 7.2 The balanced case is open, and this is Magnus' problem

The Kourovka Notebook, 21st issue (Nottingham and Novosibirsk, 2026), lists as
Problem 1.12, attributed to W. Magnus and communicated by M. D. Greendlinger:

> "The problem of the isomorphism to the trivial group for all groups with $n$
> generators and $n$ defining relations, where $n > 2$."

[verified: *Unsolved Problems in Group Theory. The Kourovka Notebook*, No. 21,
arXiv:1401.0300 (latest version dated November 2026), Problem 1.12, in the main
body of unsolved problems.] The phrase "the problem of" in that list means the
decision problem, and the entry is not in the archive of solved problems. Note
the restriction $n > 2$ in the stated problem.

### 7.3 The balanced case is exactly the set of normal generators

There is a clean reformulation which makes the relation to AC precise. Let
$N_k(F_k)$ be the set of $k$-tuples $(r_1,\dots,r_k) \in F_k^k$ whose normal
closure is all of $F_k$. Then:

* $\langle x_1,\dots,x_k \mid r_1,\dots,r_k\rangle$ presents the trivial group
  if and only if $(r_1,\dots,r_k) \in N_k(F_k)$ [argument: standard;
  triviality means each generator lies in the normal closure of the relators,
  and conversely];
* $N_k(F_k)$ is computably enumerable, because each condition
  "$x_i \in$ normal closure" is witnessed by one finite product of conjugates
  [argument];
* the AC conjecture at rank $k$ says exactly that $N_k(F_k)$ is the orbit of
  $(x_1,\dots,x_k)$ under the elementary AC moves [verified for the
  reformulation: Gilman and Myasnikov, *Andrews-Curtis groups*, J. Groups
  Complexity Cryptology **16** (2024), issue 1, article 7, section 2, state the
  conjecture in this form];
* that orbit is also computably enumerable [argument: enumerate move
  sequences].

Gilman and Myasnikov draw the computability conclusion in one sentence: "It
follows that the set $N_k(F)$ is computably enumerable, but it is not known if
it is computable." [verified: Gilman and Myasnikov, *Andrews-Curtis groups*,
J. Groups Complexity Cryptology **16** (2024), issue 1, article 7 (7 pages), in
the special issue in memory of Ben Fine, section 2. Two bibliographic details
are inconsistent in the sources I saw: the volume statement says 2024 while the
publication action is dated July 2025, and the DOI printed in the journal
metadata is 10.46298/jgcc.2025..15972, which contains a double dot, while the
PDF footer prints 10.46298/jgcc.2024.16.1.15972. I record both and neither
should be trusted without checking the landing page.]

Two implications follow immediately, and I did not find either stated in the
literature, so they are labelled as mine.

**Consequence 1** [argument]. If AC holds at rank $k$ (so the orbit equals
$N_k(F_k)$) and the orbit were computable, then $N_k(F_k)$ would be computable,
that is, Magnus' problem at rank $k$ would have a positive answer. Contrapositive:
a negative answer to Magnus' problem, together with AC at rank $k$, would force
AC-triviality at rank $k$ to be undecidable. So the two problems are not
independent, and a proof that AC-triviality is decidable would be a real result
about Magnus' problem.

**Consequence 2** [argument]. The set of AC-trivialisable balanced
$k$-generator presentations is computably enumerable and is contained in
$N_k(F_k)$. Hence the conjecture at rank $k$ is the assertion that one
computably enumerable set equals another. A decision procedure for membership in
$N_k(F_k)$ would not prove the conjecture, because it gives no information about
the orbit, and a decision procedure for the orbit would not prove it either,
because it gives no information about $N_k(F_k)$.

### 7.4 Gadgil's reduction to 3-manifold algorithms

Gadgil's abstract states: "We relate the Andrews-Curtis conjecture to the
triviality problem for balanced presentations of groups using algorithms from
3-manifold topology. Implementing this algorithm could lead to counterexamples
to the Andrews-Curtis conjecture." [reported: Gadgil, arXiv:math/0108053,
submitted 8 August 2001, 12 pages. I read the abstract only, and the arXiv record
carries no journal reference and no DOI. I do not know of a published version
and I do not state what the paper proves.]

### 7.5 Deciding existence can be fast even when moves are many

Bridson points out that large lower bounds on move counts do not preclude fast
decision procedures, and gives an example inside his own family. Diekert, Laun
and Ushakov proved that the word problem in $S_2$ is solvable in cubic time by
data compression, so for the presentations $\mathcal{P}_w$ built from words $w$
in the generators of $S_2$, AC-triviality can be decided in cubic time even
though every trivialisation needs $\Delta_2(\log_2|w|)$ moves.
[verified: Bridson, arXiv:1504.04187, section 7.3, citing Diekert, Laun and
Ushakov, STACS 2012, LIPIcs 14, 218-229, and Myasnikov, Ushakov and Won,
J. Algebra **345** (2011), 324-342. I did not read either of those two papers.]
The general moral is that "how many moves" and "how hard to decide" are
different questions, and the literature contains a family where the first is
astronomical and the second is cubic.

---

## 8. Finiteness of the group of AC moves

There is a second, independent complexity result about AC moves which is often
conflated with the conjecture. The group of AC moves at rank $n$ acts on
balanced presentations with $n$ fixed generators, and one can ask whether that
group is finitely presented. The Kourovka Notebook records Problem 18.89 (J.
Swan and A. Lisitsa) with the following answer in its archive: the group
$AC_2$ is not finitely presented, attributed to Krstic and McCool, J. London
Math. Soc. (2) **56** (1997), 264-274, and to a 2023 preprint of Roman'kov at
arXiv:2305.11838; and the groups $AC_n$ for $n \ge 3$ are finitely presented,
following from Kiralis, Krstic and McCool, Proc. London Math. Soc. (3) **73**
(1996), 481-720.
[verified as a quotation: Kourovka Notebook No. 21, arXiv:1401.0300, answer to
Problem 18.89. I did not read any of the three papers cited there, so treat the
mathematics as reported and not as verified.] I record it because it is a real
structural obstruction at rank 2, and because it is the item most likely to be
misquoted. It says nothing about decidability of AC-equivalence.

---

## 9. Upper bounds near the standard presentation in rank 2

For contrast, here is what is known in the other direction. Bridson reports, in
his section 7.2, that Casson showed the image of $\Lambda(13)$ in $\Lambda(25)$
is contained in the union of at most 6 path components and that the radius of
$\Lambda(13)$ in the path component of $\mathbb{I}_2$ is at most 217; that the
main result of Miasnikov and Myasnikov, *Balanced presentations of the trivial
group on two generators and the Andrews-Curtis conjecture*, Ohio State Univ.
Math. Res. Inst. Publ. 8, de Gruyter 2001, 257-263, is that
$\Lambda(12) \subset \mathcal{AC}_2$ is connected; and that Casson proved the
binary icosahedral group is the only non-trivial perfect group having a
2-generator balanced presentation with total relator length at most 13.
[reported: Bridson, arXiv:1504.04187, section 7.2. Casson's items come from an
unpublished 2003 Yale manuscript listed in Bridson's bibliography, so I could
not verify them at all. The Miasnikov and Myasnikov item I did not read.]

These numbers are the small-radius complement to section 3. At total relator
length at most 12 the whole ball is one path component, and Casson's
computation describes how $\Lambda(13)$ sits inside $\Lambda(25)$. I did not
verify the separate length-13 classification of two-generator presentations
(every such presentation is AC-trivialisable or AC-equivalent to $AK(3)$), which
belongs to the computational direction and which I have not read at the
primary source.

---

## 10. What the lower bounds do and do not say about search

Bridson states the interpretation himself, about his Theorem A: "one has to
exercise extreme caution when interpreting an experiment that fails to find a
trivialising sequence of AC-moves". [verified: arXiv:1504.04187, section 1.]

The logical content is the following [argument]. A search that explores all
tuples reachable in $m$ moves from $\mathcal{P}$, or all tuples of relator
length at most $L$, produces no information about AC-equivalence of
$\mathcal{P}$ unless the search radius exceeds the length of the shortest
trivialisation. Theorem A produces AC-trivialisable presentations of total
length $24(n+1)$ whose shortest trivialisation needs at least a tower of 2's of
height $\lfloor \log_2 n\rfloor + 1$. The explicit example of section 3.3 has
total relator length 832 and, per Bridson, no trivialisation with fewer than
$10^{10000}$ moves; Bridson writes "AC-moves" there without saying whether he
means basic or dihedral moves, which changes the statement by a factor of 3 at
most. A failed bounded search therefore supports "not reachable within this
radius" and nothing more, and for the specific families in Theorem A it is
consistent with everything known that the presentation is AC-trivialisable with
a very long path.

This does not cut against computational experiments in general. It says that
the useful output of an experiment is a *witness* (an explicit move sequence, or
an explicit invariant obstruction) and that a negative result at bounded radius
has to be reported as a radius and not as evidence against the conjecture.

---

## 11. Things I could not verify, and things I looked for and did not find

1. **No published version of Bridson's lower-bound paper was found.** The arXiv
   record arXiv:1504.04187 has no journal reference and no DOI. Bridson's own
   bibliography dated December 2020 lists "The complexity of balanced
   presentations and the Andrews-Curtis conjecture, arXiv:1504.04187" under
   "Submitted for Publication", and the Oxford University Research Archive entry
   for the same paper records publication status "Submitted" and peer review
   status "Under review". Cite it as a preprint.
2. **No Bridson-Riley or Bridson-Vogtmann result on AC path lengths.** The
   direction brief for D3 named them. I searched and found neither. Their joint
   work that I did find concerns Dehn functions of subgroups and of mapping
   tori, which is a different circle of ideas. I record the gap so that it is
   not filled with an invented citation.
3. **Gersten's original statement is unverified.** Bridson attributes the
   power-stability lemma to Gersten 1992 (MSRI Publ. 23, 195-224). I did not read
   that paper, so I cannot say whether Gersten's version had the embedding
   hypothesis or the asphericity hypothesis in the same form.
4. **Casson's 2003 manuscript is unpublished.** All Casson items in section 9
   are quoted from Bridson.
5. **The Lishak abstract and theorem disagree on the number of generators.**
   See section 5. The published version (J. Topol. Anal., DOI
   10.1142/S1793525317500182) was not accessed.
6. **No source decides AC-equivalence or AC-triviality.** I searched for such a
   result and found none; the statements I did find are the open problems
   recorded in sections 7 and 8.
7. **The length-13 classification in rank 2 is not verified here.** The claim
   that every balanced two-generator presentation of the trivial group with
   total relator length at most 13 is either AC-trivialisable or AC-equivalent
   to $AK(3)$ is attributed to Havas and Ramsay, *Breadth-first search and the
   Andrews-Curtis conjecture*, Internat. J. Algebra Comput. **13** (2003), 61-68
   in Bridson's bibliography. I did not read it and I do not assert it; it
   belongs to the computational direction.
8. **Not read by me:** Adian 1955; Gersten 1992; Krstic and McCool 1997;
   Kiralis, Krstic and McCool 1996; Diekert, Laun and Ushakov 2012; Myasnikov,
   Ushakov and Won 2011; Miasnikov and Myasnikov 2001; Havas and Ramsay 2003;
   Casson 2003; Roman'kov, arXiv:2305.11838; Lishak and Nabutovsky,
   arXiv:1504.05927 beyond its metadata.
9. **Not verified by me:** the triviality of any presentation in Bridson's
   Theorem A or in Lishak's theorems, and every lower bound quoted. My
   computations check bookkeeping only: the conjugate-counter recursion, the
   constant 24, and the total length of the explicit example.

---

## 12. Verification log

All commands were run in this directory, with `python3` from PATH on the shared
VM.

```
$ python3 survey/complexity_check.py
PASS conjugate count: n=2, m=0: max reached 1 == fib(m+2) 1
...                                    (30 conjugate-count lines, n = 2, 3, 4
                                        and m = 0, ..., 9; all PASS)
PASS conjugate count: n=4, m=9: max reached 89 == fib(m+2) 89
PASS offset: with n=2, m=6 the sharp bound is fib(8)=21, not fib(6)=8
PASS Delta(0)=2
PASS Delta(1)=4
PASS Delta(2)=16
PASS Delta(3)=65536
PASS Delta(m) = 2^^(m+1)
PASS Theorem A unpacked: k=1, n=2^1, length <= 24(n+1)=72, bound Delta(floor(log2 n))=4 > 2^^k=2
PASS Theorem A unpacked: k=2, n=2^2, length <= 24(n+1)=120, bound Delta(floor(log2 n))=16 > 2^^k=4
PASS Theorem A unpacked: k=3, n=2^3, length <= 24(n+1)=216, bound Delta(floor(log2 n))=65536 > 2^^k=16
PASS Theorem A unpacked (by bit length): k=4, n=2^4, length <= 408, bound Delta(4) = 2^65536 has bit length 65537 > 65536 = 2^^4
PASS Delta(k) > 2^^k by induction: base k=1 is 4 > 2, [line continues]
PASS Theorem A constant: 2*8 + 2*(12n+3) = 46 <= 24(n+1) = 48 for n=1
PASS Theorem A constant: 2*8 + 2*(12n+3) = 70 <= 24(n+1) = 72 for n=2
PASS Theorem A constant: 2*8 + 2*(12n+3) = 142 <= 24(n+1) = 144 for n=5
PASS Theorem A constant: 2*8 + 2*(12n+3) = 2422 <= 24(n+1) = 2424 for n=100
PASS Theorem A constant: 2*8 + 2*(12n+3) = 24022 <= 24(n+1) = 24024 for n=1000
PASS three basic moves give the dihedral count c_j+c_i = (1,2)

explicit example (Bridson 2015, section 7.4): relator lengths [9, 9, 407, 407], total 832, 4 generators and 4 relators
PASS explicit example: 4 generators and 4 relators (balanced)
PASS explicit example: total relator length 832 is at most 4*10^4, [line continues]
PASS explicit example: each relator is freely reduced (no c c^-1 subword)

ALL CHECKS PASSED
```

Two lines are abridged above with the marker "line continues", because they
repeat the assertion in words; nothing else is changed.

The script exits 0 and prints 50 `PASS` lines with no `FAIL`. It uses no
randomness and no wall-clock dependence, so the output is reproducible.

Text extraction: I downloaded the arXiv e-prints
`https://arxiv.org/e-print/1504.04187` and `https://arxiv.org/e-print/1504.00418`
and read `ACconjARXIV.tex` and `borisgroup22.tex` directly, so all theorem
statements above are from the authors' LaTeX. For the ICM 2006 survey I used
`pdftotext` on `https://people.maths.ox.ac.uk/bridson/papers/bridsonicm.pdf`.
For the Kourovka Notebook I downloaded `https://arxiv.org/src/1401.0300`, which
unpacks to `21tkt.tex`, and read Problem 1.12 at line 349 and the answer to
Problem 18.89 at lines 11322 to 11332.

---

## 13. Bibliography

Primary sources read.

* J. J. Andrews and M. L. Curtis, *Free groups and handlebodies*, Proc. Amer.
  Math. Soc. **16** (1965), 192-195. DOI 10.1090/S0002-9939-1965-0173241-8.
  Origin of the moves and the conjecture.
* M. R. Bridson, *The complexity of balanced presentations and the
  Andrews-Curtis conjecture*, arXiv:1504.04187, 25 pages, submitted 16 April
  2015. Preprint, no journal reference as of the sources I checked. Source of
  every lower bound in sections 2, 3 and 4.
* M. R. Bridson, *Non-positive curvature and complexity for finitely presented
  groups*, International Congress of Mathematicians Vol. II, Eur. Math. Soc.,
  Zurich 2006, 961-987. Section 4.4 announces the lower bounds; I read the
  author's PDF.
* B. Lishak, *Balanced finite presentations of the trivial group*,
  arXiv:1504.00418, DOI 10.1142/S1793525317500182 (Journal of Topology and
  Analysis). Source of section 5.
* B. Lishak and A. Nabutovsky, *Balanced presentations of the trivial group and
  four-dimensional geometry*, arXiv:1504.05927, DOI 10.1142/S1793525317500042.
  Metadata only.
* E. I. Khukhro and V. D. Mazurov (eds.), *Unsolved Problems in Group Theory.
  The Kourovka Notebook*, No. 21, Nottingham and Novosibirsk 2026,
  arXiv:1401.0300. Problem 1.12 (Magnus, communicated by Greendlinger) and
  Problem 18.89 with its archived answer.
* R. H. Gilman and A. G. Myasnikov, *Andrews-Curtis groups*, J. Groups
  Complexity Cryptology **16** (2024), issue 1, article 7, special issue in
  memory of Ben Fine. Reformulation of the conjecture as transitivity on normal
  generators, and the computability remark quoted in section 7.3.
* M. O. Rabin, *Recursive unsolvability of group theoretic problems*, Ann. of
  Math. (2) **67** (1958), 172-194. DOI 10.2307/1969933. Undecidability of
  triviality in general.
* S. Gadgil, *On the Andrews-Curtis conjecture and algorithms from topology*,
  arXiv:math/0108053, 2001. Abstract only.
* D. Panteleev and A. Ushakov, *Conjugacy search problem and the Andrews-Curtis
  conjecture*, arXiv:1609.00325, 2016. Metadata and abstract; relevant to the
  rank 2 search literature and to the realisation of $\mathrm{Aut}(F_2)$ on
  $AK(n)$.

Cited but not read by me (each is named in the body where it is used).

* S. I. Adian, 1955, undecidability of the word and triviality problems.
* S. M. Gersten, *Dehn functions and $l_1$-norms of finite presentations*, MSRI
  Publ. 23, Springer 1992, 195-224.
* V. Diekert, J. Laun and A. Ushakov, STACS 2012, LIPIcs **14**, 218-229.
* A. G. Myasnikov, A. Ushakov and D. W. Won, J. Algebra **345** (2011), 324-342.
* A. D. Miasnikov and A. G. Myasnikov, in Ohio State Univ. Math. Res. Inst.
  Publ. 8, de Gruyter 2001, 257-263.
* A. Casson, *Some algebraic questions related to the Poincare conjecture*,
  unpublished manuscript, Yale 2003.
* S. Krstic and J. McCool, J. London Math. Soc. (2) **56** (1997), 264-274.
* G. Kiralis, S. Krstic and J. McCool, Proc. London Math. Soc. (3) **73**
  (1996), 481-720.
* S. V. Roman'kov, arXiv:2305.11838, 2023.
* A. N. Platonov, *An isoperimetric function of the Baumslag-Gersten group*,
  Moscow Univ. Math. Bull. **59** (2004), 12-17.
