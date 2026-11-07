# Special classes of balanced presentations where the Andrews-Curtis conjecture is settled

Direction D9, member m1, Round 1, 2026-11-04.

This file records which classes of balanced presentations are known to satisfy the Andrews-Curtis conjecture, the exact statement of each result, and where each result is proved. It also records the short arguments I completed myself, and a script that replays every move sequence claimed here. Statements carry one of four labels.

- `[proved here]` means a complete proof is written out below, with a rerunnable check in `survey/special-classes-check.py`.
- `[verified]` means I read the statement in the cited paper or preprint, and the bibliographic data were checked against Crossref or arXiv.
- `[reported]` means a source I read asserts the statement, and I did not read the primary paper for it.
- `[unverified]` means I did not find a source I could check.

The section on computation is separate from the section on interpretation on purpose. Nothing here is a claim of proof or disproof of the conjecture.

## 1. Conventions and the three moves

Let $n \ge 1$ and let $F_n$ be the free group on $x_1,\dots,x_n$. A presentation $\langle x_1,\dots,x_n \mid r_1,\dots,r_n\rangle$ with $r_i \in F_n$ is balanced. Let $N(r)$ be the normal closure of $\{r_1,\dots,r_n\}$ in $F_n$ and let $G(r) = F_n/N(r)$ be the group presented. The standard tuple is $r^{0} = (x_1,\dots,x_n)$, which presents the trivial group.

The Andrews-Curtis moves act on one entry at a time, and my numbering is the following.

1. $r_i \mapsto r_i^{-1}$;
2. $r_i \mapsto r_i r_j$ for $j \ne i$;
3. $r_i \mapsto w r_i w^{-1}$ for any $w \in F_n$.

Havas and Ramsay number these AC2, AC1 and AC3 in that order, and they restrict move 3 to conjugating by a single generator or its inverse. Two conventions give the same equivalence relation. Conjugation by $w = y_1 \cdots y_k$ is the composite of the conjugations by $y_1,\dots,y_k$, so restricting to generators loses nothing. Writing $w^{-1} r_i w$ instead of $w r_i w^{-1}$ also loses nothing, because $w$ ranges over the whole group.

Two tuples are AC-equivalent, written $r \sim s$, when some finite sequence of moves takes $r$ to $s$. A tuple is AC-standard when $r \sim r^0$. The conjecture of Andrews and Curtis [1] states that every balanced presentation of the trivial group is AC-standard.

**Fact F1 (the presented group is an invariant).** If $r \sim s$ then $N(r) = N(s)$, so $G(r) \cong G(s)$.

*Proof.* Move 1 and move 3 keep the normal closure of the entries. For move 2, suppose $s$ is obtained from $r$ by replacing $r_i$ with $r_i r_j$. Every entry of $s$ lies in $N(r)$, so $N(s) \subseteq N(r)$. Conversely $r_i = (r_i r_j) r_j^{-1}$ lies in $N(s)$, so $N(r) \subseteq N(s)$. A finite sequence of moves composes these equalities. $\square$

Consequently a tuple that presents a nontrivial group is never AC-standard, and the conjecture concerns only the trivial group. This is the first filter for any candidate counterexample.

## 2. Lemmas proved here

Throughout, $r$ is a tuple of rank $n$ and entries are words in reduced form. A move sequence is written as a chain of tuples, and each step of the chain is one of the three moves of Section 1.

**Lemma 1 (the moves are reversible).** Each of the three moves can be undone by finitely many moves, so AC-equivalence is an equivalence relation.

*Proof.* Move 1 is its own inverse. Move 2 is undone by multiplying entry $i$ by $r_j^{-1}$, which is move 1 on entry $j$, then move 2, then move 1 on entry $j$ again. Move 3 is undone by conjugating by $w^{-1}$. Reflexivity and transitivity hold by definition of the reflexive transitive closure. $\square$

**Lemma 2 (two entries can be interchanged).** Let $i \ne j$ and let $a, b$ be the entries at those positions. Seven moves, each changing only entries $i$ and $j$, exchange them and fix every other entry. The moves realise

$$(a,b) \longmapsto (ab,\, b) \longmapsto (ab,\, a^{-1}) \longmapsto (aba^{-1},\, a^{-1}) \longmapsto (aba^{-1},\, a) \longmapsto (b,\, a).$$

*Proof.* Apply move 2 to entry $i$. Then invert entry $i$, apply move 2 to entry $j$, and invert entry $i$ back; the middle entry becomes $b(ab)^{-1} = b b^{-1} a^{-1} = a^{-1}$, which is an identity valid for all words $a,b$ in a group. Apply move 2 to entry $i$ again, getting $aba^{-1}$, then invert entry $j$, getting $a$, then conjugate entry $i$ by $w = a^{-1}$, getting $a^{-1}(aba^{-1})a = b$. The count is seven moves, and only entries $i$ and $j$ were touched. $\square$

Check T1 replays this on 200 random tuples at ranks 2 and 3, and it compares the resulting tuple with the one expected.

**Lemma 3 (multiplying by an inverse).** Replacing $r_i$ by $r_i r_j^{-1}$ takes three moves and leaves $r_j$ as it was. More generally $r_i \mapsto r_i r_j^{k}$ for $k \in \mathbb{Z}$ takes at most $3|k|$ moves.

*Proof.* Invert entry $j$, apply move 2, invert entry $j$ again. Iterate, using move 1 for the sign of $k$. $\square$

**Lemma 4 (exponent sums).** For a word $w$ let $\varepsilon(w) \in \mathbb{Z}^n$ have $k$-th coordinate equal to the exponent sum of $x_k$ in $w$. The map $\varepsilon$ is a homomorphism $F_n \to \mathbb{Z}^n$. For a tuple $r$ of rank $n$ let $A(r)$ be the $n \times n$ integer matrix whose $i$-th row is $\varepsilon(r_i)$.

(a) Move 1 negates row $i$, move 2 adds row $j$ to row $i$, and move 3 leaves every row unchanged. Hence the subgroup of $\mathbb{Z}^n$ spanned by the rows of $A(r)$, and also $|\det A(r)|$, are unchanged by every AC move.

(b) If $r$ is a balanced presentation of the trivial group then $A(r)$ is unimodular: $\det A(r) = \pm 1$ and the rows span $\mathbb{Z}^n$.

(c) Therefore every member of the class the conjecture is about has a unimodular exponent-sum matrix, so this invariant cannot separate two members of that class.

(d) The invariant is still a useful filter. If $|\det A(r)| \ne 1$ then $r$ is not AC-standard. At rank 2, the tuple $(x,1)$ has $A = \mathrm{diag}(1,0)$ and the tuple $([x,y],y)$ has rows $(0,0)$ and $(0,1)$; both present $\mathbb{Z}$ and both have determinant $0$.

*Proof.* Part (a) is a direct computation on exponent sums: conjugation fixes every exponent sum, and the other two moves are elementary row operations. For part (b), the abelianised presentation has $H_1(G(r)) = \mathbb{Z}^n / \mathrm{rowspan}(A(r))$, and a group with $H_1 = 0$ forces the row span to be all of $\mathbb{Z}^n$. For a square integer matrix, spanning $\mathbb{Z}^n$ is equivalent to having determinant $\pm 1$, since the index of the row span is $|\det A(r)|$ when the determinant is nonzero. Part (c) restates (b). Part (d) follows from (a) and the standard tuple $A(r^0) = I_n$. $\square$

Checks T5 and T7 test part (a) numerically and compute the four determinants, so part (a) has a machine check and parts (b) and (c) rest on the proof.

**Lemma 5 (deleting a generator letter).** Suppose entry $i$ of $r$ is the one-letter word $x$, where $x$ is one of the generators, and let $j \ne i$. Let $\rho \colon F_n \to F_{n-1}$ be the retraction that kills $x$ and fixes the other generators; on reduced words $\rho$ deletes every letter $x^{\pm 1}$ and reduces. Then moves that change only entry $j$ make entry $j$ conjugate to $\rho(r_j)$, and one further conjugation makes it equal to $\rho(r_j)$.

*Proof.* Write the current entry as $u x^{\epsilon} v$ with $\epsilon = \pm 1$. Three moves replace it by $v u$. First conjugate by $u^{-1}$, giving $x^{\epsilon} v u$. Then multiply by $x^{-\epsilon}$, which is legal by Lemma 3, giving $x^{\epsilon} v u x^{-\epsilon}$. Then conjugate by $x^{-\epsilon}$, giving $v u$. Iterate until entry $j$ contains no letter $x^{\pm 1}$. Each step replaces the entry by a conjugate of itself with one letter deleted, and $\rho$ of a conjugate is a conjugate of $\rho$. At the end the entry lies in $F_{n-1}$, so it equals its own $\rho$-image, and it is conjugate to $\rho(r_j)$. Conjugation by an explicit word then makes it equal to $\rho(r_j)$. Entry $i$ is only used as the word $x$, so the three moves of Lemma 3 that restore $r_i^{-1}$ keep it equal to $(x)$. $\square$

Check T2 replays the deletion step on 120 random relators at ranks 2 and 3, and it searches for the final conjugator and verifies that the other entries are untouched.

**Theorem 6 (a relator conjugate to a generator).** Let $r$ be a tuple and suppose entry $i$ is conjugate in $F_n$ to a generator $x$. Then $r$ is AC-equivalent to the tuple that has $(x)$ at position $i$ and $\rho(r_j)$ at every other position $j$, where $\rho$ is the retraction killing $x$. Consequently, if the $(n-1)$-generator tuple $(\rho(r_j))_{j \ne i}$ is AC-standard, then $r$ is AC-standard.

*Proof.* One move 3, together with move 1 if the conjugate is $x^{-1}$, puts the entry at position $i$ into the form $(x)$. Then apply Lemma 5 to each other entry in turn. For the consequence, take a sequence of moves that trivialises the reduced tuple in $F_{n-1}$ and apply the same moves to the corresponding entries of $r$ in $F_n$. Each such move inverts an entry, multiplies one entry by another, or conjugates an entry by a word in the remaining generators, and all three are legal moves of the $n$-tuple that leave position $i$ at $(x)$. $\square$

I do not prove the converse implication, that AC-standard $r$ forces the reduced tuple to be AC-standard. Nothing below needs it.

**Corollary 7 (rank 2, a relator conjugate to a generator).** Let $r = (r_1,r_2)$ be a balanced rank 2 presentation of the trivial group, and suppose $r_1$ is conjugate to $x$ or to $y$. Then $r$ is AC-standard.

*Proof.* If $r_1$ is conjugate to $y$, apply Lemma 2 to interchange the two entries. Now $r_1$ is conjugate to $x$. Theorem 6 gives $r \sim (x, \rho(r_2))$, where $\rho(r_2)$ is a word in the single generator $y$. By Fact F1 the tuple $(x,\rho(r_2))$ presents the trivial group, and its group is the cyclic group $\langle y \mid \rho(r_2)\rangle$. A cyclic group is trivial only when the relator is $y$ or $y^{-1}$, so $\rho(r_2) = y^{\pm 1}$. Move 1 then gives the standard tuple. $\square$

Check T3 runs this argument on all 3506 tuples $(x,w)$ with $|w| \le 8$ and $y$-exponent sum equal to $\pm 1$. Check T8 runs it on 135 tuples whose first relator is a nontrivial conjugate of $x$, which also exercises the conjugator search of Lemma 5.

**Corollary 8 (signed permutations of the generators).** For every permutation $\sigma$ of $\{1,\dots,n\}$ and every choice of signs $\epsilon_i = \pm 1$, the tuple $(x_{\sigma(1)}^{\epsilon_1},\dots,x_{\sigma(n)}^{\epsilon_n})$ is AC-standard. The cost is seven moves per transposition used to sort the tuple, plus one move per negative sign.

*Proof.* Lemma 2 interchanges entries and move 1 fixes signs. $\square$

Check T4 verifies all signed permutations at ranks 2, 3 and 4 by building the explicit move sequence for each of the 440 tuples involved.

**Observation 9 (no repeated or empty relators).** A balanced presentation of the trivial group has no empty relator and no two equal relators.

*Proof.* If an entry is empty, or if two entries are equal, then the normal closure $N(r)$ is the normal closure of at most $n-1$ elements. Then $G(r)^{\mathrm{ab}} = \mathbb{Z}^n / M$, where $M$ is spanned by at most $n-1$ vectors, so $M$ has rank at most $n-1$ and the quotient is nonzero. In particular $G(r)$ is nontrivial. $\square$

This is a pruning rule for searches. It also shows that the two examples in Lemma 4(d) are of different kinds, since $(x,1)$ has an empty relator and $([x,y],y)$ does not.

## 3. Classes settled in the literature

Each entry gives the class, the exact statement, and the source. The numbered classes are the answer to the direction: these are the classes where the conjecture is known.

**C1. Rank 1, all presentations.** `[proved here]`

A balanced rank 1 presentation is $\langle x \mid r\rangle$ with $r = x^{k}$ for some integer $k$. The group is trivial exactly when $k = \pm 1$, and move 1 relates $x$ to $x^{-1}$. So every balanced rank 1 presentation of the trivial group is AC-standard, with no hypothesis left over.

**C2. Rank 2, a relator conjugate to a generator, all presentations of the trivial group.** `[proved here]`

This is Corollary 7. I did not find this statement in the sources I read, and the proof above is mine.

**C3. Signed permutations of the generators, any rank.** `[proved here]`

This is Corollary 8. It is a special case of C2 at rank 2.

**C4. Gordon's family $G_q$, for every $q \in \mathbb{N}$.** `[verified]`

Let $G_q = \langle x,y \mid x = x^{-1}y^{-1}xy,\; y = y^{-1}x^{-q}yx^{q}\rangle$. Then $G_q$ satisfies the Andrews-Curtis conjecture for all $q \in \mathbb{N}$. This is Theorem 3.5 of Fernández, "Morse theory for group presentations", Trans. Amer. Math. Soc. (2024), DOI 10.1090/tran/8958, arXiv:1912.00115. The paper works with $Q^{**}$-transformations and states the conclusion as the Andrews-Curtis conjecture. I read the theorem and its proof in the arXiv version, and I did not verify the general step from $Q^{**}$-trivialisability to AC-trivialisability, which belongs to the literature on Q-transformations.

**C5. Rank 2, total relator length at most 12, all presentations of the trivial group.** `[reported]`

Havas and Ramsay state in the introduction of their 2003 paper: "Miasnikov and Myasnikov [9] have shown that the conjecture holds for all balanced presentations of the trivial group on two generators with the total length of the relators at most twelve." The reference [9] is Miasnikov and Myasnikov, "Balanced presentations of the trivial group on two generators and the Andrews-Curtis conjecture", Groups and Computation III (2001) 257-264. I did not read that paper. The result was obtained by a genetic algorithm that produces explicit move sequences.

**C6. Rank 2, total relator length at most 13, all presentations of the trivial group except one class.** `[verified]`

Havas and Ramsay prove the following theorem. Let $G$ be a group defined by a balanced presentation on two generators, with the sum of the relator lengths at most thirteen. Then:

(i) if $G$ has trivial abelianisation, $G$ is trivial or is isomorphic to the unique perfect group of order 120 (the paper writes $L_2(5)$ for this group);

(ii) if $G$ is trivial, its presentation is AC-equivalent to the standard presentation or to $\langle x,y \mid x^3 = y^4,\; xyx = yxy\rangle$.

The proof enumerates canonical forms of presentations, uses coset enumeration to decide triviality, and uses breadth-first search over AC moves. For the length 13 list, twelve presentations could not be reduced; they fall into two orbits, with representatives $\langle a^3=b^4,\;aba=bab\rangle$ and $\langle ab=bbaa,\;ba=aaabb\rangle$, and the paper shows these twelve are pairwise AC-equivalent. An exhaustive search allowed each relator to grow in length by at most five and found no length-decreasing chain for them. So the second presentation in part (ii) is the sole surviving candidate at length 13, and its AC status is not settled by that theorem.

**C7. Named presentation AK(2) = $\langle x,y \mid xyx = yxy,\; x^2 = y^3\rangle$.** `[verified]` (replayed)

Miasnikov, "Genetic algorithms and the Andrews-Curtis conjecture", IJAC 9 (1999) 671-686, gives a chain of 19 published lines reducing this presentation to the tuple $(y,x)$, which Lemma 2 carries to the standard tuple. I replayed all 19 lines in check T6 and compared every intermediate word with the published one; they agree, and seven further moves reach $(x,y)$. So this presentation is AC-standard.

**C8. Miller-Schupp members $MS_n(w^*)$ for $n = 3,\dots,8$.** `[reported]`

Lisitsa, "New Andrews-Curtis trivializations for Miller-Schupp group presentations", Examples and Counterexamples 6 (2024) 100168, reports previously unknown trivialisations of a parametric family $MS_n(w^*)$, $n = 3,\dots,8$, inside the Miller-Schupp family, and states two conjectures about the structure of the simplifications. The trivialisations are explicit sequences produced by automated reasoning. I read the abstract and verified the bibliographic data, and I did not check the sequences.

**C9. Miller-Schupp member $MS_9(w^*)$.** `[reported]`

Lisitsa, "Automated theorem proving reveals a lengthy Andrews-Curtis trivialization for a Miller-Schupp trivial group presentation", Examples and Counterexamples 8 (2025) 100201, reports a trivialisation of $MS_9(w^*)$ with 8634 elementary moves, produced by Prover9 with about 74 days of computation and over 56 GB of memory, as stated in the abstract. I did not check the sequence.

**C10. Rank 3, a relator conjugate to a generator, reduced pair of total length at most 13.** `[proved here]` (uses C6)

Let $r$ be a balanced rank 3 presentation of the trivial group, suppose that some entry is conjugate to a generator $x$, let $\rho$ be the retraction that kills $x$, and let $s, t$ be the images under $\rho$ of the two remaining entries. If $|s| + |t| \le 13$ then $r$ is AC-standard, unless the pair $(s,t)$ is AC-equivalent to $AK(3) = \langle a,b \mid a^3=b^4,\; aba=bab\rangle$.

*Proof.* Lemma 2 moves the entry that is conjugate to $x$ into position 1, and Theorem 6 gives $r \sim (x,s,t)$ with $s$ and $t$ words in the other two generators. By Fact F1 the rank 3 tuple $(x,s,t)$ presents the trivial group, so the rank 2 presentation $(s,t)$ presents the trivial group. By C6 that rank 2 presentation is AC-equivalent to the standard pair or to $AK(3)$. In the first case the moves that trivialise the pair, applied to positions 2 and 3, carry $(x,s,t)$ to the standard tuple. In the second case this argument says nothing. $\square$

Check T9 runs the reduction step of the proof at rank 3 on 80 random pairs of relators.

## 4. The named families, and where the boundary lies

**Akbulut-Kirby.** Miasnikov and Havas-Ramsay write the family as $AK(n) = \langle a,b \mid a^n = b^{n+1},\; aba = bab\rangle$ with $n \ge 2$. Akbulut and Kirby introduced it in Topology 24 (1985) 375-390; I verified the bibliographic data and did not read the paper, so I do not know the original indexing. Members at total relator length at most 12 are AC-standard by C5, which covers $AK(2) = \langle a,b \mid aba=bab,\;a^2=b^3\rangle$ explicitly, and $AK(2)$ has a published proof replayed in C7. The presentation $AK(3) = \langle a,b \mid aba=bab,\;a^3=b^4\rangle$, of total length 13, is exactly the exception in C6.

**Miller-Schupp.** Miller and Schupp, "Some presentations of the trivial group", Contemp. Math. 250 (1999) 113-115, prove that $\langle a,b \mid a^{-1}b^n a = b^{n+1},\; a = w\rangle$ presents the trivial group whenever $n > 0$ and $w$ has exponent sum 0 on $a$. Their Theorem 1 is more general: a perfect group generated by $a,b$ and satisfying $a^{-1}b^n a = b^m$ with $n,m > 0$ coprime is trivial. I read the three page paper. Small members are covered by C5, C6 and C8, C9.

**Gordon.** The family $G_{n,m,p,q} = \langle x,y \mid x = [x^m,y^n],\; y = [y^p,x^q]\rangle$ is attributed to Gordon by Fernández, who cites Gordon's 1984 survey for the presentations and proves the subfamily C4. I did not read Gordon's survey. Fernández also records, citing a reference I did not identify, a computer proof covering the members of this sequence with total relator length at most 14.

**Why AK(3) is outside every class above.** Neither relator of $AK(3)$ is conjugate to a generator: the cyclic reductions of $xyx(yxy)^{-1}$ and $x^3y^{-4}$ have lengths 6 and 7, while a conjugate of a generator has cyclic reduction of length 1. So C2 does not apply. Lemma 4 does not exclude $AK(3)$ either, because its exponent-sum matrix has rows $(1,-1)$ and $(3,-4)$ and determinant $-1$. The presentations of C4 have a fixed first relator and are not $AK(3)$.

## 5. What these lemmas give a search, and what they do not

The following three filters are cheap and exact. A candidate counterexample must pass all of them: its group must be trivial (Fact F1), its exponent-sum matrix must be unimodular (Lemma 4), and its relators must be distinct and nonempty (Observation 9). $AK(3)$ passes all three.

Corollary 7 gives a success criterion rather than a filter. If a search ever reaches a tuple in the AC class of $AK(n)$ that has some relator conjugate to a generator, then that presentation is AC-standard and the search has succeeded. Lemma 2 makes the position of that relator irrelevant.

C10 makes the criterion concrete at rank 3. If a rank 3 candidate has a relator conjugate to a generator and the reduced pair has total length at most 13, then the candidate is AC-standard unless that pair lies in the AC class of $AK(3)$.

Theorem 6 is a reduction, and it is sharp in one direction. The hypothesis that the relator is a single generator letter cannot be weakened to a proper power, because if an entry is $x^k$ with $|k| \ge 2$ then the first row of $A(r)$ is $k$ times a vector, so $|\det A(r)|$ is divisible by $|k|$ and Lemma 4 shows the group cannot be trivial.

The literature classes C5 and C6 are statements about bounded total relator length. They cannot be extended by raising the bound alone in any practical way, and they say nothing about $AK(3)$. In particular no class recorded here settles $AK(3)$, and none of C1 to C10 lists $AK(3)$ among its members.

## 6. Questions left open by this direction

These questions are mine, and they are labelled as questions rather than results. Each is phrased so that either answer would be informative.

1. Is every $AK(n)$, $n \ge 3$, AC-standard? The sources I read present this as open. Havas and Ramsay show $AK(3)$ is the only candidate at total relator length 13, and Panteleev and Ushakov describe the same presentation as the shortest potential counterexample.

2. Is the exponent-sum identity class AC-trivial? Precisely: if a balanced $n$-tuple presents the trivial group and $A(r) = I_n$, is $r$ AC-standard? Lemma 4 gives only necessity, and a negative answer would be a counterexample to the conjecture, so this is a restricted form of the conjecture with a strong abelian hypothesis.

3. Must the relator lengths grow during a proof? Havas and Ramsay report that $AK(2)$ has no proof in which every intermediate presentation has total relator length at most 12, that length 13 makes a proof of 19 essential moves possible, and that length 15 allows a proof of 14 essential moves. Is there a family of AC-standard presentations for which the necessary growth is unbounded?

4. Is there a deletion lemma for primitive relators of length greater than one? Theorem 6 replaces a relator that is a generator by the retraction that kills it. For $p = xy$ the same trick does not work, because multiplying by $p^{-1}$ cancels one letter and appends another. I do not know whether presentations with a relator equal to a fixed primitive word $p$ reduce to the quotient by $p$.

## 7. Computation

The script is `survey/special-classes-check.py`, and the identical working copy is `.ultramath/smw2fzjic/m1/special_classes_check.py`. It needs only Python 3 and its standard library.

The command below was run on 2026-11-04 from the project root. The same file run as `python3 survey/special-classes-check.py` from the project root gives the same output.

```
cd .ultramath/smw2fzjic/m1 && python3 special_classes_check.py
```

The output was as follows.

```
special_classes_check.py  (seed 20261104)
PASS T1  Lemma 2 replayed on 200 random tuples (7 moves each)
PASS T2  Lemma 5 replayed on 120 random relators (ranks 2, 3)
PASS T3  3506 tuples (x, w) with |w| <= 8 and y-exponent sum +-1, longest chain 36 moves
PASS T4  all signed permutations of rank 2, 3, 4 reach the standard tuple
PASS T5  |det| and row lattice preserved along 60 walks of 25 moves
PASS T6  19 published lines replay exactly, then 7 moves give (a, b)
PASS T7  det AK(2) = 1, det AK(3) = -1, det(x,1) = 0, det([x,y],y) = 0
PASS T8  Corollary 7 with r_1 conjugate to x, 135 random cases
PASS T9  Theorem 6 at rank 3, 80 random pairs of relators, other entries fixed

ALL CHECKS PASSED
```

The list below records what each check establishes and what it does not. The checks are consistency tests, and the general statements rest on the proofs of Section 2.

- T1, T2, T3, T4 and T8 build every move sequence from the three moves of Section 1 and verify the final tuple word by word. They are consistency checks on the proofs of Lemmas 2 and 5 and of Corollaries 7 and 8, on the stated ranges. They are not proofs of those lemmas, since the lemmas quantify over all words and the checks sample or bound the length.
- T5 checks Lemma 4(a) on random walks of 25 moves, comparing determinants and testing that each exponent-sum row of the final matrix lies in the integer row lattice of the initial one and conversely. The lattice test is exact and applies when the initial determinant is nonzero.
- T6 replays the 19 published lines of Miasnikov's reduction of $AK(2)$ and compares intermediates with the published words. This is a check of a published claim restricted to the transcription I made of it. A transcription error in the published words would show up as a mismatch only if the error changed the group element, and my transcription came from the PDF of arXiv:math/0304306.
- T7 computes four determinants. The $AK(3)$ value $-1$ is the number quoted in Section 4, and the two zero values are the examples of Lemma 4(d).
- T9 checks the reduction used in C10 at rank 3, deleting the letters of the generator relator from both other entries and then finding the conjugators, with the generator relator verified unchanged at the end.

The script contains no floating point arithmetic. Its only randomness is `random.Random(20261104)`, which is printed at the start of the output.

## 8. What I could not verify

- I did not read Akbulut and Kirby, Topology 24 (1985) 375-390. The form of $AK(n)$ used here is the form in Miasnikov (1999) and Havas and Ramsay (2003), and the original indexing may differ.
- I did not read Miasnikov and Myasnikov (2001), so C5 rests on the statement of it in Havas and Ramsay (2003).
- I did not read Lisitsa (2024, 2025) beyond their abstracts, so the trivialisations in C8 and C9 are reported and unchecked.
- I did not read Havas and Ramsay's companion paper [8] on proof words extracted from coset enumerations, so no statement above depends on it.
- I did not read Wright's paper [15] on the topological interpretation of the moves, so no statement above depends on it.
- I did not read Burns and Macedońska, "Balanced presentations of the trivial group", Bull. London Math. Soc. 25 (1993) 513-526, which several sources call the group-theoretic survey of the problem.
- I did not read Gordon's survey, so the attribution of the family $G_{n,m,p,q}$ to Gordon is reported from Fernández.
- I did not identify or read the reference that Fernández cites for the computer proof at total relator length 14, so that sentence in Section 4 rests on her paper alone.
- I read only the abstract of Ivanov, "On conjectures of Andrews and Curtis", Proc. Amer. Math. Soc. 146 (2018) 2283-2298. That abstract states that the conjecture is equivalent to a version in which arbitrary conjugations are replaced by cyclic permutations, and that a cancellative version without stabilisations is false. I do not use either statement above.
- I read only the abstract and HTML excerpt of Panteleev and Ushakov, "Conjugacy search problem and the Andrews-Curtis conjecture", Groups Complexity Cryptology 11 (2019) 43-60. I use it only as corroboration that $AK(3)$ is described as the shortest potential counterexample.
- I did not confirm a bibliographic record for the problem list of Ol'shanskii and Sapir, "Open problems in combinatorial group theory". A PDF retrieved from a Stevens Institute page attributes a positive result for free solvable groups to A. G. Myasnikov, "Extended Nielsen transformations and the trivial group", Mat. Zametki 35 (1984) 491-495. I did not read that Russian paper, so I make no class statement from it.

## 9. References

Bibliographic data below were checked against Crossref or arXiv on 2026-11-04. Items 8, 14 and 15 are background that no statement above depends on.

1. J. J. Andrews and M. L. Curtis, Free groups and handlebodies, Proc. Amer. Math. Soc. 16 (1965) 192-195, DOI 10.1090/S0002-9939-1965-0173241-8.
2. S. Akbulut and R. Kirby, A potential smooth counterexample in dimension 4 to the Poincare conjecture, the Schoenflies conjecture, and the Andrews-Curtis conjecture, Topology 24 (1985) 375-390, DOI 10.1016/0040-9383(85)90010-2. (Not read.)
3. R. G. Burns and O. Macedońska, Balanced presentations of the trivial group, Bull. London Math. Soc. 25 (1993) 513-526, DOI 10.1112/blms/25.6.513. (Not read.)
4. C. F. Miller III and P. E. Schupp, Some presentations of the trivial group, Contemp. Math. 250 (1999) 113-115, DOI 10.1090/conm/250/03848. (Read.)
5. A. D. Miasnikov, Genetic algorithms and the Andrews-Curtis conjecture, Internat. J. Algebra Comput. 9 (1999) 671-686, DOI 10.1142/S0218196799000370, arXiv:math/0304306. (Read.)
6. A. D. Miasnikov and A. G. Myasnikov, Balanced presentations of the trivial group on two generators and the Andrews-Curtis conjecture, Groups and Computation III (2001) 257-264, DOI 10.1515/9783110872743.257. (Not read.)
7. G. Havas and C. Ramsay, Breadth-first search and the Andrews-Curtis conjecture, Internat. J. Algebra Comput. 13 (2003) 61-68, DOI 10.1142/S0218196703001365. (Read.)
8. G. Havas and C. Ramsay, Andrews-Curtis and Todd-Coxeter proof words, in Groups St Andrews 2001 in Oxford, London Math. Soc. Lecture Note Ser. 304, Cambridge Univ. Press (2003) 232-237, DOI 10.1017/CBO9780511542770.022. (Abstract only.)
9. X. Fernández, Morse theory for group presentations, Trans. Amer. Math. Soc. (2024), DOI 10.1090/tran/8958, arXiv:1912.00115. (Read in the arXiv version.)
10. A. Lisitsa, New Andrews-Curtis trivializations for Miller-Schupp group presentations, Examples and Counterexamples 6 (2024) 100168, DOI 10.1016/j.exco.2024.100168. (Abstract only.)
11. A. Lisitsa, Automated theorem proving reveals a lengthy Andrews-Curtis trivialization for a Miller-Schupp trivial group presentation, Examples and Counterexamples 8 (2025) 100201, DOI 10.1016/j.exco.2025.100201. (Abstract only.)
12. S. Ivanov, On conjectures of Andrews and Curtis, Proc. Amer. Math. Soc. 146 (2018) 2283-2298, DOI 10.1090/proc/13710. (Abstract only.)
13. D. Panteleev and A. Ushakov, Conjugacy search problem and the Andrews-Curtis conjecture, Groups Complexity Cryptology 11 (2019) 43-60, DOI 10.1515/gcc-2019-2005. (Abstract and HTML excerpt only.)
14. C. Hog-Angeloni and W. Metzler, The Andrews-Curtis conjecture and its generalizations, in Two-Dimensional Homotopy and Combinatorial Group Theory, London Math. Soc. Lecture Note Ser. 197, Cambridge Univ. Press (1993) 365-380, DOI 10.1017/CBO9780511629358.014. (Not read.)
15. P. Wright, Group presentations and formal deformations, Trans. Amer. Math. Soc. 208 (1975) 161-169, DOI 10.1090/S0002-9947-1975-0380813-5. (Not read; bibliographic data only.)
