# Andrews-Curtis-Swarm

Code, Lean proofs and notes from an entry to the Andrews-Curtis Conjecture Challenge of the SAIR Foundation and Caltech. The challenge asks for short sequences of Andrews-Curtis moves that carry each of 10,115 balanced two-generator presentations of the trivial group to the standard presentation.

This repository contains no solution path and no list of solved ids. Paths stay private until the competition deadline of 30 November 2026, end of day Anywhere on Earth, and only the organisers may release them before then.

## What is here

`acc/` holds a search engine for the official move set. The engine is written in C for speed, and there is an independent Python implementation of the same fourteen moves for cross checking. `acc/crosscheck.py` compares the C engine, the Python engine and the official verifier on random states and random move sequences. `acc/greedy.py` is a greedy search that charges the true cost of rotating a relator before multiplying by it, and `acc/consolidate.py` and `acc/merge_best.py` build a best-path table and submission files and check them with the official verifier.

`lean/` holds Lean 4 proofs about the published statement. `lean/Derived.lean` proves that the reachability relation in the official statement file is an equivalence relation and that multiplication by an inverse relator is a derived move. `lean/Axioms.lean` reprints the axiom audit for each theorem.

`paper/acc.tex` is a short description of the method and the measured results. `notes/literature.md` is a dossier on prior work, assembled from six independently written parts, each of which keeps its own evidence standard. One part of that dossier lists which scored ids belong to the Akbulut-Kirby and Miller-Schupp families. Those labels contain no paths. They still form a per-id table, so the dossier is published only after the competition deadline and is not part of this repository before then.

## Method in one paragraph

A ball of radius eight around the target presentation is enumerated once and stored with exact distances. A breadth first search from a presentation to radius r then finds the shortest path whenever the distance is at most 8 + r, so short distances are decided exactly. Beyond that range a beam search over the fourteen moves, and a second beam over a coarser move set that rotates a relator to align a long common subword before multiplying, are used to find some path. Every path is replayed by the official verifier before it is accepted.

## Reproducing

The engine builds with a C compiler and needs no dependencies:

```
gcc -O2 -o acc/engine acc/engine.c -lm
```

The verifier and the Python tools need only Python 3 and the official repository, which is expected at `upstream/`. Build inputs with `python3 acc/mkinputs.py`, then run `python3 acc/crosscheck.py` to check the three move implementations against each other.

The Lean files are checked directly, without building Mathlib:

```
LEAN_PATH="$PWD/lean:$LEAN_PATH" lean lean/Axioms.lean
```

## Honest status

The engine and the Lean proofs are complete and checked. The search solved a minority of the scored pool, and both `paper/acc.tex` and the report in the private repository say so plainly. The stable track was not searched directly.

## The research campaign

`research/` holds a separate four-day research campaign on the conjecture itself, run in November 2026 with a multi-agent swarm and independent referees. It measured the neighbourhood of the conjecture and makes no claim for or against it. Its main results are a census of the balanced two-generator presentations of total length at most 14 (at length 14, 50 presentations are left undecided in at most 9 classes), an exact-peak ledger for 51,766 of 57,115 presentations from the AC-19 dataset, bounds on paths from AK(3), and a Lean 4 archive in `research/toolkit/lean/` whose axiom reports name only `propext`, `Classical.choice` and `Quot.sound`. `research/FINAL_REPORT.md` is the full report, `research/REPORT.md` is the ledger of results with their checks, and `research/directions/README.md` describes each working folder. Only six of the thirty-two direction folders are included here, because the others hold large raw search data.

## Licence

MIT. See `LICENSE`.

## Use of AI tools

The code, the Lean proofs and the prose were produced by Open Math OS agents under the direction of the author. Pragyaan Gaur checked the work and is the sole author.
