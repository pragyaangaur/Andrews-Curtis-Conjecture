#!/usr/bin/env python3
"""build_ac4.py -- assemble AC4.lean (round 4, direction G6 lean-program-4).

AC4.lean is `toolkit/lean/AC3.lean` verbatim, followed by three new sections:

  (i)   124 explicit Andrews-Curtis certificates, each replayed by the kernel with `decide` in
        blocks of at most twelve moves and glued with `checkCert_append`:
          * the 72 trivialisations of directions/resisters/std_certs.txt,
          * the 26 AK(3) hits of directions/resisters/ak3_hits_certs.txt,
          * the 21 merge paths of certs/spot22_paths.txt, whose common start is one of the 22
            resisters that round 3 left undecided at cap 20 and whose 21 targets are the other
            21, so those 22 presentations are one Andrews-Curtis class,
          * the five Carreras certificates of directions/c14/carreras/, completed to their
            declared target tuples by relator symmetries that are themselves AC moves;
  (ii)  the kernel form of the triviality of the presented group of every one of the 98
        resisters: `presentedGroup_subsingleton_iff` transported along the certificate, from
        `subsingleton_presentedGroup_standard` for the 72 and from `AK.ak_trivial 3` (the
        round-1 theorem of directions/ak-status/ak_trivial.lean, copied here verbatim) for the
        26;
  (iii) one `#print axioms` per theorem.

The certificate data is produced by `certs_replay.py`, which replays every move list in
independent Python first; this script refuses to build if any replay fails.

    python3 build_ac4.py                       # build AC4.lean next to this script
    python3 build_ac4.py --out /path/AC4.lean  # elsewhere
"""
import argparse
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def find_repo():
    d = HERE
    for _ in range(8):
        if os.path.isdir(os.path.join(d, 'directions', 'resisters')):
            return d
        d = os.path.dirname(d)
    sys.exit('cannot locate the repository root from %s' % HERE)


REPO = find_repo()

HEADER = r'''
/-! ## (i) Round-4 certificates: the 98 resisters, the 21 merge paths, the five Carreras files

Everything above this line is `toolkit/lean/AC3.lean` verbatim, so `AC4.lean` is that file
followed by this section: the file is checked by the single command `lean AC4.lean` and needs no
import beyond `Mathlib`.  This section proves no new general theorem about Andrews-Curtis
equivalence.  It adds 124 explicit certificates, each of which the kernel replays with `decide`
in blocks of at most twelve moves and glues with `checkCert_append`, the block composition that
round 3 introduced because a single `decide` on a certificate of 141 moves exceeded
`maxRecDepth`.  Section (ii) adds the triviality corollaries, section (iii) the axiom audit.

The three families and where they come from:

* **The 98 resister certificates.**  `directions/resisters/std_certs.txt` (72 lines) carries a
  move list from a length-13 or length-14 resisting presentation to the standard tuple, and
  `directions/resisters/ak3_hits_certs.txt` (26 lines) carries a move list from such a
  presentation to AK(3).  Both were produced in round 3 by direction F4 and replayed there by
  two independent checkers; `<name>_sound` below is a third, kernel-level replay.  The AK(3)
  targets are completed to the tuple `AK3pres` of this section: 16 lines already end there and
  10 end at the swapped tuple, which the six moves `swapMoves` carry to `AK3pres`.  Those six
  moves are `mul 0 1`, `invert 0`, `mul 1 0`, `invert 1`, `mul 0 1`, `invert 0`; they carry any
  rank-2 tuple to the swapped tuple, which is `acEquiv_swap` of AC3.lean read as a move list, and
  `swapMoves_std` and `swapMoves_AK3` check two instances in the kernel here.

* **The 21 merge paths.**  `BBABaba,BAbABaa` is one of the 22 resisters that round 3 left
  undecided at cap 20.  `certs/spot22_paths.txt` (copied from
  `.ultramath/smw2opo0o/m7/work/spot22_paths.txt`, sha256
  36e74c35ed4c2c19623d04869377c73b39f09190f029928d693a94c909d73d32) records one path from it
  to each of the other 21, so those 22 presentations lie in a single Andrews-Curtis class.  The
  paths are written as indices into the twelve-move table of `directions/resisters/push.c`
  (0 invert r0, 1 to 4 conjugate r0 by a, A, b, B, 5 invert r1, 6 to 9 conjugate r1 by a, A, b,
  B, 10 multiply r0 by r1, 11 multiply r1 by r0); `merge_XX_sound` is the kernel check that each
  path really ends where the file says it does.

* **The five Carreras certificates.**  `directions/c14/carreras/` holds five certificates in
  Carreras's JSON format, whose moves are inversion, conjugation by one letter, multiplication
  by a relator or its inverse, and cyclic rotation of a relator.  Multiplication by an inverse
  and rotation are expanded here into the three moves of `Move`: multiplying `r i` by `r j`
  inverse is `invert j`, `mul i j`, `invert j`, and rotating `r i = u v` left by `|u|` is
  conjugation by `u` inverse.  Each file's move list ends at its recorded `reached` tuple, which
  the file declares to lie in the orbit of its `target` under relator inversion, rotation and
  swap.  Those are AC moves, and the explicit moves carrying `reached` to `target` are appended,
  so `carr_X_sound` ends at the target tuple itself and not only in its orbit.
-/

open AndrewsCurtis

/-- AK(3) = <x, y | x y x = y x y, x^3 = y^4>, as a rank-2 presentation: relator 0 is
`x y x y^-1 x^-1 y^-1` and relator 1 is `x x x y^-1 y^-1 y^-1 y^-1`.  The 26 AK(3)
certificates below end at this tuple. -/
def AK3pres : Presentation 2 :=
  mkPres (n := 2) [[(0,true),(1,true),(0,true),(1,false),(0,false),(1,false)],
     [(0,true),(0,true),(0,true),(1,false),(1,false),(1,false),(1,false)]]

/-- The standard balanced tuple `(a, b)` in the same form as the certificate tuples.  The 72
trivialisation certificates below end here. -/
def stdPair : Presentation 2 :=
  mkPres (n := 2) [[(0,true)], [(1,true)]]

/-- `stdPair` is the tuple `standard 2` of AC3.lean. -/
theorem std2_eq_standard : stdPair = standard 2 := by decide

/-- The six moves that swap the two relators of a rank-2 tuple. -/
def swapMoves : List (Move 2) :=
  [ Move.mul 0 1, Move.invert 0, Move.mul 1 0, Move.invert 1, Move.mul 0 1, Move.invert 0 ]

/-- The six-move swap checked in the kernel on the standard tuple. -/
theorem swapMoves_std : checkCert swapMoves stdPair (fun i => stdPair (1 - i)) = true := by
  decide

/-- The same six moves on the AK(3) tuple. -/
theorem swapMoves_AK3 : checkCert swapMoves AK3pres (fun i => AK3pres (1 - i)) = true := by
  decide

/-- The standard tuple presents the trivial group. -/
theorem stdPair_trivial : Subsingleton (PresentedGroup (Set.range stdPair)) := by
  rw [std2_eq_standard]
  exact subsingleton_presentedGroup_standard 2
'''

SECTION_II = r'''
/-! ## (ii) The presented group of every one of the 98 resisters is trivial, in the kernel

`<name>_sound` gives an Andrews-Curtis equivalence from the resister to `stdPair` (the 72 of
`std_certs.txt`) or to `AK3pres` (the 26 of `ak3_hits_certs.txt`).  Triviality of the presented
group is an AC-invariant (`presentedGroup_subsingleton_iff` of AC3.lean), `stdPair` presents the
trivial group (`stdPair_trivial`), and AK(3) presents the trivial group (`ak3_trivial` below).
Hence each of the 98 resisters presents the trivial group, and `<name>_trivial` is a kernel
proof of it.

This is the statement that the presented group is trivial.  It is not Andrews-Curtis
triviality: `<name>_sound` is an AC-equivalence to the standard tuple only for the 72, and the
26 AK(3) hits are AC-equivalent to AK(3), whose AC-triviality is the open question.

The AK(3) triviality is the round-1 theorem of `directions/ak-status/ak_trivial.lean` (there at
every rank, `AK.ak_trivial : ∀ n, Subsingleton (PresentedGroup (AK.akRels n))`).  Its text from
`namespace AK` to `end AK` is copied here verbatim, so that AC4.lean stays a single
self-contained file; `AK3range` identifies the relator set of AK(3) with the tuple `AK3pres`.
-/

open PresentedGroup

'''

AK3_GLUE = r'''
end AK

open AndrewsCurtis

/-- The relator set of `AK.akRels 3` is the relator set of the tuple `AK3pres`. -/
theorem AK3range : Set.range AK3pres = AK.akRels 3 := by
  ext x
  simp only [AK.akRels, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · right; decide
    · left; decide
  · rintro (h | h)
    · refine ⟨1, ?_⟩
      rw [h]; decide
    · refine ⟨0, ?_⟩
      rw [h]; decide

/-- AK(3) presents the trivial group. -/
theorem ak3_trivial : Subsingleton (PresentedGroup (Set.range AK3pres)) := by
  rw [AK3range]
  exact AK.ak_trivial 3
'''

FOOTER = r'''
/-! ## (iii) Axiom audit

One `#print axioms` per theorem of sections (i) and (ii), plus the theorems copied into them.
Every line must read `[propext, Classical.choice, Quot.sound]`, Lean's standard axioms, or
`does not depend on any axioms`; a line mentioning `sorryAx` or any other axiom would mean a
kernel check failed.  `check_all_certs.sh` greps for exactly that.
-/
'''


def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit('failed: %s\n%s\n%s' % (' '.join(cmd), r.stdout[-4000:], r.stderr[-4000:]))
    return r.stdout


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=os.path.join(HERE, 'AC4.lean'))
    ap.add_argument('--chunk', type=int, default=12)
    ap.add_argument('--json-out', default=os.path.join(HERE, 'json'))
    ap.add_argument('--no-triviality', action='store_true')
    a = ap.parse_args()

    # 1. independent Python replay of all 124 certificates
    print(run([sys.executable, os.path.join(HERE, 'certs_replay.py'), 'all', '--quiet',
               '--json-out', a.json_out]).strip())

    # 2. Lean text for each family
    groups = ['std', 'ak3', 'merge', 'carr']
    bodies, names = [], []
    for g in groups:
        jp = os.path.join(a.json_out, 'certs_%s.json' % g)
        bodies.append(run([sys.executable, os.path.join(HERE, 'certs_to_lean.py'),
                           '--json', jp, '--chunk', str(a.chunk)]))
        names += [c['name'] for c in json.load(open(jp))]

    # 3. assemble
    ac3 = open(os.path.join(REPO, 'toolkit/lean/AC3.lean')).read().rstrip('\n')
    ak_src = open(os.path.join(REPO, 'directions/ak-status/ak_trivial.lean')).read()
    ak_body = ak_src[ak_src.index('namespace AK'):ak_src.index('\nend AK\n')]
    parts = [ac3, HEADER]
    parts += bodies
    if not a.no_triviality:
        parts.append(SECTION_II)
        parts.append(ak_body)
        parts.append(AK3_GLUE)
        # only the resister families end at a tuple whose presented group is known trivial:
        # the merge paths end at other resisters, whose triviality these certificates do not give
        for n in [x for x in names if x.startswith('std_') or x.startswith('ak3_')]:
            base = 'stdPair_trivial' if n.startswith('std_') else 'ak3_trivial'
            parts.append('theorem %s_trivial :\n'
                         '    Subsingleton (PresentedGroup (Set.range %s_s)) :=\n'
                         '  (presentedGroup_subsingleton_iff %s_sound).mpr %s'
                         % (n, n, n, base))
    parts.append(FOOTER)
    audit = ['#print axioms %s_sound' % n for n in names]
    audit += ['#print axioms swapMoves_std', '#print axioms swapMoves_AK3',
              '#print axioms std2_eq_standard', '#print axioms stdPair_trivial']
    if not a.no_triviality:
        audit += ['#print axioms AK3range', '#print axioms ak3_trivial']
        audit += ['#print axioms AK.ak_trivial', '#print axioms AK.key',
                  '#print axioms AK.pow_eq', '#print axioms AK.rel_conj',
                  '#print axioms AK.rel_pow', '#print axioms AK.conj_rel']
        audit += ['#print axioms %s_trivial' % n for n in names
                  if n.startswith('std_') or n.startswith('ak3_')]
    parts.append('\n'.join(audit))
    text = '\n'.join(parts).rstrip('\n') + '\n'
    open(a.out, 'w').write(text)
    print('wrote %s: %d certificates (%d moves), %d lines, %d bytes'
          % (a.out, len(names), sum(len(c['moves']) for g in groups
                                    for c in json.load(open(os.path.join(
                                        a.json_out, 'certs_%s.json' % g)))),
             text.count('\n') + 1, len(text)))


if __name__ == '__main__':
    main()
