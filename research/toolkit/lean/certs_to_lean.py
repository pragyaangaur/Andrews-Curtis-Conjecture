#!/usr/bin/env python3
"""certs_to_lean.py -- emit Lean 4 code checking explicit AC certificates in the kernel.

Round 4, direction G6 (lean-program-4).  The output is meant to be appended to AC3.lean (whose
`Move`, `replay`, `checkCert`, `checkCert_append` and `checkCert_sound` it uses), giving
toolkit/lean/AC4.lean.

For every certificate the emitter writes

    def  <p>_s          the recorded start tuple          (a `Presentation 2`)
    def  <p>_i1 ...     the tuple after each block of moves
    def  <p>_t          the recorded end tuple
    def  <p>_c1 ...     the blocks, each a `List (Move 2)` of at most CHUNK moves
    def  <p>_m          the whole move list, as the syntactic concatenation of the blocks
    set_option maxRecDepth 100000 in theorem <p>_b1 ...
                        `checkCert <p>_c1 <p>_s <p>_i1 = true` by `decide`, one kernel
                        computation per block (this is the maxRecDepth lesson of round 3)
    theorem <p>_k<n>    the blocks glued by `checkCert_append`, ending at
                        `checkCert <p>_m <p>_s <p>_t = true`
    theorem <p>_sound   `ACEquiv <p>_s <p>_t`, from `checkCert_sound`

The input is the JSON written by replay4.py, which has already replayed every certificate in
independent Python; the emitter refuses to emit a certificate whose replay failed or whose
recorded end tuple differs from the replayed one.

Usage:  python3 certs_to_lean.py --json certs_std.json [--chunk 12] [--out FILE]
"""
import argparse
import json
import sys

LETTERS = {1: (0, True), -1: (0, False), 2: (1, True), -2: (1, False)}


def raw_word(w):
    return '[%s]' % ','.join('(%d,%s)' % LETTERS[x] for x in w)


def lean_pres(words):
    return 'mkPres (n := 2) [%s]' % ',\n     '.join(raw_word(w) for w in words)


def lean_word(w):
    return 'mkWord (n := 2) %s' % raw_word(w)


def lean_move(mv):
    kind = mv[0]
    if kind == 'invert':
        return 'Move.invert %d' % mv[1]
    if kind == 'conj':
        return 'Move.conj %d (%s)' % (mv[1], lean_word(mv[2]))
    return 'Move.mul %d %d' % (mv[1], mv[2])


def show_word(w):
    d = {1: 'a', -1: 'A', 2: 'b', -2: 'B'}
    return ''.join(d[x] for x in w) if w else 'e'


def emit(c, chunk, lines):
    name = c['name']
    start, end, moves = c['start'], c['end'], c['moves']
    # the intermediate tuples are the ones the independent Python replay produced
    path = c['path']
    states = [path[0]] + [path[k] for k in range(chunk, len(moves), chunk)] + [path[-1]]
    assert len(states) == (len(moves) + chunk - 1) // chunk + 1, name
    nblk = len(states) - 1
    lines.append('')
    lines.append('/-- `%s`: `%s` to `%s`, %d moves in %d block(s) of at most %d. -/'
                 % (c['source'], ','.join(show_word(w) for w in start),
                    ','.join(show_word(w) for w in end), len(moves), nblk, chunk))
    lines.append('def %s_s : Presentation 2 :=\n  %s' % (name, lean_pres(start)))
    for i in range(1, nblk):
        lines.append('def %s_i%d : Presentation 2 :=\n  %s' % (name, i, lean_pres(states[i])))
    lines.append('def %s_t : Presentation 2 :=\n  %s' % (name, lean_pres(end)))
    for i in range(nblk):
        block = moves[i * chunk:(i + 1) * chunk]
        lines.append('def %s_c%d : List (Move 2) :=\n  [ %s ]'
                     % (name, i + 1, ',\n    '.join(lean_move(m) for m in block)))
    def sname(i):
        if i == 0:
            return '%s_s' % name
        return '%s_t' % name if i == nblk else '%s_i%d' % (name, i)
    for i in range(1, nblk + 1):
        lines.append('set_option maxRecDepth 100000 in\ntheorem %s_b%d :\n'
                     '    checkCert %s_c%d %s = true := by decide'
                     % (name, i, name, i,
                        ' '.join([sname(i - 1), sname(i)])))
    lines.append('theorem %s_k1 :\n    checkCert %s_c1 %s = true := %s_b1'
                 % (name, name, ' '.join([sname(0), sname(1)]), name))
    for i in range(2, nblk + 1):
        expr = ' '.join('++ %s_c%d' % (name, k) for k in range(2, i + 1))
        prev = '%s_k%d' % (name, i - 1)
        lines.append('theorem %s_k%d :\n    checkCert (%s_c1 %s) %s = true :=\n'
                     '  checkCert_append (ms\u2081 := %s_c1 %s) (ms\u2082 := %s_c%d)\n'
                     '    (start := %s) (mid := %s) (finish := %s) %s %s_b%d'
                     % (name, i, name, expr, ' '.join([sname(0), sname(i)]),
                        name, ' '.join('++ %s_c%d' % (name, k) for k in range(2, i)),
                        name, i,
                        sname(0), sname(i - 1), sname(i), prev, name, i))
    exprs = ' '.join('++ %s_c%d' % (name, k) for k in range(2, nblk + 1))
    lines.append('def %s_m : List (Move 2) :=\n  %s_c1 %s' % (name, name, exprs))
    lines.append('theorem %s_check : checkCert %s_m %s_s %s_t = true := %s_k%d'
                 % (name, name, name, name, name, nblk))
    lines.append('theorem %s_sound : ACEquiv %s_s %s_t :=\n  checkCert_sound %s_check'
                 % (name, name, name, name))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--json', required=True)
    ap.add_argument('--chunk', type=int, default=12)
    ap.add_argument('--out')
    ap.add_argument('--only', default=None, help='comma-separated certificate names')
    a = ap.parse_args()
    certs = json.load(open(a.json))
    if a.only:
        want = set(a.only.split(','))
        certs = [c for c in certs if c['name'] in want]
    bad = [c['name'] for c in certs if not c.get('ok')]
    if bad:
        sys.exit('refusing to emit, replay failed for: %s' % ' '.join(bad))
    lines = ['', 'open AndrewsCurtis']
    for c in certs:
        emit(c, a.chunk, lines)
    text = '\n'.join(lines) + '\n'
    if a.out:
        open(a.out, 'w').write(text)
        sys.stderr.write('wrote %s: %d certificates, %d moves\n'
                         % (a.out, len(certs), sum(len(c['moves']) for c in certs)))
    else:
        sys.stdout.write(text)


if __name__ == '__main__':
    main()
