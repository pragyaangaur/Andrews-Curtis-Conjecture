#!/usr/bin/env python3
"""cert_to_lean.py -- turn an explicit AC certificate into Lean code for toolkit/lean/AC3.lean.

Two input formats are supported.

  ms   the JSON format of directions/ms-ak-certs/cert_nN.json
       keys: rank (and n), start (list of words), end (list of words),
       moves (list of ["conj", i, word], ["inv", i], ["mul", i, j]), relator indices one-based.
       letters: x / X for the first generator, y / Y for the second, case = sign.

  c14  one line of the text format of directions/c14/certs_all.txt, namely  START|MOVES|END
       START and END are two words separated by a comma, letters a A b B ('e' = empty word),
       END may be the token 'std' for the standard pair (a, b);
       MOVES is a space separated list of  iN  (invert relator N),
       cNL  (conjugate relator N by the letter L) and  mN  (multiply relator N by the other
       relator).  Relator indices in this format are zero-based.

The emitted Lean code checks the certificate in the kernel with `decide`, in blocks of at most
`--chunk` moves (default 10), and glues the blocks with `checkCert_append`.  Chunking matters:
the kernel computation for a single long chain can exceed the elaborator's default recursion and
heartbeat limits, while each block stays small and the glue is symbolic.  The output contains

    def  <p>_start, <p>_c1 ... <p>_ck, <p>_s1 ... <p>_s(k-1), <p>_finish, <p>_moves
    theorem <p>_chk1 ... <p>_chkk    -- one kernel `decide` per block
    theorem <p>_acc1 ... <p>_acck    -- the glued certificates
    theorem <p>_check                -- the whole certificate, a kernel computation in blocks
    theorem <p>_sound : ACEquiv <p>_start <p>_finish

Usage:
    python3 toolkit/lean/cert_to_lean.py --ms FILE.json [--name PREFIX] [--chunk N]
    python3 toolkit/lean/cert_to_lean.py --c14 'START|MOVES|END' [--name PREFIX] [--chunk N]
    python3 toolkit/lean/cert_to_lean.py --c14-file FILE.txt --line N [--name PREFIX]

`check_cert_lean.sh` runs the whole pipeline: it writes .scratch/CertCheck.lean, which is
AC3.lean followed by this snippet, and calls lean on it.
"""

import argparse
import json
import sys

MS_LETTERS = {'x': (0, True), 'X': (0, False), 'y': (1, True), 'Y': (1, False)}
C14_LETTERS = {'a': (0, True), 'A': (0, False), 'b': (1, True), 'B': (1, False)}


# ---------------------------------------------------------------- word arithmetic (for states)
def neg(letter):
    return (letter[0], not letter[1])


def invrev(w):
    return [neg(x) for x in reversed(w)]


def reduce_word(w):
    out = []
    for x in w:
        if out and out[-1] == neg(x):
            out.pop()
        else:
            out.append(x)
    return out


def wmul(u, v):
    return reduce_word(list(u) + list(v))


def wconj(c, u):
    return wmul(wmul(c, u), invrev(c))


# ---------------------------------------------------------------- Lean rendering
def raw_word(letters):
    return '[%s]' % ','.join('(%d,%s)' % (g, 'true' if s else 'false') for g, s in letters)


def lean_word(letters):
    return 'mkWord (n := 2) %s' % raw_word(letters)


def lean_pres(words):
    return 'mkPres (n := 2) [%s]' % ',\n     '.join(raw_word(w) for w in words)


def parse_letters(word, table, allow_empty=False):
    if allow_empty and word in ('e', ''):
        return []
    out = []
    for c in word:
        if c not in table:
            raise ValueError('unknown letter %r in %r' % (c, word))
        out.append(table[c])
    return out


def apply_move(state, move):
    kind = move[0]
    if kind == 'invert':
        i = move[1]
        out = list(state)
        out[i] = invrev(out[i])
        return out
    if kind == 'conj':
        i, c = move[1], move[2]
        out = list(state)
        out[i] = wconj(c, out[i])
        return out
    if kind == 'mul':
        i, j = move[1], move[2]
        if i == j:
            raise ValueError('degenerate multiplication move')
        out = list(state)
        out[i] = wmul(out[i], out[j])
        return out
    raise ValueError('unknown move %r' % (move,))


def lean_move(move):
    kind = move[0]
    if kind == 'invert':
        return 'Move.invert %d' % move[1]
    if kind == 'conj':
        return 'Move.conj %d (%s)' % (move[1], lean_word(move[2]))
    return 'Move.mul %d %d' % (move[1], move[2])


def emit(name, start_words, moves, end_words, source, chunk):
    # simulate in python to get the chunk boundary states
    state = [list(w) for w in start_words]
    states = [ [list(w) for w in state] ]
    chunks = []
    for k in range(0, len(moves), chunk):
        block = moves[k:k + chunk]
        for m in block:
            state = apply_move(state, m)
        chunks.append(block)
        states.append([list(w) for w in state])
    if state != [list(w) for w in end_words]:
        sys.stderr.write('WARNING: the python replay does not reach the recorded finish tuple;\n'
                         'the Lean chunk checks will therefore fail unless the certificate is wrong\n'
                         'in a way that only the Lean semantics sees.\n')
    def sname(i):
        return '%s_finish' % name if i == len(chunks) else '%s_s%d' % (name, i)
    L = []
    L.append('')
    L.append('/-- Certificate from %s, checked in %d block(s) of at most %d moves. -/'
             % (source, len(chunks), chunk))
    L.append('def %s_start : Presentation 2 :=\n  %s' % (name, lean_pres(start_words)))
    for i, block in enumerate(chunks, start=1):
        L.append('def %s_c%d : List (Move 2) :=\n  [ %s ]'
                 % (name, i, ',\n    '.join(lean_move(m) for m in block)))
    for i in range(1, len(chunks)):
        L.append('def %s_s%d : Presentation 2 :=\n  %s' % (name, i, lean_pres(states[i])))
    L.append('def %s_finish : Presentation 2 :=\n  %s' % (name, lean_pres(end_words)))
    for i in range(1, len(chunks) + 1):
        L.append('set_option maxRecDepth 100000 in\ntheorem %s_chk%d :\n'
                 '    checkCert %s_c%d %s_s%d %s = true := by decide'
                 % (name, i, name, i, name, i - 1, sname(i)))
    L.append('theorem %s_acc1 :\n    checkCert %s_c1 %s_s0 %s = true := %s_chk1'
             % (name, name, name, sname(1), name))
    for i in range(2, len(chunks) + 1):
        prev = '%s_acc%d' % (name, i - 1)
        expr = ' '.join('++ %s_c%d' % (name, k) for k in range(2, i + 1))
        prev_expr = ' '.join('++ %s_c%d' % (name, k) for k in range(2, i))
        L.append('theorem %s_acc%d :\n    checkCert (%s_c1 %s) %s_s0 %s = true :=\n'
                 '  checkCert_append (n := 2) (ms\u2081 := %s_c1 %s) (ms\u2082 := %s_c%d)\n'
                 '    (start := %s_s0) (mid := %s_s%d) (finish := %s) %s %s_chk%d'
                 % (name, i, name, expr, name, sname(i),
                    name, prev_expr, name, i,
                    name, name, i - 1, sname(i), prev, name, i))
    exprs = ' '.join('++ %s_c%d' % (name, k) for k in range(2, len(chunks) + 1))
    L.append('def %s_moves : List (Move 2) :=\n  %s_c1 %s' % (name, name, exprs))
    L.append('theorem %s_check :\n    checkCert %s_moves %s_start %s_finish = true := %s_acc%d'
             % (name, name, name, name, name, len(chunks)))
    L.append('theorem %s_sound : ACEquiv %s_start %s_finish :=\n  checkCert_sound %s_check'
             % (name, name, name, name))
    # s0 is the recorded start tuple
    L = [x.replace('%s_s0' % name, '%s_start' % name) for x in L]
    return '\n\n'.join(L) + '\n'


def from_ms(path, name, chunk):
    d = json.load(open(path))
    if d.get('rank', 2) != 2:
        raise ValueError('only rank 2 is supported')
    start = [parse_letters(w, MS_LETTERS) for w in d['start']]
    end = [parse_letters(w, MS_LETTERS) for w in d['end']]
    moves = []
    for m in d['moves']:
        if m[0] == 'conj':
            moves.append(('conj', m[1] - 1, parse_letters(m[2], MS_LETTERS)))
        elif m[0] in ('inv', 'invert'):
            moves.append(('invert', m[1] - 1))
        elif m[0] == 'mul':
            moves.append(('mul', m[1] - 1, m[2] - 1))
        else:
            raise ValueError('unknown move %r' % (m,))
    return emit(name, start, moves, end, '`%s`' % path, chunk)


def from_c14(line, name, source, chunk):
    parts = line.rstrip('\n').split('|')
    if len(parts) != 3:
        raise ValueError('not a c14 certificate line')
    start = [parse_letters(w, C14_LETTERS, allow_empty=True) for w in parts[0].split(',')]
    end = parts[2]
    if end == 'std':
        end_words = [[(0, True)], [(1, True)]]
    else:
        end_words = [parse_letters(w, C14_LETTERS, allow_empty=True) for w in end.split(',')]
    moves = []
    for tok in parts[1].split():
        if tok[0] == 'i':
            moves.append(('invert', int(tok[1:])))
        elif tok[0] == 'c':
            letter = tok[-1]
            moves.append(('conj', int(tok[1:-1]), parse_letters(letter, C14_LETTERS)))
        elif tok[0] == 'm':
            i = int(tok[1:])
            moves.append(('mul', i, 1 - i))
        else:
            raise ValueError('unknown move token %r' % tok)
    return emit(name, start, moves, end_words, source, chunk)


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument('--ms')
    ap.add_argument('--c14')
    ap.add_argument('--c14-file')
    ap.add_argument('--line', type=int)
    ap.add_argument('--name', default='cert')
    ap.add_argument('--chunk', type=int, default=10)
    a = ap.parse_args(argv)
    if a.ms:
        sys.stdout.write(from_ms(a.ms, a.name, a.chunk))
    elif a.c14:
        sys.stdout.write(from_c14(a.c14, a.name, 'a `directions/c14` certificate line', a.chunk))
    elif a.c14_file:
        rows = [l for l in open(a.c14_file).read().splitlines() if l.strip()]
        line = rows[a.line]
        sys.stdout.write(from_c14(line, a.name, '`%s` line %d' % (a.c14_file, a.line), a.chunk))
    else:
        ap.error('give --ms, --c14 or --c14-file with --line')


if __name__ == '__main__':
    main(sys.argv[1:])
