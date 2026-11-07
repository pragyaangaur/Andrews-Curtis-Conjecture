#!/usr/bin/env python3
"""Independent replay verifier for the two Andrews-Curtis move sequences published in

  A. Lisitsa, "Stable Andrews-Curtis trivialization of AK(3) revisited. A case study
  using automated deduction", arXiv:2501.18601, Section 3 (sequences S2 and S3).

Nothing here is taken from the author's code or data: the move semantics are the three
standard AC moves, and the sequence text below is a verbatim copy of the LaTeX
verbatim blocks of the paper (S2 = 160 printed moves, S3 = its first 67 moves plus
three printed moves).  Words are written over a, b and their inverses A = a^-1,
B = b^-1, in reduced form.

Run:  python3 automated_check.py
Exit status 0 means every step checked.
"""
import re, sys

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}

def red(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return tuple(out)

def mul(u, v):
    return red(tuple(u) + tuple(v))

def inv(w):
    return tuple(INV[c] for c in reversed(w))

def conj(w, x):
    return mul(mul(w, x), inv(w))

def st(w):
    return ''.join(w)

S2_TEXT = """\
  1. ABaBAbaBBabAb,BAbbABabaBBa  -> INV 
  2. BaBAbbABabAba,BAbbABabaBBa  -> CONJ AbXBa
  3. BAbbABabAbaBa,BAbbABabaBBa  -> INV 
  4. AbABaBAbaBBab,BAbbABabaBBa  -> MULT-L
  5. AbABaaBBa,BAbbABabaBBa      -> INV 
  6. AbbAAbaBa,BAbbABabaBBa      -> CONJ BaXAb
  7. bAAba,BAbbABabaBBa          -> MULT-L 
  8. bAAbaBAbbABabaBBa,BAbbABabaBBa -> INV 
  9. AbbABAbaBBabABaaB,BAbbABabaBBa  -> MULT-R
 10. AbbABAbaBBabABaaB,ABaaB     -> INV 
 11. bAAbaBAbbABabaBBa,ABaaB     -> CONJ ABaaBXbAAba 
 12 .BAbbABabaBBabAAba,ABaaB     -> MULT-L 
 13. BAbbABabaBBa,ABaaB          -> CONJ BBabXBAbb
 14. ABabaBBaBAbb,ABaaB          -> INV 
 15. BBabAbbABAba,ABaaB          -> MULT-L 
 16. BBabAbbABaB,ABaaB           -> INV 
 17. bAbaBBaBAbb,ABaaB           -> CONJ ABaBxbAba
 18. BBaBAbbbAba,ABaaB           -> MULT-L 
 19. BBaBAbbbaB,ABaaB            -> CONJ bAbbXBBaB 
 20. AbbbaBBBaB,ABaaB            -> INV 
 21. bAbbbABBBa,ABaaB            -> MULT-L 
 22. bAbbbABBBBaaB,ABaaB         -> INV 
 23. bAAbbbbaBBBaB,ABaaB         -> CONJ aBXbA
 24. AbbbbaBBB,ABaaB             -> INV 
 25. bbbABBBBa,ABaaB             -> MULT-L 
 26. bbbABBBBBaaB,ABaaB          -> INV 
 27. bAAbbbbbaBBB,ABaaB          -> MULT-R
 28. bAAbbbbbaBBB,AbbbbaBBB      -> CONJ aBXbA
 29. AbbbbbaBBA,AbbbbaBBB        -> INV 
 30. abbABBBBBa,AbbbbaBBB        -> MULT-L 
 31. abbABaBBB,AbbbbaBBB         -> INV  
 32. bbbAbaBBA,AbbbbaBBB         -> CONJ AXa
 33. AbbbAbaBB,AbbbbaBBB         -> INV 
 34. bbABaBBBa,AbbbbaBBB         -> MULT-L 
 35. bbABabaBBB,AbbbbaBBB        -> CONJ baBBBXbbbAB
 36. baBABa,AbbbbaBBB            -> MULT-L 
 37. baBAbbbaBBB,AbbbbaBBB       -> INV 
 38. bbbABBBabAB,AbbbbaBBB       -> MULT-R 
 39. bbbABBBabAB,AbabAB          -> INV 
 40. baBAbbbaBBB,AbabAB          -> CONJ bABXbaB
 41. AbbbaBBaB,AbabAB            -> INV 
 42. bAbbABBBa,AbabAB            -> MULT-L 
 43. bAbbABBabAB,AbabAB          -> INV 
 44. baBAbbaBBaB,AbabAB          -> CONJ bABXbaB
 45. AbbaBBaaB,AbabAB            -> INV 
 46. bAAbbABBa,AbabAB            -> MULT-L 
 47. bAAbbABabAB,AbabAB          -> INV 
 48. baBAbaBBaaB,AbabAB          -> CONJ bABXbaB
 49. AbaBBaaaB,AbabAB            -> INV 
 50. bAAAbbABa,AbabAB            -> MULT-L 
 51. bAAAbbbAB,AbabAB            -> INV 
 52. baBBBaaaB,AbabAB            -> CONJ aaBXbAA
 53. aaaBBBa,AbabAB              -> MULT-L 
 54. aaaBBabAB,AbabAB            -> CONJ bABXbaB
 55. bABaaaBBa,AbabAB            -> MULT-L 
 56. bABaaaBabAB,AbabAB          -> CONJ bABXbaB
 57. bAABaaaBa,AbabAB            -> MULT-L 
 58. bAABaaaabAB,AbabAB          -> CONJ AbaaBXbAABa
 59. aaabAAABa,AbabAB            -> MULT-L 
 60. aaabAAbAB,AbabAB            -> CONJ AXa
 61. aabAAbABa,AbabAB            -> MULT-L 
 62. aabAAbbAB,AbabAB            -> CONJ AXa
 63. abAAbbABa,AbabAB            -> MULT-L 
 64. abAAbbbAB,AbabAB            -> CONJ AXa
 65. bAAbbbABa,AbabAB            -> MULT-L 
 66. bAAbbbbAB,AbabAB            -> CONJ aBXbA
 67. AbbbbAA,AbabAB              -> INV 
 68. aaBBBBa,AbabAB              -> MULT-L       
 69. aaBBBabAB,AbabAB            -> INV 
 70. baBAbbbAA,AbabAB            -> MULT-R 
 71. baBAbbbAA,AbbbbAA           -> CONJ bABXbaB
 72. AbbbAAbaB,AbbbbAA           -> INV 
 73. bABaaBBBa,AbbbbAA           -> MULT-L 
 74. bABaabAA,AbbbbAA            -> CONJ abAAXaaBA
 75. abAAbABa,AbbbbAA            -> MULT-L 
 76. abAAbAbbbAA,AbbbbAA         -> CONJ BaaBAXabAAb
 77. AbbbAbAAb,AbbbbAA           -> INV 
 78. BaaBaBBBa,AbbbbAA           -> MULT-L 
 79. BaaBabAA,AbbbbAA            -> CONJ AbXBa
 80. aBabAABa,AbbbbAA            -> MULT-L 
 81. aBabAAbbbAA,AbbbbAA         -> CONJ ABAbAXaBabA
 82. AbbbABabA,AbbbbAA           -> INV 
 83. aBAbaBBBa,AbbbbAA           -> MULT-L 
 84. aBAbabAA,AbbbbAA            -> CONJ abAAXaaBA
 85. abABAb,AbbbbAA              -> MULT-L 
 86. abABAbAbbbbAA,AbbbbAA       -> INV 
 87. aaBBBBaBabaBA,AbbbbAA       -> MULT-R 
 88. aaBBBBaBabaBA,BabaBA        -> INV 
 89. abABAbAbbbbAA,BabaBA        -> CONJ BabaBAXabABAb
 90. AbbbbAbABAb,BabaBA          -> MULT-L 
 91. AbbbbAA,BabaBA              -> CONJ BaXAb        
 92. bbbAAAb,BabaBA              -> MULT-L 
 93. bbbAAbaBA,BabaBA            -> CONJ aBAXabA
 94. aBAbbbAAb,BabaBA            -> MULT-L 
 95. aBAbbbAbaBA,BabaBA          -> CONJ aBAXabA
 96. aBBAbbbAb,BabaBA            -> MULT-L 
 97. aBBAbbbbaBA,BabaBA          -> CONJ BabbAXaBBAb  
 98. bbbaBBBAb,BabaBA            -> MULT-L 
 99. bbbaBBaBA,BabaBA            -> CONJ BXb
100. bbaBBaBAb,BabaBA            -> MULT-L 
101. bbaBBaaBA,BabaBA            -> CONJ BXb
102. baBBaaBAb,BabaBA            -> MULT-L 
103. baBBaaaBA,BabaBA            -> CONJ BXb
104. aBBaaaBAb,BabaBA            -> MULT-L 
105. aBBaaaaBA,BabaBA            -> CONJ bAXaB
106. BaaaaBB,BabaBA              -> INV 
107. bbAAAAb,BabaBA              -> MULT-L 
108. bbAAAbaBA,BabaBA            -> INV 
109. abABaaaBB,BabaBA            -> MULT-R 
110. abABaaaBB,BaaaaBB           -> CONJ aBAXabA
111. BaaaBBabA,BaaaaBB           -> INV 
112. aBAbbAAAb,BaaaaBB           -> MULT-L 
113. aBAbbaBB,BaaaaBB            -> CONJ baBBXbbAB
114. baBBaBAb,BaaaaBB            -> MULT-L 
115. baBBaBaaaBB,BaaaaBB         -> CONJ AbbABXbaBBa
116. BaaaBaBBa,BaaaaBB           -> INV 
117. AbbAbAAAb,BaaaaBB           -> MULT-L 
118. AbbAbaBB,BaaaaBB            -> CONJ BaXAb
119. bAbaBBAb,BaaaaBB            -> MULT-L 
120. bAbaBBaaaBB,BaaaaBB         -> CONJ bABaBXbAbaB
121. BaaaBAbaB,BaaaaBB           -> INV 
122. bABabAAAb,BaaaaBB           -> MULT-L 
123. bABabaBB,BaaaaBB            -> CONJ baBXbAB
124. abaBAB,BaaaaBB              -> INV 
125. babABA,BaaaaBB              -> MULT-L 
126. babABABaaaaBB,BaaaaBB       -> INV 
127. bbAAAAbabaBAB,BaaaaBB       -> MULT-R
128. bbAAAAbabaBAB,abaBAB        -> INV 
129. babABABaaaaBB,abaBAB        -> CONJ abaBABXbabABA
130. BaaaaBabABA,abaBAB          -> MULT-L 
131. BaaaaBB,abaBAB              -> CONJ bXB
132. aaaaBBB,abaBAB              -> INV 
133. bbbAAAA,abaBAB              -> MULT-L 
134. bbbAAAbaBAB,abaBAB          -> INV 
135. babABaaaBBB,abaBAB          -> CONJ BXb
136. abABaaaBB,abaBAB            -> INV 
137. bbAAAbaBA,abaBAB            -> MULT-L 
138. bbAAAbaaBAB,abaBAB          -> INV 
139. babAABaaaBB,abaBAB          -> CONJ BXb
140. abAABaaaB,abaBAB            -> INV 
141. bAAAbaaBA,abaBAB            -> MULT-L 
142. bAAAbaaaBAB,abaBAB          -> INV 
143. babAAABaaaB,abaBAB          -> CONJ BXb
144. abAAABaaa,abaBAB            -> INV 
145. AAAbaaaBA,abaBAB            -> MULT-L 
146. AAAbaaaaBAB,abaBAB          -> INV 
147. babAAAABaaa,abaBAB          -> CONJ aXA
148. ababAAAABaa,abaBAB          -> INV 
149. AAbaaaaBABA,abaBAB          -> MULT-L 
150. AAbaaaaBBAB,abaBAB          -> INV 
151. babbAAAABaa,abaBAB          -> CONJ aXA
152. ababbAAAABa,abaBAB          -> INV 
153. AbaaaaBBABA,abaBAB          -> MULT-L 
154. AbaaaaBBBAB,abaBAB          -> INV 
155. babbbAAAABa,abaBAB          -> CONJ aXA
156. ababbbAAAAB,abaBAB          -> INV 
157. baaaaBBBABA,abaBAB          -> MULT-L 
158. baaaaBBBBAB,abaBAB          -> INV 
159. babbbbAAAAB,abaBAB          -> CONJ ABXba
160. bbbbAAA,abaBAB              -> INV 
     aaaBBBB,abaBAB
"""

S3_TEXT = """\
68. aaBBBBa,AbabAB              -> CONJ aXA
69. aaaBBBB,AbabAB              -> CONJ-R aXA
70  aaaBBBB,babABA              -> INV-R
    aaaBBBB,abaBAB
"""

def parse(text):
    moves, final = [], None
    for line in text.strip().splitlines():
        line = line.strip()
        m = re.match(r'^(\d+)\s*\.?\s*([A-Za-z]+),([A-Za-z]+)\s*->\s*(.+)$', line)
        if m:
            moves.append((int(m.group(1)), m.group(2), m.group(3), re.sub(r'\s+', ' ', m.group(4)).strip()))
            continue
        m = re.match(r'^([A-Za-z]+),([A-Za-z]+)$', line)
        if m:
            final = (m.group(1), m.group(2))
    return moves, final

def conjugator(label):
    """label is 'CONJ wXw^-1' with X or x as the separator; return w."""
    tok = label.split()[1]
    return re.split('[Xx]', tok)[0]

def check(moves, final, name, corrections):
    states = [(red(m[1]), red(m[2])) for m in moves] + [(red(final[0]), red(final[1]))]
    bad = []
    kinds = {}
    for k, (n, r1, r2, label) in enumerate(moves):
        x, y = states[k]
        x2, y2 = states[k + 1]
        kind = label.split()[0]
        kinds[kind] = kinds.get(kind, 0) + 1
        ok = False
        if kind in ('INV', 'INV-L', 'INV-R'):
            ok = (x2, y2) == (inv(x), y) or (x2, y2) == (x, inv(y))
            if kind == 'INV-R':
                ok = (x2, y2) == (x, inv(y))
            if kind == 'INV-L':
                ok = (x2, y2) == (inv(x), y)
        elif kind in ('MULT-L', 'MULT-R'):
            ok = (y2 == y and x2 == mul(x, y)) or (x2 == x and y2 == mul(y, x))
            if not ok:  # multiplication by an inverse relator, three standard moves
                ok = (y2 == y and x2 == mul(x, inv(y))) or (x2 == x and y2 == mul(y, inv(x)))
        elif kind in ('CONJ', 'CONJ-R'):
            w = red(corrections.get(n, conjugator(label)) if kind == 'CONJ' else conjugator(label))
            ok = (y2 == y and x2 == conj(w, x)) or (x2 == x and y2 == conj(w, y))
        if not ok:
            bad.append((n, label))
    return states, kinds, bad

def main():
    moves, final = parse(S2_TEXT)
    print('S2: parsed %d printed moves, final state %s,%s' % (len(moves), final[0], final[1]))
    print('S2: printed move numbers are 1..%d: %s' % (len(moves), [m[0] for m in moves] == list(range(1, len(moves) + 1))))
    print('S2: all printed states are reduced words: %s' % all(
        st(w) == ''.join(red(w)) for m in moves for w in (m[1], m[2])))
    P = (red('ABaBAbaBBabAb'), red('BAbbABabaBBa'))
    AK3 = (red('aaaBBBB'), red('abaBAB'))
    # as printed
    states, kinds, bad = check(moves, final, 'S2', {})
    print('S2: move kinds:', kinds)
    plus = minus = 0
    for k, (n, r1, r2, label) in enumerate(moves):
        x, y = states[k]
        x2, y2 = states[k + 1]
        if label.startswith('MULT'):
            if (x2 == mul(x, y) and y2 == y) or (y2 == mul(y, x) and x2 == x):
                plus += 1
            elif (x2 == mul(x, inv(y)) and y2 == y) or (y2 == mul(y, inv(x)) and x2 == x):
                minus += 1
    print('S2: multiplications directly by the other relator: %d, by its inverse (three standard moves): %d' % (plus, minus))
    print('S2: first state equals the relator pair of the paper\'s P: %s' % (states[0] == P))
    print('S2: last state equals the AK(3) relator pair (a^3 b^-4, a b a b^-1 a^-1 b^-1): %s' % (states[-1] == AK3))
    print('S2: steps that fail exactly as printed: %d %s' % (len(bad), bad))
    # with the single documented correction
    corr = {81: 'aBAbA'}
    states, kinds, bad2 = check(moves, final, 'S2', corr)
    print('S2: with step 81 conjugator read as aBAbA instead of the printed ABAbA: failing steps = %d' % len(bad2))
    print('S2: corrected chain runs P -> AK(3) in %d standard AC moves: %s' % (
        len(moves), len(bad2) == 0 and states[0] == P and states[-1] == AK3))
    # S3
    mv3, fin3 = parse(S3_TEXT)
    pre = moves[:67]
    s3 = pre + [(68, mv3[0][1], mv3[0][2], mv3[0][3]),
                (69, mv3[1][1], mv3[1][2], mv3[1][3]),
                (70, mv3[2][1], mv3[2][2], mv3[2][3])]
    states3, kinds3, bad3 = check(s3, fin3, 'S3', {})
    print('S3: 67-move S2 prefix plus 3 printed moves = %d moves, kinds %s' % (len(s3), kinds3))
    print('S3: first state equals P: %s, last state equals AK(3): %s' % (states3[0] == P, states3[-1] == AK3))
    print('S3: failing steps: %d %s' % (len(bad3), bad3))
    ok = (len(bad2) == 0 and len(bad3) == 0 and states[0] == P and states[-1] == AK3
          and states3[0] == P and states3[-1] == AK3)
    print('RESULT: %s' % ('PASS: both published sequences replay from P to AK(3)' if ok else 'FAIL'))
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())

