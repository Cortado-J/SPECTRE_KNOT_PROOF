#!/usr/bin/env python3
"""Side lengths by edge label (paper, Section 6): the letter recurrence, the parities, the Sigma offset, closed forms.

Every side of a level-m supertile (m >= 1) carries one of the edge labels of the spectre paper's Fig. 4.2
(alpha, beta, gamma, delta, epsilon, zeta, eta, theta; signs ignored). This script checks, from the composition
pattern C (combin_8.json) and the measured side lengths (levels 1..8):
  1. partner sides in C carry the same letter (x+ with x-, eta with eta);
  2. each parent side's letter determines the multiset of child letters it is made of (the letter recurrence);
  3. side lengths depend only on the letter at every measured level, and follow the recurrence;
  4. the letter parities are a fixed point of the recurrence mod 2;
  5. the Sigma offset d_{m+1} = theta_m + epsilon_m + alpha_m and l_{m+1}(Sigma,5) - d_{m+1} = beta_m + theta_m;
  6. closed forms in lambda = 2 + sqrt 5 (exact, sympy), and the dimension of span{M^i l_1}.
Writes letters.json (used by the paper's tables).
usage: python3 letters.py
"""
import json, os, sys
from fractions import Fraction as Fr
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
C = json.load(open(os.path.join(HERE, 'combin_8.json')))
E42 = json.load(open(os.path.join(HERE, '..', 'crosscheck', 'fig51_encoding.json')))['fig42']
N = ['Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Phi', 'Psi']
LET = {'a': 'alpha', 'b': 'beta', 'g': 'gamma', 'd': 'delta', 'e': 'epsilon', 'z': 'zeta', 'h': 'eta', 't': 'theta'}
ORDER = ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta']
# code side j of kind s carries the Fig. 4.2 label of edge (3 + j) mod 6 (edges listed E, NE, NW, W, SW, SE);
# checked for all 71 placements in Fig. 5.1 by crosscheck/fig51_compare.py
lab = {s: [E42[s][(3 + j) % 6] for j in range(6)] for s in N}
letter = {s: [LET[lab[s][j][0]] for j in range(6)] for s in N}
ST = C['ST']['1']
problems = []

# 1. partners
for T in N:
    st = ST[T]
    for c, ss in enumerate(st['sides']):
        for j, o in enumerate(ss):
            if o == 'R': continue
            c2, j2 = map(int, o.split('.'))
            a, b = lab[st['kids'][c]][j], lab[st['kids'][c2]][j2]
            okp = (a == 'h' and b == 'h') or (a != 'h' and a[0] == b[0] and {a[1], b[1]} == {'+', '-'})
            if not okp: problems.append(f'{T}: partner sides {c}.{j} ({a}) and {c2}.{j2} ({b}) do not match')
print('1. partner sides carry matching labels (x+ with x-, eta with eta):', 'yes' if not problems else 'NO')

# 2. letter recurrence
rec = {}
for T in N:
    st = ST[T]
    for J, seq in enumerate(st['pside']):
        cnt = {}
        for t in seq:
            c, j = map(int, t.split('.'))
            x = letter[st['kids'][c]][j]; cnt[x] = cnt.get(x, 0) + 1
        key = letter[T][J]
        if key in rec and rec[key] != cnt: problems.append(f'letter {key}: two different decompositions {rec[key]} vs {cnt}')
        rec.setdefault(key, cnt)
print('2. letter recurrence (parent letter = sum of child letters), the same in every kind:')
for x in ORDER:
    print(f'     {x:8s} -> ' + ' + '.join((f'{k}*' if k > 1 else '') + y for y, k in sorted(rec[x].items(), key=lambda kv: ORDER.index(kv[0]))))
A = [[rec[x].get(y, 0) for y in ORDER] for x in ORDER]

# 3. lengths by letter
levels = sorted(int(m) for m in C['LEN'])
Lval = {}
for m in levels:
    by = {}
    for s in N:
        for j in range(6): by.setdefault(letter[s][j], set()).add(C['LEN'][str(m)][s][j])
    bad = {x: v for x, v in by.items() if len(v) != 1}
    if bad: problems.append(f'level {m}: lengths not determined by letter: {bad}')
    Lval[m] = [min(by[x]) for x in ORDER]
for m in levels[:-1]:
    nxt = [sum(A[i][k] * Lval[m][k] for k in range(8)) for i in range(8)]
    if nxt != Lval[m + 1]: problems.append(f'letter recurrence fails from level {m}')
print('3. lengths depend only on the letter, levels', levels[0], '..', levels[-1], ', and follow the recurrence:', 'yes' if not problems else 'NO')
for m in levels: print(f'     level {m}: ' + ', '.join(f'{x}={v}' for x, v in zip(ORDER, Lval[m])))

# 4. parities
v = [x % 2 for x in Lval[1]]
Av = [sum(A[i][k] * v[k] for k in range(8)) % 2 for i in range(8)]
print('4. parities', ''.join(map(str, v)), '(alpha..theta); fixed by the recurrence mod 2:', Av == v)
if Av != v: problems.append('parities not fixed')

# 5. Sigma offset
D = C['DEF']
for m in levels[1:]:
    p = dict(zip(ORDER, Lval[m - 1])); q = dict(zip(ORDER, Lval[m]))
    d = D[str(m)]['Sigma']
    if d['side'] != 5 or d['off'] != p['theta'] + p['epsilon'] + p['alpha']: problems.append(f'Sigma offset at level {m}')
    if C['LEN'][str(m)]['Sigma'][5] - d['off'] != p['beta'] + p['theta']: problems.append(f'Sigma remainder at level {m}')
print(f"5. Sigma offset: d_1 = {D['1']['Sigma']['off']}; d_(m+1) = theta_m + epsilon_m + alpha_m and l(Sigma,5) - d = beta_m + theta_m at levels {levels[1]}..{levels[-1]}:", 'yes' if not problems else 'NO')
print('   letter of Sigma side 5:', letter['Sigma'][5], '; of Xi sides 1, 2:', letter['Xi'][1], letter['Xi'][2], '; of Gamma side 0:', letter['Gamma'][0],
      '; of Gamma side 5:', letter['Gamma'][5], '; of Lambda side 4:', letter['Lambda'][4])

# 6. closed forms
Am = sp.Matrix(A); m = sp.symbols('m', integer=True)
lam = 2 + sp.sqrt(5); mu = 2 - sp.sqrt(5)
x1 = sp.Matrix(Lval[1])
# l_m = a lam^(m-1) + b mu^(m-1) + c, solve from l_1, l_2, l_3
a, b, c = sp.symbols('a b c')
forms = []
for i, x in enumerate(ORDER):
    l = [Lval[k][i] for k in (1, 2, 3)]
    sol = sp.solve([a + b + c - l[0], a * lam + b * mu + c - l[1], a * lam**2 + b * mu**2 + c - l[2]], [a, b, c], dict=True)[0]
    f = sp.nsimplify(sp.simplify(sol[a])), sp.nsimplify(sp.simplify(sol[b])), sp.nsimplify(sp.simplify(sol[c]))
    forms.append(f)
    for k in levels:
        val = sp.simplify(f[0] * lam**(k - 1) + f[1] * mu**(k - 1) + f[2])
        if val != Lval[k][i]: problems.append(f'closed form fails for {x} at level {k}')
print('6. closed forms l_m = a lambda^(m-1) + b mu^(m-1) + c, lambda = 2+sqrt5, mu = 2-sqrt5 (checked at all measured levels):')
for x, f in zip(ORDER, forms): print(f'     {x:8s} a = {sp.radsimp(f[0])}, b = {sp.radsimp(f[1])}, c = {f[2]}')
print('   characteristic polynomial of the letter matrix:', sp.factor(Am.charpoly().as_expr()))
# Krylov dimension of the full 54-vector
Mj = json.load(open(os.path.join(HERE, 'M.json')))['M']
l1 = [C['LEN']['1'][s][j] for s in N for j in range(6)]
Mm = sp.Matrix(Mj); K = sp.Matrix.hstack(*[Mm**i * sp.Matrix(l1) for i in range(6)])
print('   dim span{M^i l_1} =', K.rank())

json.dump({'order': ORDER, 'letter': letter, 'label': lab, 'rec': rec, 'A': A, 'L': Lval, 'parity': v,
           'closed': [[str(sp.radsimp(t)) for t in f] for f in forms], 'd1': D['1']['Sigma']['off']},
          open(os.path.join(HERE, 'letters.json'), 'w'), indent=1)
print('PROBLEMS:' if problems else 'LETTERS: ALL CHECKS PASS'); [print('  ', p) for p in problems]
sys.exit(1 if problems else 0)
