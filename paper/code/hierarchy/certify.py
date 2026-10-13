#!/usr/bin/env python3
"""Certify the obligations certnest.js could not certify locally (exact rational arithmetic, LP only as a search aid).

Every real side-length vector x = l_m (m >= 1) lies in the Krylov space Kr = span{l_1, M l_1, M^2 l_1, ...} (P2), and
has every entry >= 5 (P4). So for an obligation  a.x + e >= t  it suffices to find a' with
    (a' - a) orthogonal to Kr,   a' >= 0 coefficientwise,   5 * sum(a') + e >= t,
since then a.x = a'.x >= 5 sum(a') for every real x. For an obligation  a.x + e == 0  it suffices that a is orthogonal
to Kr and e == 0. The LP (scipy) only proposes a'; the check is exact (fractions.Fraction).
usage: python3 certify.py [certnest_deferred.json]
"""
import json, sys, os
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog

path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'certnest_deferred.json')
D = json.load(open(path))
M = [[int(c) for c in row] for row in D['M']]; n = len(M)
l1 = [int(c) for c in D['l1']]

# Krylov basis (exact)
def matvec(A, x): return [sum(A[i][j] * x[j] for j in range(n)) for i in range(n)]
rows, piv, w = [], [], l1[:]
basis = []
for it in range(n + 1):
    r = [Fr(c) for c in w]
    for (b, p) in zip(rows, piv):
        if r[p] != 0:
            f = r[p] / b[p]; r = [ri - f * bi for ri, bi in zip(r, b)]
    nz = [j for j in range(n) if r[j] != 0]
    if not nz: break
    rows.append(r); piv.append(nz[0]); basis.append(w[:])
    w = matvec(M, w)
rk = len(rows)
# nullspace of the Krylov basis (vectors rho with rho . w = 0 for all w in Kr)
A = [[Fr(c) for c in b] for b in basis]
R = [r[:] for r in A]; pivc = []; ri = 0
for c in range(n):
    p = next((i for i in range(ri, rk) if R[i][c] != 0), None)
    if p is None: continue
    R[ri], R[p] = R[p], R[ri]; pv = R[ri][c]; R[ri] = [x / pv for x in R[ri]]
    for i in range(rk):
        if i != ri and R[i][c] != 0:
            f = R[i][c]; R[i] = [x - f * y for x, y in zip(R[i], R[ri])]
    pivc.append(c); ri += 1
free = [c for c in range(n) if c not in pivc]
N = []
for fc in free:
    v = [Fr(0)] * n; v[fc] = Fr(1)
    for i, pc in enumerate(pivc): v[pc] = -R[i][fc]
    den = 1
    for x in v: den = den * x.denominator // np.gcd(den, x.denominator)
    N.append([x * den for x in v])
for v in N:
    for b in basis: assert sum(x * y for x, y in zip(v, b)) == 0
print(f'Krylov space span(M^i l_1): dimension {rk} of {n}; {len(N)} independent relations valid for every real l_m')

def cert_ge(a, e, t):
    a = [Fr(x) for x in a]
    if all(x >= 0 for x in a) and 5 * sum(a) + e >= t: return a
    if not N: return None
    Nm = np.array([[float(x) for x in v] for v in N]).T   # n x k
    af = np.array([float(x) for x in a])
    # maximise sum(a + N y) subject to a + N y >= 0, |y| bounded
    res = linprog(-Nm.sum(axis=0), A_ub=-Nm, b_ub=af, bounds=[(-1e4, 1e4)] * Nm.shape[1], method='highs')
    if res.status != 0: return None
    for lim in (10**3, 10**6, 10**9):
        y = [Fr(v).limit_denominator(lim) for v in res.x]
        ap = [a[i] + sum(N[j][i] * y[j] for j in range(len(N))) for i in range(n)]
        if all(x >= 0 for x in ap) and 5 * sum(ap) + e >= t: return ap
    return None

allok = True
for par, obs in D['obligations'].items():
    good, bad = 0, []
    for ob in obs:
        if ob['type'] == 'zero':
            ok = ob['e'] == 0 and all(sum(Fr(ob['a'][i]) * b[i] for i in range(n)) == 0 for b in basis)
        else:
            ok = cert_ge(ob['a'], ob['e'], ob['t']) is not None
        if ok: good += 1
        else: bad.append(ob['ctx'])
    print(f'{par} b: {len(obs)} deferred obligations, {good} certified, {len(bad)} NOT certified')
    for c in bad[:20]: print('   NOT certified:', c)
    allok = allok and not bad
print('ALL OBLIGATIONS CERTIFIED (valid for every base b >= 2)' if allok else 'SOME OBLIGATIONS NOT CERTIFIED')
