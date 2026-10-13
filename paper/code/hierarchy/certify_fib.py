#!/usr/bin/env python3
"""Second, independent certification of the obligations deferred by certnest.js (paper, Lemma "Uniformity in b"), using the
Fibonacci closed form of the side lengths instead of linear programming. Exact integer arithmetic only.

For m >= 1 the side lengths satisfy, letter by letter (paper, Proposition "Fibonacci side lengths"),
    l_m = F_{3m+1} u + F_{3m+2} w + z,
    u = (0,1,0,0,1,2,0,1),  w = (1,0,2,2,1,0,2,2),  z = (2,2,0,0,0,0,0,-2)   (letters alpha..theta).
An obligation  a.x + e >= t  with x = l_{b-1} (b >= 2) therefore reads  g(b) = P F_n + Q F_{n+1} + R >= 0, n = 3b - 2,
with integers P, Q, R. By Binet, P F_n + Q F_{n+1} = ((P + Q phi) phi^n - (P + Q psi) psi^n) / sqrt5.
  * P = Q = 0: g is constant; check R >= 0.
  * P + Q phi < 0: g -> -infinity; the obligation fails.
  * P + Q phi > 0: P + Q phi is a nonzero element of Z[phi], so |P + Q phi| |P + Q psi| = |P^2 + PQ - Q^2| >= 1 and
    g(b) >= phi^n / (sqrt5 |P + Q psi|) - |P + Q psi| |psi|^n / sqrt5 - |R|. This is >= 0 as soon as
    phi^n >= |P + Q psi| (|P + Q psi| + sqrt5 |R|) (as |psi|^n < 1); below that n we check g(b) >= 0 directly.
An equality  a.x + e == 0  for all b >= 2 holds iff P = Q = R = 0 (F_n, F_{n+1}, 1 are linearly independent).
The threshold is tested with integers: phi^n > F_{n-1}, so F_{n-1} >= K implies phi^n >= K.
usage: python3 certify_fib.py [certnest_deferred.json]
"""
import json, os, sys, math

HERE = os.path.dirname(os.path.abspath(__file__))
path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'certnest_deferred.json')
D = json.load(open(path))
L = json.load(open(os.path.join(HERE, 'letters.json')))
NAMES = D['names']; ORDER = L['order']
u = dict(zip(ORDER, [0, 1, 0, 0, 1, 2, 0, 1])); w = dict(zip(ORDER, [1, 0, 2, 2, 1, 0, 2, 2])); z = dict(zip(ORDER, [2, 2, 0, 0, 0, 0, 0, -2]))
letter_of = [L['letter'][s][j] for s in NAMES for j in range(6)]

def fib(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a

# sanity: the closed form reproduces the measured letter lengths and l_1
for m_str, vals in L['L'].items():
    m = int(m_str)
    for x, v in zip(ORDER, vals):
        assert fib(3 * m + 1) * u[x] + fib(3 * m + 2) * w[x] + z[x] == v, (m, x)
for i, s in enumerate(D['l1']):
    x = letter_of[i]; assert fib(4) * u[x] + fib(5) * w[x] + z[x] == s

def pqr(a, e):
    P = sum(ai * u[letter_of[i]] for i, ai in enumerate(a))
    Q = sum(ai * w[letter_of[i]] for i, ai in enumerate(a))
    R = sum(ai * z[letter_of[i]] for i, ai in enumerate(a)) + e
    return P, Q, R

def sign_P_Qphi(P, Q):   # sign of P + Q (1 + sqrt5)/2  = sign of (2P + Q) + Q sqrt5
    A, B = 2 * P + Q, Q
    if A >= 0 and B >= 0: return 0 if A == 0 and B == 0 else 1
    if A <= 0 and B <= 0: return -1
    # opposite signs: compare A^2 with 5 B^2
    if A > 0: return 1 if A * A > 5 * B * B else -1
    return 1 if 5 * B * B > A * A else -1

def certify_ge(P, Q, R):
    if P == 0 and Q == 0: return R >= 0
    if sign_P_Qphi(P, Q) < 0: return False
    # |P + Q psi| <= |P| + |Q| (|psi| < 1);  K = c (c + 3|R|) with c = |P| + |Q| bounds |P + Q psi|(|P + Q psi| + sqrt5 |R|)
    c = abs(P) + abs(Q); K = c * (c + 3 * abs(R))
    b = 2
    while True:
        n = 3 * b - 2
        if fib(n - 1) >= K: return True          # phi^n > F_{n-1} >= K: the tail bound applies from here on
        if P * fib(n) + Q * fib(n + 1) + R < 0: return False
        b += 1

allok = True
for par, obs in D['obligations'].items():
    good = 0; bad = []
    for ob in obs:
        P, Q, R = pqr(ob['a'], ob['e'])
        if ob['type'] == 'zero': ok = (P, Q, R) == (0, 0, 0)
        else: ok = certify_ge(P, Q, R - ob['t'])
        if ok: good += 1
        else: bad.append(ob['ctx'])
    print(f'{par} b: {len(obs)} deferred obligations, {good} certified by the Fibonacci closed form, {len(bad)} not')
    for c in bad[:20]: print('   NOT certified:', c)
    allok = allok and not bad
print('ALL OBLIGATIONS CERTIFIED BY THE FIBONACCI CLOSED FORM (every b >= 2)' if allok else 'SOME OBLIGATIONS NOT CERTIFIED')
sys.exit(0 if allok else 1)
