#!/usr/bin/env python3
"""Sizes table of the paper (Appendix A): tiles in a Delta-supertile (from the children of Table 1, a Mystic counting
two tiles), rim length E_m(Delta) = alpha+beta+2 gamma+epsilon+zeta and shortest side beta_m (Proposition 6.2), levels
1..9, checked against the measured lengths in letters.json where available. usage: python3 sizes.py"""
import json, os
HERE = os.path.dirname(os.path.abspath(__file__))
SR = {'Gamma': ['Pi', 'Delta', 'Theta', 'Sigma', 'Xi', 'Phi', 'Gamma'],
      'Delta': ['Xi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'], 'Theta': ['Psi', 'Delta', 'Pi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'],
      'Lambda': ['Psi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'], 'Xi': ['Psi', 'Delta', 'Pi', 'Phi', 'Sigma', 'Psi', 'Phi', 'Gamma'],
      'Pi': ['Psi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Psi', 'Phi', 'Gamma'], 'Sigma': ['Xi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Pi', 'Lambda', 'Gamma'],
      'Phi': ['Psi', 'Delta', 'Psi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'], 'Psi': ['Psi', 'Delta', 'Psi', 'Phi', 'Sigma', 'Psi', 'Phi', 'Gamma']}
C = json.load(open(os.path.join(HERE, 'combin_8.json')))
assert all(C['ST']['1'][T]['kids'] == SR[T] for T in SR), 'children differ from combin_8.json'
def F(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a
L = json.load(open(os.path.join(HERE, 'letters.json')))['L']
t = {k: (2 if k == 'Gamma' else 1) for k in SR}
print('level  tiles(Delta)  E_m(Delta)  beta_m')
for m in range(1, 10):
    t = {k: sum(t[s] for s in SR[k]) for k in SR}
    al, be, ga, ep, ze = F(3*m+2) + 2, F(3*m+1) + 2, 2*F(3*m+2), F(3*m+3), 2*F(3*m+1)
    E = al + be + 2*ga + ep + ze
    if str(m) in L:
        a, b, g, d, e, z, h, th = L[str(m)]
        assert (al, be, ga, ep, ze) == (a, b, g, e, z), m
    print(f'{m:5d}  {t["Delta"]:12d}  {E:10d}  {be:6d}')
print('SIZES: OK')
