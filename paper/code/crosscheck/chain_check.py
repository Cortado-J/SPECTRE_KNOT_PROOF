#!/usr/bin/env python3
"""Review check of Lemmas 7.1, 7.2 and 8.7 as worded in the paper (AI review pass of 11 Oct 2026; not used by the proof).

From (l_m, d_m), undo moves exactly as the proof of Lemma 7.2(b) chooses them (a side with excess chosen at random;
its third edge; on the Sigma child's side 5 the second edge before A_Sigma if d >= d_1 + 2, else the second edge after
it) until (l_1, d_1) is reached. At every step check that the move is allowed (not the first or last edge of its side
in either child, not an edge at A_Sigma), that d' follows the rule, that both pairs are admissible, and that the edge is
two edges clear of the ends of its side unless the side is Sigma's side 5 or glued to it. For m = 2, check that every
composition on the chain has the signature (Lemma 7.1, Prop 7.4) for both signs and, for Delta, the junction property
(Lemma 9.3); for m = 3, the chain only, with the compositions checked every 25 steps.

Usage: python3 crosscheck/chain_check.py   (from paper/code)
"""
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hierarchy'))
from compositions import Comp, ST, KINDS, letter_lengths, d_off, lens_of, parse

def run(T, m, check_every, rng):
    kinds = ST[T]['kids']
    adj = [[None if s == 'R' else parse(s) for s in row] for row in ST[T]['sides']]
    cs = kinds.index('Sigma')
    l1, d1 = lens_of(T, letter_lengths(1)), d_off(1)
    L, d = lens_of(T, letter_lengths(m)), d_off(m)
    n = len(kinds)

    def admissible(L, d):
        for c in range(n):
            for j in range(6):
                if L[c][j] < l1[c][j] or (L[c][j] - l1[c][j]) % 2: return False
                a = adj[c][j]
                if a and L[a[0]][a[1]] != L[c][j]: return False
        return d >= d1 and (d - d1) % 2 == 0 and L[cs][5] - d >= l1[cs][5] - d1

    def is_sig5(c, j):
        return (c, j) == (cs, 5) or adj[c][j] == (cs, 5)

    chain, problems = [(L, d)], []
    while not (L == l1 and d == d1):
        assert admissible(L, d), (T, m, 'not admissible')
        cand = [(c, j) for c in range(n) for j in range(6) if L[c][j] >= l1[c][j] + 2]
        if not cand: problems.append('no side with excess, but (L, d) != (l_1, d_1)'); break
        c, j = rng.choice(cand)
        L0 = [row[:] for row in L]
        if is_sig5(c, j):
            c, j = cs, 5
            if d >= d1 + 2: r, d0 = 1, d - 2
            else: r, d0 = d + 1, d
        else:
            r, d0 = 2, d
        L0[c][j] -= 2
        a = adj[c][j]
        if a: L0[a[0]][a[1]] -= 2
        Ls = L0[c][j]
        # the move from (L0, d0): edge r of side j of c (and Ls-1-r of the partner side)
        ok = 1 <= r and r + 2 <= Ls
        sides = [(c, j, r)] + ([(a[0], a[1], Ls - 1 - r)] if a else [])
        dnew = d0
        for (cc, jj, rr) in sides:
            ok = ok and 1 <= rr and rr + 2 <= Ls
            if (cc, jj) == (cs, 5):
                ok = ok and rr not in (d0 - 1, d0)            # not an edge at A_Sigma
                if rr + 2 <= d0: dnew = d0 + 2
            elif not is_sig5(c, j):
                ok = ok and 2 <= rr and rr + 3 <= Ls          # two edges clear of both ends
        if not ok: problems.append(f'move not allowed at {(c, j, r)}')
        if dnew != d: problems.append(f'd rule gives {dnew}, expected {d}')
        if not admissible(L0, d0): problems.append('shortened pair not admissible')
        L, d = L0, d0
        chain.append((L, d))
    checked = 0
    for i, (L, d) in enumerate(chain):
        if check_every and (i % check_every == 0 or i == len(chain) - 1):
            for om in (1, -1):
                C = Comp(T, L, d, om)
                ends = C.walk_all()
                bad = C.signature(ends) + (C.junction_map(ends) if T == 'Delta' else [])
                if bad: problems.append(f'step {i} omega {om}: {bad[:2]}')
                checked += 1
    return len(chain) - 1, checked, problems

def main():
    rng = random.Random(20261012)
    allok = True
    for m, every in ((2, 1), (3, 25)):
        for T in KINDS:
            steps, checked, problems = run(T, m, every, rng)
            allok = allok and not problems
            print(f'm={m} {T:7s}: {steps:5d} moves back to (l_1, d_1), {checked:4d} compositions checked: '
                  + ('ok' if not problems else 'PROBLEMS ' + '; '.join(problems[:3])))
    print('ALL CHAINS OK' if allok else 'FAILED')
    sys.exit(0 if allok else 1)

if __name__ == '__main__':
    main()
