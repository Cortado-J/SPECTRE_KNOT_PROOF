#!/usr/bin/env python3
"""Review check of Table 6 (the junction map, Lemma 9.3) on the actual nest blocks, built from the tiles in exact
arithmetic by exact/exact.py (AI review pass of 11 Oct 2026; not used by the proof).

For m = 1, 2, 3: N_{m+1} is the level-(m+1) Delta-supertile and N_m its child 1. From every rim port of N_m, follow the
ribbon through N_m and on through N_{m+1} (exact.py's boxes and edge matching) to the rim of N_{m+1}, and compare the rim
vertex reached with the junction that Table 6 names (or, strictly inside side 2 of N_m, with the vertex itself).

Usage: python3 crosscheck/junction_actual.py   (from paper/code)
"""
import os, sys, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'exact'))
import exact as X

HERE = os.path.dirname(os.path.abspath(__file__))
ST = json.load(open(os.path.join(HERE, '..', 'hierarchy', 'combin_8.json')))['ST']['1']['Delta']
PIECES = [tuple(map(int, p.split('.'))) for side in ST['pside'] for p in side]

def tgt(omega, V, E, u, s):
    """Table 6. V: vertex positions of N_m (own order from A); s True for R."""
    if omega > 0:
        if u in (0, 1): return 17 if s else 9
        if u <= V[2]: return 17
        if u < V[3]: return None
        if u < V[4]: return 16
        if u < V[5]: return 12
        return 9
    if u in (0, E - 1): return 21 if s else 16
    if u <= V[1]: return 21
    if u <= V[2]: return 17
    if u < V[3]: return None
    return 16

def main():
    top = 6
    lev, trs_all = X.build(top)
    VERT = {m: X.find_vertices(lev, trs_all, m, min(3, top - m))[0] for m in range(1, 4)}
    allok = True
    for m in (1, 2, 3):
        omega = 1 if m % 2 == 0 else -1
        info, kinds = X.INFO[(m + 1, 'Delta')]
        kids = [(lev[m][s], trs_all[m][i]) for i, s in enumerate(X.SR['Delta']) if s]
        mate, rim, cv = info['mate'], info['rim'], info['cv']
        P = lev[m + 1]['Delta']; PE = P.E
        child = kids[1][0]; E = child.E; Vc = VERT[m]['Delta']
        assert kinds[1] == 'Delta' and Vc[0] == 0
        # side lengths of the children (own order), for the junction positions on the parent's rim
        def sidelen(c, j):
            b = kids[c][0]; pos = VERT[m][kinds[c]]
            return ((pos[(j + 1) % 6] - pos[j]) % b.E) or b.E
        jpos = [sum(sidelen(c, j) for c, j in PIECES[:q]) for q in range(22)]
        assert sum(sidelen(c, j) for c, j in PIECES) == PE
        def cross(c, p):
            k, s = p >> 1, p & 1
            c2, k2 = mate[(c, k)]
            x = cv[c][(k + s) % kids[c][0].E]
            s_same = 0 if cv[c2][k2] == x else 1
            return c2, 2 * k2 + (1 - s_same)
        pidx = {(c, k): K for K, (c, k, v) in enumerate(rim)}
        def exit_vertex(c, p):
            """parent rim vertex (as a point) where the ribbon entering child c at port p leaves the parent"""
            while True:
                q = kids[c][0].pair[p]
                if (c, q >> 1) not in mate:
                    k, s = q >> 1, q & 1
                    return cv[c][(k + s) % kids[c][0].E]
                c, p = cross(c, q)
        bad = 0; counts = {}; bad_swapped = 0
        for u in range(E):
            k = (u + child.defA) % E
            for s in (True, False):
                p = X.portR(k, E) if s else X.portL(k, E)
                pt = exit_vertex(1, p)
                q = tgt(omega, Vc, E, u, s)
                if q is None:
                    want = cv[1][k]
                else:
                    want = P.verts[(jpos[q] + P.defA) % PE]
                counts[q] = counts.get(q, 0) + 1
                if pt != want: bad += 1
                qs = {12: 16, 16: 12}.get(q, q)                   # negative control: junctions 12 and 16 exchanged
                if qs is not None and pt != P.verts[(jpos[qs] + P.defA) % PE]: bad_swapped += 1
        allok = allok and bad == 0
        print(f'N_{m} in N_{m+1} (omega_m = {omega:+d}): {2 * E} rim ports of N_{m}, '
              + ', '.join(f'{"hook" if q is None else "J" + str(q)}: {n}' for q, n in sorted(counts.items(), key=lambda t: -1 if t[0] is None else t[0]))
              + f'; {bad} disagree with Table 6 ({bad_swapped} with junctions 12 and 16 exchanged)')
        allok = allok and bad_swapped > 0
    print('TABLE 6 HOLDS ON THE ACTUAL BLOCKS' if allok else 'FAILED')
    sys.exit(0 if allok else 1)

if __name__ == '__main__':
    main()
