#!/usr/bin/env python3
"""Independent exact re-implementation of the base computations (paper, Sections 5-7 and Appendix A).

Everything is computed in exact integer arithmetic: every tile vertex is an element of Z[zeta], zeta = exp(i pi/6),
stored as four integers (a, b, c, d) meaning a + b zeta + c zeta^2 + d zeta^3 (zeta^4 = zeta^2 - 1). Isometries are
z -> zeta^k z + t or z -> zeta^k conj(z) + t. There is no floating point except to read off the sign of a polygon's
area (|area| >= 8 for every polygon involved, so the sign is not in doubt).

This program shares no code with core/ and hierarchy/ (JavaScript, floating point). It
  1. builds Tile(1,1), the Mystic and the supertiles of levels 1..L with Kaplan's key-point construction
     (the spectre paper, Appendix A), exactly;
  2. composes the strand pairings exactly (the edge rule), level by level, and checks the signature theorem's
     hypotheses at levels 1..L: exactly two non-hook rim vertices, adjacent, at the Gamma child's A and B,
     crossover R(A)-R(B), L(A)-L(B), no closed strand;
  3. finds the six hexagon vertices of every level-m supertile (points where three level-m supertiles meet),
     extracts the composition pattern C (child sides, partners, parent sides as concatenations of child sides,
     position of the parent's A) for the compositions m -> m+1, and the side lengths l_m and Sigma offsets d_m;
  4. compares all of this with the JavaScript output hierarchy/combin_8.json (if present);
  5. optionally follows the strands through the nest N_b < N_{b+1} < ... exactly (bases given with --nest).
usage: python3 exact.py [L=4] [--nest 1,2 --nestL 6]
"""
import sys, os, json, time

# ------------------------------------------------------------------ Z[zeta], zeta = e^{i pi/6}
def zadd(x, y): return (x[0] + y[0], x[1] + y[1], x[2] + y[2], x[3] + y[3])
def zsub(x, y): return (x[0] - y[0], x[1] - y[1], x[2] - y[2], x[3] - y[3])
def zneg(x): return (-x[0], -x[1], -x[2], -x[3])
def zmul_zeta(x):  # zeta * (a + b z + c z^2 + d z^3) = a z + b z^2 + c z^3 + d (z^2 - 1)
    a, b, c, d = x; return (-d, a, b + d, c)
ZP = [(1, 0, 0, 0)]
for _ in range(11): ZP.append(zmul_zeta(ZP[-1]))
assert zmul_zeta(ZP[11]) == ZP[0]
def zrot(x, k):
    k %= 12
    for _ in range(k): x = zmul_zeta(x)
    return x
def zscale(x, n): return (x[0] * n, x[1] * n, x[2] * n, x[3] * n)
def zconj(x):  # conj(zeta^k) = zeta^(12-k)
    r = zscale(ZP[0], x[0])
    for k in (1, 2, 3): r = zadd(r, zscale(ZP[(12 - k) % 12], x[k]))
    return r
S3 = 3 ** 0.5
def zfloat(x):  # only for orientation and pictures
    re = x[0] + x[1] * S3 / 2 + x[2] * 0.5
    im = x[1] * 0.5 + x[2] * S3 / 2 + x[3]
    return (re, im)
ZERO = (0, 0, 0, 0)

# isometry: (k, refl, t):  z -> zeta^k * (conj(z) if refl else z) + t
def iapply(g, z):
    k, r, t = g
    return zadd(zrot(zconj(z) if r else z, k), t)
def icompose(g1, g2):  # g1 o g2
    k1, r1, t1 = g1; k2, r2, t2 = g2
    k = (k1 + (-k2 if r1 else k2)) % 12
    return (k, r1 ^ r2, zadd(zrot(zconj(t2) if r1 else t2, k1), t1))
ID = (0, False, ZERO)
def itrans(t): return (0, False, t)
def irot(k): return (k % 12, False, ZERO)
REFL = (6, True, ZERO)          # (x, y) -> (-x, y), i.e. z -> -conj(z)
def idet(g): return -1 if g[1] else 1

# ------------------------------------------------------------------ Tile(1,1)
# edge directions in multiples of 30 degrees, e_i = v_i v_{i+1}
DIRS = [0, 10, 1, 3, 0, 2, 5, 7, 4, 6, 6, 8, 11, 9]
PTS = [ZERO]
for k in DIRS[:-1]: PTS.append(zadd(PTS[-1], ZP[k]))
assert zadd(PTS[-1], ZP[DIRS[-1]]) == ZERO, 'tile does not close'
# the floating-point coordinates used by core/hier.js, for comparison
_S = S3
PTS_F = [(0, 0), (1, 0), (1.5, -_S / 2), (1.5 + _S / 2, 0.5 - _S / 2), (1.5 + _S / 2, 1.5 - _S / 2), (2.5 + _S / 2, 1.5 - _S / 2),
         (3 + _S / 2, 1.5), (3, 2), (3 - _S / 2, 1.5), (2.5 - _S / 2, 1.5 + _S / 2), (1.5 - _S / 2, 1.5 + _S / 2),
         (0.5 - _S / 2, 1.5 + _S / 2), (-_S / 2, 1.5), (0, 1)]
for p, q in zip(PTS, PTS_F): assert abs(zfloat(p)[0] - q[0]) < 1e-12 and abs(zfloat(p)[1] - q[1]) < 1e-12
QUAD = [PTS[3], PTS[5], PTS[7], PTS[11]]
NAMES = ['Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Phi', 'Psi']
SR = {  # children in the order of the spectre paper's substitution as implemented by Kaplan (None = no child)
    'Gamma': ['Pi', 'Delta', None, 'Theta', 'Sigma', 'Xi', 'Phi', 'Gamma'],
    'Delta': ['Xi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'],
    'Theta': ['Psi', 'Delta', 'Pi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'],
    'Lambda': ['Psi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'],
    'Xi': ['Psi', 'Delta', 'Pi', 'Phi', 'Sigma', 'Psi', 'Phi', 'Gamma'],
    'Pi': ['Psi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Psi', 'Phi', 'Gamma'],
    'Sigma': ['Xi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Pi', 'Lambda', 'Gamma'],
    'Phi': ['Psi', 'Delta', 'Psi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'],
    'Psi': ['Psi', 'Delta', 'Psi', 'Phi', 'Sigma', 'Psi', 'Phi', 'Gamma'],
}
MYSTIC2 = icompose(itrans(PTS[8]), irot(1))   # second tile of the Mystic: rotate 30 degrees, then move to v_8

def level_transforms(quad):
    """Kaplan's key-point construction: the eight child placements and the next level's key points."""
    rules = [(60, 3, 1), (0, 2, 0), (60, 3, 1), (60, 3, 1), (0, 2, 0), (60, 3, 1), (-120, 3, 3)]
    trs = [ID]; tot = 0; rot = ID; tq = list(quad)
    for ang, fr, to in rules:
        if ang:
            tot += ang; rot = irot(tot // 30); tq = [iapply(rot, q) for q in quad]
        src = iapply(trs[-1], quad[fr])
        trs.append(icompose(itrans(zsub(src, tq[to])), rot))
    trs = [icompose(REFL, t) for t in trs]
    sq = [iapply(trs[6], quad[2]), iapply(trs[5], quad[1]), iapply(trs[3], quad[2]), iapply(trs[0], quad[1])]
    return trs, sq

# ------------------------------------------------------------------ boxes: rim cycle + port pairing
# A box: E rim edges, verts[k] = rim vertex k (own frame), edge k = verts[k] -> verts[k+1], listed ccw in the own frame.
# Ports: 2k = port on edge k near verts[k]  (= R(v_k)),  2k+1 = port on edge k near verts[k+1]  (= L(v_{k+1})).
# pair: list of length 2E (involution).  defA/defB: rim positions of the two crossover corners.
def area2(pts):
    s = 0.0
    for i in range(len(pts)):
        x0, y0 = zfloat(pts[i]); x1, y1 = zfloat(pts[(i + 1) % len(pts)])
        s += x0 * y1 - x1 * y0
    return s

class Box:
    __slots__ = ('E', 'verts', 'pair', 'loops', 'defs', 'defA', 'defB', 'kind', 'level', 'ntiles')

def tile_box():
    b = Box(); b.E = 14; b.verts = list(PTS)
    assert area2(b.verts) > 0
    P = [None] * 28
    def link(x, y): P[x] = y; P[y] = x
    R = lambda i: 2 * i                     # port on e_i near v_i
    L = lambda i: 2 * ((i - 1) % 14) + 1    # port on e_{i-1} near v_i
    for i in range(2, 14): link(L(i), R(i))
    link(R(0), R(1)); link(L(0), L(1))
    b.pair = P; b.loops = 0; b.ntiles = 1
    finish(b)
    return b

def portL(k, E): return 2 * ((k - 1) % E) + 1
def portR(k, E): return 2 * k
def finish(b):
    b.defs = [k for k in range(b.E) if b.pair[portL(k, b.E)] != portR(k, b.E)]

def compose(children, labels=None):
    """children: list of (box, g). Exact composition. Returns parent box (own frame = the frame of the g's), plus
    the data needed for C: for every child rim edge its partner (child, edge) or None, and the parent rim as a
    sequence of (child, edge). labels: optional {child index: list of 2E label ids or -1} propagated to the parent
    with union-find (for the nest)."""
    edges = {}   # frozenset key of endpoints -> list of (c, k)
    cv = []      # per child: list of vertices in the parent frame, ordered as the child's own rim
    for c, (bx, g) in enumerate(children):
        V = [iapply(g, v) for v in bx.verts]
        cv.append(V)
        for k in range(bx.E):
            key = (V[k], V[(k + 1) % bx.E]) if V[k] < V[(k + 1) % bx.E] else (V[(k + 1) % bx.E], V[k])
            edges.setdefault(key, []).append((c, k))
    mate = {}
    for key, lst in edges.items():
        if len(lst) == 2: mate[lst[0]] = lst[1]; mate[lst[1]] = lst[0]
        elif len(lst) != 1: raise RuntimeError('edge shared by %d children' % len(lst))
    # parent rim: chain the unmatched child edges; each child edge is traversed in the child's own direction,
    # which is ccw in the parent frame iff g preserves orientation
    out = {}   # start vertex (parent frame, parent direction) -> (c, k, forward)
    for c, (bx, g) in enumerate(children):
        V = cv[c]
        for k in range(bx.E):
            if (c, k) in mate: continue
            p, q = V[k], V[(k + 1) % bx.E]
            if idet(g) < 0: p, q = q, p
            if p in out: raise RuntimeError('rim vertex of degree > 2')
            out[p] = (c, k, q)
    start = next(iter(out)); rim = []; v = start
    while True:
        c, k, q = out[v]; rim.append((c, k, v)); v = q
        if v == start: break
    if len(rim) != len(out): raise RuntimeError('rim is not a single cycle')
    pverts = [r[2] for r in rim]
    if area2(pverts) < 0: raise RuntimeError('parent rim not ccw')
    E = len(rim)
    # parent port of child port: child port (c, 2k+s); parent edge K traverses child edge k forward iff det > 0
    pidx = {(c, k): K for K, (c, k, v) in enumerate(rim)}
    def to_parent(c, p):
        k, s = p >> 1, p & 1
        K = pidx[(c, k)]
        fwd = idet(children[c][1]) > 0
        return 2 * K + (s if fwd else 1 - s)
    def cross(c, p):   # straight through the shared edge: near endpoint x on one side -> near the other endpoint
        k, s = p >> 1, p & 1
        c2, k2 = mate[(c, k)]
        bx, g = children[c]; bx2, g2 = children[c2]
        x = cv[c][(k + s) % bx.E]                  # the endpoint we are near
        s_same = 0 if cv[c2][k2] == x else 1       # the same endpoint in c2's numbering
        assert cv[c2][(k2 + s_same) % bx2.E] == x
        return c2, 2 * k2 + (1 - s_same)
    pair = [None] * (2 * E); visited = set(); plab = {} if labels is not None else None
    uf = None
    for K in range(E):
        for s in (0, 1):
            P0 = 2 * K + s
            if pair[P0] is not None: continue
            c, k, v = rim[K]
            fwd = idet(children[c][1]) > 0
            p = 2 * k + (s if fwd else 1 - s)
            acc = set()
            while True:
                visited.add((c, p))
                if labels is not None and c in labels and labels[c][p] >= 0: acc.add(labels[c][p])
                q = children[c][0].pair[p]; visited.add((c, q))
                if (c, q >> 1) not in mate:
                    P1 = to_parent(c, q); pair[P0] = P1; pair[P1] = P0
                    if labels is not None and acc: plab[P0] = acc; plab[P1] = acc
                    break
                c, p = cross(c, q)
    loops = 0; lost = set()
    for c, (bx, g) in enumerate(children):
        for p in range(2 * bx.E):
            if (c, p) in visited or (c, p >> 1) not in mate: continue
            loops += 1; cc, pp = c, p
            while True:
                visited.add((cc, pp))
                if labels is not None and cc in labels and labels[cc][pp] >= 0: lost.add(labels[cc][pp])
                q = children[cc][0].pair[pp]; visited.add((cc, q))
                cc, pp = cross(cc, q)
                if (cc, pp) in visited: break
    b = Box(); b.E = E; b.verts = pverts; b.pair = pair; b.loops = loops + sum(ch[0].loops for ch in children)
    b.ntiles = sum(ch[0].ntiles for ch in children)
    finish(b)
    return b, dict(mate=mate, rim=rim, cv=cv, plab=plab, lost=lost)

def crossover_ok(b, A, B):
    """signature at {A, B}: B adjacent to A and R(A)-R(B), L(A)-L(B)."""
    E = b.E
    adj = (B - A) % E in (1, E - 1)
    return adj and b.pair[portR(A, E)] == portR(B, E) and b.pair[portL(A, E)] == portL(B, E)

# ------------------------------------------------------------------ build the hierarchy
def build(L):
    tile = tile_box(); tile.kind = 'tile'; tile.level = 0
    tile.defA, tile.defB = 0, 1
    myst, info = compose([(tile, ID), (tile, MYSTIC2)])
    # the Mystic's A, B: the first tile's v_0, v_1
    vA, vB = PTS[0], PTS[1]
    myst.defA = myst.verts.index(vA); myst.defB = myst.verts.index(vB)
    lev = [{s: (myst if s == 'Gamma' else tile) for s in NAMES}]
    trs_all = []
    quad = QUAD
    for N in range(1, L + 1):
        trs, quad = level_transforms(quad)
        trs_all.append(trs)
        nxt = {}
        for T in NAMES:
            kids = [(lev[-1][s], trs[i]) for i, s in enumerate(SR[T]) if s]
            kinds = [s for s in SR[T] if s]
            b, info = compose(kids)
            b.kind = T; b.level = N
            # inherited corner: the Gamma child (the last one)'s A and B
            gb, gg = kids[-1]
            pa, pb = iapply(gg, gb.verts[gb.defA]), iapply(gg, gb.verts[gb.defB])
            b.defA = b.verts.index(pa) if pa in b.verts else -1
            b.defB = b.verts.index(pb) if pb in b.verts else -1
            nxt[T] = b
            INFO[(N, T)] = (info, kinds)
        lev.append(nxt)
    return lev, trs_all
INFO = {}

def own_positions(b):
    return {v: k for k, v in enumerate(b.verts)}

def descendants(lev, trs_all, M, T, m):
    """level-m descendants of the level-M supertile of kind T: list of (kind, g)."""
    cur = [(T, ID)]
    for N in range(M, m, -1):
        nx = []
        for s, g in cur:
            for i, k in enumerate(SR[s]):
                if k: nx.append((k, icompose(g, trs_all[N - 1][i])))
        cur = nx
    return cur

def find_vertices(lev, trs_all, m, depth):
    """Points of the rim of a level-m supertile where three or more level-m supertiles meet, observed inside the
    level-(m+d) supertiles of every kind, d = 1..depth. Returned as own-rim positions relative to A, per kind."""
    seen = {s: set() for s in NAMES}; meet = {}
    for d in range(1, depth + 1):
        M = m + d
        for T in NAMES:
            ps = descendants(lev, trs_all, M, T, m)
            cnt = {}
            vs = []
            for s, g in ps:
                b = lev[m][s]
                V = [iapply(g, v) for v in b.verts]
                vs.append(V)
                for v in V: cnt[v] = cnt.get(v, 0) + 1
            # a point is surrounded inside the patch iff it is not on the patch rim
            P = lev[M][T]; rimset = set(P.verts)
            for (s, g), V in zip(ps, vs):
                b = lev[m][s]
                for k, v in enumerate(V):
                    if v in rimset: continue
                    if cnt[v] >= 3:
                        seen[s].add((k - b.defA) % b.E); meet[cnt[v]] = meet.get(cnt[v], 0) + 1
    return {s: sorted(seen[s]) for s in NAMES}, meet

def extract_C(lev, trs_all, m, VERT, VERTP):
    """composition pattern for m -> m+1 in the same format as hierarchy/combin.js (ST)."""
    ST = {}
    for T in NAMES:
        info, kinds = INFO[(m + 1, T)]
        kids = [(lev[m][s], trs_all[m][i]) for i, s in enumerate(SR[T]) if s]
        n = len(kids)
        # child vertex rim positions (own numbering) of vertex j
        absv = []
        for c, (b, g) in enumerate(kids):
            absv.append([(p + b.defA) % b.E for p in VERT[kinds[c]]])
        def side_of(c, k):
            b = kids[c][0]; A = absv[c]
            for j in range(6):
                l = (A[(j + 1) % 6] - A[j]) % b.E
                if (k - A[j]) % b.E < l: return j
        mate = info['mate']
        sides = []
        for c, (b, g) in enumerate(kids):
            row = []
            for j in range(6):
                l = (absv[c][(j + 1) % 6] - absv[c][j]) % b.E; nb = None
                for t in range(l):
                    k = (absv[c][j] + t) % b.E
                    o = 'R' if (c, k) not in mate else '%d.%d' % (mate[(c, k)][0], side_of(*mate[(c, k)]))
                    if nb is None: nb = o
                    elif nb != o: raise RuntimeError(f'level {m} {T} child {c} side {j}: neighbour changes inside a side')
                row.append(nb)
            sides.append(row)
        # parent sides
        P = lev[m + 1][T]; PE = P.E
        pabs = [(p + P.defA) % PE for p in VERTP[T]]
        rim = info['rim']
        pside = []
        for J in range(6):
            a = pabs[J]; l = (pabs[(J + 1) % 6] - a) % PE; seq = []; cur = None; run = 0
            for t in range(l):
                c, k, v = rim[(a + t) % PE]; tag = '%d.%d' % (c, side_of(c, k))
                if tag != cur:
                    if cur is not None: seq.append((cur, run))
                    cur = tag; run = 0
                run += 1
            seq.append((cur, run))
            for tag, r in seq:
                c, j = map(int, tag.split('.'))
                lc = (absv[c][(j + 1) % 6] - absv[c][j]) % kids[c][0].E
                if lc != r: raise RuntimeError(f'level {m+1} {T} side {J}: partial child side')
            pside.append([t for t, r in seq])
        # parent A: side and whether at a vertex
        def defof(E, pos):
            for j in range(6):
                l = (pos[(j + 1) % 6] - pos[j]) % E; o = (0 - pos[j]) % E
                if o < l: return {'side': j, 'off': o}
        ST[T] = {'kids': kinds, 'sides': sides, 'pside': pside, 'pdef': defof(PE, VERTP[T])}
    return ST

def side_lengths(b, pos):
    return [((pos[(j + 1) % 6] - pos[j]) % b.E) or b.E for j in range(6)]

# ------------------------------------------------------------------ main
def main():
    args = sys.argv[1:]
    L = int(args[0]) if args and args[0].isdigit() else 4
    nest = []; nestL = 0
    if '--nest' in args: nest = [int(x) for x in args[args.index('--nest') + 1].split(',')]
    if '--nestL' in args: nestL = int(args[args.index('--nestL') + 1])
    t0 = time.time()
    problems = []
    tile = tile_box()
    print(f'Tile(1,1): 14 vertices in Z[zeta]; area {area2(tile.verts) / 2:.6f}; pieces: hooks at v2..v13, crossover at v0 v1; non-hook corners {tile.defs}')
    if tile.defs != [0, 1] or not crossover_ok(tile, 0, 1): problems.append('tile')
    top = max(L + 3, nestL)
    lev, trs_all = build(top)
    print(f'built levels 0..{top} exactly in {time.time() - t0:.1f} s; Delta rims: ' + ', '.join(str(lev[N]['Delta'].E) for N in range(top + 1)))
    print(f"Mystic: rim {lev[0]['Gamma'].E}, non-hook corners {len(lev[0]['Gamma'].defs)}, A={lev[0]['Gamma'].defA} B={lev[0]['Gamma'].defB}, crossover {crossover_ok(lev[0]['Gamma'], lev[0]['Gamma'].defA, lev[0]['Gamma'].defB)}, loops {lev[0]['Gamma'].loops}")
    # 2. signature at levels 1..L
    for N in range(1, L + 1):
        row = []
        for T in NAMES:
            b = lev[N][T]
            ok = (b.loops == 0 and len(b.defs) == 2 and b.defA >= 0 and b.defB >= 0 and sorted(b.defs) == sorted([b.defA, b.defB])
                  and crossover_ok(b, b.defA, b.defB))
            w = (b.defB - b.defA) % b.E
            w = 1 if w == 1 else -1
            if w != (-1) ** N: ok = False
            row.append(f"{T}:{b.E}e/{b.ntiles}t {'ok' if ok else 'FAIL'}")
            if not ok: problems.append(f'signature at level {N} {T}')
        print(f'level {N}: signature at the Gamma child\'s A,B with B = A + (-1)^N, crossover R-R/L-L, no loops: ' + ' '.join(row))
    # 2b. edge index parity (the drawing's crossing points coincide)
    for N in range(1, min(L, 4) + 1):
        shared, bad, dets = edge_index_parity(trs_all, N)
        print(f'level {N}: {shared} shared tile edges in the nine supertiles; all glue e_i to e_j with i+j odd, opposite directions: {bad == 0}; tile orientations in the own frame: {sorted(dets)}')
        if bad: problems.append(f'edge index parity at level {N}')
    # 3. vertices, C, lengths
    VERT = {}; meetall = {}
    for m in range(1, L + 1):
        depth = min(3, top - m)
        VERT[m], meet = find_vertices(lev, trs_all, m, depth)
        meetall[m] = meet
        bad = [s for s in NAMES if len(VERT[m][s]) != 6]
        print(f'level {m}: hexagon vertices observed within levels {m+1}..{m+depth}: ' + ' '.join(f'{s}:{VERT[m][s]}' for s in NAMES) + f' | pieces meeting {meet}' + (f' | INCOMPLETE {bad}' if bad else ''))
    ST = {}; LEN = {}; DEF = {}
    for m in range(1, L + 1):
        if any(len(VERT[m][s]) != 6 for s in NAMES): continue
        LEN[m] = {s: side_lengths(lev[m][s], VERT[m][s]) for s in NAMES}
        for s in NAMES:
            pos = VERT[m][s]; E = lev[m][s].E
            for j in range(6):
                l = (pos[(j + 1) % 6] - pos[j]) % E; o = (0 - pos[j]) % E
                if o < l: DEF.setdefault(m, {})[s] = {'side': j, 'off': o}; break
    for m in range(1, L):
        if m in LEN and m + 1 in LEN:
            ST[m] = extract_C(lev, trs_all, m, VERT[m], VERT[m + 1])
    ms = sorted(ST)
    norm = lambda st: json.dumps({T: dict(st[T], pdef={'side': st[T]['pdef']['side'], 'atVertex': st[T]['pdef']['off'] == 0}) for T in st}, sort_keys=True)
    ref = norm(ST[ms[0]])   # the Sigma offset itself grows with the level; compare only its side and whether it is a vertex
    for m in ms:
        same = norm(ST[m]) == ref
        print(f'composition pattern C_{m} ({m} -> {m+1}): ' + ('identical to C_%d' % ms[0] if same else 'DIFFERENT'))
        if not same: problems.append(f'C_{m} differs')
    for m in sorted(LEN): print(f'side lengths l_{m}: ' + ' '.join(f"{s[:3]}{LEN[m][s]}" for s in NAMES) + f"  Sigma A: side {DEF[m]['Sigma']['side']} offset {DEF[m]['Sigma']['off']}")
    # 4. compare with the JavaScript extraction
    cj = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hierarchy', 'combin_8.json')
    if os.path.exists(cj):
        J = json.load(open(cj))
        okC = all(json.dumps({T: {k: J['ST'][str(m)][T][k] for k in ('kids', 'sides', 'pside')} for T in NAMES}, sort_keys=True)
                  == json.dumps({T: {k: ST[m][T][k] for k in ('kids', 'sides', 'pside')} for T in NAMES}, sort_keys=True) for m in ms)
        okP = all(J['ST'][str(m)][T]['pdef']['side'] == ST[m][T]['pdef']['side'] and (J['ST'][str(m)][T]['pdef']['off'] == 0) == (ST[m][T]['pdef']['off'] == 0) for m in ms for T in NAMES)
        okL = all(J['LEN'][str(m)][s] == LEN[m][s] for m in LEN for s in NAMES)
        okV = all(J['VERT'][str(m)][s] == VERT[m][s] for m in LEN for s in NAMES)
        print(f'comparison with hierarchy/combin_8.json (JavaScript, floating point): C {okC}, parent A {okP}, side lengths {okL}, vertex positions {okV}')
        if not (okC and okP and okL and okV): problems.append('differs from combin_8.json')
    else:
        print('hierarchy/combin_8.json not found: comparison skipped')
    json.dump({'ST': {str(m): ST[m] for m in ST}, 'LEN': {str(m): LEN[m] for m in LEN}, 'DEF': {str(m): DEF[m] for m in DEF},
               'VERT': {str(m): VERT[m] for m in VERT}}, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'exact_C.json'), 'w'))
    # 5. nest
    if nest:
        run_nest(lev, trs_all, nest, nestL)
    print(f'total {time.time() - t0:.1f} s')
    print('EXACT: ALL CHECKS PASS' if not problems else 'EXACT: PROBLEMS ' + '; '.join(problems))
    sys.exit(1 if problems else 0)

def tile_placements(kind, level, g, trs_all):
    if level == 0:
        return [g, icompose(g, MYSTIC2)] if kind == 'Gamma' else [g]
    out = []
    for i, s in enumerate(SR[kind]):
        if s: out += tile_placements(s, level - 1, icompose(g, trs_all[level - 1][i]), trs_all)
    return out

def edge_index_parity(trs_all, L):
    """In every supertile of level L, every edge shared by two tiles is edge e_i of one and e_j of the other with
    i + j odd, traversed in opposite directions (so the crossing points at 0.5 + 0.15(-1)^i from v_i coincide), and
    every tile is a rotation + translation of Tile(1,1) composed with the frame's reflection parity."""
    bad = 0; shared = 0; dets = set()
    for T in NAMES:
        gs = tile_placements(T, L, ID, trs_all)
        dets |= {idet(g) for g in gs}
        edges = {}
        for t, g in enumerate(gs):
            V = [iapply(g, v) for v in PTS]
            for i in range(14):
                p, q = V[i], V[(i + 1) % 14]
                edges.setdefault((min(p, q), max(p, q)), []).append((t, i, p, q))
        for lst in edges.values():
            if len(lst) == 2:
                shared += 1
                (t1, i, p1, q1), (t2, j, p2, q2) = lst
                if (i + j) % 2 != 1 or not (p1 == q2 and q1 == p2): bad += 1
            elif len(lst) > 2: bad += 1
    return shared, bad, dets

def run_nest(lev, trs_all, bases, topL):
    """Exact strand following through the nest: N_b = level-b Delta; N_{k+1} = Delta composition with child 1 = N_k.
    Every arc of N_b gets a label; count the arcs of N_k carrying labels of N_b (= number of strands of N_k that the
    pieces of N_b lie on) and check that no label falls into a closed strand."""
    for b in bases:
        nb = lev[b]['Delta']
        lab = [-1] * (2 * nb.E); n = 0
        for p in range(2 * nb.E):
            if lab[p] < 0: lab[p] = n; lab[nb.pair[p]] = n; n += 1
        parent_uf = list(range(n))
        def find(x):
            while parent_uf[x] != x: parent_uf[x] = parent_uf[parent_uf[x]]; x = parent_uf[x]
            return x
        cur = nb; curlab = lab; out = []
        for N in range(b + 1, topL + 1):
            trs = trs_all[N - 1]
            kids = [((cur if i == 1 else lev[N - 1][s]), trs[i]) for i, s in enumerate(SR['Delta'])]
            par, info = compose(kids, labels={1: curlab})
            if info['lost']: out.append(f'L{N}: LOST {len(info["lost"])}'); break
            newlab = [-1] * (2 * par.E)
            for P, acc in info['plab'].items():
                acc = list(acc); r = find(acc[0])
                for x in acc[1:]:
                    rx = find(x)
                    if rx != r: parent_uf[rx] = r
                newlab[P] = find(acc[0])
            arcs = set()
            for P in range(2 * par.E):
                if newlab[P] >= 0: arcs.add(min(P, par.pair[P]))
            classes = len({find(x) for x in range(n)})
            out.append(f'L{N}: {len(arcs)} arc{"s" if len(arcs) != 1 else ""} of N_{N} carry the {n} arcs of N_{b} ({classes} class{"es" if classes != 1 else ""})')
            cur, curlab = par, [find(x) if x >= 0 else -1 for x in newlab]
        print(f'nest base {b}: ' + '; '.join(out))

if __name__ == '__main__':
    main()
