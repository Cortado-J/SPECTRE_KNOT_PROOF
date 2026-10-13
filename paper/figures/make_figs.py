#!/usr/bin/env python3
"""Make the paper's figures (vector PDF in ../tex/figs/). usage: python3 make_figs.py [names...]"""
import sys, math
from figlib import *
from figlib import _extend

LEV, TRS = X.build(6)

def top_frame(level):
    """display frame for a level-`level` supertile in its own frame: reflect odd levels so that the tiles appear
    with their true handedness (the code's own frames are mirrored at odd levels)."""
    return X.REFL if level % 2 else X.ID

def nest_g(b, top):
    """placement of N_b inside N_top's own frame (child 1 at every level)."""
    g = X.ID
    for N in range(top, b, -1): g = X.icompose(g, TRS[N - 1][1])
    return g

def draw_tiles(ax, gs, lw=0.35, fc=TILE, ec='black', z=1):
    for g in gs:
        P = [fapply(g, p) for p in TILE_PTS]
        ax.add_patch(Polygon(P, closed=True, fc=fc, ec=ec, lw=lw, joinstyle='miter', zorder=z))

# ---------------------------------------------------------------- Figure 5: the decoration on the true geometry
def fig_tileports():
    fig, ax = new_fig(3.9, 3.0)
    s = fit(ax, fig, [p[0] for p in TILE_PTS], [p[1] for p in TILE_PTS], pad=0.06)
    ax.add_patch(Polygon(TILE_PTS, closed=True, fc=TILE, ec='black', lw=1.0, joinstyle='miter', zorder=1))
    P = DESIGN['passages']
    col = {0: OI['vermillion'], 1: OI['blue']}
    for i in range(len(P)):
        ax.add_patch(PathPatch(path_of(piece_beziers(i), X.ID), fill=False, lw=1.5, edgecolor=col.get(i, RIB_EDGE), capstyle='butt', zorder=3))
    ports = {}
    for k in range(14):
        a, b = TILE_PTS[k], TILE_PTS[(k + 1) % 14]; f = 0.5 + 0.15 * (-1) ** k
        q = (a[0] + f * (b[0] - a[0]), a[1] + f * (b[1] - a[1])); ports[k] = q
        ax.plot([q[0]], [q[1]], 'o', ms=3.2, color='black', zorder=5)
    # vertex labels, outside the tile (outward bisector of the two edge normals; the polygon is counter-clockwise)
    for k, v in enumerate(TILE_PTS):
        a, b = TILE_PTS[k - 1], TILE_PTS[(k + 1) % 14]
        n1 = (v[1] - a[1], -(v[0] - a[0])); n2 = (b[1] - v[1], -(b[0] - v[0]))
        d = (n1[0] + n2[0], n1[1] + n2[1]); L = math.hypot(*d); d = (d[0] / L, d[1] / L)
        ax.text(v[0] + 0.2 * d[0], v[1] + 0.2 * d[1], r'$v_{%d}$' % k, ha='center', va='center', fontsize=8.5, zorder=6)
    # the ports round the crossover corners: each label sits beside the ribbon end it names
    lab = [((0.27, 0.16), r'$\mathrm{R}(v_0)$', OI['vermillion']), ((0.95, 0.11), r'$\mathrm{L}(v_1)$', OI['blue']),
           ((0.97, -0.43), r'$\mathrm{R}(v_1)$', OI['vermillion']), ((1.48, -0.17), r'$\mathrm{L}(v_2)$', RIB_EDGE),
           ((0.22, 0.40), r'$\mathrm{L}(v_0)$', OI['blue']), ((0.30, 0.76), r'$\mathrm{R}(v_{13})$', RIB_EDGE)]
    for (x, y), t, c in lab:
        ax.text(x, y, t, ha='center', va='center', fontsize=6.5, color=c, zorder=6)
    save(fig, 'tileports')

# ---------------------------------------------------------------- Figure 1: the tile and a supertile with a long strand
def fig_intro():
    # (a) the tile, labelled
    fig, ax = new_fig(2.3, 2.3)
    xs = [p[0] for p in TILE_PTS]; ys = [p[1] for p in TILE_PTS]
    s = fit(ax, fig, xs, ys, pad=0.12)
    draw_tiles(ax, [X.ID], lw=0.8)
    clip = ax.add_patch(Polygon(TILE_PTS, closed=True, fill=False, lw=0))
    rb = Ribbons(ax, s); draw_tile_ribbons(rb, X.ID, ext=0.3, clip=clip)
    ax.add_patch(Polygon(TILE_PTS, closed=True, fill=False, ec='black', lw=0.8, joinstyle='miter', zorder=6))
    save(fig, 'tile_ribbons')
    # (b) N_3 with the strand(s) through N_0 highlighted
    top = 3
    G = top_frame(top)
    gs = tiles_of('Delta', top, G, LEV, TRS)
    root, pmap = patch_strands(gs)
    g0 = X.icompose(G, nest_g(0, top))
    t0 = [i for i, g in enumerate(gs) if g == g0]
    assert len(t0) == 1; t0 = t0[0]
    hl = {root[14 * t0 + i] for i in range(14)}
    fig, ax = new_fig(3.4, 3.4)
    allp = [fapply(g, p) for g in gs for p in TILE_PTS]
    s = fit(ax, fig, [p[0] for p in allp], [p[1] for p in allp], pad=0.02)
    draw_tiles(ax, gs, lw=0.25)
    ax.add_patch(Polygon([fapply(g0, p) for p in TILE_PTS], closed=True, fc='#f2d36b', ec='black', lw=0.6, zorder=1.5))
    rim = rim_float(LEV[top]['Delta'], G)
    edge_t = rim_tiles(gs, rim)   # only these need their ribbons run on past the ports (the mask below cuts them off)
    rb = Ribbons(ax, s)
    for t, g in enumerate(gs):
        cols = [((AMBER, '#7a4a00') if root[14 * t + i] in hl else (RIB_FILL, RIB_EDGE)) for i in range(14)]
        draw_tile_ribbons(rb, g, cols, z=3, ext=0.3 if t in edge_t else 0.0)
    # redraw highlighted on top for visibility
    for t, g in enumerate(gs):
        for i in range(14):
            if root[14 * t + i] in hl:
                rb.stroke(path_of(_extend(piece_beziers(i), 0.3 if t in edge_t else 0.0), g), AMBER, '#7a4a00', 5)
    mask_outside(ax, rim)
    ax.add_patch(Polygon(rim, closed=True, fill=False, ec='black', lw=1.0, zorder=6))
    save(fig, 'intro_N3')
    print('  strands through N_0 in N_3:', len(hl), '; tiles', len(gs), '; on the rim', len(edge_t))


import json as _json
CJ = _json.load(open(os.path.join(HERE, '..', 'code', 'hierarchy', 'combin_8.json')))
GREEK = {'Gamma': r'\Gamma', 'Delta': r'\Delta', 'Theta': r'\Theta', 'Lambda': r'\Lambda', 'Xi': r'\Xi', 'Pi': r'\Pi',
         'Sigma': r'\Sigma', 'Phi': r'\Phi', 'Psi': r'\Psi'}

def signed_area(P):
    return sum(P[i][0] * P[(i + 1) % len(P)][1] - P[(i + 1) % len(P)][0] * P[i][1] for i in range(len(P))) / 2

def rim_label_pos(P, i0, i1, off):
    """point at the middle (by arc length) of rim polyline P[i0..i1] (cyclic), pushed outward by off."""
    n = len(P); idx = [(i0 + t) % n for t in range(((i1 - i0) % n) + 1)]
    segs = [(P[idx[t]], P[idx[t + 1]]) for t in range(len(idx) - 1)]
    L = sum(math.dist(a, b) for a, b in segs); h = L / 2
    for a, b in segs:
        d = math.dist(a, b)
        if h <= d:
            t = h / d; x = a[0] + t * (b[0] - a[0]); y = a[1] + t * (b[1] - a[1])
            nx, ny = (b[1] - a[1]) / d, -(b[0] - a[0]) / d   # right normal
            if signed_area(P) < 0: nx, ny = -nx, -ny          # outward for cw traversal is the left normal
            return x + off * nx, y + off * ny
        h -= d
    return P[i0]

# ---------------------------------------------------------------- the nine level-1 supertiles
def fig_level1():
    fig = plt.figure(figsize=(6.3, 6.6))
    order = X.NAMES
    for n, K in enumerate(order):
        ax = fig.add_axes([(n % 3) / 3, 1 - (n // 3 + 1) / 3, 1 / 3, 1 / 3]); ax.set_aspect('equal'); ax.axis('off')
        G = top_frame(1)
        gs = tiles_of(K, 1, G, LEV, TRS)
        box = LEV[1][K]; P = rim_float(box, G); E = box.E
        allp = [fapply(g, p) for g in gs for p in TILE_PTS]
        ax.set_xlim(min(p[0] for p in allp) - 1.6, max(p[0] for p in allp) + 1.6)
        ax.set_ylim(min(p[1] for p in allp) - 1.6, max(p[1] for p in allp) + 1.6)
        # Mystic tiles: the Gamma child's two tiles (the last child)
        kids = children_of(K, 1, G, TRS); myst = kids[-1][1]
        mt = {myst, X.icompose(myst, X.MYSTIC2)}
        for g in gs:
            Q = [fapply(g, p) for p in TILE_PTS]
            ax.add_patch(Polygon(Q, closed=True, fc=('#f6dd8a' if g in mt else TILE), ec='#555555', lw=0.4, zorder=1))
        ax.add_patch(Polygon(P, closed=True, fill=False, ec='black', lw=1.1, zorder=2))
        V = [(box.defA + p) % E for p in CJ['VERT']['1'][K]]
        for j in range(6):
            x, y = P[V[j]]; ax.plot([x], [y], 'o', ms=3.2, color='black', zorder=4)
            lx, ly = rim_label_pos(P, V[j], V[(j + 1) % 6], 0.75)
            ax.text(lx, ly, r'$%d$' % j, ha='center', va='center', fontsize=7.5, color=OI['blue'], zorder=5)
        a = P[box.defA]; b = P[box.defB]
        ax.plot([a[0]], [a[1]], 'o', ms=5, mfc='white', mec=OI['vermillion'], mew=1.4, zorder=6)
        ax.plot([b[0]], [b[1]], 's', ms=3.2, mfc=OI['vermillion'], mec=OI['vermillion'], zorder=6)
        # child numbers (Table 1): at the centroid of each child's tile(s)
        for c, (kk, g) in enumerate(kids):
            ts = [g, X.icompose(g, X.MYSTIC2)] if kk == 'Gamma' else [g]
            Q = [fapply(t, p) for t in ts for p in TILE_PTS]
            ax.text(sum(q[0] for q in Q) / len(Q), sum(q[1] for q in Q) / len(Q), r'$%d$' % c, ha='center', va='center',
                    fontsize=7, color='#555555', zorder=7)
        ax.text(0.04, 0.96, '$%s$' % GREEK[K], transform=ax.transAxes, ha='left', va='top', fontsize=12, zorder=7)
    save(fig, 'level1')

# ---------------------------------------------------------------- the composition pattern (Fig. 5.1 layout)
POS = {'TL': (3, 0), 'TR': (5, 0), 'G': (2, 3), 'S': (4, 3), 'L': (1, 6), 'D': (3, 6), 'R': (5, 6), 'B': (4, 9)}
NB = [(2, 0), (1, -3), (-1, -3), (-2, 0), (-1, 3), (1, 3)]
SLOT8 = ['L', 'D', 'B', 'R', 'S', 'TR', 'TL', 'G']
SLOT7 = ['L', 'D', 'R', 'S', 'TR', 'TL', 'G']
def hex_layout(T):
    st = CJ['ST']['1'][T]; slots = SLOT7 if T == 'Gamma' else SLOT8
    n = len(st['kids']); P = {c: POS[slots[c]] for c in range(n)}
    at = {P[c]: c for c in range(n)}
    def dir_to(c, c2):
        dx, dy = P[c2][0] - P[c][0], P[c2][1] - P[c][1]
        return NB.index((dx, dy))
    # per child: d(c, j) = d0 + s*j
    sides = [[None if x == 'R' else tuple(map(int, x.split('.'))) for x in ss] for ss in st['sides']]
    S = None; D0 = {}
    for c in range(n):
        known = [(j, dir_to(c, sides[c][j][0])) for j in range(6) if sides[c][j]]
        for s in (1, -1):
            d0s = {(d - s * j) % 6 for j, d in known}
            if len(d0s) == 1 and (len(known) > 1):
                S = s if S is None else S
    for c in range(n):
        known = [(j, dir_to(c, sides[c][j][0])) for j in range(6) if sides[c][j]]
        d0s = {(d - S * j) % 6 for j, d in known}; assert len(d0s) == 1, (T, c, known)
        D0[c] = d0s.pop()
    return st, P, S, D0, sides

def hexpt(cx, cy, ang, R=1.0):
    # page units -> plot coords (y up)
    X0 = cx * math.sqrt(3) / 2 * R; Y0 = -cy * R / 2
    return (X0 + R * math.cos(math.radians(ang)), Y0 - R * math.sin(math.radians(ang)))
def hexcentre(cx, cy, R=1.0): return (cx * math.sqrt(3) / 2 * R, -cy * R / 2)

def draw_pattern(ax, T, show_kinds=True):
    st, P, S, D0, sides = hex_layout(T)
    n = len(st['kids'])
    def dcj(c, j): return (D0[c] + S * j) % 6
    def edge_angles(d): return (-60 * d - 30, -60 * d + 30)
    def vertex_angle(c, i):   # child vertex i: between own sides i-1 and i
        a = set(x % 360 for x in edge_angles(dcj(c, i - 1))); b = set(x % 360 for x in edge_angles(dcj(c, i)))
        return (a & b).pop()
    for c in range(n):
        cx, cy = P[c]
        poly = [hexpt(cx, cy, -60 * d - 30) for d in range(6)]
        K = st['kids'][c]
        fc = '#f6dd8a' if K == 'Gamma' else ('#cfe8f7' if c == 1 else TILE)
        ax.add_patch(Polygon(poly, closed=True, fc=fc, ec='#444444', lw=0.6, zorder=1))
        x0, y0 = hexcentre(cx, cy)
        if show_kinds:
            ax.text(x0, y0 + 0.08, '$%s$' % GREEK[K], ha='center', va='center', fontsize=11, zorder=3)
            ax.text(x0, y0 - 0.33, r'\scriptsize $%d$' % c, ha='center', va='center', color='#555555', zorder=3)
        for j in range(6):
            d = dcj(c, j); ang = -60 * d
            lx, ly = x0 + 0.66 * math.cos(math.radians(ang)), y0 - 0.66 * math.sin(math.radians(ang)) * -1 * -1
            lx, ly = x0 + 0.68 * math.cos(math.radians(ang)), y0 - 0.68 * math.sin(math.radians(ang))
            ax.text(lx, ly, r'\tiny $%d$' % j, ha='center', va='center', color=OI['blue'], zorder=3)
    # parent rim: thick; parent vertices: start of each parent side = child vertex (j+1) of its first piece
    for c in range(n):
        cx, cy = P[c]
        for j in range(6):
            if sides[c][j] is None:
                d = dcj(c, j); a1, a2 = edge_angles(d)
                p1, p2 = hexpt(cx, cy, a1), hexpt(cx, cy, a2)
                ax.plot([p1[0], p2[0]], [p1[1], p2[1]], color='black', lw=1.6, solid_capstyle='round', zorder=4)
    pv = []
    for J in range(6):
        c, j = map(int, st['pside'][J][0].split('.'))
        ang = vertex_angle(c, j + 1); x, y = hexpt(*P[c], ang); pv.append((x, y))
        ax.plot([x], [y], 'o', ms=4.5, color='black', zorder=5)
    # parent side labels: next to the middle piece of each side, outside
    allc = [hexcentre(*P[c]) for c in range(n)]; gx = sum(p[0] for p in allc) / n; gy = sum(p[1] for p in allc) / n
    for J in range(6):
        seq = st['pside'][J]; c, j = map(int, seq[len(seq) // 2].split('.'))
        d = dcj(c, j); a1, a2 = edge_angles(d); p1, p2 = hexpt(*P[c], a1), hexpt(*P[c], a2)
        mx, my = (p1[0] + p2[0]) / 2, (p1[1] + p2[1]) / 2
        vx, vy = mx - hexcentre(*P[c])[0], my - hexcentre(*P[c])[1]; L = math.hypot(vx, vy)
        ax.text(mx + 0.42 * vx / L, my + 0.42 * vy / L, r'\textbf{%d}' % J, ha='center', va='center', fontsize=8, color=OI['vermillion'], zorder=6)
    # parent A = Gamma child's vertex 0
    g = n - 1; ang = vertex_angle(g, 0); x, y = hexpt(*P[g], ang)
    ax.plot([x], [y], 'o', ms=7, mfc='none', mec=OI['vermillion'], mew=1.3, zorder=6)
    return P

def fig_pattern():
    fig = plt.figure(figsize=(6.0, 3.6))
    for n, T in enumerate(['Delta', 'Gamma']):
        ax = fig.add_axes([n * 0.5, 0, 0.5, 1]); ax.set_aspect('equal'); ax.axis('off')
        P = draw_pattern(ax, T)
        ax.set_xlim(-0.2, 6.2 * math.sqrt(3) / 2 + 0.2); ax.set_ylim(-11 / 2 - 0.3, 1.6)
        ax.text(0.1, 1.2, r'$%s$' % GREEK[T], fontsize=13, ha='left', va='center')
    save(fig, 'pattern')


# ---------------------------------------------------------------- marks and runs of the composition 1 -> 2 (Delta)
def fig_skeleton(T='Delta', N=2):
    info, kinds = X.INFO[(N, T)]
    G = top_frame(N)
    kids = [(LEV[N - 1][s], TRS[N - 1][i]) for i, s in enumerate(X.SR[T]) if s]
    mate = info['mate']; cv = info['cv']
    n = len(kids)
    nb = lambda c, k: mate[(c, k % kids[c][0].E)][0] if (c, k % kids[c][0].E) in mate else -1
    marks = set(); defpts = {}
    for c, (b, g) in enumerate(kids):
        E = b.E
        for k in range(E):
            if nb(c, k - 1) != nb(c, k): marks.add(cv[c][k])
        marks.add(cv[c][b.defA]); marks.add(cv[c][b.defB]); defpts[cv[c][b.defA]] = 'A'; defpts.setdefault(cv[c][b.defB], 'B')
    fig, ax = new_fig(4.2, 4.6)
    gs = tiles_of(T, N, G, LEV, TRS)
    allp = [fapply(g, p) for g in gs for p in TILE_PTS]
    s = fit(ax, fig, [p[0] for p in allp], [p[1] for p in allp], pad=0.03)
    draw_tiles(ax, gs, lw=0.25, fc='#fffaf0', ec='#bbbbbb')
    F = lambda z: fapply(G, fpt(z))
    drawn = set(); cnt = {'odd': 0, 'even': 0}
    for c, (b, g) in enumerate(kids):
        E = b.E; mk = [k for k in range(E) if cv[c][k] in marks]
        for i, a in enumerate(mk):
            e = mk[(i + 1) % len(mk)]; L = (e - a) % E or E
            pts = [F(cv[c][(a + t) % E]) for t in range(L + 1)]
            o = nb(c, a)
            if o < 0:
                ax.plot([p[0] for p in pts], [p[1] for p in pts], color='black', lw=1.6, solid_joinstyle='miter', zorder=3)
                continue
            key = frozenset([cv[c][a], cv[c][e % E], c, o])
            if key in drawn: continue
            drawn.add(key)
            col = OI['blue'] if L % 2 else OI['orange']; cnt['odd' if L % 2 else 'even'] += 1
            ax.plot([p[0] for p in pts], [p[1] for p in pts], color=col, lw=2.0, solid_joinstyle='miter', zorder=3)
    for z in marks:
        x, y = F(z)
        if z in defpts:
            ax.plot([x], [y], 'o' if defpts[z] == 'A' else 's', ms=4.2 if defpts[z] == 'A' else 3.4, mfc='white', mec=OI['vermillion'], mew=1.2, zorder=5)
        else:
            ax.plot([x], [y], 'o', ms=2.8, color='black', zorder=5)
    for c, (b, g) in enumerate(kids):
        P = [F(v) for v in cv[c]]; cx = sum(p[0] for p in P) / len(P); cy = sum(p[1] for p in P) / len(P)
        ax.text(cx, cy, r'$%s_{%d}$' % (GREEK[kinds[c]], c), ha='center', va='center', fontsize=10, zorder=6,
                bbox=dict(boxstyle='round,pad=0.15', fc='white', ec='none', alpha=0.8))
    save(fig, 'skeleton')
    print('  marks', len(marks), 'shared runs', cnt)

# ---------------------------------------------------------------- the nest N_1 < N_2 < N_3 < N_4
def fig_nest():
    fig = plt.figure(figsize=(6.3, 3.3))
    for k, top in enumerate((3, 4)):
        G = top_frame(top)
        ax = fig.add_axes([k / 2, 0, 0.5, 1]); ax.set_aspect('equal'); ax.axis('off')
        rims = {}
        for b in range(top - 2, top + 1):
            g = X.icompose(G, nest_g(b, top)); box = LEV[b]['Delta']
            rims[b] = (box, g, [fapply(g, fpt(v)) for v in box.verts])
        P = rims[top][2]
        bb = ax.get_position(); Win, Hin = fig.get_size_inches()[0] * bb.width, fig.get_size_inches()[1] * bb.height
        xs = [p[0] for p in P]; ys = [p[1] for p in P]; pad = 0.03 * (max(xs) - min(xs))
        dx, dy = max(xs) - min(xs) + 2 * pad, max(ys) - min(ys) + 2 * pad
        sc = min(Win / dx, Hin / dy); cx, cy = (max(xs) + min(xs)) / 2, (max(ys) + min(ys)) / 2
        ax.set_xlim(cx - Win / sc / 2, cx + Win / sc / 2); ax.set_ylim(cy - Hin / sc / 2, cy + Hin / sc / 2)
        shade = {top - 2: '#f2d36b', top - 1: '#fbe8b0', top: '#fffaf0'}
        for b in (top, top - 1, top - 2):
            ax.add_patch(Polygon(rims[b][2], closed=True, fc=shade[b], ec='black', lw={top: 1.0, top - 1: 0.8, top - 2: 0.6}[b], zorder=1 + (top - b)))
        def side(b, j):
            box, g, Q = rims[b]; V = [(box.defA + p) % box.E for p in CJ['VERT'][str(b)]['Delta']]
            i0, i1 = V[j], V[(j + 1) % 6]; return [Q[(i0 + t) % box.E] for t in range(((i1 - i0) % box.E) + 1)]
        # blue side 4 of the middle block first and wide; the vermilion sides 2 on top, narrower, so both show
        for b, j, col, lw, z in ((top - 1, 4, OI['sky'], 4.0, 6), (top - 2, 2, OI['vermillion'], 1.8, 7), (top - 1, 2, OI['vermillion'], 1.8, 7)):
            pts = side(b, j); ax.plot([p[0] for p in pts], [p[1] for p in pts], color=col, lw=lw, solid_capstyle='butt', zorder=z)
        ax.text(cx + 0.22 * (max(xs) - min(xs)), cy - 0.32 * (max(ys) - min(ys)), r'$N_{%d}$' % top,
                ha='center', va='center', fontsize=10, zorder=8)
        ax.text(0.02, 0.97, '(a) $b=1$' if top == 3 else '(b) $b=2$', transform=ax.transAxes, ha='left', va='top', fontsize=9)
    save(fig, 'nest')

# ---------------------------------------------------------------- merging: strands through N_0 inside N_1, N_2, N_3
PAL = [OI['orange'], OI['blue'], OI['charcoal'], OI['sky'], OI['green'], OI['purple'], OI['yellow']]   # first five apart under red-green colour blindness
def darker(hexc, f=0.55):
    h = hexc.lstrip('#'); r, g, b = (int(h[i:i + 2], 16) for i in (0, 2, 4))
    return '#%02x%02x%02x' % (int(r * f), int(g * f), int(b * f))
def fig_merge(base=0, tops=(1, 2, 3), name='merge'):
    fig = plt.figure(figsize=(6.3, 2.35))
    n = len(tops)
    for k, top in enumerate(tops):
        G = top_frame(top)
        gs = tiles_of('Delta', top, G, LEV, TRS)
        root, _ = patch_strands(gs)
        gb = X.icompose(G, nest_g(base, top))
        base_gs = tiles_of('Delta', base, gb, LEV, TRS)
        idx = {g: i for i, g in enumerate(gs)}
        strands = []
        for t in [idx[g] for g in base_gs]:
            for i in range(14):
                r = root[14 * t + i]
                if r not in strands: strands.append(r)
        col = {r: PAL[j % len(PAL)] for j, r in enumerate(strands)}
        ax = fig.add_axes([k / n + 0.005, 0.0, 1 / n - 0.01, 0.88]); ax.set_aspect('equal'); ax.axis('off')
        P = rim_float(LEV[top]['Delta'], G)
        xs = [p[0] for p in P]; ys = [p[1] for p in P]
        pad = 0.03 * (max(xs) - min(xs))
        bb = ax.get_position(); Win, Hin = fig.get_size_inches()[0] * bb.width, fig.get_size_inches()[1] * bb.height
        dx, dy = max(xs) - min(xs) + 2 * pad, max(ys) - min(ys) + 2 * pad
        sc = min(Win / dx, Hin / dy); cx, cy = (max(xs) + min(xs)) / 2, (max(ys) + min(ys)) / 2
        ax.set_xlim(cx - Win / sc / 2, cx + Win / sc / 2); ax.set_ylim(cy - Hin / sc / 2, cy + Hin / sc / 2)
        s = sc * 72
        draw_tiles(ax, gs, lw=0.12 if top >= 3 else (0.25 if top == 2 else 0.4))
        prev = rim_float(LEV[top - 1]['Delta'], X.icompose(G, nest_g(top - 1, top)))
        ax.add_patch(Polygon([fapply(gb, p) for p in TILE_PTS] if base == 0 else rim_float(LEV[base]['Delta'], gb), closed=True,
                             fc='#f2d36b', ec='black', lw=0.4, zorder=1.4))
        ax.add_patch(Polygon(prev, closed=True, fill=False, ec='black', lw=0.7, ls=(0, (2, 1.2)), zorder=6))
        rb = Ribbons(ax, s)
        edge_t = rim_tiles(gs, P)   # their ribbons run on past the rim ports and are cut off by the mask
        for t, g in enumerate(gs):
            for i in range(14):
                r = root[14 * t + i]
                segs = _extend(piece_beziers(i), 0.3 if t in edge_t else 0.0)
                if r in col: rb.stroke(path_of(segs, g), col[r], darker(col[r]), 4)
                else: rb.stroke(path_of(segs, g), RIB_FILL, RIB_EDGE, 3)
        mask_outside(ax, P)
        ax.add_patch(Polygon(P, closed=True, fill=False, ec='black', lw=0.9, zorder=6))
        ax.text(0.5, 1.0, r'$N_{%d}$ (%s tiles): %d arc%s' % (top, f'{len(gs):,}', len(strands), '' if len(strands) == 1 else 's'),
                transform=ax.transAxes, ha='center', va='bottom', fontsize=9)
        print(f'  base {base} in N_{top}: {len(strands)} strands')
    save(fig, name)

FIGS = {'intro': fig_intro, 'tileports': fig_tileports, 'level1': fig_level1, 'pattern': fig_pattern, 'skeleton': fig_skeleton, 'nest': fig_nest, 'merge': fig_merge}
if __name__ == '__main__':
    names = sys.argv[1:] or list(FIGS)
    for n in names: FIGS[n]()
