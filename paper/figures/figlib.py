"""Shared drawing helpers for the paper's figures.

Geometry comes from the exact implementation in ../code/exact/exact.py (Z[zeta] coordinates, converted to floating
point only for drawing). The ribbon shapes come from the hand-drawn design (data/hand01b_norm.json, a copy of
handdesign/hand01b_norm.json): each of the 14 pieces is a chain of cubic Bezier segments in the tile's frame.
"""
import os, sys, json, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'code', 'exact'))
import exact as X
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
from matplotlib.path import Path
from matplotlib.patches import PathPatch, Polygon, Circle, FancyArrowPatch

plt.rcParams.update({
    'text.usetex': True,
    'text.latex.preamble': r'\usepackage{newpxtext}\usepackage{newpxmath}\usepackage{amsmath}',
    'font.family': 'serif', 'font.size': 9, 'pdf.fonttype': 42,
})
OUT = os.path.join(HERE, '..', 'tex', 'figs')
os.makedirs(OUT, exist_ok=True)

# colours (Okabe-Ito based; the ribbon colours of the project's drawings)
TILE = '#fff3c4'; RIB_FILL = '#a6dcc4'; RIB_EDGE = '#0b6b4e'
OI = {'orange': '#E69F00', 'sky': '#56B4E9', 'green': '#009E73', 'yellow': '#F0E442', 'blue': '#0072B2',
      'vermillion': '#D55E00', 'purple': '#CC79A7', 'black': '#000000', 'charcoal': '#3b3b3b', 'grey': '#999999'}
AMBER = '#E69F00'

DESIGN = json.load(open(os.path.join(HERE, 'data', 'hand01b_norm.json')))

def fpt(z): return X.zfloat(z)
def fapply(g, p):
    """apply an exact isometry g = (k, refl, t) to a float point p."""
    k, r, t = g
    x, y = p
    if r: y = -y
    c, s = math.cos(k * math.pi / 6), math.sin(k * math.pi / 6)
    tx, ty = fpt(t)
    return (c * x - s * y + tx, s * x + c * y + ty)

TILE_PTS = [fpt(p) for p in X.PTS]

def tiles_of(kind, level, g=X.ID, lev=None, trs_all=None):
    """tile placements (isometries) of the level-`level` supertile of `kind` placed by g."""
    if level == 0:
        return [g, X.icompose(g, X.MYSTIC2)] if kind == 'Gamma' else [g]
    out = []
    for i, s in enumerate(X.SR[kind]):
        if s: out += tiles_of(s, level - 1, X.icompose(g, trs_all[level - 1][i]), lev, trs_all)
    return out

def children_of(kind, level, g, trs_all):
    return [(s, X.icompose(g, trs_all[level - 1][i])) for i, s in enumerate(X.SR[kind]) if s]

def rim_float(box, g):
    return [fapply(g, fpt(v)) for v in box.verts]

# ---------------------------------------------------------------- Bezier pieces
def piece_beziers(pidx):
    """list of cubic segments [(P0,P1,P2,P3)] of passage pidx in the tile frame."""
    a = DESIGN['passages'][pidx]['anchors']
    segs = []
    for i in range(len(a) - 1):
        segs.append((tuple(a[i]['p']), tuple(a[i]['h2']), tuple(a[i + 1]['h1']), tuple(a[i + 1]['p'])))
    return segs

def split(seg, t):
    P0, P1, P2, P3 = [complex(*p) for p in seg]
    A = P0 + (P1 - P0) * t; B = P1 + (P2 - P1) * t; C = P2 + (P3 - P2) * t
    D = A + (B - A) * t; E = B + (C - B) * t; F = D + (E - D) * t
    c = lambda z: (z.real, z.imag)
    return (c(P0), c(A), c(D), c(F)), (c(F), c(E), c(C), c(P3))

def seglen(seg, n=24):
    P = [complex(*p) for p in seg]; L = 0; prev = P[0]
    for i in range(1, n + 1):
        t = i / n; z = (1 - t) ** 3 * P[0] + 3 * (1 - t) ** 2 * t * P[1] + 3 * (1 - t) * t * t * P[2] + t ** 3 * P[3]
        L += abs(z - prev); prev = z
    return L

def sub_from_start(seg, length):
    t = min(1.0, length / max(seglen(seg), 1e-9)); return split(seg, t)[0]
def sub_from_end(seg, length):
    t = max(0.0, 1 - length / max(seglen(seg), 1e-9)); return split(seg, t)[1]

def path_of(segs, g):
    verts = []; codes = []
    for i, s in enumerate(segs):
        pts = [fapply(g, p) for p in s]
        if i == 0: verts.append(pts[0]); codes.append(Path.MOVETO)
        verts += pts[1:]; codes += [Path.CURVE4] * 3
    return Path(verts, codes)

class Ribbons:
    """draw ribbon pieces with a given width (data units) as stroked paths; widths converted to points."""
    def __init__(self, ax, scale_pt_per_unit, width=0.10, border=0.044):
        self.ax = ax; self.s = scale_pt_per_unit; self.w = width; self.b = border
    def stroke(self, path, fill=RIB_FILL, edge=RIB_EDGE, z=3, ext=0.0, clip=None):
        for lw, c, zz in (((self.w + 2 * self.b) * self.s, edge, z), ((self.w + 2 * ext) * self.s, fill, z + 0.01)):
            pp = self.ax.add_patch(PathPatch(path, fill=False, lw=lw, edgecolor=c, capstyle='butt', joinstyle='round', zorder=zz))
            if clip is not None: pp.set_clip_path(clip)

def _straight(a, b):
    return (a, (a[0] + (b[0] - a[0]) / 3, a[1] + (b[1] - a[1]) / 3), (a[0] + 2 * (b[0] - a[0]) / 3, a[1] + 2 * (b[1] - a[1]) / 3), b)

def _past(p, q, d):
    """the point d beyond p, on the line from q through p"""
    dx, dy = p[0] - q[0], p[1] - q[1]; n = math.hypot(dx, dy) or 1.0
    return (p[0] + d * dx / n, p[1] + d * dy / n)

def _extend(segs, d, start=True, end=True):
    """run the piece straight on past its ports by d (the part outside the tile is then clipped away)"""
    segs = list(segs)
    if d and start: segs.insert(0, _straight(_past(segs[0][0], segs[0][1], d), segs[0][0]))
    if d and end: segs.append(_straight(segs[-1][3], _past(segs[-1][3], segs[-1][2], d)))
    return segs

def rim_tiles(gs, rim):
    """indices of the tiles placed by gs that have a vertex on the polygon rim"""
    key = lambda p: (round(p[0], 3), round(p[1], 3))
    rimk = {key(p) for p in rim}
    return {t for t, g in enumerate(gs) if any(key(fapply(g, p)) in rimk for p in TILE_PTS)}

def mask_outside(ax, rim, z=5.9):
    """white out everything outside the polygon rim (ribbons run on past the rim ports end exactly on it)"""
    (x0, x1), (y0, y1) = ax.get_xlim(), ax.get_ylim()
    box = [(x0, y0), (x1, y0), (x1, y1), (x0, y1), (x0, y0)]
    area = sum(rim[i][0] * rim[(i + 1) % len(rim)][1] - rim[(i + 1) % len(rim)][0] * rim[i][1] for i in range(len(rim)))
    hole = list(rim[::-1]) if area > 0 else list(rim)
    codes = [Path.MOVETO] + [Path.LINETO] * 3 + [Path.CLOSEPOLY] + [Path.MOVETO] + [Path.LINETO] * (len(hole) - 1) + [Path.CLOSEPOLY]
    ax.add_patch(PathPatch(Path(box + hole + [hole[0]], codes), fc='white', ec='none', zorder=z))

def draw_tile_ribbons(rb, g, colours=None, z=3, over=True, ext=0.0, clip=None):
    """draw the 14 pieces of one tile placed by g. colours: optional list of 14 (fill, edge) pairs.
    Over/under: full pieces first, then the 'over' ends (0.2 long) and the 'over' half of the inner crossing on top.
    ext, clip: run the pieces on past the ports by ext and clip them to the patch clip, so that the ribbons end
    exactly on the outline (a butt end at a port is square to the ribbon, not to the edge)."""
    P = DESIGN['passages']
    for i in range(len(P)):
        f, e = colours[i] if colours else (RIB_FILL, RIB_EDGE)
        rb.stroke(path_of(_extend(piece_beziers(i), ext), g), f, e, z, clip=clip)
    if not over: return
    for i, p in enumerate(P):
        f, e = colours[i] if colours else (RIB_FILL, RIB_EDGE)
        segs = piece_beziers(i)
        if p['over'][0]: rb.stroke(path_of(_extend([sub_from_start(segs[0], 0.2)], ext, end=False), g), f, e, z + 0.5, ext=0.012, clip=clip)
        if p['over'][1]: rb.stroke(path_of(_extend([sub_from_end(segs[-1], 0.2)], ext, start=False), g), f, e, z + 0.5, ext=0.012, clip=clip)
        if p.get('x0over'):
            x0 = p['x0']
            rb.stroke(path_of([sub_from_end(segs[x0 - 1], 0.2), sub_from_start(segs[x0], 0.2)], g), f, e, z + 0.6, ext=0.012, clip=clip)

def new_fig(w_in, h_in):
    fig = plt.figure(figsize=(w_in, h_in))
    ax = fig.add_axes([0, 0, 1, 1]); ax.set_aspect('equal'); ax.axis('off')
    return fig, ax

def fit(ax, fig, xs, ys, pad=0.05):
    """set limits to the bounding box with padding; return points per data unit."""
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    dx, dy = x1 - x0, y1 - y0; px, py = dx * pad + 0.2, dy * pad + 0.2
    x0 -= px; x1 += px; y0 -= py; y1 += py
    W, H = fig.get_size_inches()
    # keep aspect: expand the shorter range
    sx = W / (x1 - x0); sy = H / (y1 - y0); s = min(sx, sy)
    cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
    ax.set_xlim(cx - W / s / 2, cx + W / s / 2); ax.set_ylim(cy - H / s / 2, cy + H / s / 2)
    return s * 72.0

def save(fig, name):
    fig.savefig(os.path.join(OUT, name + '.pdf'))
    plt.close(fig)
    print('wrote figs/' + name + '.pdf')

# ---------------------------------------------------------------- strands in a finite patch (for colouring)
def ekey(p, q): return (p, q) if p < q else (q, p)
def patch_strands(tile_gs):
    """union-find over (tile, piece): pieces joined across shared tile edges by the edge rule.
    Piece i of the design joins ports given by tile.js's pairing; we use the combinatorial pairing directly:
    port (edge e, near endpoint x) of tile t joins port (edge e, near the other endpoint) of the neighbour."""
    # pieces as port pairs, in the R/L notation of the paper: R(v_i) = (e_i near v_i), L(v_i) = (e_{i-1} near v_i)
    piece_ports = []
    for i, p in enumerate(DESIGN['passages']):
        a, b = int(p['from'][1:]), int(p['to'][1:])
        piece_ports.append(None)
    # derive from tile_box(): port 2k = e_k near v_k, 2k+1 = e_k near v_{k+1}
    tb = X.tile_box(); pairs = []
    seen = set()
    for p in range(28):
        if p in seen: continue
        seen.add(p); seen.add(tb.pair[p]); pairs.append((p, tb.pair[p]))
    # map design passage index -> port pair: passage from e_a to e_b; ends: (a, near?) decided by matching
    # the design's piece list order with tile.js: e0-e1 = R(v0)-R(v1) = (0, 2); e0-e13 = L(v1)-L(v0) = (1, 27);
    # e_k - e_{k+1} = L(v_{k+1})-R(v_{k+1}) = (2k+1, 2k+2)
    pmap = {}
    for i, p in enumerate(DESIGN['passages']):
        a, b = int(p['from'][1:]), int(p['to'][1:])
        if (a, b) == (0, 1): pmap[i] = (0, 2)
        elif (a, b) == (0, 13): pmap[i] = (1, 27)
        else: pmap[i] = (2 * a + 1, 2 * b)
    port_piece = {}
    for i, (u, v) in pmap.items(): port_piece[u] = i; port_piece[v] = i
    assert sorted(port_piece) == list(range(28))
    for u, v in pairs: assert port_piece[u] == port_piece[v]
    n = len(tile_gs); par = list(range(14 * n))
    def find(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    edges = {}
    V = []
    for t, g in enumerate(tile_gs):
        vs = [X.iapply(g, v) for v in X.PTS]; V.append(vs)
        for k in range(14): edges.setdefault(ekey(vs[k], vs[(k + 1) % 14]), []).append((t, k))
    for key, lst in edges.items():
        if len(lst) != 2: continue
        (t1, k1), (t2, k2) = lst
        for s in (0, 1):
            x = V[t1][(k1 + s) % 14]
            s2 = 0 if V[t2][k2] == x else 1
            p1 = 2 * k1 + s; p2 = 2 * k2 + (1 - s2)
            a, b = find(14 * t1 + port_piece[p1]), find(14 * t2 + port_piece[p2])
            if a != b: par[a] = b
    return [find(x) for x in range(14 * n)], pmap
