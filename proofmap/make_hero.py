#!/usr/bin/env python3
"""Draw proofmap/hero.svg, the fine-line drawing beside the overview's title: the block N_2 of the nest (71 tiles, in
hairlines) with every ribbon piece drawn as a band in thin outline, over and under as in the paper's Figure 1; the
blocks N_1 (dashed) and N_0 inside it, and the two strands that carry the pieces of N_0 tinted. No strand closes:
each runs out to the rim (Theorem A for this block), where the drawing cuts it off.

    python3 proofmap/make_hero.py      # by hand, after a change to the geometry or the design; build.py embeds the file

The geometry and the ribbons are the paper's (paper/figures/figlib.py, on paper/code/exact/exact.py), so the drawing
is the same tiling and the same knot as the paper's figures, turned a quarter turn (a rotation, so the tiles keep their
handedness) to fit beside the title. The site shows it as an image (out/site/hero.svg), so its colours are its own: the
proof site's, and the gaps that make the crossings are the page's background, #f8f9f7.
"""
import math
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'paper' / 'figures'))
import figlib as F  # noqa: E402

X = F.X
TOP = 2
OUT = pathlib.Path(__file__).resolve().parent / 'hero.svg'
W = 400                     # width of the drawing's coordinates, in px of the page at its natural size
OVER = 0.2                  # the length of the over-end drawn again on top (figlib.draw_tile_ribbons)
ROT = 90                    # degrees, counter-clockwise
STYLE = ('path,use{fill:none;stroke-linejoin:round}'
         '.kh-tiles{stroke:#dbe2de;stroke-width:.5px}.kh-n0{fill:#e3eee8}'
         '.kh-ink{stroke:#8a968f;stroke-width:2.8px}.kh-gap{stroke:#f8f9f7;stroke-width:1.8px}'
         '.kh-inkt{stroke:#2f7a5b;stroke-width:2.8px}.kh-tint{stroke:#c9e6d7;stroke-width:1.8px}'
         '.kh-b1{stroke:#4d5b55;stroke-width:.8px;stroke-dasharray:3 2}.kh-b2{stroke:#4d5b55;stroke-width:.9px}')


def nest_g(b, top, trs):
    """Where N_b sits in N_top's frame: child 1 at every level (paper/figures/make_figs.py)."""
    g = X.ID
    for n in range(top, b, -1):
        g = X.icompose(g, trs[n - 1][1])
    return g


def main():
    lev, trs = X.build(TOP)
    frame = X.REFL if TOP % 2 else X.ID      # true handedness, as in the paper's figures
    gs = F.tiles_of('Delta', TOP, frame, lev, trs)
    root, _ = F.patch_strands(gs)
    g0 = X.icompose(frame, nest_g(0, TOP, trs))
    t0 = gs.index(g0)
    tinted = {root[14 * t0 + i] for i in range(14)}

    owners = {}
    for t, g in enumerate(gs):
        vs = [X.iapply(g, v) for v in X.PTS]
        for k in range(14):
            owners.setdefault(F.ekey(vs[k], vs[(k + 1) % 14]), []).append((t, k))

    rims = {b: F.rim_float(lev[b]['Delta'], X.icompose(frame, nest_g(b, TOP, trs))) for b in range(1, TOP + 1)}
    rims[0] = [F.fapply(g0, p) for p in F.TILE_PTS]
    c, sn = math.cos(math.radians(ROT)), math.sin(math.radians(ROT))

    def turn(p):
        return (c * p[0] - sn * p[1], sn * p[0] + c * p[1])

    xs = [turn(p)[0] for p in rims[TOP]]
    ys = [turn(p)[1] for p in rims[TOP]]
    pad = 0.4
    x0, x1, y0, y1 = min(xs) - pad, max(xs) + pad, min(ys) - pad, max(ys) + pad
    s = W / (x1 - x0)
    H = (y1 - y0) * s

    def f(v):
        return ('%.1f' % v).rstrip('0').rstrip('.')

    def pt(p):
        q = turn(p)
        return f((q[0] - x0) * s) + ' ' + f((y1 - q[1]) * s)

    def poly(pts):
        return 'M' + 'L'.join(pt(p) for p in pts) + 'Z'

    def bez(segs, g):
        out = 'M' + pt(F.fapply(g, segs[0][0]))
        for seg in segs:
            out += 'C' + ' '.join(pt(F.fapply(g, q)) for q in seg[1:])
        return out

    tiles = ''.join('M%sL%s' % (pt(X.zfloat(a)), pt(X.zfloat(b))) for (a, b) in owners)
    plain, tint, over_plain, over_tint = [], [], [], []
    for t, g in enumerate(gs):
        vs = [X.iapply(g, v) for v in X.PTS]
        edge_tile = any(len(owners[F.ekey(vs[k], vs[(k + 1) % 14])]) == 1 for k in range(14))
        for i, p in enumerate(F.DESIGN['passages']):
            segs = F.piece_beziers(i)
            body, over = (tint, over_tint) if root[14 * t + i] in tinted else (plain, over_plain)
            body.append(bez(F._extend(segs, 0.3) if edge_tile else segs, g))   # run on past the rim; the clip cuts it
            if p['over'][0]:
                over.append(bez([F.sub_from_start(segs[0], OVER)], g))
            if p['over'][1]:
                over.append(bez([F.sub_from_end(segs[-1], OVER)], g))
            if p.get('x0over'):
                x = p['x0']
                over.append(bez([F.sub_from_end(segs[x - 1], OVER), F.sub_from_start(segs[x], OVER)], g))

    paths = {'pp': plain, 'pt': tint, 'op': over_plain, 'ot': over_tint}
    defs = ''.join('<path id="kh-%s" vector-effect="non-scaling-stroke" d="%s"/>' % (k, ''.join(v))
                   for k, v in paths.items())

    def band(k, inner):
        ink = 'kh-inkt' if inner == 'kh-tint' else 'kh-ink'
        return '<use href="#kh-%s" class="%s"/><use href="#kh-%s" class="%s"/>' % (k, ink, k, inner)

    svg = ('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 %s %s" role="img" aria-labelledby="kh-t">'
           '<title id="kh-t">The block N2 of the nest tiling, 71 tiles, with every ribbon piece drawn in thin outline, '
           'over and under. The blocks N1 and N0 sit inside it, and the two strands through the first tile, N0, are '
           'tinted. No strand closes: each one runs out to the edge of the block.</title>'
           '<style>%s</style>'
           '<defs><clipPath id="kh-clip"><path d="%s"/></clipPath>%s</defs>'
           '<path class="kh-tiles" vector-effect="non-scaling-stroke" d="%s"/>'
           '<path class="kh-n0" d="%s"/>'
           '<g clip-path="url(#kh-clip)">%s%s%s%s</g>'
           '<path class="kh-b1" vector-effect="non-scaling-stroke" d="%s"/>'
           '<path class="kh-b2" vector-effect="non-scaling-stroke" d="%s"/>'
           '</svg>' % (f(W), f(H), STYLE, poly(rims[TOP]), defs, tiles, poly(rims[0]),
                       band('pp', 'kh-gap'), band('pt', 'kh-tint'), band('op', 'kh-gap'), band('ot', 'kh-tint'),
                       poly(rims[1]), poly(rims[TOP])))
    OUT.write_text(svg + '\n', encoding='utf-8')
    n_tint = sum(1 for t in range(len(gs)) for i in range(14) if root[14 * t + i] in tinted)
    print('wrote %s: %d tiles, %d strands through N_0 (%d pieces), %d bytes'
          % (OUT.name, len(gs), len(tinted), n_tint, len(svg)))


if __name__ == '__main__':
    main()
