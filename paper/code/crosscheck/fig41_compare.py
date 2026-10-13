#!/usr/bin/env python3
"""Scripted comparison of the level-1 supertiles with Fig. 4.1 of the spectre paper (paper, proof of Prop. 2.4, base
case of the dictionary (*)). Replaces the comparison by eye made with fig41_render.py.

Input: the PDF of Smith, Myers, Kaplan, Goodman-Strauss, "A chiral aperiodic monotile", Combinatorial Theory 4(2)
(2024) #13 (not included here; SHA-256 below). Page 13 is rendered at 300 dpi with pdftoppm.
For each of the nine marked clusters:
  1. the six marked vertex dots are found automatically (dark blobs that survive an opening with a disc of radius 6 px);
  2. our level-1 supertile of that kind is drawn as a cluster of hats and turtles (as in fig41_render.py: code frame,
     edges in odd directions lengthened to sqrt 3) and its six vertices are fitted to the six dots by a similarity
     (rotation, scale, translation; reflections tried too), over every cyclic matching; the best fit must be a
     proper similarity, with a residual far below the edge length, and clearly better than any other matching;
  3. the whole rim of our supertile, mapped by that similarity, must lie on the figure's black outline;
  4. the two tiles of our Mystic must land on the figure's two shaded tiles, the first tile on the lighter one;
  5. the labels read by hand from the figure (fig41_labels.json: anticlockwise from the leftmost dot) must be the
     labels of Table 4 of the paper on the matching sides, the leftmost dot being our vertex 0.
Control: the vertex sets of the other eight kinds fit each cluster's dots much worse, so the dots determine the kind.
usage: python3 crosscheck/fig41_compare.py PATH/TO/spectre-paper.pdf
"""
import sys, os, math, json, hashlib, subprocess, tempfile, itertools
import numpy as np
from PIL import Image
from scipy import ndimage
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'exact'))
import exact as X
from fig41_render import deform, VERT, LAB

SHA = '1a1c2123c63f7fe25efb0107ef5a3d1a8ad9d32b1e67a7d597b4723456c01be0'
WIN = {'Gamma': (470, 430, 980, 900), 'Delta': (990, 430, 1490, 900), 'Theta': (1490, 430, 2010, 900),
       'Lambda': (470, 1000, 980, 1460), 'Xi': (990, 1000, 1490, 1460), 'Pi': (1490, 1000, 2010, 1460),
       'Sigma': (470, 1560, 980, 2010), 'Phi': (990, 1560, 1490, 2010), 'Psi': (1490, 1560, 2010, 2010)}

def similarity(P, Q, allow_reflection):
    """least-squares similarity z -> s R z + t mapping points P to Q (Umeyama); returns (map, rms, proper)."""
    P = np.asarray(P, float); Q = np.asarray(Q, float)
    mp, mq = P.mean(0), Q.mean(0); A, B = P - mp, Q - mq
    U, S, Vt = np.linalg.svd(B.T @ A)
    d = np.sign(np.linalg.det(U @ Vt))
    D = np.diag([1, d]) if (allow_reflection or d > 0) else np.diag([1, 1])
    if not allow_reflection and d < 0:          # best proper rotation
        D = np.diag([1, -1])
    R = U @ D @ Vt; s = np.trace(np.diag(S) @ D) / (A ** 2).sum(); t = mq - s * R @ mp
    f = lambda Z: (s * (R @ np.asarray(Z, float).T)).T + t
    rms = math.sqrt(((f(P) - Q) ** 2).sum(1).mean())
    return f, rms, np.linalg.det(R) > 0, s

def main(pdf):
    h = hashlib.sha256(open(pdf, 'rb').read()).hexdigest()
    print('spectre paper PDF sha256', h, '(expected' + (' - ok)' if h == SHA else ' ' + SHA + ' - DIFFERENT FILE, window positions may not apply)'))
    with tempfile.TemporaryDirectory() as td:
        subprocess.run(['pdftoppm', '-f', '13', '-l', '13', '-r', '300', '-png', pdf, os.path.join(td, 'p')], check=True)
        png = [f for f in os.listdir(td) if f.endswith('.png')][0]
        im = np.array(Image.open(os.path.join(td, png)).convert('RGB')).astype(float)
    grey = im.mean(2); dark = grey < 90
    near_dark = ndimage.binary_dilation(dark, iterations=4)
    r = 6; yy, xx = np.mgrid[-r:r + 1, -r:r + 1]; disc = (xx * xx + yy * yy) <= r * r
    labels_fig = json.load(open(os.path.join(HERE, 'fig41_labels.json')))
    lev, trs_all = X.build(1)
    allok = True
    for K, (x0, y0, x1, y1) in WIN.items():
        lab, n = ndimage.label(ndimage.binary_opening(dark[y0:y1, x0:x1], structure=disc))
        dots = [(x0 + xs.mean(), y0 + ys.mean()) for xs, ys in
                ((np.nonzero(lab == i)[1], np.nonzero(lab == i)[0]) for i in range(1, n + 1)) if len(xs) > 60]
        ok = len(dots) == 6
        Q = np.array([(x, -y) for x, y in dots])                       # y up
        c = Q.mean(0); Q = Q[np.argsort(np.arctan2(Q[:, 1] - c[1], Q[:, 0] - c[0]))]   # anticlockwise as printed
        b = lev[1][K]; E = b.E
        R = np.array([deform(v) for v in b.verts])
        assert (R[:, 0] * np.roll(R[:, 1], -1) - np.roll(R[:, 0], -1) * R[:, 1]).sum() > 0   # own order is anticlockwise here
        V = R[[(b.defA + p) % E for p in VERT[K]]]                      # our vertices 0..5, anticlockwise
        fits = []
        for sh in range(6):
            for refl in (False, True):
                QQ = np.roll(Q, -sh, axis=0) if not refl else np.roll(Q[::-1], -sh, axis=0)
                f, rms, proper, s = similarity(V, QQ, refl)
                fits.append((rms / s, sh, refl, f, proper, s))           # residual in units of our edge length
        fits.sort(key=lambda z: z[0])
        best, second = fits[0], fits[1]
        res, sh, refl, f, proper, s = best
        ok &= proper and not refl and res < 0.1 and second[0] > 5 * res
        # control: the vertex sets of the other eight kinds fit these dots much worse (the dots determine the kind)
        def best_res(K2):
            b2 = lev[1][K2]; R2 = np.array([deform(v) for v in b2.verts]); V2 = R2[[(b2.defA + p) % b2.E for p in VERT[K2]]]
            return min(similarity(V2, np.roll(Q, -k, axis=0), False)[1] / similarity(V2, np.roll(Q, -k, axis=0), False)[3] for k in range(6))
        other = min((best_res(K2), K2) for K2 in WIN if K2 != K)
        ok &= other[0] > 5 * res
        # 3. outline: dense samples of our rim, mapped, must lie on the figure's dark outline
        pts = np.concatenate([np.linspace(R[k], R[(k + 1) % E], 12, endpoint=False) for k in range(E)])
        img = f(pts); xi = np.round(img[:, 0]).astype(int); yi = np.round(-img[:, 1]).astype(int)
        on = near_dark[yi, xi].mean()
        ok &= on > 0.99
        # 4. Mystic shading: first tile lighter than the second, both shaded (not white)
        gs = X.tile_placements(K, 1, X.ID, trs_all); t1, t2 = gs[-2], gs[-1]
        def colour(g):
            cen = np.mean([deform(X.iapply(g, v)) for v in X.PTS], axis=0); p = f([cen])[0]
            return im[int(round(-p[1])), int(round(p[0]))]
        c1, c2 = colour(t1), colour(t2)
        ok &= c1.mean() < 245 and c2.mean() < 245 and c1.mean() > c2.mean()
        # 5. labels: the leftmost dot must be our vertex 0; the hand-read labels from it must be those of Table 4
        left = int(np.argmin(Q[:, 0]))
        vertex_at_left = (left - sh) % 6
        ok &= vertex_at_left == 0 and labels_fig[K] == LAB[K]
        allok &= ok
        print(f'{K:7s} dots {len(dots)}; best fit: proper={proper} residual {res:.3f} edge (next best {second[0]:.2f}; best other kind {other[1]} {other[0]:.2f}); '
              f'rim on outline {100 * on:.1f}%; Mystic shading first/second {c1.mean():.0f}/{c2.mean():.0f}; '
              f'leftmost dot = our vertex {vertex_at_left}; labels {"= Table 4" if labels_fig[K] == LAB[K] else "DIFFER"}  {"ok" if ok else "FAIL"}')
    print('FIG. 4.1: ALL NINE CLUSTERS AGREE' if allok else 'FIG. 4.1: PROBLEMS')
    return 0 if allok else 1

if __name__ == '__main__':
    if len(sys.argv) < 2: print(__doc__); sys.exit(2)
    sys.exit(main(sys.argv[1]))
