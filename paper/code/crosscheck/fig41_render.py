#!/usr/bin/env python3
"""Draw the nine level-1 supertiles as clusters of hats and turtles, for comparison by eye with Fig. 4.1 of the
spectre paper (paper, proof of Prop. 2.4, base case of the dictionary (*)).

The level-1 supertiles come from exact/exact.py, in the code's own frame at level 1, which is the mirror image of the
true handedness, i.e. the handedness of the clusters drawn in the spectre paper (Figs. 2.1 and 4.1). Every vertex
a + b z + c z^2 + d z^3 (z = e^{i pi/6}) is mapped to (a + c z^2) + sqrt(3) (b z + d z^3): the edges in odd directions
are lengthened to sqrt(3), which turns even tiles into hats and odd tiles into turtles (spectre paper, Section 3).
Dots: the six vertices of each supertile, at the rim positions found by exact.py; each side j carries the label of
Table 4 (Fig. 4.2 of the spectre paper); the two tiles of the Mystic are shaded (first tile light).
usage: python3 crosscheck/fig41_render.py OUT.pdf
"""
import sys, os, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'exact'))
import exact as X
import matplotlib; matplotlib.use('pdf')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

S3 = math.sqrt(3)
def deform(z):
    a, b, c, d = z
    even = (a + c * 0.5, c * S3 / 2)                 # a + c z^2
    odd = (b * S3 / 2, b * 0.5 + d)                  # b z + d z^3
    return (even[0] + S3 * odd[0], even[1] + S3 * odd[1])

VERT = {'Gamma': [0, 7, 14, 24, 34, 39], 'Delta': [0, 10, 15, 23, 30, 40], 'Theta': [0, 10, 15, 26, 31, 41],
        'Lambda': [0, 10, 15, 23, 30, 41], 'Xi': [0, 7, 15, 26, 31, 41], 'Pi': [0, 7, 15, 23, 30, 41],
        'Sigma': [4, 10, 15, 23, 30, 40], 'Phi': [0, 10, 15, 23, 31, 41], 'Psi': [0, 7, 15, 23, 31, 41]}   # log A13
LAB = {'Gamma': ['a-', 'a+', 'g-', 'd-', 'b+', 'b-'], 'Delta': ['g+', 'b+', 'e-', 'a+', 'g-', 'z-'],
       'Theta': ['g+', 'b+', 't+', 'b+', 'h', 'b-'], 'Lambda': ['g+', 'b+', 'e-', 'a+', 't-', 'b-'],
       'Xi': ['a-', 'e+', 't+', 'b+', 'h', 'b-'], 'Pi': ['a-', 'e+', 'e-', 'a+', 't-', 'b-'],
       'Sigma': ['z+', 'b+', 'e-', 'a+', 'g-', 'd+'], 'Phi': ['g+', 'b+', 'e-', 'e+', 'h', 'b-'],
       'Psi': ['a-', 'e+', 'e-', 'e+', 'h', 'b-']}                                                         # Table 4
GR = {'a': r'\alpha', 'b': r'\beta', 'g': r'\gamma', 'd': r'\delta', 'e': r'\epsilon', 'z': r'\zeta', 'h': r'\eta', 't': r'\theta'}
def tex(l): return '$' + GR[l[0]] + ('^{' + l[1] + '}' if len(l) > 1 else '') + '$'
GREEK = {'Gamma': r'\Gamma', 'Delta': r'\Delta', 'Theta': r'\Theta', 'Lambda': r'\Lambda', 'Xi': r'\Xi', 'Pi': r'\Pi',
         'Sigma': r'\Sigma', 'Phi': r'\Phi', 'Psi': r'\Psi'}

def main(out):
    lev, trs_all = X.build(1)
    fig, axs = plt.subplots(3, 3, figsize=(9, 9.6))
    for ax, T in zip(axs.flat, X.NAMES):
        ax.set_aspect('equal'); ax.axis('off')
        b = lev[1][T]; E = b.E
        gs = X.tile_placements(T, 1, X.ID, trs_all)
        myst = gs[-2:]                                  # the Gamma child (last) is the Mystic: first tile, then second
        for g in gs:
            P = [deform(X.iapply(g, v)) for v in X.PTS]
            fc = '#d9dcc8' if g == myst[0] else ('#b5b795' if g == myst[1] else 'white')
            ax.add_patch(Polygon(P, closed=True, fc=fc, ec='#aaaaaa', lw=0.5))
        R = [deform(v) for v in b.verts]
        ax.add_patch(Polygon(R, closed=True, fill=False, ec='black', lw=1.8))
        V = [(b.defA + p) % E for p in VERT[T]]
        cx = sum(p[0] for p in R) / E; cy = sum(p[1] for p in R) / E
        for j, k in enumerate(V):
            ax.plot(*R[k], 'o', color='black', ms=5)
            k2 = V[(j + 1) % 6]; L = (k2 - k) % E; mid = R[(k + L // 2) % E]
            dx, dy = mid[0] - cx, mid[1] - cy; n = math.hypot(dx, dy)
            ax.text(mid[0] + 0.9 * dx / n, mid[1] + 0.9 * dy / n, tex(LAB[T][j]), ha='center', va='center', fontsize=11)
            ax.text(mid[0] - 0.9 * dx / n, mid[1] - 0.9 * dy / n, str(j), ha='center', va='center', fontsize=7, color='#0072B2')
        A = R[b.defA]; ax.plot(*A, 'o', mfc='none', mec='#D55E00', ms=10, mew=1.5)
        xs = [p[0] for p in R]; ys = [p[1] for p in R]
        ax.set_xlim(min(xs) - 2, max(xs) + 2); ax.set_ylim(min(ys) - 2, max(ys) + 2)
        ax.set_title('$' + GREEK[T] + '$', fontsize=12)
    plt.rcParams['text.usetex'] = False
    fig.suptitle('Level-1 supertiles as hat/turtle clusters (code frame = handedness of the spectre paper, Fig. 4.1).\n'
                 'Dots: vertices; circle: A; labels: Table 4; small numbers: side j', fontsize=9)
    fig.savefig(out); print('wrote', out)

if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'fig41_render.pdf')
