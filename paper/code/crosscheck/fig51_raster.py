#!/usr/bin/env python3
"""Reproduce, from the PDF of the spectre paper, the raster data that fig51_compare.py uses (paper, Remark 2.5):
the six marked vertex dots of each panel of Fig. 5.1 (the DOTS table in fig51_compare.py) and the centre of the Gamma
hexagon of each panel (gamma_centres.json). Both were first found on a 400-dpi render of page 17 (blob detection for
the dots, template matching of the Gamma glyph for the centres); this script redoes that from the PDF and checks that
it finds the same points.
usage: python3 crosscheck/fig51_raster.py PATH/TO/spectre-paper.pdf
"""
import sys, os, json, hashlib, subprocess, tempfile, re
import numpy as np
from PIL import Image
from scipy import ndimage
from scipy.signal import fftconvolve
HERE = os.path.dirname(os.path.abspath(__file__))
SHA = '1a1c2123c63f7fe25efb0107ef5a3d1a8ad9d32b1e67a7d597b4723456c01be0'
NAMES = ['Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Phi', 'Psi']

def main(pdf):
    h = hashlib.sha256(open(pdf, 'rb').read()).hexdigest()
    print('spectre paper PDF sha256', h, '(ok)' if h == SHA else '(DIFFERENT FILE from the one encoded: ' + SHA + ')')
    E = json.load(open(os.path.join(HERE, 'fig51_encoding.json')))
    G = json.load(open(os.path.join(HERE, 'gamma_centres.json')))
    src = open(os.path.join(HERE, 'fig51_compare.py')).read()
    DOTS = eval(re.search(r'DOTS=(\{.*?\})\n', src, re.S).group(1))
    WSC = 3308 / 1414
    with tempfile.TemporaryDirectory() as td:
        subprocess.run(['pdftoppm', '-f', '17', '-l', '17', '-r', '400', '-png', pdf, os.path.join(td, 'p')], check=True)
        png = [f for f in os.listdir(td) if f.endswith('.png')][0]
        page = np.array(Image.open(os.path.join(td, png)).convert('L')).astype(float)
    print('page 17 rendered at 400 dpi:', page.shape[1], 'x', page.shape[0], 'px')
    crops = {}
    for T in NAMES:
        b = E['crop_boxes_display'][T]
        x0, y0, x1, y1 = [int(round(v * WSC)) for v in b]
        crops[T] = page[y0:y1, x0:x1]
    r = 11; yy, xx = np.mgrid[-r:r + 1, -r:r + 1]; disc = (xx * xx + yy * yy) <= r * r
    T0 = (crops['Delta'][360:415, 225:275] < 80).astype(float); T0 -= T0.mean()   # the Gamma glyph in the Delta panel
    ok = True
    for T in NAMES:
        a = crops[T] < 60
        lab, n = ndimage.label(ndimage.binary_opening(a, structure=disc))
        found = sorted((xs.mean(), ys.mean()) for xs, ys in ((np.nonzero(lab == i)[1], np.nonzero(lab == i)[0]) for i in range(1, n + 1)))
        enc = sorted(DOTS[T])
        dmax = max(min(np.hypot(fx - ex, fy - ey) for fx, fy in found) for ex, ey in enc) if found else 1e9
        c = fftconvolve((crops[T] < 80).astype(float), T0[::-1, ::-1], mode='same')
        gy, gx = np.unravel_index(np.argmax(c), c.shape)
        dg = np.hypot(gx - G[T][0], gy - G[T][1])
        good = len(found) == 6 and dmax <= 3 and dg <= 3
        ok &= good
        print(f'{T:7s} dots found {len(found)}, max distance to the encoded dots {dmax:.1f} px; Gamma centre ({gx},{gy}) vs encoded {tuple(G[T])}: {dg:.1f} px  {"ok" if good else "FAIL"}')
    print('FIG. 5.1 RASTER DATA REPRODUCED' if ok else 'FIG. 5.1 RASTER DATA: PROBLEMS')
    return 0 if ok else 1

if __name__ == '__main__':
    if len(sys.argv) < 2: print(__doc__); sys.exit(2)
    sys.exit(main(sys.argv[1]))
