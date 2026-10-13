"""Cut the paper's figures out of the built PDF, so the map shows exactly what the paper shows.

A figure is found by its caption ("Figure N."); its picture is everything drawn above the caption and below the
previous full-width text, with short text blocks (labels) counted as part of the picture. Needs PyMuPDF; without it
the map is built without figures.
"""
import re
from pathlib import Path

ZOOM = 2.2          # 72 dpi * 2.2 = about 160 dpi
GAP = 16            # points: items closer than this to the picture belong to it
HEADER = 70        # points from the top: the running head (page number, title or author) lies above this


def extract(pdf_path, out_dir, numbers):
    try:
        import pymupdf
    except ImportError:
        try:
            import fitz as pymupdf
        except ImportError:
            print('figures: PyMuPDF not installed, building without figures')
            return {}
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    doc = pymupdf.open(str(pdf_path))
    found = {}
    for page in doc:
        blocks = page.get_text('blocks')
        text_w = max((b[2] - b[0] for b in blocks), default=0)
        for b in blocks:
            m = re.match(r'\s*Figure (\d+)\.', b[4])
            if not m or int(m.group(1)) not in numbers or int(m.group(1)) in found:
                continue
            n = int(m.group(1))
            cap = pymupdf.Rect(b[:4])
            items = [pymupdf.Rect(d['rect']) for d in page.get_drawings()]
            items += [pymupdf.Rect(i['bbox']) for i in page.get_image_info()]
            items += [pymupdf.Rect(t[:4]) for t in blocks
                      if t is not b and (t[2] - t[0]) < 0.8 * text_w and not re.match(r'\s*Figure \d+\.', t[4])]
            items = [r for r in items if r.y1 <= cap.y0 + 1 and r.width > 0.5 and r.height > 0.5 and r.y0 > HEADER]
            region = None
            for r in sorted(items, key=lambda r: -r.y1):
                top = region.y0 if region else cap.y0
                if r.y1 >= top - GAP:
                    region = pymupdf.Rect(r) if region is None else region | r
            if region is None:
                continue
            region = (region + (-3, -3, 3, 3)) & page.rect
            pix = page.get_pixmap(matrix=pymupdf.Matrix(ZOOM, ZOOM), clip=region, alpha=False)
            name = 'fig-%d.png' % n
            pix.save(str(out_dir / name))
            found[n] = {'file': name, 'w': pix.width, 'h': pix.height, 'page': page.number + 1}
    missing = sorted(set(numbers) - set(found))
    if missing:
        print('figures: not found in the PDF:', missing)
    return found
