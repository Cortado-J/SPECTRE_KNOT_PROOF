"""Cut the paper's figures out of the built PDF, so the map shows exactly what the paper shows.

A figure is found by its caption ("Figure N."); its picture is everything drawn above the caption and below the
previous full-width text, with short text blocks (labels) counted as part of the picture, but nothing of a table
above it on the same page (Table 1 sits right above Figure 3). Needs PyMuPDF; without it the map is built without
figures.
"""
import re
from pathlib import Path

ZOOM = 2.2          # 72 dpi * 2.2 = about 160 dpi
GAP = 16            # points: items closer than this to the picture belong to it
HEADER = 70        # points from the top: the running head (page number, title or author) lies above this
TABLE_GAP = 160     # points: a table's rules lie closer together than this; the next rule further down is not its own


def tables(page, rect):
    """The tables on a page (rect: PyMuPDF's Rect, which extract imports), each from its caption ("Table N.", set
    above the table) down to the last of its booktabs rules, which are thin horizontal strokes."""
    rules = sorted((rect(d['rect']) for d in page.get_drawings()
                    if d['rect'].height < 2 and d['rect'].width > 30), key=lambda r: r.y0)
    caps = [rect(b[:4]) for b in page.get_text('blocks') if re.match(r'\s*Table \d+\.', b[4])]
    found = []
    for cap in caps:
        bottom = cap.y1
        for r in rules:
            if r.y0 < cap.y1:
                continue
            if r.y0 - bottom > TABLE_GAP or any(bottom < c.y0 < r.y0 for c in caps):   # another table's rules
                break
            bottom = r.y1
        found.append(rect(cap.x0, cap.y0, cap.x1, bottom))
    return found


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
        page_tables = tables(page, pymupdf.Rect)
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
            for t in page_tables:       # a table above the figure: start below its last rule
                if region.y0 < t.y1 <= cap.y0:
                    region.y0 = t.y1 + 2
            pix = page.get_pixmap(matrix=pymupdf.Matrix(ZOOM, ZOOM), clip=region, alpha=False)
            name = 'fig-%d.png' % n
            pix.save(str(out_dir / name))
            found[n] = {'file': name, 'w': pix.width, 'h': pix.height, 'page': page.number + 1}
    missing = sorted(set(numbers) - set(found))
    if missing:
        print('figures: not found in the PDF:', missing)
    return found
