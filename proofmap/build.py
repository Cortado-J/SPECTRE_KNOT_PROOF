#!/usr/bin/env python3
"""Build the proof site: a page for every numbered result of the paper, with its statement and proof taken from the
LaTeX, what it cites and what cites it, the Lean declarations that formalise it and the scripts that compute it; a
graph of the results; a page for every Lean declaration; and Statement.lean line by line (lean/guide).

Sources: paper/tex/spectre_knot.tex (numbering checked against paper/spectre_knot.pdf), lean/README.md, the Lean files
under lean/SpectreKnot/, lean/guide/, and two hand-kept files: proofmap/notes.json (short labels for untitled
results, what part of a result the Lean covers, the AI-written reading aids, and which results belong to each step of
the public site's Prove page) and proofmap/status.html (the line about AI, linking to the public site's Made with AI page).

    python3 proofmap/build.py              # the site into out/site/ (index.html, statement.html, figures,
                                           # downloads), the artifact files into out/, and addresses.json
    python3 proofmap/build.py --site DIR   # the site into DIR
"""
import html
import json
import re
import shutil
import subprocess
import sys
import zipfile
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
import texparse  # noqa: E402
import leanparse  # noqa: E402
import figures as figmod  # noqa: E402
sys.path.insert(0, str(ROOT / 'lean' / 'guide'))
import build_guide  # noqa: E402

TEX = ROOT / 'paper/tex/spectre_knot.tex'
PDF = ROOT / 'paper/spectre_knot.pdf'
LEAN = ROOT / 'lean'
README = LEAN / 'README.md'
OUT = ROOT / 'out'

esc = html.escape


def rid(label):
    return 'r-' + re.sub(r'[^A-Za-z0-9]', '-', label)


def lid(name):
    return 'lean-' + re.sub(r'[^A-Za-z0-9._~-]', '-', name)


# ---------------------------------------------------------------- LaTeX to HTML

class Tex:
    def __init__(self, data, bib):
        self.labels = data['labels']
        self.bib = bib
        self.pages = set()
        self.figpages = set()

    def refname(self, lab, cap):
        info = self.labels.get(lab)
        if not info:
            return esc(lab)
        t, n = info['type'], info['number']
        if t == 'result':
            text = '%s&nbsp;%s' % (info['name'], n)
            if lab in self.pages:
                return '<a href="#%s">%s</a>' % (rid(lab), text)
            return text
        word = {'section': 'Section', 'figure': 'Figure', 'table': 'Table', 'equation': 'Equation'}[t]
        if t == 'figure' and int(n) in self.figpages:
            return '<a href="#f-%s">Figure&nbsp;%s</a>' % (n, n)
        if t == 'equation':
            return '%s&nbsp;(%s)' % (word, n)
        return '<span class="pref" title="in the paper">%s&nbsp;%s</span>' % (word, n)

    def ref(self, cmd, arg):
        labs = [a.strip() for a in arg.split(',') if a.strip()]
        if cmd == 'ref':
            return ', '.join(self.labels.get(l, {}).get('number', l) for l in labs)
        if cmd == 'eqref':
            return ', '.join('(%s)' % self.labels.get(l, {}).get('number', l) for l in labs)
        parts = [self.refname(l, cmd == 'Cref') for l in labs]
        if len(parts) == 1:
            return parts[0]
        return ', '.join(parts[:-1]) + ' and ' + parts[-1]

    def cite(self, opt, keys):
        out = []
        for k in keys.split(','):
            b = self.bib.get(k.strip())
            out.append(b['short'] if b else esc(k))
        s = '; '.join(out)
        if opt:
            s += ', ' + self.inline(opt)
        return '<span class="cite">[%s]</span>' % s

    def math_protect(self, s, store):
        def keep(m, display=False, tag=None):
            body = m.group(0)
            store.append((body, display))
            return '\x00%d\x00' % (len(store) - 1)

        def env(m):
            body = m.group(0)
            lab = re.search(r'\\label\{([^}]*)\}', body)
            if lab:
                num = self.labels.get(lab.group(1), {}).get('number', '')
                body = body.replace(lab.group(0), '\\tag{%s}' % num)
            body = body.replace('\\begin{equation}', '\\begin{equation*}').replace('\\end{equation}',
                                                                                     '\\end{equation*}')
            store.append((body, True))
            return '\x00%d\x00' % (len(store) - 1)

        s = re.sub(r'\\begin\{(align\*?|equation\*?|gather\*?)\}.*?\\end\{\1\}', env, s, flags=re.S)
        s = re.sub(r'\\\[.*?\\\]', lambda m: keep(m, True), s, flags=re.S)
        s = re.sub(r'(?<!\\)\$(?:\\\$|[^$])+?(?<!\\)\$', keep, s, flags=re.S)
        return s

    def math_restore(self, s, store):
        def put(m):
            body, display = store[int(m.group(1))]
            if display:
                return '<div class="mathd">%s</div>' % esc(body, quote=False)
            return '<span class="math">%s</span>' % esc(body, quote=False)
        return re.sub(r'\x00(\d+)\x00', put, s)

    def commands(self, s):
        """Text-mode commands, applied to HTML-escaped text."""
        s = re.sub(r'\\(cref|Cref|ref|eqref)\{([^}]*)\}', lambda m: self.ref(m.group(1), m.group(2)), s)
        s = re.sub(r'\\cite(?:\[([^\]]*)\])?\{([^}]*)\}', lambda m: self.cite(m.group(1), m.group(2)), s)
        s = re.sub(r'\\label\{[^}]*\}', '', s)
        for _ in range(3):   # nested one-argument commands
            s = re.sub(r'\\(emph|textit)\{([^{}]*)\}', r'<em>\2</em>', s)
            s = re.sub(r'\\textbf\{([^{}]*)\}', r'<strong>\1</strong>', s)
            s = re.sub(r'\\(code|texttt)\{([^{}]*)\}', lambda m: '<code>%s</code>' % m.group(2).replace('\\_', '_'),
                       s)
            s = re.sub(r'\\(textup|textrm|mbox|text)\{([^{}]*)\}', r'\2', s)
        rep = [('---', '\u2014'), ('--', '\u2013'), ('``', '\u201c'), ("''", '\u201d'), ('~', '\u00a0'),
               ('\\,', '\u2009'), ('\\ ', ' '), ('\\S', '\u00a7'), ('\\ldots', '\u2026'), ('\\dots', '\u2026'),
               ('\\&amp;', '&amp;'), ('\\%', '%'), ('\\_', '_'), ('\\#', '#'), ('\\qedhere', ''), ('\\noindent', ''),
               ('\\medskip', ''), ('\\allowbreak', ''), ('\\smallskip', ''), ('\\bigskip', ''), ('\\quad', ' '), ('\\-', '')]
        for a, b in rep:
            s = s.replace(a, b)
        s = re.sub(r'\{\\"(\w)\}', lambda m: m.group(1) + '\u0308', s)
        s = re.sub(r"\{\\'(\w)\}", lambda m: m.group(1) + '\u0301', s)
        left = re.findall(r'\\[A-Za-z]+', s)
        if left:
            raise SystemExit('unhandled LaTeX in text: %s\n%s' % (sorted(set(left)), s[:400]))
        return s

    def inline(self, s):
        store = []
        s = self.math_protect(s, store)
        s = self.commands(esc(s, quote=False))
        return self.math_restore(s, store)

    def lists(self, s):
        """enumerate/itemize -> ol/ul (applied after escaping; items keep their own paragraphs)."""
        def envrepl(m):
            kind, opt, body = m.group(1), m.group(2) or '', m.group(3)
            items = re.split(r'\\item\b(?:\[([^\]]*)\])?', body)
            lis = []
            n = 0
            for k in range(1, len(items), 2):
                n += 1
                mark = items[k]
                if mark is None and kind == 'enumerate':
                    if 'alph' in opt:
                        mark = '(%s)' % chr(96 + n)
                    elif 'roman' in opt:
                        mark = '(%s)' % ['i', 'ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii'][n - 1]
                    else:
                        mark = '%d.' % n
                mark_html = '<span class="lm">%s</span>' % mark if mark else ''
                lis.append('<li>%s<div>%s</div></li>' % (mark_html, items[k + 1].strip()))
            return '\n\n<ul class="tl">%s</ul>\n\n' % ''.join(lis)
        for _ in range(2):
            s = re.sub(r'\\begin\{(enumerate|itemize)\}(\[[^\]]*\])?(.*?)\\end\{\1\}', envrepl, s, flags=re.S)
        return s

    def block(self, s):
        store = []
        s = self.math_protect(s, store)
        s = esc(s, quote=False)
        s = self.lists(s)
        s = self.commands(s)
        paras = [p.strip() for p in re.split(r'\n\s*\n', s) if p.strip()]
        out = []
        for p in paras:
            if p.startswith('<ul'):
                out.append(p)
                continue
            # a displayed formula cannot sit inside <p>: split the paragraph around it
            text = []
            for piece in re.split(r'(\x00\d+\x00)', p):
                m = re.fullmatch(r'\x00(\d+)\x00', piece)
                if m and store[int(m.group(1))][1]:
                    if ''.join(text).strip():
                        out.append('<p>%s</p>' % ''.join(text).strip())
                    text = []
                    out.append(piece)
                else:
                    text.append(piece)
            if ''.join(text).strip():
                out.append('<p>%s</p>' % ''.join(text).strip())
        return self.math_restore('\n'.join(out), store)


def read_bib(path):
    bib = {}
    text = Path(path).read_text(encoding='utf8')
    for m in re.finditer(r'@\w+\{([^,]+),(.*?)\n\}', text, flags=re.S):
        key, body = m.group(1).strip(), m.group(2)
        f = dict((k.lower(), v) for k, v in re.findall(r'(\w+)\s*=\s*\{((?:[^{}]|\{[^{}]*\})*)\}', body))
        authors = [a.strip() for a in f.get('author', '').split(' and ') if a.strip()]
        sur = [re.sub(r'[{}]', '', a.split(',')[0]) for a in authors]
        sur = [s.replace('\\"u', 'ü').replace("\\'a", 'á').replace("\\'c", 'ć') for s in sur]
        who = sur[0] + (' et al.' if len(sur) > 2 else (' and ' + sur[1] if len(sur) == 2 else '')) if sur else key
        title = re.sub(r'[{}]', '', f.get('title', ''))
        bib[key] = {'short': '%s, <i>%s</i>' % (esc(who), esc(title)), 'title': title}
    return bib


# ---------------------------------------------------------------- small Markdown (README, Lean doc comments)

def md_inline(s):
    out = []
    for k, part in enumerate(re.split(r'(`[^`]*`)', s)):
        if k % 2:
            out.append('<code>%s</code>' % esc(part[1:-1]))
        else:
            t = esc(part, quote=False)
            t = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', t)
            t = re.sub(r'(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?!\w)', r'<em>\1</em>', t)
            out.append(t)
    return ''.join(out)


def md_block(s):
    lines = s.split('\n')
    out, para, items = [], [], []

    def flush():
        if para:
            out.append('<p>%s</p>' % md_inline(' '.join(x.strip() for x in para)))
            para.clear()
        if items:
            out.append('<ul class="md">%s</ul>' % ''.join('<li>%s</li>' % md_inline(' '.join(i)) for i in items))
            items.clear()
    for line in lines:
        if not line.strip():
            flush()
            continue
        m = re.match(r'^\s*[-*]\s+(.*)', line)
        if m:
            if para:
                flush()
            items.append([m.group(1)])
            continue
        if items and line.startswith('  '):
            items[-1].append(line.strip())
            continue
        if items:
            flush()
        para.append(line)
    flush()
    return '\n'.join(out)


LEAN_KW = re.compile(r'\b(theorem|lemma|def|abbrev|structure|inductive|instance|class|where|fun|let|have|show|by|'
                     r'from|match|with|if|then|else|Prop|Type|∀|∃)\b')


def lean_html(code):
    out = []
    for line in code.split('\n'):
        k = line.find('--')
        main, com = (line[:k], line[k:]) if k >= 0 else (line, '')
        main = LEAN_KW.sub(lambda m: '\x01%s\x02' % m.group(0), main)
        main = esc(main, quote=False).replace('\x01', '<span class="kw">').replace('\x02', '</span>')
        out.append(main + ('<span class="com">%s</span>' % esc(com, quote=False) if com else ''))
    return '\n'.join(out)


# ---------------------------------------------------------------- the graph

NODE_W, NODE_H, GAP_X, GAP_Y, DUMMY_W = 120, 98, 14, 56, 12   # a card: heading, up to three lines of name, marks


def layout(nodes, uses, order_key, pack=False):
    """Layered drawing: premises above conclusions. Returns positions, the drawn (reduced) edges with routes. With
    `pack`, each row is packed tight and centred (for small graphs, which are shown scaled down)."""
    reach = {}

    def below(n):   # everything n's proof rests on, transitively
        if n not in reach:
            s = set()
            for u in uses[n]:
                s.add(u)
                s |= below(u)
            reach[n] = s
        return reach[n]
    for n in nodes:
        below(n)
    # transitive reduction: drop u -> n if u is below another premise of n
    red = {n: [u for u in uses[n] if not any(u in reach[v] for v in uses[n] if v != u)] for n in nodes}
    users = defaultdict(list)
    for n in nodes:
        for u in red[n]:
            users[u].append(n)
    layer = {}

    def lay(n):
        if n not in layer:
            layer[n] = 0 if not red[n] else 1 + max(lay(u) for u in red[n])
        return layer[n]
    for n in nodes:
        lay(n)
    # results cited only further down are drawn just above their first user
    for n in sorted(nodes, key=lambda n: -layer[n]):
        if users[n]:
            layer[n] = max(layer[n], min(layer[v] for v in users[n]) - 1)
    nl = max(layer.values()) + 1
    rows = [[] for _ in range(nl)]
    for n in sorted(nodes, key=order_key):
        rows[layer[n]].append(n)
    # dummies for edges longer than one layer
    edges = []
    width = {n: NODE_W for n in nodes}
    for n in nodes:
        for u in red[n]:
            chain = [u]
            for L in range(layer[u] + 1, layer[n]):
                d = ('d', u, n, L)
                rows[L].append(d)
                width[d] = DUMMY_W
                chain.append(d)
            chain.append(n)
            edges.append(chain)
    nbr_up = defaultdict(list)
    nbr_dn = defaultdict(list)
    for ch in edges:
        for a, b in zip(ch, ch[1:]):
            nbr_dn[a].append(b)
            nbr_up[b].append(a)
    # barycentre sweeps
    pos = {}

    def number():
        for row in rows:
            for i, v in enumerate(row):
                pos[v] = i
    number()
    for it in range(24):
        rng = range(1, nl) if it % 2 == 0 else range(nl - 2, -1, -1)
        for L in rng:
            nb = nbr_up if it % 2 == 0 else nbr_dn
            def bc(v):
                ns = nb[v]
                return sum(pos[x] for x in ns) / len(ns) if ns else pos[v]
            rows[L].sort(key=bc)
            for i, v in enumerate(rows[L]):
                pos[v] = i
    # x coordinates: pack, then pull each node towards its neighbours, keeping order and spacing
    x = {}
    for row in rows:
        cx = 0
        for v in row:
            x[v] = cx + width[v] / 2
            cx += width[v] + GAP_X
    for it in range(40):
        for L in (range(nl) if it % 2 == 0 else range(nl - 1, -1, -1)):
            row = rows[L]
            want = {}
            for v in row:
                ns = nbr_up[v] + nbr_dn[v]
                want[v] = sum(x[n] for n in ns) / len(ns) if ns else x[v]
            for v in row:
                x[v] = 0.5 * x[v] + 0.5 * want[v]
            for i in range(1, len(row)):
                a, b = row[i - 1], row[i]
                lo = x[a] + (width[a] + width[b]) / 2 + GAP_X
                if x[b] < lo:
                    x[b] = lo
            for i in range(len(row) - 2, -1, -1):
                a, b = row[i], row[i + 1]
                hi = x[b] - (width[a] + width[b]) / 2 - GAP_X
                if x[a] > hi:
                    x[a] = hi
    if pack:
        rw = [sum(width[v] for v in row) + GAP_X * (len(row) - 1) for row in rows]
        for row, w in zip(rows, rw):
            cx = (max(rw) - w) / 2
            for v in row:
                x[v] = cx + width[v] / 2
                cx += width[v] + GAP_X
    minx = min(x[v] - width[v] / 2 for v in x)
    for v in x:
        x[v] -= minx
    W = max(x[v] + width[v] / 2 for v in x)
    y = {}
    for L, row in enumerate(rows):
        for v in row:
            y[v] = L * (NODE_H + GAP_Y)
    H = (nl - 1) * (NODE_H + GAP_Y) + NODE_H
    return {'x': x, 'y': y, 'W': W, 'H': H, 'edges': edges, 'red': red, 'layer': layer}


def svg_graph(nodes, lay, info, gid='all', ext=(), label='Graph of the results of the paper: each arrow runs from a '
              'result to one whose proof cites it'):
    """The graph as SVG. `gid` makes the arrowhead's id unique on the page (every graph is in the one page); `ext` are
    nodes from neighbouring steps, drawn dashed."""
    pad = 14
    W, H = lay['W'] + 2 * pad, lay['H'] + 2 * pad
    x, y = lay['x'], lay['y']
    out = ['<svg class="graph" viewBox="0 0 %d %d" width="%d" height="%d" role="img" aria-label="%s">'
           % (W, H, W, H, esc(label))]
    out.append('<defs><marker id="pm-arr-%s" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" '
               'orient="auto-start-reverse"><path d="M0,1 L9,5 L0,9 z" fill="var(--edge)"/></marker></defs>' % gid)
    out.append('<g class="edges">')
    for ch in lay['edges']:
        pts = []
        for k, v in enumerate(ch):
            cx = x[v] + pad
            if k == 0:
                pts.append((cx, y[v] + pad + NODE_H))
            elif k == len(ch) - 1:
                pts.append((cx, y[v] + pad - 2))
            else:
                pts.append((cx, y[v] + pad))
                pts.append((cx, y[v] + pad + NODE_H))
        d = 'M%.1f,%.1f' % pts[0]
        for (x1, y1), (x2, y2) in zip(pts, pts[1:]):
            if abs(x1 - x2) < 0.5:
                d += ' L%.1f,%.1f' % (x2, y2)
            else:
                my = (y1 + y2) / 2
                d += ' C%.1f,%.1f %.1f,%.1f %.1f,%.1f' % (x1, my, x2, my, x2, y2)
        out.append('<path d="%s" data-a="%s" data-b="%s" marker-end="url(#pm-arr-%s)"/>' % (d, ch[0], ch[-1], gid))
    out.append('</g><g class="nodes">')
    for n in nodes:
        i = info[n]
        nx, ny = x[n] - NODE_W / 2 + pad, y[n] + pad
        cls = 'node %s%s%s' % (i['status'], ' main' if i['env'] == 'mainthm' else '', ' ext' if n in ext else '')
        out.append('<a href="#%s" class="%s" data-n="%s"><title>%s</title>' % (rid(n), cls, n, esc(i['plain'])))
        out.append('<rect x="%.1f" y="%.1f" width="%d" height="%d" rx="10"/>' % (nx, ny, NODE_W, NODE_H))
        out.append('<text x="%.1f" y="%.1f" class="nh">%s</text>' % (nx + 10, ny + 19, esc(i['abbr'])))
        for k, line in enumerate(wrap(i['short'], 17, 3)):
            out.append('<text x="%.1f" y="%.1f" class="nt">%s</text>' % (nx + 10, ny + 36 + 14 * k, esc(line)))
        # status chips along the bottom: the word itself, so colour is not the only cue
        chips = [(i['status'], STATUS_WORD[i['status']])]
        if i['lean']:
            chips.append(('lean' + (' part' if i['lean_part'] else ''), 'Lean' + ('\u00bd' if i['lean_part'] else '')))
        cx = nx + 10
        for cls_, word in chips:
            w = 7 + 6.3 * len(word)
            out.append('<rect class="chip %s" x="%.1f" y="%.1f" width="%.1f" height="15" rx="7.5"/>'
                       '<text class="chipt %s" x="%.1f" y="%.1f">%s</text>' % (cls_, cx, ny + NODE_H - 23, w, cls_,
                                                                             cx + w / 2, ny + NODE_H - 12, word))
            cx += w + 4
        out.append('</a>')
    out.append('</g></svg>')
    return '\n'.join(out)


def wrap(s, n, most=2):
    words, lines, cur = s.split(), [], ''
    for w in words:
        if cur and len(cur) + 1 + len(w) > n:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + ' ' + w).strip()
    if cur:
        lines.append(cur)
    if len(lines) > most:
        lines = lines[:most]
        lines[-1] = lines[-1][:n - 1].rstrip() + '\u2026'
    return lines


STATUS_WORD = {'argued': 'argued', 'computed': 'computed', 'cited': 'cited'}
ABBR = {'Theorem': 'Thm', 'Proposition': 'Prop', 'Corollary': 'Cor', 'Computation': 'Comp',
        'Construction': 'Constr'}   # the graph's node headings; the pages use the full names


# ---------------------------------------------------------------- page assembly

LABELS = {}


def plain(tex):
    s = re.sub(r'\\[cC]ref\{([^}]*)\}', lambda m: ' and '.join(
        '%s %s' % (LABELS[l]['name'], LABELS[l]['number']) if LABELS.get(l, {}).get('type') == 'result' else l
        for l in m.group(1).split(',')), tex)
    s = re.sub(r'\\cite(\[[^\]]*\])?\{[^}]*\}', '', s)
    s = re.sub(r'\$([^$]*)\$', r'\1', s)
    s = re.sub(r'\\[A-Za-z]+', '', s)
    s = s.replace('{', '').replace('}', '').replace('~', ' ').strip().rstrip(',').strip()
    return s


def computations_table(body_tex, tex):
    """Rows of the appendix table 'What was computed': labels -> (computation, scripts)."""
    part = body_tex.split('\\subsection*{What was computed}', 1)[1]
    part = part.split('\\midrule', 1)[1].split('\\bottomrule', 1)[0]
    rows = defaultdict(list)
    for row in re.split(r'\\\\\s*\n', part):
        cells = [c.strip() for c in re.split(r'(?<!\\)&', row)]
        if len(cells) != 3:
            continue
        labs = [l.strip() for m in re.finditer(r'\\[cC]ref\{([^}]*)\}', cells[0]) for l in m.group(1).split(',')]
        for l in labs:
            rows[l].append({'what': tex.inline(cells[1]), 'scripts': tex.inline(cells[2]),
                            'for': tex.inline(cells[0])})
    return rows


def status_box():
    """The line about AI at the top of the map (proofmap/status.html), linking to the public site's Made with AI page."""
    return (HERE / 'status.html').read_text(encoding='utf8').strip()


def build(site_dir=None):
    notes = json.loads((HERE / 'notes.json').read_text(encoding='utf8'))
    guide = build_guide.load()        # the line-by-line guide to Statement.lean, checked against the file
    data = texparse.parse(TEX)
    texparse.check_numbers(data['results'], PDF)
    bib = read_bib(ROOT / 'paper/tex/refs.bib')
    tex = Tex(data, bib)
    LABELS.update(data['labels'])
    results = data['results']
    R = {r['label']: r for r in results if r['label']}
    tex.pages = set(R)
    sec_title = {s['number']: s['title'] for s in data['sections']}

    decls = leanparse.index(LEAN)
    short_index = defaultdict(list)
    for k in decls:
        short_index[k.split('.')[-1]].append(k)
    rows = leanparse.readme_table(README)
    by_num = {(r['kind'], r['number']): r['label'] for r in results if r['label']}
    lean_rows = defaultdict(list)
    lean_named = []
    for row in rows:
        row['decls'] = [leanparse.resolve(n, decls) or n for n in row['lean']]
        for n in row['decls']:
            if n in decls and n not in lean_named:
                lean_named.append(n)
        refs = leanparse.paper_refs(row['paper'])
        for kind, num in refs:
            lab = by_num.get((kind, num))
            if lab is None:   # the README names a result the paper does not have: renumbered, or a typo
                raise SystemExit('lean/README.md names %s %s ("%s"), which is not in the paper' % (kind, num,
                                                                                                 row['paper']))
            if row not in lean_rows[lab]:
                lean_rows[lab].append(row)
        if not refs and not row['paper'].startswith(('—', '§')):
            print('proof map: README row "%s" names no numbered result' % row['paper'])
        missing = [n for n in row['lean'] if leanparse.resolve(n, decls) is None]
        if missing:
            raise SystemExit('lean/README.md names Lean declarations that are not in lean/: %s' % ', '.join(missing))
    # the claims the main theorems prove (a theorem `foo : Claim`): give the claim its own page too
    for n in list(lean_named):
        st, _ = leanparse.split_statement(decls[n]['text'], decls[n]['kw'])
        m = re.match(r'^\s*(?:theorem|lemma)\s+\S+\s*:\s*([A-Za-z_][\w.]*)\s*$', st)
        if m:
            c = leanparse.resolve(m.group(1), decls) or leanparse.resolve('Statement.' + m.group(1), decls)
            if c:
                decls[n]['claim'] = c
                if c not in lean_named:
                    lean_named.append(c)
    lean_cites = {}
    for k, d in decls.items():
        if not d['data']:
            lean_cites[k] = leanparse.cites(d, decls, short_index)
    lean_cited_by = defaultdict(list)
    for k, cs in lean_cites.items():
        for c in cs:
            lean_cited_by[c].append(k)

    comp_rows = computations_table(strip_body(TEX), tex)

    figs = figmod.extract(PDF, OUT / 'proofmap_figs', [f['number'] for f in data['figures']])
    tex.figpages = set(figs)
    fig_by_num = {f['number']: f for f in data['figures'] if f['number'] in figs}
    figs_of = defaultdict(list)     # result -> figures: those it cites, and those placed inside it or its proof
    for r in results:
        if not r['label']:
            continue
        for f in fig_by_num.values():
            if (f['label'] in r['refs']) or r['pos'] <= f['pos'] <= r['proof_end']:
                figs_of[r['label']].append(f['number'])

    # result info
    info = {}
    for r in results:
        if not r['label']:
            continue
        l = r['label']
        has_lean = any(not row['kind'].startswith('definitions') for row in lean_rows[l])
        if r['env'] == 'computation':
            status = 'computed'
        elif l == 'thm:smkgs':
            status = 'cited'
        else:
            status = 'argued'
        title = r['title']
        short = plain(title) if title else notes['labels'].get(l, '')
        if l == 'thm:smkgs':
            short = 'The spectre hierarchy'
        info[l] = {'env': r['env'], 'status': status, 'lean': has_lean, 'lean_part': l in notes['lean_part'],
                   'head': '%s %s' % (r['kind'], r['number']), 'short': short,
                   'abbr': '%s %s' % (ABBR.get(r['kind'], r['kind']) if r['env'] != 'mainthm' else r['kind'],
                                      r['number']),
                   'plain': '%s %s%s' % (r['kind'], r['number'], (' (%s)' % short) if short else '')}

    off = notes.get('off_graph', {})
    graph_nodes = [r['label'] for r in results if r['env'] in texparse.GRAPH_ENVS and r['label'] and r['label'] not in off]
    gset = set(graph_nodes)
    uses = {l: [x for x in R[l]['refs'] if x in gset] for l in graph_nodes}
    used_by = defaultdict(list)
    for l in R:
        for x in R[l]['refs']:
            if x in R:
                used_by[x].append(l)
    linked = [l for l in graph_nodes if uses[l] or any(l in uses[k] for k in graph_nodes)]
    loose = [l for l in graph_nodes if l not in linked]
    order = {r['label']: k for k, r in enumerate(results)}
    lay = layout(linked, {l: uses[l] for l in linked}, lambda n: order[n])
    graph = svg_graph(linked, lay, info)

    # what each result rests on (everything below it in the graph), and one shortest chain of citations from it up to
    # a main theorem (its length is the result's depth)
    below = {}

    def rests_on(n):
        if n not in below:
            s = set()
            for u in uses[n]:
                s.add(u)
                s |= rests_on(u)
            below[n] = s
        return below[n]
    for l in graph_nodes:
        rests_on(l)
    up, todo = {}, []
    for m in ('thm:A', 'thm:B'):
        up[m] = [m]
        todo.append(m)
    while todo:
        v = todo.pop(0)
        for u in sorted(uses[v], key=order.get):
            if u not in up:
                up[u] = [u] + up[v]
                todo.append(u)
    steps = sorted((k for k in notes['prove_steps'] if k.isdigit()), key=int)   # step n follows section n of the paper
    step_of = {l: k for k in steps for l in notes['prove_steps'][k]}
    geo = dict(below=below, up=up, step_of=step_of, used_by=used_by, uses=uses)

    # the top of the proof: the two theorems and the results they cite
    top = ['thm:A', 'thm:B']
    top += [u for n in list(top) for u in lay['red'][n] if u not in top]
    top = sorted(top, key=order.get)
    top_lay = layout(top, {n: [u for u in top if u in below[n]] for n in top}, lambda n: order[n], pack=True)
    top_svg = svg_graph(top, top_lay, info, gid='top', label='The top of the proof')
    # each step of the route: its results, with their neighbours in other steps drawn dashed
    step_svgs = {}
    for k in steps:
        S = [l for l in notes['prove_steps'][k] if l in lay['red']]
        if not S:
            continue
        ext = {u for n in S for u in lay['red'][n]} | {v for v in linked for n in S if n in lay['red'][v]}
        ext -= set(S)
        sub = sorted(set(S) | ext, key=order.get)
        sl = layout(sub, {n: [u for u in sub if u in below[n]] for n in sub}, lambda n: order[n])
        step_svgs[k] = svg_graph(sub, sl, info, gid=sanchor(k), ext=ext,
                                 label='How the results of %s depend on each other' % sname(k, notes))
    longest = {}

    def chain_up(n):   # the longest chain of citations from n up to a main theorem (None if there is none)
        if n not in longest:
            if R[n]['env'] == 'mainthm':
                longest[n] = 0
            else:
                ls = [chain_up(v) for v in linked if n in uses[v]]
                ls = [x for x in ls if x is not None]
                longest[n] = 1 + max(ls) if ls else None
        return longest[n]
    lean_lines = sum(len(f.read_text(encoding='utf8').split('\n')) for f in (LEAN / 'SpectreKnot').rglob('*.lean')
                     if 'Data' not in f.parts)
    lean_all = sorted(k for k, d in decls.items() if not d['data'])
    numbers = [
        (len(R), 'numbered results, definitions and remarks in the paper'),
        (len(linked), 'results in the graph'),
        (sum(len(uses[l]) for l in linked), 'citations by number between them'),
        (max(x for x in map(chain_up, linked) if x is not None), 'longest chain of citations up to a main theorem'),
        (max(len(c) for c in up.values()) - 1, 'greatest depth: shortest chain from a result up to a main theorem'),
        (sum(1 for l in linked if info[l]['status'] == 'computed'), 'finite checks done by program'),
        (sum(1 for l in linked if info[l]['lean']), 'results also checked in Lean, fully or in part'),
        (len(lean_all), 'Lean declarations, each with its own page'),
        (lean_lines, 'lines of Lean, not counting the generated data files'),
    ]

    views = []
    views.append(front_view(R, info, tex, notes, decls, top_svg, steps, numbers))
    views.append(route_view(R, info, tex, notes, steps))
    for k in steps:
        views.append(step_view(k, R, info, tex, notes, steps, step_svgs.get(k), geo, lean_rows))
    views.append(graph_view(R, info, graph, loose, off, linked, geo, notes, order))
    views.append(index_view(results, info, sec_title, lean_rows, data['figures'], tex))
    for r in results:
        if r['label']:
            views.append(result_view(r, R, info, tex, notes, lean_rows, decls, used_by, comp_rows, sec_title,
                                     [(fig_by_num[n], figs[n]) for n in figs_of[r['label']]], geo))
    for n, f in sorted(fig_by_num.items()):
        views.append(figure_view(f, figs[n], tex, [l for l in figs_of if n in figs_of[l]], info))
    # every declaration outside the generated data files gets a page
    lean_pages = set(lean_all)
    paper_of = defaultdict(list)
    for lab, rs in lean_rows.items():
        for row in rs:
            for n in row['decls']:
                if lab not in paper_of[n]:
                    paper_of[n].append(lab)
    # which paper results rest on a declaration: those whose named declarations reach it through the names in
    # their proofs (textual, so a guide rather than a certificate)
    rests = defaultdict(list)
    for lab in sorted(paper_of_results(lean_rows), key=lambda l: order_of(results, l)):
        seen, todo = set(), [n for row in lean_rows[lab] for n in row['decls'] if n in decls]
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            seen.add(n)
            todo.extend(lean_cites.get(n, []))
            if decls[n].get('claim'):
                todo.append(decls[n]['claim'])
        for n in seen:
            rests[n].append(lab)
    views.append(lean_index_view(rows, decls, R, info, lean_all, rests, guide))
    for n in lean_all:
        views.append(lean_view(n, decls, lean_cites, lean_cited_by, lean_pages, paper_of, info, rests, guide))
    views.append(about_view(data, decls, lean_all, rows, notes))

    macros = json.dumps({k: v[0] if v[1] == 0 else [v[0], v[1]] for k, v in data['macros'].items() if k != 'code'})
    # the search box: every numbered item of the paper, the steps of the route, every Lean declaration with a page
    search = [['#' + rid(l), 'paper', info[l]['head'], info[l]['short']] for l in sorted(R, key=order.get)]
    search += [['#' + sanchor(k), 'route', 'Step ' + k, notes['route'][k]['title']]
               for k in steps]
    search += [['#' + lid(n), 'Lean', n, decls[n]['file'][len('lean/'):]] for n in lean_all]
    global SEARCH_HINT
    SEARCH_HINT = 'Search %d items of the paper, %d Lean names\u2026' % (len(R), len(lean_all))
    page = (TEMPLATE.replace('%MACROS%', macros).replace('%VIEWS%', '\n'.join(views)).replace('%PMCSS%', PM_CSS)
            .replace('%STATUS%', status_box()).replace('%FONTS%', FONTS)
            .replace('%SEARCH%', json.dumps(search, ensure_ascii=False).replace('</', '<\\/')))
    OUT.mkdir(exist_ok=True)
    gparts = build_guide.prerender_parts(build_guide.assemble(guide), OUT)
    guide_html = build_guide.fill(build_guide.assemble(
        guide, title=GUIDE_TITLE, head=FONTS, css=PM_CSS + GUIDE_CSS, top=map_header(MAP_FILE, current='statement') + PM_H_SCRIPT,
        foot=FOOTER), gparts)
    # the artifact (its main page is served as index.html): MathJax from a public CDN, the guide beside it
    art = page.replace('%MATHJAX%', MATHJAX_CDN).replace('%HEADER%', map_header('')).replace('%FOOTER%', FOOTER)
    (OUT / 'proofmap-artifact.html').write_text(art.replace('<!--BODY-->', ''), encoding='utf8')
    (OUT / 'artifact-statement.html').write_text(guide_html, encoding='utf8')
    # the website: index.html and statement.html, MathJax served from the site, the figures and the downloads
    www = Path(site_dir) if site_dir else OUT / 'site'
    write_site(page, www, guide_html)
    write_addresses(R, info, notes, linked)
    print('proof map: %d results (%d in the graph, %d not cited by number), %d Lean pages, %d KB; '
          'Statement.lean guide: %d items; site in %s' % (len(R), len(linked), len(loose), len(lean_all),
                                                          len(page.encode()) // 1024, len(guide['guide']['items']),
                                                          www.relative_to(ROOT) if www.is_relative_to(ROOT) else www))


PROOF_BASE = 'https://cortado-j.github.io/SPECTRE_KNOT_PROOF/'   # this site, once the owner turns on Pages
PUBLIC_BASE = 'https://cortado-j.github.io/SPECTRE_KNOT/'        # the public site (pictures, ideas, Prove)
MAP_FILE = 'index.html'          # the map
STATEMENT_FILE = 'statement.html'   # the line-by-line guide to Statement.lean, beside it
GUIDE_TITLE = 'Statement.lean, line by line · The Spectre Knot: the proof'
HEAD = ('<!doctype html>\n<html lang="en-GB">\n<head>\n<meta charset="utf-8">\n'
        '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n')
TAIL = '\n</body>\n</html>\n'
FONTS = ('<link rel="preconnect" href="https://fonts.googleapis.com">\n'
         '<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n'
         '<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Source+Serif+4:ital,opsz,wght@0,8..60,400;'
         '0,8..60,600;1,8..60,400&family=Source+Sans+3:wght@400;600;700&family=JetBrains+Mono:wght@400;600&display=swap">')
MATHJAX_CDN = 'https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-svg-full.js'
MATHJAX_LOCAL = 'assets/mathjax/tex-svg-full.js'
NAV_ITEMS = [('map', 'Overview'), ('route', 'Route'), ('graph', 'Graph'), ('results', 'Results'), ('lean', 'Lean'),
             ('statement', 'Statement.lean'), ('about', 'About')]
SEARCH_HINT = 'Search by name\u2026'   # set by build() with the counts
FOOTER = ('<footer class="pm-foot"><div class="in"><p>The tile is the straight-edged form of the spectre, discovered in '
          '2023 by David Smith, Joseph Samuel Myers, Craig&nbsp;S. Kaplan and Chaim Goodman&#8209;Strauss. The knot: '
          'Justin Roughley came up with the original idea of looking for a mono&#8209;stranded aperiodic knot, and then '
          'used AI to search for it (2026). <a href="%sabout.html#licence">Licence and contact</a>.</p></div></footer>'
          % PUBLIC_BASE)


def map_nav(base, current=None):
    """The map's navigation. `base` is '' inside the map (hash links) or the map's file name from another page; the
    line-by-line guide is its own page."""
    links = []
    for k, t in NAV_ITEMS:
        href = STATEMENT_FILE if k == 'statement' else '%s#%s' % (base, k)
        cur = ' aria-current="page"' if k == current else ''
        links.append('<a href="%s"%s%s>%s</a>' % (href, '' if k == 'statement' else ' data-nav="%s"' % k, cur, t))
    return '<nav class="pm-nav" aria-label="The proof">%s</nav>' % ''.join(links)


def map_header(base, current=None):
    """The top bar: brand, navigation, the search box (on the map itself, where the views it finds are), and the
    link to the public site."""
    search = ('<div class="pm-search" role="search"><input id="pm-q" type="search" placeholder="%s" autocomplete="off" '
              'spellcheck="false" aria-label="Search the results and the Lean declarations"><div id="pm-qr" hidden>'
              '</div></div>' % esc(SEARCH_HINT)) if base == '' else ''
    return ('<header class="pm-top"><div class="in"><a class="pm-brand" href="%s#map"><b>The Spectre Knot</b> '
            '<span>the proof</span></a>%s%s<a class="pm-public" href="%s">Pictures and ideas &rarr;</a></div></header>'
            % (base, map_nav(base, current), search, PUBLIC_BASE))


def write_site(page, www, guide_html):
    """The proof site: index.html (the map) and statement.html (the guide), MathJax served from the site, the
    figures, and the paper and code as downloads."""
    www.mkdir(parents=True, exist_ok=True)
    html_ = page.replace('%MATHJAX%', MATHJAX_LOCAL).replace('%HEADER%', map_header('')).replace('%FOOTER%', FOOTER)
    html_ = html_.replace('<title>Spectre Knot Proof Map</title>', '<title>The Spectre Knot: the proof</title>\n'
                          '<meta name="description" content="Every numbered result of the proof that the Spectre Knot is '
                          'one endless strand: statement, proof, what it rests on, and the Lean that formalises it.">', 1)
    (www / MAP_FILE).write_text(HEAD + html_.replace('<!--BODY-->', '</head>\n<body>') + TAIL, encoding='utf8')
    (www / STATEMENT_FILE).write_text(guide_html, encoding='utf8')
    (www / 'assets' / 'mathjax').mkdir(parents=True, exist_ok=True)
    for f in ('tex-svg-full.js', 'LICENSE'):
        shutil.copy(ROOT / 'vendor' / 'mathjax' / f, www / 'assets' / 'mathjax' / f)
    figs = www / 'proofmap_figs'
    if figs.exists():
        shutil.rmtree(figs)
    if (OUT / 'proofmap_figs').exists():
        shutil.copytree(OUT / 'proofmap_figs', figs)
    dl = www / 'downloads'
    dl.mkdir(exist_ok=True)
    shutil.copy(PDF, dl / 'The-Spectre-Knot-paper.pdf')
    # the proof's programs and logs as code/..., and the Lean formalisation as lean/..., from the files git knows
    # about; fixed dates, so the zip only changes when they do
    files = subprocess.run(['git', 'ls-files', '--cached', 'paper/code', 'lean'], cwd=ROOT, capture_output=True,
                           text=True, check=True).stdout.split()
    with zipfile.ZipFile(dl / 'The-Spectre-Knot-proof-code.zip', 'w', zipfile.ZIP_DEFLATED) as z:
        for f in sorted(files):
            info = zipfile.ZipInfo(f[len('paper/'):] if f.startswith('paper/code/') else f, (2026, 1, 1, 0, 0, 0))
            info.external_attr = (0o755 if f.endswith('.sh') else 0o644) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, (ROOT / f).read_bytes())
    (www / '.nojekyll').write_text('')


def write_addresses(R, info, notes, linked):
    """addresses.json at the top of the repo: every result's address on this site, its marks, and the step of the
    public site's Prove page it belongs to. The public site's build reads it (a copy is kept in SPECTRE_KNOT_DEV) and
    fails if it links to an address that is not here."""
    step_of = {}
    for k, labels in notes['prove_steps'].items():
        if not k.startswith('_'):
            for l in labels:
                step_of[l] = int(k)
    res = {}
    for l, r in R.items():
        i = info[l]
        res[l] = {'url': '%s#%s' % (PROOF_BASE, rid(l)), 'kind': r['kind'], 'number': r['number'],
                  'name': i['short'], 'status': i['status'] if r['env'] in texparse.GRAPH_ENVS else None,
                  'lean': i['lean'], 'lean_part': i['lean_part'], 'step': step_of.get(l)}
    out = {'_about': 'Written by proofmap/build.py in SPECTRE_KNOT_PROOF. The addresses of the proof site that the '
                     'public site may link to.',
           'base': PROOF_BASE, 'statement': PROOF_BASE + STATEMENT_FILE,
           'paper': PROOF_BASE + 'downloads/The-Spectre-Knot-paper.pdf',
           'code': PROOF_BASE + 'downloads/The-Spectre-Knot-proof-code.zip',
           'steps': {k: v for k, v in notes['prove_steps'].items() if not k.startswith('_')}, 'results': res}
    (ROOT / 'addresses.json').write_text(json.dumps(out, ensure_ascii=False, indent=1) + '\n', encoding='utf8')


# the top bar and footer
PM_CSS = """
.pm-top { position: sticky; top: env(safe-area-inset-top, 0px); z-index: 10; background: color-mix(in srgb, var(--surf) 94%, transparent); backdrop-filter: blur(6px); -webkit-backdrop-filter: blur(6px); border-bottom: 1px solid var(--line); font-family: var(--font); }
.pm-top .in, .pm-foot .in { max-width: 1120px; margin: 0 auto; padding: 10px 20px; display: flex; flex-wrap: wrap; gap: 8px 14px; align-items: center; }
.pm-brand { color: var(--ink); text-decoration: none; font-family: var(--serif); font-size: 1.12rem; }
.pm-brand span { color: var(--mint); }
.pm-nav { display: flex; gap: 0; flex-wrap: wrap; }
.pm-nav a { color: var(--mut); text-decoration: none; padding: 5px 9px; border-radius: 6px; font-weight: 600; font-size: .93rem; }
.pm-nav a:hover { color: var(--ink); background: var(--surf2); }
.pm-nav a[aria-current="page"] { color: var(--mint); background: var(--surf2); }
.pm-public { font-size: .9rem; color: var(--mint); text-decoration: none; border: 1px solid var(--line); border-radius: 6px; padding: 4px 10px; }
.pm-public:hover { background: var(--surf2); }
.pm-brand b { font-weight: 400; }
.pm-search { position: relative; flex: 1 1 150px; min-width: 150px; max-width: 340px; }
.pm-search input { width: 100%; padding: 6px 10px; border: 1px solid var(--line); border-radius: 6px; font: .9rem var(--font); background: var(--surf); color: var(--ink); }
.pm-search input:focus { outline: 2px solid var(--mint); outline-offset: 0; }
#pm-qr { position: absolute; top: calc(100% + 4px); left: 0; right: 0; min-width: 300px; background: var(--surf); border: 1px solid var(--line); border-radius: 8px; max-height: 70vh; overflow: auto; box-shadow: 0 8px 24px rgba(0,0,0,.12); z-index: 30; }
#pm-qr a { display: block; padding: 6px 10px; border-bottom: 1px solid var(--bg2); color: var(--ink); text-decoration: none; font: .9rem/1.35 var(--font); }
#pm-qr a:hover, #pm-qr a.on { background: var(--surf2); }
#pm-qr a .k { display: inline-block; font-size: .66rem; text-transform: uppercase; letter-spacing: .05em; color: #fff; background: var(--mint); border-radius: 3px; padding: 0 5px; margin-right: 6px; vertical-align: 1px; }
#pm-qr a .k.Lean { background: var(--leanink); }
#pm-qr a .k.route { background: var(--sky); }
#pm-qr a .s { color: var(--mut); font-size: .8rem; margin-left: 6px; }
#pm-qr a code { background: none; padding: 0; font-size: .82rem; word-break: break-all; }
#pm-qr p { padding: 8px 10px; margin: 0; color: var(--mut); font: .85rem var(--font); }
.pm-foot { border-top: 1px solid var(--line); margin-top: 40px; color: var(--faint); font: .88rem/1.5 var(--font); }
.pm-foot .in { padding-block: 22px 36px; }
.pm-foot p { max-width: 90ch; }
"""

# the guide in this site's colours: its own light theme, for every viewer (the site is light only)
PM_H_SCRIPT = """<script>(function () {   // the map bar's height, for the guide's bar and rail below it (GUIDE_CSS)
  var top = document.querySelector('.pm-top'), root = document.documentElement;
  function set() { root.style.setProperty('--pm-h', top.offsetHeight + 'px'); }
  set();
  if (window.ResizeObserver) new ResizeObserver(set).observe(top); else window.addEventListener('resize', set);
})();</script>"""

GUIDE_CSS = """
:root:root:root {
  --bg: #f8f9f7; --surface: #ffffff; --sunk: #f0f3f1; --code-bg: #f7f9f8; --ink: #1d2622; --ink-2: #4d5b55; --ink-3: #77847e;
  --rule: #d3dcd7; --rule-2: #e3e9e6; --accent: #1f6a4c; --accent-ink: #ffffff; --accent-soft: #e8f0eb;
  --kw: #9b3a70; --ty: #00698f; --val: #7a4f00; --num: #9a4a00; --com: #66736e; --def: #0b5ea8; --loc: #5b4a9a; --sym: #36423e;
  --ok: #0067a3; --ok-soft: #e3eff8; --note: #8f5600; --note-soft: #fbf0dc; --data: #833d89; --data-soft: #f4e7f5;
  --tile: #fff3c4; --tile-2: #fdeeb2; --tile-edge: #33302a; --hook: #009e73; --xr: #d55e00; --xl: #0072b2;
  --rib: #a6dcc4; --rib-edge: #0b6b4e; --mark: #e69f00; --flash: #ffe7a3;
  --surf: #ffffff; --surf2: #e8f0eb; --line: #d3dcd7; --mut: #4d5b55; --faint: #77847e; --mint: #1f6a4c;
  --font: "Source Sans 3", "Segoe UI", system-ui, sans-serif; --serif: "Source Serif 4", Georgia, serif;
  --font-ui: var(--font); color-scheme: light;
}
/* the map's bar stays on top, as on every other page; the guide's own bar and contents rail sit just below it
   (--pm-h, the map bar's height, is measured by PM_H_SCRIPT). On a phone only the map's bar stays. */
:root { --pm-h: 50px; }
.pm-top { z-index: 30; }
.bar { top: calc(env(safe-area-inset-top, 0px) + var(--pm-h)); }
.rail { top: calc(env(safe-area-inset-top, 0px) + var(--pm-h) + var(--bar-h)); height: calc(100vh - var(--pm-h) - var(--bar-h)); }
html { scroll-padding-top: calc(var(--pm-h) + var(--bar-h) + 12px); }
.ln { scroll-margin-top: calc(var(--pm-h) + var(--bar-h) + 40px); }
@media (max-width: 820px) {
  .bar { position: static; }
  html { scroll-padding-top: calc(var(--pm-h) + 12px); }
  .ln { scroll-margin-top: calc(var(--pm-h) + 40px); }
}
.hero h2 { font-family: var(--font-prose); font-weight: 400; }   /* quiet headings, as on the map */
"""


def paper_of_results(lean_rows):
    return [l for l, rs in lean_rows.items() if any(not r['kind'].startswith('definitions') for r in rs)]


def order_of(results, label):
    return next(k for k, r in enumerate(results) if r['label'] == label)


def strip_body(path):
    return texparse.strip_comments(Path(path).read_text(encoding='utf8'))


def chips(i, big=False):
    s = '<span class="st %s">%s</span>' % ({'argued': 'proved'}.get(i['status'], i['status']), STATUS_WORD[i['status']])
    if i['lean']:
        s += ' <span class="st lean%s">%s</span>' % (' part' if i['lean_part'] else '',
                                                      'Lean, in part' if i['lean_part'] else 'Lean')
    return '<span class="chips">%s</span>' % s


def rlink_head(l, info):
    return '<a href="#%s">%s</a>' % (rid(l), esc(info[l]['head']))


def rlink(l, info):
    i = info[l]
    return '<a href="#%s">%s</a>%s' % (rid(l), esc(i['head']), (' <span class="mut">%s</span>' % esc(i['short']))
                                         if i['short'] else '')


def counts(labels, R, info):
    """'3 results, 2 definitions · 2 in Lean' for a step of the route."""
    res = [l for l in labels if R[l]['env'] in texparse.GRAPH_ENVS]
    other = defaultdict(int)
    for l in labels:
        if R[l]['env'] not in texparse.GRAPH_ENVS:
            other[R[l]['kind'].lower()] += 1
    parts = ['%d result%s' % (len(res), '' if len(res) == 1 else 's')] if res else []
    parts += ['%d %s%s' % (n, k, '' if n == 1 else 's') for k, n in sorted(other.items())]
    lean = sum(1 for l in res if info[l]['lean'])
    return ', '.join(parts) + (' &middot; %d in Lean' % lean if lean else '')


def sanchor(k):
    """A step's page on this site: #s1 … #s10."""
    return 's%s' % k


def panchor(k):
    """The same step on the public site's Prove page: #p1 … #p10."""
    return 'p%s' % k


def sname(k, notes):
    return '%s. %s' % (k, notes['route'][k]['title'])


def route_cards(R, info, notes, steps):
    return '<div class="cards">%s</div>' % ''.join(
        '<div class="card rcard"><h3><span class="stage-num">%s</span><a href="#%s">%s</a></h3><p class="num">%s</p></div>'
        % (k, sanchor(k), esc(notes['route'][k]['title']),
           counts(notes['prove_steps'][k], R, info) or 'no results of its own') for k in steps)


def meta_line(l, R, geo, decls=None):
    """The numbers under a result: what it rests on, what it cites, what cites it, its depth."""
    cites = [x for x in R[l]['refs'] if x in R]
    parts = []
    if l in geo['below']:
        n = len(geo['below'][l])
        parts.append('rests on %d result%s' % (n, '' if n == 1 else 's'))
    parts.append('cites %d' % len(cites))
    parts.append('cited by %d' % len(geo['used_by'].get(l, [])))
    if l in geo['up']:
        parts.append('depth %d' % (len(geo['up'][l]) - 1))
    return ' &middot; '.join(parts)


def thm_card(l, R, info, tex, geo):
    r = R[l]
    i = info[l]
    tags = chips(i) if r['env'] in texparse.GRAPH_ENVS else '<span class="st other">%s</span>' % r['kind'].lower()
    return ('<div class="thm-card"><p class="tc-head"><a href="#%s"><b>%s</b>%s</a> %s</p><div class="tc-st">%s</div>'
            '<p class="meta">%s</p></div>' % (
                rid(l), esc(i['head']), (' %s' % esc(i['short'])) if i['short'] else '', tags, tex.block(r['statement']),
                meta_line(l, R, geo)))


def front_view(R, info, tex, notes, decls, top_svg, steps, numbers):
    a, b = R['thm:A'], R['thm:B']
    claim = lambda r, name: (
        '<div class="pm-claim"><p class="ctop"><a href="#%s"><b>Theorem %s</b> &middot; %s</a> %s</p>'
        '<div class="claimst">%s</div></div>' % (rid(r['label']), r['number'], name, chips(info[r['label']]),
                                                  tex.block(r['statement'])))
    mains = ['Statement.theoremA_strand', 'Statement.theoremB_strand']
    lean_st = '\n'.join(leanparse.split_statement(decls[n]['text'], decls[n]['kw'])[0].strip() for n in mains)
    notshown = md_block(leanparse.readme_section(README, 'What it does not show'))
    nums = ''.join('<div><b>{:,}</b><span>{}</span></div>'.format(n, t) for n, t in numbers)
    claims = (lid('Statement.TheoremA_strand'), lid('Statement.TheoremB_strand'))
    return '''<section class="view" id="v-map" data-view="map">
<div class="hero">
<div class="hero-l">
  <h1>The Spectre Knot theorems, proved</h1>
  <p class="lede">A reader&rsquo;s guide to the proof that the Spectre Knot has no closed loop in any spectre tiling whose supertiles fill the plane, and is one endless strand in the nest tiling: what is proved, by which route, and how the results of the paper hang together. Every result has a page with its statement and proof from the paper, what it cites, what cites it, and the Lean that formalises it.</p>
  %s%s
  <p class="small">In Lean 4, the two main theorems. Their claims, <a href="#%s"><code>TheoremA_strand</code></a> and <a href="#%s"><code>TheoremB_strand</code></a>, are written out in the statement file in a combinatorial form, with patches described by which edges are glued:</p>
  <pre class="lean hero-lean">%s</pre>
  <p class="small">The build, <code>lean/build.sh</code>, runs <code>#print axioms</code> on the main theorems (<code>lean/Axioms.lean</code>) and fails unless the answer is among Lean&rsquo;s standard three, <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>: no <code>sorryAx</code>, no <code>Lean.ofReduceBool</code>.</p>
  <p class="small">That actual spectre tilings are glued as the formal statements assume is argued in the paper, not formalised: <a href="#notcovered">what the Lean does not cover</a>.</p>
  %%STATUS%%
  <p class="badges"><a class="badge root" href="#%s">Theorem A&rsquo;s page &rarr;</a> <a class="badge root" href="#%s">Theorem B&rsquo;s page &rarr;</a> <a class="badge" href="#route">the route, step by step</a> <a class="badge" href="#graph">the graph</a> <a class="badge" href="downloads/The-Spectre-Knot-paper.pdf">the paper (PDF)</a> <a class="badge" href="%s">Statement.lean, line by line</a></p>
</div>
<figure class="figure topfig"><div class="figsvg">%s</div><figcaption>The top of the proof. Premises above conclusions: an arrow runs from a result to one whose proof cites it, possibly through results not drawn here. Click any card; <a href="#graph">the whole graph</a>.</figcaption></figure>
</div>
<h2 class="sh">The route</h2>
<p class="gl">The proof climbs the supertile hierarchy. First it shows that every supertile, of every kind and level, looks the same from outside; then it follows the ribbons up the nest. Step 1 sets out the two theorems and the method; steps 2&ndash;7 prove the Daedalus Theorem; steps 8 and 9 add the Ariadne Theorem; step 10 says what is covered. The ten steps are those of the public site&rsquo;s <a href="%sprove.html">Prove page</a>, which explains each with pictures, and step <i>n</i> follows section <i>n</i> of the paper.</p>
<p class="badges"><a class="badge root" href="#route">The route: ten steps, each with its results &rarr;</a></p>
<h2 class="sh">The numbers</h2>
<div class="numbers-grid">%s</div>
<h2 class="sh" id="notcovered">What the Lean checks, and what it does not</h2>
<div class="grid2">
<div class="card"><h3 class="ch">What it checks</h3>
<div class="md small"><p>The Lean formalisation proves the results marked <span class="st lean">Lean</span> about patches described by which edges are glued: every supertile has the signature (%s), every strand of a chain of supertiles covering the plane is two-way infinite (%s), and the nest tiling is one two-way infinite strand, with the paper&rsquo;s bounds (%s). Its kernel also re-runs the finite computations these use.</p>
<p>Its statement file, <code>lean/SpectreKnot/Statement.lean</code>, holds every definition the main theorems use, so whether the right thing has been proved comes down to reading it: <a href="%s">line by line</a>.</p></div></div>
<div class="card"><h3 class="ch">What it does not cover</h3>
<p class="small mut">From <code>lean/README.md</code>.</p>
<div class="md small">%s</div></div>
</div>
<h2 class="sh">How to use these pages</h2>
<ul class="md howto">
<li><b>Search</b> (in the top bar) matches any part of a result&rsquo;s number or name, or of a Lean declaration&rsquo;s name.</li>
<li>A <b>result&rsquo;s page</b> shows its statement and proof as the paper gives them, what it cites and what cites it, one shortest chain of citations up to a main theorem, the Lean declarations that formalise it, the programs that compute it, and the step of the public site&rsquo;s Prove page that explains it with pictures.</li>
<li>The <a href="#route">route</a> takes the proof in ten steps, each with the statements of its results and a small graph; the <a href="#graph">graph</a> shows all the results at once, with a table; <a href="#results">Results</a> lists everything numbered in the paper, in its order.</li>
<li><a href="#lean">Lean</a> lists the paper-to-Lean table and every declaration, each with its own page; <a href="%s">Statement.lean</a> reads the statement file line by line.</li>
<li>Marks: <span class="st proved">argued</span> proved in words in the paper; <span class="st computed">computed</span> a finite check done by program; <span class="st cited">cited</span> from the spectre paper; <span class="st lean">Lean</span> also checked by the Lean proof assistant (<span class="st lean part">Lean, in part</span> where it checks part). <i>Rests on</i> counts everything below a result in the graph; <i>depth</i> is the length of a shortest chain of citations from it up to Theorem A or B.</li>
</ul>
</section>''' % ((claim(a, 'the Daedalus Theorem'), claim(b, 'the Ariadne Theorem')) + claims + (
                  lean_html(lean_st), rid('thm:A'), rid('thm:B'), STATEMENT_FILE, top_svg, PUBLIC_BASE,
                  nums, rlink_head('thm:signature', info), rlink_head('thm:A', info),
                  rlink_head('thm:B', info), STATEMENT_FILE, notshown, STATEMENT_FILE))


def method_tex():
    """The paper's 'The method' (in its introduction), as LaTeX."""
    return strip_body(TEX).split('\\subsection*{The method}', 1)[1].split('\\subsection*', 1)[0]


def route_view(R, info, tex, notes, steps):
    return ('<section class="view" id="v-route" data-view="route" hidden>'
            '<nav class="crumbs small"><a href="#map">Overview</a></nav>'
            '<div class="pm-hero"><h1>The route of the proof, step by step</h1>'
            '<p class="lede">The ten steps of the public site&rsquo;s <a href="%sprove.html">Prove page</a>, one page '
            'each, with the exact statements of the results each step is made of and how they depend on each other. '
            'Step <i>n</i> follows section <i>n</i> of the paper. Step 1 sets out the two theorems and the method; '
            'steps 2&ndash;7 prove the Daedalus Theorem; steps 8 and 9 add the Ariadne Theorem; step 10 says what is '
            'covered. The one-sentence summaries are a paraphrase, written by the AI; where they and the paper differ, '
            'the paper is right. The method, as the paper&rsquo;s introduction states it, is on '
            '<a href="#s1">step 1&rsquo;s page</a>.</p></div>%s'
            '</section>' % (PUBLIC_BASE, route_cards(R, info, notes, steps)))


def step_nav(k, steps, notes):
    i = steps.index(k)
    prev = ('<a href="#%s">&larr; %s</a>' % (sanchor(steps[i - 1]), esc(sname(steps[i - 1], notes)))
            if i else '<a href="#route">&larr; The route</a>')
    nxt = ('<a href="#%s">%s &rarr;</a>' % (sanchor(steps[i + 1]), esc(sname(steps[i + 1], notes)))
           if i + 1 < len(steps) else '<a href="#route">The route &rarr;</a>')
    return '<p class="small stepnav">%s<span>%s</span></p>' % (prev, nxt)


def step_view(k, R, info, tex, notes, steps, svg, geo, lean_rows):
    labels = notes['prove_steps'][k]
    rt = notes['route'][k]
    parts = ['<section class="view" id="v-%s" data-view="%s" hidden>' % (sanchor(k), sanchor(k)),
             '<nav class="crumbs small"><a href="#map">Overview</a> &rsaquo; <a href="#route">Route</a></nav>',
             '<div class="pm-hero"><h1>%s</h1><p class="lede">%s</p>'
             '<p class="small mut">A paraphrase, written by the AI; the statements below are the paper&rsquo;s.</p>'
             '<p class="small pub"><a href="%sprove.html#%s">Explained with pictures: %s &rarr;</a></p>'
             '</div>' % (esc(sname(k, notes)), tex.inline(rt['summary']), PUBLIC_BASE, panchor(k),
                         'step %s of the Prove page' % k),
             step_nav(k, steps, notes)]
    if svg:
        parts.append('<h2 class="sh">How the results of this step depend on each other</h2>'
                     '<p class="small mut gl">Solid cards are the results of this step; dashed cards are results of '
                     'neighbouring steps they connect to. Premises above conclusions; an arrow may pass through results '
                     'not drawn here. Click a card for its page.</p><div class="graphbox">%s</div>' % svg)
    if labels:
        parts.append('<h2 class="sh">The results of this step <span class="mut small">(%s)</span></h2>'
                     % counts(labels, R, info))
        parts += [thm_card(l, R, info, tex, geo) for l in labels]
    else:   # step 1, the paper's introduction: the two theorems (proved in steps 7 and 9) and the method
        parts.append('<h2 class="sh">The two theorems</h2><p class="small mut gl">As the paper&rsquo;s introduction '
                     'states them; they are proved in steps 7 and 9.</p>')
        parts += [thm_card(l, R, info, tex, geo) for l in ('thm:A', 'thm:B')]
        parts.append('<h2 class="sh">The method, as the paper&rsquo;s introduction states it</h2>'
                     '<div class="prose method">%s</div>' % tex.block(method_tex()))
    parts.append(step_nav(k, steps, notes))
    parts.append('</section>')
    return '\n'.join(parts)


def graph_view(R, info, graph, loose, off, linked, geo, notes, order):
    below = []
    if loose:
        below.append('Not cited by number in any statement or proof: %s.' % ', '.join(rlink(l, info) for l in loose))
    for l, why in off.items():
        why = re.sub(r'\{([a-z]+:[\w-]+)\}', lambda m: '<a href="#%s">%s</a>' % (rid(m.group(1)), esc(info[m.group(1)]['head'])), esc(why))
        below.append('Not drawn: %s, %s.' % (rlink(l, info), why))
    rows = []
    for l in sorted(linked, key=order.get):
        st = geo['step_of'].get(l)
        rows.append('<tr><td>%s</td><td>%s</td><td class="n">%d</td><td class="n">%s</td><td>%s</td></tr>' % (
            rlink(l, info), '<a href="#%s">%s</a>' % (sanchor(st), st) if st else '&ndash;', len(geo['below'][l]),
            len(geo['up'][l]) - 1 if l in geo['up'] else '&ndash;', chips(info[l])))
    return '''<section class="view" id="v-graph" data-view="graph" hidden>
<nav class="crumbs small"><a href="#map">Overview</a></nav>
<div class="pm-hero"><h1>The results and how they depend on each other</h1>
<p class="lede">The %d results of the paper that the argument is made of. Premises above, conclusions below; click a result for its page.</p></div>
<div class="legend">
  <span><span class="st proved">argued</span> proved in words in the paper</span>
  <span><span class="st computed">computed</span> a finite check done by program</span>
  <span><span class="st cited">cited</span> from the spectre paper</span>
  <span><span class="st lean">Lean</span> also checked by the Lean proof assistant (<span class="st lean part">Lean&frac12;</span> in part)</span>
</div>
<p class="mut small gl">An arrow runs from a result to one whose statement or proof cites it by number; an arrow is left out when a longer chain of arrows already joins the two. Each result&rsquo;s page lists everything it cites, including definitions, remarks and tables. Uses described only in words are not drawn. Wider than the screen: scroll sideways. The <a href="#route">route</a> pages carry one smaller graph per step.</p>
<div class="graphbox" tabindex="0">%s</div>
%s
<h2 class="sh">The results as a table</h2>
<p class="small mut gl"><i>Step</i>: the step of the route. <i>Rests on</i>: the results below it in the graph. <i>Depth</i>: the length of a shortest chain of citations from it up to Theorem A or B.</p>
<div class="tablebox"><table class="lt"><thead><tr><th>result</th><th>step</th><th>rests on</th><th>depth</th><th>marks</th></tr></thead><tbody>%s</tbody></table></div>
</section>''' % (len(linked), graph, ''.join('<p class="mut small gl">%s</p>' % t for t in below), ''.join(rows))


def index_view(results, info, sec_title, lean_rows, figures, tex):
    out = ['<section class="view" id="v-results" data-view="results" hidden><div class="pm-hero">'
           '<h1>All numbered results</h1><p class="lede">In the paper&rsquo;s order. Definitions and remarks are included; '
           'the graph shows only the results the argument is made of.</p></div><div class="idx">']
    cur = None
    for r in results:
        if not r['label']:
            continue
        sec = r['section'].split('.')[0] if r['section'] else ''
        if sec != cur:
            if cur is not None:
                out.append('</ul>')
            out.append('<h2 class="sh">&sect;%s %s</h2><ul class="rl">' % (sec, esc(plain(sec_title.get(sec, '')))))
            cur = sec
        i = info[r['label']]
        tags = chips(i) if r['env'] in texparse.GRAPH_ENVS else '<span class="st other">%s</span>' % r['kind'].lower()
        out.append('<li>%s %s</li>' % (rlink(r['label'], info), tags))
    out.append('</ul>')
    figs = [f for f in figures if f['number'] in tex.figpages]
    if figs:
        out.append('<h2 class="sh">Figures</h2><ul class="rl">%s</ul>' % ''.join(
            '<li><a href="#f-%d">Figure %d</a> <span class="mut">%s</span></li>' % (
                f['number'], f['number'], esc(plain(f['caption']).split('. ')[0][:90])) for f in figs))
    out.append('</div></section>')
    return '\n'.join(out)


def result_view(r, R, info, tex, notes, lean_rows, decls, used_by, comp_rows, sec_title, rfigs, geo):
    l = r['label']
    i = info[l]
    title = tex.inline(r['title']) if r['title'] else ''
    sec = r['section'] or ''
    step = geo['step_of'].get(l)
    crumbs = '<a href="#map">Overview</a> &rsaquo; ' + (
        '<a href="#route">Route</a> &rsaquo; <a href="#%s">%s</a>' % (sanchor(step), esc(sname(step, notes)))
        if step else '<a href="#results">Results</a>')
    parts = ['<section class="view" id="v-%s" data-view="%s" hidden>' % (rid(l), rid(l)),
             '<nav class="crumbs small">%s</nav>' % crumbs,
             '<div class="rhead"><h1><span class="num">%s %s</span>%s</h1>%s</div>' % (
                 r['kind'], r['number'], (' <span class="ttl">%s</span>' % title) if title else '',
                 chips(i) if r['env'] in texparse.GRAPH_ENVS else ''),
             '<p class="small mut src">Paper &sect;%s %s, line %d of <code>spectre_knot.tex</code> &middot; %s</p>' % (
                 esc(sec), esc(plain(sec_title.get(sec, sec_title.get(sec.split('.')[0], '')))), r['line'],
                 meta_line(l, R, geo))]
    if l in geo['up'] and len(geo['up'][l]) > 1:
        chain = list(reversed(geo['up'][l]))
        parts.append('<nav class="path small" aria-label="Up to a main theorem">%s</nav>' % (
            ' <span class="sep">&rarr;</span> '.join(
                '<span class="here">%s</span>' % esc(info[x]['head']) if x == l else
                '<a href="#%s">%s</a>' % (rid(x), esc(info[x]['head'])) for x in reversed(chain))
            + ' <span class="mut">&middot; one shortest chain of citations up to %s</span>' % (
                'Theorem A' if chain[0] == 'thm:A' else 'Theorem B')))
    if step:
        parts.append('<p class="small pub"><a href="%sprove.html#%s">Explained with pictures: %s &rarr;</a></p>' % (
            PUBLIC_BASE, panchor(step), 'step %s of the Prove page' % step))
    if l in notes['notes']:
        parts.append('<aside class="ainote"><p class="kick">Reading aid, written by the AI</p><p>%s</p>'
                     '<p class="small mut">The paper&rsquo;s statement and proof below are the text of record.</p>'
                     '</aside>' % tex.inline(notes['notes'][l]))
    parts.append('<h2 class="sh">Statement</h2><div class="stmt">%s</div>' % tex.block(r['statement']))
    for p in r['proofs']:
        ptitle = tex.inline(p['title']) if p['title'] else 'Proof'
        parts.append('<h2 class="sh">%s</h2><div class="proof">%s<span class="qed">&#8718;</span></div>' % (
            ptitle, tex.block(p['tex'])))
    if not r['proofs'] and r['env'] == 'computation':
        parts.append('<p class="mut">The paper gives no proof in words: this is a finite check, done by the programs below.</p>')
    if rfigs:
        parts.append('<h2 class="sh">Figure%s</h2>' % ('s' if len(rfigs) > 1 else ''))
        for f, img in rfigs:
            parts.append(fig_html(f, img, tex))
    # neighbourhood: cites / cited by
    cites = [x for x in r['refs'] if x in R]
    other = [x for x in r['refs'] if x not in R]
    ub = used_by.get(l, [])
    col = lambda ls: ''.join('<li>%s</li>' % rlink(x, info) for x in ls) or '<li class="mut">none</li>'
    parts.append('<h2 class="sh">Where it sits</h2><div class="nbr"><div><p class="kick">Cites</p><ul>%s</ul>%s</div>'
                 '<div class="me"><p class="kick">This</p><p><b>%s</b></p></div>'
                 '<div><p class="kick">Cited by</p><ul>%s</ul></div></div>' % (
                     col(cites), ('<p class="small mut">Also cites %s.</p>' % ', '.join(tex.refname(x, False) for x in other))
                     if other else '', esc(i['head']), col(ub)))
    # Lean
    if lean_rows.get(l):
        rows_html = []
        for row in lean_rows[l]:
            ds = ''.join(lean_card(n, decls) for n in row['decls'] if n in decls)
            rows_html.append('<div class="leanrow"><p class="small"><b>%s</b> &middot; %s</p><p>%s</p>%s</div>' % (
                md_inline(row['paper']), md_inline(row['kind']), md_inline(row['what']), ds))
        part = ('<p class="small mut">What the Lean covers here: %s</p>' % tex.inline(notes['lean_part'][l])) \
            if l in notes['lean_part'] else ''
        parts.append('<h2 class="sh">In Lean</h2>%s<p class="small mut">From the paper-to-Lean table of '
                     '<code>lean/README.md</code>; statements quoted from the Lean files.</p>%s' % (part, ''.join(rows_html)))
    elif r['env'] in texparse.GRAPH_ENVS:
        parts.append('<h2 class="sh">In Lean</h2><p class="mut">Not formalised.%s</p>' % (
            ' It is part of the link to real tilings, assumption (M).' if l in ('thm:smkgs', 'lem:rigid',
                                                                               'prop:nestwell', 'prop:nesttiling',
                                                                               'con:nest') else ''))
    if comp_rows.get(l):
        lis = ''.join('<li><p>%s</p><p class="small mut">%s</p></li>' % (c['what'], c['scripts']) for c in comp_rows[l])
        parts.append('<h2 class="sh">Computed by</h2><p class="small mut">From the paper&rsquo;s table '
                     '&ldquo;What was computed&rdquo;. Scripts are in <code>paper/code/</code>, their logs in '
                     '<code>paper/code/logs/</code>.</p><ul class="comp">%s</ul>' % lis)
    parts.append('</section>')
    return '\n'.join(parts)


def fig_html(f, img, tex, big=False):
    return ('<figure class="pm-fig%s"><a href="#f-%d" class="figimg"><img src="proofmap_figs/%s" width="%d" height="%d" '
            'alt="Figure %d of the paper" loading="lazy"></a><figcaption><b>Figure %d.</b> %s</figcaption></figure>' % (
                ' big' if big else '', f['number'], img['file'], img['w'], img['h'], f['number'], f['number'],
                tex.inline(f['caption'])))


def figure_view(f, img, tex, users, info):
    return ('<section class="view" id="v-f-%d" data-view="f-%d" hidden>'
            '<nav class="crumbs small"><a href="#map">Overview</a> &rsaquo; <a href="#results">Results</a></nav>'
            '<div class="rhead"><h1><span class="num">Figure %d</span></h1></div>'
            '<p class="small mut src">Paper, page %d; cut from the built PDF</p>%s'
            '<h2 class="sh">Shown with</h2><ul class="ll">%s</ul></section>' % (
                f['number'], f['number'], f['number'], img['page'], fig_html(f, img, tex, True),
                ''.join('<li>%s</li>' % rlink(l, info) for l in users) or '<li class="mut">no numbered result</li>'))


def lean_card(n, decls):
    d = decls[n]
    st, _ = leanparse.split_statement(d['text'], d['kw'])
    lines = st.split('\n')
    if len(lines) > 14:
        st = '\n'.join(lines[:14]) + '\n  …'
    return ('<div class="lcard"><p class="small"><a href="#%s"><code>%s</code></a> <span class="mut">%s, line %d</span></p>'
            '<pre class="lean">%s</pre>%s</div>' % (lid(n), esc(n), esc(d['file']), d['line'], lean_html(st),
                                                    claim_html(d, decls)))


def claim_html(d, decls):
    """For `theorem foo : Claim`, the claim itself, from the statement file."""
    c = d.get('claim')
    if not c:
        return ''
    cd = decls[c]
    return ('<details class="claimdef"><summary>The claim <code>%s</code> (%s, line %d)</summary>'
            '<pre class="lean">%s</pre></details>' % (esc(c), esc(cd['file']), cd['line'], lean_html(cd['text'])))


def lean_index_view(rows, decls, R, info, lean_all, rests, guide):
    out = ['<section class="view" id="v-lean" data-view="lean" hidden><div class="pm-hero">'
           '<h1>The Lean formalisation</h1><p class="lede">%d declarations in %d files, each with its own page. First the '
           'rows of the paper-to-Lean table in <code>lean/README.md</code>, then every declaration, file by file.</p>'
           '</div><div class="card guidecard"><h2 class="ch">Statement.lean, line by line</h2><p>The statement file holds every '
           'definition the main theorems use, and the theorems themselves as claims: whether the right thing has been '
           'proved comes down to reading it. <a href="%s">The line-by-line reading</a> shows all %d lines beside a plain '
           'reading of each piece, in %d pieces.</p></div><h2 class="sh">By result of the paper</h2><div class="tablebox"><table class="lt"><thead>'
           '<tr><th>paper</th><th>Lean</th><th>kind</th></tr></thead><tbody>' % (
               len(lean_all), len({decls[n]['file'] for n in lean_all}), STATEMENT_FILE, guide['n_lines'],
               len(guide['guide']['items']))]
    for row in rows:
        names = ', '.join('<a href="#%s"><code>%s</code></a>' % (lid(n), esc(n)) if n in decls else
                          '<code>%s</code>' % esc(n) for n in row['decls'])
        out.append('<tr><td>%s</td><td>%s</td><td>%s</td></tr>' % (md_inline(row['paper']), names,
                                                                   md_inline(row['kind'])))
    out.append('</tbody></table></div><h2 class="sh">By file</h2><p class="small mut">In file order. The figure after '
               'each name counts the paper results that rest on it (see a declaration&rsquo;s page). '
               '<span class="kw">thm</span> marks theorems and lemmas.</p><div class="files">')
    by_file = defaultdict(list)
    for n in lean_all:
        by_file[decls[n]['file']].append(n)
    for f in sorted(by_file, key=lambda f: (f.count('/'), f)):
        ns = sorted(by_file[f], key=lambda n: decls[n]['line'])
        lis = ''.join('<li><a href="#%s"><code>%s</code></a>%s%s</li>' % (
            lid(n), esc(n), ' <span class="kw">thm</span>' if decls[n]['kw'] in ('theorem', 'lemma') else '',
            ' <span class="cnt" title="paper results resting on it">%d</span>' % len(rests[n]) if rests.get(n) else '')
            for n in ns)
        out.append('<details class="file"><summary><code>%s</code> <span class="mut small">%d</span></summary>'
                   '<ul class="ll">%s</ul></details>' % (esc(f), len(ns), lis))
    out.append('</div></section>')
    return '\n'.join(out)


def lean_view(n, decls, cites, cited_by, pages, paper_of, info, rests, guide):
    d = decls[n]
    st, body = leanparse.split_statement(d['text'], d['kw'])
    link = lambda k: ('<a href="#%s"><code>%s</code></a>' % (lid(k), esc(k)) if k in pages else
                      '<code>%s</code> <span class="mut small">%s:%d</span>' % (esc(k), esc(decls[k]['file']),
                                                                              decls[k]['line']))
    cs = cites.get(n, [])
    cb = cited_by.get(n, [])
    lst = lambda ks: '<ul class="ll">%s</ul>' % ''.join('<li>%s</li>' % link(k) for k in ks[:60]) + (
        '<p class="small mut">and %d more</p>' % (len(ks) - 60) if len(ks) > 60 else '') if ks else '<p class="mut">none</p>'
    parts = ['<section class="view" id="v-%s" data-view="%s" hidden>' % (lid(n), lid(n)),
             '<nav class="crumbs small"><a href="#map">Overview</a> &rsaquo; <a href="#lean">Lean</a></nav>',
             '<div class="rhead"><h1><code class="lname">%s</code></h1></div>' % esc(n),
             '<p class="small mut src">%s in <code>%s</code>, line %d</p>' % (d['kw'], esc(d['file']), d['line'])]
    if paper_of.get(n):
        parts.append('<p>Formalises %s.</p>' % ', '.join(rlink(l, info) for l in paper_of[n]))
    under = [l for l in rests.get(n, []) if l not in paper_of.get(n, [])]
    if under:
        parts.append('<p class="small">Used, through the names in proofs, for %s.</p>' % ', '.join(
            '<a href="#%s">%s</a>' % (rid(l), esc(info[l]['head'])) for l in under))
    if d['file'].endswith('SpectreKnot/Statement.lean'):
        item = build_guide.item_at(guide, d['line'])
        if item:
            parts.append('<p class="small">In the statement file: <a href="%s#item-%s">read it line by line</a>.</p>' % (
                STATEMENT_FILE, item))
    if d['doc']:
        parts.append('<h2 class="sh">Doc comment</h2><div class="md">%s</div>' % md_block(d['doc']))
    parts.append('<h2 class="sh">Statement</h2><pre class="lean">%s</pre>' % lean_html(st))
    if d.get('claim'):
        parts.append('<p>The claim it proves: %s.</p>' % link(d['claim']))
    parts.append('<div class="grid2"><div><h2 class="sh">Names in its proof</h2>%s</div>'
                 '<div><h2 class="sh">Named in the proofs of</h2>%s</div></div>' % (lst(cs), lst(cb)))
    parts.append('<p class="small mut">Read from the Lean text, not from Lean: a project declaration counts when its '
                 'name is written in the proof, in full, relative to the enclosing namespace or to an <code>open</code>, or '
                 'as field notation <code>x.foo</code> when <code>foo</code> names exactly one declaration. A guide, '
                 'not a certificate: a name used through notation, an instance or a tactic is missed.</p>')
    if body is not None:
        lines = body.split('\n')
        parts.append('<details><summary>The proof (%d lines)</summary><pre class="lean">%s</pre></details>' % (
            len(lines), lean_html(body)))
    parts.append('</section>')
    return '\n'.join(parts)


def about_view(data, decls, lean_all, rows, notes):
    n_thm = sum(1 for v in decls.values() if v['kw'] in ('theorem', 'lemma'))
    return '''<section class="view" id="v-about" data-view="about" hidden><div class="pm-hero">
<h1>About this map</h1></div><div class="prose">
<p>This site is generated by <code>proofmap/build.py</code> from the sources, so it changes when they change:</p>
<ul class="md">
<li>statements and proofs: the paper&rsquo;s LaTeX, <code>paper/tex/spectre_knot.tex</code>, converted for the web; the numbers are checked against the built PDF, and the build stops if they differ;</li>
<li>what a result cites: the references by number (<code>\\cref</code>) in its statement and proof;</li>
<li>the Lean declarations of a result: the paper-to-Lean table in <code>lean/README.md</code> (%d rows); the Lean statements are quoted from the Lean files (%d declarations read, %d of them theorems);</li>
<li>the computations: the paper&rsquo;s table &ldquo;What was computed&rdquo;;</li>
<li>the figures: cut from the built PDF, <code>paper/spectre_knot.pdf</code>, with their captions from the LaTeX;</li>
<li>written by hand, in <code>proofmap/notes.json</code>: short labels for %d untitled results, what part of %d results the Lean covers, and %d reading aids; which results make up each step of the route (the ten steps of the public site&rsquo;s Prove page), with a title and a one-sentence summary for each step. The reading aids and the summaries were written by the AI and are labelled where they appear.</li>
<li>the numbers on the overview, the depths and the chains of citations up to a main theorem: counted from the above when the site is built.</li>
</ul>
<p>The layout follows the reader&rsquo;s guide to the Lean proof of Fermat&rsquo;s Last Theorem (tianyipeng.github.io/fermats-last-theorem): an overview with the statement and the top of the proof, the route step by step, the graph with a table, a page for every result and every declaration, and a search box.</p>
<p>Lean dependencies are read from the text, not from Lean itself: a declaration counts as named in a proof when its name is written there, in full, relative to the enclosing namespace or to an <code>open</code>, or as field notation <code>x.foo</code> when <code>foo</code> names exactly one declaration. Names used only through notation, instances or tactics are missed. No Lean was run to make this page.</p>
<p>Mathematics is typeset in the browser by MathJax.</p>
</div></section>''' % (len(rows), len(decls), n_thm, len(notes['labels']), len(notes['lean_part']), len(notes['notes']))


TEMPLATE = r'''<title>Spectre Knot Proof Map</title>
%FONTS%
<style>
/* Layout: a reading room, after the reader's guide to the Lean proof of Fermat's Last Theorem: a quiet top bar,
   serif reading text in one column, results as cards, a wide scrolling graph. Light only, by choice.
   Colours: status words carry the meaning; colour (Okabe-Ito based) only repeats it. */
:root {
  --bg: #f8f9f7; --bg2: #f0f3f1; --surf: #ffffff; --surf2: #e8f0eb; --ink: #1d2622; --mut: #4d5b55; --faint: #77847e;
  --line: #d3dcd7; --edge: #98a69f;
  --mint: #1f6a4c; --amber: #b0540b; --sky: #0067a3; --pink: #a3497d; --yellow: #F0E442; --leanink: #6b6200;
  --font: "Source Sans 3", "Segoe UI", system-ui, -apple-system, Roboto, sans-serif;
  --serif: "Source Serif 4", "Iowan Old Style", "Palatino Linotype", Georgia, serif;
  --mono: "JetBrains Mono", ui-monospace, "DejaVu Sans Mono", Menlo, Consolas, monospace;
  --r: 10px; --max: 1120px; --read: 760px; color-scheme: light;
}
* { box-sizing: border-box; }
[hidden] { display: none !important; }
html { background: var(--bg); }
body { margin: 0; background: var(--bg); color: var(--ink); font-family: var(--serif); font-size: 17.5px; line-height: 1.62; }
nav, .st, .kick, .legend, .crumbs, .small, .chips, button, summary, table.lt, .nbr, .files { font-family: var(--font); }
a { color: var(--mint); text-underline-offset: 3px; text-decoration-thickness: 1px; }
a:hover { color: #134a35; }
:focus-visible { outline: 3px solid var(--sky); outline-offset: 3px; border-radius: 4px; }
h1, h2, h3 { line-height: 1.18; margin: 0; text-wrap: balance; font-weight: 600; letter-spacing: -0.005em; font-family: var(--serif); }
h1 { font-size: clamp(1.65rem, 3.6vw, 2.1rem); font-weight: 400; letter-spacing: -0.01em; }
p { margin: 0; }
code, pre { font-family: var(--mono); font-size: .86em; }
code { background: var(--surf2); border-radius: 5px; padding: 1px 5px; }
.kick { font-size: .74rem; letter-spacing: .14em; text-transform: uppercase; color: var(--mint); font-weight: 700; }
.lede { color: var(--mut); font-size: 1.1rem; max-width: 62ch; }
.mut { color: var(--mut); }
.small { font-size: .88rem; }
%PMCSS%
main { max-width: var(--max); margin: 0 auto; padding: 0 20px 80px; }
.view { display: grid; gap: 18px; padding-top: 34px; }
.pm-hero { display: grid; gap: 12px; padding-bottom: 6px; }
.hero { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); gap: 28px; align-items: start; }
@media (max-width: 980px) { .hero { grid-template-columns: 1fr; } }
.hero-l { display: grid; gap: 12px; min-width: 0; }
.hero .pm-claim { padding: 12px 16px; gap: 6px; }
.hero .claimst { font-size: 1rem; line-height: 1.55; }
.ctop { font-family: var(--font); font-size: .95rem; display: flex; flex-wrap: wrap; gap: 4px 10px; align-items: center; }
.ctop a { text-decoration: none; }
.ctop a:hover { text-decoration: underline; }
pre.hero-lean { border: 1.5px solid var(--mint); background: var(--surf); font-size: .85rem; white-space: pre-wrap; }
.hero .status { padding: 0; border: 0; background: none; }
.hero .status p { font-size: .88rem; color: var(--mut); font-family: var(--font); }
.badges { display: flex; flex-wrap: wrap; gap: 6px; font-family: var(--font); }
.badge { display: inline-block; font-size: .8rem; border-radius: 999px; padding: 2px 11px; border: 1px solid var(--edge); background: var(--surf2); color: var(--ink); text-decoration: none; white-space: nowrap; }
.badge:hover { background: #d7e7dd; color: var(--ink); }
.badge.root { background: var(--mint); border-color: var(--mint); color: #fff; }
.badge.root:hover { background: #134a35; color: #fff; }
.figure { margin: 0; background: var(--surf); border: 1px solid var(--line); border-radius: var(--r); padding: 10px; display: grid; gap: 8px; min-width: 0; }
.figure .figsvg { overflow-x: auto; }
.figure .figsvg svg { display: block; width: 100%; height: auto; }
@media (max-width: 560px) { .figure .figsvg svg { min-width: 480px; } }
.figure figcaption { font: .85rem/1.5 var(--font); color: var(--mut); }
.cards { display: grid; gap: 10px; grid-template-columns: repeat(auto-fill, minmax(min(100%, 250px), 1fr)); }
.rcard { padding: 12px 14px; gap: 4px; }
.rcard h3 { font-size: 1rem; line-height: 1.35; font-weight: 600; }
.rcard h3 a { text-decoration: none; color: var(--ink); }
.rcard h3 a:hover { text-decoration: underline; color: var(--mint); }
.rcard .num { font: .78rem var(--font); color: var(--mut); }
.stage-num { display: inline-block; width: 1.55em; height: 1.55em; line-height: 1.55em; text-align: center; border-radius: 50%; background: var(--mint); color: #fff; font: 700 .8rem/1.55em var(--font); margin-right: .45em; vertical-align: 1px; }
.numbers-grid { display: grid; gap: 10px; grid-template-columns: repeat(auto-fill, minmax(min(100%, 170px), 1fr)); }
.numbers-grid div { background: var(--surf); border: 1px solid var(--line); border-radius: var(--r); padding: 8px 12px; display: grid; }
.numbers-grid b { font: 400 1.45rem var(--serif); color: var(--mint); }
.numbers-grid span { font: .8rem/1.4 var(--font); color: var(--mut); }
ul.howto { max-width: 90ch; }
.thm-card { background: var(--surf); border: 1px solid var(--line); border-left: 4px solid var(--mint); border-radius: 0 var(--r) var(--r) 0; padding: 10px 16px; display: grid; gap: 8px; max-width: var(--read); }
.tc-head { font-family: var(--font); display: flex; flex-wrap: wrap; gap: 4px 10px; align-items: center; }
.tc-head a { text-decoration: none; }
.tc-head a:hover { text-decoration: underline; }
.tc-st { display: grid; gap: 8px; font-size: .97rem; }
.thm-card .meta { font: .78rem var(--font); color: var(--mut); }
nav.path { background: var(--surf); border: 1px solid var(--line); border-radius: 8px; padding: 6px 12px; max-width: var(--read); line-height: 1.8; }
nav.path .sep { color: var(--edge); }
nav.path .here { font-weight: 700; }
.stepnav { display: flex; justify-content: space-between; gap: 12px; flex-wrap: wrap; max-width: var(--read); }
.method { max-width: var(--read); }
table.lt td.n { text-align: right; font-variant-numeric: tabular-nums; }
.graph .node.ext > rect:first-of-type { stroke-dasharray: 5 4; stroke: var(--edge); }
.status { border: 1.5px solid var(--amber); border-radius: var(--r); background: color-mix(in srgb, var(--amber) 9%, var(--surf)); padding: 10px 16px; display: grid; gap: 6px; }
.status h2 { font-size: 1.05rem; }
.status p { max-width: 72ch; }
.pm-claims { display: grid; gap: 14px; grid-template-columns: repeat(auto-fit, minmax(min(100%, 330px), 1fr)); }
.pm-claim { display: grid; gap: 10px; align-content: start; background: var(--surf); border: 1px solid var(--line); border-radius: var(--r); padding: 18px 20px; color: var(--ink); text-decoration: none; }
.pm-claim a.kick { text-decoration: none; }
.pm-claim a.kick:hover { text-decoration: underline; }
.claimst p { color: var(--ink); }
.sh { font-size: 1.25rem; margin-top: 12px; }
.ch { font-size: 1.1rem; }
.legend { display: flex; flex-wrap: wrap; gap: 8px 22px; font-size: .9rem; color: var(--mut); }
.gl { max-width: 90ch; }
.st { font-size: .68rem; letter-spacing: .08em; text-transform: uppercase; border-radius: 999px; padding: 2px 9px; border: 1.5px solid; white-space: nowrap; font-weight: 700; display: inline-block; line-height: 1.4; }
.st.cited { color: var(--amber); border-color: var(--amber); }
.st.computed { color: var(--sky); border-color: var(--sky); }
.st.proved { color: var(--mint); border-color: var(--mint); }
.st.lean { color: var(--ink); background: var(--yellow); border-color: #c9bd1c; }
.st.lean.part { color: var(--leanink); background: transparent; border-color: var(--leanink); border-style: dashed; }
.st.other { color: var(--faint); border-color: var(--line); }
.chips { display: inline-flex; gap: 6px; flex-wrap: wrap; vertical-align: 2px; }
.graphbox { overflow-x: auto; border: 1px solid var(--line); border-radius: var(--r); background: var(--surf); padding: 8px; }
.graph { display: block; max-width: none; }
.graph .edges path { fill: none; stroke: var(--edge); stroke-width: 1.4; transition: stroke .15s, opacity .15s; }
.graph .node rect:first-of-type { fill: var(--surf); stroke-width: 1.6; }
.graph .node.argued > rect:first-of-type { stroke: var(--mint); }
.graph .node.computed > rect:first-of-type { stroke: var(--sky); }
.graph .node.cited > rect:first-of-type { stroke: var(--amber); }
.graph .node.main > rect:first-of-type { fill: #e3efe8; stroke-width: 2.6; }
.graph .node:hover > rect:first-of-type, .graph .node:focus > rect:first-of-type { fill: var(--surf2); }
.graph .nh { fill: var(--ink); font: 700 13.5px var(--font); }
.graph text { font-family: var(--font); }
.graph .nt { fill: var(--mut); font: 500 12px var(--font); }
.graph .chip { fill: none; stroke-width: 1.2; }
.graph .chip.argued { stroke: var(--mint); } .graph .chipt.argued { fill: var(--mint); }
.graph .chip.computed { stroke: var(--sky); } .graph .chipt.computed { fill: var(--sky); }
.graph .chip.cited { stroke: var(--amber); } .graph .chipt.cited { fill: var(--amber); }
.graph .chip.lean { fill: var(--yellow); stroke: #c9bd1c; } .graph .chipt.lean { fill: var(--ink); }
.graph .chip.lean.part { fill: none; stroke: var(--leanink); stroke-dasharray: 3 2; } .graph .chipt.lean.part { fill: var(--leanink); }
.graph .chipt { font: 700 9.5px var(--font); text-anchor: middle; letter-spacing: .04em; text-transform: uppercase; }
.graph.hl .edges path { opacity: .18; }
.graph.hl .edges path.on { opacity: 1; stroke: var(--amber); stroke-width: 2.2; }
.graph.hl .node { opacity: .45; }
.graph.hl .node.on { opacity: 1; }
.grid2 { display: grid; gap: 16px; grid-template-columns: repeat(auto-fit, minmax(min(100%, 340px), 1fr)); }
.grid2 > * { min-width: 0; }
.below { margin-top: 10px; }
.card { background: var(--surf); border: 1px solid var(--line); border-radius: var(--r); padding: 18px 20px; display: grid; gap: 10px; align-content: start; min-width: 0; }
pre.lean { background: var(--bg2); border: 1px solid var(--line); border-radius: 10px; padding: 12px 14px; overflow-x: auto; margin: 0; line-height: 1.5; white-space: pre; color: var(--ink); }
pre.lean .kw { color: var(--sky); font-weight: 600; }
pre.lean .com { color: var(--faint); font-style: italic; }
.md p + p, .md p + ul, .md ul + p { margin-top: 8px; }
ul.md { margin: 0; padding-left: 1.2em; display: grid; gap: 6px; }
.crumbs { color: var(--mut); }
.rhead { display: flex; flex-wrap: wrap; align-items: baseline; gap: 10px 16px; }
.rhead .num { color: var(--amber); margin-right: .35em; }
.rhead .ttl { font-weight: 600; }
.lname { background: none; padding: 0; font-size: clamp(1.1rem, 3vw, 1.6rem); word-break: break-all; }
.src { margin-top: -10px; }
.pub { margin-top: -6px; }
.stmt, .proof, .prose, .ainote, .nbr, .comp, .leanrow, .crumbs, .rhead, .src { max-width: var(--read); }
.stmt { background: var(--surf); border: 1px solid var(--line); border-left: 3px solid var(--mint); border-radius: 0 var(--r) var(--r) 0; padding: 14px 18px; display: grid; gap: 10px; }
.proof { display: grid; gap: 10px; }
.proof .qed { justify-self: end; color: var(--mut); }
.mathd { overflow-x: auto; overflow-y: hidden; padding: 2px 0; }
ul.tl { list-style: none; margin: 0; padding: 0; display: grid; gap: 8px; }
ul.tl li { display: grid; grid-template-columns: 2.4em 1fr; }
ul.tl li .lm { color: var(--mut); }
ul.tl li > div { min-width: 0; }
.cite { color: var(--mut); }
.pref { color: var(--ink); border-bottom: 1px dotted var(--faint); }
.ainote { border: 1.5px dashed var(--pink); border-radius: var(--r); padding: 14px 18px; display: grid; gap: 8px; background: color-mix(in srgb, var(--pink) 6%, var(--bg)); }
.ainote .kick { color: var(--pink); }
.nbr { display: grid; grid-template-columns: 1fr auto 1fr; gap: 12px; align-items: start; }
.nbr > div { background: var(--surf); border: 1px solid var(--line); border-radius: 12px; padding: 12px 14px; min-width: 0; display: grid; gap: 6px; }
.nbr .me { align-self: center; text-align: center; border-color: var(--amber); }
.nbr ul { margin: 0; padding: 0; list-style: none; display: grid; gap: 4px; font-size: .93rem; }
@media (max-width: 620px) { .nbr { grid-template-columns: 1fr; } }
.leanrow { border-top: 1px solid var(--line); padding-top: 12px; display: grid; gap: 8px; }
.lcard { display: grid; gap: 6px; min-width: 0; }
ul.comp { margin: 0; padding-left: 1.1em; display: grid; gap: 10px; }
table.lt { border-collapse: collapse; width: 100%; font-size: .92rem; }
table.lt th, table.lt td { text-align: left; vertical-align: top; padding: 8px 10px; border-bottom: 1px solid var(--line); }
table.lt th { color: var(--mut); font-weight: 650; }
.files { display: grid; gap: 6px; }
.file summary { color: var(--ink); font-weight: 500; }
.file ul { margin: 8px 0 12px; }
.kw { color: var(--sky); font-size: .78rem; font-weight: 700; }
.cnt { display: inline-block; min-width: 1.6em; text-align: center; font-size: .74rem; font-weight: 700; color: var(--ink); background: var(--yellow); border-radius: 999px; padding: 0 6px; }
.tablebox { overflow-x: auto; }
.guidecard { max-width: var(--read); }
.pm-fig { margin: 0; display: grid; gap: 8px; max-width: var(--read); }
.pm-fig.big { max-width: 100%; }
.figimg { display: block; background: #fffdf6; border-radius: 12px; padding: 12px; border: 1px solid var(--line); }
.figimg img { display: block; width: 100%; height: auto; }
.pm-fig.big .figimg img { width: auto; max-width: 100%; margin: 0 auto; }
.pm-fig figcaption { color: var(--mut); font-size: .9rem; }
.idx ul.rl { list-style: none; padding: 0; margin: 8px 0 0; display: grid; gap: 6px; }
ul.ll { margin: 0; padding-left: 1.1em; display: grid; gap: 3px; font-size: .92rem; }
details summary { cursor: pointer; color: var(--mint); font-weight: 650; }
details pre { margin-top: 10px; }
.claimdef summary { font-size: .88rem; }
.prose { display: grid; gap: 12px; }
@media (max-width: 700px) { table.lt { display: block; overflow-x: auto; } }
@media (prefers-reduced-motion: reduce) { * { transition: none !important; } }
</style>
<script>
window.MathJax = { tex: { inlineMath: [['$', '$']], displayMath: [['\\[', '\\]']], processEscapes: true, macros: %MACROS% },
  svg: { fontCache: 'global' }, startup: { typeset: false } };
</script>
<script src="%MATHJAX%" defer></script>
<!--BODY-->
%HEADER%
<main id="main">
%VIEWS%
</main>
%FOOTER%
<script>
(function () {
  var views = {};
  document.querySelectorAll('.view').forEach(function (v) { views[v.dataset.view] = v; });
  var done = new WeakSet();
  function typeset(v) {
    if (done.has(v) || !window.MathJax || !MathJax.typesetPromise) return;
    done.add(v);
    MathJax.typesetPromise([v]).catch(function () { done.delete(v); });
  }
  function show() {
    var h = (location.hash || '#map').slice(1);
    if (!views[h]) h = 'map';
    Object.keys(views).forEach(function (k) { views[k].hidden = (k !== h); });
    var sec = (h.indexOf('r-') === 0 || h.indexOf('f-') === 0) ? 'results' : h.indexOf('lean') === 0 ? 'lean' :
      /^s[0-9]+$/.test(h) ? 'route' : h;
    document.querySelectorAll('[data-nav]').forEach(function (a) {
      if (a.dataset.nav === sec) a.setAttribute('aria-current', 'page'); else a.removeAttribute('aria-current');
    });
    typeset(views[h]);
    window.scrollTo(0, 0);
  }
  window.addEventListener('hashchange', show);
  show();
  document.addEventListener('DOMContentLoaded', function () {
    var t = setInterval(function () {
      if (window.MathJax && MathJax.typesetPromise) { clearInterval(t); show(); }
    }, 100);
  });
  if (document.readyState !== 'loading') document.dispatchEvent(new Event('DOMContentLoaded'));
  // graph: highlight a result's arrows on hover or focus
  document.querySelectorAll('svg.graph').forEach(function (g) {
    var edges = g.querySelectorAll('.edges path');
    function on(n) {
      g.classList.add('hl');
      var keep = {}; keep[n] = 1;
      edges.forEach(function (e) {
        var hit = e.dataset.a === n || e.dataset.b === n;
        e.classList.toggle('on', hit);
        if (hit) { keep[e.dataset.a] = 1; keep[e.dataset.b] = 1; }
      });
      g.querySelectorAll('.node').forEach(function (a) { a.classList.toggle('on', !!keep[a.dataset.n]); });
    }
    function off() { g.classList.remove('hl'); }
    g.querySelectorAll('.node').forEach(function (a) {
      a.addEventListener('mouseenter', function () { on(a.dataset.n); });
      a.addEventListener('focus', function () { on(a.dataset.n); });
      a.addEventListener('mouseleave', off);
      a.addEventListener('blur', off);
    });
  });
  // search: every numbered item of the paper, the steps of the route, and the Lean declarations, by name
  var q = document.getElementById('pm-q'), box = document.getElementById('pm-qr'), INDEX = %SEARCH%, act = -1;
  function hits() {
    var t = q.value.trim().toLowerCase();
    if (!t) return null;
    var out = [];
    INDEX.forEach(function (e) {
      var k = (e[1] === 'Lean' ? e[2] : e[2] + ' ' + e[3]).toLowerCase().indexOf(t);
      if (k >= 0) out.push([e[1] === 'Lean' ? 1 : 0, k, out.length, e]);
    });
    out.sort(function (a, b) { return a[0] - b[0] || a[1] - b[1] || a[2] - b[2]; });
    return out.map(function (x) { return x[3]; });
  }
  function render() {
    var hs = hits();
    act = -1;
    box.textContent = '';
    if (!hs) { box.hidden = true; return; }
    hs.slice(0, 40).forEach(function (e) {
      var a = document.createElement('a'), k = document.createElement('span');
      a.href = e[0];
      k.className = 'k ' + e[1]; k.textContent = e[1];
      a.appendChild(k);
      if (e[1] === 'Lean') { var c = document.createElement('code'); c.textContent = e[2]; a.appendChild(c); }
      else a.appendChild(document.createTextNode(e[2]));
      if (e[3]) { var s = document.createElement('span'); s.className = 's'; s.textContent = e[3]; a.appendChild(s); }
      a.addEventListener('click', close);
      box.appendChild(a);
    });
    if (!hs.length) { var p = document.createElement('p'); p.textContent = 'Nothing matches.'; box.appendChild(p); }
    else if (hs.length > 40) { var m = document.createElement('p'); m.textContent = (hs.length - 40) + ' more: type more of the name.'; box.appendChild(m); }
    box.hidden = false;
  }
  function close() { box.hidden = true; q.value = ''; q.blur(); }
  function mark(d) {
    var as = box.querySelectorAll('a');
    if (!as.length) return;
    act = (act + d + as.length) % as.length;
    as.forEach(function (a, i) { a.classList.toggle('on', i === act); });
    as[act].scrollIntoView({ block: 'nearest' });
  }
  if (q) {
    q.addEventListener('input', render);
    q.addEventListener('focus', render);
    q.addEventListener('keydown', function (ev) {
      if (ev.key === 'ArrowDown') { mark(1); ev.preventDefault(); }
      else if (ev.key === 'ArrowUp') { mark(-1); ev.preventDefault(); }
      else if (ev.key === 'Escape') close();
      else if (ev.key === 'Enter') {
        var as = box.querySelectorAll('a');
        if (as.length) { location.hash = as[Math.max(act, 0)].getAttribute('href'); close(); }
      }
    });
    document.addEventListener('click', function (ev) { if (!ev.target.closest('.pm-search')) box.hidden = true; });
  }
})();
</script>'''


if __name__ == '__main__':
    build(sys.argv[sys.argv.index('--site') + 1] if '--site' in sys.argv else None)
