#!/usr/bin/env python3
"""The line-by-line guide to Statement.lean: Statement.lean, line for line, beside the explanations in content.js.

    python3 lean/guide/build_guide.py          # check content.js against Statement.lean
    python3 proofmap/build.py                  # writes the guide, as a page of the proof map

The guide is a page of the proof map (statement.html); proofmap/build.py calls `load`, `assemble`,
`prerender_parts` and `fill` here. `load` embeds the current SpectreKnot/Statement.lean (and lines 7-20 of Basic.lean,
which hold `Kind` and `iter`) and fails if the items of content.js do not cover every line of the file exactly once, if
an item's clauses do not cover its lines, or if a [[...]] reference is broken. It warns (and the page shows a banner)
if Statement.lean has changed since content.js was written. Needs node, to read content.js.

If Playwright is installed, the page is also rendered once in Chromium and the result is written into the file, so
that viewers that do not run scripts (such as the Claude app's file preview) still show the whole reading; the script
redraws it where scripts run.
"""
import hashlib
import json
import pathlib
import re
import subprocess
import sys

STATIC_NOTE = ('<p class="static-note">Static copy: this viewer has not run the page\'s script, so the pop-ups, the '
               'figures\' clicks and the reading ticks are off. The reading itself is all here.</p>')

HERE = pathlib.Path(__file__).resolve().parent
LEAN = HERE.parent
BASIC_FROM, BASIC_TO = 7, 20  # Kind and iter


def load():
    """Read Statement.lean, content.js, app.js and template.html, and check that the explanations cover every line
    of the file exactly once. Exits with the problems if they do not."""
    src = (LEAN / 'SpectreKnot/Statement.lean').read_text(encoding='utf-8')
    basic_lines = (LEAN / 'SpectreKnot/Basic.lean').read_text(encoding='utf-8').split('\n')
    basic = '\n'.join(basic_lines[BASIC_FROM - 1:BASIC_TO])
    if not basic_lines[BASIC_FROM - 1].startswith('/-- The nine kinds') or not basic_lines[BASIC_TO - 1].startswith('  | n + 1, x'):
        sys.exit('Basic.lean has moved: update BASIC_FROM/BASIC_TO in build_guide.py')
    sha = hashlib.sha256(src.encode('utf-8')).hexdigest()
    n_lines = len(src.rstrip('\n').split('\n'))
    content = (HERE / 'content.js').read_text(encoding='utf-8')

    guide = json.loads(subprocess.run(
        ['node', '-e', 'global.window = {}; require(process.argv[1]); console.log(JSON.stringify(window.GUIDE));',
         str(HERE / 'content.js')], check=True, capture_output=True, text=True).stdout)

    errors = []
    nxt = 1
    ids = {it['id'] for it in guide['items']}
    for it in guide['items']:
        a, b = it['lines']
        if a != nxt:
            errors.append(f"item {it['id']} starts at line {a}, expected {nxt}")
        nxt = b + 1
        if 'clauses' in it:
            c0 = a
            for c in it['clauses']:
                if c['lines'][0] != c0:
                    errors.append(f"item {it['id']}: clause starts at {c['lines'][0]}, expected {c0}")
                c0 = c['lines'][1] + 1
            if c0 != b + 1:
                errors.append(f"item {it['id']}: clauses end at {c0 - 1}, item ends at {b}")
    if nxt != n_lines + 1:
        errors.append(f'items end at line {nxt - 1}; Statement.lean has {n_lines} lines')
    for ref in re.findall(r'\[\[([^\]|]+)(?:\|[^\]]+)?\]\]', content[content.index('window.GUIDE'):]):
        m = re.fullmatch(r'L(\d+)', ref)
        if m and not 1 <= int(m.group(1)) <= n_lines:
            errors.append(f'[[{ref}]]: no such line')
        elif not m and ref not in ids:
            errors.append(f'[[{ref}]]: no such item')
    if errors:
        sys.exit('build_guide.py: ' + '\n  '.join(['content.js does not fit Statement.lean:'] + errors))
    if guide['writtenFor'] != sha:
        print('WARNING: Statement.lean has changed since content.js was written; review the explanations, then set '
              f"writtenFor to {sha}", file=sys.stderr)
    return {'src': src, 'sha': sha, 'basic': basic, 'n_lines': n_lines, 'guide': guide, 'content': content,
            'app': (HERE / 'app.js').read_text(encoding='utf-8'),
            'tpl': (HERE / 'template.html').read_text(encoding='utf-8')}


def js(s):  # only a closing script tag would end the inline script early
    return re.sub(r'</(script)', r'<\\/\1', s, flags=re.IGNORECASE)


def assemble(g, title=None, head=None, css='', top='', foot=''):
    """The page: the template with the file, the explanations and the engine filled in. The proof map passes its own
    title, head links (in place of the template's font links), extra CSS, a header to put above the guide's bar and a
    footer."""
    data = 'window.GUIDE_DATA = ' + js(json.dumps(
        {'src': g['src'], 'sha': g['sha'], 'basic': g['basic'], 'basicStart': BASIC_FROM}, ensure_ascii=False)) + ';'
    out = (g['tpl'].replace('/*__DATA__*/', data)
                   .replace('/*__CONTENT__*/', js(g['content']))
                   .replace('/*__APP__*/', js(g['app'])))
    if title:
        out = re.sub(r'<title>.*?</title>', lambda m: '<title>%s</title>' % title, out, count=1)
    if head is not None:
        out, n = re.subn(r'<link rel="preconnect".*?display=swap">\n', lambda m: head + '\n', out, count=1,
                         flags=re.S)
        if n != 1:
            sys.exit('build_guide.py: the font links in template.html have changed')
    for old, new in (('</style>\n</head>', css + '\n</style>\n</head>'), ('<body>\n', '<body>\n' + top + '\n'),
                     ('</body>', foot + '\n</body>')):
        if out.count(old) != 1:
            sys.exit(f'build_guide.py: {old!r} not found once in template.html')
        out = out.replace(old, new)
    return out


def prerender_parts(html, workdir):
    """Render the page once in Chromium and return the drawn parts, for the static copy. None if Playwright is not
    installed."""
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        print('note: Playwright is not installed, so the guide has no static copy (viewers that do not run '
              'scripts will show only a notice)', file=sys.stderr)
        return None
    dest = pathlib.Path(workdir) / '_guide_render.html'
    dest.write_text(html, encoding='utf-8')
    with sync_playwright() as p:
        browser = p.chromium.launch()
        page = browser.new_page(viewport={'width': 1400, 'height': 900})
        errors = []
        page.on('pageerror', lambda e: errors.append(str(e)))
        page.route('http*://**', lambda r: r.abort())   # fonts are not needed for the drawing
        page.goto(dest.resolve().as_uri())
        page.wait_for_selector('article.item')
        parts = page.evaluate("""() => ({
            main: document.getElementById('main').innerHTML, toc: document.getElementById('toc').innerHTML,
            tocm: document.getElementById('toc-m').innerHTML, sha: document.getElementById('src-sha').textContent,
            prog: document.getElementById('prog-n').textContent })""")
        browser.close()
    dest.unlink()
    if errors:
        sys.exit('build_guide.py: the page raised errors in Chromium: ' + '; '.join(errors))
    return parts


def fill(out, parts):
    """Write the drawn parts into the page's static placeholders."""
    if not parts:
        return out
    fills = [
        (re.compile(r'<div id="main">.*?</div>\n    <footer>', re.S), f'<div id="main">{STATIC_NOTE}{parts["main"]}</div>\n    <footer>'),
        ('<div id="toc"></div>', f'<div id="toc">{parts["toc"]}</div>'),
        ('<div id="toc-m"></div>', f'<div id="toc-m">{parts["tocm"]}</div>'),
        ('<span id="src-sha"></span>', f'<span id="src-sha">{parts["sha"]}</span>'),
        ('<span id="prog-n">0 of 0</span>', f'<span id="prog-n">{parts["prog"]}</span>'),
    ]
    for old, new in fills:
        if isinstance(old, str):
            if out.count(old) != 1:
                sys.exit(f'build_guide.py: placeholder {old!r} not found once in template.html')
            out = out.replace(old, new)
        else:
            out, n = old.subn(lambda m: new, out, count=1)
            if n != 1:
                sys.exit('build_guide.py: placeholder <div id="main"> not found in template.html')
    return out


def item_at(g, line):
    """The id of the guide item that covers a line of Statement.lean."""
    for it in g['guide']['items']:
        if it['lines'][0] <= line <= it['lines'][1]:
            return it['id']
    return None


def main():
    g = load()
    print(f'content.js covers Statement.lean: {len(g["guide"]["items"])} items, {g["n_lines"]} lines. '
          'The guide itself is written by python3 proofmap/build.py, as a page of the proof map.')


if __name__ == '__main__':
    main()
