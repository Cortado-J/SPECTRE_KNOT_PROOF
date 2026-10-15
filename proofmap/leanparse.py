"""Read the Lean formalisation as text: every declaration with its doc comment, statement and source position, and
the paper-to-Lean table of `lean/README.md`. No Lean is run; dependencies between declarations are read off the
names written in each proof (see `cites`)."""
import re
from pathlib import Path

DECL_RE = re.compile(r'^(?P<mods>(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*)'
                     r'(?P<kw>theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+(?P<name>[^\s:(\[{]+)')
KEYWORDS = r'\b(theorem|lemma|def|abbrev|structure|inductive|instance|class|where|fun|let|have|show|by|from|at|with|' \
           r'match|if|then|else|do|for|in|open|namespace|end|variable|deriving|Prop|Type|true|false|decide|simp|' \
           r'intro|exact|rfl|omega|cases|induction|rcases|obtain|refine|apply|rw|constructor|use|calc)\b'


def index(lean_root):
    """All declarations under SpectreKnot/ (the generated data files are indexed for names only)."""
    decls = {}
    root = Path(lean_root)
    files = sorted(root.glob('SpectreKnot/**/*.lean')) + [root / 'SpectreKnot.lean']
    for f in files:
        rel = f.relative_to(root.parent).as_posix()
        lines = f.read_text(encoding='utf8').split('\n')
        ns = []
        starts = []
        opens = []
        for n, line in enumerate(lines):
            m = re.match(r'^open\s+(.*)$', line)
            if m:
                opens.extend(x for x in m.group(1).split() if re.match(r'^[A-Z][\w.]*$', x))
            m = re.match(r'^namespace\s+(\S+)', line)
            if m:
                ns.append(m.group(1))
                continue
            m = re.match(r'^end\s+(\S+)\s*$', line)
            if m and ns and ns[-1] == m.group(1):
                ns.pop()
                continue
            m = DECL_RE.match(line)
            if m:
                full = '.'.join(ns + [m.group('name')])
                if full.startswith('SpectreKnot.'):
                    full = full[len('SpectreKnot.'):]
                starts.append((n, full, m.group('kw')))
        for k, (n, full, kw) in enumerate(starts):
            # the declaration runs to the next declaration, doc comment or top-level command
            stop = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
            j = n + 1
            while j < stop:
                s = lines[j]
                if re.match(r'^(/--|/-|namespace\b|end\b|section\b|open\b|variable\b|#|@\[|attribute\b|set_option\b|'
                            r'--)', s) and not s.startswith('  '):
                    break
                j += 1
            text = '\n'.join(lines[n:j]).rstrip()
            doc = None
            d = n - 1
            while d >= 0 and lines[d].strip() == '':
                d -= 1
            if d >= 0 and lines[d].rstrip().endswith('-/'):
                e = d
                while e >= 0 and '/--' not in lines[e] and '/-' not in lines[e]:
                    e -= 1
                if e >= 0 and '/--' in lines[e]:
                    doc = '\n'.join(lines[e:d + 1])
                    doc = re.sub(r'^\s*/--\s?', '', doc)
                    doc = re.sub(r'\s*-/\s*$', '', doc).strip()
            decls[full] = {'name': full, 'kw': kw, 'file': rel, 'line': n + 1, 'text': text, 'doc': doc,
                           'data': '/Data/' in rel, 'opens': [o[len('SpectreKnot.'):] if o.startswith('SpectreKnot.')
                                                              else o for o in opens]}
    return decls


def split_statement(text, kw):
    """The statement: for a theorem, everything before the first ':=' at bracket depth 0."""
    if kw not in ('theorem', 'lemma', 'instance'):
        return text, None
    depth = 0
    i = 0
    while i < len(text) - 1:
        c = text[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif c == ':' and text[i + 1] == '=' and depth == 0:
            line = text[text.rfind('\n', 0, i) + 1:i]
            if not re.match(r'\s*(let|have)\b', line):   # a `let x := …` inside the statement is not the proof
                return text[:i].rstrip(), text[i + 2:].strip()
        i += 1
    return text, None


def resolve(name, decls):
    """A name as the README writes it (possibly without its namespace) -> the indexed declaration's full name."""
    if name in decls:
        return name
    hits = [k for k in decls if k.endswith('.' + name)]
    return hits[0] if len(hits) == 1 else None


def cites(decl, decls, short_index):
    """Project declarations whose names occur in the body (textual, like an import list). A name counts if it is
    written in full, relative to the declaration's namespace or one of its parents, or to a namespace the file opens;
    a dotted name `x.foo` that resolves no other way counts when `foo` names exactly one declaration (field
    notation). Comments are skipped."""
    stmt, body = split_statement(decl['text'], decl['kw'])
    src = body if body is not None else decl['text'].split('\n', 1)[-1]
    src = re.sub(r'/-.*?-/', ' ', src, flags=re.S)
    src = re.sub(r'--[^\n]*', ' ', src)
    ns = decl['name'].split('.')[:-1]
    prefixes = ['.'.join(ns[:k]) for k in range(len(ns), -1, -1)] + decl.get('opens', [])
    found = []
    for tok in set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", src)):
        tok = tok.rstrip('.')
        cand = None
        for pre in prefixes:
            full = (pre + '.' + tok) if pre else tok
            if full in decls:
                cand = full
                break
        if cand is None and '.' in tok:
            hits = [k for k in short_index.get(tok.split('.')[-1], []) if not decls[k]['data']]
            if len(hits) == 1:
                cand = hits[0]
        if cand and cand != decl['name'] and not decls[cand]['data'] and cand not in found:
            found.append(cand)
    return sorted(found)


# How a row's Lean statement differs from the paper's: the first words of the README table's last column.
DIFFERS = ('same', 'stronger', 'weaker', 'part', 'other form', 'not in the paper')


def readme_table(readme_path):
    """Rows of the README's 'What is formalised' table: paper column, Lean names, kind, description, and how the Lean
    statement differs from the paper's. Stops unless every row has the five cells and its last says how it differs
    (one of DIFFERS, then any detail), so that a row cannot pair a result with a weaker statement without saying so."""
    text = Path(readme_path).read_text(encoding='utf8')
    sec = text.split('## What is formalised', 1)[1].split('\n## ', 1)[0]
    rows = []
    for line in sec.split('\n'):
        if not line.startswith('|') or line.startswith('|---') or line.startswith('| paper'):
            continue
        cells = [c.strip() for c in line.strip().strip('|').split(' | ')]
        if len(cells) != 5:
            raise SystemExit('lean/README.md, "What is formalised": a row with %d cells, not 5 (paper, Lean, kind, what '
                             'it says, how it differs from the paper): %s' % (len(cells), line[:100]))
        paper, lean, kind, what, differs = cells
        if not re.match(r'(%s)(:|$)' % '|'.join(DIFFERS), differs):
            raise SystemExit('lean/README.md, "What is formalised": the row for "%s" does not say how it differs from the '
                             'paper (its last cell must start with one of: %s)' % (paper, ', '.join(DIFFERS)))
        rows.append({'paper': paper, 'lean': re.findall(r'`([^`]+)`', lean), 'kind': kind, 'what': what,
                     'differs': differs})
    return rows


def readme_section(readme_path, heading):
    text = Path(readme_path).read_text(encoding='utf8')
    return text.split('## ' + heading, 1)[1].split('\n## ', 1)[0].strip()


PAPER_REF = re.compile(r'\b(Theorem|Thm|Lemma|Prop|Proposition|Cor|Corollary|Comp|Computation|Def|Definition|Remark)\s+'
                       r'([0-9]+\.[0-9]+|[AB])\b')
KIND_OF = {'Thm': 'Theorem', 'Theorem': 'Theorem', 'Lemma': 'Lemma', 'Prop': 'Proposition',
           'Proposition': 'Proposition', 'Cor': 'Corollary', 'Corollary': 'Corollary', 'Comp': 'Computation',
           'Computation': 'Computation', 'Def': 'Definition', 'Definition': 'Definition',
           'Remark': 'Remark'}


def paper_refs(cell):
    """('Lemma', '5.1') pairs named in a README paper cell (bold markers removed)."""
    cell = cell.replace('**', '')
    return [(KIND_OF[k], n) for k, n in PAPER_REF.findall(cell)]
