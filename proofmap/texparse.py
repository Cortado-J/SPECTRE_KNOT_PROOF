"""Read the paper's LaTeX: numbered results, their statements and proofs, and what each proof cites.

Numbering follows amsart as the paper sets it up: one counter, reset by each section, shared by every theorem-like
environment; Theorems A and B on their own counter; figures, tables and equations numbered straight through.
`check_numbers` compares the numbers with the built PDF, so a change to the paper that this parser misreads fails
the build instead of mislabelling the map.
"""
import re
import subprocess
from pathlib import Path

RESULT_ENVS = {
    'theorem': 'Theorem', 'lemma': 'Lemma', 'proposition': 'Proposition', 'corollary': 'Corollary',
    'mainthm': 'Theorem', 'definition': 'Definition', 'construction': 'Construction',
    'computation': 'Computation', 'remark': 'Remark', 'example': 'Example',
}
# What the graph shows: the results the argument is made of (definitions, remarks and examples are listed on the
# pages that use them, not drawn).
GRAPH_ENVS = {'theorem', 'lemma', 'proposition', 'corollary', 'mainthm', 'construction', 'computation'}

REF_RE = re.compile(r'\\(cref|Cref|ref|eqref)\{([^}]*)\}')


def strip_comments(tex):
    out = []
    for line in tex.split('\n'):
        m = re.search(r'(?<!\\)%', line)
        out.append(line[:m.start()] if m else line)
    return '\n'.join(out)


def read_group(s, i, open_ch='{', close_ch='}'):
    """s[i] is open_ch; return (content, index after the matching close_ch). Braces nest inside brackets."""
    assert s[i] == open_ch, (s[i:i + 40], open_ch)
    depth, j = 0, i
    brace = 0
    while j < len(s):
        c = s[j]
        if c == '\\':
            j += 2
            continue
        if open_ch == '[':
            if c == '{':
                brace += 1
            elif c == '}':
                brace -= 1
            elif c == '[' and brace == 0:
                depth += 1
            elif c == ']' and brace == 0:
                depth -= 1
                if depth == 0:
                    return s[i + 1:j], j + 1
        else:
            if c == open_ch:
                depth += 1
            elif c == close_ch:
                depth -= 1
                if depth == 0:
                    return s[i + 1:j], j + 1
        j += 1
    raise ValueError('unbalanced group at %d' % i)


def find_env_end(s, env, i):
    """Index of the \\end{env} closing the environment whose body starts at i (no nesting of the same env)."""
    k = s.find('\\end{%s}' % env, i)
    if k < 0:
        raise ValueError('no \\end{%s}' % env)
    return k


def parse(tex_path):
    raw = Path(tex_path).read_text(encoding='utf8')
    tex = strip_comments(raw)
    pre, body = tex.split('\\begin{document}', 1)
    body_offset = len(pre) + len('\\begin{document}')

    macros = {}
    for m in re.finditer(r'\\newcommand\{\\(\w+)\}(?:\[(\d)\])?\{', pre):
        content, _ = read_group(pre, m.end() - 1)
        macros[m.group(1)] = (content, int(m.group(2) or 0))

    token = re.compile(r'\\appendix|\\(section|subsection)(\*?)\{|\\begin\{(\w+\*?)\}|\\label\{([^}]*)\}')
    sec_num = 0
    sub_num = 0
    appendix = False
    thm = 0
    main = 0
    fig = tab = eq = 0
    labels = {}       # label -> dict(kind, number)
    results = []      # in order
    figures = []
    env_stack = []    # (env, end index) for figure/table/equation/result, to attach labels
    sections = []
    i = 0
    while True:
        m = token.search(body, i)
        if not m:
            break
        pos = m.start()
        env_stack = [e for e in env_stack if e[1] > pos]
        if m.group(0) == '\\appendix':
            appendix = True
            sec_num = 0
            i = m.end()
            continue
        if m.group(1):
            title, end = read_group(body, m.end() - 1)
            if m.group(2) != '*':
                if m.group(1) == 'section':
                    sec_num += 1
                    sub_num = 0
                    thm = 0
                else:
                    sub_num += 1
                sec = chr(64 + sec_num) if appendix else str(sec_num)
                num = sec if m.group(1) == 'section' else '%s.%d' % (sec, sub_num)
                sections.append({'kind': m.group(1), 'number': num, 'title': title, 'pos': pos})
                env_stack.append(('section', len(body), num))
            i = end
            continue
        if m.group(3):
            env = m.group(3)
            if env in RESULT_ENVS:
                k = m.end()
                title = None
                if k < len(body) and body[k] == '[':
                    title, k = read_group(body, k, '[', ']')
                end = find_env_end(body, env, k)
                if env == 'mainthm':
                    main += 1
                    number = chr(64 + main)
                else:
                    thm += 1
                    sec = chr(64 + sec_num) if appendix else str(sec_num)
                    number = '%s.%d' % (sec, thm)
                lab = re.match(r'\s*\\label\{([^}]*)\}', body[k:])
                label = lab.group(1) if lab else None
                stmt_start = k + (lab.end() if lab else 0)
                r = {'env': env, 'kind': RESULT_ENVS[env], 'number': number, 'title': title, 'label': label,
                     'statement': body[stmt_start:end].strip(), 'pos': pos, 'end': end + len('\\end{%s}' % env),
                     'section': sections[-1]['number'] if sections else None, 'proofs': []}
                results.append(r)
                if label:
                    labels[label] = {'type': 'result', 'name': r['kind'], 'number': number}
                i = stmt_start
                continue
            if env in ('figure', 'figure*'):
                fig += 1
                fend = find_env_end(body, env, m.end())
                env_stack.append(('figure', fend, str(fig)))
                inner = body[m.end():fend]
                cm = re.search(r'\\caption\{', inner)
                cap = read_group(inner, cm.end() - 1)[0] if cm else ''
                lm = re.search(r'\\label\{([^}]*)\}', inner)
                figures.append({'number': fig, 'caption': cap.strip(), 'label': lm.group(1) if lm else None,
                                'pos': pos})
            elif env in ('table', 'table*'):
                tab += 1
                env_stack.append(('table', find_env_end(body, env, m.end()), str(tab)))
            elif env in ('equation', 'align'):
                eq += 1
                env_stack.append(('equation', find_env_end(body, env, m.end()), str(eq)))
            i = m.end()
            continue
        if m.group(4):
            lab = m.group(4)
            if lab not in labels:
                inner = env_stack[-1] if env_stack else None
                if inner:
                    labels[lab] = {'type': inner[0], 'number': inner[2]}
            i = m.end()
            continue

    # proofs: "Proof of \cref{X}" goes to X; any other proof to the result just before it, if no result environment
    # starts in between.
    by_label = {r['label']: r for r in results if r['label']}
    for m in re.finditer(r'\\begin\{proof\}', body):
        k = m.end()
        opt = None
        if body[k] == '[':
            opt, k = read_group(body, k, '[', ']')
        end = find_env_end(body, 'proof', k)
        text = body[k:end].strip()
        target = None
        if opt and 'Proof of' in opt:
            rm = REF_RE.search(opt)
            target = by_label[rm.group(2)]
        else:
            prev = [r for r in results if r['end'] <= m.start()]
            if prev:
                cand = prev[-1]
                between = [r for r in results if cand['end'] <= r['pos'] < m.start()]
                if not between:
                    target = cand
        if target is None:
            raise ValueError('proof at %d belongs to no result' % m.start())
        target['proofs'].append({'title': opt, 'tex': text, 'pos': m.start()})

    # a sentence ending in a colon just before a result leads into it ("Since ..., Proposition 6.2 gives:"): what it
    # cites, the result rests on, as for a corollary stated without a proof of its own
    for r in results:
        para = re.split(r'\n\s*\n', body[:r['pos']].rstrip())[-1].strip()
        r['leadin'] = para if para.endswith(':') and not para.startswith('\\') else None
    # a numbered equation stated inside a result: citing the equation cites that result (Prop 6.2 uses (1) of Prop 6.1)
    eq_owner = {}
    for r in results:
        for lab in re.findall(r'\\label\{([^}]*)\}', r['statement']):
            if r['label'] and labels.get(lab, {}).get('type') == 'equation':
                eq_owner[lab] = r['label']
    for r in results:
        refs = []
        for part in [r['statement']] + [p['tex'] for p in r['proofs']] + ([r['leadin']] if r['leadin'] else []):
            for m in REF_RE.finditer(part):
                for lab in m.group(2).split(','):
                    lab = lab.strip()
                    for x in (lab, eq_owner.get(lab)):
                        if x and x != r['label'] and x not in refs:
                            refs.append(x)
        r['refs'] = refs
        r['line'] = raw[:body_offset + r['pos']].count('\n') + 1

    for r in results:
        r['proof_end'] = max([r['end']] + [body.find('\\end{proof}', p['pos']) for p in r['proofs']])
    return {'results': results, 'labels': labels, 'macros': macros, 'sections': sections, 'figures': figures}


def check_numbers(results, pdf_path):
    """Every titled result must appear in the PDF's text as '<Kind> <number> (<start of title>'."""
    txt = subprocess.run(['pdftotext', '-layout', str(pdf_path), '-'], capture_output=True, text=True,
                         check=True).stdout
    txt = re.sub(r'\s+', ' ', txt)
    bad = []
    for r in results:
        head = '%s %s' % (r['kind'], r['number'])
        if r['title']:
            word = re.sub(r'[^A-Za-z].*', '', r['title'].strip())
            needle = head + ' (' + word if word else head + ' ('
        else:
            needle = head + '.'
        if needle not in txt:
            bad.append(needle)
    if bad:
        raise SystemExit('numbering differs from the PDF (rebuild the paper, or fix texparse.py): ' + '; '.join(bad))


def pdf_pages(results, pdf_path):
    """Where things begin in the built PDF: {(kind, number): page} for every result found, {section number: page}
    from the PDF's outline, the number of pages, and {table number: page} from the tables' captions ('Table 2.' opening
    a line; a reference in the text has no full stop after the number, or comes later). A result's heading is bold (italic for the kinds amsthm sets in the remark style) and opens
    a line, followed by its title or a full stop; references in running text are upright, or italic inside a theorem,
    which is why italic counts only for kinds that never appear in bold. Fails if the pages do not rise in the paper's
    order, which would mean a heading was misread."""
    import pymupdf
    kinds = sorted({r['kind'] for r in results})
    pat = re.compile(r'^(%s)\s+([0-9]+\.[0-9]+|[A-Z])\s*[.(]' % '|'.join(kinds))
    doc = pymupdf.open(str(pdf_path))
    bold, italic, tables = {}, {}, {}
    for pno in range(doc.page_count):
        for block in doc[pno].get_text('dict')['blocks']:
            for line in block.get('lines', []):
                spans = [s for s in line['spans'] if s['text'].strip()]
                if not spans:
                    continue
                head = re.sub(r'\s+', ' ', ' '.join(s['text'] for s in spans[:4])).strip()
                t = re.match(r'^Table (\d+)\. ', head)
                if t:
                    tables.setdefault(t.group(1), pno + 1)
                m = pat.match(head)
                if not m:
                    continue
                if spans[0]['flags'] & 16:
                    bold.setdefault((m.group(1), m.group(2)), pno + 1)
                elif spans[0]['flags'] & 2:
                    italic.setdefault((m.group(1), m.group(2)), pno + 1)
    in_bold = {k for k, _ in bold}
    found = dict(bold)
    for key, page in italic.items():
        if key[0] not in in_bold:
            found.setdefault(key, page)
    last = 0
    for r in results:
        page = found.get((r['kind'], r['number']))
        if page is None:
            continue
        if page < last:
            raise SystemExit('pdf_pages: %s %s is on page %d, before the result above it (page %d)'
                             % (r['kind'], r['number'], page, last))
        last = page
    secs = {}
    for _, title, page in doc.get_toc():
        m = re.match(r'^(?:Appendix\s+)?([0-9]+(?:\.[0-9]+)?|[A-Z])\.\s', title)
        if m:
            secs[m.group(1)] = page
    return found, secs, doc.page_count, tables
