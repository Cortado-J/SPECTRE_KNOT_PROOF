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

    for r in results:
        refs = []
        for part in [r['statement']] + [p['tex'] for p in r['proofs']]:
            for m in REF_RE.finditer(part):
                for lab in m.group(2).split(','):
                    lab = lab.strip()
                    if lab and lab != r['label'] and lab not in refs:
                        refs.append(lab)
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
