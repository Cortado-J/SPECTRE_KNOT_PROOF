#!/usr/bin/env python3
"""Fail unless every `theorem` and every `have` in the Lean sources carries a comment.

A `theorem` needs a comment ending on the line above it (a `/-- … -/` doc comment, or `--` lines), attributes
(`@[simp]`, `set_option … in`) allowed in between. A `have` needs a `--` comment on the line above it, or at the
end of its own line; and there is at most one `have` per line. Generated data files are skipped.
"""
import pathlib
import re
import sys


def code_and_comments(text):
    """Split each line into its code (comments removed) and whether the line holds or ends a comment."""
    code_lines, comment_lines = [], []
    depth, i, line_code, line_comment = 0, 0, [], False
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2; line_comment = True
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2; line_comment = True
        elif not depth and text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
            line_comment = True
        elif text[i] == '\n':
            code_lines.append(''.join(line_code)); comment_lines.append(line_comment or depth > 0)
            line_code, line_comment = [], depth > 0
            i += 1
        else:
            if not depth:
                line_code.append(text[i])
            i += 1
    code_lines.append(''.join(line_code)); comment_lines.append(line_comment)
    return code_lines, comment_lines


def check(path):
    text = path.read_text()
    raw = text.split('\n')
    code, commented = code_and_comments(text)
    bad = []
    for n, line in enumerate(code):
        if re.match(r'\s*(private\s+|protected\s+)?theorem\b', line):
            k = n - 1
            while k >= 0 and (re.match(r'\s*(@\[|set_option\b.*\bin\s*$)', code[k]) and not commented[k]):
                k -= 1
            if k < 0 or not commented[k] or code[k].strip():
                bad.append(f'{path}:{n + 1}: theorem without a comment above it')
        haves = re.findall(r'\bhave\b', line)
        if len(haves) > 1:
            bad.append(f'{path}:{n + 1}: more than one `have` on a line')
        elif haves:
            own_comment = '--' in raw[n][raw[n].find('have'):]
            above = n > 0 and commented[n - 1] and code[n - 1].strip() in ('', '·')
            if not (own_comment or above):
                bad.append(f'{path}:{n + 1}: `have` without a comment')
    return bad


files = [f for f in sorted(pathlib.Path('SpectreKnot').glob('**/*.lean')) if 'Data' not in f.parts]
files += [pathlib.Path('Tests.lean'), pathlib.Path('TestsSlow.lean')]
bad = [b for f in files for b in check(f)]
print('\n'.join(bad) if bad else 'every theorem and have has a comment')
print(f'{len(bad)} problems', file=sys.stderr) if bad else None
sys.exit(1 if bad else 0)
