#!/usr/bin/env python3
"""Fail if any Lean source uses sorry, admit or native_decide outside comments."""
import pathlib
import re
import sys

bad = []
for f in sorted(pathlib.Path('.').glob('SpectreKnot/**/*.lean')) + [pathlib.Path('Axioms.lean'), pathlib.Path('Tests.lean'), pathlib.Path('TestsSlow.lean')]:
    s = f.read_text()
    out, i, depth = [], 0, 0
    while i < len(s):   # drop (nested) block comments and line comments
        if s.startswith('/-', i):
            depth += 1; i += 2
        elif depth and s.startswith('-/', i):
            depth -= 1; i += 2
        elif not depth and s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j
        else:
            if not depth:
                out.append(s[i])
            elif s[i] == '\n':
                out.append('\n')
            i += 1
    for n, line in enumerate(''.join(out).split('\n'), 1):
        if re.search(r'\b(sorry|admit|native_decide)\b', line):
            bad.append(f'{f}:{n}: {line.strip()}')
print('\n'.join(bad) if bad else 'no sorry, admit or native_decide')
sys.exit(1 if bad else 0)
