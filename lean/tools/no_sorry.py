#!/usr/bin/env python3
"""Fail if any Lean source uses, outside comments, sorry, admit or native_decide, or another way round Lean's kernel
or the axiom check: axiom, opaque, partial, unsafe, implemented_by, extern, debug.skipKernelTC (declarations it lets
through are never checked by the kernel, and #print axioms does not show it), ofReduceBool or reduceBool (what
native_decide uses); or if lakefile.toml turns the kernel off (skipKernelTC)."""
import pathlib
import re
import sys

BANNED = (r'\b(sorry|admit|native_decide|axiom|opaque|partial|unsafe|implemented_by|extern|skipKernelTC|'
          r'ofReduceBool|reduceBool)\b')

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
        if re.search(BANNED, line):
            bad.append(f'{f}:{n}: {line.strip()}')
if 'skipKernelTC' in pathlib.Path('lakefile.toml').read_text():
    bad.append('lakefile.toml: skipKernelTC')
print('\n'.join(bad) if bad else 'no sorry, admit, native_decide or other way round the kernel')
sys.exit(1 if bad else 0)
