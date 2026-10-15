#!/usr/bin/env python3
"""The files that fix what the Lean proves, with their SHA-256, in TRUSTED.sha256: `Statement.lean`, which holds every
definition and claim, and everything it imports (`Basic.lean` and the two data files). `build.sh` runs this first and
fails if any of them has changed since its hash was recorded, or if the imports have changed, so that a change to what
is proved is never silent. (The file has the format of `sha256sum`, so `sha256sum -c TRUSTED.sha256` also checks it.)

    python3 tools/check_trusted.py            # check (build.sh)
    python3 tools/check_trusted.py --update   # record the current files, after a deliberate change to the statement
"""
import hashlib
import pathlib
import re
import sys

LEAN = pathlib.Path(__file__).resolve().parent.parent
LIST = LEAN / 'TRUSTED.sha256'


def closure(start='SpectreKnot/Statement.lean'):
    """`Statement.lean` and the files of this project it imports, directly or not."""
    todo, seen = [start], set()
    while todo:
        f = todo.pop()
        if f not in seen:
            seen.add(f)
            for line in (LEAN / f).read_text(encoding='utf-8').splitlines():
                m = re.match(r'import\s+(SpectreKnot(?:\.\w+)+)\s*$', line)
                if m:
                    todo.append(m.group(1).replace('.', '/') + '.lean')
    return sorted(seen)


def sha(f):
    return hashlib.sha256((LEAN / f).read_bytes()).hexdigest()


files = closure()
if sys.argv[1:] == ['--update']:
    LIST.write_text(''.join('%s  %s\n' % (sha(f), f) for f in files), encoding='utf-8')
    print('recorded in TRUSTED.sha256:', ', '.join(files))
    sys.exit(0)
recorded = dict(reversed(line.split(None, 1)) for line in LIST.read_text(encoding='utf-8').splitlines() if line.strip())
changed = [f for f in files if f in recorded and recorded[f] != sha(f)]
added = [f for f in files if f not in recorded]
dropped = [f for f in recorded if f not in files]
if changed or added or dropped:
    parts = [('changed: ' + ', '.join(changed)) if changed else '',
             ('now imported: ' + ', '.join(added)) if added else '',
             ('no longer imported: ' + ', '.join(dropped)) if dropped else '']
    sys.exit('FAIL: the files that fix what is proved are not as recorded in TRUSTED.sha256 (%s), so the theorems '
             'have changed. If that is intended, record it: python3 tools/check_trusted.py --update'
             % '; '.join(x for x in parts if x))
print('the %d files that fix what is proved are as recorded in TRUSTED.sha256' % len(files))
