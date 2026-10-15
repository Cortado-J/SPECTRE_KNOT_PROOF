#!/usr/bin/env python3
"""The change log, CHANGELOG.md: what each publication changed on the public proof site, newest first.

    python3 proofmap/changelog.py release PUBLIC_CHECKOUT   # before each publication: is there an entry for it?

Only changes that reach the public site go in it (the paper, the Lean, the code and the site's pages as published),
never work that stays in the development repository. The file: the title ("# Changes"), one paragraph saying what it
is, then one section per day of publishing, newest first, headed by its date (UK time) as "## 15 October 2026", with
one bullet per change, each starting **Paper:**, **Lean:**, **Code:** or **Site:**. A second publication on the same
day adds its bullets to that day's section.

build.py shows it as the site's Changes page and stops if it is malformed. `release` stops a publication unless the
newest section is dated today and is new, or has grown, since the copy in the public checkout (the last publication).
"""
import datetime
import pathlib
import sys
from zoneinfo import ZoneInfo

ROOT = pathlib.Path(__file__).resolve().parent.parent
FILE = ROOT / 'CHANGELOG.md'


def fmt(day):
    """A date as the headings write it: 15 October 2026."""
    return '%d %s' % (day.day, day.strftime('%B %Y'))


def parse(text, where='CHANGELOG.md'):
    """The change log's title, its introduction (one paragraph) and its sections [(date, heading, body)], newest
    first. Exits with a message if the file does not have that form."""
    lines = text.rstrip('\n').split('\n')
    if not lines[0].startswith('# '):
        sys.exit('%s: the first line must be the title, "# Changes"' % where)
    intro, sections = [], []
    for line in lines[1:]:
        if line.startswith('## '):
            heading = line[3:].strip()
            try:
                day = datetime.datetime.strptime(heading, '%d %B %Y').date()
            except ValueError:
                sys.exit('%s: "## %s" is not a date written like "## 15 October 2026"' % (where, heading))
            if heading != fmt(day):
                sys.exit('%s: write "## %s" as "## %s"' % (where, heading, fmt(day)))
            sections.append([day, heading, []])
        elif line.startswith('#'):
            sys.exit('%s: "%s": only the title starts "# ", and each day "## <date>"' % (where, line))
        elif sections:
            sections[-1][2].append(line)
        else:
            intro.append(line)
    if not sections:
        sys.exit('%s: no dated sections' % where)
    for (a, ha, _), (b, hb, _) in zip(sections, sections[1:]):
        if not a > b:
            sys.exit('%s: "## %s" comes after "## %s": newest first, one section per day' % (where, hb, ha))
    out = []
    for day, heading, body in sections:
        body = '\n'.join(body).strip()
        if not any(l.lstrip().startswith(('- ', '* ')) for l in body.split('\n')):
            sys.exit('%s: "## %s" lists no changes (one "- " line each)' % (where, heading))
        out.append((day, heading, body))
    return lines[0][2:].strip(), ' '.join('\n'.join(intro).split()), out


def read(path=FILE):
    """The change log of this repository (see `parse`)."""
    return parse(path.read_text(encoding='utf8'), path.name)


def release(public):
    """Before a publication: the newest section must be dated today (UK) and be new, or have grown, since the copy in
    the public checkout. Prints the section, to write the publication's commit message from."""
    _, _, sections = read()
    day, heading, body = sections[0]
    today = datetime.datetime.now(ZoneInfo('Europe/London')).date()   # here, so that build.py needs no time zones
    if day != today:
        sys.exit('CHANGELOG.md: the newest section is "## %s", but today is %s (UK). Add "## %s" at the top, with what '
                 'this publication changes on the public site, commit and merge it, then publish again.'
                 % (heading, fmt(today), fmt(today)))
    published = pathlib.Path(public) / FILE.name
    if published.exists():
        _, _, old = parse(published.read_text(encoding='utf8'), 'the published ' + FILE.name)
        if old[0][0] == day and old[0][2] == body:
            sys.exit('CHANGELOG.md: "## %s" is as it was at the last publication. Add what this publication changes on '
                     'the public site, commit and merge it, then publish again.' % heading)
    print('Change log, %s:\n%s' % (heading, body))


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == 'release':
        release(sys.argv[2])
    else:
        sys.exit('usage: python3 proofmap/changelog.py release PUBLIC_CHECKOUT')
