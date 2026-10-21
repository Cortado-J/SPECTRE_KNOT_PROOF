#!/usr/bin/env python3
"""Comparison with Kaplan's implementation of the spectre's substitution (paper, Table 1 and the base of the dictionary
(*) in the proof of Prop. 2.4).

Input: spectre.js, the program of the interactive application on the spectre authors' page
(https://cs.uwaterloo.ca/~csk/spectre/, by Craig S. Kaplan). It is published without a licence, so it is not included
here: this script downloads it, or reads a copy given by its path, and checks its SHA-256 (below: the file compared on
15 Oct 2026). A downloaded file with another SHA-256 is not run. kaplan_run.js runs it in a V8 context of its own,
with no access to node. It is the only program in these checks not written with the AI system.

  1. Table 1: Kaplan's table of the children (super_rules, read from the file) is exact.py's, including the empty slot
     of Gamma, and has the kinds of the children in hierarchy/combin_8.json at each of its levels;
  2. levels 0..4: every tile of every supertile, in Kaplan's drawing order, has the same label (the kind of its level-0
     supertile; Gamma1 and Gamma2 for the Mystic's tiles) and the same 14 vertices (within 1e-9) as the placements of
     exact.py; so do the key points of every level;
  3. from Kaplan's tiles alone, without exact.py: the rim of each level-1 supertile, counted from its crossover corner
     A (the first tile of its Gamma child, at v_0), and its six vertices, the rim points where three level-1
     supertiles meet, found on every level-1 supertile whose every rim edge is shared inside Kaplan's level-4
     supertiles (all of a kind must agree); with them, the side lengths and the position of A. These must be VERT, LEN
     and DEF of level 1 in hierarchy/combin_8.json, and l_1 (by the letters of Table 4) and d_1 in hierarchy/letters.json;
  4. negative controls: two altered copies of the file must fail 1 or 2: two children of Delta exchanged in its table,
     and one rule of its key-point construction changed.
usage: python3 crosscheck/kaplan_compare.py [PATH/TO/spectre.js]
"""
import sys, os, re, json, math, hashlib, subprocess, tempfile, urllib.request
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'exact'))
import exact as X

URL = 'https://cs.uwaterloo.ca/~csk/spectre/spectre.js'
SHA = 'd4d7758f268e2e5f3f56deb771f6f783e519f5351b46f8e6e05c0f629d2f6df1'
L = 4
NAMES = X.NAMES
CONTROLS = [('two children of Delta exchanged in its table',
             "'Delta' :  ['Xi','Delta','Xi','Phi',", "'Delta' :  ['Xi','Delta','Phi','Xi',"),
            ('one rule of the key-point construction changed', '[-120, 3, 3]', '[-120, 3, 2]')]


def run_kaplan(src, levels):
    out = src[:-len('.js')] + '_%d.json' % levels
    subprocess.run(['node', os.path.join(HERE, 'kaplan_run.js'), src, out, str(levels)], check=True)
    return json.load(open(out))


def kaplan_table(text):
    body = re.search(r'const super_rules = \{(.*?)\};', text, re.S)
    assert body, 'no table super_rules in the file'
    return {k: [None if s == 'null' else s for s in re.findall(r"'(\w+)'", v)]
            for k, v in re.findall(r"'(\w+)'\s*:\s*\[([^\]]*)\]", body.group(1))}


# ------------------------------------------------------------------ exact.py's supertiles, with the kinds of the tiles
lev, trs_all = X.build(L)

def ours(kind, level, g):
    if level == 0:
        return [('Gamma1', g), ('Gamma2', X.icompose(g, X.MYSTIC2))] if kind == 'Gamma' else [(kind, g)]
    out = []
    for i, s in enumerate(X.SR[kind]):
        if s:
            out += ours(s, level - 1, X.icompose(g, trs_all[level - 1][i]))
    return out

OURS = [{K: [(lab, [X.zfloat(X.iapply(g, v)) for v in X.PTS]) for lab, g in ours(K, m, X.ID)] for K in NAMES}
        for m in range(L + 1)]
QUADS = [X.QUAD]
for m in range(L):
    QUADS.append(X.level_transforms(QUADS[-1])[1])


def compare_tiles(KD, levels):
    """per level: (level, tiles, kinds whose labels differ, largest vertex difference, largest key point difference)"""
    res = []
    for m in range(levels + 1):
        bad, worst = [], 0.0
        for K in NAMES:
            mine, theirs = OURS[m][K], KD['levels'][m]['kinds'][K]['tiles']
            if len(mine) != len(theirs):
                bad.append(K); worst = math.inf
                continue
            if any(lab != t['label'] for (lab, _), t in zip(mine, theirs)):
                bad.append(K)
            worst = max(worst, max(math.dist(p, q) for (_, P), t in zip(mine, theirs) for p, q in zip(P, t['pts'])))
        qd = max(math.dist(X.zfloat(p), q) for p, q in zip(QUADS[m], KD['levels'][m]['quad']))
        res.append((m, sum(len(KD['levels'][m]['kinds'][K]['tiles']) for K in NAMES), bad, worst, qd))
    return res


# ------------------------------------------------------------------ the level-1 supertiles from Kaplan's tiles alone
def key(p):
    return (round(p[0] * 1e5), round(p[1] * 1e5))

def edges_of(tiles):
    """undirected edge (two snapped points) -> [(tile, i, from, to)]"""
    E = {}
    for t, T in enumerate(tiles):
        P = [key(q) for q in T['pts']]
        for i in range(14):
            E.setdefault(frozenset((P[i], P[(i + 1) % 14])), []).append((t, i, P[i], P[(i + 1) % 14]))
    return E

def snapping_safe(tiles):
    """no two distinct snapped points are neighbours on the grid, so snapping neither splits nor merges a point"""
    ks = {key(q) for T in tiles for q in T['pts']}
    return all((a + da, b + db) not in ks for a, b in ks for da in (-1, 0, 1) for db in (-1, 0, 1) if da or db)

def rim_from_A(tiles, ccw):
    """the rim of a supertile given by its tiles, as snapped points, counterclockwise if ccw (else clockwise), from A:
    the first vertex of its tile labelled Gamma1"""
    nxt = {}
    for lst in edges_of(tiles).values():
        assert len(lst) <= 2, 'an edge of three tiles'
        if len(lst) == 1:
            _, _, p, q = lst[0]
            assert p not in nxt, 'the rim is not a simple cycle'
            nxt[p] = q
    cyc = [next(iter(nxt))]
    while nxt[cyc[-1]] != cyc[0]:
        cyc.append(nxt[cyc[-1]])
    assert len(cyc) == len(nxt), 'the rim is not one cycle'
    P = {key(q): q for T in tiles for q in T['pts']}
    area = sum(P[a][0] * P[b][1] - P[b][0] * P[a][1] for a, b in zip(cyc, cyc[1:] + cyc[:1]))
    if (area > 0) != ccw:
        cyc.reverse()
    first = [T for T in tiles if T['label'] == 'Gamma1']
    assert len(first) == 1
    a = cyc.index(key(first[0]['pts'][0]))
    return cyc[a:] + cyc[:a]

def vertices(KD):
    """for each kind, the set of rim positions (from A, in the supertile's own counterclockwise sense) of the points
    where three level-1 supertiles meet, one tuple per level-1 supertile of that kind whose every rim edge is shared
    with another, in Kaplan's level-L supertiles of all nine kinds; and how many such supertiles there are"""
    found, count = {K: set() for K in NAMES}, {K: 0 for K in NAMES}
    for top in NAMES:
        tiles, insts = KD['levels'][L]['kinds'][top]['tiles'], KD['levels'][L]['kinds'][top]['insts']
        assert snapping_safe(tiles)
        by = {}
        for T in tiles:
            by.setdefault(T['inst'], []).append(T)
        rims = {n: [e for e, lst in edges_of(ts).items() if len(lst) == 1] for n, ts in by.items()}
        shared, on = {}, {}
        for n, es in rims.items():
            for e in es:
                shared[e] = shared.get(e, 0) + 1
                for p in e:
                    on.setdefault(p, set()).add(n)
        for n, ts in by.items():
            if any(shared[e] < 2 for e in rims[n]):
                continue
            S = insts[n]['S']
            cyc = rim_from_A(ts, ccw=S[0] * S[4] - S[1] * S[3] > 0)   # own counterclockwise sense, in the plane
            K = insts[n]['kind']
            found[K].add(tuple(i for i, p in enumerate(cyc) if len(on[p]) >= 3))
            count[K] += 1
    return found, count


def main(arg):
    with tempfile.TemporaryDirectory() as td:
        src = os.path.join(td, 'spectre.js')
        if arg:
            data = open(arg, 'rb').read()
            print("Kaplan's spectre.js: read from", arg)
        else:
            data = urllib.request.urlopen(URL, timeout=60).read()
            print("Kaplan's spectre.js: downloaded from", URL)
        h = hashlib.sha256(data).hexdigest()
        if h == SHA:
            print('  sha256', h, '(the file compared on 15 Oct 2026)')
        else:
            print('  sha256', h, '- NOT the file compared on 15 Oct 2026 (sha256 %s)' % SHA)
            if not arg:
                print('NOT RUN: the downloaded file has changed. Read it, then give its path to compare it.')
                return 1
        open(src, 'wb').write(data)
        text = data.decode('utf8')
        ok = True

        T1 = kaplan_table(text)
        C8 = json.load(open(os.path.join(HERE, '..', 'hierarchy', 'combin_8.json')))
        LET = json.load(open(os.path.join(HERE, '..', 'hierarchy', 'letters.json')))
        print("\n1. Table 1: Kaplan's table of the children (super_rules; - an empty slot)")
        for K in NAMES:
            print('  %-7s' % K, ' '.join(s or '-' for s in T1.get(K, [])))
        a = T1 == X.SR
        b = all(C8['ST'][m][K]['kids'] == [s for s in T1.get(K, []) if s] for m in C8['ST'] for K in NAMES)
        print("  = exact.py's: %s; = the kinds of the children in combin_8.json, levels %s: %s"
              % ('yes' if a else 'NO', '-'.join([min(C8['ST'], key=int), max(C8['ST'], key=int)]), 'yes' if b else 'NO'))
        ok &= a and b

        KD = run_kaplan(src, L)
        print("\n2. Every tile of every supertile, in Kaplan's drawing order, against exact.py")
        for m, n, bad, worst, qd in compare_tiles(KD, L):
            good = not bad and worst < 1e-9 and qd < 1e-9
            print('  level %d: %5d tiles; labels %s; largest vertex difference %.1e; key points %.1e%s'
                  % (m, n, 'agree' if not bad else 'DIFFER (%s)' % ', '.join(bad), worst, qd, '' if good else '  FAIL'))
            ok &= good

        print("\n3. The level-1 supertiles from Kaplan's tiles alone (rim positions counted from the crossover corner A)")
        found, count = vertices(KD)
        ok3 = True
        for K in NAMES:
            tiles = KD['levels'][1]['kinds'][K]['tiles']
            assert snapping_safe(tiles)
            n = len(rim_from_A(tiles, ccw=True))
            if len(found[K]) != 1 or len(next(iter(found[K]))) != 6:
                print('  %-7s FAIL: the level-1 supertiles of this kind give the vertices %s' % (K, sorted(found[K])))
                ok3 = False
                continue
            rel = list(next(iter(found[K])))
            sides = [b - a for a, b in zip(rel, rel[1:])] + [n + rel[0] - rel[-1]]
            dA = {'side': 0, 'off': 0} if rel[0] == 0 else {'side': 5, 'off': n - rel[-1]}
            lets = [LET['L']['1'][LET['order'].index(x)] for x in LET['letter'][K]]
            good = (rel == C8['VERT']['1'][K] and sides == C8['LEN']['1'][K] and dA == C8['DEF']['1'][K]
                    and sides == lets and (K != 'Sigma' or dA['off'] == LET['d1']))
            print('  %-7s %2d tiles, rim %d; vertices %s (from %3d level-1 supertiles); sides %s; A on side %d at %d%s'
                  % (K, len(tiles), n, rel, count[K], sides, dA['side'], dA['off'], '' if good else '  FAIL'))
            ok3 &= good
        print('  = VERT, LEN, DEF of level 1 in combin_8.json, and l_1 and d_1 in letters.json: %s' % ('yes' if ok3 else 'NO'))
        ok &= ok3

        print('\n4. Negative controls (levels 0-2)')
        for name, old, new in CONTROLS:
            if text.count(old) != 1:
                print('  %s: NOT RUN (the text to alter is not in the file exactly once)' % name)
                ok = False
                continue
            alt =os.path.join(td, 'altered%d.js' % CONTROLS.index((name, old, new)))
            open(alt, 'w').write(text.replace(old, new))
            res = compare_tiles(run_kaplan(alt, 2), 2)
            t1 = kaplan_table(text.replace(old, new)) != X.SR
            labs = [m for m, _, bad, _, _ in res if bad]
            far = max(w for _, _, _, w, _ in res)
            rejected = t1 or labs or far > 1e-9
            print('  %s: %s (Table 1 %s; %s; largest vertex difference %.2f)'
                  % (name, 'rejected' if rejected else 'NOT REJECTED', 'differs' if t1 else 'agrees',
                     'labels differ at levels ' + ', '.join(map(str, labs)) if labs else 'labels agree', far))
            ok &= bool(rejected)

    print()
    print("KAPLAN'S IMPLEMENTATION AGREES: TABLE 1, EVERY TILE TO LEVEL 4, THE LEVEL-1 VERTICES, l_1 AND d_1" if ok
          else "DISAGREEMENT WITH KAPLAN'S IMPLEMENTATION")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else None))
