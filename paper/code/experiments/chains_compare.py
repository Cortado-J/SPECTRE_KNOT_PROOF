# Remark 10.1 (experiment, not part of the proof): the label bookkeeping along an arbitrary chain
# (hierarchy/chains_label.js) against exact strand following (exact/exact.py), on chains chosen at random step by step
# as in random_chains.js (here with Python's random, seed 1), for b = 1, 2, 3, up to level 8. For each level N the two
# must give the same number of arcs of X_N on which the arcs of X_b lie. About 1 hour, ~10 GB RAM.
# usage: python3 chains_compare.py [chains per b = 20]
import sys, os, time, random, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'exact'))
import exact as X
L = 8; per_b = int(sys.argv[1]) if len(sys.argv) > 1 else 20
t0 = time.time(); lev, trs_all = X.build(L); print(f'built 0..{L} in {time.time()-t0:.0f}s', flush=True)
KIDS = {T: [s for s in X.SR[T] if s] for T in X.NAMES}
PARENTS = {K: [(T, c) for T in X.NAMES for c, s in enumerate(KIDS[T]) if s == K] for K in X.NAMES}
def raw(T, c):
    k = -1
    for i, s in enumerate(X.SR[T]):
        if s: k += 1
        if s and k == c: return i
def follow(b, K0, chain):
    """exact: the number of arcs of X_N carrying arcs of X_b, N = b+1..L (as experiments/three_exact.py)."""
    xb = lev[b][K0]; lab = [-1] * (2 * xb.E); n = 0
    for p in range(2 * xb.E):
        if lab[p] < 0: lab[p] = n; lab[xb.pair[p]] = n; n += 1
    uf = list(range(n))
    def find(x):
        while uf[x] != x: uf[x] = uf[uf[x]]; x = uf[x]
        return x
    cur, curlab, kind, out = xb, lab, K0, []
    for k, (T, c) in enumerate(chain):
        N = b + k + 1; i = raw(T, c); assert X.SR[T][i] == kind
        trs = trs_all[N - 1]; kids = []; pos = None
        for j, s in enumerate(X.SR[T]):
            if not s: continue
            if j == i: pos = len(kids); kids.append((cur, trs[j]))
            else: kids.append((lev[N - 1][s], trs[j]))
        par, info = X.compose(kids, labels={pos: curlab})
        if info['lost'] or par.loops: raise RuntimeError('lost labels or closed strand')
        newlab = [-1] * (2 * par.E)
        for P, acc in info['plab'].items():
            acc = list(acc); r = find(acc[0])
            for x in acc[1:]:
                rx = find(x)
                if rx != r: uf[rx] = r
            newlab[P] = find(acc[0])
        curlab = [find(x) if x >= 0 else -1 for x in newlab]
        out.append(len({min(P, par.pair[P]) for P in range(2 * par.E) if curlab[P] >= 0}))
        cur, kind = par, T
    return out
def label(b, K0, chain):
    """the label bookkeeping of hierarchy/chains_label.js on the same chain."""
    arg = ','.join(f'{T}:{c}' for T, c in chain)
    line = subprocess.run(['node', os.path.join(HERE, '..', 'hierarchy', 'chains_label.js'), str(b), K0, arg],
                          capture_output=True, text=True, check=True).stdout.strip()
    return [int(tok.split(':')[1].split('(')[0]) for tok in line.split(': ', 1)[1].split()]
rng = random.Random(1); bad = 0; total = 0
for b in (1, 2, 3):
    for i in range(per_b):
        K0 = rng.choice(X.NAMES); chain = []; kind = K0
        for N in range(b + 1, L + 1):
            T, c = rng.choice(PARENTS[kind]); chain.append((T, c)); kind = T
        ex, lb = follow(b, K0, chain), label(b, K0, chain); total += 1
        ok = ex == lb; bad += not ok
        print(f'b={b} {K0} {",".join(f"{T}:{c}" for T, c in chain)}: exact {ex} label {lb} {"same" if ok else "DIFFERENT"}', flush=True)
print(f'total {time.time()-t0:.0f}s')
print(f'ALL {total} CHAINS AGREE UP TO LEVEL {L}' if not bad else f'{bad} OF {total} CHAINS DIFFER')
sys.exit(1 if bad else 0)
