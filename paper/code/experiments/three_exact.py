# Remark 10.1 (experiment, not part of the proof): exact strand following along the chain
# Theta (odd levels, child 2 of Gamma) / Gamma (even levels, child 7 of Theta), and the other alignment.
# Prints the number of arcs of X_N that the arcs of X_b lie on, N = b+1..8. About 15 minutes, ~10 GB RAM.
import sys, time
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'exact'))
import exact as X
L = 8; t0 = time.time(); lev, trs_all = X.build(L); print(f'built 0..{L} in {time.time()-t0:.0f}s', flush=True)
def raw(T, c):
    k = -1
    for i, s in enumerate(X.SR[T]):
        if s: k += 1
        if s and k == c: return i
def follow(b, K0, chain):
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
        newlab = [-1] * (2 * par.E)
        for P, acc in info['plab'].items():
            acc = list(acc); r = find(acc[0])
            for x in acc[1:]:
                rx = find(x)
                if rx != r: uf[rx] = r
            newlab[P] = find(acc[0])
        curlab = [find(x) if x >= 0 else -1 for x in newlab]
        arcs = {min(P, par.pair[P]) for P in range(2 * par.E) if curlab[P] >= 0}
        out.append(f'L{N}:{len(arcs)}' + (f' LOST{len(info["lost"])}' if info['lost'] else '') + (f' loops{par.loops}' if par.loops else ''))
        cur, kind = par, T
    return out
for b, K0 in [(1, 'Theta'), (2, 'Gamma'), (3, 'Theta'), (1, 'Gamma')]:
    chain = []; kind = K0
    for N in range(b + 1, L + 1):
        st = ('Theta', 7) if kind == 'Gamma' else ('Gamma', 2); chain.append(st); kind = st[0]
    print(f'b={b} {K0} (exact): ' + ' '.join(follow(b, K0, chain)), flush=True)
