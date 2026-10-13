#!/usr/bin/env python3
# Checks on the hand-drawn design (paper, Remark 'Over and under'): each piece stays inside the tile away from its
# ends; apart from their common ends on the edges, the only crossing between pieces of one tile is the crossover, and
# it is transversal; at each edge the two pieces of a tile meet the
# crossing point at +-45 degrees to the edge, so ribbons continue smoothly across the edge and cross at right angles.
# Curves are sampled (400 points per cubic segment). usage: python3 drawing/drawcheck.py
import json, math, itertools
D = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'hand01b_norm.json')))
S3 = 3 ** 0.5
PTS = [(0, 0), (1, 0), (1.5, -S3 / 2), (1.5 + S3 / 2, 0.5 - S3 / 2), (1.5 + S3 / 2, 1.5 - S3 / 2), (2.5 + S3 / 2, 1.5 - S3 / 2),
       (3 + S3 / 2, 1.5), (3, 2), (3 - S3 / 2, 1.5), (2.5 - S3 / 2, 1.5 + S3 / 2), (1.5 - S3 / 2, 1.5 + S3 / 2),
       (0.5 - S3 / 2, 1.5 + S3 / 2), (-S3 / 2, 1.5), (0, 1)]
def bez(P, t):
    a, b, c, d = P
    return tuple((1-t)**3*a[i] + 3*(1-t)**2*t*b[i] + 3*(1-t)*t*t*c[i] + t**3*d[i] for i in range(2))
def poly(pidx, n=400):
    A = D['passages'][pidx]['anchors']; out = []
    for i in range(len(A) - 1):
        P = (A[i]['p'], A[i]['h2'], A[i + 1]['h1'], A[i + 1]['p'])
        for k in range(n): out.append(bez(P, k / n))
    out.append(tuple(A[-1]['p'])); return out
def segx(p, q, r, s):
    d = (q[0]-p[0])*(s[1]-r[1]) - (q[1]-p[1])*(s[0]-r[0])
    if abs(d) < 1e-15: return None
    t = ((r[0]-p[0])*(s[1]-r[1]) - (r[1]-p[1])*(s[0]-r[0])) / d
    u = ((r[0]-p[0])*(q[1]-p[1]) - (r[1]-p[1])*(q[0]-p[0])) / d
    if 0 <= t <= 1 and 0 <= u <= 1: return (p[0]+t*(q[0]-p[0]), p[1]+t*(q[1]-p[1]))
    return None
def inside(pt):
    x, y = pt; c = False
    for i in range(14):
        a, b = PTS[i], PTS[(i + 1) % 14]
        if (a[1] > y) != (b[1] > y) and x < (b[0]-a[0])*(y-a[1])/(b[1]-a[1]) + a[0]: c = not c
    return c
def dist_to_boundary(pt):
    best = 9
    for i in range(14):
        a, b = PTS[i], PTS[(i + 1) % 14]; vx, vy = b[0]-a[0], b[1]-a[1]
        t = max(0, min(1, ((pt[0]-a[0])*vx + (pt[1]-a[1])*vy)/(vx*vx+vy*vy)))
        best = min(best, math.hypot(a[0]+t*vx-pt[0], a[1]+t*vy-pt[1]))
    return best
P = [poly(i) for i in range(14)]
# 1. each piece stays inside the tile except at its two ends
mind = min(dist_to_boundary(p) for pl in P for p in pl[5:-5])
allin = all(inside(p) for pl in P for p in pl[3:-3])
print('pieces strictly inside the tile away from their ends:', allin, '; min distance to boundary (excluding 5 end samples):', round(mind, 4))
# 2. pairwise intersections, excluding shared endpoints (ports)
ends = {i: (tuple(D['passages'][i]['anchors'][0]['p']), tuple(D['passages'][i]['anchors'][-1]['p'])) for i in range(14)}
for i, j in itertools.combinations(range(14), 2):
    hits = []
    for a in range(len(P[i]) - 1):
        for b in range(len(P[j]) - 1):
            x = segx(P[i][a], P[i][a+1], P[j][b], P[j][b+1])
            if x and min(math.dist(x, e) for e in ends[i] + ends[j]) > 1e-3:
                if not hits or min(math.dist(x, h) for h in hits) > 1e-3: hits.append(x)
    if hits:
        print(f'pieces {i} ({D["passages"][i]["from"]}-{D["passages"][i]["to"]}) and {j} ({D["passages"][j]["from"]}-{D["passages"][j]["to"]}) cross at', [tuple(round(c, 3) for c in h) for h in hits])
        for h in hits:   # angle between the two pieces at the crossing (tangents from neighbouring samples)
            def tan_at(pl):
                a = min(range(1, len(pl) - 1), key=lambda k: math.dist(pl[k], h))
                v = (pl[a + 1][0] - pl[a - 1][0], pl[a + 1][1] - pl[a - 1][1]); L = math.hypot(*v); return (v[0] / L, v[1] / L)
            u, w = tan_at(P[i]), tan_at(P[j])
            ang = math.degrees(math.acos(min(1, abs(u[0] * w[0] + u[1] * w[1]))))
            print(f'   angle between the pieces there: {ang:.1f} deg (transversal: {ang > 10})')
# 3. port points: on edge e_k the point at 0.5+0.15(-1)^k from v_k; tangents of the pieces there
def tangent(pidx, end):
    A = D['passages'][pidx]['anchors']
    if end == 0: v = (A[0]['h2'][0]-A[0]['p'][0], A[0]['h2'][1]-A[0]['p'][1])
    else: v = (A[-1]['h1'][0]-A[-1]['p'][0], A[-1]['h1'][1]-A[-1]['p'][1])
    L = math.hypot(*v); return (v[0]/L, v[1]/L)
for k in range(14):
    a, b = PTS[k], PTS[(k + 1) % 14]; f = 0.5 + 0.15 * (-1) ** k
    port = (a[0] + f*(b[0]-a[0]), a[1] + f*(b[1]-a[1]))
    at = [(i, e) for i in range(14) for e in (0, 1) if math.dist(tuple(D['passages'][i]['anchors'][-e if e else 0]['p']), port) < 1e-6]
    ed = ((b[0]-a[0]), (b[1]-a[1]))
    angs = []
    for i, e in at:
        t = tangent(i, e); angs.append(round(math.degrees(math.atan2(t[0]*ed[1]-t[1]*ed[0], t[0]*ed[0]+t[1]*ed[1])), 1))
    print(f'edge e{k}: port at {f:.2f} from v{k}; piece ends there: {len(at)}; angle of each piece to the edge direction (deg): {angs}')
