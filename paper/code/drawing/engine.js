/* Spectre knot engine (port of build.py). Produces, per grid mode:
   { strands:[{c, z, p:Float64Array [x0,y0, (c1x,c1y,c2x,c2y,x,y)*n]}], crossings:[[o,j,u,ju]], faces:[{k,c,r:[sid,a,n,dir,...]}] }
   y is flipped for screen coordinates. */
var SpectreEngine = (function () {
  const S3 = Math.sqrt(3);
  const PTS = [[0, 0], [1, 0], [1.5, -S3 / 2], [1.5 + S3 / 2, 0.5 - S3 / 2], [1.5 + S3 / 2, 1.5 - S3 / 2],
    [2.5 + S3 / 2, 1.5 - S3 / 2], [3 + S3 / 2, 1.5], [3, 2], [3 - S3 / 2, 1.5],
    [2.5 - S3 / 2, 1.5 + S3 / 2], [1.5 - S3 / 2, 1.5 + S3 / 2], [0.5 - S3 / 2, 1.5 + S3 / 2],
    [-S3 / 2, 1.5], [0, 1]];
  const IDENT = [1, 0, 0, 0, 1, 0];
  const mul = (A, B) => [A[0] * B[0] + A[1] * B[3], A[0] * B[1] + A[1] * B[4], A[0] * B[2] + A[1] * B[5] + A[2],
    A[3] * B[0] + A[4] * B[3], A[3] * B[1] + A[4] * B[4], A[3] * B[2] + A[4] * B[5] + A[5]];
  const trot = (a) => { const c = Math.cos(a), s = Math.sin(a); return [c, -s, 0, s, c, 0]; };
  const ttrans = (x, y) => [1, 0, x, 0, 1, y];
  const tp = (M, P) => [M[0] * P[0] + M[1] * P[1] + M[2], M[3] * P[0] + M[4] * P[1] + M[5]];
  const transTo = (p, q) => ttrans(q[0] - p[0], q[1] - p[1]);
  const QUAD = [PTS[3], PTS[5], PTS[7], PTS[11]];
  const KERNEL = [1.6268, 0.9];   // a point that sees the whole spectre boundary (inside its kernel)
  const NAMES = ['Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Phi', 'Psi'];

  function base() {
    const b = {};
    for (const l of NAMES) if (l !== 'Gamma') b[l] = { tile: true, quad: QUAD };
    b.Gamma = { geoms: [[{ tile: true }, IDENT], [{ tile: true }, mul(ttrans(PTS[8][0], PTS[8][1]), trot(Math.PI / 6))]], quad: QUAD };
    return b;
  }
  function supertiles(ts) {
    const quad = ts.Delta.quad, R = [-1, 0, 0, 0, 1, 0];
    const rules = [[60, 3, 1], [0, 2, 0], [60, 3, 1], [60, 3, 1], [0, 2, 0], [60, 3, 1], [-120, 3, 3]];
    let trs = [IDENT], tot = 0, rot = IDENT, tq = quad.slice();
    for (const [ang, fr, to] of rules) {
      if (ang !== 0) { tot += ang; rot = trot(tot * Math.PI / 180); tq = quad.map((q) => tp(rot, q)); }
      trs.push(mul(transTo(tq[to], tp(trs[trs.length - 1], quad[fr])), rot));
    }
    trs = trs.map((t) => mul(R, t));
    const sr = {
      Gamma: ['Pi', 'Delta', null, 'Theta', 'Sigma', 'Xi', 'Phi', 'Gamma'],
      Delta: ['Xi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'],
      Theta: ['Psi', 'Delta', 'Pi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'],
      Lambda: ['Psi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'],
      Xi: ['Psi', 'Delta', 'Pi', 'Phi', 'Sigma', 'Psi', 'Phi', 'Gamma'],
      Pi: ['Psi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Psi', 'Phi', 'Gamma'],
      Sigma: ['Xi', 'Delta', 'Xi', 'Phi', 'Sigma', 'Pi', 'Lambda', 'Gamma'],
      Phi: ['Psi', 'Delta', 'Psi', 'Phi', 'Sigma', 'Pi', 'Phi', 'Gamma'],
      Psi: ['Psi', 'Delta', 'Psi', 'Phi', 'Sigma', 'Psi', 'Phi', 'Gamma']
    };
    const sq = [tp(trs[6], quad[2]), tp(trs[5], quad[1]), tp(trs[3], quad[2]), tp(trs[0], quad[1])];
    const out = {};
    for (const l in sr) {
      const geoms = [];
      sr[l].forEach((s, i) => { if (s) geoms.push([ts[s], trs[i]]); });
      out[l] = { geoms, quad: sq };
    }
    return out;
  }

  const vkey = (p) => Math.round(p[0] * 1000) + ',' + Math.round(p[1] * 1000);
  const sub = (a, b) => [a[0] - b[0], a[1] - b[1]];
  const add = (a, b) => [a[0] + b[0], a[1] + b[1]];
  const scl = (a, k) => [a[0] * k, a[1] * k];
  const nrm = (a) => Math.hypot(a[0], a[1]);
  const unit = (v) => { const n = nrm(v); return n > 1e-12 ? [v[0] / n, v[1] / n] : v; };
  const rot90 = (v) => [-v[1], v[0]];
  const dot = (a, b) => a[0] * b[0] + a[1] * b[1];
  const cross3 = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);

  // local bounding circle of every shape (shapes are shared between metatiles, so memoise)
  const bound = new WeakMap();
  function bounds(sh) {
    if (bound.has(sh)) return bound.get(sh);
    let res;
    if (sh.tile) {
      let cx = 0, cy = 0; for (const p of PTS) { cx += p[0]; cy += p[1]; } cx /= 14; cy /= 14;
      let r = 0; for (const p of PTS) r = Math.max(r, Math.hypot(p[0] - cx, p[1] - cy));
      res = [cx, cy, r];
    } else {
      const kids = sh.geoms.map(([s, t]) => { const b = bounds(s); const c = tp(t, b); return [c[0], c[1], b[2]]; });
      let cx = 0, cy = 0; for (const k of kids) { cx += k[0]; cy += k[1]; } cx /= kids.length; cy /= kids.length;
      let r = 0; for (const k of kids) r = Math.max(r, Math.hypot(k[0] - cx, k[1] - cy) + k[2]);
      res = [cx, cy, r];
    }
    bound.set(sh, res);
    return res;
  }

  // Final smoothing: every span between two crossings is replaced by a least-squares cubic B-spline with only a few
  // knots (one per `fitSpan` of arc length), pinned to the crossing points with their 45-degree tangents. A curve with so
  // few knots cannot wiggle at a small scale. Any span whose smooth curve would cut through another strand or a tile
  // edge gets twice as many knots and is fitted again, down to the resolution of the relaxed polyline if need be.
  function fitSplines(S, out, obstacles, prm, helpers) {
    const { segDist2, properCrossXY } = helpers;
    const h = prm.h, DELTA = prm.fitSpan;
    // ---- cubic B-spline basis on a clamped uniform knot vector over [0, L] with m segments
    function basisFns(m, L) {
      const n = m + 2;   // control points 0..n
      const t = new Float64Array(n + 5);
      for (let i = 0; i < 4; i++) { t[i] = 0; t[n + 1 + i] = L; }
      for (let i = 1; i < m; i++) t[3 + i] = L * i / m;
      // returns [first index, N[4], dN[4]] at u
      return (u) => {
        if (u >= L) u = L - 1e-12 * Math.max(1, L); if (u < 0) u = 0;
        let k = 3; while (k < n && t[k + 1] <= u) k++;   // t[k] <= u < t[k+1]
        const N = [0, 0, 0, 0], dN = [0, 0, 0, 0];
        // degree 0..3 by the triangular scheme (Piegl & Tiller A2.2), with the degree-2 row kept for derivatives
        let Nd = [1]; let N2 = null;
        for (let p = 1; p <= 3; p++) {
          const Nn = new Array(p + 1).fill(0);
          for (let j = 0; j <= p; j++) {
            const i = k - p + j;
            const a = (t[i + p] - t[i]) > 0 ? (u - t[i]) / (t[i + p] - t[i]) : 0;
            const b = (t[i + p + 1] - t[i + 1]) > 0 ? (t[i + p + 1] - u) / (t[i + p + 1] - t[i + 1]) : 0;
            Nn[j] = (j > 0 ? a * Nd[j - 1] : 0) + (j < p ? b * Nd[j] : 0);
          }
          if (p === 2) N2 = Nn;
          Nd = Nn;
        }
        for (let j = 0; j < 4; j++) {
          N[j] = Nd[j];
          const i = k - 3 + j;
          const c1 = (t[i + 3] - t[i]) > 0 ? 3 / (t[i + 3] - t[i]) : 0, c2 = (t[i + 4] - t[i + 1]) > 0 ? 3 / (t[i + 4] - t[i + 1]) : 0;
          dN[j] = c1 * (j > 0 ? N2[j - 1] : 0) - c2 * (j < 3 ? N2[j] : 0);
        }
        return [k - 3, N, dN];
      };
    }
    function solveSPD(A, b) {   // small dense symmetric positive definite system, Cholesky
      const n = b.length, Lm = A.map((r) => r.slice());
      for (let i = 0; i < n; i++) {
        for (let j = 0; j <= i; j++) {
          let s = Lm[i][j]; for (let k = 0; k < j; k++) s -= Lm[i][k] * Lm[j][k];
          if (i === j) { if (s <= 1e-14) s = 1e-14; Lm[i][i] = Math.sqrt(s); } else Lm[i][j] = s / Lm[j][j];
        }
      }
      const y = new Float64Array(n), x = new Float64Array(n);
      for (let i = 0; i < n; i++) { let s = b[i]; for (let k = 0; k < i; k++) s -= Lm[i][k] * y[k]; y[i] = s / Lm[i][i]; }
      for (let i = n - 1; i >= 0; i--) { let s = y[i]; for (let k = i + 1; k < n; k++) s -= Lm[k][i] * x[k]; x[i] = s / Lm[i][i]; }
      return x;
    }
    // ---- fit one span: dense points q (arrays [x,y]), end tangents Ta (leaving a), Tb (arriving at b)
    function fitSpan(q, Ta, Tb, m) {
      const K = q.length - 1;
      const cum = [0]; for (let i = 1; i <= K; i++) cum.push(cum[i - 1] + Math.hypot(q[i][0] - q[i - 1][0], q[i][1] - q[i - 1][1]));
      const L = cum[K] || 1e-9;
      const n = m + 2, basis = basisFns(m, L);
      const Xa = q[0], Xb = q[K];
      const nFree = Math.max(0, n - 3), nz = 2 + 2 * nFree;   // alpha_a, alpha_b, free control points 2..n-2
      const A = Array.from({ length: nz }, () => new Float64Array(nz)), bvec = new Float64Array(nz);
      const rows = [];
      for (let i = 0; i <= K; i++) {
        const [i0, N] = basis(cum[i]);
        const coef = new Float64Array(n + 1); for (let j = 0; j < 4; j++) coef[i0 + j] = N[j];
        for (let c = 0; c < 2; c++) {   // x and y rows
          const row = new Float64Array(nz); let rhs = q[i][c];
          rhs -= (coef[0] + coef[1]) * Xa[c] + (coef[n - 1] + coef[n]) * Xb[c];
          row[0] = coef[1] * Ta[c]; row[1] = -coef[n - 1] * Tb[c];
          for (let j = 2; j <= n - 2; j++) row[2 + 2 * (j - 2) + c] = coef[j];
          rows.push([row, rhs]);
        }
      }
      for (const [row, rhs] of rows) for (let a = 0; a < nz; a++) { if (row[a] === 0) continue; bvec[a] += row[a] * rhs; for (let b2 = 0; b2 < nz; b2++) A[a][b2] += row[a] * row[b2]; }
      for (let a = 0; a < nz; a++) A[a][a] += 1e-9;
      const z = solveSPD(A, bvec);
      const amin = 0.08 * L / m;
      const P = [Xa, [Xa[0] + Math.max(amin, z[0]) * Ta[0], Xa[1] + Math.max(amin, z[0]) * Ta[1]]];
      for (let j = 2; j <= n - 2; j++) P.push([z[2 + 2 * (j - 2)], z[2 + 2 * (j - 2) + 1]]);
      P.push([Xb[0] - Math.max(amin, z[1]) * Tb[0], Xb[1] - Math.max(amin, z[1]) * Tb[1]], Xb);
      // exact cubic Bezier pieces, one per knot interval, from position and derivative at the knots
      const bez = [];
      const at = (u) => { const [i0, N, dN] = basis(u); const p = [0, 0], d = [0, 0]; for (let j = 0; j < 4; j++) { p[0] += N[j] * P[i0 + j][0]; p[1] += N[j] * P[i0 + j][1]; d[0] += dN[j] * P[i0 + j][0]; d[1] += dN[j] * P[i0 + j][1]; } return [p, d]; };
      for (let k = 0; k < m; k++) {
        const u0 = L * k / m, u1 = L * (k + 1) / m, du = u1 - u0;
        const [p0, d0] = at(u0), [p1, d1] = at(u1);
        bez.push([k === 0 ? Xa : p0, [p0[0] + d0[0] * du / 3, p0[1] + d0[1] * du / 3], [p1[0] - d1[0] * du / 3, p1[1] - d1[1] * du / 3], k === m - 1 ? Xb : p1]);
      }
      return { bez, L };
    }
    // ---- spans per strand
    const spansOf = [];   // per strand: [{ i0, i1, q, Ta, Tb, m, fit }]
    S.forEach((st, sid) => {
      const nd = st.nodes, n = nd.length, s = out[sid];
      const xs = []; nd.forEach((p, i) => { if (p.fixed && p.tag >= 0 && s.gridAt.has(p.tag)) xs.push(i); });
      const spans = [];
      const tangentAt = (i) => { const t = s.gridAt.get(nd[i].tag); return t; };
      const freeTangent = (i) => { const A = nd[(i - 1 + n) % n], B = nd[(i + 1) % n]; const tx = B.x - A.x, ty = B.y - A.y, l = Math.hypot(tx, ty) || 1; return [tx / l, ty / l]; };
      const mk = (i0, i1, Ta, Tb) => { const q = []; for (let k = i0; k <= i1; k++) { const p = nd[k % n]; q.push([p.x, p.y]); } return { i0, i1, q, Ta, Tb }; };
      if (!xs.length) {   // no crossing at all: one span round the loop (or along the chain) with free end tangents
        if (st.closed) spans.push(mk(0, n, freeTangent(0), freeTangent(0)));
        else spans.push(mk(0, n - 1, freeTangent(0), freeTangent(n - 1)));
      } else if (st.closed) {
        for (let q = 0; q < xs.length; q++) { const a = xs[q], b = q + 1 < xs.length ? xs[q + 1] : xs[0] + n; spans.push(mk(a, b, tangentAt(a), tangentAt(xs[(q + 1) % xs.length]))); }
      } else {
        if (xs[0] > 0) spans.push(mk(0, xs[0], freeTangent(0), tangentAt(xs[0])));
        for (let q = 0; q + 1 < xs.length; q++) spans.push(mk(xs[q], xs[q + 1], tangentAt(xs[q]), tangentAt(xs[q + 1])));
        if (xs[xs.length - 1] < n - 1) spans.push(mk(xs[xs.length - 1], n - 1, tangentAt(xs[xs.length - 1]), freeTangent(n - 1)));
      }
      for (const sp of spans) { const K = sp.q.length - 1; let L = 0; for (let i = 1; i <= K; i++) L += Math.hypot(sp.q[i][0] - sp.q[i - 1][0], sp.q[i][1] - sp.q[i - 1][1]); sp.len = L; sp.m = Math.max(1, Math.min(Math.round(L / DELTA), Math.max(1, Math.floor(K / 4)))); sp.mMax = Math.max(1, K - 2); }
      spansOf.push(spans);
    });
    const doFit = (sp) => { sp.fit = fitSpan(sp.q, sp.Ta, sp.Tb, sp.m); };
    spansOf.forEach((spans) => spans.forEach(doFit));
    // ---- validity: flatten and look for crossings between strands (and with edges); refine offending spans
    const flat = (bz, k) => { const pts = []; for (let i = 0; i <= k; i++) { const t = i / k, mt = 1 - t; pts.push([mt * mt * mt * bz[0][0] + 3 * mt * mt * t * bz[1][0] + 3 * mt * t * t * bz[2][0] + t * t * t * bz[3][0], mt * mt * mt * bz[0][1] + 3 * mt * mt * t * bz[1][1] + 3 * mt * t * t * bz[2][1] + t * t * t * bz[3][1]]); } return pts; };
    let refined = 0;
    for (let round = 0; round < prm.fitRounds; round++) {
      // sample segments: [x0,y0,x1,y1, sid, span index, piece index]
      const segs = [];
      spansOf.forEach((spans, sid) => spans.forEach((sp, si) => sp.fit.bez.forEach((bz) => { const k = Math.max(2, Math.ceil(sp.len / sp.m / h)); const pts = flat(bz, k); for (let i = 0; i + 1 < pts.length; i++) segs.push([pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1], sid, si]); })));
      const cs = 0.5, key = (x, y) => Math.floor(x / cs) * 73856093 ^ Math.floor(y / cs) * 19349663;
      const grid = new Map();
      segs.forEach((sg, id) => { const x0 = Math.min(sg[0], sg[2]), x1 = Math.max(sg[0], sg[2]), y0 = Math.min(sg[1], sg[3]), y1 = Math.max(sg[1], sg[3]); for (let cx = Math.floor(x0 / cs); cx <= Math.floor(x1 / cs); cx++) for (let cy = Math.floor(y0 / cs); cy <= Math.floor(y1 / cs); cy++) { const k = key(cx * cs + 1e-9, cy * cs + 1e-9); let l = grid.get(k); if (!l) { l = []; grid.set(k, l); } l.push(id); } });
      const obGrid = new Map();
      obstacles.forEach(([p, q, , , rad], id) => { if (rad) return; const x0 = Math.min(p[0], q[0]), x1 = Math.max(p[0], q[0]), y0 = Math.min(p[1], q[1]), y1 = Math.max(p[1], q[1]); for (let cx = Math.floor(x0 / cs); cx <= Math.floor(x1 / cs); cx++) for (let cy = Math.floor(y0 / cs); cy <= Math.floor(y1 / cs); cy++) { const k = key(cx * cs + 1e-9, cy * cs + 1e-9); let l = obGrid.get(k); if (!l) { l = []; obGrid.set(k, l); } l.push(id); } });
      const bad = new Set();
      const same = (ax, ay, bx, by) => Math.abs(ax - bx) < 1e-9 && Math.abs(ay - by) < 1e-9;
      segs.forEach((sg, id) => {
        const x0 = Math.min(sg[0], sg[2]), x1 = Math.max(sg[0], sg[2]), y0 = Math.min(sg[1], sg[3]), y1 = Math.max(sg[1], sg[3]);
        const seen = new Set();
        for (let cx = Math.floor(x0 / cs); cx <= Math.floor(x1 / cs); cx++) for (let cy = Math.floor(y0 / cs); cy <= Math.floor(y1 / cs); cy++) {
          const k = key(cx * cs + 1e-9, cy * cs + 1e-9);
          for (const jd of (grid.get(k) || [])) {
            if (jd <= id || seen.has(jd)) continue; seen.add(jd);
            const o = segs[jd];
            if (same(sg[2], sg[3], o[0], o[1]) || same(o[2], o[3], sg[0], sg[1]) || same(sg[0], sg[1], o[0], o[1]) || same(sg[2], sg[3], o[2], o[3])) continue;   // consecutive pieces / shared crossing point
            if (properCrossXY(sg[0], sg[1], sg[2], sg[3], o[0], o[1], o[2], o[3])) { bad.add(sg[4] + ':' + sg[5]); bad.add(o[4] + ':' + o[5]); }
          }
          for (const od of (obGrid.get(k) || [])) {
            const [p, q] = obstacles[od];
            if (properCrossXY(sg[0], sg[1], sg[2], sg[3], p[0], p[1], q[0], q[1])) bad.add(sg[4] + ':' + sg[5]);
          }
        }
      });
      if (prm.fitDebug) console.log('fit round', round, 'segs', segs.length, 'bad', bad.size);
      if (!bad.size) break;
      let any = false;
      for (const bk of bad) { const [sid, si] = bk.split(':').map(Number); const sp = spansOf[sid][si]; if (sp.m < sp.mMax) { sp.m = Math.min(sp.mMax, sp.m * 2); doFit(sp); any = true; refined++; } }
      if (!any) break;
    }
    // ---- write back: Bezier pieces, points at piece ends, crossing indices, piece junctions by arc position
    S.forEach((st, sid) => {
      const s = out[sid], spans = spansOf[sid], nd = st.nodes, n = nd.length;
      // arc length along the relaxed polyline
      const cum = [0]; for (let i = 1; i <= (st.closed ? n : n - 1); i++) { const A = nd[(i - 1) % n], B = nd[i % n]; cum.push(cum[i - 1] + Math.hypot(B.x - A.x, B.y - A.y)); }
      // junction tags -> absolute arc positions (their fractions refer to spans between consecutive fixed nodes)
      const fixedAt = []; nd.forEach((p, k) => { if (p.fixed) fixedAt.push(k); });
      const fspans = [];
      if (!fixedAt.length) fspans.push([0, st.closed ? n : n - 1]);
      else if (st.closed) for (let q = 0; q < fixedAt.length; q++) fspans.push([fixedAt[q], q + 1 < fixedAt.length ? fixedAt[q + 1] : fixedAt[0] + n]);
      else { if (fixedAt[0] > 0) fspans.push([0, fixedAt[0]]); for (let q = 0; q + 1 < fixedAt.length; q++) fspans.push([fixedAt[q], fixedAt[q + 1]]); if (fixedAt[fixedAt.length - 1] < n - 1) fspans.push([fixedAt[fixedAt.length - 1], n - 1]); }
      const total = cum[cum.length - 1];
      const juncPos = [];
      for (const [tag, jsi, fr] of st.juncs) { if (jsi < 0 || !fspans[jsi]) continue; const [k0, k1] = fspans[jsi]; const c0 = cum[Math.min(k0, cum.length - 1)], c1 = k1 < cum.length ? cum[k1] : total; juncPos.push([tag, c0 + fr * (c1 - c0)]); }
      const pts = [], bez = [], tagIdx = new Map(), endPos = [];
      spans.forEach((sp, si) => {
        const start = cum[Math.min(sp.i0, cum.length - 1)];
        if (si === 0) { pts.push(sp.fit.bez[0][0]); endPos.push(start); const tg = nd[sp.i0 % n].tag; if (tg >= 0) tagIdx.set(tg, 0); }
        sp.fit.bez.forEach((bz, k) => { bez.push([bz[1], bz[2]]); pts.push(bz[3]); endPos.push(start + sp.len * (k + 1) / sp.m); });
        const tg = nd[sp.i1 % n].tag; if (tg >= 0 && !tagIdx.has(tg)) tagIdx.set(tg, pts.length - 1);
      });
      if (st.closed && pts.length > 1) { pts.pop(); endPos.pop(); }   // last point repeats the first
      for (const [tag, pos] of juncPos) { if (tagIdx.has(tag)) continue; let best = 0, bd = Infinity; endPos.forEach((p, i) => { const d = Math.abs(p - pos); if (d < bd) { bd = d; best = i; } }); tagIdx.set(tag, best); }
      s.pts = pts; s.bez = bez; s.tang = null;
      const g2 = new Map(); for (const [i, t] of s.gridAt) { const k = tagIdx.get(i); if (k !== undefined) g2.set(k % Math.max(1, pts.length), t); } s.gridAt = g2;
      const origN = s.pts0;
      s.pieces = s.pieces.map(([seg, a, n2, d]) => { const a2 = tagIdx.get(a), b2 = st.closed && a + n2 === origN ? pts.length : tagIdx.get(a + n2); return [seg, a2 === undefined ? 0 : a2, a2 === undefined || b2 === undefined ? 0 : Math.max(0, b2 - a2), d]; });
    });
    return { refined };
  }
  // Fairing of the routed strands. Every strand becomes a dense polyline that relaxes like a stiff elastic band: each
  // point is pulled toward the midpoint of its neighbours (shortening, which takes up slack) and toward the position
  // that minimises bending; strands are kept at least dMin apart, kept dObs away from every tile edge and never allowed
  // to pass through each other or through an edge, so the knot's diagram (which strand crosses which, where) is kept
  // exactly. The crossing points stay where they are and the strands keep their 45-degree directions there (two anchor
  // points on each side of every crossing are fixed too). Points marked keep (piece junctions) survive resampling.
  function fairStrands(out, xings, obstacles, prm) {
    const h = prm.h, aT = prm.anchor, dMin = prm.dMin, dObs = prm.dObs, step = prm.step;
    const nS = out.length;
    // ---- 1. nodes: x, y, fixed, keep, tag (original index for keep points), per strand
    let S = out.map((s, sid) => {
      const n = s.pts.length, nodes = []; s.pts0 = n;
      const isX = new Map(); for (const [i, t] of s.gridAt) isX.set(i, t);
      const keepIdx = new Set(); for (const [, a, n2] of s.pieces) { keepIdx.add(a); keepIdx.add(a + n2); }
      for (let i = 0; i < n; i++) {
        const p = s.pts[i], t = isX.get(i);
        if (t && !(s.closed === false && i === 0)) nodes.push({ x: p[0] - aT * t[0], y: p[1] - aT * t[1], fixed: 1, keep: 0, tag: -1 });
        nodes.push({ x: p[0], y: p[1], fixed: t ? 1 : 0, keep: 0, tag: i, junc: keepIdx.has(i) ? 1 : 0 });
        if (t && !(s.closed === false && i === n - 1)) nodes.push({ x: p[0] + aT * t[0], y: p[1] + aT * t[1], fixed: 1, keep: 0, tag: -1 });
      }
      // drop free points crowded against an anchor (closer than 1.5 aT to a crossing point)
      const outN = [];
      for (let k = 0; k < nodes.length; k++) {
        const nd = nodes[k];
        if (!nd.fixed) {
          let near = false;
          for (let q = Math.max(0, k - 3); q <= Math.min(nodes.length - 1, k + 3); q++) if (nodes[q].fixed && nodes[q].tag >= 0 && Math.hypot(nodes[q].x - nd.x, nodes[q].y - nd.y) < 1.5 * aT) near = true;
          if (near) { if (nd.junc) nd.dropped = true; else continue; }
        }
        outN.push(nd);
      }
      // piece junctions are remembered as a fraction of the arc length of the free span they lie in
      const juncs = [];   // [tag, spanIndex, fraction]
      {
        const nn = outN.length, fixedAt = []; outN.forEach((p, k) => { if (p.fixed) fixedAt.push(k); });
        const spans = [];   // [k0, k1] unwrapped
        if (!fixedAt.length) spans.push([0, s.closed ? nn : nn - 1]);
        else if (s.closed) for (let q = 0; q < fixedAt.length; q++) spans.push([fixedAt[q], q + 1 < fixedAt.length ? fixedAt[q + 1] : fixedAt[0] + nn]);
        else { if (fixedAt[0] > 0) spans.push([0, fixedAt[0]]); for (let q = 0; q + 1 < fixedAt.length; q++) spans.push([fixedAt[q], fixedAt[q + 1]]); if (fixedAt[fixedAt.length - 1] < nn - 1) spans.push([fixedAt[fixedAt.length - 1], nn - 1]); }
        spans.forEach(([k0, k1], si) => {
          let L = 0; const cum = [0];
          for (let k = k0; k < k1; k++) { const A = outN[k % nn], B = outN[(k + 1) % nn]; L += Math.hypot(B.x - A.x, B.y - A.y); cum.push(L); }
          for (let k = k0; k <= k1; k++) { const p = outN[k % nn]; if (p.junc && !p.fixed) juncs.push([p.tag, si, L > 0 ? cum[k - k0] / L : 0]); }
        });
        for (const p of outN) if (p.fixed && p.tag >= 0) juncs.push([p.tag, -1, 0]);
      }
      if (prm.debug) console.log('strand', sid, 'closed', s.closed, 'gridAt', JSON.stringify([...s.gridAt].map(([i, t]) => [i, +t[0].toFixed(2), +t[1].toFixed(2)])), 'pts', JSON.stringify(s.pts.slice(0, 4).map((p) => [+p[0].toFixed(2), +p[1].toFixed(2)])), 'nodes', JSON.stringify(outN.slice(0, 5).map((p) => [+p.x.toFixed(2), +p.y.toFixed(2), p.fixed])));
      return { nodes: outN.filter((p) => !p.dropped), closed: s.closed, juncs };
    });
    // ---- 2. flatten + resample helpers
    let X, Y, FIX, TAG, SID, LAB, LABD, start, cnt, N, tagAt;
    const CLOSED = new Uint8Array(nS); S.forEach((st, s) => { CLOSED[s] = st.closed ? 1 : 0; });
    const nxt = (i) => { const s = SID[i], e = start[s] + cnt[s] - 1; return i < e ? i + 1 : (CLOSED[s] ? start[s] : -1); };
    const prv = (i) => { const s = SID[i]; return i > start[s] ? i - 1 : (CLOSED[s] ? start[s] + cnt[s] - 1 : -1); };
    function resample() {
      for (const st of S) {
        const nd = st.nodes, n = nd.length; if (n < 2) continue;
        let ks = []; nd.forEach((p, i) => { if (p.fixed) ks.push(i); });
        if (!ks.length) ks = [0];
        const res = [];
        const span = (i0, i1) => {   // resample the open run from node i0 to node i1 (cyclic indices), excluding i1
          const pts = [nd[i0]]; let i = i0; do { i = (i + 1) % n; pts.push(nd[i]); } while (i !== i1 && pts.length <= n);
          const cum = [0]; for (let k = 1; k < pts.length; k++) cum.push(cum[k - 1] + Math.hypot(pts[k].x - pts[k - 1].x, pts[k].y - pts[k - 1].y));
          const L = cum[cum.length - 1], m = Math.max(1, Math.round(L / h));
          res.push(nd[i0]);
          let k = 0;
          for (let q = 1; q < m; q++) {
            const s = L * q / m; while (k < cum.length - 2 && cum[k + 1] < s) k++;
            const t = cum[k + 1] > cum[k] ? (s - cum[k]) / (cum[k + 1] - cum[k]) : 0;
            res.push({ x: pts[k].x + t * (pts[k + 1].x - pts[k].x), y: pts[k].y + t * (pts[k + 1].y - pts[k].y), fixed: 0, tag: -1 });
          }
        };
        if (st.closed) { for (let q = 0; q < ks.length; q++) span(ks[q], ks[(q + 1) % ks.length]); }
        else {
          if (ks[0] !== 0) ks.unshift(0);
          if (ks[ks.length - 1] !== n - 1) ks.push(n - 1);
          for (let q = 0; q + 1 < ks.length; q++) span(ks[q], ks[q + 1]);
          res.push(nd[n - 1]);
        }
        st.nodes = res;
      }
      N = 0; start = new Int32Array(nS); cnt = new Int32Array(nS);
      S.forEach((st, s) => { start[s] = N; cnt[s] = st.nodes.length; N += st.nodes.length; });
      X = new Float64Array(N); Y = new Float64Array(N); FIX = new Uint8Array(N); TAG = new Int32Array(N); SID = new Int32Array(N); LAB = new Int32Array(2 * N).fill(-1); LABD = new Int32Array(2 * N);
      S.forEach((st, s) => st.nodes.forEach((p, i) => { const g = start[s] + i; X[g] = p.x; Y[g] = p.y; FIX[g] = p.fixed; TAG[g] = p.tag; SID[g] = s; }));
      // crossing labels: every point within arc distance dMin of a crossing point carries that crossing's id
      const W = Math.ceil(dMin / h);
      tagAt = new Map(); for (let g = 0; g < N; g++) if (TAG[g] >= 0) tagAt.set(SID[g] * 4194304 + TAG[g], g);
      xings.forEach(([sa, ia, sb, ib], xid) => {
        for (const [s, i] of [[sa, ia], [sb, ib]]) {
          const g0 = tagAt.get(s * 4194304 + i); if (g0 === undefined) continue;
          const mark = (g, q) => { if (LAB[2 * g] < 0 || LAB[2 * g] === xid) { LAB[2 * g] = xid; LABD[2 * g] = q; } else { LAB[2 * g + 1] = xid; LABD[2 * g + 1] = q; } };
          let g = g0; for (let q = 0; q <= W && g >= 0; q++) { mark(g, q); g = nxt(g); if (g === g0) break; }
          g = prv(g0); for (let q = 1; q <= W && g >= 0; q++) { mark(g, q); g = prv(g); if (g === g0) break; }
        }
      });
    }
    const unload = () => { S.forEach((st, s) => { st.nodes = []; for (let i = 0; i < cnt[s]; i++) { const g = start[s] + i; st.nodes.push({ x: X[g], y: Y[g], fixed: FIX[g], tag: TAG[g] }); } }); };
    resample();
    // ---- 3. spatial grids
    let minx = Infinity, miny = Infinity, maxx = -Infinity, maxy = -Infinity;
    for (let g = 0; g < N; g++) { if (X[g] < minx) minx = X[g]; if (X[g] > maxx) maxx = X[g]; if (Y[g] < miny) miny = Y[g]; if (Y[g] > maxy) maxy = Y[g]; }
    for (const [p, q] of obstacles) { minx = Math.min(minx, p[0], q[0]); maxx = Math.max(maxx, p[0], q[0]); miny = Math.min(miny, p[1], q[1]); maxy = Math.max(maxy, p[1], q[1]); }
    minx -= 1; miny -= 1; maxx += 1; maxy += 1;
    const cs = Math.max(dMin, 5 * h, dObs, prm.rVertex || 0);
    const GW = Math.ceil((maxx - minx) / cs) + 1, GH = Math.ceil((maxy - miny) / cs) + 1;
    const cellOf = (x, y) => { let cx = Math.floor((x - minx) / cs), cy = Math.floor((y - miny) / cs); cx = cx < 0 ? 0 : cx >= GW ? GW - 1 : cx; cy = cy < 0 ? 0 : cy >= GH ? GH - 1 : cy; return cy * GW + cx; };
    // obstacles: static cell lists
    const obHead = new Int32Array(GW * GH + 1); const obList = [];
    {
      const per = [];
      obstacles.forEach(([p0, q0, full], id) => {
        const p = full ? full[0] : p0, q = full ? full[1] : q0, ex = h + (obstacles[id][4] || 0);
        const x0 = Math.min(p[0], q[0]) - ex, x1 = Math.max(p[0], q[0]) + ex, y0 = Math.min(p[1], q[1]) - ex, y1 = Math.max(p[1], q[1]) + ex;
        const c0 = cellOf(x0, y0), c1 = cellOf(x1, y1); const cx0 = c0 % GW, cy0 = (c0 / GW) | 0, cx1 = c1 % GW, cy1 = (c1 / GW) | 0;
        for (let cy = cy0; cy <= cy1; cy++) for (let cx = cx0; cx <= cx1; cx++) per.push([cy * GW + cx, id]);
      });
      per.sort((a, b) => a[0] - b[0]);
      let k = 0; for (let c = 0; c < GW * GH; c++) { obHead[c] = obList.length; while (k < per.length && per[k][0] === c) obList.push(per[k++][1]); } obHead[GW * GH] = obList.length;
    }
    const OBX0 = new Float64Array(obstacles.length), OBY0 = new Float64Array(obstacles.length), OBX1 = new Float64Array(obstacles.length), OBY1 = new Float64Array(obstacles.length), OBXID = new Int32Array(obstacles.length).fill(-1), OBR = new Float64Array(obstacles.length).fill(dObs);
    { const keyToX = new Map(); xings.forEach((x, i) => { if (x[5]) keyToX.set(x[5], i); }); obstacles.forEach(([p, q, , key, rad], id) => { OBX0[id] = p[0]; OBY0[id] = p[1]; OBX1[id] = q[0]; OBY1[id] = q[1]; if (key && keyToX.has(key)) OBXID[id] = keyToX.get(key); if (rad) OBR[id] = rad; }); }
    // points: counting-sort grid rebuilt per iteration
    let head = new Int32Array(GW * GH + 1), order = new Int32Array(N), cellP = new Int32Array(N);
    function buildGrid(PX, PY) {
      if (order.length !== N) { order = new Int32Array(N); cellP = new Int32Array(N); }
      head.fill(0);
      for (let g = 0; g < N; g++) { const c = cellOf(PX[g], PY[g]); cellP[g] = c; head[c + 1]++; }
      for (let c = 0; c < GW * GH; c++) head[c + 1] += head[c];
      const fillp = head.slice(0, GW * GH);
      for (let g = 0; g < N; g++) order[fillp[cellP[g]]++] = g;
    }
    const orient = (ax, ay, bx, by, cx, cy) => (bx - ax) * (cy - ay) - (by - ay) * (cx - ax);
    const properCross = (ax, ay, bx, by, cx, cy, dx, dy) => {
      const d1 = orient(cx, cy, dx, dy, ax, ay), d2 = orient(cx, cy, dx, dy, bx, by), d3 = orient(ax, ay, bx, by, cx, cy), d4 = orient(ax, ay, bx, by, dx, dy);
      return ((d1 > 1e-12 && d2 < -1e-12) || (d1 < -1e-12 && d2 > 1e-12)) && ((d3 > 1e-12 && d4 < -1e-12) || (d3 < -1e-12 && d4 > 1e-12));
    };
    const segDist2 = (px, py, ax, ay, bx, by) => { const vx = bx - ax, vy = by - ay, L2 = vx * vx + vy * vy; let t = L2 > 1e-18 ? ((px - ax) * vx + (py - ay) * vy) / L2 : 0; t = t < 0 ? 0 : t > 1 ? 1 : t; const dx = ax + t * vx - px, dy = ay + t * vy - py; return [dx * dx + dy * dy, t]; };
    const arcGap = (i, j) => { const s = SID[i], n = cnt[s]; let d = i > j ? i - j : j - i; if (CLOSED[s] && n - d < d) d = n - d; return d; };
    const shareLab = (i, j) => { const a = LAB[2 * i], b = LAB[2 * i + 1], c = LAB[2 * j], d = LAB[2 * j + 1]; return (a >= 0 && (a === c || a === d)) || (b >= 0 && (b === c || b === d)); };
    // for two points near the same crossing: the larger of their arc distances from it (in index steps), else -1
    const sharedDist = (i, j) => {
      const a = LAB[2 * i], b = LAB[2 * i + 1], c = LAB[2 * j], d = LAB[2 * j + 1]; let best = -1, t;
      if (a === c) { t = LABD[2 * i] > LABD[2 * j] ? LABD[2 * i] : LABD[2 * j]; if (t > best) best = t; }
      if (a === d && d >= 0) { t = LABD[2 * i] > LABD[2 * j + 1] ? LABD[2 * i] : LABD[2 * j + 1]; if (t > best) best = t; }
      if (b >= 0 && b === c) { t = LABD[2 * i + 1] > LABD[2 * j] ? LABD[2 * i + 1] : LABD[2 * j]; if (t > best) best = t; }
      if (b >= 0 && b === d) { t = LABD[2 * i + 1] > LABD[2 * j + 1] ? LABD[2 * i + 1] : LABD[2 * j + 1]; if (t > best) best = t; }
      return best;
    };
    // does segment (i, nxt(i)) at the given coordinates cross any other segment or any obstacle?
    function segBlocked(i, PX, PY) {
      const j = nxt(i); if (j < 0) return false;
      const ax = PX[i], ay = PY[i], bx = PX[j], by = PY[j];
      for (let e = 0; e < 2; e++) {
        const g0 = e === 0 ? i : j;
        const c = cellP.length === N ? cellP[g0] : cellOf(PX[g0], PY[g0]), cx = c % GW, cy = (c / GW) | 0;
        for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
          const ccx = cx + dx, ccy = cy + dy; if (ccx < 0 || ccy < 0 || ccx >= GW || ccy >= GH) continue;
          const cc = ccy * GW + ccx;
          for (let q = head[cc]; q < head[cc + 1]; q++) {
            const k = order[q], l = nxt(k); if (l < 0 || k === i) continue;
            if (k === j || l === i || l === j) continue;   // shares an endpoint with the moving segment
            if (properCross(ax, ay, bx, by, PX[k], PY[k], PX[l], PY[l])) return true;
          }
          if (g0 === i) for (let q = obHead[cc]; q < obHead[cc + 1]; q++) { const o = obList[q]; if (properCross(ax, ay, bx, by, OBX0[o], OBY0[o], OBX1[o], OBY1[o])) return true; }
        }
      }
      return false;
    }
    // ---- 4. relaxation. Target shape: the smoothest curve (least bending energy) through the fixed points, found by an
    // implicit solve on every free span between fixed points; every point moves toward it by at most `step` per
    // iteration, pushed apart from other strands and tile edges, and any move that would cross something is rejected.
    const kSelf = Math.ceil((prm.selfGap || Math.PI * dMin / 2) / h) + 1;
    let NX = new Float64Array(N), NY = new Float64Array(N), moved = new Uint8Array(N), TX = new Float64Array(N), TY = new Float64Array(N);
    let stats = { rejected: 0, initialBlocked: 0, points: N };
    buildGrid(X, Y); stats.blockedAt = []; for (let g = 0; g < N; g++) if (segBlocked(g, X, Y)) { stats.initialBlocked++; if (stats.blockedAt.length < 12) stats.blockedAt.push([SID[g], g - start[SID[g]], +X[g].toFixed(3), +Y[g].toFixed(3), FIX[g]]); }
    const eps = 1 / prm.lambda;
    // banded (bandwidth 2) symmetric positive definite solve, A = L D L^T
    function bandSolve(m, d0, d1, d2, rx, ry) {
      const L1 = new Float64Array(m), L2 = new Float64Array(m), D = new Float64Array(m);
      for (let i = 0; i < m; i++) {
        L2[i] = i >= 2 ? d2[i - 2] / D[i - 2] : 0;
        L1[i] = i >= 1 ? (d1[i - 1] - (i >= 2 ? L2[i] * D[i - 2] * L1[i - 1] : 0)) / D[i - 1] : 0;
        D[i] = d0[i] - (i >= 2 ? L2[i] * L2[i] * D[i - 2] : 0) - (i >= 1 ? L1[i] * L1[i] * D[i - 1] : 0);
      }
      for (let i = 0; i < m; i++) { if (i >= 1) { rx[i] -= L1[i] * rx[i - 1]; ry[i] -= L1[i] * ry[i - 1]; } if (i >= 2) { rx[i] -= L2[i] * rx[i - 2]; ry[i] -= L2[i] * ry[i - 2]; } }
      for (let i = 0; i < m; i++) { rx[i] /= D[i]; ry[i] /= D[i]; }
      for (let i = m - 1; i >= 0; i--) { if (i + 1 < m) { rx[i] -= L1[i + 1] * rx[i + 1]; ry[i] -= L1[i + 1] * ry[i + 1]; } if (i + 2 < m) { rx[i] -= L2[i + 2] * rx[i + 2]; ry[i] -= L2[i + 2] * ry[i + 2]; } }
    }
    let PUX = new Float64Array(N), PUY = new Float64Array(N), NEAR = new Uint8Array(N);
    const nearR2 = Math.pow(2.5 * h + 2 * step, 2);   // a segment can only be crossed by something whose endpoint is this close
    // contact pushes: away from other strands closer than dMin and from tile edges closer than dObs
    function pushes() {
      for (let g = 0; g < N; g++) {
        PUX[g] = 0; PUY[g] = 0; NEAR[g] = 0; if (FIX[g]) continue;
        let fx = 0, fy = 0;
        const c = cellP[g], cx = c % GW, cy = (c / GW) | 0;
        for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
          const ccx = cx + dx, ccy = cy + dy; if (ccx < 0 || ccy < 0 || ccx >= GW || ccy >= GH) continue;
          const cc = ccy * GW + ccx;
          for (let q = head[cc]; q < head[cc + 1]; q++) {
            const k = order[q]; if (k === g) continue;
            if (SID[k] === SID[g] && arcGap(g, k) <= kSelf) continue;
            // near a shared crossing the two strands meet at right angles: the clearance is a cone, not a band
            let clr = dMin; if (LAB[2 * g] >= 0 && LAB[2 * k] >= 0) { const sd = sharedDist(g, k); if (sd >= 0) clr = Math.min(dMin, prm.cone * sd * h); }
            const vx = X[g] - X[k], vy = Y[g] - Y[k], d2 = vx * vx + vy * vy;
            if (d2 < nearR2) NEAR[g] = 1;
            if (d2 >= clr * clr || d2 < 1e-18) continue;
            const d = Math.sqrt(d2), push = (clr - d) * (FIX[k] ? 1 : 0.5);
            fx += push * vx / d; fy += push * vy / d;
          }
          for (let q = obHead[cc]; q < obHead[cc + 1]; q++) {
            const o = obList[q]; const [d2, t] = segDist2(X[g], Y[g], OBX0[o], OBY0[o], OBX1[o], OBY1[o]);
            if (d2 < nearR2) NEAR[g] = 1;
            // near its own crossing a strand leaves the edge at 45 degrees: the clearance there is a cone, not a band
            let clr = OBR[o]; const xo = OBXID[o];
            if (xo >= 0) { if (LAB[2 * g] === xo) clr = Math.min(dObs, prm.cone * LABD[2 * g] * h); else if (LAB[2 * g + 1] === xo) clr = Math.min(dObs, prm.cone * LABD[2 * g + 1] * h); }
            if (d2 >= clr * clr || d2 < 1e-18) continue;
            const d = Math.sqrt(d2), qx = OBX0[o] + t * (OBX1[o] - OBX0[o]), qy = OBY0[o] + t * (OBY1[o] - OBY0[o]);
            const push = clr - d; fx += push * (X[g] - qx) / d; fy += push * (Y[g] - qy) / d;
          }
        }
        PUX[g] = fx; PUY[g] = fy;
      }
    }
    const wC = prm.wContact, tau = prm.tension;
    let ACT = new Uint8Array(N);
    // per-span system structure (matrix bands and the fixed-point coupling terms), rebuilt after every resample
    let SPANS = null;
    function buildSpans() {
      SPANS = [];
      for (let s = 0; s < nS; s++) {
        const st = start[s], n = cnt[s];
        let f0 = -1; for (let i = 0; i < n; i++) if (FIX[st + i]) { f0 = i; break; }
        if (f0 < 0) continue;   // free loop / chain: handled explicitly in targets()
        const at = (k) => st + (CLOSED[s] ? ((k % n) + n) % n : k);
        const ok = (k) => CLOSED[s] || (k >= 0 && k < n);
        let k = CLOSED[s] ? f0 + 1 : 0; const end = CLOSED[s] ? f0 + n : n;
        while (k < end) {
          if (FIX[at(k)]) { k++; continue; }
          let a = k; while (k < end && !FIX[at(k)]) k++; let b = k - 1;
          const m = b - a + 1;
          const d0 = new Float64Array(m), d1 = new Float64Array(m), d2 = new Float64Array(m);
          const rhsJ = [], rhsG = [], rhsC = [];   // rhs[j] -= c * X[g]
          const add = (j, kk, c) => { if (kk >= a && kk <= b) { const dd = kk - j; if (dd === 0) d0[j - a] += c; else if (dd === 1) d1[j - a] += c; else if (dd === 2) d2[j - a] += c; } else { rhsJ.push(j - a); rhsG.push(at(kk)); rhsC.push(c); } };
          for (let i = a - 1; i <= b + 1; i++) {   // bending |p[i-1] - 2 p[i] + p[i+1]|^2, stiffer next to fixed points
            if (!ok(i - 1) || !ok(i) || !ok(i + 1)) continue;
            let wb = 1;
            if (prm.clamp > 1) { let dfx = 1e9; for (let q = -prm.taper; q <= prm.taper; q++) { if (ok(i + q) && FIX[at(i + q)]) dfx = Math.min(dfx, Math.abs(q)); } if (dfx <= prm.taper) wb = Math.max(1, prm.clamp / Math.pow(2, dfx)); }
            const idx = [i - 1, i, i + 1], cf = [1, -2, 1];
            for (let u = 0; u < 3; u++) { const j = idx[u]; if (j < a || j > b) continue; for (let v = 0; v < 3; v++) if (idx[v] >= j) add(j, idx[v], wb * cf[u] * cf[v]); else if (idx[v] < a || idx[v] > b) add(j, idx[v], wb * cf[u] * cf[v]); }
          }
          for (let i = a - 1; i <= b; i++) {   // tension tau |p[i+1] - p[i]|^2
            if (!ok(i) || !ok(i + 1)) continue;
            const idx = [i, i + 1], cf = [-1, 1];
            for (let u = 0; u < 2; u++) { const j = idx[u]; if (j < a || j > b) continue; for (let v = 0; v < 2; v++) if (idx[v] >= j) add(j, idx[v], tau * cf[u] * cf[v]); else if (idx[v] < a || idx[v] > b) add(j, idx[v], tau * cf[u] * cf[v]); }
          }
          const gs = new Int32Array(m); for (let j = 0; j < m; j++) gs[j] = at(a + j);
          SPANS.push({ m, d0, d1, d2, gs, rhsJ: Int32Array.from(rhsJ), rhsG: Int32Array.from(rhsG), rhsC: Float64Array.from(rhsC), w0: new Float64Array(m), w1: new Float64Array(m), w2: new Float64Array(m), rx: new Float64Array(m), ry: new Float64Array(m) });
        }
      }
    }
    function targets(withContacts) {
      if (!SPANS) buildSpans();
      for (let s = 0; s < nS; s++) {
        const st = start[s], n = cnt[s];
        let f0 = -1; for (let i = 0; i < n; i++) if (FIX[st + i]) { f0 = i; break; }
        if (f0 < 0) {   // free loop or free open chain: plain Laplacian smoothing plus the pushes
          for (let i = 0; i < n; i++) { const g = st + i, p = prv(g), q = nxt(g); if (p < 0 || q < 0) { TX[g] = X[g]; TY[g] = Y[g]; } else { TX[g] = X[g] + prm.alpha * (0.5 * (X[p] + X[q]) - X[g]) + PUX[g]; TY[g] = Y[g] + prm.alpha * (0.5 * (Y[p] + Y[q]) - Y[g]) + PUY[g]; } }
          continue;
        }
        for (let i = 0; i < n; i++) if (FIX[st + i]) { TX[st + i] = X[st + i]; TY[st + i] = Y[st + i]; }
      }
      for (const sp of SPANS) {
        const { m, gs, rhsJ, rhsG, rhsC, w0, w1, w2, rx, ry } = sp;
        w0.set(sp.d0); w1.set(sp.d1); w2.set(sp.d2); rx.fill(0); ry.fill(0);
        for (let q = 0; q < rhsJ.length; q++) { const j = rhsJ[q], g = rhsG[q], c = rhsC[q]; rx[j] -= c * X[g]; ry[j] -= c * Y[g]; }
        for (let j = 0; j < m; j++) { const g = gs[j]; const w = withContacts && ACT[g] ? wC : eps; w0[j] += w; rx[j] += w * (X[g] + PUX[g]); ry[j] += w * (Y[g] + PUY[g]); }
        bandSolve(m, w0, w1, w2, rx, ry);
        for (let j = 0; j < m; j++) { const g = gs[j]; TX[g] = rx[j]; TY[g] = ry[j]; }
      }
    }
    // crossings that may turn start out facing the way their strands naturally run: each strand's direction through
    // the crossing is set from the chord between its neighbouring crossings, and the frame is the best right-angle fit
    const turnGroup = (xg, dth) => {
      const sl = xg[4], gX = tagAt.get(xg[0] * 4194304 + xg[1]); if (gX === undefined) return false;
      const cx = X[gX], cy = Y[gX], group = [];
      for (const [s, i] of [[xg[0], xg[1]], [xg[2], xg[3]]]) {
        const g0 = tagAt.get(s * 4194304 + i); if (g0 === undefined) continue;
        for (const dir of [-1, 1]) { let g = g0; for (;;) { const nb = dir < 0 ? prv(g) : nxt(g); if (nb < 0 || nb === g0 || !FIX[nb]) break; g = nb; group.push(g); } }
      }
      const c = Math.cos(dth), sn = Math.sin(dth);
      if (NX.length !== N) { NX = new Float64Array(N); NY = new Float64Array(N); }
      NX.set(X); NY.set(Y);
      for (const g of group) { const dx = X[g] - cx, dy = Y[g] - cy; NX[g] = cx + c * dx - sn * dy; NY[g] = cy + sn * dx + c * dy; }
      for (const g of group) { const p = prv(g); if (segBlocked(g, NX, NY) || (p >= 0 && segBlocked(p, NX, NY))) return false; }
      for (const g of group) { X[g] = NX[g]; Y[g] = NY[g]; }
      sl.theta += dth; return true;
    };
    if (prm.rotate && prm.initTurn) {
      buildGrid(X, Y);
      for (const xg of xings) {
        const sl = xg[4]; if (!sl || !sl.rot) continue;
        const gX = tagAt.get(xg[0] * 4194304 + xg[1]); if (gX === undefined) continue;
        // chord direction of each strand between the crossings (or ends) before and after this one
        const chords = [], dirs = [];
        for (const [s, i] of [[xg[0], xg[1]], [xg[2], xg[3]]]) {
          const g0 = tagAt.get(s * 4194304 + i); if (g0 === undefined) continue;
          const t = out[s].gridAt.get(i); if (!t) continue;
          let a = g0, b = g0; for (let q = 0; q < 4000; q++) { const nb = prv(a); if (nb < 0 || nb === g0) break; a = nb; if (TAG[a] >= 0 && out[s].gridAt.has(TAG[a])) break; }
          for (let q = 0; q < 4000; q++) { const nb = nxt(b); if (nb < 0 || nb === g0) break; b = nb; if (TAG[b] >= 0 && out[s].gridAt.has(TAG[b])) break; }
          const dx = X[b] - X[a], dy = Y[b] - Y[a]; if (Math.hypot(dx, dy) < 1e-6) continue;
          chords.push(Math.atan2(dy, dx)); dirs.push(Math.atan2(t[1], t[0]));
        }
        if (chords.length !== 2) continue;
        // the frame turns by the mean of the two strands' wanted turns (each wrapped to [-pi/2, pi/2))
        let sum = 0; for (let q = 0; q < 2; q++) { let d = chords[q] - dirs[q]; d = Math.atan2(Math.sin(d), Math.cos(d)); sum += d; }
        let dth = sum / 2; dth = Math.max(-prm.initTurnMax, Math.min(prm.initTurnMax, dth));
        for (let tries = 0; tries < 4 && Math.abs(dth) > 1e-3; tries++) { if (turnGroup(xg, dth)) { stats.initTurned = (stats.initTurned || 0) + Math.abs(dth); break; } dth *= 0.5; }
      }
    }
    for (let it = 0; it < prm.iters; it++) {
      if (NX.length !== N) { NX = new Float64Array(N); NY = new Float64Array(N); moved = new Uint8Array(N); TX = new Float64Array(N); TY = new Float64Array(N); PUX = new Float64Array(N); PUY = new Float64Array(N); NEAR = new Uint8Array(N); }
      buildGrid(X, Y);
      pushes();
      // active set: a contact holds when the unconstrained target would move the point into (or keep it inside) the clearance
      targets(false);
      if (ACT.length !== N) ACT = new Uint8Array(N);
      let nAct = 0;
      for (let g = 0; g < N; g++) {
        ACT[g] = 0; if (FIX[g] || (PUX[g] === 0 && PUY[g] === 0)) continue;
        const pl = Math.hypot(PUX[g], PUY[g]);
        if ((TX[g] - X[g]) * PUX[g] + (TY[g] - Y[g]) * PUY[g] <= 0.3 * pl * pl || pl > 0.3 * dObs) { ACT[g] = 1; nAct++; }
      }
      // active-set refinement: a contact whose anchor would pull the point toward the obstacle is not a real contact
      for (let pass = 0; pass < prm.actPasses && nAct; pass++) {
        targets(true);
        let released = 0;
        for (let g = 0; g < N; g++) {
          if (!ACT[g]) continue;
          const fx = X[g] + PUX[g] - TX[g], fy = Y[g] + PUY[g] - TY[g];
          if (fx * PUX[g] + fy * PUY[g] < 0) { ACT[g] = 0; nAct--; released++; }
        }
        if (!released) break;
        if (pass === prm.actPasses - 1 || !nAct) targets(nAct > 0);
      }
      for (let g = 0; g < N; g++) {
        if (FIX[g]) { NX[g] = X[g]; NY[g] = Y[g]; moved[g] = 0; continue; }
        let fx = TX[g] - X[g], fy = TY[g] - Y[g];
        const fl = Math.hypot(fx, fy); if (fl > step) { fx *= step / fl; fy *= step / fl; }
        NX[g] = X[g] + fx; NY[g] = Y[g] + fy; moved[g] = (fx !== 0 || fy !== 0) ? 1 : 0;
      }
      // reject moves that make a strand pass through another strand, itself or a tile edge
      for (let pass = 0; pass < 8; pass++) {
        let any = false;
        for (let g = 0; g < N; g++) {
          if (!moved[g]) continue;
          const p = prv(g), n = nxt(g);
          if (!NEAR[g] && !(p >= 0 && NEAR[p]) && !(n >= 0 && NEAR[n])) continue;   // nothing within reach: a small move cannot cross anything
          if (segBlocked(g, NX, NY) || (p >= 0 && segBlocked(p, NX, NY))) { NX[g] = X[g]; NY[g] = Y[g]; moved[g] = 0; any = true; stats.rejected++; }
        }
        if (!any) break;
      }
      X.set(NX); Y.set(NY);
      // crossings slide along their edge, pulled by the four strand arms, so the knot balances itself
      for (const xg of xings) {
        const sl = xg[4]; if (!sl || !(sl.o1 < 0 ? prm.slideSpokes : prm.slide)) continue;
        const gX = tagAt.get(xg[0] * 4194304 + xg[1]); if (gX === undefined) continue;
        const group = [], arms = [];   // arms: a point a few steps beyond each anchor, as a lever on the crossing
        for (const [s, i] of [[xg[0], xg[1]], [xg[2], xg[3]]]) {
          const g0 = tagAt.get(s * 4194304 + i); if (g0 === undefined) continue;
          group.push(g0);
          for (const dir of [-1, 1]) {
            let g = g0, k = 0, contiguous = true; for (;;) { const nb = dir < 0 ? prv(g) : nxt(g); if (nb < 0 || nb === g0) { g = -1; break; } g = nb; if (FIX[g]) { if (contiguous) { group.push(g); continue; } g = -1; break; } contiguous = false; if (++k >= prm.lever) break; }
            if (g >= 0 && !FIX[g]) arms.push(g);
          }
        }
        if (!arms.length) continue;
        let pull = 0; for (const g of arms) pull += (X[g] - X[gX]) * sl.u[0] + (Y[g] - Y[gX]) * sl.u[1];
        let d = pull / arms.length * prm.slideGain; if (d > step) d = step; if (d < -step) d = -step;
        const t = (X[gX] - sl.A[0]) * sl.u[0] + (Y[gX] - sl.A[1]) * sl.u[1] + d;
        if ((t < sl.lo && d < 0) || (t > sl.hi && d > 0) || Math.abs(d) < 1e-9) continue;
        for (const g of group) { NX[g] = X[g] + d * sl.u[0]; NY[g] = Y[g] + d * sl.u[1]; }
        let ok = true;
        for (const g of group) { const p = prv(g); if (segBlocked(g, NX, NY) || (p >= 0 && segBlocked(p, NX, NY))) { ok = false; break; } }
        if (ok) {
          for (const g of group) { X[g] = NX[g]; Y[g] = NY[g]; }
          const Xn = [X[gX], Y[gX]];
          if (sl.o1 >= 0) { OBX1[sl.o1] = Xn[0]; OBY1[sl.o1] = Xn[1]; OBX0[sl.o2] = Xn[0]; OBY0[sl.o2] = Xn[1]; }
          stats.slid = (stats.slid || 0) + Math.abs(d);
        } else for (const g of group) { NX[g] = X[g]; NY[g] = Y[g]; }
      }
      // crossings on undrawn lines (spokes) are free to turn: the two strands still cross at right angles there
      if (prm.rotate) for (const xg of xings) {
        const sl = xg[4]; if (!sl || !sl.rot) continue;
        const gX = tagAt.get(xg[0] * 4194304 + xg[1]); if (gX === undefined) continue;
        const cx = X[gX], cy = Y[gX], group = []; let torque = 0, narm = 0;
        for (const [s, i] of [[xg[0], xg[1]], [xg[2], xg[3]]]) {
          const g0 = tagAt.get(s * 4194304 + i); if (g0 === undefined) continue;
          for (const dir of [-1, 1]) {
            let g = g0, last = g0, k = 0, contiguous = true; for (;;) { const nb = dir < 0 ? prv(g) : nxt(g); if (nb < 0 || nb === g0) { g = -1; break; } g = nb; if (FIX[g]) { if (contiguous) { last = g; group.push(g); continue; } g = -1; break; } contiguous = false; if (++k >= prm.lever) break; }
            if (g < 0 || FIX[g]) continue;
            const dx = X[last] - cx, dy = Y[last] - cy, tx = X[g] - cx, ty = Y[g] - cy;
            torque += Math.atan2(dx * ty - dy * tx, dx * tx + dy * ty); narm++;
          }
        }
        if (!narm) continue;
        let dth = torque / narm * prm.rotGain; const lim = step / Math.max(aT, 1e-6); if (dth > lim) dth = lim; if (dth < -lim) dth = -lim;
        if (Math.abs(dth) < 1e-6) continue;
        const c = Math.cos(dth), sn = Math.sin(dth);
        for (const g of group) { const dx = X[g] - cx, dy = Y[g] - cy; NX[g] = cx + c * dx - sn * dy; NY[g] = cy + sn * dx + c * dy; }
        let ok = true;
        for (const g of group) { const p = prv(g); if (segBlocked(g, NX, NY) || (p >= 0 && segBlocked(p, NX, NY))) { ok = false; break; } }
        if (ok) { for (const g of group) { X[g] = NX[g]; Y[g] = NY[g]; } sl.theta += dth; stats.turned = (stats.turned || 0) + Math.abs(dth); if (prm.debugRot) (stats.rotLog = stats.rotLog || []).push(+dth.toFixed(4)); }
        else for (const g of group) { NX[g] = X[g]; NY[g] = Y[g]; }
      }
      if ((it + 1) % prm.every === 0 && it + 1 < prm.iters) { unload(); resample(); SPANS = null; }
    }
    unload();
    // turned crossings: the fixed tangents follow
    for (const xg of xings) {
      const sl = xg[4]; if (!sl || !sl.rot || !sl.theta) continue;
      const c = Math.cos(sl.theta), sn = Math.sin(sl.theta);
      for (const [s, i] of [[xg[0], xg[1]], [xg[2], xg[3]]]) { const t = out[s].gridAt.get(i); if (t) out[s].gridAt.set(i, [c * t[0] - sn * t[1], sn * t[0] + c * t[1]]); }
      sl.theta = 0;
    }
    if (prm.keepDebug) { stats.nodes = S.map((st) => st.nodes.map((p) => [p.x, p.y, p.fixed])); stats.obstacles = obstacles; }
    { // clearance statistics
      let minD = Infinity, nClose = 0, where = null;
      for (let g = 0; g < N; g++) { if (FIX[g]) continue; for (let o = 0; o < obstacles.length; o++) { if (obstacles[o][4]) continue; const [d2] = segDist2(X[g], Y[g], OBX0[o], OBY0[o], OBX1[o], OBY1[o]); const d = Math.sqrt(d2); if (d < minD) { minD = d; where = [SID[g], g - start[SID[g]], +X[g].toFixed(3), +Y[g].toFixed(3)]; } if (d < 0.5 * dObs) nClose++; } }
      stats.minObs = +minD.toFixed(3); stats.nClose = nClose; stats.closeAt = where;
    }
    // ---- 5. write back
    if (prm.fit) {
      const properCrossXY = (ax, ay, bx, by, cx, cy, dx, dy) => properCross(ax, ay, bx, by, cx, cy, dx, dy);
      const r = fitSplines(S, out, obstacles, prm, { segDist2, properCrossXY });
      stats.refined = r.refined;
      return stats;
    }
    const tol2 = prm.tol * prm.tol;
    S.forEach((st, sid) => {
      const nd = st.nodes, n = nd.length, s = out[sid];
      const keepFlag = new Uint8Array(n); nd.forEach((p, i) => { if (p.fixed) keepFlag[i] = 1; });
      if (!st.closed) { keepFlag[0] = 1; keepFlag[n - 1] = 1; } else if (!keepFlag.some((v) => v)) keepFlag[0] = 1;
      const dp = (i0, i1) => {   // Douglas-Peucker on the open run i0..i1 (indices increasing, mod n for closed)
        const stack = [[i0, i1]];
        while (stack.length) {
          const [a, b] = stack.pop(); const len = b - a; if (len < 2) continue;
          const A = nd[a % n], B = nd[b % n]; let best = -1, bd = -1;
          for (let q = 1; q < len; q++) { const P = nd[(a + q) % n]; const [d2] = segDist2(P.x, P.y, A.x, A.y, B.x, B.y); if (d2 > bd) { bd = d2; best = a + q; } }
          if (bd > tol2) { keepFlag[best % n] = 1; stack.push([a, best], [best, b]); }
        }
      };
      const ks = []; for (let i = 0; i < n; i++) if (keepFlag[i]) ks.push(i);
      if (st.closed) { for (let q = 0; q < ks.length; q++) dp(ks[q], q + 1 < ks.length ? ks[q + 1] : ks[0] + n); }
      else for (let q = 0; q + 1 < ks.length; q++) dp(ks[q], ks[q + 1]);
      // never leave kept points further apart than maxSeg, so the Bezier conversion stays close to the dense curve
      {
        const maxN = Math.max(1, Math.round(prm.maxSeg / h));
        let last = -1, first = -1;
        for (let i = 0; i < n; i++) if (keepFlag[i]) { if (first < 0) first = i; if (last >= 0 && i - last > maxN) { const m = Math.ceil((i - last) / maxN); for (let q = 1; q < m; q++) keepFlag[last + Math.round((i - last) * q / m)] = 1; } last = i; }
        if (st.closed && first >= 0) { const gap = first + n - last; if (gap > maxN) { const m = Math.ceil(gap / maxN); for (let q = 1; q < m; q++) keepFlag[(last + Math.round(gap * q / m)) % n] = 1; } }
      }
      const pts = [], tang = [], tagIdx = new Map(), newIdx = new Int32Array(n).fill(-1);
      for (let i = 0; i < n; i++) {
        if (!keepFlag[i]) continue;
        const P = nd[i], A = nd[st.closed ? (i - 1 + n) % n : Math.max(0, i - 1)], B = nd[st.closed ? (i + 1) % n : Math.min(n - 1, i + 1)];
        const tx = B.x - A.x, ty = B.y - A.y, L = Math.hypot(tx, ty) || 1;
        if (P.tag >= 0) tagIdx.set(P.tag, pts.length);
        newIdx[i] = pts.length;
        pts.push([P.x, P.y]); tang.push([tx / L, ty / L]);
      }
      // piece junctions: the kept point nearest to the remembered fraction of its span
      {
        const fixedAt = []; nd.forEach((p, k) => { if (p.fixed) fixedAt.push(k); });
        const spans = [];
        if (!fixedAt.length) spans.push([0, st.closed ? n : n - 1]);
        else if (st.closed) for (let q = 0; q < fixedAt.length; q++) spans.push([fixedAt[q], q + 1 < fixedAt.length ? fixedAt[q + 1] : fixedAt[0] + n]);
        else { if (fixedAt[0] > 0) spans.push([0, fixedAt[0]]); for (let q = 0; q + 1 < fixedAt.length; q++) spans.push([fixedAt[q], fixedAt[q + 1]]); if (fixedAt[fixedAt.length - 1] < n - 1) spans.push([fixedAt[fixedAt.length - 1], n - 1]); }
        const cums = spans.map(([k0, k1]) => { let L = 0; const cum = [0]; for (let k = k0; k < k1; k++) { const A = nd[k % n], B = nd[(k + 1) % n]; L += Math.hypot(B.x - A.x, B.y - A.y); cum.push(L); } return cum; });
        for (const [tag, si, fr] of st.juncs) {
          if (si < 0 || !spans[si]) continue;
          const [k0, k1] = spans[si], cum = cums[si], L = cum[cum.length - 1], target = fr * L;
          let best = -1, bd = Infinity;
          for (let k = k0; k <= k1; k++) { const ni = newIdx[k % n]; if (ni < 0) continue; const d = Math.abs(cum[k - k0] - target); if (d < bd) { bd = d; best = ni; } }
          if (best >= 0 && !tagIdx.has(tag)) tagIdx.set(tag, best);
        }
      }
      s.pts = pts; s.tang = tang;
      const g2 = new Map(); for (const [i, t] of s.gridAt) { const k = tagIdx.get(i); if (k !== undefined) g2.set(k, t); } s.gridAt = g2;
      const origN = s.pts0;
      s.pieces = s.pieces.map(([seg, a, n2, d]) => { const a2 = tagIdx.get(a), b2 = st.closed && a + n2 === origN ? pts.length : tagIdx.get(a + n2); return [seg, a2 === undefined ? 0 : a2, a2 === undefined || b2 === undefined ? 0 : Math.max(0, b2 - a2), d]; });
    });
    return stats;
  }
  function simplifyStrands(out, crossingPts, crossMates, rimSegs, prm) {
    const margin = prm.margin;
    const inter = ((o, p, q) => (p[0] - o[0]) * (q[1] - o[1]) - (p[1] - o[1]) * (q[0] - o[0]));
    const properCross = (a, b, c, d) => { const d1 = inter(c, d, a), d2 = inter(c, d, b), d3 = inter(a, b, c), d4 = inter(a, b, d); return ((d1 > 1e-12 && d2 < -1e-12) || (d1 < -1e-12 && d2 > 1e-12)) && ((d3 > 1e-12 && d4 < -1e-12) || (d3 < -1e-12 && d4 > 1e-12)); };
    const segDist = (a, b, c, d) => {   // distance between segments ab and cd
      if (properCross(a, b, c, d)) return 0;
      const pd = (p, u, v) => { const vx = v[0] - u[0], vy = v[1] - u[1]; const L2 = vx * vx + vy * vy; let t = L2 > 1e-12 ? ((p[0] - u[0]) * vx + (p[1] - u[1]) * vy) / L2 : 0; t = t < 0 ? 0 : t > 1 ? 1 : t; return Math.hypot(u[0] + t * vx - p[0], u[1] + t * vy - p[1]); };
      return Math.min(pd(a, c, d), pd(b, c, d), pd(c, a, b), pd(d, a, b));
    };
    const same = (p, q) => Math.abs(p[0] - q[0]) < 1e-9 && Math.abs(p[1] - q[1]) < 1e-9;
    out.forEach((s) => { s.orig = s.pts.map((_, i) => i); s.keptOrig = new Set(s.orig); });
    const fixed = (sid, i) => crossingPts.has(sid + ',' + s_orig(sid, i));
    const s_orig = (sid, i) => out[sid].orig[i];
    let changed = true, passes = 0;
    while (changed && passes++ < 30) {
      changed = false;
      // spatial hash of all current segments
      const cs = 1.0; const key = (x, y) => Math.floor(x / cs) * 73856093 ^ Math.floor(y / cs) * 19349663;
      const grid = new Map(); const segs = [];
      out.forEach((s, sid) => { const m = s.pts.length; const nsg = s.closed ? m : m - 1; for (let i = 0; i < nsg; i++) { const a = s.pts[i], b = s.pts[(i + 1) % m]; const id = segs.length; segs.push([sid, i, a, b]); const x0 = Math.min(a[0], b[0]), x1 = Math.max(a[0], b[0]), y0 = Math.min(a[1], b[1]), y1 = Math.max(a[1], b[1]); for (let cx = Math.floor(x0 / cs); cx <= Math.floor(x1 / cs); cx++) for (let cy = Math.floor(y0 / cs); cy <= Math.floor(y1 / cs); cy++) { const k = cx * 73856093 ^ cy * 19349663; let l = grid.get(k); if (!l) { l = []; grid.set(k, l); } l.push(id); } } });
      const rimGrid = new Map();
      rimSegs.forEach(([a, b], id) => { const x0 = Math.min(a[0], b[0]), x1 = Math.max(a[0], b[0]), y0 = Math.min(a[1], b[1]), y1 = Math.max(a[1], b[1]); for (let cx = Math.floor(x0 / cs); cx <= Math.floor(x1 / cs); cx++) for (let cy = Math.floor(y0 / cs); cy <= Math.floor(y1 / cs); cy++) { const k = cx * 73856093 ^ cy * 19349663; let l = rimGrid.get(k); if (!l) { l = []; rimGrid.set(k, l); } l.push(id); } });
      const clear = (sid, i0, i2, a, b) => {   // is chord ab (replacing point between i0 and i2 of strand sid) clear?
        const x0 = Math.min(a[0], b[0]), x1 = Math.max(a[0], b[0]), y0 = Math.min(a[1], b[1]), y1 = Math.max(a[1], b[1]);
        const seen = new Set();
        // other strands' segments next to a crossing that the chord ends at: only a genuine crossing counts there
        // the chord must keep its strand's two arms separating the other strand's two arms at any crossing it ends at
        const armsOk = () => {
          for (const [ii, far] of [[i0, b], [i2, a]]) {
            const mates = crossMates.get(sid + ',' + s_orig(sid, ii)); if (!mates) continue;
            const X = out[sid].pts[ii]; const me = out[sid].pts.length;
            const otherArm = out[sid].pts[ii === i0 ? (i0 - 1 + me) % me : (i2 + 1) % me];
            if (!out[sid].closed && ((ii === i0 && i0 === 0) || (ii === i2 && i2 === me - 1))) continue;   // strand end, no second arm
            for (const [ms, mo] of mates) {
              const idx = out[ms].orig.indexOf(mo); if (idx < 0) continue; const mm = out[ms].pts.length;
              if (!out[ms].closed && (idx === 0 || idx === mm - 1)) continue;
              const m1 = out[ms].pts[(idx - 1 + mm) % mm], m2 = out[ms].pts[(idx + 1) % mm];
              const ang = (p) => Math.atan2(p[1] - X[1], p[0] - X[0]);
              const rays = [[ang(far), 0], [ang(otherArm), 0], [ang(m1), 1], [ang(m2), 1]].sort((p, q) => p[0] - q[0]);
              if (!(rays[0][1] !== rays[1][1] && rays[1][1] !== rays[2][1] && rays[2][1] !== rays[3][1])) return false;
            }
          }
          return true;
        };
        if (!armsOk()) return false;
        // a chord that starts or ends at a crossing point must stay on the right side of that crossing's edge
        {
          const nA = out[sid].gridN && out[sid].gridN.get(s_orig(sid, i0)), nB = out[sid].gridN && out[sid].gridN.get(s_orig(sid, i2));
          if (nA && (b[0] - a[0]) * nA[0] + (b[1] - a[1]) * nA[1] <= 1e-9) return false;
          if (nB && (a[0] - b[0]) * nB[0] + (a[1] - b[1]) * nB[1] >= -1e-9) return false;
        }
        const nearMate = (osid, oi) => { for (const ii of [i0, i2]) { const mates = crossMates.get(sid + ',' + s_orig(sid, ii)); if (!mates) continue; for (const [ms, mo] of mates) { if (ms !== osid) continue; const idx = out[ms].orig.indexOf(mo); if (idx >= 0 && Math.abs(oi - idx) <= 3) return true; } } return false; };
        for (let cx = Math.floor((x0 - margin) / cs); cx <= Math.floor((x1 + margin) / cs); cx++) for (let cy = Math.floor((y0 - margin) / cs); cy <= Math.floor((y1 + margin) / cs); cy++) {
          const k = cx * 73856093 ^ cy * 19349663;
          for (const id of (grid.get(k) || [])) {
            if (seen.has(id)) continue; seen.add(id);
            const [osid, oi, c, d] = segs[id];
            const m = out[osid].pts.length;
            if (osid === sid && (oi === i0 || oi === (i0 + 1) % m)) continue;   // the two segments being replaced
            // segments touching the chord at an endpoint, the strand's own nearby segments, and the other strand's
            // segments right next to a shared crossing: only a genuine crossing counts
            const touches = same(c, a) || same(d, a) || same(c, b) || same(d, b);
            const ownNear = osid === sid && Math.min(Math.abs(oi - i0), out[sid].closed ? m - Math.abs(oi - i0) : 1e9) <= 8;
            if (touches || ownNear || nearMate(osid, oi)) { if (properCross(a, b, c, d)) return false; continue; }
            if (segDist(a, b, c, d) < margin) { if (globalThis.DBGSIMP && globalThis.DBGSIMP.verbose) console.log('blocked chord', sid, i0, i2, 'by', osid, oi, 'dist', segDist(a, b, c, d).toFixed(3)); return false; }
          }
          for (const id of (rimGrid.get(k) || [])) { const [c, d] = rimSegs[id]; if (properCross(a, b, c, d)) return false; const touches = same(c, a) || same(d, a) || same(c, b) || same(d, b); if (!touches && segDist(a, b, c, d) < 0.5 * margin && !(Math.min(Math.hypot(a[0] - c[0], a[1] - c[1]), Math.hypot(a[0] - d[0], a[1] - d[1]), Math.hypot(b[0] - c[0], b[1] - c[1]), Math.hypot(b[0] - d[0], b[1] - d[1])) < 1e-6)) { /* chord hugging the rim: allowed only if it does not cross */ } }
        }
        return true;
      };
      out.forEach((s, sid) => {
        const m = s.pts.length; if (m < 3) return;
        for (let i = s.closed ? 0 : 1; i < (s.closed ? m : m - 1); i++) {
          if (fixed(sid, i)) continue;
          const i0 = (i - 1 + m) % m, i2 = (i + 1) % m; const a = s.pts[i0], b = s.pts[i2];
          if (!clear(sid, i0, i2, a, b)) { if (globalThis.DBGSIMP) globalThis.DBGSIMP.blocked = (globalThis.DBGSIMP.blocked || 0) + 1; continue; }
          if (globalThis.DBGSIMP) globalThis.DBGSIMP.removed = (globalThis.DBGSIMP.removed || 0) + 1;
          s.keptOrig.delete(s.orig[i]); s.pts.splice(i, 1); s.orig.splice(i, 1); changed = true;
          return;   // one removal per strand per pass keeps the hash valid
        }
      });
    }
  }

  // tiles of the level-N patch whose centroid lies within radius of centre (absolute patch coordinates)
  function makeTiles(N, radius, centre) {
    let shapes = base();
    for (let i = 0; i < N; i++) shapes = supertiles(shapes);
    const [ox, oy] = centre, lim = radius + 8;
    const tiles = [];
    (function collect(sh, T, path) {
      const b = bounds(sh), c = tp(T, b);
      if (Math.hypot(c[0] - ox, c[1] - oy) - b[2] > lim) return;
      if (sh.tile) {
        const P0 = PTS.map((p) => tp(T, p));
        let sx = 0, sy = 0; for (const p of P0) { sx += p[0]; sy += p[1]; }
        if (Math.hypot(sx / 14 - ox, sy / 14 - oy) > lim) return;
        let P = P0.map((p) => [p[0] - ox, p[1] - oy]);
        let a = 0; for (let i = 0; i < 14; i++) { const q = P[(i + 1) % 14]; a += P[i][0] * q[1] - q[0] * P[i][1]; }
        const rev = a < 0;
        if (rev) P = P.reverse();
        const parts = path.split('.'), kc = tp(T, KERNEL);
        tiles.push({ P, rev, kc: [kc[0] - ox, kc[1] - oy], sup1: parts.slice(0, N).join('.'), sup2: parts.slice(0, N - 1).join('.') });
        return;
      }
      sh.geoms.forEach(([s, t], k) => collect(s, mul(T, t), path + '.' + k));
    })(shapes.Delta, IDENT, '');
    return tiles;
  }

  function cellsFromTiles(tiles) { return tiles.map((t, k) => ({ P: t.P, tiles: [k] })); }

  // fan each spectre from its kernel point to the chosen vertices (indices into PTS)
  function cellsFan(tiles, spokes) {
    const cells = [];
    tiles.forEach((t, k) => {
      const idx = spokes.map((i) => t.rev ? 13 - i : i).sort((a, b) => a - b);
      for (let j = 0; j < idx.length; j++) {
        const a = idx[j], b = idx[(j + 1) % idx.length];
        const poly = [t.kc], labels = []; let i = a;
        const cv = (q) => t.rev ? 13 - q : q;                       // canonical vertex index
        const ce = (q) => t.rev ? (q === 13 ? 13 : 12 - q) : q;     // canonical index of edge (q, q+1)
        labels.push('s' + cv(a));
        for (;;) { poly.push(t.P[i]); if (i === b) break; labels.push('e' + ce(i)); i = (i + 1) % 14; }
        labels.push('s' + cv(b));
        cells.push({ P: poly, tiles: [k], labels, tileRef: t });
      }
    });
    return cells;
  }

  function cellsFromSupertiles(tiles, level) {
    const groups = new Map(), keyOf = (t) => level === 2 ? t.sup2 : t.sup1;
    tiles.forEach((t, k) => { const g = keyOf(t); if (!groups.has(g)) groups.set(g, []); groups.get(g).push(k); });
    const cells = [];
    for (const ks of groups.values()) {
      const cnt = new Map();
      for (const k of ks) { const P = tiles[k].P; for (let i = 0; i < 14; i++) { const a = vkey(P[i]), b = vkey(P[(i + 1) % 14]); const e = a < b ? a + '|' + b : b + '|' + a; cnt.set(e, (cnt.get(e) || 0) + 1); } }
      const nxt = new Map(), coord = new Map();
      let pinched = false;
      for (const k of ks) {
        const P = tiles[k].P;
        for (let i = 0; i < 14; i++) {
          const a = vkey(P[i]), b = vkey(P[(i + 1) % 14]); const e = a < b ? a + '|' + b : b + '|' + a;
          if (cnt.get(e) === 1) { if (nxt.has(a)) pinched = true; nxt.set(a, b); coord.set(a, P[i]); }
        }
      }
      if (pinched || !nxt.size) continue;
      const start = nxt.keys().next().value; const loop = [start]; let cur = nxt.get(start);
      while (cur !== start && loop.length < 2000 && cur !== undefined) { loop.push(cur); cur = nxt.get(cur); }
      if (loop.length !== nxt.size) continue;
      cells.push({ P: loop.map((v) => coord.get(v)), tiles: ks });
    }
    return cells;
  }

  function degrees(cells) {
    const und = new Set();
    for (const c of cells) { const P = c.P, n = P.length; for (let i = 0; i < n; i++) { const a = vkey(P[i]), b = vkey(P[(i + 1) % n]); und.add(a < b ? a + '|' + b : b + '|' + a); } }
    const deg = new Map();
    for (const e of und) { const [a, b] = e.split('|'); deg.set(a, (deg.get(a) || 0) + 1); deg.set(b, (deg.get(b) || 0) + 1); }
    return deg;
  }

  function straighten(cells) {
    const deg = degrees(cells);
    return cells.map((c) => {
      const keep = c.P.filter((p) => deg.get(vkey(p)) !== 2);
      return Object.assign({}, c, { P: keep, orig: c.P });
    });
  }

  function polylineAt(pts, cum, s) {
    let k = 0; while (k < cum.length - 2 && cum[k + 1] <= s) k++;
    const seg = cum[k + 1] - cum[k]; const f = seg < 1e-12 ? 0 : (s - cum[k]) / seg;
    return [pts[k][0] + (pts[k + 1][0] - pts[k][0]) * f, pts[k][1] + (pts[k + 1][1] - pts[k][1]) * f];
  }
  function projectPolyline(pts, cum, q) {
    let bd = 1e9, bs = 0;
    for (let k = 0; k < pts.length - 1; k++) {
      const a = pts[k], ab = sub(pts[k + 1], a), L2 = dot(ab, ab);
      const t = L2 < 1e-12 ? 0 : Math.max(0, Math.min(1, dot(sub(q, a), ab) / L2));
      const d = nrm(sub(add(a, scl(ab, t)), q));
      if (d < bd) { bd = d; bs = cum[k] + t * (cum[k + 1] - cum[k]); }
    }
    return bs;
  }

  function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }

  // hand-drawn tile designs (from the tile editor), keyed by grid kind and design digits
  const HAND_DESIGNS = {};
  HAND_DESIGNS['fan14:0:0222221'] = HAND_DESIGNS[':0:0222221'] = {"design":"0222221","grid":"fan14","savedAt":"2026-10-07T00:04:47Z","passages":[{"from":"e0","to":"e11","x0":1,"anchors":[{"p":[0.5,0.0],"h1":null,"h2":[0.36650000000000005,0.13349999999999998]},{"p":[0.3703,0.3662],"h1":[0.3648,0.1946],"h2":[0.3784,0.6173]},{"p":[0.5372,1.022],"h1":[0.56,0.6916],"h2":[0.5193,1.2807]},{"p":[0.0721,1.6242],"h1":[0.237,1.5094],"h2":[-0.1093,1.7505]},{"p":[-0.6160254037844386,1.9330127018922192],"h1":[-0.4599321190059791,1.9748377714925287],"h2":null}]},{"from":"e0","to":"e1","x0":-1,"anchors":[{"p":[0.5,0.0],"h1":null,"h2":[0.669,0.169]},{"p":[1.0362,0.114],"h1":[0.8522,0.1837],"h2":[1.2202,0.0442]},{"p":[1.25,-0.4330127018922193],"h1":[1.289841095986324,-0.28432370744202967],"h2":null}]},{"from":"e1","to":"e2","x0":-1,"anchors":[{"p":[1.25,-0.4330127018922193],"h1":null,"h2":[1.3719092532467119,-0.465678187849557]},{"p":[1.9330127018922192,-0.6160254037844386],"h1":[1.811103448645507,-0.5833599178271008],"h2":null}]},{"from":"e2","to":"e3","x0":-1,"anchors":[{"p":[1.9330127018922192,-0.6160254037844386],"h1":null,"h2":[1.9791258164688785,-0.4439289172891011]},{"p":[2.3660254037844384,0.1339745962155614],"h1":[2.1734254037844383,-0.05862540378443862],"h2":null}]},{"from":"e3","to":"e4","x0":-1,"anchors":[{"p":[2.3660254037844384,0.1339745962155614],"h1":null,"h2":[2.226625403784438,0.2733745962155615]},{"p":[2.2863,0.7175],"h1":[2.0858,0.556],"h2":[2.4718,0.8668]},{"p":[2.8660254037844384,0.6339745962155614],"h1":[2.7262254037844382,0.7737745962155615],"h2":null}]},{"from":"e4","to":"e5","x0":-1,"anchors":[{"p":[2.8660254037844384,0.6339745962155614],"h1":null,"h2":[3.0586254037844385,0.8265745962155614]},{"p":[3.6160254037844384,1.0669872981077808],"h1":[3.4439289172891008,1.0208741835311215],"h2":null}]},{"from":"e5","to":"e6","x0":-1,"anchors":[{"p":[3.6160254037844384,1.0669872981077808],"h1":null,"h2":[3.5833599178271007,1.188896551354493]},{"p":[3.433012701892219,1.75],"h1":[3.465678187849557,1.628090746753288],"h2":null}]},{"from":"e6","to":"e7","x0":-1,"anchors":[{"p":[3.433012701892219,1.75],"h1":null,"h2":[3.2609162153968816,1.7038868854233407]},{"p":[2.566987298107781,1.75],"h1":[2.7390837846031184,1.7038868854233407],"h2":null}]},{"from":"e7","to":"e8","x0":-1,"anchors":[{"p":[2.566987298107781,1.75],"h1":null,"h2":[2.5326079346081722,1.6216944686875823]},{"p":[2.1252,1.3551],"h1":[2.3911,1.2979],"h2":[1.8424,1.416]},{"p":[1.8839745962155616,1.9330127018922192],"h1":[1.849570233140791,1.8046138708951287],"h2":null}]},{"from":"e8","to":"e9","x0":-1,"anchors":[{"p":[1.8839745962155616,1.9330127018922192],"h1":null,"h2":[1.7632849568957474,1.9653513932827669]},{"p":[1.1339745962155614,2.3660254037844384],"h1":[1.2726745962155614,2.2273254037844383],"h2":null}]},{"from":"e9","to":"e10","x0":-1,"anchors":[{"p":[1.1339745962155614,2.3660254037844384],"h1":null,"h2":[0.8520745962155614,2.084125403784438]},{"p":[0.1339745962155614,2.3660254037844384],"h1":[0.30567459621556137,2.1943254037844384],"h2":null}]},{"from":"e10","to":"e13","x0":3,"anchors":[{"p":[0.1339745962155614,2.3660254037844384],"h1":null,"h2":[-0.06242540378443867,2.1696254037844382]},{"p":[0.4982,1.7602],"h1":[0.0908,1.9987],"h2":[0.7703,1.601]},{"p":[1.0021,1.0623],"h1":[0.9608,1.3602],"h2":[1.0363,0.8164]},{"p":[0.3703,0.3662],"h1":[0.7351,0.3544],"h2":[0.2007,0.3717]},{"p":[0.0,0.5],"h1":[0.07219999999999999,0.4278],"h2":null}]},{"from":"e11","to":"e12","x0":-1,"anchors":[{"p":[-0.6160254037844386,1.9330127018922192],"h1":null,"h2":[-0.5833599178271008,1.811103448645507]},{"p":[-0.4330127018922193,1.25],"h1":[-0.465678187849557,1.3719092532467119],"h2":null}]},{"from":"e12","to":"e13","x0":-1,"anchors":[{"p":[-0.4330127018922193,1.25],"h1":null,"h2":[-0.3335029313821815,1.276663562647171]},{"p":[0.0842,1.0444],"h1":[-0.0266,1.2001],"h2":[0.1949,0.8886]},{"p":[0.0,0.5],"h1":[0.1156,0.6156],"h2":null}]}]};
  HAND_DESIGNS['fan21:0:01222222222222'] = HAND_DESIGNS[':0:01222222222222'] = {"design":"0.1:01","grid":"fan21","spokes":[0,1],"states":[0,1],"edgeOffset":0.15,"savedAt":"2026-10-07T14:29:00Z","passages":[{"from":"e0","to":"e1","x0":1,"over":[true,true],"x0over":false,"anchors":[{"p":[0.65,0.0],"h1":null,"h2":[0.4716,0.1784]},{"p":[0.6214,0.4993],"h1":[0.4677,0.3289],"h2":[0.7621,0.6552]},{"p":[1.175,-0.3031088913245535],"h1":[1.3952506034606935,0.5188775511884605],"h2":null}]},{"from":"e0","to":"e13","x0":1,"over":[false,false],"x0over":true,"anchors":[{"p":[0.65,0.0],"h1":null,"h2":[0.8447,0.19469999999999998]},{"p":[0.6214,0.4993],"h1":[0.7982,0.3398],"h2":[0.3071,0.783]},{"p":[0.0,0.65],"h1":[0.1402,0.5098],"h2":null}]},{"from":"e1","to":"e2","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[1.175,-0.3031088913245535],"h1":null,"h2":[1.3501888303354381,-0.3500505969358871]},{"p":[2.0629165124598847,-0.5410254037844386],"h1":[1.8877276821244466,-0.49408369817310505],"h2":null}]},{"from":"e2","to":"e3","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[2.0629165124598847,-0.5410254037844386],"h1":null,"h2":[2.1291510722419353,-0.2938346614608678]},{"p":[2.3660254037844384,-0.01602540378443862],"h1":[2.1497254037844384,-0.2323254037844386],"h2":null}]},{"from":"e3","to":"e4","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[2.3660254037844384,-0.01602540378443862],"h1":null,"h2":[2.1497254037844384,0.20027459621556137]},{"p":[2.2728,0.7125],"h1":[2.1089,0.5376],"h2":[2.4631,0.9155]},{"p":[3.0160254037844383,0.6339745962155614],"h1":[2.8590254037844383,0.7909745962155614],"h2":null}]},{"from":"e4","to":"e5","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[3.0160254037844383,0.6339745962155614],"h1":null,"h2":[3.1775254037844385,0.7954745962155615]},{"p":[3.541025403784438,0.9370834875401148],"h1":[3.345521419999341,0.8846983529678307],"h2":null}]},{"from":"e5","to":"e6","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[3.541025403784438,0.9370834875401148],"h1":null,"h2":[3.4940836981731045,1.112272317875553]},{"p":[3.3031088913245537,1.825],"h1":[3.3500505969358874,1.6498111696645619],"h2":null}]},{"from":"e6","to":"e7","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[3.3031088913245537,1.825],"h1":null,"h2":[3.1086129202251467,1.7728849616128068]},{"p":[2.6968911086754463,1.825],"h1":[2.875900385659876,1.7770346087943427],"h2":null}]},{"from":"e7","to":"e8","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[2.6968911086754463,1.825],"h1":null,"h2":[2.63108334442707,1.5794020802925437]},{"p":[2.1168,1.3916],"h1":[2.3854,1.3258],"h2":[1.7853,1.4728]},{"p":[1.8089745962155614,2.0629165124598847],"h1":[1.7595654236279086,1.878518970002824],"h2":null}]},{"from":"e8","to":"e9","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[1.8089745962155614,2.0629165124598847],"h1":null,"h2":[1.6059730176459646,2.1173106214998514]},{"p":[1.2839745962155615,2.3660254037844384],"h1":[1.4041745962155616,2.2458254037844383],"h2":null}]},{"from":"e9","to":"e10","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[1.2839745962155615,2.3660254037844384],"h1":null,"h2":[1.0841745962155613,2.166225403784438]},{"p":[-0.01602540378443862,2.3660254037844384],"h1":[0.36797459621556144,1.9820254037844385],"h2":null}]},{"from":"e10","to":"e11","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[-0.01602540378443862,2.3660254037844384],"h1":null,"h2":[-0.23232540378443858,2.1497254037844384]},{"p":[-0.5410254037844386,2.0629165124598847],"h1":[-0.2938346614608678,2.1291510722419353],"h2":null}]},{"from":"e11","to":"e12","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[-0.5410254037844386,2.0629165124598847],"h1":null,"h2":[-0.4940836981731051,1.8877276821244466]},{"p":[-0.30310889132455354,1.175],"h1":[-0.35005059693588714,1.3501888303354381],"h2":null}]},{"from":"e12","to":"e13","x0":-1,"over":[false,true],"x0over":false,"anchors":[{"p":[-0.30310889132455354,1.175],"h1":null,"h2":[-0.15249717207598837,1.215356288543316]},{"p":[0.1038,1.065],"h1":[0.0251,1.1976],"h2":[0.1667,0.9588]},{"p":[0.0,0.65],"h1":[0.1282,0.7782],"h2":null}]}]};
  const designKey = (d) => (d.edges || 0) + ':' + Object.keys(d.spokes || {}).sort((a, b) => +a.slice(1) - +b.slice(1)).map((k) => d.spokes[k] || 0).join('');
  function build(cells, mode, inset, relaxIt, margin, opts) {
    opts = opts || {};
    let tilesOf = opts.tiles || null;
    if (!tilesOf && cells.length && cells[0].tileRef) { tilesOf = []; for (const c of cells) tilesOf[c.tiles[0]] = c.tileRef; }
    var handApplied = false;
    const u = inset / 0.22;
    const FAIR = opts.fair === false ? null : Object.assign({ h: 0.07 * u, anchor: 0.07 * u, dMin: 0.33 * u, gap: 0.3 * u, step: 0.025 * u, iters: 80, every: 10, lambda: 1e4, alpha: 0.3, maxSeg: 0.3 * u, slide: false, slideSpokes: true, slideGain: 0.1, slideRange: 0.12 * u, actPasses: 3, cone: 0.65, rotate: true, rotGain: 0.3, lever: 6, initTurn: true, initTurnMax: 1.2, clamp: 16, taper: 4, dObs: 0.2 * u, tension: 0.01, wContact: 2, selfGap: 0.42 * u, rVertex: 0, tol: 0.004 * u, fit: true, fitSpan: 0.4 * u, fitRounds: 6 }, typeof opts.fair === 'object' ? opts.fair : {});
    const deg = degrees(cells);
    const runsByKey = new Map();
    cells.forEach((c, ci) => {
      const P = c.P, n = P.length;
      let real = mode === 'edge' ? P.map((_, i) => i) : P.map((_, i) => i).filter((i) => deg.get(vkey(P[i])) !== 2);
      if (real.length < 2) real = P.map((_, i) => i);
      c.real = real; c.runs = [];
      for (let r = 0; r < real.length; r++) {
        const a = real[r], b = real[(r + 1) % real.length];
        const idx = [a]; while (idx[idx.length - 1] !== b) idx.push((idx[idx.length - 1] + 1) % n);
        const pts = idx.map((k) => P[k]);
        const cum = [0]; for (let k = 1; k < pts.length; k++) cum.push(cum[k - 1] + nrm(sub(pts[k], pts[k - 1])));
        const L = cum[cum.length - 1];
        const key = vkey(polylineAt(pts, cum, L / 2));
        c.runs.push({ key, idx, pts, cum, L });
        if (!runsByKey.has(key)) runsByKey.set(key, []);
        runsByKey.get(key).push([ci, r]);
      }
    });
    const owner = new Map(), gidOf = new Map();
    let ng = 0;
    for (const [k, lst] of runsByKey) { owner.set(k, lst[0]); gidOf.set(k, ng++); }
    const sval = new Float64Array(ng);
    for (const [k, lst] of runsByKey) {
      const g = gidOf.get(k); sval[g] = cells[lst[0][0]].runs[lst[0][1]].L / 2;
      lst.forEach(([ci, r], i) => { const run = cells[ci].runs[r]; run.gid = g; run.own = i === 0; });
    }
    cells.forEach((c) => { c.ins = c.P.map((_, i) => insetPoint(c.P, i)); });

    // single-thread mode: crossings only on a uniform spanning tree of the cells, breaks everywhere else
    const isT = new Uint8Array(ng);     // state per grid point: 0 crossing, 1 cell-hugging break, 2 vertex-hugging break
    let treeInfo = null;
    if (opts.design) {
      // one design for every tile: interior (spoke) points by label, edge points all alike
      const d = opts.design;
      for (const [k, lst] of runsByKey) {
        const [ci, r] = lst[0], lab = cells[ci].labels ? cells[ci].labels[r] : null;
        let st = 0;
        if (lab && lab[0] === 's') st = d.spokes[lab] || 0;
        else if (lab && lab[0] === 'e') st = d.edges || 0;
        if (lst.length !== 2 && st === 2) st = 1;
        isT[gidOf.get(k)] = st;
      }
    }
    if (opts.thread) {
      for (const [k, lst] of runsByKey) if (lst.length !== 2) isT[gidOf.get(k)] = 1;
      const adjC = cells.map(() => []);
      for (const [k, lst] of runsByKey) if (lst.length === 2) {
        const g = gidOf.get(k), a = lst[0][0], b = lst[1][0];
        if (a !== b) { adjC[a].push(b, g); adjC[b].push(a, g); }
      }
      let root = 0, bd = 1e18;
      cells.forEach((c, ci) => { const p = c.P[0], d = p[0] * p[0] + p[1] * p[1]; if (d < bd) { bd = d; root = ci; } });
      const comp = new Uint8Array(cells.length); const stack = [root]; comp[root] = 1;
      while (stack.length) { const u = stack.pop(); const nb = adjC[u]; for (let q = 0; q < nb.length; q += 2) if (!comp[nb[q]]) { comp[nb[q]] = 1; stack.push(nb[q]); } }
      const treeG = new Uint8Array(ng);
      let treeEdges = 0;
      if (opts.tree === 'spiral') {
        // spiral: order cells along an Archimedean spiral and take a minimum spanning tree
        // weighted by distance along it, so the tree runs round the turns with few links between them
        const cen = cells.map((c) => { let x = 0, y = 0; for (const p of c.P) { x += p[0]; y += p[1]; } return [x / c.P.length, y / c.P.length]; });
        let area = 0;
        for (const c of cells) { let a = 0; const P = c.P; for (let i = 0; i < P.length; i++) { const q = P[(i + 1) % P.length]; a += P[i][0] * q[1] - q[0] * P[i][1]; } area += Math.abs(a) / 2; }
        const pitch = 1.15 * Math.sqrt(area / cells.length);
        const theta = cen.map(([x, y]) => {
          const r = Math.hypot(x, y); let t = Math.atan2(y, x); if (t < 0) t += 2 * Math.PI;
          const k = Math.round((2 * Math.PI * r / pitch - t) / (2 * Math.PI));
          return t + 2 * Math.PI * k;
        });
        const edges = [];
        for (let a = 0; a < cells.length; a++) { const nb = adjC[a]; for (let q = 0; q < nb.length; q += 2) if (nb[q] > a) edges.push([Math.abs(theta[a] - theta[nb[q]]) * (1 + 1e-9 * nb[q + 1]), a, nb[q], nb[q + 1]]); }
        edges.sort((x, y) => x[0] - y[0]);
        const uf = cells.map((_, i) => i);
        const find = (x) => { while (uf[x] !== x) { uf[x] = uf[uf[x]]; x = uf[x]; } return x; };
        for (const [, a, b, g] of edges) { if (!comp[a]) continue; const ra = find(a), rb = find(b); if (ra !== rb) { uf[ra] = rb; treeG[g] = 1; treeEdges++; } }
      } else {
        const rnd = mulberry32(opts.seed || 7);
        const inTree = new Uint8Array(cells.length), nxt = new Int32Array(cells.length), nxtG = new Int32Array(cells.length);
        inTree[root] = 1;
        const order = cells.map((_, i) => i);
        for (let i = order.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); const t = order[i]; order[i] = order[j]; order[j] = t; }
        for (const st of order) {
          if (!comp[st]) continue;
          let u = st;
          while (!inTree[u]) { const nb = adjC[u], q = 2 * Math.floor(rnd() * nb.length / 2); nxt[u] = nb[q]; nxtG[u] = nb[q + 1]; u = nb[q]; }
          u = st;
          while (!inTree[u]) { inTree[u] = 1; treeG[nxtG[u]] = 1; treeEdges++; u = nxt[u]; }
        }
      }
      for (const [k, lst] of runsByKey) if (lst.length === 2) { const g = gidOf.get(k); isT[g] = treeG[g] ? 0 : 1; }
      treeInfo = { treeEdges, cells: cells.length, outside: cells.length - comp.reduce((a, b) => a + b, 0) };
    }

    function runState(ci, r, which) {
      const run = cells[ci].runs[r];
      let s = run.own ? sval[run.gid] : run.L - sval[run.gid];
      const st = isT[run.gid];
      if (st === 2) {
        // vertex-hugging break: the two strands do not meet at the grid point. The strand arriving here (end) keeps to
        // the run's start vertex and the strand leaving (start) keeps to its end vertex, so each gets its own waypoint
        // close to the vertex it hugs; the other cell sees the run reversed, so its points match.
        const hug = Math.min(opts.hug || inset, run.L / 2 - 0.05);
        s = which === 'end' ? hug : run.L - hug;
      }
      let g = polylineAt(run.pts, run.cum, s);
      if (st === 1) {
        let k = 0; while (k < run.cum.length - 2 && run.cum[k + 1] <= s) k++;
        const along = unit(sub(run.pts[k + 1], run.pts[k])), d = Math.min(opts.eps || 0.28, 0.3 * run.L);
        g = add(g, scl(rot90(along), d));
      }
      const before = [], after = [];
      for (let q = 1; q < run.idx.length - 1; q++) {
        if (run.cum[q] < s - 1e-6) before.push(run.idx[q]);
        else if (run.cum[q] > s + 1e-6) after.push(run.idx[q]);
      }
      return [g, before, after];
    }
    function insetPoint(P, i) {
      const n = P.length, a0 = P[(i - 1 + n) % n], v = P[i], b0 = P[(i + 1) % n];
      const e1 = unit(sub(v, a0)), e2 = unit(sub(b0, v));
      if (e1[0] * e2[1] - e1[1] * e2[0] > 1e-9) return null;
      const n1 = rot90(e1), n2 = rot90(e2), s = add(n1, n2);
      const bis = nrm(s) > 1e-9 ? unit(s) : n1;
      return add(v, scl(bis, inset));
    }
    // arc-and-tangent routing round a single cell vertex: straight if the chord already clears the vertex's circle,
    // otherwise tangent in, circular arc (clockwise for a ccw cell), tangent out
    function wrapOne(gp, gn, V) {
      const rho = inset;
      const d = sub(gn, gp), L = nrm(d);
      if (L < 1e-9) return [gp, gn];
      const side = cross3(gp, gn, V);   // > 0: V left of gp->gn
      const t = Math.max(0, Math.min(1, dot(sub(V, gp), d) / (L * L)));   // closest point of the segment to V
      const dseg = nrm(sub(V, add(gp, scl(d, t))));
      if (side <= 0 && dseg >= rho * 0.999) return [gp, gn];   // V to the right and the segment clears it
      if (Math.abs(side) / L < 0.02 && t > 0.05 && t < 0.95) {   // straight vertex: a gentle bulge inward is enough
        const n = rot90(unit(d)); return [gp, add(V, scl(n, 0.6 * rho)), gn];
      }
      const tangent = (Q, arriving) => {
        const v = sub(Q, V), dq = nrm(v), phi = Math.atan2(v[1], v[0]);
        if (dq <= rho * 1.0001) return phi;
        const beta = Math.acos(rho / dq);
        let best = null;
        for (const a of [phi + beta, phi - beta]) {
          const T = [V[0] + rho * Math.cos(a), V[1] + rho * Math.sin(a)], tcw = [Math.sin(a), -Math.cos(a)];
          const ok = arriving ? dot(sub(T, Q), tcw) > 0 : dot(sub(Q, T), tcw) > 0;
          if (ok) best = a;
        }
        return best === null ? phi : best;
      };
      const a1 = tangent(gp, true), a2 = tangent(gn, false);
      let sweep = ((a1 - a2) % (2 * Math.PI) + 2 * Math.PI) % (2 * Math.PI);   // clockwise from a1 down to a2
      const ns = Math.max(2, Math.ceil(sweep / (20 * Math.PI / 180)) + 1);
      const out = [gp];
      for (let q = 0; q < ns; q++) { const a = a1 - sweep * q / (ns - 1); out.push([V[0] + rho * Math.cos(a), V[1] + rho * Math.sin(a)]); }
      out.push(gn);
      return out;
    }
    function chain(ci, r, arcs) {
      const c = cells[ci], P = c.P, m = c.runs.length;
      const [gp, , after] = runState(ci, (r - 1 + m) % m, 'start');
      const [gn, before] = runState(ci, r, 'end');
      if (arcs && after.length === 0 && before.length === 0) return wrapOne(gp, gn, P[c.real[r]]);
      const pts = [[gp, null]];
      for (const vi of after.concat([c.real[r]], before)) { const q = c.ins[vi]; if (q) pts.push([q, P[vi]]); }
      pts.push([gn, null]);
      const st = [];
      for (const p of pts) {
        while (st.length >= 2 && cross3(st[st.length - 2][0], st[st.length - 1][0], p[0]) >= -1e-9) st.pop();
        st.push(p);
      }
      if (!arcs) return st.map((p) => p[0]);
      const out = [st[0][0]];
      for (let k = 1; k < st.length - 1; k++) {
        const V = st[k][1], A = out[out.length - 1], B = st[k + 1][0], Vp = st[k][0];
        const din = unit(sub(Vp, A)), dout = unit(sub(B, Vp));
        const ra = rot90(din), rb = rot90(dout);
        const a0 = Math.atan2(ra[1], ra[0]), a1 = Math.atan2(rb[1], rb[0]);
        let da = ((a1 - a0 + Math.PI) % (2 * Math.PI) + 2 * Math.PI) % (2 * Math.PI) - Math.PI;
        if (da > 0) { out.push(Vp); continue; }
        const ns = Math.max(2, Math.floor(Math.abs(da) / (28 * Math.PI / 180)) + 1);
        for (let q = 0; q < ns; q++) { const ang = a0 + da * q / (ns - 1); out.push([V[0] + inset * Math.cos(ang), V[1] + inset * Math.sin(ang)]); }
      }
      out.push(st[st.length - 1][0]);
      let changed = true;
      while (changed && out.length > 2) {
        changed = false;
        for (let k = 1; k < out.length - 1; k++) {
          const u = sub(out[k], out[k - 1]), v = sub(out[k + 1], out[k]), nu = nrm(u), nv = nrm(v);
          if (nu < 0.05 || nv < 0.05 || dot(u, v) < -0.2 * nu * nv) { out.splice(k, 1); changed = true; break; }
        }
      }
      return out;
    }

    // relax grid points along their shared boundary
    const fullKeys = []; for (const [k, lst] of runsByKey) if (lst.length === 2) fullKeys.push(k);
    for (let it = 0; it < relaxIt; it++) {
      const ch = cells.map((c, ci) => c.runs.map((_, r) => chain(ci, r, false)));
      const upd = [];
      for (const k of fullKeys) {
        let sx = 0, sy = 0;
        for (const [ci, r] of runsByKey.get(k)) {
          const m = cells[ci].runs.length, e = ch[ci][r], s = ch[ci][(r + 1) % m];
          sx += e[e.length - 2][0] + s[1][0]; sy += e[e.length - 2][1] + s[1][1];
        }
        const target = [sx / 4, sy / 4];
        const [ci, r] = owner.get(k), run = cells[ci].runs[r];
        const sp = projectPolyline(run.pts, run.cum, target);
        const lo = Math.min(margin, run.L / 2), hi = run.L - lo, g = run.gid;
        upd.push([g, Math.min(hi, Math.max(lo, sval[g] + 0.5 * (sp - sval[g])))]);
      }
      for (const [g, v] of upd) sval[g] = v;
    }

    const SID = (ci, r) => ci * 128 + r;
    const segPts = new Map();
    cells.forEach((c, ci) => c.runs.forEach((_, r) => segPts.set(SID(ci, r), chain(ci, r, true))));

    const link = new Map(), nodes = [];
    for (const [k, lst] of runsByKey) {
      const st = isT[gidOf.get(k)];
      if (st === 1 || (st && lst.length !== 2)) {
        // cell-hugging break: each cell's two strand ends at this grid point join inside that cell
        for (const [ci, r] of lst) {
          const m = cells[ci].runs.length, e = SID(ci, r), s = SID(ci, (r + 1) % m);
          link.set(e * 2 + 1, s * 2); link.set(s * 2, e * 2 + 1);
        }
        continue;
      }
      if (lst.length !== 2) continue;
      const [[c1, r1], [c2, r2]] = lst;
      const m1 = cells[c1].runs.length, m2 = cells[c2].runs.length;
      const e1 = SID(c1, r1), e2 = SID(c2, r2), s1 = SID(c1, (r1 + 1) % m1), s2 = SID(c2, (r2 + 1) % m2);
      if (st === 2) {
        // vertex-hugging break: strands cross the boundary and turn round the two vertices
        link.set(e1 * 2 + 1, s2 * 2); link.set(s2 * 2, e1 * 2 + 1);
        link.set(s1 * 2, e2 * 2 + 1); link.set(e2 * 2 + 1, s1 * 2);
        continue;
      }
      link.set(e1 * 2 + 1, e2 * 2 + 1); link.set(e2 * 2 + 1, e1 * 2 + 1);
      link.set(s1 * 2, s2 * 2); link.set(s2 * 2, s1 * 2);
      nodes.push({ key: k, over: [e1, e2], under: [s1, s2] });
    }

    const used = new Set(), strands = [];
    const allSegs = Array.from(segPts.keys());
    function walk(seg, d) {
      const seq = [];
      for (;;) {
        if (used.has(seg * 2 + d) || used.has(seg * 2 + 1 - d)) return seq;
        used.add(seg * 2 + d); seq.push([seg, d]);
        const nx = link.get(seg * 2 + (d === 1 ? 1 : 0));
        if (nx === undefined) return seq;
        seg = nx >> 1; d = (nx & 1) === 1 ? 0 : 1;
      }
    }
    for (const seg of allSegs) for (const end of [0, 1]) {
      if (!link.has(seg * 2 + end) && !used.has(seg * 2) && !used.has(seg * 2 + 1)) strands.push([walk(seg, end === 0 ? 1 : 0), false]);
    }
    for (const seg of allSegs) if (!used.has(seg * 2) && !used.has(seg * 2 + 1)) strands.push([walk(seg, 1), true]);

    const out = [], segLoc = new Map(), junc = new Map();
    const jkey = (a, b) => a < b ? a + '|' + b : b + '|' + a;
    // tangent of a strand as it passes a crossing grid point, from the combinatorics: the piece [seg, d] arrives at the
    // grid point of run R via its 'e' end (came round R's start vertex, continues to the far side towards R's end: u - n)
    // or its 's' end (-u - n); u is R's direction and n the inward normal of the piece's cell.
    const passTangent = (seg, d, departing) => {
      const ci = seg >> 7, r = seg & 127, c = cells[ci], m = c.runs.length;
      const atE = departing ? d === 0 : d === 1;                      // arriving via end 1 ('e' of run r) / departing from end 1
      const run = c.runs[atE ? r : (r - 1 + m) % m];
      if (isT[run.gid] !== 0) return null;                           // only crossings get the 45-degree treatment
      const u = unit(sub(run.pts[run.pts.length - 1], run.pts[0])), n = rot90(u);
      // [unit tangent, normal of the edge pointing to the side the strand continues on]
      if (!departing) return [unit(atE ? sub(u, n) : sub(scl(u, -1), n)), scl(n, -1)];
      return [unit(atE ? add(scl(u, -1), n) : add(u, n)), n];
    };
    strands.forEach(([seq, closed], sid) => {
      let pts = []; const pieces = []; const gridAt = new Map(), gridN = new Map();   // point index -> fixed unit tangent / forward-side normal at a crossing
      { const [seg0, d0] = seq[0]; const t0 = passTangent(seg0, d0, true); if (t0) { gridAt.set(0, t0[0]); gridN.set(0, t0[1]); } }
      for (const [seg, d] of seq) {
        let sp = segPts.get(seg); if (d === 0) sp = sp.slice().reverse();
        const start = Math.max(pts.length - 1, 0);
        if (pts.length) sp = sp.slice(1); else { pts.push(sp[0]); sp = sp.slice(1); }
        for (const p of sp) {
          pts.push(p);
        }
        pieces.push([seg, start, pts.length - 1 - start, d]);
        { const t = passTangent(seg, d, false); if (t) { gridAt.set(pts.length - 1, t[0]); gridN.set(pts.length - 1, t[1]); } }
      }
      if (closed && pts.length > 2 && nrm(sub(pts[0], pts[pts.length - 1])) < 1e-6) { pts = pts.slice(0, -1); if (gridAt.has(pts.length)) { gridAt.delete(pts.length); gridN.delete(pts.length); } }
      out.push({ pts, closed, pieces, gridAt, gridN });
    });
    // crossing points: never moved or removed
    const crossingPts = new Set();   // 'sid,idx'
    const juncIndex = (sid, q) => { const pc = out[sid].pieces; return q < pc.length - 1 ? pc[q][1] + pc[q][2] : 0; };
    out.forEach((s, sid) => { s.pieces.forEach((pc, q) => { if (q < s.pieces.length - 1 || s.closed) junc.set(jkey(pc[0], s.pieces[(q + 1) % s.pieces.length][0]), [sid, juncIndex(sid, q)]); }); });
    for (const nd of nodes) { for (const pair of [nd.over, nd.under]) { const j = junc.get(jkey(pair[0], pair[1])); if (j) crossingPts.add(j[0] + ',' + j[1]); } }
    const crossMates = new Map();
    for (const nd of nodes) { const jo = junc.get(jkey(nd.over[0], nd.over[1])), ju = junc.get(jkey(nd.under[0], nd.under[1])); if (jo && ju) { const ko = jo[0] + ',' + jo[1], ku = ju[0] + ',' + ju[1]; if (!crossMates.has(ko)) crossMates.set(ko, []); if (!crossMates.has(ku)) crossMates.set(ku, []); crossMates.get(ko).push(ju); crossMates.get(ku).push(jo); } }
    // tile edges (never spokes) as obstacles, cut open around every crossing point
    // obstaclesGap: edges cut open round every crossing (for the simplifier); obstacles: edges split exactly at the
    // crossing point and keyed by run (for fairing, which keeps strands off their own crossing's edge by a 45-degree cone)
    const obstaclesGap = [], obstacles = [], slideOf = new Map();   // run key -> { A, B, u, lo, hi, o1, o2 }
    {
      const gap = FAIR ? FAIR.gap : 0.3 * inset / 0.22;
      for (const [k, lst] of runsByKey) {
        const [ci, r] = lst[0], run = cells[ci].runs[r], lab = cells[ci].labels ? cells[ci].labels[r] : null;
        if (lab && lab[0] === 's') continue;
        const s = isT[run.gid] === 0 ? sval[run.gid] : -1;
        for (let q = 0; q + 1 < run.pts.length; q++) {
          const a = run.cum[q], b = run.cum[q + 1];
          if (s < 0 || b <= s - gap || a >= s + gap) { obstaclesGap.push([run.pts[q], run.pts[q + 1]]); obstacles.push([run.pts[q], run.pts[q + 1]]); continue; }
          const A = run.pts[q], B = run.pts[q + 1], full = [A, B], u = unit(sub(B, A)), Ls = b - a, Xp = polylineAt(run.pts, run.cum, s);
          if (a < s - gap) obstaclesGap.push([A, polylineAt(run.pts, run.cum, s - gap)]);
          if (b > s + gap) obstaclesGap.push([polylineAt(run.pts, run.cum, s + gap), B]);
          const o1 = obstacles.length; obstacles.push([A, Xp, full, k]);
          const o2 = obstacles.length; obstacles.push([Xp, B, full, k]);
          const m = Math.max(Math.min(margin, Ls / 2), Ls / 2 - (FAIR ? FAIR.slideRange : 0));
          slideOf.set(k, { A, B, u, lo: m, hi: Ls - m, o1, o2 });
        }
      }
    }
    // tile vertices as round obstacles, so strands turn corners with a generous radius
    if (FAIR && FAIR.rVertex > 0) {
      const seen = new Set();
      for (const [k, lst] of runsByKey) {
        const [ci, r] = lst[0], run = cells[ci].runs[r], lab = cells[ci].labels ? cells[ci].labels[r] : null;
        if (lab && lab[0] === 's') continue;
        for (const p of [run.pts[0], run.pts[run.pts.length - 1]]) { const vk = vkey(p); if (seen.has(vk)) continue; seen.add(vk); obstacles.push([p, p, null, null, FAIR.rVertex]); }
      }
    }
    // spokes are not drawn, but a crossing on a spoke may slide along it too
    if (FAIR) for (const [k, lst] of runsByKey) {
      const [ci, r] = lst[0], run = cells[ci].runs[r], lab = cells[ci].labels ? cells[ci].labels[r] : null;
      if (!(lab && lab[0] === 's') || isT[run.gid] !== 0 || lst.length !== 2) continue;
      const s = sval[run.gid]; let q = 0; while (q + 2 < run.pts.length && run.cum[q + 1] < s) q++;
      const A = run.pts[q], B = run.pts[q + 1], u = unit(sub(B, A)), Ls = run.cum[q + 1] - run.cum[q];
      const m = Math.max(Math.min(margin, Ls / 2), Ls / 2 - FAIR.slideRange);
      slideOf.set(k, { A, B, u, lo: m, hi: Ls - m, o1: -1, o2: -1, rot: true, theta: 0 });
    }
    // hand-drawn design: every tile passage (rim port to rim port) is a stored Bezier chain in the canonical tile frame,
    // mapped onto the tile by its own isometry; the combinatorics (strands, crossings, over/under) stay the engine's
    const HAND = opts.hand || (opts.design && opts.hand !== false && HAND_DESIGNS[(opts.fanKind || '') + ':' + designKey(opts.design)]) || null;
    if (HAND) {
      const byKey = new Map(); HAND.passages.forEach((ps) => { byKey.set(ps.from + '>' + ps.to, [ps, 1]); byKey.set(ps.to + '>' + ps.from, [ps, 0]); });
      const tileT = new Map();   // tile index -> affine map PTS -> tile
      const transformOf = (k) => {
        if (tileT.has(k)) return tileT.get(k);
        const t = tilesOf ? tilesOf[k] : null; let T = IDENT;
        if (t) {
          const Q = (i) => t.P[t.rev ? 13 - i : i];
          const q0 = Q(0), q1 = Q(1), q7 = Q(7), p0 = PTS[0], p1 = PTS[1], p7 = PTS[7];
          const u = [p1[0] - p0[0], p1[1] - p0[1]], v = [p7[0] - p0[0], p7[1] - p0[1]], U = [q1[0] - q0[0], q1[1] - q0[1]], V = [q7[0] - q0[0], q7[1] - q0[1]];
          const det = u[0] * v[1] - u[1] * v[0];
          const a = (U[0] * v[1] - V[0] * u[1]) / det, b = (V[0] * u[0] - U[0] * v[0]) / det, d = (U[1] * v[1] - V[1] * u[1]) / det, e = (V[1] * u[0] - U[1] * v[0]) / det;
          T = [a, b, q0[0] - a * p0[0] - b * p0[1], d, e, q0[1] - d * p0[0] - e * p0[1]];
        }
        tileT.set(k, T); return T;
      };
      const labelOf = (ci, r) => cells[ci].labels ? cells[ci].labels[r] : null;
      out.forEach((s, sid) => {
        const pts = [], bez = [], newPieces = [];
        const groups = [];   // consecutive pieces in one tile
        for (const pc of s.pieces) { const tk = cells[pc[0] >> 7].tiles ? cells[pc[0] >> 7].tiles[0] : -1; if (groups.length && groups[groups.length - 1].tile === tk) groups[groups.length - 1].pcs.push(pc); else groups.push({ tile: tk, pcs: [pc] }); }
        if (s.closed && groups.length > 1 && groups[0].tile === groups[groups.length - 1].tile) { const last = groups.pop(); groups[0].pcs = last.pcs.concat(groups[0].pcs); }
        let ok = true;
        groups.forEach((gr, gi) => {
          const first = gr.pcs[0], last = gr.pcs[gr.pcs.length - 1];
          const ci1 = first[0] >> 7, r1 = first[0] & 127, m1 = cells[ci1].runs.length, ci2 = last[0] >> 7, r2 = last[0] & 127, m2 = cells[ci2].runs.length;
          const from = first[3] === 1 ? labelOf(ci1, (r1 - 1 + m1) % m1) : labelOf(ci1, r1), to = last[3] === 1 ? labelOf(ci2, r2) : labelOf(ci2, (r2 - 1 + m2) % m2);
          const hit = byKey.get(from + '>' + to); if (!hit) { ok = false; return; }
          const [ps, fwd] = hit, T = transformOf(gr.tile); gr.from = from; gr.to = to; gr.fwd = fwd; gr.base = pts.length ? pts.length - 1 : 0;
          const A = fwd ? ps.anchors : ps.anchors.slice().reverse().map((a) => ({ p: a.p, h1: a.h2, h2: a.h1 }));
          if (opts.handDebug) { const q0 = tp(T, A[0].p), q1 = tp(T, A[A.length - 1].p), e0 = s.pts[first[1]], e1 = s.pts[(last[1] + last[2]) % s.pts.length]; const d0 = Math.hypot(q0[0] - e0[0], q0[1] - e0[1]), d1 = Math.hypot(q1[0] - e1[0], q1[1] - e1[1]); if (d0 > 1e-3 || d1 > 1e-3) console.log('hand mismatch strand', sid, 'tile', gr.tile, from, to, 'fwd', fwd, 'd', d0.toFixed(3), d1.toFixed(3)); }
          const x0 = ps.x0 >= 0 ? (fwd ? ps.x0 : A.length - 1 - ps.x0) : -1;
          const base = pts.length ? pts.length - 1 : 0;
          const mapP = (p) => tp(T, p);
          A.forEach((a, i) => { if (i === 0) { if (!pts.length) pts.push(mapP(a.p)); } else { bez.push([mapP(A[i - 1].h2), mapP(a.h1)]); pts.push(mapP(a.p)); } });
          // piece ranges inside the group: the crossing junction (if any) sits at the x0 anchor, the rest spread evenly
          const nj = gr.pcs.length - 1, endIdx = base + A.length - 1;
          let xj = -1; for (let j = 0; j < nj; j++) { const pc = gr.pcs[j]; const ci = pc[0] >> 7, r = pc[0] & 127; const run = cells[ci].runs[pc[3] === 1 ? r : (r - 1 + cells[ci].runs.length) % cells[ci].runs.length]; if (isT[run.gid] === 0) xj = j; }
          const cuts = [base];
          for (let j = 0; j < nj; j++) {
            let idx;
            if (xj >= 0 && x0 >= 0) { if (j === xj) idx = base + x0; else if (j < xj) idx = base + Math.round(x0 * (j + 1) / (xj + 1)); else idx = base + x0 + Math.round((A.length - 1 - x0) * (j - xj) / (nj - xj)); }
            else idx = base + Math.round((A.length - 1) * (j + 1) / (nj + 1));
            cuts.push(idx);
          }
          cuts.push(endIdx);
          gr.pcs.forEach((pc, j) => newPieces.push([pc[0], cuts[j], Math.max(0, cuts[j + 1] - cuts[j]), pc[3]]));
        });
        if (!ok) return;
        if (s.closed && pts.length > 1) pts.pop();
        s.pts = pts; s.bez = bez; s.pieces = newPieces; s.hand = true; s.handGroups = groups.map((gr) => [gr.tile, gr.from, gr.to, gr.fwd, gr.base]);
      });
      const allHand = out.every((s) => s.hand);
      if (allHand) {
        junc.clear(); segLoc.clear();
        out.forEach((s, sid) => {
          for (const [seg, a, n, d] of s.pieces) segLoc.set(seg, [sid, a, n, d]);
          s.pieces.forEach((pc, q) => { if (q < s.pieces.length - 1 || s.closed) junc.set(jkey(pc[0], s.pieces[(q + 1) % s.pieces.length][0]), [sid, q < s.pieces.length - 1 ? pc[1] + pc[2] : 0]); });
        });
      } else out.forEach((s) => { delete s.hand; });
      var handApplied = allHand;
    }
    if (!handApplied && opts.simplify !== false) simplifyStrands(out, crossingPts, crossMates, obstaclesGap, { margin: (opts.simplifyMargin || 0.6) * inset });
    else if (!handApplied) out.forEach((s) => { s.orig = s.pts.map((_, i) => i); s.keptOrig = new Set(s.orig); });
    // rebuild index maps after simplification (points carry their original index in s.orig)
    if (!handApplied) { junc.clear();
    out.forEach((s, sid) => {
      const newIndex = (origIdx) => { let lo = 0, hi = s.orig.length - 1; while (lo < hi) { const mid = (lo + hi) >> 1; if (s.orig[mid] < origIdx) lo = mid + 1; else hi = mid; } return lo; };   // first kept point with orig >= origIdx
      s.pieces = s.pieces.map(([seg, a, n, d]) => { const a2 = newIndex(a), b2 = newIndex(a + n); return [seg, a2, Math.max(0, b2 - a2), d]; });
      for (const [seg, a, n, d] of s.pieces) segLoc.set(seg, [sid, a, n, d]);
      s.pieces.forEach((pc, q) => { if (q < s.pieces.length - 1 || s.closed) junc.set(jkey(pc[0], s.pieces[(q + 1) % s.pieces.length][0]), [sid, q < s.pieces.length - 1 ? pc[1] + pc[2] : 0]); });
      const g2 = new Map(), n2 = new Map(); for (const [i, u] of s.gridAt) if (s.keptOrig.has(i)) { g2.set(newIndex(i), u); n2.set(newIndex(i), s.gridN.get(i)); } s.gridAt = g2; s.gridN = n2;
    }); }

    const res0 = { hand: !!handApplied, handGroups: handApplied ? out.map((s) => s.handGroups) : null };
    // fairing: strands relax into smooth curves that keep the crossings, their 45-degree directions and the diagram
    if (FAIR && !handApplied) {
      const xings = [];
      for (const nd of nodes) { const o = junc.get(jkey(nd.over[0], nd.over[1])), u2 = junc.get(jkey(nd.under[0], nd.under[1])); if (o && u2) xings.push([o[0], o[1], u2[0], u2[1], slideOf.get(nd.key) || null, nd.key]); }
      // two strands ending at the same grid point (a crossing cut by the edge of the patch) meet there like a crossing
      for (const [k, lst] of runsByKey) {
        if (lst.length !== 1 || isT[gidOf.get(k)] !== 0) continue;
        const [ci, r] = lst[0], m = cells[ci].runs.length, e = segLoc.get(SID(ci, r)), s2 = segLoc.get(SID(ci, (r + 1) % m));
        if (!e || !s2) continue;
        xings.push([e[0], e[3] === 1 ? e[1] + e[2] : e[1], s2[0], s2[3] === 1 ? s2[1] : s2[1] + s2[2], null, k]);
      }
      res0.fair = fairStrands(out, xings, obstacles, FAIR);
      if (FAIR.keepDebug) { res0.fairDebug = { nodes: res0.fair.nodes, obstacles: res0.fair.obstacles }; delete res0.fair.nodes; delete res0.fair.obstacles; }
      junc.clear(); segLoc.clear();
      out.forEach((s, sid) => {
        for (const [seg, a, n, d] of s.pieces) segLoc.set(seg, [sid, a, n, d]);
        s.pieces.forEach((pc, q) => { if (q < s.pieces.length - 1 || s.closed) junc.set(jkey(pc[0], s.pieces[(q + 1) % s.pieces.length][0]), [sid, q < s.pieces.length - 1 ? pc[1] + pc[2] : 0]); });
      });
    }
    // centripetal Catmull-Rom -> Bezier, y flipped
    const res = res0; res.strands = []; res.crossings = []; res.faces = [];
    const TENS = opts.tension || 1.0;
    for (const s of out) {
      const P = s.pts, n = P.length, np = s.closed ? n : n - 1;
      const p = new Float64Array(2 + 6 * np);
      p[0] = P[0][0]; p[1] = -P[0][1];
      if (s.bez) {
        for (let i = 0; i < np; i++) { const [c1, c2] = s.bez[i], P2 = P[(i + 1) % n], o = 2 + 6 * i; p[o] = c1[0]; p[o + 1] = -c1[1]; p[o + 2] = c2[0]; p[o + 3] = -c2[1]; p[o + 4] = P2[0]; p[o + 5] = -P2[1]; }
        res.strands.push({ c: 0, z: s.closed ? 1 : 0, p });
        continue;
      }
      // unit tangent at every point: Catmull-Rom direction, snapped to 45 degrees against the edge at grid points
      const T = [];
      for (let i = 0; i < n; i++) {
        let P0, P2;
        if (s.closed) { P0 = P[(i - 1 + n) % n]; P2 = P[(i + 1) % n]; } else { P0 = i > 0 ? P[i - 1] : P[0]; P2 = i + 1 < n ? P[i + 1] : P[n - 1]; }
        let t = s.tang ? s.tang[i] : unit(sub(P2, P0));
        const fixedT = opts.snap45 !== false && s.gridAt && s.gridAt.get(i);
        if (fixedT) t = fixedT;
        T.push(t);
      }
      for (let i = 0; i < np; i++) {
        const P1 = P[i], P2 = P[(i + 1) % n], T1 = T[i], T2 = T[(i + 1) % n];
        const L = nrm(sub(P2, P1)) * TENS / 3;
        const o = 2 + 6 * i;
        p[o] = P1[0] + T1[0] * L; p[o + 1] = -(P1[1] + T1[1] * L); p[o + 2] = P2[0] - T2[0] * L; p[o + 3] = -(P2[1] - T2[1] * L); p[o + 4] = P2[0]; p[o + 5] = -P2[1];
      }
      res.strands.push({ c: 0, z: s.closed ? 1 : 0, p });
    }
    for (const nd of nodes) {
      const o = junc.get(jkey(nd.over[0], nd.over[1])), u = junc.get(jkey(nd.under[0], nd.under[1]));
      if (o && u) res.crossings.push([o[0], o[1], u[0], u[1]]);
    }
    // crossings cut by the edge of the patch: two strand ends at one grid point, the e piece over the s piece
    res.ends = [];
    for (const [k, lst] of runsByKey) {
      if (lst.length !== 1 || isT[gidOf.get(k)] !== 0) continue;
      const [ci, r] = lst[0], m = cells[ci].runs.length, e = segLoc.get(SID(ci, r)), s = segLoc.get(SID(ci, (r + 1) % m));
      if (!e || !s) continue;
      res.ends.push([e[0], e[3] === 1 ? e[1] + e[2] : e[1], s[0], s[3] === 1 ? s[1] : s[1] + s[2], cells[ci].labels ? cells[ci].labels[r] : null]);
    }
    // colours
    const adj = res.strands.map(() => new Set());
    for (const [so, , su] of res.crossings) if (so !== su) { adj[so].add(su); adj[su].add(so); }
    const order = res.strands.map((_, i) => i).sort((a, b) => adj[b].size - adj[a].size);
    const col = new Array(res.strands.length).fill(-1);
    for (const sid of order) {
      const usedC = new Set(); for (const x of adj[sid]) if (col[x] >= 0) usedC.add(col[x]);
      let c = 0; while (c < 7 && usedC.has(c)) c++;
      col[sid] = c < 7 ? c : sid % 7; res.strands[sid].c = col[sid];
    }
    // faces
    const full = new Set(); for (const [k, lst] of runsByKey) if (lst.length === 2) full.add(k);
    const cellNb = cells.map(() => new Set());
    for (const nd of nodes) { const a = nd.over[0] >> 7, b = nd.over[1] >> 7; cellNb[a].add(b); cellNb[b].add(a); }
    const ccol = new Map();
    const pushFace = (k, c, segs, dirs) => {
      const r = [];
      segs.forEach((seg, i) => { const [sid, a, n, sd] = segLoc.get(seg); r.push(sid, a, n, dirs[i] === 1 ? sd : 1 - sd); });
      res.faces.push({ k, c, r });
    };
    cells.forEach((c, ci) => {
      if (!c.runs.every((run) => full.has(run.key))) return;
      const segs = c.runs.map((_, r) => SID(ci, r));
      if (!segs.every((s) => segLoc.has(s))) return;
      const usedC = new Set(); for (const x of cellNb[ci]) if (ccol.has(x)) usedC.add(ccol.get(x));
      let cc = 0; while (usedC.has(cc)) cc++;
      ccol.set(ci, cc);
      pushFace(0, cc % 6, segs, segs.map(() => 1));
    });
    const byV = new Map();
    cells.forEach((c, ci) => c.runs.forEach((_, r) => { const v = vkey(c.P[c.real[r]]); if (!byV.has(v)) byV.set(v, []); byV.get(v).push(SID(ci, r)); }));
    for (const [v, segs] of byV) {
      if ((deg.get(v) || 0) < 2 || !segs.every((s) => segLoc.has(s))) continue;
      const ends = new Map(); let ok = true;
      for (const s of segs) {
        const ci = s >> 7, r = s & 127, m = cells[ci].runs.length;
        const a = cells[ci].runs[(r - 1 + m) % m].key, b = cells[ci].runs[r].key;
        if (!full.has(a) || !full.has(b)) ok = false;
        ends.set(s, [a, b]);
      }
      if (!ok) continue;
      const ord = [segs[0]], dirs = [1]; let cur = ends.get(segs[0])[1]; const left = new Set(segs.slice(1));
      while (left.size) {
        let found = false;
        for (const s of left) {
          const [a, b] = ends.get(s);
          if (a === cur) { ord.push(s); dirs.push(1); cur = b; left.delete(s); found = true; break; }
          if (b === cur) { ord.push(s); dirs.push(0); cur = a; left.delete(s); found = true; break; }
        }
        if (!found) { ok = false; break; }
      }
      if (ok && cur === ends.get(segs[0])[0]) pushFace(1, 0, ord, dirs);
    }
    res.tree = treeInfo;
    let nb = 0; for (const [k, lst] of runsByKey) if (lst.length === 2 && isT[gidOf.get(k)]) nb++;
    res.breaks = nb;
    return res;
  }

  function outlines(cells) {
    return cells.map((c) => { const f = new Float64Array(c.P.length * 2); c.P.forEach((p, i) => { f[2 * i] = p[0]; f[2 * i + 1] = -p[1]; }); return f; });
  }

  const FAN = { fan21: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], fan14: [0, 2, 4, 6, 8, 9, 11], fan10: [1, 5, 10] };

  // the interactive viewer keeps the quick routing (no fairing, no simplification); a hand-drawn design, where one exists, is instant
  const QUICK = { fair: false, simplify: false, snap45: false };
  function create(N, radius, centre) {
    const tiles = makeTiles(N, radius, centre);
    const cache = {};
    const supC = {};
    const sup = (lv) => supC[lv] || (supC[lv] = cellsFromSupertiles(tiles, lv));
    const MODES = {
      fan21: (o) => build(cellsFan(tiles, FAN.fan21), 'edge', 0.18, 12, 0.15, Object.assign({ eps: 0.14, fanKind: 'fan21' }, QUICK, o)),
      fan14: (o) => build(cellsFan(tiles, FAN.fan14), 'edge', 0.22, 12, 0.18, Object.assign({ eps: 0.18, fanKind: 'fan14' }, QUICK, o)),
      fan10: (o) => build(cellsFan(tiles, FAN.fan10), 'edge', 0.26, 12, 0.2, Object.assign({ eps: 0.22, fanKind: 'fan10' }, QUICK, o)),
      edge: (o) => build(cellsFromTiles(tiles), 'edge', 0.26, 12, 0.22, Object.assign({ eps: 0.2 }, QUICK, o)),
      contact: (o) => build(cellsFromTiles(tiles), 'contact', 0.30, 12, 0.22, Object.assign({}, QUICK, o)),
      smooth: (o) => build(straighten(cellsFromTiles(tiles)), 'edge', 0.30, 12, 0.22, Object.assign({}, QUICK, o)),
      superhug: (o) => build(sup(1).map((c) => Object.assign({}, c)), 'contact', 0.55, 3, 0.5, Object.assign({ eps: 0.45 }, QUICK, o)),
      super: (o) => build(straighten(sup(1)), 'edge', 0.55, 8, 0.6, Object.assign({ eps: 0.5 }, QUICK, o)),
      super2hug: (o) => build(sup(2).map((c) => Object.assign({}, c)), 'contact', 1.2, 3, 1.2, Object.assign({ eps: 1.0 }, QUICK, o)),
      super2: (o) => build(straighten(sup(2)), 'edge', 1.2, 8, 1.5, Object.assign({ eps: 1.1 }, QUICK, o))
    };
    return {
      tileCount: tiles.length,
      tileOutlines: () => outlines(tiles),
      supOutlines: (lv) => outlines(sup(lv || 1)),
      fanOutlines: (kind) => outlines(cellsFan(tiles, FAN[kind])),
      // mode names: e.g. 'smooth' or 'smooth|thread'
      spokes: (kind) => FAN[kind],
      mode: (m) => {
        if (cache[m]) return cache[m];
        const [base, tag] = m.split('|');
        let opts = {};
        if (tag === 'thread') opts = { thread: true };
        else if (tag === 'spiral') opts = { thread: true, tree: 'spiral' };
        else if (tag && tag.startsWith('d=')) {
          const [edges, sp] = tag.slice(2).split(':'), spokes = {};
          (FAN[base] || []).forEach((v, i) => { spokes['s' + v] = +(sp[i] || 0); });
          opts = { design: { edges: +edges, spokes } };
        }
        return (cache[m] = MODES[base](opts));
      }
    };
  }
  return { create, makeTiles, PTS, KERNEL, FAN, HAND_DESIGNS, designKey };
})();
if (typeof module !== 'undefined') module.exports = SpectreEngine;
