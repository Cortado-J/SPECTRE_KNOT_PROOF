// Shared helpers for the L5 study. Loads the hierarchy from core/reduce.js (design 0.1:01, fan21).
process.env.FAM = 'fan21';
const V = __dirname + '/../core/';
const R = require(V + 'reduce.js');
const H = require(V + 'hier.js');
const { NAMES, SR, mul, IDENT } = H;
const det = (T) => T[0] * T[4] - T[1] * T[3];
const vert = (sh, k) => { const e = sh.cyc[k]; return sh.fwd[k] ? [sh.px[e], sh.py[e]] : [sh.qx[e], sh.qy[e]]; };
const tp = (T, p) => [T[0] * p[0] + T[1] * p[1] + T[2], T[3] * p[0] + T[4] * p[1] + T[5]];
const key = (p) => Math.round(p[0] * 100) + ',' + Math.round(p[1] * 100);

let CACHE = null;
function load(L) {
  if (CACHE && CACHE.L >= L) return CACHE;
  const b = R.build('01222222222222', L, true);
  CACHE = Object.assign({ L }, b);
  return CACHE;
}
// shape of kind s at level m (m >= 0)
function shapeAt(D, m, s) { if (m === 0) return s === 'Gamma' ? D.gamma : D.tile; return D.LEV[m - 1].shapes[s]; }
// children of kind T at level N (N >= 1): [{kind, T, sr}] in the order used by reduce.js (nulls skipped)
function kidsOf(D, N, t) { const out = []; SR[t].forEach((s, i) => { if (s) out.push({ kind: s, T: D.LEV[N - 1].trs[i], sr: i }); }); return out; }
// all level-m descendants of a level-M supertile of kind t, with transforms into its frame
function descendants(D, M, t, m) {
  let cur = [{ kind: t, T: IDENT, path: [] }];
  for (let N = M; N > m; N--) {
    const nx = [];
    for (const p of cur) kidsOf(D, N, p.kind).forEach((k, c) => nx.push({ kind: k.kind, T: mul(p.T, k.T), path: p.path.concat([c]) }));
    cur = nx;
  }
  return cur;
}
module.exports = { R, H, NAMES, SR, mul, IDENT, det, vert, tp, key, load, shapeAt, kidsOf, descendants };
