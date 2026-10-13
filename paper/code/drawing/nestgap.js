// Does the nest block N_b share any vertex with the rim of N_{b+2}?  And the smallest distance between them.
const MAXL = +(process.argv[2] || 8);
const DS = require('./dsg.js');
const { build } = require('../core/reduce.js');
const H = require('../core/hier.js');
const { LEV } = build(DS.digits, MAXL, true);
const key = (x, y) => Math.round(x * 100) + ',' + Math.round(y * 100);
for (let b = 1; b + 2 <= MAXL; b++) {
  const base = LEV[b - 1].shapes.Delta, anc = LEV[b + 1].shapes.Delta;
  const T = H.mul(LEV[b + 1].trs[1], LEV[b].trs[1]);
  const rimV = new Set(); for (let e = 0; e < anc.E; e++) { rimV.add(key(anc.px[e], anc.py[e])); rimV.add(key(anc.qx[e], anc.qy[e])); }
  let shared = 0; const pts = [];
  for (let e = 0; e < base.E; e++) { const p = H.tp(T, [base.px[e], base.py[e]]); pts.push(p); if (rimV.has(key(p[0], p[1]))) shared++; }
  // min distance from base rim vertices to ancestor rim segments
  let dmin = 1e18;
  for (const c of pts) for (let e = 0; e < anc.E; e++) { const ax = anc.px[e], ay = anc.py[e], vx = anc.qx[e] - ax, vy = anc.qy[e] - ay; const L2 = vx * vx + vy * vy; let u = ((c[0] - ax) * vx + (c[1] - ay) * vy) / L2; u = Math.max(0, Math.min(1, u)); const d = Math.hypot(ax + u * vx - c[0], ay + u * vy - c[1]); if (d < dmin) dmin = d; }
  console.log(`N_${b} vs rim of N_${b + 2}: shared vertices ${shared}, smallest gap ${dmin.toFixed(3)} edge lengths`);
}
