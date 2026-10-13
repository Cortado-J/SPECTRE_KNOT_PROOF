const DS = require('./dsg.js');
// distance from the level-1 base block of the nest (child-1 chain) to the rim of N_k, k = 2..MAXL
const MAXL = +(process.argv[2] || 9);
const { build } = require('../core/reduce.js');
const H = require('../core/hier.js');
const { LEV } = build(DS.digits, MAXL, true);
const base = LEV[0].shapes.Delta;
let cx = 0, cy = 0; for (let e = 0; e < base.E; e++) { cx += base.px[e]; cy += base.py[e]; } cx /= base.E; cy /= base.E;
let T = H.IDENT;
for (let k = 2; k <= MAXL; k++) {
  T = H.mul(LEV[k - 1].trs[1], T);
  const c = H.tp(T, [cx, cy]); const sh = LEV[k - 1].shapes.Delta;
  let dmin = 1e18, far = 0;
  for (let e = 0; e < sh.E; e++) { const ax = sh.px[e], ay = sh.py[e], bx = sh.qx[e], by = sh.qy[e]; const vx = bx - ax, vy = by - ay; const L2 = vx * vx + vy * vy; let u = ((c[0] - ax) * vx + (c[1] - ay) * vy) / L2; u = Math.max(0, Math.min(1, u)); const dx = ax + u * vx - c[0], dy = ay + u * vy - c[1]; const d = Math.sqrt(dx * dx + dy * dy); if (d < dmin) dmin = d; if (d > far) far = d; }
  console.log(`N_${k}: base centre ${dmin.toFixed(1)} edge lengths from the nearest rim point, ${far.toFixed(0)} from the farthest; ~${Math.round(8.2 ** k).toLocaleString()} tiles`);
}
