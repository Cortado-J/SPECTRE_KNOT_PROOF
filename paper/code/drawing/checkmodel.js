const DS = require('./dsg.js');
// Loophole check 1: does the exact hierarchical model (hier.js/reduce.js port pairing) agree with the ribbons the drawing
// engine actually draws?  Build a supertile's tiles in the engine, draw the design, read off each open ribbon's two
// ends (rim edge + which end of the edge it heads for) and compare the resulting pairing with the model's.
const fs = require("fs"); const MAXL0 = +(process.argv[2] || 2);
const { build } = require('../core/reduce.js');
const H = require('../core/hier.js');
const { PTS, KERNEL, IDENT, mul, trot, ttrans, tp, NAMES, SR } = H;
const engSrc = fs.readFileSync(__dirname + '/engine.js', 'utf8').replace('return { create, makeTiles, PTS, KERNEL, FAN, HAND_DESIGNS, designKey };', 'return { create, makeTiles, PTS, KERNEL, FAN, HAND_DESIGNS, designKey, build, cellsFan };').replace('const res = res0; res.strands = []; res.crossings = []; res.faces = [];', 'const res = res0; res.strands = []; res.crossings = []; res.faces = []; res.raw = strands; res.cells = cells;');
const ENG = eval(engSrc + '; SpectreEngine');
const MAXL = MAXL0;
const { LEV } = build(DS.digits, MAXL, true);
const G2 = mul(ttrans(PTS[8][0], PTS[8][1]), trot(Math.PI / 6));
function tileTransforms(t, L, T) { if (L === 0) return t === 'Gamma' ? [T, mul(T, G2)] : [T]; const trs = LEV[L - 1].trs; const out = []; SR[t].forEach((s, i) => { if (s) out.push(...tileTransforms(s, L - 1, mul(T, trs[i]))); }); return out; }
function engineTiles(transforms) { return transforms.map((T) => { const P0 = PTS.map((p) => tp(T, p)); let a = 0; for (let i = 0; i < 14; i++) { const q = P0[(i + 1) % 14]; a += P0[i][0] * q[1] - q[0] * P0[i][1]; } const rev = a < 0; const P = rev ? P0.slice().reverse() : P0; return { P, rev, kc: tp(T, KERNEL) }; }); }
const DESIGN = DS.design;
for (let L = 1; L <= MAXL; L++) for (const t of NAMES) {
  const sh = LEV[L - 1].shapes[t];
  const tiles = engineTiles(tileTransforms(t, L, IDENT));
  const res = DS.knot(ENG, tiles, { });
  // model rim edges by midpoint key
  const key = (x, y) => Math.round(x * 100) + ',' + Math.round(y * 100);
  const edgeByMid = new Map(); for (let e = 0; e < sh.E; e++) edgeByMid.set(key((sh.px[e] + sh.qx[e]) / 2, (sh.py[e] + sh.qy[e]) / 2), e);
  // a segment end of the engine -> model port.  segment (ci, r) end 1 sits at run r's grid point on the P side of that run
  // (the strand piece came round the run's start vertex); end 0 sits at run r-1's grid point on its Q side.
  const cells = res.cells;
  const portOfEnd = (seg, end) => {
    const ci = Math.floor(seg / 128), r = seg % 128, c = cells[ci], m = c.runs.length;
    const run = end === 1 ? c.runs[r] : c.runs[(r + m - 1) % m];
    const mid = run.pts.length === 2 ? [(run.pts[0][0] + run.pts[1][0]) / 2, (run.pts[0][1] + run.pts[1][1]) / 2] : null;
    if (!mid) return null; const e = edgeByMid.get(key(mid[0], mid[1])); if (e === undefined) return null;
    // run direction in the cell vs model edge direction P->Q
    const sameDir = Math.hypot(run.pts[0][0] - sh.px[e], run.pts[0][1] - sh.py[e]) < 1e-6;
    const side = end === 1 ? 0 : 1;                 // P side of the run / Q side of the run
    return 2 * e + (sameDir ? side : 1 - side);
  };
  let ok = 0, bad = 0, unmatched = 0, closed = 0; const seen = new Set();
  for (const [seq, isClosed] of res.raw) {
    if (isClosed) { closed++; continue; }
    const [seg0, d0] = seq[0], [seg1, d1] = seq[seq.length - 1];
    const a = portOfEnd(seg0, 1 - d0), b = portOfEnd(seg1, d1);
    if (a === null || b === null) { unmatched++; continue; }
    if (sh.pair[a] === b) ok++; else bad++;
    seen.add(a); seen.add(b);
  }
  console.log(`level ${L} ${t.padEnd(6)}: ${tiles.length} tiles, ${res.strands.length} ribbon pieces drawn, model has ${sh.E} arcs | pairs agree ${ok}, disagree ${bad}, unmatched ${unmatched}, closed ${closed}, ports seen ${seen.size}/${2 * sh.E}`);
}
