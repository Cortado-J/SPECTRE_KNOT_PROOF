// Overlap / exact-fill check for the code's supertile patches.
// For kind T at level N: expand to level-0 tiles (Mystic -> 2 tiles), orient each tile ccw,
// form the 1-chain sum of directed unit edges (vertices snapped to a 1e-3 grid), cancel opposite pairs.
// PASS iff the residual chain is a single simple closed cycle equal to the code's rim, with net counts in {0,1}.
// Then sum of tile winding numbers = winding of rim, in {0,1}: tiles have disjoint interiors and exactly fill the rim.
// Also: shoelace(rim) vs nTiles*area(tile); snapping tolerance (max deviation of a vertex from its grid key, min distance
// between distinct snapped vertices).
const ARGV = process.argv.slice();
const L5 = __dirname + '/../hierarchy/lib.js';
const { H, NAMES, mul, IDENT, det, load, shapeAt, kidsOf } = require(L5);
const { PTS } = H;
const MAXL = +(ARGV[2] || 6), ONLY = ARGV[3] && ARGV[3] !== 'all' ? ARGV[3].split(',') : NAMES, MINL = +(ARGV[4] || 1);
const D = load(MAXL);
const trot = (a) => { const c = Math.cos(a), s = Math.sin(a); return [c, -s, 0, s, c, 0]; };
const MYST = [IDENT, mul([1, 0, PTS[8][0], 0, 1, PTS[8][1]], trot(Math.PI / 6))];
const area = (P) => { let a = 0; for (let i = 0; i < P.length; i++) { const p = P[i], q = P[(i + 1) % P.length]; a += p[0] * q[1] - q[0] * p[1]; } return a / 2; };
const AT = area(PTS);
const SC = 1000; console.log("tile area", AT);
function check(N, T) {
  const t0 = Date.now();
  // collect tile transforms
  let cur = [{ kind: T, M: IDENT }];
  for (let n = N; n >= 1; n--) { const nx = []; for (const p of cur) for (const k of kidsOf(D, n, p.kind)) nx.push({ kind: k.kind, M: mul(p.M, k.T) }); cur = nx; }
  const tiles = []; for (const p of cur) { if (p.kind === 'Gamma') for (const m of MYST) tiles.push(mul(p.M, m)); else tiles.push(p.M); }
  const nT = tiles.length;
  // vertex snapping
  const vmap = new Map(); const VX = [], VY = []; let maxdev = 0;
  const vid = (x, y) => { const kx = Math.round(x * SC), ky = Math.round(y * SC); const key = (kx + 2 ** 25) * 2 ** 26 + (ky + 2 ** 25); let id = vmap.get(key); if (id === undefined) { id = VX.length; vmap.set(key, id); VX.push(x); VY.push(y); } else { const d = Math.hypot(VX[id] - x, VY[id] - y); if (d > maxdev) maxdev = d; } return id; };
  const net = new Map(); // key a*2^26+b (a<b) -> net count in direction a->b
  let negTiles = 0;
  for (const M of tiles) {
    const ids = PTS.map((p) => vid(M[0] * p[0] + M[1] * p[1] + M[2], M[3] * p[0] + M[4] * p[1] + M[5]));
    const d = det(M); if (Math.abs(Math.abs(d) - 1) > 1e-9) throw new Error('non-isometry');
    const order = d > 0 ? ids : ids.slice().reverse(); // PTS is ccw (area>0) so det<0 reverses
    if (d < 0) negTiles++;
    for (let i = 0; i < 14; i++) { const a = order[i], b = order[(i + 1) % 14]; const [u, v, s] = a < b ? [a, b, 1] : [b, a, -1]; const k = u * 2 ** 26 + v; net.set(k, (net.get(k) || 0) + s); }
  }
  // residual
  const out = new Map(); let bad = 0, resid = 0;
  for (const [k, c] of net) { if (c === 0) continue; if (Math.abs(c) !== 1) { bad++; continue; } resid++; const u = Math.floor(k / 2 ** 26), v = k - u * 2 ** 26; const [a, b] = c > 0 ? [u, v] : [v, u]; if (out.has(a)) bad++; out.set(a, b); }
  // single simple cycle?
  let cycOK = bad === 0 && out.size === resid; let len = 0;
  if (cycOK) { const s = out.keys().next().value; let v = s; const seen = new Set(); do { if (seen.has(v)) { cycOK = false; break; } seen.add(v); v = out.get(v); len++; if (v === undefined) { cycOK = false; break; } } while (v !== s); if (len !== resid) cycOK = false; }
  // compare with code rim (undirected edge set) and shoelace
  const sh = shapeAt(D, N, T); let rimMatch = sh.E === resid, rimArea = 0;
  for (let e = 0; e < sh.E; e++) {
    const a = vid(sh.px[e], sh.py[e]), b = vid(sh.qx[e], sh.qy[e]);
    if (!(out.get(a) === b || out.get(b) === a)) rimMatch = false;
  }
  // shoelace of residual cycle
  if (cycOK) { for (const [a, b] of out) rimArea += VX[a] * VY[b] - VX[b] * VY[a]; rimArea /= 2; }
  // min distance between distinct snapped vertices (grid hash, cell 0.5)
  let mind = Infinity; const g = new Map(); const cell = 0.5;
  for (let i = 0; i < VX.length; i++) { const cx = Math.floor(VX[i] / cell), cy = Math.floor(VY[i] / cell); const k = cx * 1e6 + cy; if (!g.has(k)) g.set(k, []); g.get(k).push(i); }
  for (const [k, lst] of g) { const cx = Math.round(k / 1e6), cy = k - cx * 1e6; for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) { const l2 = g.get((cx + dx) * 1e6 + cy + dy); if (!l2) continue; for (const i of lst) for (const j of l2) if (i < j) { const d = Math.hypot(VX[i] - VX[j], VY[i] - VY[j]); if (d < mind) mind = d; } } }
  const relA = Math.abs(rimArea - nT * AT) / (nT * AT);
  const pass = cycOK && rimMatch && relA < 1e-9 && maxdev < 1e-6 && mind > 0.1;
  console.log(`L${N} ${T.padEnd(6)} tiles=${nT} reflected=${negTiles} rimE=${resid} cycle=${cycOK} rim=code:${rimMatch} area(rim)/(n*A)-1=${relA.toExponential(1)} badNet=${bad} maxdev=${maxdev.toExponential(1)} minVdist=${mind.toFixed(4)} ${pass ? 'PASS' : 'FAIL'} (${Date.now() - t0}ms)`);
  return pass;
}
let all = true;
for (let N = MINL; N <= MAXL; N++) for (const T of ONLY) all = check(N, T) && all;
console.log(all ? 'ALL PASS' : 'SOME FAIL');
