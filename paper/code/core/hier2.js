// Deep hierarchical strand connectivity with typed arrays.
// usage: node hier2.js <family> <digits> <maxLevel> <bases e.g. 1,2,3,4,5,6>
const H = require('./hier.js');
const { PTS, IDENT, mul, trot, ttrans, tp, QUAD, levelTransforms, NAMES, SR } = H;
const [FAMILY, DIGITS, MAXL] = [process.argv[2], process.argv[3], +process.argv[4]];
const BASES0 = (process.argv[5] || '1,2,3,4').split(',').map(Number);
const ROUND = 100;   // coordinate rounding for vertex keys (vertices are at least ~0.5 apart)

// ---- shape: { E, px, py, qx, qy (Float64Array), pair (Int32Array 2E), reps: {b: Int32Array 2E} }
function fromTangle(t) {
  const E = t.edges.length, px = new Float64Array(E), py = new Float64Array(E), qx = new Float64Array(E), qy = new Float64Array(E), pair = new Int32Array(2 * E);
  t.edges.forEach((ed, e) => { px[e] = ed.p[0]; py[e] = ed.p[1]; qx[e] = ed.q[0]; qy[e] = ed.q[1]; });
  for (const [a, b] of t.pair) { const [e1, s1] = a.split(',').map(Number), [e2, s2] = b.split(',').map(Number); pair[2 * e1 + s1] = 2 * e2 + s2; }
  return { E, px, py, qx, qy, pair, reps: {} };
}
// union-find per base
let UF = {}; const ufFind = (b, x) => { const u = UF[b]; while (u[x] !== x) { u[x] = u[u[x]]; x = u[x]; } return x; };
const ufUnion = (b, x, y) => { x = ufFind(b, x); y = ufFind(b, y); if (x !== y) UF[b][x] = y; };
let LOST = {};

function compose(children, withReps) {
  const offs = new Int32Array(children.length + 1);
  children.forEach((c, i) => { offs[i + 1] = offs[i] + c.shape.E; });
  const M = offs[children.length];
  const PX = new Float64Array(M), PY = new Float64Array(M), QX = new Float64Array(M), QY = new Float64Array(M);
  const owner = new Int32Array(M);
  children.forEach(({ shape, T }, c) => {
    const o = offs[c];
    for (let e = 0; e < shape.E; e++) {
      const g = o + e; owner[g] = c;
      PX[g] = T[0] * shape.px[e] + T[1] * shape.py[e] + T[2]; PY[g] = T[3] * shape.px[e] + T[4] * shape.py[e] + T[5];
      QX[g] = T[0] * shape.qx[e] + T[1] * shape.qy[e] + T[2]; QY[g] = T[3] * shape.qx[e] + T[4] * shape.qy[e] + T[5];
    }
  });
  // integer keys
  const kpx = new Int32Array(M), kpy = new Int32Array(M), kqx = new Int32Array(M), kqy = new Int32Array(M);
  for (let g = 0; g < M; g++) { kpx[g] = Math.round(PX[g] * ROUND); kpy[g] = Math.round(PY[g] * ROUND); kqx[g] = Math.round(QX[g] * ROUND); kqy[g] = Math.round(QY[g] * ROUND); }
  // hash table on sorted endpoint pair
  let size = 1; while (size < 2 * M) size <<= 1;
  const hA = new Int32Array(size), hB = new Int32Array(size), hC = new Int32Array(size), hD = new Int32Array(size), hV = new Int32Array(size).fill(-1);
  const mate = new Int32Array(M).fill(-1), flip = new Uint8Array(M);
  const mix = (a, b, c, d) => { let h = Math.imul(a, 73856093) ^ Math.imul(b, 19349663) ^ Math.imul(c, 83492791) ^ Math.imul(d, 2654435761 | 0); h ^= h >>> 15; h = Math.imul(h, 0x2c1b3c6d); h ^= h >>> 12; return h & (size - 1); };
  for (let g = 0; g < M; g++) {
    let a = kpx[g], b = kpy[g], c = kqx[g], d = kqy[g], fl = 0;
    if (a > c || (a === c && b > d)) { const ta = a, tb = b; a = c; b = d; c = ta; d = tb; fl = 1; }   // fl: my P is the larger endpoint
    let h = mix(a, b, c, d);
    for (;;) {
      const v = hV[h];
      if (v < 0) { hA[h] = a; hB[h] = b; hC[h] = c; hD[h] = d; hV[h] = g; flip[g] = fl; break; }
      if (hA[h] === a && hB[h] === b && hC[h] === c && hD[h] === d) {
        if (mate[v] >= 0) throw new Error('edge shared by three children');
        mate[v] = g; mate[g] = v; const x = fl ^ flip[v]; flip[g] = x; flip[v] = x;   // flip: 1 if my P corresponds to mate's Q
        break;
      }
      h = (h + 1) & (size - 1);
    }
  }
  // parent edges
  let E = 0; const pidx = new Int32Array(M).fill(-1);
  for (let g = 0; g < M; g++) if (mate[g] < 0) pidx[g] = E++;
  const px = new Float64Array(E), py = new Float64Array(E), qx = new Float64Array(E), qy = new Float64Array(E), back = new Int32Array(E);
  for (let g = 0; g < M; g++) if (pidx[g] >= 0) { const k = pidx[g]; px[k] = PX[g]; py[k] = PY[g]; qx[k] = QX[g]; qy[k] = QY[g]; back[k] = g; }
  // rim sanity: every rim vertex should have degree 2
  { const cnt = new Map(); for (let k = 0; k < E; k++) { const a = Math.round(px[k] * ROUND) + ',' + Math.round(py[k] * ROUND), b = Math.round(qx[k] * ROUND) + ',' + Math.round(qy[k] * ROUND); cnt.set(a, (cnt.get(a) || 0) + 1); cnt.set(b, (cnt.get(b) || 0) + 1); } let bad = 0; for (const v of cnt.values()) if (v !== 2) bad++; if (bad) throw new Error('rim vertex degree error: ' + bad); }
  // walk
  const pair = new Int32Array(2 * E).fill(-1), visited = new Uint8Array(2 * M);
  const bases = withReps ? Object.keys(withReps).map(Number) : [];
  const reps = {}; for (const b of bases) reps[b] = new Int32Array(2 * E).fill(-1);
  const childPair = (g, s) => { const c = owner[g], sh = children[c].shape, q = sh.pair[2 * (g - offs[c]) + s]; return [offs[c] + (q >> 1), q & 1]; };
  const childRep = (b, g, s) => { const c = owner[g], sh = children[c].shape; const R = sh.reps[b]; return R ? R[2 * (g - offs[c]) + s] : -1; };
  const cross = (g, s) => { const m = mate[g]; const sm = flip[g] ? 1 - s : s; return [m, 1 - sm]; };
  const cur = {};
  for (let k = 0; k < E; k++) for (let s = 0; s < 2; s++) {
    if (pair[2 * k + s] >= 0) continue;
    let g = back[k], ss = s; for (const b of bases) cur[b] = -1; let guard = 0;
    for (;;) {
      if (++guard > 4 * M + 10) throw new Error('walk does not terminate');
      visited[2 * g + ss] = 1;
      for (const b of bases) { const r = childRep(b, g, ss); if (r >= 0) cur[b] = cur[b] < 0 ? ufFind(b, r) : (ufUnion(b, cur[b], r), ufFind(b, cur[b])); }
      const [g2, s2] = childPair(g, ss); visited[2 * g2 + s2] = 1;
      if (mate[g2] < 0) { const k2 = pidx[g2]; pair[2 * k + s] = 2 * k2 + s2; pair[2 * k2 + s2] = 2 * k + s; for (const b of bases) { reps[b][2 * k + s] = cur[b]; reps[b][2 * k2 + s2] = cur[b]; } break; }
      [g, ss] = cross(g2, s2);
    }
  }
  let loops = 0;
  for (let g = 0; g < M; g++) for (let s = 0; s < 2; s++) {
    if (visited[2 * g + s] || mate[g] < 0) continue;
    loops++; let gg = g, ss = s;
    for (;;) { visited[2 * gg + ss] = 1; for (const b of bases) { const r = childRep(b, gg, ss); if (r >= 0) LOST[b].add(ufFind(b, r)); } const [g2, s2] = childPair(gg, ss); visited[2 * g2 + s2] = 1; [gg, ss] = cross(g2, s2); if (visited[2 * gg + ss]) break; }
  }
  return { E, px, py, qx, qy, pair, reps, loops };
}

// ---- build
function run(digits, MAXL, BASES, quiet) {
UF = {}; LOST = {};
const tile = fromTangle(H.tileTangle(digits));
const result = [];
let shapes = {}; for (const t of NAMES) shapes[t] = tile;
shapes.Gamma = compose([{ shape: tile, T: IDENT }, { shape: tile, T: mul(ttrans(PTS[8][0], PTS[8][1]), trot(Math.PI / 6)) }], null);
let quad = QUAD, nest = null; const NB = {};
const t0 = Date.now();
for (let N = 1; N <= MAXL; N++) {
  const { trs, superQuad } = levelTransforms(quad);
  const next = {}; let loops = 0;
  for (const t of NAMES) { const kids = []; SR[t].forEach((s, i) => { if (s) kids.push({ shape: shapes[s], T: trs[i] }); }); next[t] = compose(kids, null); loops += next[t].loops; }
  // nest: Delta whose child 1 is the previous nest (with reps)
  const kids = []; SR.Delta.forEach((s, i) => { kids.push({ shape: (i === 1 && nest) ? nest : shapes[s], T: trs[i] }); });
  const active = {}; for (const b of BASES) if (b < N && UF[b]) active[b] = true;
  nest = compose(kids, Object.keys(active).length ? active : null);
  if (BASES.includes(N)) {   // start labels for base N: one id per arc of the nest at this level
    UF[N] = []; LOST[N] = new Set(); const R = new Int32Array(2 * nest.E).fill(-1); let id = 0;
    for (let p = 0; p < 2 * nest.E; p++) { if (R[p] >= 0) continue; R[p] = id; R[nest.pair[p]] = id; UF[N].push(id); id++; }
    nest.reps[N] = R; NB[N] = id;
  }
  const parts = [];
  for (const b of BASES) if (b <= N && UF[b]) { const roots = new Set(); for (let x = 0; x < UF[b].length; x++) roots.add(ufFind(b, x)); parts.push(`base ${b} (${NB[b]} arcs): ${roots.size}${LOST[b].size ? ' LOST ' + LOST[b].size : ''}`); }
  const merged = {}; for (const b of BASES) if (b <= N && UF[b]) { const roots = new Set(); for (let x = 0; x < UF[b].length; x++) roots.add(ufFind(b, x)); merged[b] = roots.size; }
  result.push({ N, loops, merged });
  if (!quiet) console.log(`level ${N}: rim ${next.Delta.E} edges, 8.2^N = ${Math.round(8.2 ** N).toLocaleString()} (rough size, not a tile count), loops ${loops}, ${Math.round((Date.now() - t0) / 1000)}s | strands meeting nested blocks: ${parts.join('; ')}`);
  shapes = next; quad = superQuad;
}
  return result;
}
module.exports = { run };
if (require.main === module) run(DIGITS, MAXL, BASES0, false);
