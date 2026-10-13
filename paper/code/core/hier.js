// Exact strand connectivity of a one-tile design up the spectre substitution hierarchy.
// A level-N supertile is represented by its boundary unit edges (in its own frame) and the pairing of
// the two strand ends ("ports") on each boundary edge. Level N+1 is composed from level-N children by
// identifying shared edges; interior detail is never needed, so the depth is limited only by the
// exponential growth of the boundary.
//
// usage: node hier.js <fan14|fan21> <spoke digits> <maxLevel> [nestBase]
const S3 = Math.sqrt(3);
const PTS = [[0, 0], [1, 0], [1.5, -S3 / 2], [1.5 + S3 / 2, 0.5 - S3 / 2], [1.5 + S3 / 2, 1.5 - S3 / 2],
  [2.5 + S3 / 2, 1.5 - S3 / 2], [3 + S3 / 2, 1.5], [3, 2], [3 - S3 / 2, 1.5],
  [2.5 - S3 / 2, 1.5 + S3 / 2], [1.5 - S3 / 2, 1.5 + S3 / 2], [0.5 - S3 / 2, 1.5 + S3 / 2],
  [-S3 / 2, 1.5], [0, 1]];
const KERNEL = [1.6268, 0.9];
const FAN = { fan21: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], fan14: [0, 2, 4, 6, 8, 9, 11], fan10: [1, 5, 10] };
const IDENT = [1, 0, 0, 0, 1, 0];
const mul = (A, B) => [A[0] * B[0] + A[1] * B[3], A[0] * B[1] + A[1] * B[4], A[0] * B[2] + A[1] * B[5] + A[2],
  A[3] * B[0] + A[4] * B[3], A[3] * B[1] + A[4] * B[4], A[3] * B[2] + A[4] * B[5] + A[5]];
const trot = (a) => { const c = Math.cos(a), s = Math.sin(a); return [c, -s, 0, s, c, 0]; };
const ttrans = (x, y) => [1, 0, x, 0, 1, y];
const tp = (M, P) => [M[0] * P[0] + M[1] * P[1] + M[2], M[3] * P[0] + M[4] * P[1] + M[5]];
const transTo = (p, q) => ttrans(q[0] - p[0], q[1] - p[1]);
const QUAD = [PTS[3], PTS[5], PTS[7], PTS[11]];
const vkey = (p) => Math.round(p[0] * 1000) + ',' + Math.round(p[1] * 1000);

const [FAMILY, DIGITS, MAXL, NESTB] = [process.argv[2] || 'fan14', process.argv[3] || '0000000', +(process.argv[4] || 8), +(process.argv[5] || 1)];
const spokesArg = FAMILY;
const spokes = FAN[FAMILY];
const spokeState = {}; spokes.forEach((v, k) => { spokeState[v] = +(DIGITS[k] || 0); });

// ---------------------------------------------------------------- the tile's own tangle
// cells: sectors [kernel, P[a], ..., P[b]]; runs: polygon edges; strand ends per run: e (arriving at the grid point
// from the run's start vertex) and s (leaving towards its end vertex)
function tileTangle(digitsOverride) {
  const spokeState = {}; spokes.forEach((v, k) => { spokeState[v] = +((digitsOverride || DIGITS)[k] || 0); });
  const idx = spokes.slice().sort((a, b) => a - b);
  const cells = [];
  for (let j = 0; j < idx.length; j++) {
    const a = idx[j], b = idx[(j + 1) % idx.length];
    const poly = [KERNEL], kind = ['s' + a]; let i = a;
    for (;;) { poly.push(PTS[i]); if (i === b) break; kind.push('e' + i); i = (i + 1) % 14; }
    kind.push('s' + b);
    cells.push({ poly, kind });
  }
  const SID = (ci, r) => ci * 32 + r;
  const byKey = new Map();
  cells.forEach((c, ci) => c.kind.forEach((k, r) => { if (!byKey.has(k)) byKey.set(k, []); byKey.get(k).push([ci, r]); }));
  const link = new Map();
  const ports = new Map();   // 'i,0' (near PTS[i]) / 'i,1' (near PTS[i+1]) -> strand end id
  for (const [k, lst] of byKey) {
    if (k[0] === 'e') {
      const [ci, r] = lst[0], m = cells[ci].kind.length;
      const e = SID(ci, r) * 2 + 1, s = SID(ci, (r + 1) % m) * 2;
      const i = +k.slice(1); ports.set(i + ',0', e); ports.set(i + ',1', s);
      continue;
    }
    const st = spokeState[+k.slice(1)];
    const [[c1, r1], [c2, r2]] = lst; const m1 = cells[c1].kind.length, m2 = cells[c2].kind.length;
    const e1 = SID(c1, r1) * 2 + 1, s1 = SID(c1, (r1 + 1) % m1) * 2, e2 = SID(c2, r2) * 2 + 1, s2 = SID(c2, (r2 + 1) % m2) * 2;
    const L = (a, b) => { link.set(a, b); link.set(b, a); };
    if (st === 0) { L(e1, e2); L(s1, s2); } else if (st === 1) { L(e1, s1); L(e2, s2); } else { L(e1, s2); L(s1, e2); }
  }
  // walk from each port: strand end -> other end of the same segment -> link -> ...
  const other = (x) => x ^ 1;
  const pair = new Map(); const seen = new Set(); let loops = 0;
  const endOf = new Map(); for (const [p, x] of ports) endOf.set(x, p);
  for (const [p, x] of ports) {
    if (pair.has(p)) continue;
    let cur = other(x); seen.add(x); seen.add(cur);
    for (;;) {
      if (endOf.has(cur)) { const q = endOf.get(cur); pair.set(p, q); pair.set(q, p); break; }
      const nx = link.get(cur); if (nx === undefined) throw new Error('dangling end at ' + cur);
      seen.add(nx); cur = other(nx); seen.add(cur);
    }
  }
  // closed loops inside the tile
  for (const [a] of link) { if (seen.has(a)) continue; let cur = a; loops++; for (;;) { seen.add(cur); const o = other(cur); seen.add(o); cur = link.get(o); if (cur === a) break; } }
  const edges = []; for (let i = 0; i < 14; i++) edges.push({ p: PTS[i], q: PTS[(i + 1) % 14] });
  const pr = new Map(); for (const [a, b] of pair) pr.set(a, b);   // keys 'edge,side'
  return { edges, pair: pr, loops, labels: null };
}

// ---------------------------------------------------------------- composition
function compose(children, labelChild) {
  // children: [{ shape, T }]. Returns shape in parent frame. If labelChild >= 0, that child's arc labels propagate.
  const ek = new Map();      // parent edge key -> [{c, e, P, Q}]
  const cinfo = [];
  children.forEach(({ shape, T }, c) => {
    const info = [];
    shape.edges.forEach((ed, e) => {
      const P = tp(T, ed.p), Q = tp(T, ed.q), kp = vkey(P), kq = vkey(Q);
      const key = kp < kq ? kp + '|' + kq : kq + '|' + kp;
      const rec = { c, e, P, Q, kp, kq, key };
      info.push(rec);
      if (!ek.has(key)) ek.set(key, []); ek.get(key).push(rec);
    });
    cinfo.push(info);
  });
  const outer = []; const outerIndex = new Map();   // key -> parent edge index
  for (const [key, lst] of ek) {
    if (lst.length === 1) { outerIndex.set(key, outer.length); outer.push(lst[0]); }
    else if (lst.length !== 2) throw new Error('edge shared by ' + lst.length + ' children');
  }
  const edges = outer.map((r) => ({ p: r.P, q: r.Q }));
  // child port (c, e, side) <-> string
  const cp = (c, e, s) => c + ':' + e + ',' + s;
  const partnerInChild = (c, e, s) => { const q = children[c].shape.pair.get(e + ',' + s); const [ee, ss] = q.split(','); return [c, +ee, +ss]; };
  const cross = (c, e, s) => {
    const rec = cinfo[c][e], lst = ek.get(rec.key), o = lst[0].c === c && lst[0].e === e ? lst[1] : lst[0];
    const endKey = s === 0 ? rec.kp : rec.kq;                // endpoint we are near
    const sO = o.kp === endKey ? 0 : 1;                       // same endpoint in the other child
    return [o.c, o.e, 1 - sO];                                // straight through: continue near the other endpoint
  };
  const isOuter = (c, e) => outerIndex.has(cinfo[c][e].key);
  const toParentPort = (c, e, s) => { const rec = cinfo[c][e], k = outerIndex.get(rec.key), o = outer[k]; const endKey = s === 0 ? rec.kp : rec.kq; return k + ',' + (o.kp === endKey ? 0 : 1); };
  const pair = new Map(), labels = new Map(); const visited = new Set(); let loops = 0, lostLabels = new Set();
  const childLabels = (c, e, s) => { const L = children[c].shape.labels; return L ? L.get(e + ',' + s) : null; };
  for (let k = 0; k < outer.length; k++) for (const s of [0, 1]) {
    const start = outer[k]; const startPort = k + ',' + s;
    if (pair.has(startPort)) continue;
    let [c, e, ss] = [start.c, start.e, (s === 0 ? (start.kp === (start.kp) ? 0 : 1) : 1)];
    // side s of the parent edge is the endpoint P (s=0) or Q (s=1) of outer[k], which is the child's own p/q
    ss = s;
    const acc = new Set();
    for (;;) {
      visited.add(cp(c, e, ss));
      const [c2, e2, s2] = partnerInChild(c, e, ss); visited.add(cp(c2, e2, s2));
      if (c === labelChild) { const L = childLabels(c, e, ss); if (L) for (const x of L) acc.add(x); }
      if (isOuter(c2, e2)) { const q = toParentPort(c2, e2, s2); pair.set(startPort, q); pair.set(q, startPort); if (acc.size) { labels.set(startPort, acc); labels.set(q, acc); } break; }
      [c, e, ss] = cross(c2, e2, s2);
    }
  }
  // closed loops: internal child ports never visited
  children.forEach(({ shape }, c) => {
    for (const p of shape.pair.keys()) {
      const [e, s] = p.split(',').map(Number); if (visited.has(cp(c, e, s)) || isOuter(c, e)) continue;
      loops++; let [cc, ee, ss] = [c, e, s];
      for (;;) { visited.add(cp(cc, ee, ss)); const [c2, e2, s2] = partnerInChild(cc, ee, ss); visited.add(cp(c2, e2, s2));
        if (cc === labelChild) { const L = childLabels(cc, ee, ss); if (L) for (const x of L) lostLabels.add(x); }
        [cc, ee, ss] = cross(c2, e2, s2); if (visited.has(cp(cc, ee, ss))) break; }
    }
  });
  return { edges, pair, loops, labels: labels.size ? labels : null, lostLabels };
}

// ---------------------------------------------------------------- substitution
const NAMES = ['Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Phi', 'Psi'];
const SR = {
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
function levelTransforms(quad) {
  const R = [-1, 0, 0, 0, 1, 0];
  const rules = [[60, 3, 1], [0, 2, 0], [60, 3, 1], [60, 3, 1], [0, 2, 0], [60, 3, 1], [-120, 3, 3]];
  let trs = [IDENT], tot = 0, rot = IDENT, tq = quad.slice();
  for (const [ang, fr, to] of rules) {
    if (ang !== 0) { tot += ang; rot = trot(tot * Math.PI / 180); tq = quad.map((q) => tp(rot, q)); }
    trs.push(mul(transTo(tq[to], tp(trs[trs.length - 1], quad[fr])), rot));
  }
  trs = trs.map((t) => mul(R, t));
  const superQuad = [tp(trs[6], quad[2]), tp(trs[5], quad[1]), tp(trs[3], quad[2]), tp(trs[0], quad[1])];
  return { trs, superQuad };
}

if (typeof module !== 'undefined') module.exports = { PTS, KERNEL, FAN, IDENT, mul, trot, ttrans, tp, transTo, QUAD, vkey, compose, levelTransforms, NAMES, SR, tileTangle: (d) => tileTangle(d) };
if (require.main === module) {
const tile = tileTangle();
console.log(FAMILY, 'spokes', DIGITS, '| tile: 28 ports, closed loops inside the tile:', tile.loops);
let shapes = {};
for (const n of NAMES) shapes[n] = tile;
shapes.Gamma = compose([{ shape: tile, T: IDENT }, { shape: tile, T: mul(ttrans(PTS[8][0], PTS[8][1]), trot(Math.PI / 6)) }], -1);
// nest: the Delta at the fixed point, with labels on the arcs of the level-NESTB Delta
let nest = null, nestArcs = 0;
let quad = QUAD;
const nestHistory = [];
for (let N = 1; N <= MAXL; N++) {
  const { trs, superQuad } = levelTransforms(quad);
  const next = {};
  let loopsThisLevel = 0;
  for (const t of NAMES) {
    const kids = []; SR[t].forEach((s, i) => { if (s) kids.push({ shape: shapes[s], T: trs[i] }); });
    next[t] = compose(kids, -1);
    loopsThisLevel += next[t].loops;
  }
  // nest step
  if (N === NESTB) {
    nest = next.Delta;
    const lab = new Map(); let id = 0; const seenP = new Set();
    for (const [a, b] of nest.pair) { if (seenP.has(a)) continue; seenP.add(a); seenP.add(b); const S = new Set([id++]); lab.set(a, S); lab.set(b, S); }
    nest = Object.assign({}, nest, { labels: lab }); nestArcs = id;
  } else if (N > NESTB) {
    const kids = []; SR.Delta.forEach((s, i) => { kids.push({ shape: s === 'Delta' && i === 1 ? nest : shapes[s], T: trs[i] }); });
    const li = kids.findIndex((k) => k.shape === nest);
    const before = nest;
    nest = compose(kids, li);
    // edges of the nest child on the parent's outer boundary
    const T = trs[1]; const outerKeys = new Set(nest.edges.map((ed) => { const a = vkey(ed.p), b = vkey(ed.q); return a < b ? a + '|' + b : b + '|' + a; }));
    let onRim = 0; for (const ed of before.edges) { const P = tp(T, ed.p), Q = tp(T, ed.q); const a = vkey(P), b = vkey(Q); if (outerKeys.has(a < b ? a + '|' + b : b + '|' + a)) onRim++; }
    nest.onRim = onRim;
  }
  const ports = next.Delta.edges.length * 2;
  let classes = '-', lost = '';
  if (nest && N >= NESTB) {
    const sets = new Set(); if (nest.labels) for (const S of nest.labels.values()) sets.add(S);
    classes = sets.size; if (nest.lostLabels && nest.lostLabels.size) lost = ' LOST ' + nest.lostLabels.size + ' arcs into loops';
  }
  const tilesApprox = Math.round(8.2 ** N * 1.05);
  console.log(`level ${N}: Delta boundary ${next.Delta.edges.length} edges (${ports} ports), ~${tilesApprox.toLocaleString()} tiles; closed loops inside any level-${N} supertile: ${loopsThisLevel}; arcs of the level-${NESTB} Delta (${nestArcs}) fall into ${classes} strands within the level-${N} Delta${lost}`);
  if (nest && nest.onRim !== undefined) console.log(`   (nest child has ${nest.onRim} of its ${nest.edges ? '' : ''}boundary edges on the parent's rim)`);
  nestHistory.push(classes);
  shapes = next; quad = superQuad;
}
}
