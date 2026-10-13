// Reduced (parity-only) description of each level of the spectre hierarchy, and the reduced composition.
//
// A level-N supertile's tangle is (by the exact computation) "hooks at every rim vertex except a crossover at two
// defect vertices".  When such children are glued along a shared run of n unit edges, the strands zigzag along the run
// and the outcome depends only on n mod 2 (zigzag lemma).  So the parent's tangle is determined by the REDUCED DATA:
// the skeleton of children, the marks (junction vertices + defect vertices), the parity of every run between marks,
// and which runs face which.  This file
//   (1) extracts the reduced data from the directly composed geometry (floating point) at every level,
//   (2) runs the reduced composition on it and compares with the exact tangle,
//   (3) prints a canonical encoding of the reduced data so that levels can be compared,
//   (4) extracts the two-level data needed for the nest (positions of a supertile's own rim marks inside the runs it
//       gets as child 1 of Delta at the next level).
// usage: node reduce.js <digits> <maxLevel>
const DIGITS = process.argv[2] || '0222221', MAXL = +(process.argv[3] || 9), DUMP = process.argv[4] === 'dump';
process.argv[2] = process.env.FAM || 'fan14'; process.argv[3] = DIGITS;
const H = require('./hier.js');
const { PTS, IDENT, mul, trot, ttrans, QUAD, levelTransforms, NAMES, SR } = H;
const ROUND = 100;
const det = (T) => T[0] * T[4] - T[1] * T[3];

// ------------------------------------------------------------------ shapes
// {E, px,py,qx,qy, pair(2E), cyc(E), fwd(E), defA, defB (cycle positions), marks: [{pos, tag}] own rim marks}
function cycleOf(E, px, py, qx, qy) {
  const key = (x, y) => Math.round(x * ROUND) + ',' + Math.round(y * ROUND);
  const at = new Map();
  for (let e = 0; e < E; e++) { for (const [k, s] of [[key(px[e], py[e]), 0], [key(qx[e], qy[e]), 1]]) { if (!at.has(k)) at.set(k, []); at.get(k).push(e * 2 + s); } }
  for (const l of at.values()) if (l.length !== 2) throw new Error('rim vertex degree ' + l.length);
  const cyc = new Int32Array(E), fwd = new Uint8Array(E); const used = new Uint8Array(E);
  let e = 0, s = 0;   // traverse edge e starting from side s
  for (let k = 0; k < E; k++) {
    cyc[k] = e; fwd[k] = s === 0 ? 1 : 0; used[e] = 1;
    const endKey = s === 0 ? key(qx[e], qy[e]) : key(px[e], py[e]);
    const l = at.get(endKey); const o = (l[0] >> 1) === e ? l[1] : l[0];
    e = o >> 1; s = o & 1;
    if (k < E - 1 && used[e]) throw new Error('rim not a single cycle');
  }
  // orientation: signed area
  let A = 0;
  for (let k = 0; k < E; k++) { const e = cyc[k]; const ax = fwd[k] ? px[e] : qx[e], ay = fwd[k] ? py[e] : qy[e], bx = fwd[k] ? qx[e] : px[e], by = fwd[k] ? qy[e] : py[e]; A += ax * by - bx * ay; }
  if (A < 0) { const c2 = new Int32Array(E), f2 = new Uint8Array(E); for (let k = 0; k < E; k++) { c2[k] = cyc[E - 1 - k]; f2[k] = 1 - fwd[E - 1 - k]; } return { cyc: c2, fwd: f2 }; }
  return { cyc, fwd };
}
const portL = (sh, k) => { const j = (k + sh.E - 1) % sh.E; return 2 * sh.cyc[j] + (sh.fwd[j] ? 1 : 0); };   // port near vertex k on the edge before it
const portR = (sh, k) => 2 * sh.cyc[k] + (sh.fwd[k] ? 0 : 1);                                           // port near vertex k on the edge after it
const vert = (sh, k) => { const e = sh.cyc[k]; return sh.fwd[k] ? [sh.px[e], sh.py[e]] : [sh.qx[e], sh.qy[e]]; };
function finishShape(sh) {
  Object.assign(sh, cycleOf(sh.E, sh.px, sh.py, sh.qx, sh.qy));
  const defs = [];
  for (let k = 0; k < sh.E; k++) if (sh.pair[portL(sh, k)] !== portR(sh, k)) defs.push(k);
  sh.defs = defs;
  return sh;
}
function fromTangle(t) {
  const E = t.edges.length, px = new Float64Array(E), py = new Float64Array(E), qx = new Float64Array(E), qy = new Float64Array(E), pair = new Int32Array(2 * E);
  t.edges.forEach((ed, e) => { px[e] = ed.p[0]; py[e] = ed.p[1]; qx[e] = ed.q[0]; qy[e] = ed.q[1]; });
  for (const [a, b] of t.pair) { const [e1, s1] = a.split(',').map(Number), [e2, s2] = b.split(',').map(Number); pair[2 * e1 + s1] = 2 * e2 + s2; }
  const sh = finishShape({ E, px, py, qx, qy, pair, loops: t.loops });
  if (sh.defs.length !== 2) throw new Error('tile is not hooks+crossover: defects ' + sh.defs.length);
  // tag: A = the defect at PTS[0] (tile vertex 0)
  const v0 = sh.defs.map((k) => vert(sh, k));
  const a = Math.hypot(v0[0][0] - PTS[0][0], v0[0][1] - PTS[0][1]) < 1e-6 ? 0 : 1;
  sh.defA = sh.defs[a]; sh.defB = sh.defs[1 - a];
  sh.marks = [{ pos: sh.defA, tag: 'A' }, { pos: sh.defB, tag: 'B' }];
  return sh;
}

// ------------------------------------------------------------------ exact composition + reduced data extraction
function compose(children, want) {
  const nC = children.length;
  const offs = new Int32Array(nC + 1);
  children.forEach((c, i) => { offs[i + 1] = offs[i] + c.shape.E; });
  const M = offs[nC];
  const PX = new Float64Array(M), PY = new Float64Array(M), QX = new Float64Array(M), QY = new Float64Array(M), owner = new Int32Array(M);
  children.forEach(({ shape, T }, c) => {
    const o = offs[c];
    for (let e = 0; e < shape.E; e++) { const g = o + e; owner[g] = c; PX[g] = T[0] * shape.px[e] + T[1] * shape.py[e] + T[2]; PY[g] = T[3] * shape.px[e] + T[4] * shape.py[e] + T[5]; QX[g] = T[0] * shape.qx[e] + T[1] * shape.qy[e] + T[2]; QY[g] = T[3] * shape.qx[e] + T[4] * shape.qy[e] + T[5]; }
  });
  const kpx = new Int32Array(M), kpy = new Int32Array(M), kqx = new Int32Array(M), kqy = new Int32Array(M);
  for (let g = 0; g < M; g++) { kpx[g] = Math.round(PX[g] * ROUND); kpy[g] = Math.round(PY[g] * ROUND); kqx[g] = Math.round(QX[g] * ROUND); kqy[g] = Math.round(QY[g] * ROUND); }
  let size = 1; while (size < 2 * M) size <<= 1;
  const hA = new Int32Array(size), hB = new Int32Array(size), hC = new Int32Array(size), hD = new Int32Array(size), hV = new Int32Array(size).fill(-1);
  const mate = new Int32Array(M).fill(-1), flip = new Uint8Array(M);
  const mix = (a, b, c, d) => { let h = Math.imul(a, 73856093) ^ Math.imul(b, 19349663) ^ Math.imul(c, 83492791) ^ Math.imul(d, 2654435761 | 0); h ^= h >>> 15; h = Math.imul(h, 0x2c1b3c6d); h ^= h >>> 12; return h & (size - 1); };
  for (let g = 0; g < M; g++) {
    let a = kpx[g], b = kpy[g], c = kqx[g], d = kqy[g], fl = 0;
    if (a > c || (a === c && b > d)) { const ta = a, tb = b; a = c; b = d; c = ta; d = tb; fl = 1; }
    let h = mix(a, b, c, d);
    for (;;) {
      const v = hV[h];
      if (v < 0) { hA[h] = a; hB[h] = b; hC[h] = c; hD[h] = d; hV[h] = g; flip[g] = fl; break; }
      if (hA[h] === a && hB[h] === b && hC[h] === c && hD[h] === d) { if (mate[v] >= 0) throw new Error('edge shared by three children'); mate[v] = g; mate[g] = v; const x = fl ^ flip[v]; flip[g] = x; flip[v] = x; break; }
      h = (h + 1) & (size - 1);
    }
  }
  let E = 0; const pidx = new Int32Array(M).fill(-1);
  for (let g = 0; g < M; g++) if (mate[g] < 0) pidx[g] = E++;
  const px = new Float64Array(E), py = new Float64Array(E), qx = new Float64Array(E), qy = new Float64Array(E), back = new Int32Array(E);
  for (let g = 0; g < M; g++) if (pidx[g] >= 0) { const k = pidx[g]; px[k] = PX[g]; py[k] = PY[g]; qx[k] = QX[g]; qy[k] = QY[g]; back[k] = g; }
  const pair = new Int32Array(2 * E).fill(-1), visited = new Uint8Array(2 * M);
  const childPair = (g, s) => { const c = owner[g], sh = children[c].shape, q = sh.pair[2 * (g - offs[c]) + s]; return [offs[c] + (q >> 1), q & 1]; };
  const cross = (g, s) => { const m = mate[g]; const sm = flip[g] ? 1 - s : s; return [m, 1 - sm]; };
  for (let k = 0; k < E; k++) for (let s = 0; s < 2; s++) {
    if (pair[2 * k + s] >= 0) continue;
    let g = back[k], ss = s, guard = 0;
    for (;;) { if (++guard > 4 * M + 10) throw new Error('walk does not terminate'); visited[2 * g + ss] = 1; const [g2, s2] = childPair(g, ss); visited[2 * g2 + s2] = 1; if (mate[g2] < 0) { const k2 = pidx[g2]; pair[2 * k + s] = 2 * k2 + s2; pair[2 * k2 + s2] = 2 * k + s; break; } [g, ss] = cross(g2, s2); }
  }
  let loops = 0;
  for (let g = 0; g < M; g++) for (let s = 0; s < 2; s++) { if (visited[2 * g + s] || mate[g] < 0) continue; loops++; let gg = g, ss = s; for (;;) { visited[2 * gg + ss] = 1; const [g2, s2] = childPair(gg, ss); visited[2 * g2 + s2] = 1; [gg, ss] = cross(g2, s2); if (visited[2 * gg + ss]) break; } }
  const parent = finishShape({ E, px, py, qx, qy, pair, loops });
  if (!want) return parent;

  // ---------------- reduced data
  // child cycles in the parent frame, ccw
  const kidCyc = children.map(({ shape, T }, c) => {
    const E0 = shape.E, cyc = new Int32Array(E0), fwd = new Uint8Array(E0);
    if (det(T) > 0) { for (let k = 0; k < E0; k++) { cyc[k] = shape.cyc[k]; fwd[k] = shape.fwd[k]; } }
    else { for (let k = 0; k < E0; k++) { cyc[k] = shape.cyc[E0 - 1 - k]; fwd[k] = 1 - shape.fwd[E0 - 1 - k]; } }
    return { cyc, fwd, E: E0 };
  });
  // own-cycle position -> parent-frame-cycle position
  const posMap = children.map(({ shape, T }, c) => { const E0 = shape.E; const m = new Int32Array(E0); if (det(T) > 0) { for (let k = 0; k < E0; k++) m[k] = k; } else { for (let k = 0; k < E0; k++) m[k] = (E0 - k) % E0; } return m; });
  // (vertex k of own cycle = start of own edge cyc[k]; in the reversed cycle, that vertex is the start of reversed position E0-k)
  const vkeyP = (g, side) => (side === 0 ? kpx[g] + ',' + kpy[g] : kqx[g] + ',' + kqy[g]);
  const startKey = (c, k) => { const g = offs[c] + kidCyc[c].cyc[k]; return vkeyP(g, kidCyc[c].fwd[k] ? 0 : 1); };
  const nbOf = (c, k) => { const g = offs[c] + kidCyc[c].cyc[k]; return mate[g] < 0 ? -1 : owner[mate[g]]; };
  // marks: vertices where some child's neighbour changes, or defect vertices of some child
  const markKeys = new Map();   // key -> mark id
  const addMark = (key) => { if (!markKeys.has(key)) markKeys.set(key, markKeys.size); return markKeys.get(key); };
  const markInfo = [];          // id -> { defOf: [[c, tag]], kids: Set }
  const ensure = (id) => { while (markInfo.length <= id) markInfo.push({ defOf: [], key: null }); return markInfo[id]; };
  children.forEach(({ shape }, c) => {
    const E0 = shape.E;
    for (let k = 0; k < E0; k++) { const j = (k + E0 - 1) % E0; if (nbOf(c, j) !== nbOf(c, k)) { const id = addMark(startKey(c, k)); ensure(id).key = startKey(c, k); } }
    shape.defs.forEach((pos, di) => { const tag = pos === shape.defA ? 'A' : pos === shape.defB ? 'B' : 'D' + di; const k = posMap[c][pos]; const id = addMark(startKey(c, k)); const mi = ensure(id); mi.key = startKey(c, k); mi.defOf.push([c, tag]); });
  });
  // runs per child
  const kids = children.map(({ shape }, c) => {
    const E0 = shape.E; const cy = kidCyc[c];
    const markPos = []; for (let k = 0; k < E0; k++) if (markKeys.has(startKey(c, k))) markPos.push(k);
    if (!markPos.length) throw new Error('child without marks');
    const runs = [];
    for (let i = 0; i < markPos.length; i++) {
      const a = markPos[i], b = markPos[(i + 1) % markPos.length];
      const len = ((b - a) + E0) % E0 || E0;
      const nb = nbOf(c, a); for (let k = 1; k < len; k++) if (nbOf(c, (a + k) % E0) !== nb) throw new Error('neighbour changes inside a run');
      runs.push({ a, b, len, nb, startMark: markKeys.get(startKey(c, a)), endMark: markKeys.get(startKey(c, b)), firstEdge: offs[c] + cy.cyc[a] });
    }
    const defA = shape.defA === undefined ? -1 : markPos.indexOf(posMap[c][shape.defA]), defB = shape.defB === undefined ? -1 : markPos.indexOf(posMap[c][shape.defB]);
    // this child's own rim marks (from its own level) located in the parent-level runs: [{tag, runIdx, offset} | {tag, markIdx}]
    const own = shape.marks.map((m) => { const k = posMap[c][m.pos]; const mi = markPos.indexOf(k); if (mi >= 0) return { tag: m.tag, markIdx: mi }; let r = 0; while (!(((k - markPos[r]) + E0) % E0 < runs[r].len)) r++; return { tag: m.tag, runIdx: r, offset: ((k - markPos[r]) + E0) % E0 }; });
    return { type: children[c].type, runs, markPos, markIds: markPos.map((k) => markKeys.get(startKey(c, k))), defA, defB, own, regular: shape.defs.length === 2, posMap: posMap[c], E: E0 };
  });
  // partner runs
  kids.forEach((kid, c) => kid.runs.forEach((r, i) => {
    if (r.nb < 0) { r.partner = null; return; }
    const g2 = mate[r.firstEdge]; const c2 = owner[g2]; const e2 = g2 - offs[c2];
    const k2 = kidCyc[c2].cyc.indexOf(e2);   // position of that edge in c2's cycle
    const j = kids[c2].runs.findIndex((r2) => ((k2 - r2.a) + kidCyc[c2].E) % kidCyc[c2].E < r2.len);
    const r2 = kids[c2].runs[j];
    if (r2.nb !== c || r2.len !== r.len || r2.startMark !== r.endMark || r2.endMark !== r.startMark) throw new Error('partner run mismatch');
    r.partner = [c2, j];
  }));
  // parent rim: sequence of (c, runIdx) ccw
  const rimRuns = []; kids.forEach((kid, c) => kid.runs.forEach((r, i) => { if (r.nb < 0) rimRuns.push([c, i]); }));
  const byStart = new Map(); for (const [c, i] of rimRuns) byStart.set(kids[c].runs[i].startMark, [c, i]);
  const rim = []; let cur = rimRuns[0]; for (let n = 0; n < rimRuns.length; n++) { rim.push(cur); cur = byStart.get(kids[cur[0]].runs[cur[1]].endMark); }
  if (rim.length !== rimRuns.length) throw new Error('rim runs do not chain');
  // parent's own marks (for the next level): rim mark vertices in parent cycle positions; also defects
  const parentKeyPos = new Map(); for (let k = 0; k < E; k++) { const e = parent.cyc[k]; parentKeyPos.set(parent.fwd[k] ? kpx[back[e]] + ',' + kpy[back[e]] : kqx[back[e]] + ',' + kqy[back[e]], k); }
  const pdef = parent.defs.map((k) => parentKeyPos.has ? k : k);
  const defKeys = parent.defs.map((k) => { const e = parent.cyc[k]; return parent.fwd[k] ? kpx[back[e]] + ',' + kpy[back[e]] : kqx[back[e]] + ',' + kqy[back[e]]; });
  const parentDefMarks = defKeys.map((key) => markKeys.has(key) ? markKeys.get(key) : -1);
  // which child's defect coincides with the parent's, and A/B tags inherited
  let defA = -1, defB = -1, inherit = null;
  parent.defs.forEach((k, idx) => { const id = parentDefMarks[idx]; if (id >= 0 && markInfo[id].defOf.length) { const [c, tag] = markInfo[id].defOf[0]; inherit = inherit || []; inherit.push([c, tag]); if (tag === 'A') defA = k; else defB = k; } });
  if (parent.defs.length === 2 && defA >= 0 && defB >= 0) { parent.defA = defA; parent.defB = defB; }
  else if (parent.defs.length === 2) { parent.defA = parent.defs[0]; parent.defB = parent.defs[1]; inherit = 'NOT INHERITED'; }
  else { parent.defA = undefined; parent.defB = undefined; inherit = 'IRREGULAR(' + parent.defs.length + ')'; }
  parent.marks = [];
  const defTag = (k) => k === parent.defA ? 'A' : k === parent.defB ? 'B' : 'D';
  for (const [id, key] of [...markKeys].map(([k, id]) => [id, k])) if (parentKeyPos.has(key)) { const pos = parentKeyPos.get(key); parent.marks.push({ pos, tag: parent.defs.includes(pos) ? defTag(pos) : 'J' }); }
  for (const k of parent.defs) if (!parent.marks.some((m) => m.pos === k)) parent.marks.push({ pos: k, tag: defTag(k) });
  parent.marks.sort((u, v) => u.pos - v.pos);
  parent.regular = parent.defs.length === 2 && kids.every((k) => k.regular);
  // child position (parent-frame cycle) -> parent cycle position, for rim vertices
  kids.forEach((kid, c) => { kid.toParent = new Int32Array(kid.E).fill(-1); });
  const cycInv = kidCyc.map((cy) => { const inv = new Int32Array(cy.E); for (let k = 0; k < cy.E; k++) inv[cy.cyc[k]] = k; return inv; });
  for (let K = 0; K < E; K++) { const g = back[parent.cyc[K]]; const c = owner[g]; const k = cycInv[c][g - offs[c]]; if (kidCyc[c].fwd[k] !== parent.fwd[K]) throw new Error('rim edge direction mismatch'); kids[c].toParent[k] = K; }
  parent.rd = { kids, rim, parentDefMarks, inherit, nMarks: markKeys.size, loops };
  return parent;
}

// ------------------------------------------------------------------ canonical encoding of reduced data
function encode(rd, withLen) {
  const { kids, rim } = rd;
  // rotate each child's runs to start at its defect A; name marks by their first (child, rotated index) occurrence
  const rot = kids.map((k) => k.defA);
  const ri = (c, i) => ((i - rot[c]) % kids[c].runs.length + kids[c].runs.length) % kids[c].runs.length;
  const name = new Map();
  kids.forEach((k, c) => k.markIds.forEach((id, i) => { const key = c + '.' + ri(c, i); if (!name.has(id) || key < name.get(id)) name.set(id, key); }));
  const parts = [];
  kids.forEach((k, c) => {
    const n = k.runs.length; const seq = [];
    for (let t = 0; t < n; t++) { const i = (rot[c] + t) % n; const r = k.runs[i]; seq.push(`${r.nb < 0 ? 'rim' : r.nb + '/' + ri(r.partner[0], r.partner[1])}:${r.len % 2}${withLen ? '(' + r.len + ')' : ''}>${name.get(r.endMark)}${k.markIds[(i + 1) % n] === k.markIds[k.defB] ? 'B' : ''}`); }
    parts.push(`${c}=${k.type}[${seq.join(' ')}]`);
  });
  // rim starting at the Gamma child's (last child) defect A if on the rim, else at the smallest name
  let start = 0; const rimNames = rim.map(([c, i]) => name.get(kids[c].runs[i].startMark));
  const gA = kids[kids.length - 1].markIds[kids[kids.length - 1].defA];
  const gi = rim.findIndex(([c, i]) => kids[c].runs[i].startMark === gA);
  if (gi >= 0) start = gi; else { let best = null; rimNames.forEach((nm, i) => { if (best === null || nm < rimNames[best]) best = i; }); start = best; }
  const rimSeq = []; for (let t = 0; t < rim.length; t++) { const [c, i] = rim[(start + t) % rim.length]; rimSeq.push(`${c}.${ri(c, i)}`); }
  parts.push('rim[' + rimSeq.join(' ') + ']');
  parts.push('def[' + rd.parentDefMarks.map((id) => name.get(id)).join(',') + ']');
  return parts.join(' ');
}
function encodeOwn(rd, c, kidsOnly) {   // two-level data: where child c's own (previous-level) rim marks sit in this level's runs
  const k = rd.kids[c]; const n = k.runs.length; const rot = k.defA; const ri = (i) => ((i - rot) % n + n) % n;
  const items = k.own.map((o) => o.markIdx !== undefined ? `${o.tag}@m${ri(o.markIdx)}` : `${o.tag}@r${ri(o.runIdx)}+${o.offset % 2}`);
  const a = items.findIndex((x) => x[0] === 'A'); return items.slice(a).concat(items.slice(0, a)).join(' ');
}

// ------------------------------------------------------------------ reduced composition (no geometry)
// ports: (c, markIdx, side) with side 0 = L (on the run before the mark), 1 = R (on the run after it)
function rcompose(rd, labelsIn) {
  const { kids, rim } = rd;
  const pid = (c, m, s) => (c * 4096 + m) * 2 + s;
  const tau = (c, m, s) => { const k = kids[c]; if (m === k.defA) return pid(c, k.defB, s); if (m === k.defB) return pid(c, k.defA, s); return pid(c, m, 1 - s); };
  const sigma = (c, m, s) => {   // port on an interior run -> its transfer partner; null if on a rim run
    const k = kids[c]; const n = k.runs.length;
    const i = s === 1 ? m : (m + n - 1) % n;   // run carrying the port: R(m) is on run m, L(m) on run m-1
    const r = k.runs[i]; if (r.nb < 0) return null;
    const [c2, j] = r.partner; const n2 = kids[c2].runs.length;
    if (r.len % 2 === 1) return s === 1 ? pid(c2, j, 1) : pid(c2, (j + 1) % n2, 0);      // odd: R(c,A)<->R(c',B), L(c,B)<->L(c',A)
    return s === 1 ? pid(c, (i + 1) % n, 0) : pid(c, i, 1);                                  // even: R(c,A)<->L(c,B)
  };
  const dec = (p) => [Math.floor(p / 8192), Math.floor(p / 2) % 4096, p % 2];
  // parent ports: rim runs' end ports
  const parentPorts = [];   // [{c, m, s, rimIdx, end}] ; parent rim marks in order: mark at start of rim run t
  rim.forEach(([c, i], t) => { const n = kids[c].runs.length; parentPorts.push({ p: pid(c, i, 1), t, side: 'R' }); parentPorts.push({ p: pid(c, (i + 1) % n, 0), t: (t + 1) % rim.length, side: 'L' }); });
  const isParent = new Map(parentPorts.map((q) => [q.p, q]));
  const uf = new Map(); const find = (x) => { while (uf.get(x) !== x) { uf.set(x, uf.get(uf.get(x))); x = uf.get(x); } return x; };
  const union = (a, b) => { a = find(a); b = find(b); if (a !== b) uf.set(a, b); };
  const labels = labelsIn || new Map();   // port -> [label]
  for (const ls of labels.values()) for (const l of ls) if (!uf.has(l)) uf.set(l, l);
  const visited = new Set(); const pairing = new Map(); const strandClass = new Map(); const lost = new Set();
  for (const q of parentPorts) {
    if (pairing.has(q.p)) continue;
    let p = q.p; let cls = null; let guard = 0;
    for (;;) {
      if (++guard > 1e6) throw new Error('reduced walk does not terminate');
      visited.add(p); for (const l of (labels.get(p) || [])) { cls = cls === null ? find(l) : (union(cls, l), find(cls)); }
      const [c, m, s] = dec(p); const p2 = tau(c, m, s); visited.add(p2); for (const l of (labels.get(p2) || [])) { cls = cls === null ? find(l) : (union(cls, l), find(cls)); }
      if (isParent.has(p2)) { pairing.set(q.p, p2); pairing.set(p2, q.p); strandClass.set(q.p, cls); strandClass.set(p2, cls); break; }
      const [c2, m2, s2] = dec(p2); p = sigma(c2, m2, s2); if (p === null) throw new Error('interior port expected');
    }
  }
  let loops = 0;
  kids.forEach((k, c) => k.runs.forEach((r, i) => { for (const s of [0, 1]) { const p = pid(c, i, s); if (visited.has(p) || isParent.has(p)) continue; loops++; let x = p; for (;;) { visited.add(x); for (const l of (labels.get(x) || [])) lost.add(find(l)); const [cc, mm, ss] = dec(x); const y = tau(cc, mm, ss); visited.add(y); for (const l of (labels.get(y) || [])) lost.add(find(l)); const [c2, m2, s2] = dec(y); x = sigma(c2, m2, s2); if (visited.has(x)) break; } } }));
  // classify parent rim marks: hook / other
  const nR = rim.length; const byMark = []; for (let t = 0; t < nR; t++) byMark.push({});
  for (const q of parentPorts) byMark[q.t][q.side] = q.p;
  const hooks = []; const nonHook = [];
  for (let t = 0; t < nR; t++) { const L = byMark[t].L, R = byMark[t].R; if (pairing.get(L) === R) hooks.push(t); else nonHook.push(t); }
  const pattern = nonHook.map((t) => { const L = byMark[t].L, R = byMark[t].R; const pl = parentPorts.find((q) => q.p === pairing.get(L)), pr = parentPorts.find((q) => q.p === pairing.get(R)); return `${t}:L->${pl.t}${pl.side},R->${pr.t}${pr.side}`; });
  return { loops, hooks: hooks.length, nonHook, pattern, byMark, pairing, strandClass, find, uf, lost, parentPorts };
}

// ------------------------------------------------------------------ main
function build(DIGITS, MAXL, quiet) {
const log = quiet ? () => {} : console.log;
const tile = fromTangle(H.tileTangle(DIGITS));
log(`design ${DIGITS}: tile rim ${tile.E} edges, defects at vertices ${tile.defs.join(',')} (A=${tile.defA}), loops ${tile.loops}`);
let shapes = {}; for (const t of NAMES) shapes[t] = tile;
const gamma = compose([{ shape: tile, T: IDENT, type: 'tile' }, { shape: tile, T: mul(ttrans(PTS[8][0], PTS[8][1]), trot(Math.PI / 6)), type: 'tile' }], true);
shapes.Gamma = gamma;
log(`Gamma (2 tiles): rim ${gamma.E}, non-hook rim vertices ${gamma.defs.length}, loops ${gamma.loops}`);
let quad = QUAD; const ENC = {}, OWN = {}, LEV = [];
const t0 = Date.now();
for (let N = 1; N <= MAXL; N++) {
  const { trs, superQuad } = levelTransforms(quad);
  const next = {}; const line = [];
  for (const t of NAMES) {
    const kids = []; SR[t].forEach((s, i) => { if (s) kids.push({ shape: shapes[s], T: trs[i], type: s }); });
    const sh = compose(kids, true);
    next[t] = sh;
    const exactOK = sh.defs.length === 2 && sh.loops === 0;
    const regularKids = sh.rd.kids.every((k) => k.regular);
    let same = null, rc = null, defT = null;
    if (regularKids) {
      rc = rcompose(sh.rd);
      const redOK = rc.loops === 0 && rc.nonHook.length === 2;
      defT = sh.rd.parentDefMarks.map((id) => sh.rd.rim.findIndex(([c, i]) => sh.rd.kids[c].runs[i].startMark === id));
      same = redOK && rc.nonHook.every((t2) => defT.includes(t2));
      ENC[t] = ENC[t] || []; ENC[t][N] = encode(sh.rd, false);
      OWN[t] = OWN[t] || []; OWN[t][N] = encodeOwn(sh.rd, 1);
    }
    line.push(`${t}:${sh.E}e/${sh.rd.nMarks}m ${exactOK ? 'ok' : 'EXACT-FAIL(' + sh.defs.length + ')'}/${same === null ? 'n/a' : same ? 'ok' : 'RED-FAIL'} inh=${JSON.stringify(sh.rd.inherit)}`);
    if (!exactOK || same === false) log('   detail', t, 'defs', sh.defs, 'loops', sh.loops, 'reduced', rc && rc.pattern, 'defT', defT);
  }
  log(`level ${N} (${Math.round((Date.now() - t0) / 1000)}s): ${line.join(' | ')}`);
  LEV.push({ shapes: next, trs });
  shapes = next; quad = superQuad;
}
return { LEV, ENC, OWN, tile, gamma };
}
function report(DIGITS, MAXL) {
const { LEV, ENC, OWN } = build(DIGITS, MAXL, false);
// level-independence of the reduced data
console.log('\nReduced data (skeleton, marks, run parities, partners, rim order, defect marks) compared across levels:');
for (const t of NAMES) {
  const s = [];
  for (let N = 2; N < MAXL; N++) s.push(`${N}=${N + 1}:${ENC[t][N] === ENC[t][N + 1] ? 'same' : 'DIFF'}`);
  for (let N = 2; N + 2 <= MAXL; N++) s.push(`${N}=${N + 2}:${ENC[t][N] === ENC[t][N + 2] ? 'same' : 'DIFF'}`);
  console.log(`  ${t.padEnd(6)} ${s.join(' ')}`);
}
console.log('\nTwo-level data for Delta child 1 (its own rim marks located in the runs of the next level):');
for (let N = 2; N < MAXL; N++) console.log(`  level ${N}: ${OWN.Delta[N]} ${N + 1 <= MAXL ? (OWN.Delta[N] === OWN.Delta[N + 1] ? '(= next)' : '(differs from next)') : ''} ${N + 2 <= MAXL ? (OWN.Delta[N] === OWN.Delta[N + 2] ? '(= N+2)' : '(differs from N+2)') : ''}`);
if (DUMP) { for (const t of NAMES) { console.log('\n' + t); for (let N = 1; N <= MAXL; N++) console.log(' L' + N + ': ' + ENC[t][N]); console.log(' own: ' + OWN[t].slice(1).join(' | ')); } }
}
module.exports = { build, rcompose, encode, encodeOwn };
if (require.main === module) report(DIGITS, MAXL);
