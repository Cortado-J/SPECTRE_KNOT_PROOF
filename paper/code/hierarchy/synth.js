// Step 4: the small map S_{m+1}(T) as an explicit function F(C, v, d, beta) of
//   C    = the fixed combinatorics (combin json, structure ST),
//   v    = side lengths mod 2 (54 bits), d = Sigma's defect offset mod 2,
//   beta = +1 / -1: B = A + beta in the child's own order (counter-clockwise in the code's own frame, which is mirrored at odd levels).
// F builds a synthetic reduced-data object with PROXY lengths (6 + parity; offset 2 + parity), so only parities
// enter, and encodes it with reduce.js's own encode(). Compared with the real encodings from the directly composed geometry (floating point).
// usage: node synth.js combin_<L>.json <maxLevel for the real build>
const fs = require('fs');
const CJ = (require.main === module && process.argv[2]) || __dirname + '/combin_8.json', MAXL = +(process.argv[3] || 6);
const J = JSON.parse(fs.readFileSync(CJ));
const { R, NAMES, load } = require('./lib.js');
const ST = J.ST[1];

function F(T, v, d, beta, LENS, DELTA) {
  const st = ST[T]; const kinds = st.kids; const n = kinds.length;
  const len = kinds.map((s) => [0, 1, 2, 3, 4, 5].map((j) => (LENS ? LENS[s][j] : 6 + v[s][j])));
  const U = len.map((l) => { const u = [0]; for (let j = 0; j < 6; j++) u.push(u[j] + l[j]); return u; });   // U[c][6] = E
  const E = U.map((u) => u[6]);
  const nbr = st.sides.map((ss) => ss.map((x) => (x === 'R' ? null : x.split('.').map(Number))));
  // vertex identification
  const uf = new Map(); const f = (x) => { while (uf.get(x) !== x) x = uf.get(x); return x; }; const vk = (c, j) => c + ':' + (j % 6);
  for (let c = 0; c < n; c++) for (let j = 0; j < 6; j++) uf.set(vk(c, j), vk(c, j));
  const un = (a, b) => { a = f(a); b = f(b); if (a !== b) uf.set(a, b); };
  for (let c = 0; c < n; c++) for (let j = 0; j < 6; j++) { const p = nbr[c][j]; if (p) { un(vk(c, j), vk(p[0], p[1] + 1)); un(vk(c, j + 1), vk(p[0], p[1])); } }
  // point key of own position u on child c
  const sideAt = (c, u) => { for (let j = 0; j < 6; j++) if (u >= U[c][j] && u < U[c][j + 1]) return j; };
  const pkey = (c, u) => {
    u = ((u % E[c]) + E[c]) % E[c]; const j = sideAt(c, u), o = u - U[c][j];
    if (o === 0) return 'V' + f(vk(c, j));
    const p = nbr[c][j]; const a = `S${c}.${j}.${o}`; if (!p) return a;
    const b = `S${p[0]}.${p[1]}.${len[c][j] - o}`; return a < b ? a : b;
  };
  // defects
  const defU = kinds.map((s, c) => { const uA = s === 'Sigma' ? U[c][5] + (DELTA !== undefined ? DELTA : 2 + d) : 0; return [uA, ((uA + beta) % E[c] + E[c]) % E[c]]; });
  const markKeys = new Map(); const addMark = (k) => { if (!markKeys.has(k)) markKeys.set(k, markKeys.size); return markKeys.get(k); };
  const nbOfSide = (c, j) => (nbr[c][j] ? nbr[c][j][0] : -1);
  for (let c = 0; c < n; c++) for (let j = 0; j < 6; j++) if (nbOfSide(c, (j + 5) % 6) !== nbOfSide(c, j)) addMark(pkey(c, U[c][j]));
  for (let c = 0; c < n; c++) for (const u of defU[c]) addMark(pkey(c, u));
  // candidate positions on each child's rim that may carry marks: all vertices and all defect points mapped onto it
  const kids = [];
  for (let c = 0; c < n; c++) {
    const cand = new Set(); for (let j = 0; j < 6; j++) cand.add(U[c][j]);
    for (let c2 = 0; c2 < n; c2++) for (const u2 of defU[c2]) {   // defect of c2 located on c's rim?
      if (c2 === c) { cand.add(u2); continue; }
      const j2 = sideAt(c2, u2), o2 = u2 - U[c2][j2];
      if (o2 === 0) continue;   // a vertex: already a candidate if shared
      const p = nbr[c2][j2]; if (p && p[0] === c) cand.add(U[c][p[1]] + len[c2][j2] - o2);
    }
    const P = (u) => (E[c] - u) % E[c];   // parent-frame position (child is reflected)
    const marks = [...cand].filter((u) => markKeys.has(pkey(c, u))).sort((a, b) => P(a) - P(b));
    const runs = [];
    for (let i = 0; i < marks.length; i++) {
      const a = marks[i], b = marks[(i + 1) % marks.length]; const L = ((P(b) - P(a)) + E[c]) % E[c] || E[c];
      const j = sideAt(c, (b + 0) % E[c]);   // own edge [b, b+1] lies in the run (own direction b -> a)
      runs.push({ a: P(a), len: L, nb: nbOfSide(c, j), side: j, uFirst: (a - 1 + E[c]) % E[c], startMark: markKeys.get(pkey(c, a)), endMark: markKeys.get(pkey(c, b)) });
    }
    const markIds = marks.map((u) => markKeys.get(pkey(c, u)));
    kids.push({ type: kinds[c], runs, markIds, defA: marks.indexOf(defU[c][0]), defB: marks.indexOf(defU[c][1]), regular: true, marksU: marks });
  }
  // partners
  kids.forEach((k, c) => k.runs.forEach((r) => {
    if (r.nb < 0) { r.partner = null; return; }
    const j = r.side, o = r.uFirst - U[c][j]; const [c2, j2] = nbr[c][j]; const e2 = U[c2][j2] + len[c][j] - 1 - o;   // mate edge [e2, e2+1] in c2
    const k2 = kids[c2]; const i2 = k2.runs.findIndex((r2) => { const ua = k2.marksU[k2.runs.indexOf(r2)]; return ((ua - 1 - e2) % E[c2] + E[c2]) % E[c2] < r2.len; });
    const r2 = k2.runs[i2]; if (r2.nb !== c || r2.len % 2 !== r.len % 2 || r2.startMark !== r.endMark || r2.endMark !== r.startMark) throw new Error('synthetic partner mismatch ' + T);
    r.partner = [c2, i2];
  }));
  const rimRuns = []; kids.forEach((k, c) => k.runs.forEach((r, i) => { if (r.nb < 0) rimRuns.push([c, i]); }));
  const byStart = new Map(); for (const [c, i] of rimRuns) byStart.set(kids[c].runs[i].startMark, [c, i]);
  const rim = []; let cur = rimRuns[0]; for (let t = 0; t < rimRuns.length; t++) { rim.push(cur); cur = byStart.get(kids[cur[0]].runs[cur[1]].endMark); }
  const g = n - 1; const parentDefMarks = [kids[g].markIds[kids[g].defA], kids[g].markIds[kids[g].defB]];
  return { kids, rim, parentDefMarks, nMarks: markKeys.size };
}
if (require.main === module) {
const canon = (s) => s.replace(/def\[([^\]]*)\]/, (_, x) => 'def[' + x.split(',').sort().join(',') + ']');
const t0 = Date.now();
const D = load(MAXL);
console.log(`real build to level ${MAXL}: ${((Date.now() - t0) / 1000).toFixed(0)} s`);
const vOf = (m) => { const v = {}; for (const s of NAMES) v[s] = J.LEN[m][s].map((x) => x % 2); return v; };
const v1 = vOf(1), d1 = J.DEF[1].Sigma.off % 2;
let allOK = true;
for (let N = 2; N <= MAXL; N++) {
  const m = N - 1, beta = m % 2 === 1 ? -1 : 1;
  const res = [];
  for (const T of NAMES) {
    const syn = canon(R.encode(F(T, v1, d1, beta), false)); const real = canon(D.ENC[T][N]);
    res.push(`${T}:${syn === real ? 'ok' : 'DIFF'}`); if (syn !== real) { allOK = false; if (process.argv[4] === 'v') console.log('SYN ' + syn + '\nREAL ' + real); }
  }
  console.log(`S_${N} = F(C, v_1, d_1, beta=${beta > 0 ? '+1' : '-1'}): ${res.join(' ')}`);
}
// the real B orientation and parities at each level, for the record
for (let m = 1; m < MAXL; m++) { const sh = D.LEV[m - 1].shapes.Delta; console.log(`level ${m}: B - A = ${(sh.defB - sh.defA + sh.E) % sh.E === 1 ? '+1' : '-1'} (own ccw); Sigma offset parity ${J.DEF[m] ? J.DEF[m].Sigma.off % 2 : '?'}`); }
console.log(allOK ? 'ALL MATCH' : 'MISMATCH');
fs.writeFileSync(__dirname + '/F_' + MAXL + '.json', JSON.stringify({ odd: Object.fromEntries(NAMES.map((T) => [T, canon(R.encode(F(T, v1, d1, -1), false))])), even: Object.fromEntries(NAMES.map((T) => [T, canon(R.encode(F(T, v1, d1, 1), false))])) }));
}
module.exports = { F, ST };
