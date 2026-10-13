// Step 2: the combinatorics C_m of each composition level m -> m+1, in terms of the six sides of each child,
// and the side lengths l_m(s, j).  Vertices: observed (vertices_*.json) where available, else propagated with the
// rule (parent vertex J = child c's vertex j) learnt at the level of the same parity, and then checked.
// usage: node combin.js <maxLevel> <vertices json>
const MAXL = +(process.argv[2] || 6), VJ = process.argv[3];
const fs = require('fs');
const { NAMES, det, vert, tp, key, load, shapeAt, kidsOf } = require('./lib.js');
const D = load(MAXL);
const OBS = VJ ? JSON.parse(fs.readFileSync(VJ)) : {};
const VERT = {};   // VERT[m][s] = sorted rel positions (rel to defA, own ccw)
for (const m of Object.keys(OBS)) if (+m >= 1) { VERT[m] = {}; for (const s of NAMES) VERT[m][s] = OBS[m][s].pos; }
const RULE = {};   // RULE[parity][T] = [[c, j]] parent vertex J = child c's vertex j
const ST = {};
const C = {};      // C[m][T] = canonical combinatorics string
const LEN = {};    // LEN[m][s] = [six side lengths]
const DEF = {};    // DEF[m][s] = {side, off} position of A: side index containing A (from its start vertex), offset
const sideLens = (E, pos) => pos.map((p, j) => ((pos[(j + 1) % pos.length] - p) + E) % E || E);
function defOf(E, pos) { // A is at rel 0
  for (let j = 0; j < pos.length; j++) { const a = pos[j], l = ((pos[(j + 1) % pos.length] - a) + E) % E; const o = ((0 - a) + E) % E; if (o < l) return { side: j, off: o }; }
}
const log = [];
for (let m = 1; m < MAXL; m++) {
  if (!VERT[m]) throw new Error('no vertices at level ' + m);
  LEN[m] = {}; DEF[m] = {};
  for (const s of NAMES) { const sh = shapeAt(D, m, s); LEN[m][s] = sideLens(sh.E, VERT[m][s]); DEF[m][s] = defOf(sh.E, VERT[m][s]); }
  C[m] = {}; ST[m] = {};
  const propagate = !VERT[m + 1];
  if (propagate) VERT[m + 1] = {};
  for (const T of NAMES) {
    const kids = kidsOf(D, m + 1, T);
    // child vertex keys and side edge keys in parent frame
    const info = kids.map((k) => {
      const sh = shapeAt(D, m, k.kind), E = sh.E, pos = VERT[m][k.kind];
      const vk = []; for (let i = 0; i < E; i++) vk.push(key(tp(k.T, vert(sh, i))));
      const abs = pos.map((p) => (p + sh.defA) % E);   // own cycle index of vertex j
      return { sh, E, pos, abs, vk, d: det(k.T) > 0 ? 1 : -1 };
    });
    const edgeOwner = new Map();
    info.forEach((I, c) => { for (let i = 0; i < I.E; i++) { const a = I.vk[i], b = I.vk[(i + 1) % I.E]; const ek = a < b ? a + '|' + b : b + '|' + a; if (!edgeOwner.has(ek)) edgeOwner.set(ek, []); edgeOwner.get(ek).push([c, i]); } });
    const sideOfEdge = (c, i) => { const I = info[c]; for (let j = 0; j < 6; j++) { const l = ((I.abs[(j + 1) % 6] - I.abs[j]) + I.E) % I.E; if (((i - I.abs[j]) + I.E) % I.E < l) return j; } };
    // classify sides
    const sides = info.map((I, c) => {
      const out = [];
      for (let j = 0; j < 6; j++) {
        const l = ((I.abs[(j + 1) % 6] - I.abs[j]) + I.E) % I.E; let nb = null;
        for (let t = 0; t < l; t++) {
          const i = (I.abs[j] + t) % I.E, a = I.vk[i], b = I.vk[(i + 1) % I.E]; const lst = edgeOwner.get(a < b ? a + '|' + b : b + '|' + a);
          const o = lst.length === 1 ? 'R' : (() => { const [c2, i2] = lst[0][0] === c ? lst[1] : lst[0]; return c2 + '.' + sideOfEdge(c2, i2); })();
          if (nb === null) nb = o; else if (nb !== o) throw new Error(`level ${m} ${T} child ${c} side ${j}: neighbour changes inside a side (${nb} -> ${o})`);
        }
        out.push(nb);
      }
      return out;
    });
    // symmetric partner check
    sides.forEach((ss, c) => ss.forEach((o, j) => { if (o !== 'R') { const [c2, j2] = o.split('.').map(Number); if (sides[c2][j2] !== c + '.' + j) throw new Error('asymmetric partner'); } }));
    // junction check: every vertex where the neighbour changes is a child vertex (automatic if sides are uniform)
    // parent sides
    const P = shapeAt(D, m + 1, T), PE = P.E;
    const pkeys = []; for (let i = 0; i < PE; i++) pkeys.push(key(vert(P, i)));
    // child vertex lookup by key, among rim vertices
    const cvAt = new Map(); info.forEach((I, c) => I.abs.forEach((a, j) => { const k = I.vk[a]; if (!cvAt.has(k)) cvAt.set(k, []); cvAt.get(k).push([c, j]); }));
    let ppos = VERT[m + 1] && VERT[m + 1][T];
    let rule;
    if (propagate) {
      const R = RULE[(m + 1) % 2] && RULE[(m + 1) % 2][T]; if (!R) throw new Error('no rule to propagate');
      const want = R.map(([c, j]) => info[c].vk[info[c].abs[j]]);
      const idx = new Map(pkeys.map((k, i) => [k, i]));
      ppos = want.map((k) => { if (!idx.has(k)) throw new Error('propagated vertex not on parent rim'); return (idx.get(k) - P.defA + PE) % PE; });
      ppos.sort((a, b) => a - b);
      VERT[m + 1][T] = ppos;
    }
    const pabs = ppos.map((p) => (p + P.defA) % PE);
    rule = pabs.map((a) => { const l = cvAt.get(pkeys[a]) || []; const rimL = l.filter(([c, j]) => { const I = info[c]; const s0 = sides[c][(j + 5) % 6], s1 = sides[c][j]; return s0 === 'R' || s1 === 'R'; }); return rimL; });
    // parent side J: walk parent rim edges from pabs[J] to pabs[J+1], decompose into child sides
    const pside = [];
    for (let J = 0; J < 6; J++) {
      const a = pabs[J], l = ((pabs[(J + 1) % 6] - a) + PE) % PE; const seq = []; let cur = null, run = 0;
      for (let t = 0; t < l; t++) {
        const i = (a + t) % PE, ka = pkeys[i], kb = pkeys[(i + 1) % PE]; const lst = edgeOwner.get(ka < kb ? ka + '|' + kb : kb + '|' + ka);
        if (!lst || lst.length !== 1) throw new Error('parent rim edge not a single child edge');
        const [c, ci] = lst[0]; const j = sideOfEdge(c, ci); const tag = c + '.' + j;
        if (tag !== cur) { if (cur !== null) seq.push([cur, run]); cur = tag; run = 0; } run++;
      }
      seq.push([cur, run]);
      // each piece must be a whole child side
      for (const [tag, r] of seq) { const [c, j] = tag.split('.').map(Number); if (LEN[m][kids[c].kind][j] !== r) throw new Error(`level ${m + 1} ${T} side ${J}: partial child side ${tag} (${r} of ${LEN[m][kids[c].kind][j]})`); }
      pside.push(seq.map(([t]) => t));
    }
    // parent vertices as child vertices: the child vertex at the start of the first piece (in parent ccw order)
    const prule = pside.map((seq, J) => { const [c, j] = seq[0].split('.').map(Number); const I = info[c]; const jj = I.d > 0 ? j : (j + 1) % 6; if (I.vk[I.abs[jj]] !== pkeys[pabs[J]]) throw new Error('parent vertex is not the start of a child side'); return [c, jj]; });
    RULE[(m + 1) % 2] = RULE[(m + 1) % 2] || {}; if (!propagate || !RULE[(m + 1) % 2][T]) RULE[(m + 1) % 2][T] = prule;
    if (RULE[(m + 1) % 2][T] && JSON.stringify(RULE[(m + 1) % 2][T]) !== JSON.stringify(prule)) log.push(`rule differs at level ${m} for ${T}`);
    const gi = kids.length - 1, G = info[gi];
    const gA = G.vk[G.sh.defA], gB = G.vk[G.sh.defB];
    const ainh = pkeys[P.defA] === gA && pkeys[P.defB] === gB && kids[gi].kind === 'Gamma';
    const dirs = info.map((I) => (I.d > 0 ? '+' : '-')).join('');
    ST[m][T] = { kids: kids.map((k) => k.kind), sides, pside, pdef: defOf(PE, ppos), ainh };
    C[m][T] = `kids=${kids.map((k) => k.kind).join(',')} det=${dirs} sides=[${sides.map((s) => s.join(' ')).join(' | ')}] parent=[${pside.map((s) => s.join(' ')).join(' | ')}] Pdef=side${defOf(PE, ppos).side}${defOf(PE, ppos).off === 0 ? '@vertex' : '@interior'} AinhFromGamma=${ainh}`;
  }
}
// last level lengths
LEN[MAXL] = {}; DEF[MAXL] = {};
for (const s of NAMES) { const sh = shapeAt(D, MAXL, s); LEN[MAXL][s] = sideLens(sh.E, VERT[MAXL][s]); DEF[MAXL][s] = defOf(sh.E, VERT[MAXL][s]); }
for (const l of log) console.log(l);
console.log('Combinatorics compared across levels (m -> m+1):');
for (const T of NAMES) { const s = []; for (let m = 1; m + 1 < MAXL; m++) s.push(`${m}=${m + 1}:${C[m][T] === C[m + 1][T] ? 'same' : 'diff'}`); for (let m = 1; m + 2 < MAXL; m++) s.push(`${m}=${m + 2}:${C[m][T] === C[m + 2][T] ? 'same' : 'diff'}`); console.log('  ' + T.padEnd(7) + s.join(' ')); }
for (const m of [1, 2]) { console.log(`\nC_${m}:`); for (const T of NAMES) console.log(`  ${T}: ${C[m][T]}`); }
console.log('\nSide lengths l_m(s, j) and position of A (side, offset):');
for (let m = 1; m <= MAXL; m++) console.log(`  m=${m}: ` + NAMES.map((s) => `${s.slice(0, 3)}[${LEN[m][s].join(',')}]A${DEF[m][s].side}+${DEF[m][s].off}`).join(' '));
fs.writeFileSync(__dirname + `/combin_${MAXL}.json`, JSON.stringify({ C, ST, LEN, DEF, VERT, RULE }));
// compare propagated vertices with extra observations (a vertices json given as 4th argument)
if (process.argv[4]) {
  const X = JSON.parse(fs.readFileSync(process.argv[4]));
  for (const m of Object.keys(X)) if (+m >= 1 && VERT[m] && !OBS[m]) {
    const r = NAMES.map((s) => { const o = X[m][s].pos, p = VERT[m][s]; const sub = o.every((x) => p.includes(x)); return `${s}:${sub ? (o.length === 6 ? 'equal' : 'observed ' + o.length + ' all propagated') : 'MISMATCH'}`; });
    console.log(`level ${m} propagated vs observed (extra file): ${r.join(' ')}`);
  }
}
