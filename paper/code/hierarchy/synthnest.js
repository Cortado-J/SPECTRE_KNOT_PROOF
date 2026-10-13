// Step 6 (L8): the label input of core/nest.js, rebuilt from (C, v, Sigma offset parity, beta) alone.
//
// EXACT: runNestExact(b) is core/nest.js's runNest, copied line for line (same placement rules, same union-find,
//   same trace strings), plus an ORDER-FREE canonical dump of what it hands to rcompose at every relative level:
//     ports  : every labelled port as child.(mark index rotated to the child's own A).(side), with the labels on it,
//              each label named by the lexicographically least original label of its current class;
//     part   : the partition of all labels created so far, after this level's merging;
//     carry  : number of carried hooks / carried intervals, lost labels, loops.
// SYNTH: runNestSynth(beta_b) does the same from the combinatorics C (combin_8.json, through synth.js's F), the
//   parity vector v (M.json, combin_8.json) and beta_b only. Lengths are PROXIES:
//     P_0 at the base level ('uB:D': B + v with Sigma offset D; 'l1+2l3' etc.: combinations of l_m = M^(m-1) l_1, which
//     are genuine side-length vectors), P_{k+1} = M P_k, delta_k = P_{k-1}(Xi,2) + P_{k-1}(Xi,1) + P_{k-1}(Gamma,0)
//     above the base, beta_{b+k} = beta_b (-1)^k. None of this depends on b except through beta_b.
//   Positions are own-frame rim coordinates u (u = 0 at the supertile's A, ccw), so nothing absolute is used.
// The two canonical dumps are compared for every base and relative level; the synthetic run is repeated for several
// proxy choices to show that nothing but parities (and the fixed cyclic order) enters. certnest.js + certify.py then
// remove the proxies: they certify every length-dependent decision for all real lengths and every b >= 2.
// usage: node synthnest.js <maxLevel> <bases, e.g. 1,2,3,4,5,6> [proxy specs, e.g. u8:4,l1,l1+2l2] [v]
const fs = require('fs');
const MAXL = +(process.argv[2] || 7), BASES = (process.argv[3] || '1,2,3,4').split(',').map(Number);
const SPECS = (process.argv[4] || 'u8:4,u10:6,u100:10,l1,l2,l3,l1+2l2,3l1+2l3,l1+l2+l4').split(',');
const VERB = process.argv[5] === 'v';
const { F, ST } = require('./synth.js');
const { R, NAMES, load } = require('./lib.js');
const { rcompose } = R;
const J = JSON.parse(fs.readFileSync(__dirname + '/combin_8.json'));
const { M } = JSON.parse(fs.readFileSync(__dirname + '/M.json'));
const det = (T) => T[0] * T[4] - T[1] * T[3];
const v = {}; for (const s of NAMES) v[s] = J.LEN[1][s].map((x) => x % 2);
if (J.DEF[1].Sigma.off % 2 !== 0) throw new Error('Sigma offset parity at level 1 is odd');

// ---------------------------------------------------------------- canonical, order-free dump of one level
function canonLevel(labels, kids, ufFind, allLabels) {
  // class name = least original label in the class
  const least = new Map(); for (const l of allLabels) { const r = ufFind(l); if (!least.has(r) || l < least.get(r)) least.set(r, l); }
  const nm = (l) => least.get(ufFind(l));
  const ent = [];
  for (const [p, ls] of labels) {
    const c = Math.floor(p / 8192), m = Math.floor(p / 2) % 4096, s = p % 2; const n = kids[c].runs.length;
    ent.push(`${c}.${((m - kids[c].defA) % n + n) % n}.${s}=${ls.map(nm).sort().join(',')}`);
  }
  return ent.sort().join(' ');
}
function partition(allLabels, ufFind) {
  const cl = new Map(); for (const l of allLabels) { const r = ufFind(l); if (!cl.has(r)) cl.set(r, []); cl.get(r).push(l); }
  return [...cl.values()].map((x) => x.sort().join(',')).sort().join(' | ');
}

// ---------------------------------------------------------------- EXACT (verbatim logic of core/nest.js)
let LEV = null;
function runNestExact(b) {
  const trace = [], canon = [];
  const uf = new Map(); const find = (x) => { while (uf.get(x) !== x) { uf.set(x, uf.get(uf.get(x))); x = uf.get(x); } return x; };
  const add = (x) => { uf.set(x, x); return x; };
  const base = LEV[b - 1].shapes.Delta;
  const after = (base.defB - base.defA + base.E) % base.E === 1;
  const interval = after ? [(base.defB + 1) % base.E, (base.defA - 1 + base.E) % base.E] : [(base.defA + 1) % base.E, (base.defB - 1 + base.E) % base.E];
  let state = { E: base.E, hooks: new Map(), intervals: [interval], cross: [add('c0'), add('c1')], defA: base.defA, defB: base.defB };
  const lost = new Set(); const results = [];
  for (let m = b; m < MAXL; m++) {
    const parent = LEV[m].shapes.Delta; const rd = parent.rd; const kid = rd.kids[1];
    const n = kid.runs.length; const rot = kid.defA; const ri = (i) => ((i - rot) % n + n) % n;
    const pid = (c, mm, s) => (c * 4096 + mm) * 2 + s;
    const labels = new Map(); const put = (p, l) => { if (!labels.has(p)) labels.set(p, []); labels.get(p).push(l); };
    const enc = [];
    const lvl = 'L' + (m + 1 - b);
    const locate = (k) => { const mi = kid.markPos.indexOf(k); if (mi >= 0) return { mark: mi }; let r = 0; while (!(((k - kid.markPos[r]) + kid.E) % kid.E < kid.runs[r].len)) r++; return { run: r, off: ((k - kid.markPos[r]) + kid.E) % kid.E }; };
    const carriedHooks = new Map(); const carriedIntervals = [];
    const hookList = [...state.hooks].sort((u, w) => u[0] - w[0]);
    for (const [pos, lab] of hookList) {
      const k = kid.posMap[pos]; const loc = locate(k);
      if (loc.mark !== undefined) { put(pid(1, loc.mark, 1), lab); enc.push(`${lab}@m${ri(loc.mark)}`); continue; }
      const r = kid.runs[loc.run];
      if (r.nb < 0) { carriedHooks.set(kid.toParent[k], lab); enc.push(`${lab}@rim`); continue; }
      if (loc.off % 2 === 0) put(pid(1, loc.run, 1), lab);
      else if (r.len % 2 === 0) put(pid(r.partner[0], r.partner[1], 1), lab);
      else put(pid(1, (loc.run + 1) % n, 0), lab);
      enc.push(`${lab}@r${ri(loc.run)}+${loc.off % 2}`);
    }
    if (state.intervals.length > 1) throw new Error('more than one carried interval (exact)');
    state.intervals.forEach(([s0, s1], ii) => {
      const len = ((s1 - s0) + state.E) % state.E + 1;
      const pieces = new Map();
      let carry = null; const carried = [];
      for (let t = 0; t < len; t++) {
        const pos = (s0 + t) % state.E; const k = kid.posMap[pos]; const loc = locate(k);
        if (loc.mark !== undefined) { const lab = add(`${lvl}I${ii}@m${ri(loc.mark)}`); put(pid(1, loc.mark, 1), lab); enc.push(`I${ii}@m${ri(loc.mark)}`); if (carry) { carried.push(carry); carry = null; } continue; }
        const r = kid.runs[loc.run];
        if (r.nb < 0) { const K = kid.toParent[k]; if (K < 0) throw new Error('rim vertex without parent position'); if (carry && (carry[1] + 1) % parent.E === K) carry[1] = K; else if (carry && (carry[0] + parent.E - 1) % parent.E === K) carry[0] = K; else { if (carry) carried.push(carry); carry = [K, K]; } continue; }
        if (carry) { carried.push(carry); carry = null; }
        if (!pieces.has(loc.run)) pieces.set(loc.run, { even: 0, odd: 0 });
        pieces.get(loc.run)[loc.off % 2 === 0 ? 'even' : 'odd']++;
      }
      if (carry) carried.push(carry);
      for (const [rIdx, pc] of [...pieces].sort((u, w) => u[0] - w[0])) {
        if (pc.even) { const lab = add(`${lvl}I${ii}r${ri(rIdx)}e`); put(pid(1, rIdx, 1), lab); }
        if (pc.odd) { const lab = add(`${lvl}I${ii}r${ri(rIdx)}o`); const rr = kid.runs[rIdx]; if (rr.len % 2 === 0) put(pid(rr.partner[0], rr.partner[1], 1), lab); else put(pid(1, (rIdx + 1) % n, 0), lab); }
        enc.push(`I${ii}@r${ri(rIdx)}(${pc.even ? 'e' : ''}${pc.odd ? 'o' : ''})`);
      }
      for (const cpiece of carried) carriedIntervals.push(cpiece);
      if (carried.length) enc.push(`I${ii}@rim×${carried.length}`);
    });
    const sw = det(LEV[m].trs[1]) < 0 ? 1 : 0;
    if (sw !== 1) throw new Error('child 1 not placed by a reflection at level ' + (m + 1));
    if (state.cross[0] !== null) { put(pid(1, kid.defA, 1 - sw), state.cross[0]); enc.push(`${state.cross[0]}@XR`); }
    if (state.cross[1] !== null) { put(pid(1, kid.defA, sw), state.cross[1]); enc.push(`${state.cross[1]}@XL`); }
    const portsCanon = canonLevel(labels, rd.kids, find, [...uf.keys()]);
    const rc = rcompose(rd, labels);
    for (const l of rc.lost) lost.add(find(l));
    for (const [l] of rc.uf) { const r = rc.find(l); if (r !== l) { const a = find(l), c2 = find(r); if (a !== c2) uf.set(a, c2); } }
    const newHooks = new Map(carriedHooks);
    const rimStartPos = rd.rim.map(([c, i]) => rd.kids[c].toParent[rd.kids[c].runs[i].a]);
    const nR = rd.rim.length; let cross = [null, null];
    for (let t = 0; t < nR; t++) {
      const L = rc.byMark[t].L, Rr = rc.byMark[t].R; const K = rimStartPos[t];
      if (rc.pairing.get(L) === Rr) { const cls = rc.strandClass.get(Rr); if (cls !== null && cls !== undefined) newHooks.set(K, find(cls)); }
      else if (K === parent.defA) { const clsR = rc.strandClass.get(Rr), clsL = rc.strandClass.get(L); cross = [clsR === null || clsR === undefined ? null : find(clsR), clsL === null || clsL === undefined ? null : find(clsL)]; }
    }
    for (const [K, lab] of carriedHooks) newHooks.set(K, find(lab));
    state = { E: parent.E, hooks: newHooks, intervals: carriedIntervals, cross, defA: parent.defA, defB: parent.defB };
    const roots = new Set(); for (const l of uf.keys()) roots.add(find(l));
    results.push({ level: m + 1, classes: roots.size, lost: lost.size, loops: rc.loops, hooksCarried: carriedHooks.size, intervalsCarried: carriedIntervals.length, labelled: newHooks.size });
    trace.push(`${lvl}: ${enc.join(' ')}`);
    canon.push(`ports{${portsCanon}} part{${partition([...uf.keys()], find)}} carry{${carriedHooks.size}h/${carriedIntervals.length}i lost${lost.size} loops${rc.loops} cross${cross.map((x) => (x === null ? '-' : 'y')).join('')} labelledRim${newHooks.size}}`);
  }
  return { results, trace, canon };
}

// ---------------------------------------------------------------- SYNTHETIC: from (C, v, d, beta_b) only
const flat = (p) => NAMES.flatMap((s) => p[s]);
const unflat = (a) => { const p = {}; NAMES.forEach((s, i) => { p[s] = a.slice(6 * i, 6 * i + 6); }); return p; };
const Mul = (p) => unflat(M.map((r) => r.reduce((a, x, i) => a + x * flat(p)[i], 0)));
const sum = (a) => a.reduce((x, y) => x + y, 0);
const STD = ST.Delta;

// Proxy specs (all depend on C and l_1 only, never on the base b):
//   'uB:D'      P_0 = B + v (B even), Sigma offset D (even) at the base level;
//   'l1+2l3' .. P_0 = sum c_m l_m with l_m = M^(m-1) l_1 (l_1 = the level-1 side lengths, from combin_8.json) and
//               Sigma offset sum c_m delta_m (delta_1 = 6, delta_m = l_(m-1)(Xi,2) + l_(m-1)(Xi,1) + l_(m-1)(Gamma,0));
//               sum c_m must be odd so that P_0 = v mod 2. These are genuine side-length vectors (matched sides equal).
const LR = [null, {}]; for (const s of NAMES) LR[1][s] = J.LEN[1][s].slice();
for (let m = 2; m <= 12; m++) LR.push(Mul(LR[m - 1]));
const deltaR = (m) => (m === 1 ? J.DEF[1].Sigma.off : LR[m - 1].Xi[2] + LR[m - 1].Xi[1] + LR[m - 1].Gamma[0]);
function proxy(spec) {
  const P0 = {};
  if (spec[0] === 'u') { const [B, D] = spec.slice(1).split(':').map(Number); if (B % 2 || D % 2) throw new Error('uniform proxy base and offset must be even'); for (const s of NAMES) P0[s] = v[s].map((x) => B + x); return { P0, d0: D }; }
  const terms = spec.split('+').map((t) => { const m = /^(\d*)l(\d+)$/.exec(t); if (!m) throw new Error('bad proxy spec ' + spec); return [m[1] === '' ? 1 : +m[1], +m[2]]; });
  if (terms.reduce((a, [c]) => a + c, 0) % 2 !== 1) throw new Error('coefficients must sum to an odd number');
  for (const s of NAMES) P0[s] = [0, 1, 2, 3, 4, 5].map((j) => terms.reduce((a, [c, m]) => a + c * LR[m][s][j], 0));
  return { P0, d0: terms.reduce((a, [c, m]) => a + c * deltaR(m), 0) };
}
function runNestSynth(betaB, K, spec, diag) {
  const { P0, d0 } = proxy(spec); const P = [P0];
  for (const s of NAMES) for (let j = 0; j < 6; j++) if (P0[s][j] % 2 !== v[s][j]) throw new Error('proxy parity');
  if (d0 % 2 !== 0) throw new Error('Sigma offset proxy must be even');
  // proxies must realise the fixed cyclic order (P4): Sigma's A strictly inside side 5 with room for B on either side
  if (!(d0 >= 4 && P[0].Sigma[5] - d0 >= 4)) return null;
  for (let k = 0; k < K; k++) P.push(Mul(P[k]));
  const delta = (k) => (k === 0 ? d0 : P[k - 1].Xi[2] + P[k - 1].Xi[1] + P[k - 1].Gamma[0]);
  const uf = new Map(); const find = (x) => { while (uf.get(x) !== x) { uf.set(x, uf.get(uf.get(x))); x = uf.get(x); } return x; };
  const add = (x) => { uf.set(x, x); return x; };
  const E0 = sum(P[0].Delta); const B0 = ((betaB % E0) + E0) % E0;
  // base interval: every rim vertex of N_b except A (u = 0) and B (u = beta_b), as a ccw range
  let state = { E: E0, hooks: new Map(), intervals: [betaB > 0 ? [2, E0 - 1] : [1, E0 - 2]], cross: [add('c0'), add('c1')] };
  if (B0 !== (betaB > 0 ? 1 : E0 - 1)) throw new Error('B placement');
  const lost = new Set(); const results = [], canon = [];
  for (let k = 0; k < K; k++) {
    const betaK = k % 2 === 0 ? betaB : -betaB;
    const rd = F('Delta', null, 0, betaK, P[k], delta(k));
    const kids = STD.kids;
    // child own lengths, cumulative vertices, parent pieces (pside): child (c, j) own offset o from its vertex j <-> parent u1 - o
    const len = kids.map((s) => P[k][s]); const U = len.map((l) => { const u = [0]; for (let j = 0; j < 6; j++) u.push(u[j] + l[j]); return u; });
    const Ec = U.map((u) => u[6]); const EP = sum(P[k + 1].Delta);
    const piece = new Map(); { let u = 0; for (let Jx = 0; Jx < 6; Jx++) for (const tag of STD.pside[Jx]) { const [c, j] = tag.split('.').map(Number); piece.set(c + '.' + j, u + len[c][j]); u += len[c][j]; } if (u !== EP) throw new Error('parent rim length'); }
    const sideAt = (c, u) => { for (let j = 0; j < 6; j++) if (u >= U[c][j] && u < U[c][j + 1]) return j; };
    // parent own coordinate of child c's own rim position u, using the own edge [u-1, u] (which lies on a rim side)
    const toParentU = (c, u) => { const j = sideAt(c, (u - 1 + Ec[c]) % Ec[c]); let o = u - U[c][j]; if (o <= 0) o += Ec[c]; const u1 = piece.get(c + '.' + j); if (u1 === undefined) throw new Error('not a rim side'); return ((u1 - o) % EP + EP) % EP; };
    const kid = rd.kids[1]; const E = Ec[1]; if (E !== state.E) throw new Error('own rim length mismatch');
    const n = kid.runs.length;
    const Pf = (u) => (E - u) % E;   // parent-frame order (child 1 is reflected)
    const pid = (c, mm, s) => (c * 4096 + mm) * 2 + s;
    const labels = new Map(); const put = (p, l) => { if (!labels.has(p)) labels.set(p, []); labels.get(p).push(l); };
    const ri = (i) => ((i - kid.defA) % n + n) % n;
    const lvl = 'L' + (k + 1);
    const locate = (u) => { const mi = kid.marksU.indexOf(u); if (mi >= 0) return { mark: mi }; let r = 0; while (!(((Pf(u) - kid.runs[r].a) + E) % E < kid.runs[r].len)) r++; return { run: r, off: ((Pf(u) - kid.runs[r].a) + E) % E }; };
    const carriedHooks = new Map(); const carriedIntervals = [];
    for (const [u, lab] of state.hooks) {
      const loc = locate(u);
      if (loc.mark !== undefined) { put(pid(1, loc.mark, 1), lab); continue; }
      const r = kid.runs[loc.run];
      if (r.nb < 0) { carriedHooks.set(toParentU(1, u), lab); continue; }
      if (loc.off % 2 === 0) put(pid(1, loc.run, 1), lab);
      else if (r.len % 2 === 0) put(pid(r.partner[0], r.partner[1], 1), lab);
      else put(pid(1, (loc.run + 1) % n, 0), lab);
    }
    if (state.intervals.length > 1) throw new Error('more than one carried interval (synth)');
    state.intervals.forEach(([s0, s1], ii) => {
      const L = ((s1 - s0) + E) % E + 1;
      const pieces = new Map(); let carry = null; const carried = [];
      for (let t = 0; t < L; t++) {
        const u = (s0 + t) % E; const loc = locate(u);
        if (loc.mark !== undefined) { put(pid(1, loc.mark, 1), add(`${lvl}I${ii}@m${ri(loc.mark)}`)); if (carry) { carried.push(carry); carry = null; } continue; }
        const r = kid.runs[loc.run];
        if (r.nb < 0) { const Kp = toParentU(1, u); if (carry && (carry[1] + 1) % EP === Kp) carry[1] = Kp; else if (carry && (carry[0] + EP - 1) % EP === Kp) carry[0] = Kp; else { if (carry) carried.push(carry); carry = [Kp, Kp]; } continue; }
        if (carry) { carried.push(carry); carry = null; }
        if (!pieces.has(loc.run)) pieces.set(loc.run, { even: 0, odd: 0 });
        pieces.get(loc.run)[loc.off % 2 === 0 ? 'even' : 'odd']++;
      }
      if (carry) carried.push(carry);
      for (const [rIdx, pc] of pieces) {
        if (diag) diag.minPiece = Math.min(diag.minPiece, pc.even + pc.odd);
        if (pc.even) put(pid(1, rIdx, 1), add(`${lvl}I${ii}r${ri(rIdx)}e`));
        if (pc.odd) { const lab = add(`${lvl}I${ii}r${ri(rIdx)}o`); const rr = kid.runs[rIdx]; if (rr.len % 2 === 0) put(pid(rr.partner[0], rr.partner[1], 1), lab); else put(pid(1, (rIdx + 1) % n, 0), lab); }
      }
      for (const cp of carried) carriedIntervals.push(cp);
    });
    // crossover: child 1 is placed by a reflection at every level (C), so its own R(A) is L(A) in the parent frame
    if (state.cross[0] !== null) put(pid(1, kid.defA, 0), state.cross[0]);
    if (state.cross[1] !== null) put(pid(1, kid.defA, 1), state.cross[1]);
    const portsCanon = canonLevel(labels, rd.kids, find, [...uf.keys()]);
    const rc = rcompose(rd, labels);
    for (const l of rc.lost) lost.add(find(l));
    for (const [l] of rc.uf) { const r = rc.find(l); if (r !== l) { const a = find(l), c2 = find(r); if (a !== c2) uf.set(a, c2); } }
    const newHooks = new Map(carriedHooks);
    const rimStartU = rd.rim.map(([c, i]) => toParentU(c, rd.kids[c].marksU[i]));
    let cross = [null, null];
    for (let t = 0; t < rd.rim.length; t++) {
      const Lp = rc.byMark[t].L, Rp = rc.byMark[t].R; const Kp = rimStartU[t];
      if (rc.pairing.get(Lp) === Rp) { const cls = rc.strandClass.get(Rp); if (cls !== null && cls !== undefined) newHooks.set(Kp, find(cls)); }
      else if (Kp === 0) { const a = rc.strandClass.get(Rp), c2 = rc.strandClass.get(Lp); cross = [a == null ? null : find(a), c2 == null ? null : find(c2)]; }
    }
    for (const [Kp, lab] of carriedHooks) newHooks.set(Kp, find(lab));
    if (diag) for (const [s0, s1] of carriedIntervals) diag.carriedLen.push(((s1 - s0) + EP) % EP + 1);
    state = { E: EP, hooks: newHooks, intervals: carriedIntervals, cross };
    const roots = new Set(); for (const l of uf.keys()) roots.add(find(l));
    results.push({ rel: k + 1, classes: roots.size, lost: lost.size, loops: rc.loops, hooksCarried: carriedHooks.size, intervalsCarried: carriedIntervals.length });
    canon.push(`ports{${portsCanon}} part{${partition([...uf.keys()], find)}} carry{${carriedHooks.size}h/${carriedIntervals.length}i lost${lost.size} loops${rc.loops} cross${cross.map((x) => (x === null ? '-' : 'y')).join('')} labelledRim${newHooks.size}}`);
  }
  return { results, canon };
}

module.exports = { runNestSynth };
if (require.main === module) {
  const t0 = Date.now();
  const D = load(MAXL); LEV = D.LEV;
  console.log(`real build to level ${MAXL}: ${((Date.now() - t0) / 1000).toFixed(0)} s`);
  // real beta_b: B - A in N_b's own ccw order
  const realBeta = (b) => { const sh = LEV[b - 1].shapes.Delta; return (sh.defB - sh.defA + sh.E) % sh.E === 1 ? 1 : -1; };
  let all = true; const synthCache = new Map(); const exactOut = {};
  const Kmax = MAXL - Math.min(...BASES);
  // synthetic runs: both betas, every proxy choice; they must agree with each other
  for (const beta of [1, -1]) {
    let ref = null;
    for (const spec of SPECS) {
      const diag = { minPiece: Infinity, carriedLen: [] };
      const s = runNestSynth(beta, Kmax, spec, diag);
      if (!s) { console.log(`synth proxy ${spec}: skipped (violates the P4 order constraint)`); continue; }
      const tag = `beta=${beta > 0 ? '+1' : '-1'} proxy ${spec} (Delta sides ${proxy(spec).P0.Delta.join(',')}, Sigma offset ${proxy(spec).d0})`;
      if (!ref) { ref = s; synthCache.set(beta, s); }
      const same = s.canon.every((x, i) => x === ref.canon[i]);
      if (!same) all = false;
      console.log(`synth ${tag}: ${same ? 'same as first proxy' : 'DIFFERS from first proxy'}; min interval piece ${diag.minPiece} vertices; carried interval lengths ${diag.carriedLen.join(',')}; classes ${s.results.map((r) => r.classes + (r.hooksCarried || r.intervalsCarried ? `(c${r.hooksCarried}h/${r.intervalsCarried}i)` : '') + (r.lost ? 'LOST' + r.lost : '') + (r.loops ? 'loops' + r.loops : '')).join(' ')}`);
    }
  }
  for (const b of BASES) {
    const t1 = Date.now();
    const ex = runNestExact(b); exactOut[b] = ex;
    const beta = realBeta(b), want = (b % 2 === 0 ? 1 : -1);
    const syn = synthCache.get(beta);
    const cmp = ex.canon.map((x, i) => (x === syn.canon[i] ? 'ok' : 'DIFF'));
    if (cmp.includes('DIFF') || beta !== want) all = false;
    console.log(`\nbase ${b}: real beta_b ${beta > 0 ? '+1' : '-1'} (expected (-1)^b ${want > 0 ? '+1' : '-1'}); exact ${((Date.now() - t1) / 1000).toFixed(0)} s`);
    console.log('  exact classes: ' + ex.results.map((r) => `L${r.level}:${r.classes}${r.hooksCarried || r.intervalsCarried ? `(c${r.hooksCarried}h/${r.intervalsCarried}i)` : ''}${r.lost ? ' LOST' + r.lost : ''}${r.loops ? ' loops' + r.loops : ''}`).join(' '));
    console.log('  synth = exact, by relative level: ' + cmp.map((c, i) => `R${i + 1}:${c}`).join(' '));
    for (let i = 0; i < ex.canon.length; i++) if (VERB || cmp[i] === 'DIFF') { console.log(`   R${i + 1} exact ${ex.canon[i]}`); if (cmp[i] === 'DIFF') console.log(`   R${i + 1} synth ${syn.canon[i]}`); }
    for (const t of ex.trace) console.log('  trace ' + t);
  }
  console.log('\nExact canonical inputs, base b vs b+2 (order-free):');
  for (const b of BASES) if (BASES.includes(b + 2)) { const A = exactOut[b].canon, B = exactOut[b + 2].canon; console.log(`  base ${b} vs ${b + 2}: ` + B.map((x, i) => `R${i + 1}:${x === A[i] ? 'same' : 'DIFF'}`).join(' ')); }
  console.log('\nSynthetic canonical inputs (proxy ' + SPECS[0] + '):');
  for (const beta of [1, -1]) { console.log(`  beta_b ${beta > 0 ? '+1 (even b)' : '-1 (odd b)'}:`); synthCache.get(beta).canon.forEach((x, i) => console.log(`   R${i + 1} ${x}`)); }
  console.log(all ? '\nALL MATCH (nest label inputs = synthetic from (C, v, beta_b); proxies agree)' : '\nMISMATCH');
}
