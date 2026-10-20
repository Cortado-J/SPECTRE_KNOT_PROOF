// Experiment (not part of the proof): the label computation of the paper's Appendix A (label states and their steps) run along an
// ARBITRARY chain X_b < X_{b+1} < ... , where X_N is child c_N of a parent of kind T_N, instead of the nest (Delta, child 1).
// Positions are carried as integer affine forms in x = l_1 (54 side lengths at level 1) with the actual numbers as the
// shadow, so the run is exact for the given b. Prints per relative level: label classes, stretch vertices, |P_k(b)|.
// usage: node chains_label.js <b> <K0> <T:c,T:c,...>      (c = child number as in Table 1)
const ARGS = process.argv.slice(2);
const fs = require('fs');
const { F, ST } = require('./synth.js');
const { R, NAMES } = require('./lib.js');
const { rcompose } = R;
const J = JSON.parse(fs.readFileSync(__dirname + '/combin_8.json'));
const { M } = JSON.parse(fs.readFileSync(__dirname + '/M.json'));
const NV = 54; const IX = (s, j) => NAMES.indexOf(s) * 6 + j;
const vstar = NAMES.flatMap((s) => J.LEN[1][s].map((x) => x % 2));
const xref = NAMES.flatMap((s) => J.LEN[1][s]);   // x = l_1
// ---------------------------------------------------------------- linear forms
const mk = (a, e) => ({ a, e, v: a.reduce((s, c, i) => s + c * xref[i], 0) + e });
const zero = () => mk(new Array(NV).fill(0), 0);
const cst = (c) => mk(new Array(NV).fill(0), c);
const add = (p, q) => ({ a: p.a.map((c, i) => c + q.a[i]), e: p.e + q.e, v: p.v + q.v });
const sub = (p, q) => ({ a: p.a.map((c, i) => c - q.a[i]), e: p.e - q.e, v: p.v - q.v });
const addc = (p, c) => ({ a: p.a, e: p.e + c, v: p.v + c });
const mulc = (p, c) => ({ a: p.a.map((x) => x * c), e: p.e * c, v: p.v * c });
const par = (p) => ((p.a.reduce((s, c, i) => s + c * vstar[i], 0) + p.e) % 2 + 2) % 2;
const same = (p, q) => p.e === q.e && p.a.every((c, i) => c === q.a[i]);

// ---------------------------------------------------------------- obligations
// Local certificate: f == 0 identically, or f >= t with a >= 0 coefficientwise and 5*sum(a) + e >= t (all sides >= 5).
// Anything else is DEFERRED to certify.py, which certifies it on the Krylov space span{M^i l_1} that contains every
// real l_m (m >= 1): it finds a' = a + rho with rho orthogonal to that space (so a'.x = a.x for every real x),
// a' >= 0 and 5*sum(a') + e >= t, or (for f == 0) checks a is orthogonal to it and e = 0. Exact rational arithmetic.
const OB = new Map(); const deferred = [];
function need(f, t, ctx) {
  if (!(f.v >= t)) throw new Error('shadow violates its own decision: ' + ctx);
  const key = f.a.join(',') + '|' + f.e + '|' + t; if (OB.has(key)) return;
  const local = f.a.every((c) => c >= 0) && 5 * f.a.reduce((s, c) => s + c, 0) + f.e >= t;
  OB.set(key, { local, ctx }); if (!local) deferred.push({ type: 'ge', a: f.a, e: f.e, t, ctx });
}
function needZero(f, ctx) {
  if (f.v !== 0) throw new Error('shadow nonzero: ' + ctx);
  const key = 'Z' + f.a.join(',') + '|' + f.e; if (OB.has(key)) return;
  const local = f.e === 0 && f.a.every((c) => c === 0);
  OB.set(key, { local, ctx }); if (!local) deferred.push({ type: 'zero', a: f.a, e: f.e, ctx });
}
function decideEq(f, g, ctx) {   // is f == g ? records the answer
  const dlt = sub(f, g);
  if (dlt.v === 0) { needZero(dlt, ctx); return true; }
  if (dlt.v > 0) need(dlt, 1, ctx); else need(mulc(dlt, -1), 1, ctx);
  return false;
}
function decideLE(f, g, ctx) { if (f.v <= g.v) { need(sub(g, f), 0, ctx); return true; } need(sub(f, g), 1, ctx); return false; }
function modE(u, E, ctx) {   // u mod E as a form
  const q = Math.floor(u.v / E.v); const r = sub(u, mulc(E, q));
  need(r, 0, ctx + ' mod>=0'); need(sub(E, r), 1, ctx + ' mod<E'); return r;
}


const unit = (i) => { const a = new Array(NV).fill(0); a[i] = 1; return mk(a, 0); };
const step = (P) => { const Q = {}; NAMES.forEach((s, si) => { Q[s] = [0, 1, 2, 3, 4, 5].map((j) => { const row = M[si * 6 + j]; let f = zero(); row.forEach((cf, i) => { if (cf) f = add(f, mulc(P[NAMES[Math.floor(i / 6)]][i % 6], cf)); }); return f; }); }); return Q; };
const sumF = (arr) => arr.reduce((s, f) => add(s, f), zero());
function levelData(maxLevel) {   // LV[m][s][j] = form of l_m(s, j); DL[m] = form of d_m
  const LV = []; const DL = [];
  LV[1] = {}; NAMES.forEach((s) => { LV[1][s] = [0, 1, 2, 3, 4, 5].map((j) => unit(IX(s, j))); }); DL[1] = cst(6);
  for (let m = 2; m <= maxLevel; m++) { LV[m] = step(LV[m - 1]); DL[m] = add(add(LV[m - 1].Xi[2], LV[m - 1].Xi[1]), LV[m - 1].Gamma[0]); }
  return { LV, DL };
}
function compo(LV, DL, m, T, beta) {   // composition of a level-(m+1) T-supertile from level-m children
  const st = ST[T]; const kinds = st.kids; const nK = kinds.length;
  const nbr = st.sides.map((ss) => ss.map((x) => (x === 'R' ? null : x.split('.').map(Number))));
  const len = kinds.map((s) => LV[m][s]);
  const U = len.map((l) => { const u = [zero()]; for (let j = 0; j < 6; j++) u.push(add(u[j], l[j])); return u; });
  const E = U.map((u) => u[6]);
  const lens = {}; NAMES.forEach((s) => { lens[s] = LV[m][s].map((f) => f.v); });
  const rd = F(T, null, 0, beta, lens, DL[m].v);
  const sideAt = (c, u, ctx) => { for (let j = 0; j < 6; j++) if (U[c][j].v <= u.v && u.v < U[c][j + 1].v) { need(sub(u, U[c][j]), 0, ctx); need(sub(U[c][j + 1], u), 1, ctx); return j; } throw new Error('sideAt'); };
  const defU = kinds.map((s, c) => {
    let uA = zero();
    if (s === 'Sigma') { uA = add(U[c][5], DL[m]); need(DL[m], 2, 'delta>=2'); need(sub(len[c][5], DL[m]), 2, 'l-delta>=2'); }
    let uB = addc(uA, beta); if (uB.v < 0) uB = add(uB, E[c]);
    return [uA, uB];
  });
  const P = (c, u) => modE(sub(E[c], u), E[c], 'P');
  const marks = [];
  for (let c = 0; c < nK; c++) {
    const cand = []; for (let j = 0; j < 6; j++) cand.push(U[c][j]);
    for (let c2 = 0; c2 < nK; c2++) for (const u2 of defU[c2]) {
      if (c2 === c) { cand.push(u2); continue; }
      const j2 = sideAt(c2, u2, 'def'); const o2 = sub(u2, U[c2][j2]);
      if (decideEq(o2, zero(), 'def at vertex?')) continue;
      const p = nbr[c2][j2]; if (p && p[0] === c) cand.push(sub(add(U[c][p[1]], len[c2][j2]), o2));
    }
    const ms = [];
    for (const wv of rd.kids[c].marksU) { const hits = cand.filter((f) => f.v === wv); if (!hits.length) throw new Error('mark not among candidates'); ms.push(hits[0]); }
    const Ps = ms.map((u) => P(c, u));
    const runs = Ps.map((p, i) => { const q = i + 1 < Ps.length ? Ps[i + 1] : add(Ps[0], E[c]); return { a: p, len: sub(q, p) }; });
    marks.push({ u: ms, P: Ps, runs });
  }
  const piece = new Map(); let u = zero();
  for (let Jx = 0; Jx < 6; Jx++) for (const tag of st.pside[Jx]) { const [c, j] = tag.split('.').map(Number); u = add(u, len[c][j]); piece.set(c + '.' + j, u); }
  const EP = u; if (!same(EP, sumF(LV[m + 1][T]))) throw new Error('parent rim length form');
  const toParentU = (c, uu, ctx) => {
    let w = addc(uu, -1); if (w.v < 0) w = add(w, E[c]);
    const j = sideAt(c, w, ctx); let o = sub(uu, U[c][j]); if (o.v <= 0) o = add(o, E[c]);
    const u1 = piece.get(c + '.' + j); if (!u1) throw new Error('not a rim side');
    return modE(sub(u1, o), EP, ctx);
  };
  const parentA = T === 'Sigma' ? add(sumF(LV[m + 1].Sigma.slice(0, 5)), DL[m + 1]) : zero();
  return { rd, U, E, marks, EP, toParentU, P, parentA };
}
let LVDL = null;
function levels(maxLevel) { if (!LVDL || LVDL.LV.length <= maxLevel + 1) LVDL = levelData(maxLevel + 1); return LVDL; }
const omega = (m) => (m % 2 === 0 ? 1 : -1);
function initState(b, K0, maxLevel) {
  const { LV, DL } = levels(maxLevel || b + 20);
  const uf = new Map(); uf.set('c0', 'c0'); uf.set('c1', 'c1');
  const E0 = sumF(LV[b][K0]);
  const A0 = K0 === 'Sigma' ? add(sumF(LV[b].Sigma.slice(0, 5)), DL[b]) : zero();
  const w0 = omega(b);
  return { b, m: b, uf, lost: 0, E: E0, kind: K0, hooks: [], intervals: [w0 > 0 ? [addc(A0, 2), addc(A0, -1)] : [addc(A0, 1), addc(A0, -2)]], cross: ['c0', 'c1'] };
}
function cloneState(st) { return { ...st, uf: new Map(st.uf), hooks: st.hooks.slice(), intervals: st.intervals.slice(), cross: st.cross.slice() }; }
function advance(st0, T, cc) {   // returns [new state, row]; st0 is not modified
  const st = cloneState(st0); const uf = st.uf;
  const find = (x) => { while (uf.get(x) !== x) { uf.set(x, uf.get(uf.get(x))); x = uf.get(x); } return x; };
  const add_ = (x) => { uf.set(x, x); return x; };
  const { LV, DL } = levels(st.m + 2); const m = st.m;
  if (ST[T].kids[cc] !== st.kind) throw new Error(`child ${cc} of ${T} is ${ST[T].kids[cc]}, not ${st.kind}`);
  const C = compo(LV, DL, m, T, omega(m)); const { rd, marks } = C; const mk1 = marks[cc]; const E = C.E[cc];
  if (!same(E, st.E)) throw new Error('own rim form mismatch');
  const kid = rd.kids[cc]; const n = kid.runs.length;
  const pid = (c, mm, s) => (c * 4096 + mm) * 2 + s;
  const labels = new Map(); const put = (p, l) => { if (!labels.has(p)) labels.set(p, []); labels.get(p).push(l); };
  const lvl = 'L' + (m + 1);
  const locate = (u) => {
    const Pu = C.P(cc, u);
    for (let i = 0; i < mk1.P.length; i++) if (Pu.v === mk1.P[i].v) return { mark: i };
    for (let r = 0; r < n; r++) { const off = modE(sub(Pu, mk1.runs[r].a), E, 'off'); if (off.v < mk1.runs[r].len.v) return { run: r, off }; }
    throw new Error('locate');
  };
  const carriedHooks = []; const carriedIntervals = [];
  for (const [u, lab] of st.hooks) {
    const loc = locate(u);
    if (loc.mark !== undefined) { put(pid(cc, loc.mark, 1), lab); continue; }
    const r = kid.runs[loc.run];
    if (r.nb < 0) { carriedHooks.push([C.toParentU(cc, u, 'hook'), lab]); continue; }
    if (par(loc.off) === 0) put(pid(cc, loc.run, 1), lab);
    else if (r.len % 2 === 0) put(pid(r.partner[0], r.partner[1], 1), lab);
    else put(pid(cc, (loc.run + 1) % n, 0), lab);
  }
  st.intervals.forEach(([s0, s1], ii) => {
    const Lr = modE(sub(s1, s0), E, 'len');
    const inArc = [];
    mk1.u.forEach((mu, i) => { const rel = modE(sub(mu, s0), E, 'rel'); if (rel.v <= Lr.v) inArc.push({ i, rel }); });
    inArc.sort((p, q) => p.rel.v - q.rel.v);
    const pieces = new Map(); const carried = [];
    const stretch = (x0, x1) => {
      const uF = modE(add(s0, x0), E, 'first'), uL = modE(add(s0, x1), E, 'last');
      const loc = locate(uF); const r = kid.runs[loc.run];
      if (r.nb < 0) { carried.push([C.toParentU(cc, uL, 'carried'), C.toParentU(cc, uF, 'carried')]); return; }
      if (!pieces.has(loc.run)) pieces.set(loc.run, { even: 0, odd: 0 });
      const pc = pieces.get(loc.run);
      if (x1.v <= x0.v) pc[par(loc.off) === 0 ? 'even' : 'odd']++; else { pc.even++; pc.odd++; }
    };
    let cur = cst(0);
    for (const { i, rel } of inArc) { if (rel.v !== cur.v) stretch(cur, addc(rel, -1)); put(pid(cc, i, 1), add_(`${lvl}I${ii}@m${i}`)); cur = addc(rel, 1); }
    if (cur.v <= Lr.v) stretch(cur, Lr);
    for (const [rIdx, pc] of pieces) {
      if (pc.even) put(pid(cc, rIdx, 1), add_(`${lvl}I${ii}r${rIdx}e`));
      if (pc.odd) { const lab = add_(`${lvl}I${ii}r${rIdx}o`); const rr = kid.runs[rIdx]; if (rr.len % 2 === 0) put(pid(rr.partner[0], rr.partner[1], 1), lab); else put(pid(cc, (rIdx + 1) % n, 0), lab); }
    }
    for (const cpair of carried) carriedIntervals.push(cpair);
  });
  if (st.cross[0] !== null) put(pid(cc, kid.defA, 0), st.cross[0]);
  if (st.cross[1] !== null) put(pid(cc, kid.defA, 1), st.cross[1]);
  const rc = rcompose(rd, labels);
  st.lost += rc.lost.length || rc.lost.size || 0;
  for (const [l] of rc.uf) { const r = rc.find(l); if (r !== l) { const a = find(l), c2 = find(r); if (a !== c2) uf.set(a, c2); } }
  const newHooks = carriedHooks.map(([u, l]) => [u, l]);
  let cross = [null, null];
  for (let t = 0; t < rd.rim.length; t++) {
    const [c, i] = rd.rim[t]; const Kp = C.toParentU(c, marks[c].u[i], 'parent mark');
    const Lp = rc.byMark[t].L, Rp = rc.byMark[t].R;
    if (rc.pairing.get(Lp) === Rp) { const cls = rc.strandClass.get(Rp); if (cls != null) newHooks.push([Kp, find(cls)]); }
    else if (Kp.v === C.parentA.v) { const a = rc.strandClass.get(Rp), c2 = rc.strandClass.get(Lp); cross = [a == null ? null : find(a), c2 == null ? null : find(c2)]; }
  }
  st.E = C.EP; st.kind = T; st.m = m + 1; st.hooks = newHooks.map(([u, l]) => [u, find(l)]); st.intervals = carriedIntervals; st.cross = cross;
  const classes = new Set([...uf.keys()].map(find)).size;
  const stretchV = carriedIntervals.reduce((s, [s0, s1]) => s + ((((s1.v - s0.v) % C.EP.v) + C.EP.v) % C.EP.v) + 1, 0);
  const row = { N: m + 1, T, c: cc, classes, stretchV, blocks: classes + stretchV, hooks: newHooks.length, carried: carriedHooks.length, cross: cross.filter((x) => x !== null).length, lost: st.lost, loops: rc.loops };
  if (Math.abs(C.EP.v) > 2 ** 52) throw new Error('positions too large for exact doubles (level ' + (m + 1) + ')');
  return [st, row];
}
function runChain(b, K0, chain) {
  let st = initState(b, K0, b + chain.length + 1); const rows = [];
  for (const [T, cc] of chain) { const [s2, row] = advance(st, T, cc); st = s2; rows.push(row); }
  return rows;
}
module.exports = { runChain, initState, advance, levels };
if (require.main === module) {
  const b = +ARGS[0], K0 = ARGS[1]; const chain = ARGS[2].split(',').map((s) => { const [T, c] = s.split(':'); return [T, +c]; });
  const rows = runChain(b, K0, chain);
  console.log(`b=${b} ${K0}: ` + rows.map((r) => `${r.T.slice(0, 2)}${r.c}:${r.blocks}${r.stretchV ? '(' + r.classes + '+' + r.stretchV + ')' : ''}`).join(' '));
}
