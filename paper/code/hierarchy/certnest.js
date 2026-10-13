// Step 7 (L8 for every b): a symbolic run of the nest label propagation with NO proxies.
//
// Every rim position is carried as an exact integer linear form  f(x) = a.x + e  in the 54 side lengths
// x = l_{b-1} (kinds x sides) of the level below the base, with l_{b+k} = M^{k+1} x (P2) and Sigma offsets
// delta_{b+k} = l_{b+k-1}(Xi,2) + l_{b+k-1}(Xi,1) + l_{b+k-1}(Gamma,0) (P3). A numeric shadow (x = l_1, i.e. b = 2)
// picks the branch at every decision the label propagation makes (which run or mark a point is in, whether a point
// is a mark, which side of a child it lies on, interval stretches empty / one vertex / longer, a position equal to the
// parent's A, every "mod E"), and each decision is recorded as an obligation  f >= t  or  f == 0  on a linear form.
// An obligation is CERTIFIED locally when f == 0 identically, or f = a.x + e with a >= 0 coefficientwise and
// 5*sum(a) + e >= t (every side length of every level >= 1 is >= 5). The others are written to
// certnest_deferred.json and certified by certify_fib.py (Fibonacci closed form, integers only) and, independently,
// by certify.py (Krylov space, LP proposals checked in exact rationals). Both are valid for every b >= 2.
// Parities of forms are evaluated at v* (x = v* mod 2 for every b >= 2). A disequality is recorded as +-f >= 1, and
// every reduction "mod E" as the two obligations 0 <= r and r < E.
// So for every base b >= 2 of a given parity, nest.js's label input at every relative level equals the one computed
// here, which depends on b only through beta_b (= omega_b in the paper). Compared with synthnest.js's synthetic run.
// usage: node certnest.js <relative levels K, default 6>
const fs = require('fs');
const K = +(process.argv[2] || 6);
const { F, ST } = require('./synth.js');
const { R, NAMES } = require('./lib.js');
const { rcompose } = R;
const { runNestSynth } = require('./synthnest.js');
const J = JSON.parse(fs.readFileSync(__dirname + '/combin_8.json'));
const { M } = JSON.parse(fs.readFileSync(__dirname + '/M.json'));
const NV = 54; const IX = (s, j) => NAMES.indexOf(s) * 6 + j;
const vstar = NAMES.flatMap((s) => J.LEN[1][s].map((x) => x % 2));
const xref = NAMES.flatMap((s) => J.LEN[1][s]);   // numeric shadow: x = l_1 (base b = 2)

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

// ---------------------------------------------------------------- level data
const LEN = [];   // LEN[k][s][j]: form of l_{b+k}(s, j); LEN[-1] = x
const unit = (i) => { const a = new Array(NV).fill(0); a[i] = 1; return mk(a, 0); };
const X = {}; NAMES.forEach((s) => { X[s] = [0, 1, 2, 3, 4, 5].map((j) => unit(IX(s, j))); });
const step = (P) => { const Q = {}; NAMES.forEach((s, si) => { Q[s] = [0, 1, 2, 3, 4, 5].map((j) => { const row = M[si * 6 + j]; let f = zero(); row.forEach((c, i) => { if (c) f = add(f, mulc(P[NAMES[Math.floor(i / 6)]][i % 6], c)); }); return f; }); }); return Q; };
let prev = X; const DEL = [];
for (let k = 0; k <= K; k++) { const P = step(prev); LEN.push(P); DEL.push(add(add(prev.Xi[2], prev.Xi[1]), prev.Gamma[0])); prev = P; }
const STD = ST.Delta; const kinds = STD.kids; const nK = kinds.length;
const nbr = STD.sides.map((ss) => ss.map((x) => (x === 'R' ? null : x.split('.').map(Number))));
const sumF = (arr) => arr.reduce((s, f) => add(s, f), zero());

// symbolic composition data at relative step k (children at level b+k), checked against numeric F
function compo(k, beta) {
  const len = kinds.map((s) => LEN[k][s]);
  const U = len.map((l) => { const u = [zero()]; for (let j = 0; j < 6; j++) u.push(add(u[j], l[j])); return u; });
  const E = U.map((u) => u[6]);
  const lens = {}; NAMES.forEach((s) => { lens[s] = LEN[k][s].map((f) => f.v); });
  const rd = F('Delta', null, 0, beta, lens, DEL[k].v);
  const sideAt = (c, u, ctx) => { for (let j = 0; j < 6; j++) if (U[c][j].v <= u.v && u.v < U[c][j + 1].v) { need(sub(u, U[c][j]), 0, ctx + ' side>=' ); need(sub(U[c][j + 1], u), 1, ctx + ' side<'); return j; } throw new Error('sideAt'); };
  // defects
  const defU = kinds.map((s, c) => {
    let uA = zero();
    if (s === 'Sigma') { uA = add(U[c][5], DEL[k]); need(DEL[k], 2, `k${k} delta>=2`); need(sub(len[c][5], DEL[k]), 2, `k${k} l(Sigma,5)-delta>=2`); }
    let uB = addc(uA, beta); if (uB.v < 0) uB = add(uB, E[c]);
    return [uA, uB];
  });
  // candidate mark points per child (as in F), restricted to those F marks, in F's order
  const P = (c, u) => modE(sub(E[c], u), E[c], `k${k} P c${c}`);
  const marks = [];
  for (let c = 0; c < nK; c++) {
    const cand = []; for (let j = 0; j < 6; j++) cand.push(U[c][j]);
    for (let c2 = 0; c2 < nK; c2++) for (const u2 of defU[c2]) {
      if (c2 === c) { cand.push(u2); continue; }
      const j2 = sideAt(c2, u2, `k${k} def c${c2}`); const o2 = sub(u2, U[c2][j2]);
      if (decideEq(o2, zero(), `k${k} def c${c2} at vertex?`)) continue;
      const p = nbr[c2][j2]; if (p && p[0] === c) cand.push(sub(add(U[c][p[1]], len[c2][j2]), o2));
    }
    const want = rd.kids[c].marksU; const ms = [];
    for (const wv of want) { const hits = cand.filter((f) => f.v === wv); if (!hits.length) throw new Error('mark not among candidates'); for (const h of hits.slice(1)) needZero(sub(h, hits[0]), `k${k} c${c} coincident candidates`); ms.push(hits[0]); }
    // strict parent-frame order of the marks, and no other candidate is ambiguous: consecutive P differences >= 1
    const Ps = ms.map((u) => P(c, u));
    for (let i = 0; i + 1 < Ps.length; i++) need(sub(Ps[i + 1], Ps[i]), 1, `k${k} c${c} mark order`);
    const runs = Ps.map((p, i) => { const q = i + 1 < Ps.length ? Ps[i + 1] : add(Ps[0], E[c]); const l = sub(q, p); if (l.v !== rd.kids[c].runs[i].len || p.v !== rd.kids[c].runs[i].a) throw new Error('run mismatch with F'); if (par(l) !== l.v % 2) throw new Error('parity'); return { a: p, len: l }; });
    marks.push({ u: ms, P: Ps, runs });
  }
  // parent pieces: (c, j) -> end position u1 in the parent's own frame
  const piece = new Map(); let u = zero();
  for (let Jx = 0; Jx < 6; Jx++) for (const tag of STD.pside[Jx]) { const [c, j] = tag.split('.').map(Number); u = add(u, len[c][j]); piece.set(c + '.' + j, u); }
  const EP = u; if (!same(EP, sumF(LEN[k + 1].Delta))) throw new Error('parent rim length form');
  const toParentU = (c, uu, ctx) => {
    let w = addc(uu, -1); if (w.v < 0) w = add(w, E[c]);
    const j = sideAt(c, w, ctx + ' toParent'); let o = sub(uu, U[c][j]); if (o.v <= 0) o = add(o, E[c]);
    const u1 = piece.get(c + '.' + j); if (!u1) throw new Error('not a rim side');
    return modE(sub(u1, o), EP, ctx + ' toParent');
  };
  return { rd, U, E, marks, EP, toParentU, P };
}

function runSym(betaB) {
  const uf = new Map(); const find = (x) => { while (uf.get(x) !== x) { uf.set(x, uf.get(uf.get(x))); x = uf.get(x); } return x; };
  const add_ = (x) => { uf.set(x, x); return x; };
  const E0 = sumF(LEN[0].Delta);
  let state = { E: E0, hooks: [], intervals: [betaB > 0 ? [cst(2), addc(E0, -1)] : [cst(1), addc(E0, -2)]], cross: [add_('c0'), add_('c1')] };
  const canon = []; const lost = new Set();
  for (let k = 0; k < K; k++) {
    const betaK = k % 2 === 0 ? betaB : -betaB;
    const C = compo(k, betaK); const { rd, marks } = C; const mk1 = marks[1]; const E = C.E[1];
    if (!same(E, state.E)) throw new Error('own rim form mismatch');
    const kid = rd.kids[1]; const n = kid.runs.length; const ri = (i) => ((i - kid.defA) % n + n) % n;
    const pid = (c, mm, s) => (c * 4096 + mm) * 2 + s;
    const labels = new Map(); const put = (p, l) => { if (!labels.has(p)) labels.set(p, []); labels.get(p).push(l); };
    const lvl = 'L' + (k + 1);
    const locate = (u, ctx) => {
      const Pu = C.P(1, u);
      for (let i = 0; i < mk1.P.length; i++) if (Pu.v === mk1.P[i].v) { needZero(sub(Pu, mk1.P[i]), ctx + ' is mark'); return { mark: i }; }
      for (let r = 0; r < n; r++) { const off = modE(sub(Pu, mk1.runs[r].a), E, ctx + ' off'); if (off.v < mk1.runs[r].len.v) { need(off, 1, ctx + ' strictly inside run'); need(sub(mk1.runs[r].len, off), 1, ctx + ' inside run'); return { run: r, off }; } }
      throw new Error('locate');
    };
    const carriedHooks = []; const carriedIntervals = [];
    for (const [u, lab] of state.hooks) {
      const loc = locate(u, `k${k} hook`);
      if (loc.mark !== undefined) { put(pid(1, loc.mark, 1), lab); continue; }
      const r = kid.runs[loc.run];
      if (r.nb < 0) { carriedHooks.push([C.toParentU(1, u, `k${k} hook`), lab]); continue; }
      if (par(loc.off) === 0) put(pid(1, loc.run, 1), lab);
      else if (r.len % 2 === 0) put(pid(r.partner[0], r.partner[1], 1), lab);
      else put(pid(1, (loc.run + 1) % n, 0), lab);
    }
    if (state.intervals.length > 1) throw new Error('more than one carried interval');
    state.intervals.forEach(([s0, s1], ii) => {
      const ctx = `k${k} interval`;
      const Lr = modE(sub(s1, s0), E, ctx + ' length');
      // marks inside the arc, by position from s0
      const inArc = [];
      mk1.u.forEach((mu, i) => { const rel = modE(sub(mu, s0), E, ctx + ' mark rel'); if (decideLE(rel, Lr, ctx + ' mark in arc?')) inArc.push({ i, rel }); });
      inArc.sort((p, q) => p.rel.v - q.rel.v);
      for (let t = 0; t + 1 < inArc.length; t++) need(sub(inArc[t + 1].rel, inArc[t].rel), 1, ctx + ' marks order');
      const pieces = new Map(); const carried = [];
      const stretch = (x0, x1) => {   // vertices rel x0..x1 (x1 >= x0), no marks inside
        const uF = modE(add(s0, x0), E, ctx + ' first'), uL = modE(add(s0, x1), E, ctx + ' last');
        const loc = locate(uF, ctx + ' stretch'); const r = kid.runs[loc.run];
        // the last vertex is in the same run (no mark between): certify through its own location
        const locL = locate(uL, ctx + ' stretch end'); if (locL.run !== loc.run) throw new Error('stretch crosses runs');
        if (r.nb < 0) { carried.push([C.toParentU(1, uL, ctx + ' carried'), C.toParentU(1, uF, ctx + ' carried')]); return; }
        if (!pieces.has(loc.run)) pieces.set(loc.run, { even: 0, odd: 0 });
        const pc = pieces.get(loc.run);
        if (decideLE(x1, x0, ctx + ' one-vertex stretch?')) pc[par(loc.off) === 0 ? 'even' : 'odd']++; else { pc.even++; pc.odd++; }
      };
      let cur = cst(0);   // next unvisited rel
      for (const { i, rel } of inArc) {
        if (!decideEq(rel, cur, ctx + ' stretch empty?')) stretch(cur, addc(rel, -1));
        put(pid(1, i, 1), add_(`${lvl}I${ii}@m${ri(i)}`));
        cur = addc(rel, 1);
      }
      if (decideLE(cur, Lr, ctx + ' tail nonempty?')) stretch(cur, Lr);
      for (const [rIdx, pc] of pieces) {
        if (pc.even) put(pid(1, rIdx, 1), add_(`${lvl}I${ii}r${ri(rIdx)}e`));
        if (pc.odd) { const lab = add_(`${lvl}I${ii}r${ri(rIdx)}o`); const rr = kid.runs[rIdx]; if (rr.len % 2 === 0) put(pid(rr.partner[0], rr.partner[1], 1), lab); else put(pid(1, (rIdx + 1) % n, 0), lab); }
      }
      for (const cp of carried) carriedIntervals.push(cp);
    });
    if (state.cross[0] !== null) put(pid(1, kid.defA, 0), state.cross[0]);
    if (state.cross[1] !== null) put(pid(1, kid.defA, 1), state.cross[1]);
    const portsCanon = canonLevel(labels, rd.kids, find, [...uf.keys()]);
    const rc = rcompose(rd, labels);
    for (const l of rc.lost) lost.add(find(l));
    for (const [l] of rc.uf) { const r = rc.find(l); if (r !== l) { const a = find(l), c2 = find(r); if (a !== c2) uf.set(a, c2); } }
    const newHooks = carriedHooks.map(([u, l]) => [u, l]);
    let cross = [null, null];
    for (let t = 0; t < rd.rim.length; t++) {
      const [c, i] = rd.rim[t]; const Kp = C.toParentU(c, marks[c].u[i], `k${k} parent mark`);
      const Lp = rc.byMark[t].L, Rp = rc.byMark[t].R;
      if (rc.pairing.get(Lp) === Rp) { const cls = rc.strandClass.get(Rp); if (cls != null) newHooks.push([Kp, find(cls)]); }
      else if (decideEq(Kp, zero(), `k${k} parent mark = parent A?`)) { const a = rc.strandClass.get(Rp), c2 = rc.strandClass.get(Lp); cross = [a == null ? null : find(a), c2 == null ? null : find(c2)]; }
    }
    for (let i = 0; i < newHooks.length; i++) for (let j = i + 1; j < newHooks.length; j++) if (decideEq(newHooks[i][0], newHooks[j][0], `k${k} distinct hook positions`)) throw new Error('two hooks at one point');
    state = { E: C.EP, hooks: newHooks.map(([u, l]) => [u, find(l)]), intervals: carriedIntervals, cross };
    canon.push(`ports{${portsCanon}} part{${partition([...uf.keys()], find)}} carry{${carriedHooks.length}h/${carriedIntervals.length}i lost${lost.size} loops${rc.loops} cross${cross.map((x) => (x === null ? '-' : 'y')).join('')} labelledRim${newHooks.length}}`);
  }
  return canon;
}
function canonLevel(labels, kids, ufFind, allLabels) {
  const least = new Map(); for (const l of allLabels) { const r = ufFind(l); if (!least.has(r) || l < least.get(r)) least.set(r, l); }
  const nm = (l) => least.get(ufFind(l)); const ent = [];
  for (const [p, ls] of labels) { const c = Math.floor(p / 8192), m = Math.floor(p / 2) % 4096, s = p % 2; const n = kids[c].runs.length; ent.push(`${c}.${((m - kids[c].defA) % n + n) % n}.${s}=${ls.map(nm).sort().join(',')}`); }
  return ent.sort().join(' ');
}
function partition(allLabels, ufFind) { const cl = new Map(); for (const l of allLabels) { const r = ufFind(l); if (!cl.has(r)) cl.set(r, []); cl.get(r).push(l); } return [...cl.values()].map((x) => x.sort().join(',')).sort().join(' | '); }

let ok = true; const out = {};
for (const beta of [1, -1]) {
  OB.clear(); deferred.length = 0;
  const t0 = Date.now();
  const canon = runSym(beta);
  const syn = runNestSynth(beta, K, 'u8:4').canon;
  const cmp = canon.map((x, i) => (x === syn[i] ? 'ok' : 'DIFF'));
  const nLocal = [...OB.values()].filter((o) => o.local).length;
  console.log(`beta_b = ${beta > 0 ? '+1 (even b)' : '-1 (odd b)'}: ${K} relative levels, ${OB.size} distinct obligations, ${nLocal} certified locally, ${deferred.length} deferred to certify.py; ${((Date.now() - t0) / 1000).toFixed(1)} s`);
  console.log('  symbolic = synthetic (synthnest.js, proxy u8:4): ' + cmp.map((c, i) => `R${i + 1}:${c}`).join(' '));
  if (cmp.includes('DIFF')) ok = false;
  canon.forEach((x, i) => console.log(`   R${i + 1} ${x}`));
  out[beta > 0 ? 'even' : 'odd'] = deferred.slice();
}
fs.writeFileSync(__dirname + '/certnest_deferred.json', JSON.stringify({ K, names: NAMES, l1: xref, M, obligations: out }));
console.log(ok ? 'symbolic run reproduces the synthetic label inputs; deferred obligations written to certnest_deferred.json' : 'MISMATCH');
