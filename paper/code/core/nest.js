// Reduced (parity-only) propagation of the strand labels of a nest base N_b up the chain N_b < N_{b+1} < ... (child 1 of Delta).
// Every arc of N_b gets its own label; we follow the labels through the reduced compositions and count how many
// classes remain at each level.  The computation uses only (a) the reduced data R(Delta, N) of each level and
// (b) the location (run index + offset parity, or mark index) of the labelled rim positions of N_m inside the runs
// of the next level.  Both are printed as canonical strings so that bases b and b+2 can be compared.
// usage: node nest.js <digits> <maxLevel> <bases e.g. 2,3,4,5>
const DIGITS = process.argv[2] || '0222221', MAXL = +(process.argv[3] || 9);
const BASES = (process.argv[4] || '2,3,4,5').split(',').map(Number);
const { build, rcompose, encode } = require('./reduce.js');
const { LEV } = build(DIGITS, MAXL, true);
const det = (T) => T[0] * T[4] - T[1] * T[3];

function runNest(b) {
  const trace = [];
  // union-find on labels
  const uf = new Map(); const find = (x) => { while (uf.get(x) !== x) { uf.set(x, uf.get(uf.get(x))); x = uf.get(x); } return x; };
  const add = (x) => { uf.set(x, x); return x; };
  // state of N_m in its own frame: hooks Map(pos -> label), intervals [[start, end]] (cyclic ranges of rim vertices, all fresh singletons),
  // cross [labelR, labelL] for the crossover arcs through R(defA) and L(defA)
  const base = LEV[b - 1].shapes.Delta;
  // one interval: every rim vertex except the two crossover corners (defB is defA +/- 1, so the complementary interval would wrap the whole rim)
  const after = (base.defB - base.defA + base.E) % base.E === 1;
  const interval = after ? [(base.defB + 1) % base.E, (base.defA - 1 + base.E) % base.E] : [(base.defA + 1) % base.E, (base.defB - 1 + base.E) % base.E];
  let state = { E: base.E, hooks: new Map(), intervals: [interval], cross: [add('c0'), add('c1')], defA: base.defA, defB: base.defB };
  const lost = new Set(); const results = [];
  for (let m = b; m < MAXL; m++) {
    const parent = LEV[m].shapes.Delta; const rd = parent.rd; const kid = rd.kids[1];
    const n = kid.runs.length; const rot = kid.defA; const ri = (i) => ((i - rot) % n + n) % n;
    const pid = (c, mm, s) => (c * 4096 + mm) * 2 + s;
    const labels = new Map(); const put = (p, l) => { if (!labels.has(p)) labels.set(p, []); labels.get(p).push(l); };
    const enc = [];   // canonical encoding of this level's label input
    const lvl = 'L' + (m + 1 - b);
    const locate = (k) => { const mi = kid.markPos.indexOf(k); if (mi >= 0) return { mark: mi }; let r = 0; while (!(((k - kid.markPos[r]) + kid.E) % kid.E < kid.runs[r].len)) r++; return { run: r, off: ((k - kid.markPos[r]) + kid.E) % kid.E }; };
    const carriedHooks = new Map(); const carriedIntervals = [];
    // labelled hooks
    const hookList = [...state.hooks].sort((u, v) => u[0] - v[0]);
    for (const [pos, lab] of hookList) {
      const k = kid.posMap[pos]; const loc = locate(k);
      if (loc.mark !== undefined) { put(pid(1, loc.mark, 1), lab); enc.push(`${lab}@m${ri(loc.mark)}`); continue; }
      const r = kid.runs[loc.run];
      if (r.nb < 0) { carriedHooks.set(kid.toParent[k], lab); enc.push(`${lab}@rim`); continue; }
      if (loc.off % 2 === 0) put(pid(1, loc.run, 1), lab);
      else if (r.len % 2 === 0) put(pid(r.partner[0], r.partner[1], 1), lab);   // even run: odd hooks are on the partner's zigzag
      else put(pid(1, (loc.run + 1) % n, 0), lab);
      enc.push(`${lab}@r${ri(loc.run)}+${loc.off % 2}`);
    }
    // intervals: walk the vertices, split by runs / marks
    state.intervals.forEach(([s0, s1], ii) => {
      const len = ((s1 - s0) + state.E) % state.E + 1;
      const pieces = new Map();   // run -> {even, odd, first}
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
      for (const [rIdx, pc] of [...pieces].sort((u, v) => u[0] - v[0])) {
        if (pc.even) { const lab = add(`${lvl}I${ii}r${ri(rIdx)}e`); put(pid(1, rIdx, 1), lab); }
        if (pc.odd) { const lab = add(`${lvl}I${ii}r${ri(rIdx)}o`); const rr = kid.runs[rIdx]; if (rr.len % 2 === 0) put(pid(rr.partner[0], rr.partner[1], 1), lab); else put(pid(1, (rIdx + 1) % n, 0), lab); }
        enc.push(`I${ii}@r${ri(rIdx)}(${pc.even ? 'e' : ''}${pc.odd ? 'o' : ''})`);
      }
      // merge adjacent carried pieces (cyclic adjacency ignored: the interval never wraps the whole rim)
      for (const cpiece of carried) carriedIntervals.push(cpiece);
      if (carried.length) enc.push(`I${ii}@rim×${carried.length}`);
    });
    // crossover
    const sw = det(LEV[m].trs[1]) < 0 ? 1 : 0;   // child 1 placed by a reflection: its own R(A) is L(A) in the parent frame
    if (state.cross[0] !== null) { put(pid(1, kid.defA, 1 - sw), state.cross[0]); enc.push(`${state.cross[0]}@XR`); }
    if (state.cross[1] !== null) { put(pid(1, kid.defA, sw), state.cross[1]); enc.push(`${state.cross[1]}@XL`); }
    // reduced walk
    const rc = rcompose(rd, labels);
    for (const l of rc.lost) lost.add(find(l));
    // merge classes found by the walk into our union-find (rcompose has its own uf over the labels we passed)
    for (const [l] of rc.uf) { const r = rc.find(l); if (r !== l) { const a = find(l), c2 = find(r); if (a !== c2) uf.set(a, c2); } }
    // new state: hooks at parent rim marks, crossover, carried
    const keyPos = new Map(); parent.marks.forEach((mk) => keyPos.set(mk.pos, mk.tag));
    const newHooks = new Map(carriedHooks);
    // parent rim marks in rim order t: the mark at the start of rim run t; its parent cycle position:
    const rimStartPos = rd.rim.map(([c, i]) => rd.kids[c].toParent[rd.kids[c].runs[i].a]);
    const nR = rd.rim.length; let cross = [null, null];
    for (let t = 0; t < nR; t++) {
      const L = rc.byMark[t].L, R = rc.byMark[t].R; const K = rimStartPos[t];
      if (rc.pairing.get(L) === R) { const cls = rc.strandClass.get(R); if (cls !== null && cls !== undefined) newHooks.set(K, find(cls)); }
      else if (K === parent.defA) { const clsR = rc.strandClass.get(R), clsL = rc.strandClass.get(L); cross = [clsR === null || clsR === undefined ? null : find(clsR), clsL === null || clsL === undefined ? null : find(clsL)]; }
    }
    for (const [K, lab] of carriedHooks) newHooks.set(K, find(lab));
    state = { E: parent.E, hooks: newHooks, intervals: carriedIntervals, cross, defA: parent.defA, defB: parent.defB };
    const roots = new Set(); for (const l of uf.keys()) roots.add(find(l));
    results.push({ level: m + 1, classes: roots.size, lost: lost.size, loops: rc.loops, hooksCarried: carriedHooks.size, intervalsCarried: carriedIntervals.length, labelled: newHooks.size });
    trace.push(`${lvl}: ${enc.join(' ')}`);
  }
  return { results, trace };
}
const out = {};
for (const b of BASES) {
  const { results, trace } = runNest(b); out[b] = trace;
  console.log(`base ${b} (level-${b} Delta, ${LEV[b - 1].shapes.Delta.E} arcs): ` + results.map((r) => `L${r.level}: ${r.classes} class${r.classes === 1 ? '' : 'es'}${r.lost ? ' LOST' + r.lost : ''}${r.loops ? ' loops' + r.loops : ''} (carried ${r.hooksCarried}h/${r.intervalsCarried}i)`).join('; '));
}
console.log('\nCanonical label-input encodings compared between bases b and b+2 (same relative level):');
for (const b of BASES) if (BASES.includes(b + 2)) {
  const A = out[b], B = out[b + 2]; const k = Math.min(A.length, B.length);
  const cmp = []; for (let j = 0; j < k; j++) cmp.push(`L${j + 1}:${A[j] === B[j] ? 'same' : 'DIFF'}`);
  console.log(`  base ${b} vs ${b + 2}: ${cmp.join(' ')}`);
}
if (process.argv[5] === 'dump') for (const b of BASES) { console.log('\nbase ' + b); for (const t of out[b]) console.log('  ' + t); }
