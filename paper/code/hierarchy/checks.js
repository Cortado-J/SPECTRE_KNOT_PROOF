// Audit checks. usage: FAM=fan21 node checks.js 01222222222222 <maxL>
// 1. crossover shape of every directly composed supertile (floating point): defects adjacent, and R(A)<->R(B), L(A)<->L(B)
// 2. full reduced pairing (rcompose) vs directly composed parent pairing at every rim-mark port
const V = __dirname + '/../core/';
const MAXL = +(process.argv[3] || 7), DIG = process.argv[2];
const { build, rcompose } = require(V + 'reduce.js');
const { LEV, tile, gamma } = build(DIG, MAXL, true);
const portL = (sh, k) => { const j = (k + sh.E - 1) % sh.E; return 2 * sh.cyc[j] + (sh.fwd[j] ? 1 : 0); };
const portR = (sh, k) => 2 * sh.cyc[k] + (sh.fwd[k] ? 0 : 1);
function shape(sh, name) {
  const [A, B] = [sh.defA, sh.defB];
  const adj = (B - A + sh.E) % sh.E === 1 || (A - B + sh.E) % sh.E === 1;
  const rr = sh.pair[portR(sh, A)] === portR(sh, B) && sh.pair[portL(sh, A)] === portL(sh, B);
  const rl = sh.pair[portR(sh, A)] === portL(sh, B) && sh.pair[portL(sh, A)] === portR(sh, B);
  return `${name}: defs=${sh.defs.length} A=${A} B=${B} adjacent=${adj} shape=${rr ? 'RR/LL(crossing)' : rl ? 'RL/LR(other)' : '??'} loops=${sh.loops}`;
}
console.log(shape(tile, 'tile'));
console.log(shape(gamma, 'mystic'));
let bad = 0, checked = 0;
for (let N = 1; N <= MAXL; N++) {
  const out = [];
  for (const [t, sh] of Object.entries(LEV[N - 1].shapes)) {
    const s = shape(sh, t); if (!s.includes('defs=2') || !s.includes('adjacent=true') || !s.includes('RR/LL') || !s.includes('loops=0')) { bad++; console.log('  BAD', N, s); }
    // reduced vs direct
    const rd = sh.rd; const rc = rcompose(rd);
    const rimStartPos = rd.rim.map(([c, i]) => rd.kids[c].toParent[rd.kids[c].runs[i].a]);
    const info = new Map(rc.parentPorts.map((q) => [q.p, q]));
    let mism = 0;
    for (const q of rc.parentPorts) {
      const K = rimStartPos[q.t]; const ex = q.side === 'R' ? portR(sh, K) : portL(sh, K);
      const o = info.get(rc.pairing.get(q.p)); const K2 = rimStartPos[o.t]; const ex2 = o.side === 'R' ? portR(sh, K2) : portL(sh, K2);
      checked++; if (sh.pair[ex] !== ex2) mism++;
    }
    // also: every non-mark rim vertex of the parent is a hook (direct) -- implied by defs=2 at marks
    if (mism) { bad++; console.log('  REDUCED != EXACT', N, t, mism); }
    out.push(`${t}:${rc.parentPorts.length}p/${rc.loops}l/${mism}x`);
  }
  console.log(`level ${N}: ${out.join(' ')}`);
}
console.log('reduced-vs-direct port checks', checked, 'problems', bad);
