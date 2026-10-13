// Step 5: the two-level data OWN_N(T) (where the Delta child's own rim marks from its own composition sit in the
// level-N runs) as an explicit function of (C, v, beta_{N-1}), built from nested PROXY lengths:
//   p_{N-2}(s, j) = 6 + v(s, j),  p_{N-1} = M p_{N-2},  Sigma offsets delta = Xi2 + Xi1 + Gam0 of the level below.
// Also re-checks S_N = F(...) with these nested proxies. Compared with reduce.js's OWN / ENC from the directly composed geometry (floating point).
// usage: node synthown.js <maxLevel>
const MAXL = +(process.argv[2] || 6), VERB = process.argv[3] === 'v';
const fs = require('fs');
const { F, ST } = require('./synth.js');
const { R, NAMES, load } = require('./lib.js');
const J = JSON.parse(fs.readFileSync(__dirname + '/combin_8.json'));
const { M } = JSON.parse(fs.readFileSync(__dirname + '/M.json'));
const v = {}; for (const s of NAMES) v[s] = J.LEN[1][s].map((x) => x % 2);
const p0 = {}; for (const s of NAMES) p0[s] = v[s].map((b) => 6 + b);
const flat = (p) => NAMES.flatMap((s) => p[s]);
const unflat = (a) => { const p = {}; NAMES.forEach((s, i) => { p[s] = a.slice(6 * i, 6 * i + 6); }); return p; };
const p1 = unflat(M.map((r) => r.reduce((a, x, i) => a + x * flat(p0)[i], 0)));
const delta = (p) => p.Xi[2] + p.Xi[1] + p.Gamma[0];
const d0 = 2 + (J.DEF[1].Sigma.off % 2);   // Sigma offset at the lower level (proxy)
const d1 = delta(p0);                      // Sigma offset at the upper level, from the lower lengths

// own rim marks of a level-(N-1) supertile of kind K from its composition (children at level N-2, betaLow):
// returns [{u, tag}] with u = position along its own ccw rim from its own vertex 0 (lengths p1), sorted ccw from A.
function ownMarks(K, betaLow) {
  const st = ST[K]; const kinds = st.kids; const n = kinds.length;
  const E = p1[K].reduce((a, b) => a + b, 0);
  const V = [0]; for (let j = 0; j < 6; j++) V.push(V[j] + p1[K][j]);
  // walk the parent rim: pieces (c, j) in parent ccw order; reflected child: piece goes from c's vertex j+1 to vertex j
  const pts = []; // {u, c, kind:'junction'|'def', tag}
  const pieces = []; for (let Jx = 0; Jx < 6; Jx++) { let u = V[Jx]; for (const tag of st.pside[Jx]) { const [c, j] = tag.split('.').map(Number); const l = p0[kinds[c]][j]; pieces.push({ c, j, u0: u, u1: u + l, l }); u += l; } }
  for (let i = 0; i < pieces.length; i++) { const a = pieces[i], b = pieces[(i + 1) % pieces.length]; if (a.c !== b.c) pts.push({ u: a.u1 % E, tag: 'J' }); }
  // defects of children on the rim
  const defs = [];
  pieces.forEach((pc) => {
    const s = kinds[pc.c];
    // child's own coordinates along side j: offset o from its vertex j corresponds to parent position u1 - o
    const own = []; // [offsetFromVertexJ, which]
    const uAside = s === 'Sigma' ? [5, d0] : [0, 0];
    const Bside = s === 'Sigma' ? [5, d0 + betaLow] : (betaLow > 0 ? [0, 1] : [5, p0[s][5] - 1]);
    for (const [which, [sj, o]] of [['A', uAside], ['B', Bside]]) {
      if (sj === pc.j && o >= 0 && o < pc.l) own.push([o, which]);
      if (o === 0 && ((sj + 5) % 6) === pc.j) own.push([pc.l, which]);   // vertex at the end of the previous side
    }
    for (const [o, which] of own) defs.push({ u: (pc.u1 - o) % E, c: pc.c, which });
  });
  const g = n - 1;
  for (const d of defs) { const tag = d.c === g ? d.which : 'J'; const ex = pts.find((q) => q.u === d.u); if (ex) { if (tag !== 'J') ex.tag = tag; } else pts.push({ u: d.u, tag }); }
  // sort ccw from A (A is at u = 0 for non-Sigma, else inside side 5)
  const uA = pts.find((q) => q.tag === 'A').u;
  pts.sort((x, y) => ((x.u - uA + E) % E) - ((y.u - uA + E) % E));
  return { pts, E };
}
// locate own marks of child 1 in the level-N runs (synthetic F with lengths p1, Sigma offset d1)
function ownEnc(T, betaHigh, betaLow) {
  const rd = F(T, null, 0, betaHigh, p1, d1);
  const k = rd.kids[1]; const K = k.type; const { pts, E } = ownMarks(K, betaLow);
  const P = (u) => (E - u) % E;
  const n = k.runs.length; const rot = k.defA; const ri = (i) => ((i - rot) % n + n) % n;
  const items = pts.map((q) => {
    const mi = k.marksU.indexOf(q.u); if (mi >= 0) return `${q.tag}@m${ri(mi)}`;
    let r = 0; while (!(((P(q.u) - k.runs[r].a) + E) % E < k.runs[r].len)) r++;
    return `${q.tag}@r${ri(r)}+${(((P(q.u) - k.runs[r].a) + E) % E) % 2}`;
  });
  return { own: items.join(' '), rd };
}
const canon = (s) => s.replace(/def\[([^\]]*)\]/, (_, x) => 'def[' + x.split(',').sort().join(',') + ']');
const D = load(MAXL);
let all = true;
for (let N = 3; N <= MAXL; N++) {
  const betaHigh = (N - 1) % 2 ? -1 : 1, betaLow = (N - 2) % 2 ? -1 : 1;
  const res = [];
  for (const T of NAMES) {
    const { own, rd } = ownEnc(T, betaHigh, betaLow);
    const okS = canon(R.encode(rd, false)) === canon(D.ENC[T][N]);
    const okO = own === D.OWN[T][N];
    if (!okO && VERB) console.log(`  ${T} N=${N}\n   syn  ${own}\n   real ${D.OWN[T][N]}`);
    all = all && okS && okO; res.push(`${T}:${okS ? 'S' : 's!'}${okO ? 'O' : 'o!'}`);
  }
  console.log(`N=${N}: ${res.join(' ')}`);
}
console.log('OWN (Delta) real:'); for (let N = 2; N <= MAXL; N++) console.log(`  N=${N}: ${D.OWN.Delta[N]}`);
console.log(all ? 'ALL MATCH (S and OWN, nested proxies)' : 'MISMATCH');
