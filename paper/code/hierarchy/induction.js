// The induction step of the signature theorem (paper, Theorem "Signature" and Computation "The induction step directly"), as a finite check.
//
// For every kind T and both orientation signs w = w_m = (-1)^m of the children, build the skeleton
//   S_T(l_1, d_1, w) = F(T, ..., w, LENS = l_1, DELTA = d_1)
// from the composition pattern C (combin_8.json, extracted from the geometry and compared with the spectre paper's
// Fig. 5.1 by crosscheck/fig51_compare.py), the level-1 side lengths l_1 and the level-1 Sigma offset d_1, and run the
// reduced walk (core/reduce.js rcompose) on it. The step is valid if, for all 18 cases:
//   (a) the walk closes no loop;
//   (b) every parent rim mark is a hook except two, which are the Gamma child's A and B;
//   (c) those two are adjacent on the parent rim (the rim run between them has length 1), with B = A + w' in the
//       parent's own orientation, w' = -w;
//   (d) the pairing at them is the crossover R(A) <-> R(B), L(A) <-> L(B).
// By the parity lemma (paper, "Parity lemma") the skeleton of the composition m -> m+1 equals S_T(l_1, d_1, w_m) for every
// m >= 1, because l_m = l_1 and d_m = d_1 (mod 2) and both satisfy the order condition; this script also checks the
// order condition for l_1, d_1 and, as a corroboration of the parity lemma, that other length vectors with the same
// parities give the same skeleton.
// usage: node induction.js [MAXL]     (needs combin_8.json and M.json from combin.js / recur.js; with MAXL >= 2 it
//        also compares with the skeletons of the actual supertiles of levels 2..MAXL, which needs ~6.5 GB at MAXL = 9)
const MAXL = +(process.argv[2] || 0);   // read before requiring reduce.js, which overwrites process.argv
const fs = require('fs');
const J = JSON.parse(fs.readFileSync(__dirname + '/combin_8.json'));
const { M } = JSON.parse(fs.readFileSync(__dirname + '/M.json'));
const { F, ST } = require('./synth.js');
const { R, NAMES } = require('./lib.js');
const { rcompose, encode } = R;

const L1 = J.LEN[1], d1 = J.DEF[1].Sigma.off;
const flat = (p) => NAMES.flatMap((s) => p[s]);
const unflat = (a) => { const p = {}; NAMES.forEach((s, i) => { p[s] = a.slice(6 * i, 6 * i + 6); }); return p; };
const apply = (v) => M.map((row) => row.reduce((a, x, i) => a + x * v[i], 0));

// ---- order condition for (l_1, d_1)
const minL = Math.min(...flat(L1));
const oc = (L, d) => Math.min(...flat(L)) >= 3 && d >= 3 && L.Sigma[5] - d >= 3;
console.log(`level-1 side lengths: min ${minL}; Sigma: d_1 = ${d1}, l_1(Sigma,5) = ${L1.Sigma[5]}; order condition ${oc(L1, d1) ? 'holds' : 'FAILS'}`);
if (!oc(L1, d1)) process.exit(1);

// ---- position of the parent's A from C: the Gamma child's vertex 0 on the parent rim
for (const T of NAMES) {
  const st = ST[T]; const g = st.kids.length - 1; let where = null;
  st.pside.forEach((seq, Jx) => seq.forEach((tag, i) => { if (tag === g + '.5') where = [Jx, seq.slice(0, i)]; }));
  const [Jx, before] = where;
  console.log(`  ${T.padEnd(6)} parent A = Gamma child's vertex 0: on parent side ${Jx} after ${before.length ? before.map((t) => { const [c, j] = t.split('.').map(Number); return st.kids[c] + '.' + j; }).join(' + ') : 'nothing (a parent vertex)'}`);
}

// ---- the 18 checks
function check(T, w, LENS, DELTA) {
  const rd = F(T, null, 0, w, LENS, DELTA);
  const rc = rcompose(rd);
  const nR = rd.rim.length;
  const tOf = (id) => rd.rim.findIndex(([c, i]) => rd.kids[c].runs[i].startMark === id);
  const [idA, idB] = rd.parentDefMarks; const tA = tOf(idA), tB = tOf(idB);
  const wp = -w;
  const adj = tA >= 0 && tB >= 0 && (tA + wp + nR) % nR === tB;
  const runAB = wp > 0 ? rd.rim[tA] : rd.rim[tB];   // the rim run from the earlier of the two marks
  const len1 = runAB && rd.kids[runAB[0]].runs[runAB[1]].len === 1;
  const nh = rc.nonHook.slice().sort((a, b) => a - b), want = [tA, tB].sort((a, b) => a - b);
  const hooksOK = nh.length === 2 && nh[0] === want[0] && nh[1] === want[1];
  const bm = rc.byMark;
  const cross = hooksOK && rc.pairing.get(bm[tA].R) === bm[tB].R && rc.pairing.get(bm[tA].L) === bm[tB].L;
  const ok = rc.loops === 0 && hooksOK && adj && len1 && cross;
  return { ok, rd, rc, nR, line: `${T.padEnd(6)} w=${w > 0 ? '+1' : '-1'}: ${rd.kids.length} children, ${rd.nMarks} marks, ${rd.kids.reduce((a, k) => a + k.runs.length, 0)} runs, parent rim marks ${nR}: loops ${rc.loops}, non-hooks ${rc.nonHook.length} ${hooksOK ? '= {A,B}' : 'WRONG'}, adjacent ${adj && len1}, crossover R(A)-R(B) L(A)-L(B) ${cross} => ${ok ? 'OK' : 'FAIL'}` };
}
let all = true; const enc = {};
for (const w of [-1, 1]) for (const T of NAMES) { const r = check(T, w, L1, d1); console.log(r.line); all = all && r.ok; enc[T + w] = encode(r.rd, false); }

// ---- corroboration of the parity lemma: other lengths with the same parities, satisfying the order condition
const canon = (s) => s.replace(/def\[([^\]]*)\]/, (_, x) => 'def[' + x.split(',').sort().join(',') + ']');
const l2 = unflat(apply(flat(L1))), l3 = unflat(apply(flat(l2)));
const dOf = (L) => L.Xi[2] + L.Xi[1] + L.Gamma[0];   // d_{m+1} from l_m (paper, Lemma "Position of A")
const alts = [['l_2, d_2', l2, dOf(L1)], ['l_3, d_3', l3, dOf(l2)], ['l_1 + 2 l_2, d_1 + 2 d_2', unflat(flat(L1).map((x, i) => x + 2 * flat(l2)[i])), d1 + 2 * dOf(L1)]];
for (const [name, L, d] of alts) {
  if (!oc(L, d) || flat(L).some((x, i) => (x - flat(L1)[i]) % 2) || (d - d1) % 2) { console.log('bad alternative ' + name); all = false; continue; }
  const same = NAMES.every((T) => [-1, 1].every((w) => canon(encode(F(T, null, 0, w, L, d), false)) === canon(enc[T + w])));
  console.log(`parity lemma corroboration with (${name}): skeletons ${same ? 'identical' : 'DIFFERENT'} for all 18 cases`);
  all = all && same;
}
// ---- optional: compare with the skeletons extracted from the actual supertiles, levels 2..MAXL (stage B)
if (MAXL >= 2) {
  const { load } = require('./lib.js');
  const Dx = load(MAXL);
  for (let N = 2; N <= MAXL; N++) {
    const w = (N - 1) % 2 ? -1 : 1;   // children of a level-N supertile have level N-1
    const same = NAMES.every((T) => canon(enc[T + w]) === canon(Dx.ENC[T][N]));
    console.log(`level ${N}: actual skeletons (direct composition, floating point) = S_T(l_1, d_1, ${w > 0 ? '+1' : '-1'}) for all nine kinds: ${same}`);
    all = all && same;
  }
}
console.log(all ? 'INDUCTION STEP VERIFIED (18 skeletons)' + (MAXL >= 2 ? ', AND EQUAL TO THE ACTUAL SKELETONS AT LEVELS 2..' + MAXL : '') : 'INDUCTION STEP FAILED');
if (!all) process.exit(1);
