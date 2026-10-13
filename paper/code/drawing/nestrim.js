// How much of the nest base N_b's rim lies on the rim of N_{b+k}?  (child-1 chain of Delta)
const H = require('../core/hier.js');
const { PTS, IDENT, mul, trot, ttrans, tp, QUAD, vkey, levelTransforms, NAMES, SR } = H;
const MAXL = +(process.argv[4] || 7);
const t = H.tileTangle();
let shapes = {}; for (const n of NAMES) shapes[n] = t;
shapes.Gamma = H.compose([{ shape: t, T: IDENT }, { shape: t, T: mul(ttrans(PTS[8][0], PTS[8][1]), trot(Math.PI / 6)) }], -1);
let quad = QUAD; const per = [];
for (let N = 1; N <= MAXL; N++) { const { trs, superQuad } = levelTransforms(quad); const next = {}; for (const ty of NAMES) { const kids = []; SR[ty].forEach((s, i) => { if (s) kids.push({ shape: shapes[s], T: trs[i] }); }); next[ty] = H.compose(kids, -1); } per.push({ trs, shapes: next }); shapes = next; quad = superQuad; }
const ek = (P, Q) => { const a = vkey(P), b = vkey(Q); return a < b ? a + '|' + b : b + '|' + a; };
for (let b = 1; b <= MAXL - 1; b++) {
  let T = IDENT; const base = per[b - 1].shapes.Delta; const out = [];
  for (let k = 1; b + k <= MAXL; k++) {
    T = mul(per[b + k - 1].trs[1], T);
    const anc = per[b + k - 1].shapes.Delta; const rim = new Set(anc.edges.map((ed) => ek(ed.p, ed.q)));
    let n = 0; for (const ed of base.edges) if (rim.has(ek(tp(T, ed.p), tp(T, ed.q)))) n++;
    out.push(`k=${k}: ${n}`);
  }
  console.log(`base level ${b} (rim ${base.edges.length}): edges on the rim of N_{b+k}: ${out.join(', ')}`);
}
