// Step 3: the side-length recurrence l_{m+1} = M l_m, the defect offset, and the mod-2 analysis.
// usage: node recur.js combin_<L>.json
const fs = require('fs');
const J = JSON.parse(fs.readFileSync(process.argv[2]));
const NAMES = ['Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Phi', 'Psi'];
const levels = Object.keys(J.ST).map(Number).sort((a, b) => a - b);
const L = Math.max(...Object.keys(J.LEN).map(Number));
// 1. structure identical at every level
const ref = JSON.stringify(J.ST[levels[0]], (k, v) => (k === 'pdef' ? { side: v.side, atVertex: v.off === 0 } : v));
for (const m of levels) {
  const s = JSON.stringify(J.ST[m], (k, v) => (k === 'pdef' ? { side: v.side, atVertex: v.off === 0 } : v));
  console.log(`structure C_${m} (composition ${m}->${m + 1}) ${s === ref ? 'identical to' : 'DIFFERS from'} C_${levels[0]}; A inherited from the Gamma child in all kinds: ${NAMES.every((T) => J.ST[m][T].ainh)}`);
}
const ST = J.ST[levels[0]];
// 2. matrix M (54 x 54), index (s, j) -> 6*s + j
const idx = (s, j) => 6 * NAMES.indexOf(s) + j;
const M = []; for (let i = 0; i < 54; i++) M.push(new Array(54).fill(0));
for (const T of NAMES) ST[T].pside.forEach((seq, Jx) => seq.forEach((tag) => { const [c, j] = tag.split('.').map(Number); M[idx(T, Jx)][idx(ST[T].kids[c], j)] += 1; }));
const vec = (m) => { const v = []; for (const s of NAMES) for (let j = 0; j < 6; j++) v.push(J.LEN[m][s][j]); return v; };
const apply = (A, v) => A.map((row) => row.reduce((a, x, i) => a + x * v[i], 0));
let ok = true;
for (let m = levels[0]; m < L; m++) { const p = apply(M, vec(m)), q = vec(m + 1); const good = p.every((x, i) => x === q[i]); ok = ok && good; console.log(`l_${m + 1} = M l_${m}: ${good ? 'yes' : 'NO'}`); }
// row sums / structure of M
console.log('M: nonnegative integer 54x54, row sums', [...new Set(M.map((r) => r.reduce((a, b) => a + b, 0)))].join(','));
console.log('M rows (parent side (T,J) = sum of child sides):');
for (const T of NAMES) for (let Jx = 0; Jx < 6; Jx++) { const r = M[idx(T, Jx)]; const terms = []; r.forEach((x, i) => { if (x) terms.push(`${x > 1 ? x + '*' : ''}${NAMES[Math.floor(i / 6)].slice(0, 3)}${i % 6}`); }); console.log(`  ${T.slice(0, 3)}${Jx} = ${terms.join(' + ')}`); }
// 3. defect offset of Sigma: A = Gamma child's vertex 0; offset along the parent side from its start vertex
for (const T of NAMES) {
  const { pdef, pside, kids } = ST[T]; const seq = pside[pdef.side]; const gi = kids.length - 1; const terms = [];
  for (const tag of seq) { const [c, j] = tag.split('.').map(Number); if (c === gi && j === 5) break; terms.push([kids[c], j]); if (c === gi && j === 0) break; }
  const pred = (m) => terms.reduce((a, [s, j]) => a + J.LEN[m][s][j], 0);
  const chk = []; for (let m = levels[0]; m < L; m++) chk.push(pred(m) === J.DEF[m + 1][T].off && pdef.side === J.DEF[m + 1][T].side);
  console.log(`A of ${T}: side ${pdef.side}, offset = ${terms.length ? terms.map(([s, j]) => s.slice(0, 3) + j).join(' + ') + ' (child lengths)' : '0'}; matches computed at levels ${levels[0] + 1}..${L}: ${chk.every((x) => x)}`);
}
// 4. mod 2
const mod2 = (v) => v.map((x) => ((x % 2) + 2) % 2);
for (let m = levels[0]; m <= L; m++) console.log(`v_${m} = l_${m} mod 2 = ${mod2(vec(m)).join('')}`);
const v1 = mod2(vec(levels[0])); const Mv1 = mod2(apply(M, v1));
console.log(`M v_${levels[0]} == v_${levels[0]} (mod 2): ${Mv1.every((x, i) => x === v1[i])}`);
// order of M mod 2, and the dimension of the fixed space, rank of (M-I) and (M-I)^2 over F2
const mm = (A, B) => A.map((r) => B[0].map((_, j) => r.reduce((a, x, k) => a ^ (x & B[k][j]), 0)));
const M2 = M.map((r) => r.map((x) => x & 1));
const I = M2.map((r, i) => r.map((_, j) => (i === j ? 1 : 0)));
const rank = (A) => { const a = A.map((r) => r.slice()); let rk = 0; const n = a.length, c = a[0].length; for (let col = 0; col < c && rk < n; col++) { let p = -1; for (let i = rk; i < n; i++) if (a[i][col]) { p = i; break; } if (p < 0) continue; [a[rk], a[p]] = [a[p], a[rk]]; for (let i = 0; i < n; i++) if (i !== rk && a[i][col]) for (let k = 0; k < c; k++) a[i][k] ^= a[rk][k]; rk++; } return rk; };
const sub = (A, B) => A.map((r, i) => r.map((x, j) => x ^ B[i][j]));
const MI = sub(M2, I);
console.log(`over F2: rank(M) = ${rank(M2)}, rank(M - I) = ${rank(MI)}, rank((M - I)^2) = ${rank(mm(MI, MI))}, rank((M-I)^3) = ${rank(mm(mm(MI, MI), MI))}`);
let P = M2, seen = [JSON.stringify(P)]; for (let k = 2; k <= 40; k++) { P = mm(P, M2); const s = JSON.stringify(P); const i = seen.indexOf(s); if (i >= 0) { console.log(`powers of M mod 2: M^${k} = M^${i + 1}, so preperiod ${i + 1}, period ${k - i - 1}`); break; } seen.push(s); }
// real growth
let v = vec(L).map(Number); const r = vec(L).map((x, i) => x / vec(L - 1)[i]); console.log(`ratios l_${L}/l_${L - 1}: ${Math.min(...r).toFixed(4)}..${Math.max(...r).toFixed(4)} (phi^3 = ${(((1 + Math.sqrt(5)) / 2) ** 3).toFixed(4)})`);
console.log('min side length per level:', levels.concat([L]).map((m) => Math.min(...vec(m))).join(' '));
fs.writeFileSync(__dirname + '/M.json', JSON.stringify({ M, NAMES }));
