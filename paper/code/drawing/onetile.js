// how many strands of the level-L block pass through each tile of the nest's 9-tile block N1, L = 1..TOP
const DS = require('./dsg.js');
const fs = require('fs');
const TOP = +(process.argv[2] || 5);
const { build } = require('../core/reduce.js');
const H = require('../core/hier.js');
const { PTS, KERNEL, IDENT, mul, trot, ttrans, tp, SR } = H;
const engSrc = fs.readFileSync(__dirname + '/engine.js', 'utf8').replace('return { create, makeTiles, PTS, KERNEL, FAN, HAND_DESIGNS, designKey };', 'return { create, makeTiles, PTS, KERNEL, FAN, HAND_DESIGNS, designKey, build, cellsFan };').replace('const res = res0; res.strands = []; res.crossings = []; res.faces = [];', 'const res = res0; res.strands = []; res.crossings = []; res.faces = []; res.raw = strands;');
const ENG = eval(engSrc + '; SpectreEngine');
const { LEV } = build(DS.digits, TOP, true);
const G2 = mul(ttrans(PTS[8][0], PTS[8][1]), trot(Math.PI / 6));
function tileTransforms(t, L, T) { if (L === 0) return t === 'Gamma' ? [T, mul(T, G2)] : [T]; const trs = LEV[L - 1].trs; const out = []; SR[t].forEach((s, i) => { if (s) out.push(...tileTransforms(s, L - 1, mul(T, trs[i]))); }); return out; }
function engineTiles(Ts) { return Ts.map((T) => { const P0 = PTS.map((p) => tp(T, p)); let a = 0; for (let i = 0; i < 14; i++) { const q = P0[(i + 1) % 14]; a += P0[i][0] * q[1] - q[0] * P0[i][1]; } const rev = a < 0; return { P: rev ? P0.slice().reverse() : P0, rev, kc: tp(T, KERNEL) }; }); }
function chainT(b, L) { let T = IDENT; for (let k = L; k > b; k--) T = mul(T, LEV[k - 1].trs[1]); return T; }
const cen = (T) => { const c = tp(T, [1.5, 0.75]); return Math.round(c[0] * 100) + ',' + Math.round(c[1] * 100); };
const baseTs = tileTransforms('Delta', 1, IDENT);
const rows = baseTs.map(() => []);
for (let L = 1; L <= TOP; L++) {
  const Ts = tileTransforms('Delta', L, IDENT);
  const res = DS.knot(ENG, engineTiles(Ts), {});
  if (!res.raw) throw new Error('no raw');
  const C = chainT(1, L); const idx = new Map(); Ts.forEach((T, i) => idx.set(cen(T), i));
  const through = new Map();   // tile -> set of strands
  res.raw.forEach(([seq], k) => { for (const [seg] of seq) { const t = Math.floor(Math.floor(seg / 128) / DS.perTile); if (!through.has(t)) through.set(t, new Set()); through.get(t).add(k); } });
  baseTs.forEach((T, j) => { const i = idx.get(cen(mul(C, T))); rows[j].push(i === undefined ? '?' : through.get(i).size); });
  console.log('level', L, 'tiles', Ts.length, 'strands', res.raw.length);
}
rows.forEach((r, j) => console.log('tile', j, 'strands through it at levels 1..' + TOP + ':', r.join(' ')));
