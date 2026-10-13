// The tile's own tangle (paper, Section 3): print the 14 pieces of design 0.1:01 as pairs of ports and check that
// they are exactly the hooks at v_2, ..., v_13 and the crossover at the edge v_0 v_1.
// Port 'i,0' is on edge e_i = v_i v_{i+1} near v_i; port 'i,1' is on e_i near v_{i+1}.
// In the paper's notation R(v_i) = (e_i near v_i) = 'i,0' and L(v_i) = (e_{i-1} near v_i) = '(i-1),1'.
// usage: node tile.js
process.argv[2] = 'fan21'; process.argv[3] = '01222222222222';
const H = require('./hier.js');
const t = H.tileTangle('01222222222222');
const R = (i) => `${i},0`, L = (i) => `${(i + 13) % 14},1`;
const name = (p) => { const [e, s] = p.split(',').map(Number); return s === 0 ? `R(v${e})` : `L(v${(e + 1) % 14})`; };
const want = new Map();
const pairUp = (a, b) => { want.set(a, b); want.set(b, a); };
for (let i = 2; i < 14; i++) pairUp(L(i), R(i));     // hooks
pairUp(R(0), R(1)); pairUp(L(0), L(1));               // crossover
const seen = new Set(); const pieces = [];
for (const [a, b] of t.pair) { if (seen.has(a)) continue; seen.add(a); seen.add(b); pieces.push(`${name(a)}-${name(b)}`); }
console.log(`tile of design 0.1:01: ${t.pair.size} ports, ${pieces.length} pieces, closed loops ${t.loops}`);
console.log('  ' + pieces.join('  '));
const ok = t.pair.size === 28 && t.loops === 0 && [...want].every(([a, b]) => t.pair.get(a) === b);
console.log(ok ? 'TILE PAIRING = hooks at v2..v13 + crossover R(v0)-R(v1), L(v0)-L(v1): OK' : 'TILE PAIRING MISMATCH');
if (!ok) process.exit(1);
