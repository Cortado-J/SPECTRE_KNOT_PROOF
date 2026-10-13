// Remark 10.1 (experiment, not part of the proof): the label bookkeeping of Section 9 (hierarchy/chains_label.js) along
// chains chosen at random, step by step. X_b has a random kind; at each level the parent of the current supertile is
// drawn uniformly from all pairs (parent kind T, child number c) of Table 1 whose child c has the current kind.
// Records the first level N <= 20 at which all the arcs of X_b lie on a single arc of X_N.
// usage: node random_chains.js <b> [chains = 30000] [seed = 1]      (about 10 minutes per 30,000 chains)
const b = +process.argv[2], n = +(process.argv[3] || 30000), seed0 = +(process.argv[4] || 1); let seed = seed0 >>> 0;
process.argv.length = 2;   // synth.js reads its own command-line arguments when loaded
const { initState, advance } = require('../hierarchy/chains_label.js');
const { ST } = require('../hierarchy/synth.js');
const rnd = () => { seed = (seed + 0x6D2B79F5) >>> 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
const KINDS = Object.keys(ST);
const parents = {}; KINDS.forEach((K) => { parents[K] = []; });
KINDS.forEach((T) => ST[T].kids.forEach((K, c) => parents[K].push([T, c])));
const TOP = 20; const first = {}; const fails = []; let steps = 0;
for (let i = 0; i < n; i++) {
  const K0 = KINDS[Math.floor(rnd() * KINDS.length)];
  let st = initState(b, K0, TOP + 2); let kind = K0; const chain = []; let hit = 0;
  for (let N = b + 1; N <= TOP; N++) {
    const opts = parents[kind]; const [T, c] = opts[Math.floor(rnd() * opts.length)];
    const [s2, row] = advance(st, T, c); st = s2; kind = T; chain.push(`${T}:${c}`); steps++;
    if (row.loops) throw new Error('closed strand found: ' + chain.join(','));
    if (row.blocks === 1) { hit = N; break; }
  }
  if (hit) first[hit] = (first[hit] || 0) + 1; else fails.push(`${K0} ${chain.join(',')}`);
}
console.log(`b=${b}: ${n} chains (seed ${seed0}), ${steps} steps`);
console.log('  first level N at which the arcs of X_b lie on one arc of X_N: ' + Object.keys(first).sort((p, q) => p - q).map((N) => `${N}:${first[N]}`).join(' '));
console.log(`  not on one arc by level ${TOP}: ${fails.length}`);
fails.forEach((f) => console.log('    ' + f));
console.log(`b=${b}: ${n - fails.length} of ${n} chains reach a single arc by level ${TOP}`);
