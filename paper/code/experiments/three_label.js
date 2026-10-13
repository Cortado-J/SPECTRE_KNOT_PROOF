// Remark 10.1 (experiment, not part of the proof): the label bookkeeping of Section 9 along the same chain, to level 20.
// Per level: number of arcs of X_N that the arcs of X_b lie on; "c2" = 2 of them still carried on the rim stretch.
const { initState, advance } = require('../hierarchy/chains_label.js');
// pure periodic chain: ... Gamma is child 7 of Theta, Theta is child 2 of Gamma, ...
for (const [b, K0] of [[1, 'Gamma'], [2, 'Gamma'], [3, 'Gamma'], [1, 'Theta'], [2, 'Theta'], [3, 'Theta']]) {
  let st = initState(b, K0, 22); const out = [];
  let kind = K0;
  for (let N = b + 1; N <= 20; N++) {
    const step = kind === 'Gamma' ? ['Theta', 7] : ['Gamma', 2];
    const [s2, row] = advance(st, step[0], step[1]); st = s2; kind = step[0];
    out.push(`${row.blocks}${row.carried ? 'c' + row.carried : ''}`);
  }
  console.log(`b=${b} ${K0}: blocks per level ${b + 1}..20: ${out.join(' ')}`);
}
