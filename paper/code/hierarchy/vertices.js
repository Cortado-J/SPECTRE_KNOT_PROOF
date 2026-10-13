// Step 1: find the "hexagon vertices" of every kind at level m as the rim points where the neighbouring level-m
// supertile changes, observed inside level-(m+d) supertiles (d = 1..depth). Positions are given in the piece's own
// ccw cycle, relative to its defect A. Also counts how many pieces meet at each such point.
// usage: node vertices.js <maxM> <depth>
const MAXM = +(process.argv[2] || 4), DEPTH = +(process.argv[3] || 2);
const { NAMES, det, vert, tp, key, load, shapeAt, descendants } = require('./lib.js');
const D = load(MAXM + DEPTH);
const result = {};
for (let m = 0; m <= MAXM; m++) {
  const seen = {}; NAMES.forEach((s) => { seen[s] = new Map(); });
  const deg = new Map();
  for (let d = 1; d <= DEPTH; d++) {
    const M = m + d;
    for (const t of NAMES) {
      const ps = descendants(D, M, t, m);
      const edgeOwners = new Map();   // edge key -> [piece idx]
      const pv = [];                  // per piece: array of vertex keys
      const vcount = new Map();
      ps.forEach((p, i) => {
        const sh = shapeAt(D, m, p.kind); const ks = [];
        for (let k = 0; k < sh.E; k++) ks.push(key(tp(p.T, vert(sh, k))));
        pv.push(ks);
        for (let k = 0; k < sh.E; k++) {
          const a = ks[k], b = ks[(k + 1) % sh.E]; const ek = a < b ? a + '|' + b : b + '|' + a;
          if (!edgeOwners.has(ek)) edgeOwners.set(ek, []); edgeOwners.get(ek).push(i);
          if (!vcount.has(a)) vcount.set(a, new Set()); vcount.get(a).add(i);
        }
      });
      ps.forEach((p, i) => {
        const sh = shapeAt(D, m, p.kind); const ks = pv[i]; const E = sh.E;
        const nb = (k) => { const a = ks[k], b = ks[(k + 1) % E]; const l = edgeOwners.get(a < b ? a + '|' + b : b + '|' + a); if (l.length > 2) throw new Error('3 owners'); return l.length === 1 ? -1 : (l[0] === i ? l[1] : l[0]); };
        for (let k = 0; k < E; k++) {
          const n0 = nb((k + E - 1) % E), n1 = nb(k);
          if (n0 !== n1) {
            const rel = (k - sh.defA + E) % E;
            const mp = seen[p.kind]; mp.set(rel, (mp.get(rel) || 0) + 1);
            const c = vcount.get(ks[k]).size; deg.set(c, (deg.get(c) || 0) + 1);
          }
        }
      });
    }
  }
  result[m] = {};
  const line = [];
  for (const s of NAMES) { const sh = shapeAt(D, m, s); const pos = [...seen[s].keys()].sort((a, b) => a - b); result[m][s] = { E: sh.E, defB: (sh.defB - sh.defA + sh.E) % sh.E, pos }; line.push(`${s}(E=${sh.E},B=${result[m][s].defB}): ${pos.join(',')}`); }
  console.log(`m=${m}: pieces-meeting counts at junctions ${JSON.stringify([...deg])}`);
  for (const l of line) console.log('   ' + l);
}
require('fs').writeFileSync(__dirname + `/vertices_${MAXM}_${DEPTH}.json`, JSON.stringify(result));
