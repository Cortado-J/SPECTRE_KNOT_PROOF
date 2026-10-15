// Run Kaplan's implementation of the spectre's substitution (spectre.js, the program of the spectre authors'
// interactive application, https://cs.uwaterloo.ca/~csk/spectre/; not included here, see kaplan_compare.py) and
// write, as JSON, every tile of every supertile of levels 0..L in its drawing order: its label (the kind of its
// level-0 supertile; Gamma1 and Gamma2 for the Mystic's two tiles), its 14 vertices, and which level-1 supertile it
// lies in (with that supertile's kind and placement); and the key points of each level.
// The file runs in a V8 context of its own with no access to node (no require, process or file system); the only
// names it is given are the four p5.js names its geometry uses (PI, cos, sin, radians), defined inside that context.
// Of its functions only buildSpectreBase (straight edges: Tile(1,1)) and buildSupertiles are called.
// usage: node crosscheck/kaplan_run.js PATH/TO/spectre.js OUT.json [L=4]
'use strict';
const vm = require('vm'), fs = require('fs');
const [src, out, Ls] = process.argv.slice(2);
const L = +(Ls || 4);
const ctx = vm.createContext(Object.create(null));
vm.runInContext('var PI = Math.PI, cos = Math.cos, sin = Math.sin; function radians(d) { return d * PI / 180; }', ctx);
vm.runInContext(fs.readFileSync(src, 'utf8'), ctx, { filename: 'spectre.js', timeout: 10000 });
const json = vm.runInContext(`(function (L) {
  let sys = buildSpectreBase(false);
  const tag = (s, m) => { for (const k of tile_names) { s[k].kind_ = k; s[k].level_ = m; } };
  tag(sys, 0);
  function flat(g, S, tiles, insts) {   // the tiles of g placed by S, in drawing order
    if (g instanceof Meta) {
      if (g.level_ === 1) insts.push({ kind: g.kind_, S: S });
      for (const c of g.geoms) flat(c.geom, mul(S, c.xform), tiles, insts);
    } else {
      tiles.push({ label: g.label, inst: insts.length - 1,
                   pts: g.pts.map(p => { const q = transPt(S, p); return [q.x, q.y]; }) });
    }
  }
  const out = { levels: [] };
  for (let m = 0; m <= L; ++m) {
    const lev = { quad: sys['Delta'].quad.map(p => [p.x, p.y]), kinds: {} };
    for (const k of tile_names) {
      const tiles = [], insts = [];
      flat(sys[k], ident, tiles, insts);
      lev.kinds[k] = { tiles: tiles, insts: insts };
    }
    out.levels.push(lev);
    if (m < L) { sys = buildSupertiles(sys); tag(sys, m + 1); }
  }
  return JSON.stringify(out);
})(${L})`, ctx, { timeout: 300000 });
if (typeof json !== 'string') throw new Error('spectre.js gave no output');
fs.writeFileSync(out, json);
