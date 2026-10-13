// design selection shared by the figure / check scripts: DSG=01 (default, 0.1:01 on the 14-spoke fan) or DSG=0222221
const SETS = {
  '01': { name: '0.1:01', fam: 'fan21', digits: '01222222222222', perTile: 14, args: ['edge', 0.18, 12, 0.15], eps: 0.14, defLabels: ['0', '1'] },
  '0222221': { name: '0222221', fam: 'fan14', digits: '0222221', perTile: 7, args: ['edge', 0.22, 12, 0.18], eps: 0.18, defLabels: ['0', '11'] },
};
const D = SETS[process.env.DSG || '01'];
process.env.FAM = D.fam;
const FANS = { fan21: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], fan14: [0, 2, 4, 6, 8, 9, 11] };
D.design = { edges: 0, spokes: {} }; FANS[D.fam].forEach((i, k) => { D.design.spokes['s' + i] = +D.digits[k]; });
// build the engine knot on a list of engine tiles
D.knot = (ENG, tiles, extra) => ENG.build(ENG.cellsFan(tiles, ENG.FAN[D.fam]), D.args[0], D.args[1], D.args[2], D.args[3], Object.assign({ eps: D.eps, design: D.design, fanKind: D.fam }, extra || {}));
module.exports = D;
