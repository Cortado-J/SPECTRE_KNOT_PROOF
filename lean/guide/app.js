/* The page engine of the proof map's Statement.lean page (statement.html): renders Statement.lean (embedded by build_guide.py) with the explanations
   of content.js, the figures, the glossary pop-ups and the reading ticks. No libraries. */
(function () {
'use strict';
const G = window.GUIDE, D = window.GUIDE_DATA;
const LINES = D.src.replace(/\n$/, '').split('\n');
const NL = LINES.length;
const $ = (s, el) => (el || document).querySelector(s);
const $$ = (s, el) => Array.from((el || document).querySelectorAll(s));
const esc = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
const SUB = '₀₁₂₃₄₅₆₇₈₉', sub = n => String(n).split('').map(c => SUB[+c] || c).join('');
const fmt = n => n.toLocaleString('en-GB');

/* ---------- browser storage (optional: everything works without it) ---------- */
const store = {
  get(k, d) { try { const v = localStorage.getItem(k); return v === null ? d : v; } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem(k, v); } catch (e) { /* not available */ } },
  del(k) { try { localStorage.removeItem(k); } catch (e) { /* not available */ } },
};
function fnv(s) { let h = 0x811c9dc5; for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 0x01000193); } return (h >>> 0).toString(36); }

/* ---------- names ---------- */
const ITEMS = G.items, BYID = {};
ITEMS.forEach(it => { BYID[it.id] = it; });
const SKIP = new Set(['comment', 'import', 'namespace', 'section', 'end']);
const DEF = {};
ITEMS.forEach(it => { if (!SKIP.has(it.kind)) { DEF[it.title] = it.id; if (it.alias) DEF[it.alias] = it.id; } });
['tiles', 'glue', 'rim', 'vtx'].forEach(f => { DEF[f] = 'Patch'; });
const MEMBERS = G.members || {};
/* the line holding `text` (the first one after the line holding `after`, if given): figures cite lines this way */
function lineOf(text, after) {
  let from = 0;
  if (after) from = LINES.findIndex(l => l.includes(after));
  const i = LINES.findIndex((l, k) => k >= from && l.includes(text));
  return i + 1;
}
const MODULES = {
  'SpectreKnot.Basic': 'SpectreKnot/Basic.lean: the nine kinds (Kind), the eight letters, and iter. This file uses Kind and iter; both are shown under Imports.',
  'SpectreKnot.Data.Pattern': 'SpectreKnot/Data/Pattern.lean, generated: the paper\'s Tables 1–4, the level-1 side lengths and d₁. This file uses Tables 1–3 (kids, adj, pside).',
  'SpectreKnot.Data.Clusters': 'SpectreKnot/Data/Clusters.lean, generated in exact arithmetic: the nine level-1 supertiles, tile by tile.',
  'SpectreKnot.Statement': 'The namespace of this file: every name defined here has this prefix.',
};
const KW = new Set(['import', 'namespace', 'end', 'abbrev', 'def', 'theorem', 'structure', 'where', 'inductive', 'variable', 'match', 'with', 'fun', 'let', 'if', 'then', 'else']);
const TY = new Set(['Prop', 'Nat', 'Bool', 'Option', 'List', 'Port', 'Patch', 'Tiling', 'Kind']);
const VAL = new Set(['true', 'false', 'some', 'none']);

const REG = [], USES = {};
const defInfo = (name, id) => ({ type: 'def', key: 'def:' + id + ':' + name, name, id });
function reg(info, line, file) {
  REG.push(info);
  if (file === 'S') { (USES[info.key] = USES[info.key] || new Set()).add(line); }
  return REG.length - 1;
}
function lookName(key, line, file) {
  if (file === 'S') {
    const sc = G.scoped.find(s => s.name === key && line >= s.lines[0] && line <= s.lines[1]);
    if (sc && sc.id) return defInfo(key, sc.id);
    if (sc) return { type: 'scoped', key: 'sc:' + key + ':' + sc.lines[0], name: key, sc };
  }
  if (DEF[key]) return defInfo(key, DEF[key]);
  if (G.glossary[key]) return { type: 'gl', key: 'gl:' + key, name: key };
  if (MODULES[key]) return { type: 'mod', key: 'mod:' + key, name: key };
  return null;
}
function lookMember(seg, recv) {
  if (/^\d+$/.test(seg)) return G.glossary['.' + seg] ? { type: 'gl', key: 'gl:.' + seg, name: '.' + seg } : null;
  if (recv && MEMBERS[recv] && MEMBERS[recv][seg]) return defInfo(seg, MEMBERS[recv][seg]);
  if (DEF[seg]) return defInfo(seg, DEF[seg]);
  if (G.glossary['.' + seg]) return { type: 'gl', key: 'gl:.' + seg, name: '.' + seg };
  return null;
}

/* ---------- tokeniser ---------- */
const IDENT = /^\.?[A-Za-z_Ͱ-Ͽ][A-Za-z0-9_'₀-₉Ͱ-Ͽ]*\??(?:\.(?:[A-Za-z_][A-Za-z0-9_'₀-₉]*\??|\d+))*/;
const SYM2 = [':=', '=>', '==', ']?'];
function tokenize(lines) {
  let inBlock = false; const out = [];
  for (const line of lines) {
    const toks = []; let i = 0;
    while (i < line.length) {
      if (inBlock) {
        const e = line.indexOf('-/', i);
        if (e < 0) { toks.push(['com', line.slice(i)]); i = line.length; } else { toks.push(['com', line.slice(i, e + 2)]); i = e + 2; inBlock = false; }
        continue;
      }
      const rest = line.slice(i); let m;
      if (rest.startsWith('/-')) {
        const e = line.indexOf('-/', i + 2);
        if (e < 0) { toks.push(['com', rest]); inBlock = true; i = line.length; } else { toks.push(['com', line.slice(i, e + 2)]); i = e + 2; }
        continue;
      }
      if (rest.startsWith('--')) { toks.push(['com', rest]); break; }
      if ((m = /^\s+/.exec(rest))) { toks.push(['ws', m[0]]); i += m[0].length; continue; }
      if ((m = /^\d+/.exec(rest))) { toks.push(['num', m[0]]); i += m[0].length; continue; }
      if ((m = IDENT.exec(rest))) { toks.push(['id', m[0]]); i += m[0].length; continue; }
      const s2 = SYM2.find(s => rest.startsWith(s));
      if (s2) { toks.push(['sym', s2]); i += 2; continue; }
      toks.push(['sym', rest[0]]); i += 1;
    }
    out.push(toks);
  }
  return out;
}
function tk(text, info, line, file, cls) {
  if (!info) return cls ? `<span class="${cls}">${esc(text)}</span>` : esc(text);
  const c = info.type === 'def' ? 'k-def' : info.type === 'scoped' ? 'k-loc' : info.type === 'mod' ? 'k-mod' : (cls || 'k-lib');
  return `<span class="tk ${c}" tabindex="0" role="button" data-r="${reg(info, line, file)}">${esc(text)}</span>`;
}
function renderChain(s, line, file) {
  const lead = s.startsWith('.');
  const parts = (lead ? s.slice(1) : s).split('.');
  let html = '', k = 0, recv = null;
  if (!lead) {
    let matched = 1, info = null;
    for (let m = parts.length; m >= 1; m--) {
      const r = lookName(parts.slice(0, m).join('.'), line, file);
      if (r) { matched = m; info = r; break; }
    }
    const head = parts.slice(0, matched).join('.');
    const cls = KW.has(head) ? 'kw' : TY.has(head) ? 'ty' : VAL.has(head) ? 'val' : '';
    html += tk(head, info, line, file, cls);
    if (info && info.type === 'scoped' && info.sc.recv && file === 'S') recv = info.sc.recv;
    k = matched;
  }
  for (; k < parts.length; k++) html += tk('.' + parts[k], lookMember(parts[k], recv), line, file, '');
  return html;
}
function renderLine(toks, line, file) {
  let html = '';
  for (const [t, s] of toks) {
    if (t === 'com') html += `<span class="com">${esc(s)}</span>`;
    else if (t === 'ws') html += s;
    else if (t === 'num') html += `<span class="num">${s}</span>`;
    else if (t === 'id') html += renderChain(s, line, file);
    else html += G.glossary[s] ? tk(s, { type: 'gl', key: 'gl:' + s, name: s }, line, file, 'sym') : esc(s);
  }
  return html;
}
const TOKS = tokenize(LINES);
const isComLine = toks => toks.length > 0 && toks.every(([t]) => t === 'com' || t === 'ws');
function codeBlock(a, b, file, toks, lines, prefix) {
  let html = '', all = true;
  for (let n = a; n <= b; n++) {
    const tks = toks[n - 1], cl = isComLine(tks);
    if (!cl && lines[n - 1].trim() !== '') all = false;
    const id = prefix + n;
    html += `<div class="ln${cl ? ' cl' : ''}" id="${id}"><a class="no" href="#${id}" aria-label="line ${n}">${n}</a><span class="tx">${renderLine(tks, n, file) || ' '}</span></div>`;
  }
  return `<div class="code${all ? ' allcom' : ''}"><div class="code-in">${html}</div><div class="hidden-note">Comment lines hidden</div></div>`;
}

/* ---------- prose markup: [[id]], [[id|text]], [[L123]] ---------- */
function mark(s) {
  return String(s || '').replace(/\[\[([^\]|]+)(?:\|([^\]]+))?\]\]/g, (m, ref, text) => {
    const L = /^L(\d+)$/.exec(ref);
    if (L) return `<a class="lref" href="#L${L[1]}">line ${L[1]}</a>`;
    const it = BYID[ref];
    if (!it) return esc(text || ref);
    return `<a class="xref" href="#item-${ref}">${text || `<code>${esc(it.title)}</code>`}</a>`;
  });
}

/* ---------- checks, examples ---------- */
const TONE = { ok: ['As intended', '✓'], note: ['Be aware', '!'], data: ['Outside Lean', '◆'] };
function checksHtml(list) {
  return (list || []).map(c => `<details class="check t-${c.tone}"${c.tone === 'ok' ? '' : ' open'}><summary class="check-h"><span class="badge">${TONE[c.tone][1]} ${TONE[c.tone][0]}</span> <strong>${esc(c.title)}</strong></summary><p>${mark(c.text)}</p></details>`).join('');
}
function howHtml(how) {
  return how ? `<details class="how"><summary>How the Lean says it</summary><p>${mark(how)}</p></details>` : '';
}
function examplesHtml(list) {
  if (!list || !list.length) return '';
  return `<div class="examples"><div class="lbl">Lean's own output <span class="lbl-sub">#eval</span></div>` + list.map(e =>
    `<div class="ex"><pre class="ex-in">${esc(e.expr.startsWith('--') ? e.expr : '#eval ' + e.expr)}</pre><pre class="ex-out">${esc(e.out)}</pre>${e.note ? `<p class="ex-note">${mark(e.note)}</p>` : ''}</div>`).join('') + `</div>`;
}
function explHtml(o, isClause) {
  return `${isClause && o.title ? `<h4>${esc(o.title)}</h4>` : ''}` +
    (o.what ? `<div class="what"><p>${mark(o.what)}</p></div>` : '') + howHtml(o.how) +
    examplesHtml(o.examples) + checksHtml(o.checks);
}

/* ---------- what each piece uses, and where it is used ---------- */
const itemOfLine = n => ITEMS.find(it => it.lines[0] <= n && n <= it.lines[1]);
const DEPS = (() => {
  TOKS.forEach((t, i) => renderLine(t, i + 1, 'S'));   // fills USES: the lines on which each name is used
  const uses = {}, usedBy = {};
  Object.keys(USES).forEach(key => {
    if (!key.startsWith('def:')) return;
    const id = key.split(':')[1];
    USES[key].forEach(n => {
      const it = itemOfLine(n);
      if (!it || it.id === id || SKIP.has(it.kind)) return;
      (uses[it.id] = uses[it.id] || new Set()).add(id);
      (usedBy[id] = usedBy[id] || new Set()).add(it.id);
    });
  });
  return { uses, usedBy };
})();
const ORDER = {}; ITEMS.forEach((it, k) => { ORDER[it.id] = k; });
const chipsHtml = set => Array.from(set || []).sort((a, b) => ORDER[a] - ORDER[b])
  .map(id => `<a class="dchip" href="#item-${id}"><code>${esc(BYID[id].title)}</code></a>`).join(' ');
function depsHtml(id) {
  const u = DEPS.uses[id], b = DEPS.usedBy[id];
  if (!u && !b) return '';
  return `<div class="deps">${u ? `<span><span class="dl">Uses</span> ${chipsHtml(u)}</span>` : ''}${b ? `<span><span class="dl">Used by</span> ${chipsHtml(b)}</span>` : ''}</div>`;
}

/* ---------- items ---------- */
const readKey = it => 'skg-read:' + it.id + ':' + fnv(LINES.slice(it.lines[0] - 1, it.lines[1]).join('\n'));
const KINDNAME = { comment: 'comment', import: 'import', namespace: 'namespace', section: 'heading', abbrev: 'abbrev', def: 'def', structure: 'structure', inductive: 'inductive', claim: 'def : Prop', end: 'end' };
const linesLabel = ([a, b]) => a === b ? `line ${a}` : `lines ${a}–${b}`;

function itemHtml(it) {
  const head = `<header class="item-h"><div class="item-t"><span class="kind k-${it.kind}">${KINDNAME[it.kind]}</span><h3>${esc(it.title)}</h3><a class="item-lines" href="#L${it.lines[0]}">${linesLabel(it.lines)}</a></div>` +
    (it.summary ? `<p class="item-sum">${esc(it.summary)}</p>` : '') +
    `<label class="read"><input type="checkbox" id="read-${it.id}" data-id="${it.id}"> Read and agreed</label></header>`;
  let body = '';
  if (it.clauses) {
    body += `<div class="intro">${explHtml({ what: it.what, how: it.how }, false)}</div>`;
    body += it.clauses.map(c => `<div class="row">${codeBlock(c.lines[0], c.lines[1], 'S', TOKS, LINES, 'L')}<div class="expl">${explHtml(c, true)}</div></div>`).join('');
  } else {
    body += `<div class="row">${codeBlock(it.lines[0], it.lines[1], 'S', TOKS, LINES, 'L')}<div class="expl">${explHtml({ what: it.what, how: it.how, examples: it.examples, checks: it.checks }, false)}</div></div>`;
  }
  if (it.extra === 'basic') body += basicHtml();
  if (it.fig) body += `<div class="fig" data-fig="${it.fig}"></div>`;
  if (it.clauses) body += `<div class="item-foot">${examplesHtml(it.examples)}${checksHtml(it.checks)}</div>`;
  body += depsHtml(it.id);
  return `<article class="item kind-${it.kind}" id="item-${it.id}">${head}${body}</article>`;
}
function sectionItemHtml(it) {
  return `<div class="sec-code" id="item-${it.id}">${codeBlock(it.lines[0], it.lines[1], 'S', TOKS, LINES, 'L')}</div>`;
}
function basicHtml() {
  const bl = D.basic.split('\n'), bt = tokenize(bl), off = D.basicStart - 1;
  const toks = new Array(off).fill([]).concat(bt), lines = new Array(off).fill('').concat(bl);
  return `<div class="basic"><div class="lbl">From <code>SpectreKnot/Basic.lean</code>, lines ${D.basicStart}–${D.basicStart + bl.length - 1}: the two definitions this file uses</div>` +
    codeBlock(D.basicStart, D.basicStart + bl.length - 1, 'B', toks, lines, 'B') +
    `<p class="basic-note">${mark(`<code>Kind</code> has nine values, one per supertile kind; <code>deriving DecidableEq, Repr</code> lets Lean compare and print them. <code>Letter</code> is not used here. <code>iter f n x</code> applies <code>f</code> to <code>x</code>, <code>n</code> times, defined by recursion on <code>n</code>; it is used only in [[TheoremB_strand|TheoremB_strand]] and [[TheoremA_strand|TheoremA_strand]]. The two theorems after it in <code>Basic.lean</code> are facts about <code>iter</code>, not definitions.`)}</p></div>`;
}

/* ---------- coverage (build_guide.py checks this too) ---------- */
function coverage() {
  const errs = []; let next = 1;
  ITEMS.forEach(it => {
    if (it.lines[0] !== next) errs.push(`${it.id} starts at ${it.lines[0]}, expected ${next}`);
    next = it.lines[1] + 1;
    if (it.clauses) {
      let c0 = it.lines[0];
      it.clauses.forEach(c => { if (c.lines[0] !== c0) errs.push(`${it.id}: clause at ${c.lines[0]}, expected ${c0}`); c0 = c.lines[1] + 1; });
      if (c0 !== it.lines[1] + 1) errs.push(`${it.id}: clauses end at ${c0 - 1}`);
    }
  });
  if (next !== NL + 1) errs.push(`items end at ${next - 1}; the file has ${NL} lines`);
  return errs;
}

/* ---------- page ---------- */
function build() {
  const main = $('#main');
  const errs = coverage();
  let html = '';
  if (G.writtenFor !== D.sha) html += `<div class="banner warn"><strong>Statement.lean has changed</strong> since these explanations were written (${esc(G.written)}). The code shown is the current file; some explanations may describe older lines. Reading ticks on changed items have been cleared.</div>`;
  if (errs.length) html += `<div class="banner warn"><strong>Line coverage problem:</strong> ${esc(errs.join('; '))}</div>`;
  html += $('#tpl-intro').innerHTML;
  html += trustHtml() + primerHtml() + startHtml();
  G.sections.forEach(sec => {
    const its = ITEMS.filter(it => it.section === sec.id);
    html += `<section class="sec" id="${sec.id}"><h2>${esc(sec.title)}</h2>`;
    its.forEach(it => { html += it.kind === 'section' ? sectionItemHtml(it) : itemHtml(it); });
    html += `</section>`;
  });
  html += reviewHtml() + glossaryHtml();
  main.innerHTML = html;
  $('#toc').innerHTML = tocHtml();
  $('#toc-m').innerHTML = tocHtml();
  $$('.fig').forEach(el => FIGS[el.dataset.fig] && FIGS[el.dataset.fig](el));
  $('#src-sha').textContent = D.sha.slice(0, 12);
}
function primerHtml() {
  const code = c => c.split('\n').map(l => renderLine(tokenize([l])[0], 0, 'P')).join('\n');
  return `<section class="sec" id="primer"><h2>Lean for this file</h2><p class="lede">Enough Lean to read the file, in
    ${G.primer.length} short pieces, each with an example from it. In the code further down, every coloured word can be
    clicked for its meaning, and the <a href="#glossary">glossary</a> lists them all.</p><div class="primer">` +
    G.primer.map((p, k) => `<div class="pr"><h3><span class="pr-n">${k + 1}</span>${esc(p.title)}</h3><pre class="pr-code">${code(p.code)}</pre><p>${mark(p.text)}</p></div>`).join('') +
    `</div></section>`;
}
const START = ['TheoremB_strand', 'TheoremA_strand', 'TheoremB', 'TheoremB_sharp', 'TheoremB_exact', 'Grandparent',
  'NestModel', 'TheoremA', 'ChainModel', 'NestCovers'];
function startHtml() {
  return `<section class="sec" id="start"><h2>Where to start</h2><p class="lede">The file is written from the bottom
    up: small definitions first, the claims at the end. To read it, go the other way: pick a claim, then follow the
    names it uses. Every piece below lists what it uses and where it is used. The two final claims are the first two
    here; the others are steps on the way, proved too.</p><ol class="start">` +
    START.map(id => { const it = BYID[id]; return `<li><div><a class="st-name" href="#item-${id}"><code>${esc(it.title)}</code></a> <span class="st-sum">${esc(it.summary)}</span></div>` +
      (DEPS.uses[id] ? `<div class="st-uses"><span class="dl">Uses</span> ${chipsHtml(DEPS.uses[id])}</div>` : '') + `</li>`; }).join('') +
    `</ol></section>`;
}
function trustHtml() {
  const ST = { build: ['Checked by the build', 's-build'], read: ['Your reading: this page', 's-read'], tested: ['Tested, not proved', 's-tested'], assumed: ['Assumed', 's-assumed'] };
  return `<section class="sec" id="trust"><h2>What has to hold</h2><p class="lede">For the theorems to mean what the paper says, six things must hold. The build checks the first three; the fourth is the reading this page supports; the last two lie outside Lean.</p><ol class="trust">` +
    G.trust.map(t => `<li><div class="trust-h"><span class="st ${ST[t.status][1]}">${ST[t.status][0]}</span><strong>${esc(t.title)}</strong></div><p>${mark(t.text)}</p></li>`).join('') + `</ol></section>`;
}
function reviewHtml() {
  const notes = [];
  ITEMS.forEach(it => {
    const add = (c, where) => { if (c.tone !== 'ok') notes.push({ c, it, where }); };
    (it.checks || []).forEach(c => add(c, it.title));
    (it.clauses || []).forEach(cl => (cl.checks || []).forEach(c => add(c, it.title + ': ' + (cl.title || ''))));
  });
  const nOk = ITEMS.reduce((n, it) => n + (it.checks || []).filter(c => c.tone === 'ok').length + (it.clauses || []).reduce((m, cl) => m + (cl.checks || []).filter(c => c.tone === 'ok').length, 0), 0);
  return `<section class="sec" id="review"><h2>Findings of this reading</h2>
    <p class="lede">Every piece was read against the paper's definitions and its own comment. <strong>No line says something different from what it claims.</strong> The two conventions that are easiest to get wrong were re-derived from the paper: which port a ribbon continues as across an edge ([[straightThrough]]), and the order in which two children's shared sides are glued ([[compose]]). Both are right.</p>
    <p>The page carries ${nOk} "as intended" notes and ${notes.length} others. None of the others is an error. Each marks a place where a line's meaning depends on something outside it:</p>
    <ul class="findings">${notes.map(({ c, it, where }) => `<li class="t-${c.tone}"><span class="badge">${TONE[c.tone][1]} ${TONE[c.tone][0]}</span> <a href="#item-${it.id}">${esc(where)}</a>: ${esc(c.title)}</li>`).join('')}</ul></section>`.replace(/\[\[[^\]]+\]\]/g, m => mark(m));
}
function tocHtml() {
  let h = `<a class="toc-top" href="#trust">What has to hold</a><a class="toc-top" href="#primer">Lean for this file</a><a class="toc-top" href="#start">Where to start</a>`;
  G.sections.forEach(sec => {
    h += `<div class="toc-sec"><a href="#${sec.id}">${esc(sec.title)}</a></div>`;
    ITEMS.filter(it => it.section === sec.id && it.kind !== 'section').forEach(it => {
      h += `<a class="toc-it" href="#item-${it.id}" data-id="${it.id}"><span class="tick" aria-hidden="true"></span><span class="toc-name">${esc(it.title)}</span></a>`;
    });
  });
  return h + `<a class="toc-top" href="#review">Findings</a><a class="toc-top" href="#glossary">Glossary</a>`;
}
function glossaryHtml() {
  const order = ['Keyword', 'Notation', 'Type', 'Value', 'Pair', 'List', 'Option', 'List / Option', 'Function', 'Kind', 'Basic.lean', 'Data/Pattern.lean', 'Data/Clusters.lean'];
  const keys = Object.keys(G.glossary).sort((a, b) => order.indexOf(G.glossary[a][0]) - order.indexOf(G.glossary[b][0]));
  let h = `<section class="sec" id="glossary"><h2>Glossary</h2><p class="lede">Every piece of Lean notation and every outside name the file uses, with the lines where it appears. Click a line number to go there.</p><div class="gl">`;
  let cat = '';
  keys.forEach(k => {
    const [c, text] = G.glossary[k];
    if (c !== cat) { h += `<div class="gl-cat">${esc(c)}</div>`; cat = c; }
    const uses = Array.from(USES['gl:' + k] || []).sort((a, b) => a - b);
    h += `<div class="gl-row"><code class="gl-k">${esc(k === ']?' ? 'l[i]?' : k)}</code><div class="gl-t">${mark(text)}${uses.length ? `<div class="gl-lines">${linesLinks(uses)}</div>` : ''}</div></div>`;
  });
  return h + `</div></section>`;
}
function linesLinks(arr, max) {
  max = max || 40;
  const s = arr.slice(0, max).map(n => `<a href="#L${n}">${n}</a>`).join(', ');
  return 'Lines ' + s + (arr.length > max ? ` and ${arr.length - max} more` : '');
}

/* ---------- reading ticks and options ---------- */
function syncTicks() {
  let done = 0, total = 0;
  ITEMS.forEach(it => {
    if (it.kind === 'section') return;
    total++;
    const on = store.get(readKey(it), '') === '1';
    if (on) done++;
    const cb = $('#read-' + it.id); if (cb) cb.checked = on;
    const art = $('#item-' + it.id); if (art) art.classList.toggle('is-read', on);
    $$(`.toc-it[data-id="${it.id}"]`).forEach(a => a.classList.toggle('is-read', on));
  });
  $('#prog-n').textContent = `${done} of ${total}`;
  $('#prog-bar').style.width = (100 * done / total) + '%';
  $('#clear').hidden = done === 0;
}
function bindOptions() {
  const how = $('#opt-how');
  how.checked = store.get('skg-howopen', '0') === '1';
  const setHow = () => $$('details.how').forEach(d => { d.open = how.checked; });
  setHow();
  how.addEventListener('change', () => { store.set('skg-howopen', how.checked ? '1' : '0'); setHow(); });
  const opts = [['opt-com', 'nocom', 'skg-com']];
  opts.forEach(([id, cls, key]) => {
    const cb = $('#' + id);
    cb.checked = store.get(key, '1') === '1';
    document.body.classList.toggle(cls, !cb.checked);
    cb.addEventListener('change', () => { store.set(key, cb.checked ? '1' : '0'); document.body.classList.toggle(cls, !cb.checked); });
  });
  document.addEventListener('change', e => {
    const cb = e.target.closest('.read input');
    if (!cb) return;
    const it = BYID[cb.dataset.id];
    if (cb.checked) store.set(readKey(it), '1'); else store.del(readKey(it));
    syncTicks();
  });
  const clear = $('#clear'), conf = $('#clear-confirm');
  clear.addEventListener('click', () => { conf.hidden = false; clear.hidden = true; });
  $('#clear-no').addEventListener('click', () => { conf.hidden = true; syncTicks(); });
  $('#clear-yes').addEventListener('click', () => { ITEMS.forEach(it => store.del(readKey(it))); conf.hidden = true; syncTicks(); });
}

/* ---------- pop-ups ---------- */
const pop = document.createElement('div');
pop.className = 'pop'; pop.hidden = true; pop.setAttribute('role', 'dialog');
let popFrom = null;
function popHtml(info) {
  if (info.type === 'def') {
    const it = BYID[info.id];
    const uses = Array.from(USES[info.key] || []).filter(n => n < it.lines[0] || n > it.lines[1]).sort((a, b) => a - b);
    const field = info.id === 'Patch' && ['tiles', 'glue', 'rim', 'vtx'].includes(info.name);
    return `<div class="pop-h"><code>${esc(info.name)}</code><span class="pop-c">${field ? 'field of Patch' : (info.name !== it.title && info.id === 'Chain' ? 'field of Chain' : 'defined in this file')}</span></div>` +
      `<p>${field ? mark(G.fields[info.name]) : esc(it.summary || '')}</p>` +
      `<p class="pop-links"><a href="#item-${it.id}">Go to ${esc(it.title)} (${linesLabel(it.lines)})</a></p>` +
      (uses.length ? `<p class="pop-uses">Also used on ${linesLinks(uses, 24).replace('Lines', 'lines')}</p>` : '');
  }
  if (info.type === 'scoped') return `<div class="pop-h"><code>${esc(info.name)}</code><span class="pop-c">${esc(info.sc.kind)}</span></div><p>${info.sc.text}</p>`;
  if (info.type === 'mod') return `<div class="pop-h"><code>${esc(info.name)}</code><span class="pop-c">module</span></div><p>${esc(MODULES[info.name])}</p>`;
  const [c, text] = G.glossary[info.name];
  const uses = Array.from(USES[info.key] || []).sort((a, b) => a - b);
  return `<div class="pop-h"><code>${esc(info.name === ']?' ? 'l[i]?' : info.name)}</code><span class="pop-c">${esc(c)}</span></div><p>${mark(text)}</p>` +
    (uses.length ? `<p class="pop-uses">${linesLinks(uses, 24)}</p>` : '') + `<p class="pop-links"><a href="#glossary">Glossary</a></p>`;
}
function showPop(el) {
  const info = REG[+el.dataset.r];
  pop.innerHTML = popHtml(info) + `<button class="pop-x" type="button" aria-label="Close">×</button>`;
  pop.hidden = false; popFrom = el;
  const r = el.getBoundingClientRect(), w = Math.min(380, window.innerWidth - 24);
  pop.style.width = w + 'px';
  const left = Math.max(12, Math.min(r.left, window.innerWidth - w - 12));
  pop.style.left = (left + window.scrollX) + 'px';
  const below = r.bottom + 8 + window.scrollY;
  pop.style.top = below + 'px';
  const ph = pop.offsetHeight;
  if (r.bottom + 8 + ph > window.innerHeight && r.top - 8 - ph > 0) pop.style.top = (r.top - 8 - ph + window.scrollY) + 'px';
}
function hidePop() { if (!pop.hidden) { pop.hidden = true; if (popFrom && document.activeElement === document.body) popFrom.focus(); popFrom = null; } }

/* ---------- navigation ---------- */
function go(hash, push) {
  const id = hash.replace(/^#/, '');
  let el = id && document.getElementById(id);
  if (!el) return false;
  if (el.classList.contains('cl') && document.body.classList.contains('nocom')) el = el.closest('.row, .sec-code') || el;
  el.scrollIntoView({ block: el.classList.contains('ln') ? 'center' : 'start', behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth' });
  if (el.classList.contains('ln')) { el.classList.remove('flash'); void el.offsetWidth; el.classList.add('flash'); }
  if (push) { try { history.pushState(null, '', '#' + id); } catch (e) { /* some viewers refuse */ } }
  return true;
}
function bindNav() {
  document.addEventListener('click', e => {
    const t = e.target.closest('.tk');
    if (t) { e.preventDefault(); showPop(t); return; }
    if (e.target.closest('.pop-x')) { hidePop(); return; }
    const a = e.target.closest('a[href^="#"]');
    if (a) {
      if (go(a.getAttribute('href'), true)) { e.preventDefault(); hidePop(); const d = a.closest('details'); if (d && d.id === 'toc-wrap-m') d.open = false; }
      return;
    }
    if (!e.target.closest('.pop')) hidePop();
  });
  document.addEventListener('keydown', e => {
    if (e.key === 'Escape') hidePop();
    if ((e.key === 'Enter' || e.key === ' ') && e.target.classList && e.target.classList.contains('tk')) { e.preventDefault(); showPop(e.target); }
  });
  window.addEventListener('popstate', () => go(location.hash, false));
  if ('IntersectionObserver' in window) {
    const io = new IntersectionObserver(ents => {
      ents.forEach(en => {
        if (!en.isIntersecting) return;
        const id = en.target.id.replace('item-', '');
        $$('#toc .toc-it').forEach(a => a.classList.toggle('active', a.dataset.id === id));
      });
    }, { rootMargin: '-30% 0px -60% 0px' });
    $$('article.item').forEach(a => io.observe(a));
  }
}

/* ================================================================================================================ */
/* Figures                                                                                                           */
/* ================================================================================================================ */
const FIGS = {};
const svgEl = (w, h, inner, label) => `<svg viewBox="0 0 ${w} ${h}" role="img" aria-label="${esc(label)}">${inner}</svg>`;

/* The tile: vertices from the paper's turning sequence, ports, pieces. Click a port to see pieceEnd. */
FIGS.tile = function (host) {
  const K = [0, 10, 1, 3, 0, 2, 5, 7, 4, 6, 6, 8, 11, 9];
  const V = [[0, 0]];
  for (let i = 0; i < 13; i++) { const a = K[i] * Math.PI / 6; V.push([V[i][0] + Math.cos(a), V[i][1] + Math.sin(a)]); }
  const d = [], nn = [];
  for (let i = 0; i < 14; i++) {
    const p = V[i], q = V[(i + 1) % 14], L = Math.hypot(q[0] - p[0], q[1] - p[1]);
    d.push([(q[0] - p[0]) / L, (q[1] - p[1]) / L]); nn.push([-d[i][1], d[i][0]]);
  }
  const add = (a, b, s) => [a[0] + s * b[0], a[1] + s * b[1]];
  const C = V.map((v, i) => add(v, d[i], 0.5 + 0.15 * (i % 2 ? -1 : 1)));
  const A = 0.13, H = 0.085;
  const port = (i, s) => s ? add(add(C[i], d[i], -A), nn[i], H) : (e => add(add(C[e], d[e], A), nn[e], H))((i + 13) % 14);
  const S = 78, pad = 34;
  const xs = V.map(v => v[0]), ys = V.map(v => v[1]);
  const minx = Math.min(...xs), maxy = Math.max(...ys);
  const W = (Math.max(...xs) - minx) * S + 2 * pad, Hh = (maxy - Math.min(...ys)) * S + 2 * pad;
  const P = p => [((p[0] - minx) * S + pad).toFixed(1), ((maxy - p[1]) * S + pad).toFixed(1)];
  const pt = p => P(p).join(' ');
  const pieces = {};
  for (let i = 2; i < 14; i++) {
    const a = nn[(i + 13) % 14], b = nn[i], dot = a[0] * b[0] + a[1] * b[1];
    const q = [V[i][0] + H * (a[0] + b[0]) / (1 + dot), V[i][1] + H * (a[1] + b[1]) / (1 + dot)];
    pieces['h' + i] = { cls: 'pc-h', d: `M${pt(C[(i + 13) % 14])} L${pt(port(i, false))} Q${pt(q)} ${pt(port(i, true))} L${pt(C[i])}` };
  }
  {
    const p0 = port(0, true), p3 = port(1, true), p1 = add(add(p0, d[0], -0.45), nn[0], 0.6), p2 = add(add(p3, d[1], -0.45), nn[1], 0.6);
    pieces.xR = { cls: 'pc-r', d: `M${pt(C[0])} L${pt(p0)} C${pt(p1)} ${pt(p2)} ${pt(p3)} L${pt(C[1])}` };
    const q0 = port(0, false), q3 = port(1, false), q1 = add(add(q0, d[13], 0.45), nn[13], 0.6), q2 = add(add(q3, d[0], 0.45), nn[0], 0.6);
    pieces.xL = { cls: 'pc-l', d: `M${pt(C[13])} L${pt(q0)} C${pt(q1)} ${pt(q2)} ${pt(q3)} L${pt(C[0])}` };
  }
  const pieceOf = (i, s) => i >= 2 ? 'h' + i : (s ? 'xR' : 'xL');
  const partner = (i, s) => i === 0 ? [1, s] : i === 1 ? [0, s] : [i, !s];
  let g = `<polygon class="tile-poly" points="${V.map(pt).join(' ')}"/>`;
  g += Object.entries(pieces).map(([k, p]) => `<path class="pc ${p.cls}" data-p="${k}" d="${p.d}"/>`).join('');
  g += C.map(c => `<circle class="xpt" cx="${P(c)[0]}" cy="${P(c)[1]}" r="2.6"/>`).join('');
  V.forEach((v, i) => {
    const a = nn[(i + 13) % 14], b = nn[i], m = Math.hypot(a[0] + b[0], a[1] + b[1]) || 1;
    const L = add(v, [(a[0] + b[0]) / m, (a[1] + b[1]) / m], -0.27), [x, y] = P(L);
    g += `<text class="vlab" x="${x}" y="${y}" dy="0.35em">v${sub(i)}</text>`;
    const mid = add(add(v, d[i], 0.5), nn[i], -0.2), [ex, ey] = P(mid);
    g += `<text class="elab" x="${ex}" y="${ey}" dy="0.35em">e${sub(i)}</text>`;
  });
  for (let i = 0; i < 14; i++) for (const s of [true, false]) {
    const [x, y] = P(port(i, s));
    g += `<g class="port" tabindex="0" role="button" data-i="${i}" data-s="${s}" aria-label="${s ? 'R' : 'L'}(v${i})"><circle class="hit" cx="${x}" cy="${y}" r="9"/><circle class="pm ${s ? 'pm-r' : 'pm-l'}" cx="${x}" cy="${y}" r="4.2"/></g>`;
  }
  host.innerHTML = `<div class="fig-h">The tile and its 28 ports <span class="fig-sub">drawn from the paper's turning sequence (0, 10, 1, 3, 0, 2, 5, 7, 4, 6, 6, 8, 11, 9), in units of 30°</span></div>
    <div class="fig-body fig-tile">${svgEl(Math.ceil(W), Math.ceil(Hh), g, 'The tile with its fourteen vertices and twenty-eight ports')}
    <div class="fig-side"><div class="readout" aria-live="polite"></div>
    <ul class="legend"><li><span class="sw sw-r"></span><span>R(v<sub>i</sub>): <code>s = true</code>, on e<sub>i</sub></span></li><li><span class="sw sw-l"></span><span>L(v<sub>i</sub>): <code>s = false</code>, on e<sub>i−1</sub></span></li><li><span class="ln-sw pc-h"></span><span>a hook, L(v<sub>i</sub>) – R(v<sub>i</sub>)</span></li><li><span class="ln-sw pc-r"></span><span>crossover R(v<sub>0</sub>) – R(v<sub>1</sub>)</span></li><li><span class="ln-sw pc-l"></span><span>crossover L(v<sub>0</sub>) – L(v<sub>1</sub>)</span></li><li><span class="dot-sw"></span><span>crossing point of an edge</span></li></ul>
    <label class="fig-opt"><input type="checkbox" id="opt-elab"> Show edge names</label>
    <p class="fig-note">Every port sits at the crossing point of its edge: on e<sub>i</sub>, R(v<sub>i</sub>) is the end that runs off towards v<sub>i</sub> and L(v<sub>i+1</sub>) the end towards v<sub>i+1</sub>. They are drawn a little apart so that each can be clicked.</p></div></div>`;
  const svg = $('svg', host), out = $('.readout', host);
  const name = (i, s) => `${s ? 'R' : 'L'}(v${sub(i)})`;
  function select(i, s) {
    const [j, s2] = partner(i, s), pk = pieceOf(i, s);
    $$('.port', svg).forEach(p => { const pi = +p.dataset.i, ps = p.dataset.s === 'true'; p.classList.toggle('on', pi === i && ps === s); p.classList.toggle('mate', pi === j && ps === s2); });
    $$('.pc', svg).forEach(p => { p.classList.toggle('on', p.dataset.p === pk); });
    svg.classList.add('has-sel');
    const kind = i >= 2 ? `the hook round v${sub(i)}` : `one of the two crossover pieces (line ${i === 0 ? lineOf('| (t, 0, s) => (t, 1, s)') : lineOf('| (t, 1, s) => (t, 0, s)')})`;
    out.innerHTML = `<code>pieceEnd (t, ${i}, ${s}) = (t, ${j}, ${s2})</code><p>${name(i, s)} and ${name(j, s2)} are the two ends of ${kind}${i >= 2 ? ` (line ${lineOf('| (t, i, s) => (t, i, !s)')}: <code>!s</code> swaps R and L)` : ''}.</p>`;
  }
  svg.addEventListener('click', e => { const p = e.target.closest('.port'); if (p) select(+p.dataset.i, p.dataset.s === 'true'); });
  svg.addEventListener('keydown', e => { const p = e.target.closest('.port'); if (p && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); select(+p.dataset.i, p.dataset.s === 'true'); } });
  $('#opt-elab', host).addEventListener('change', e => svg.classList.toggle('show-e', e.target.checked));
  select(0, true);
};

/* One shared edge, two tiles, four ports: the straight-through rule. */
FIGS.across = function (host) {
  const W = 560, H = 300, y0 = 150, xl = 70, xr = 490, xm = 280;
  const arms = {
    UL: { x: 190, y: 62, rib: 'a', lab: 'R(vᵢ) of t', ax: 176, ay: 66, an: 'end' },
    UR: { x: 370, y: 62, rib: 'b', lab: 'L(vᵢ₊₁) of t', ax: 384, ay: 66, an: 'start' },
    LR: { x: 370, y: 238, rib: 'a', lab: 'R(vⱼ) of t′', ax: 384, ay: 242, an: 'start' },
    LL: { x: 190, y: 238, rib: 'b', lab: 'L(vⱼ₊₁) of t′', ax: 176, ay: 242, an: 'end' },
  };
  const rib = (k, a, b) => `<g class="rib rib-${k}" data-rib="${k}"><line class="rib-e" x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}"/><line class="rib-f" x1="${a.x}" y1="${a.y}" x2="${b.x}" y2="${b.y}"/></g>`;
  let g = `<polygon class="tile-poly" points="${xl},${y0} ${xr},${y0} ${xr - 50},26 ${xl + 50},26"/><polygon class="tile-poly t2" points="${xl},${y0} ${xr},${y0} ${xr - 50},274 ${xl + 50},274"/>`;
  g += `<text class="tlab" x="${xm}" y="40">tile t</text><text class="tlab" x="${xm}" y="270">tile t′</text>`;
  g += rib('b', arms.UR, arms.LL) + rib('a', arms.UL, arms.LR);
  g += `<line class="edge" x1="${xl}" y1="${y0}" x2="${xr}" y2="${y0}"/><circle class="xpt big" cx="${xm}" cy="${y0}" r="4"/>`;
  g += `<circle class="vpt" cx="${xl}" cy="${y0}" r="3.5"/><circle class="vpt" cx="${xr}" cy="${y0}" r="3.5"/>`;
  g += `<text class="vlab2" x="${xl - 8}" y="${y0 - 10}" text-anchor="end">vᵢ of t</text><text class="vlab2" x="${xl - 8}" y="${y0 + 20}" text-anchor="end">vⱼ₊₁ of t′</text>`;
  g += `<text class="vlab2" x="${xr + 8}" y="${y0 - 10}">vᵢ₊₁ of t</text><text class="vlab2" x="${xr + 8}" y="${y0 + 20}">vⱼ of t′</text>`;
  g += `<text class="elab2" x="${xm + 60}" y="${y0 - 8}">eᵢ of t →</text><text class="elab2" x="${xm - 60}" y="${y0 + 18}" text-anchor="end">← eⱼ of t′</text>`;
  Object.entries(arms).forEach(([k, a]) => {
    g += `<g class="arm" tabindex="0" role="button" data-k="${k}" aria-label="${a.lab}"><circle class="hit" cx="${a.x}" cy="${a.y}" r="22"/><circle class="arm-end" cx="${a.x}" cy="${a.y}" r="6"/><text class="alab" x="${a.ax}" y="${a.ay}" text-anchor="${a.an}">${a.lab}</text></g>`;
  });
  host.innerHTML = `<div class="fig-h">The straight-through rule at one edge <span class="fig-sub">edge e<sub>i</sub> of tile t is edge e<sub>j</sub> of tile t′: <code>glue t i = some (t′, j)</code></span></div>
    <div class="fig-body fig-across">${svgEl(W, H + 10, g, 'Two tiles sharing an edge, with two ribbons crossing at its crossing point')}
    <div class="fig-side"><div class="readout" aria-live="polite"></div><p class="fig-note">Click any of the four ribbon ends. Each ribbon runs straight through the crossing point, so the end heading towards one end of the edge in t continues as the end heading towards the other end of the edge in t′.</p></div></div>`;
  const svg = $('svg', host), out = $('.readout', host);
  const LR_ = lineOf('| (t, i, true) => (glue t i)'), LL_ = lineOf('| (t, i, false) => (glue t');
  const TXT = {
    UL: `<code>across (t, i, true)</code><p>Line ${LR_}. The port lies on e<sub>i</sub>: look up <code>glue t i = some (t′, j)</code>, answer <code>some (t′, j, true)</code>: R(v<sub>j</sub>) of t′, the lower right end.</p>`,
    UR: `<code>across (t, i+1, false)</code><p>Line ${LL_}. L(v<sub>i+1</sub>) lies on edge <code>(i+1+13) % 14</code> = i: look up <code>glue t i = some (t′, j)</code>, answer <code>some (t′, (j+1) % 14, false)</code>: L(v<sub>j+1</sub>) of t′, the lower left end.</p>`,
    LR: `<code>across (t′, j, true)</code><p>Line ${LR_}, seen from t′: <code>glue t′ j = some (t, i)</code> (the gluing is symmetric), answer <code>some (t, i, true)</code>: back to R(v<sub>i</sub>) of t.</p>`,
    LL: `<code>across (t′, j+1, false)</code><p>Line ${LL_}, seen from t′: <code>glue t′ j = some (t, i)</code>, answer <code>some (t, i+1, false)</code>: back to L(v<sub>i+1</sub>) of t.</p>`,
  };
  function select(k) {
    const r = arms[k].rib;
    $$('.arm', svg).forEach(a => { a.classList.toggle('on', a.dataset.k === k); a.classList.toggle('mate', a.dataset.k !== k && arms[a.dataset.k].rib === r); });
    $$('.rib', svg).forEach(x => x.classList.toggle('dim', x.dataset.rib !== r));
    out.innerHTML = TXT[k];
  }
  svg.addEventListener('click', e => { const a = e.target.closest('.arm'); if (a) select(a.dataset.k); });
  svg.addEventListener('keydown', e => { const a = e.target.closest('.arm'); if (a && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); select(a.dataset.k); } });
  select('UL');
};

/* Two children sharing a boundary: o-th edge from the start is (length-1-o)-th of the other side. */
FIGS.compose = function (host) {
  const n = 5, x0 = 60, w = 84, y = 130, W = x0 * 2 + n * w, H = 250;
  let g = `<rect class="kid" x="${x0}" y="34" width="${n * w}" height="${y - 34}"/><rect class="kid k2" x="${x0}" y="${y}" width="${n * w}" height="${H - 34 - y}"/>`;
  g += `<text class="tlab" x="${W / 2}" y="58">child c, side j</text><text class="tlab" x="${W / 2}" y="${H - 46}">child c′, side j′</text>`;
  g += `<line class="arrow" x1="${x0 + 10}" y1="78" x2="${x0 + n * w - 10}" y2="78" marker-end="url(#ah)"/><line class="arrow" x1="${x0 + n * w - 10}" y1="${H - 74}" x2="${x0 + 10}" y2="${H - 74}" marker-end="url(#ah)"/>`;
  for (let o = 0; o < n; o++) {
    const xa = x0 + o * w, xb = xa + w;
    g += `<g class="seg" tabindex="0" role="button" data-o="${o}" aria-label="edge ${o}"><rect class="hit" x="${xa}" y="${y - 30}" width="${w}" height="60"/><line class="segl" x1="${xa + 3}" y1="${y}" x2="${xb - 3}" y2="${y}"/><text class="olab" x="${xa + w / 2}" y="${y - 12}">o = ${o}</text><text class="olab o2" x="${xa + w / 2}" y="${y + 24}">${n - 1 - o}</text></g>`;
  }
  const defs = `<defs><marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path class="ahead" d="M0,0 L10,5 L0,10 z"/></marker></defs>`;
  host.innerHTML = `<div class="fig-h">Gluing two children along a shared boundary <span class="fig-sub">line ${lineOf('(s[s.length - 1 - o]?)')}: <code>s[s.length - 1 - o]?</code></span></div>
    <div class="fig-body fig-compose">${svgEl(W, H, defs + g, 'Two children sharing a boundary of five edges, numbered in opposite directions')}
    <div class="fig-side"><div class="readout" aria-live="polite"></div><p class="fig-note">The children run along their shared boundary in opposite directions, so counting from the start of side j and from the start of side j′ gives opposite numberings. Click an edge.</p></div></div>`;
  const svg = $('svg', host), out = $('.readout', host);
  function select(o) {
    $$('.seg', svg).forEach(s => s.classList.toggle('on', +s.dataset.o === o));
    out.innerHTML = `<code>o = ${o}</code><p>This edge is entry ${o} of side j of child c, counted from its start, and entry ${n} − 1 − ${o} = ${n - 1 - o} of side j′ of child c′, counted from its start: <code>s[${n} - 1 - ${o}]?</code> with <code>s.length = ${n}</code>.</p>`;
  }
  svg.addEventListener('click', e => { const s = e.target.closest('.seg'); if (s) select(+s.dataset.o); });
  svg.addEventListener('keydown', e => { const s = e.target.closest('.seg'); if (s && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); select(+s.dataset.o); } });
  select(1);
};

/* The nest's numbering: gid, loc, up, with the tile counts of the blocks. */
const NT = [1], NS = [1];
{ let nb = 9, gb = 8; NT.push(nb); NS.push(nb); for (let m = 2; m <= 8; m++) { const n2 = 7 * nb + gb, g2 = 6 * nb + gb; nb = n2; gb = g2; NT.push(nb); NS.push(nb); } }
function gid(b, t) { if (b === 0) return t; const s = NS[b - 1], n = NT[b - 1]; if (s <= t && t < s + n) return gid(b - 1, t - s); if (t < s) return n + t; return t; }
function loc(b, g) { if (b === 0) return g; const s = NS[b - 1], n = NT[b - 1]; if (g < n) return loc(b - 1, g) + s; if (g < n + s) return g - n; return g; }
function up(b, k, t) { return k === 0 ? t : up(b + 1, k - 1, t + NS[b]); }
window.__nest = { gid, loc, up, NT, NS };
function gidTrace(b, t) {
  const steps = [], D0 = 'def gid : Nat → Nat → Nat';
  const L0 = lineOf('| 0, t => t', D0), L1 = lineOf('then gid b (t - nestShift b)', D0), L2 = lineOf('(N b).tiles + t', D0), L3 = lineOf('else t', D0);
  while (true) {
    if (b === 0) { steps.push(`<code>gid 0 ${t}</code> = ${t} (line ${L0})`); break; }
    const s = NS[b - 1], n = NT[b - 1];
    if (s <= t && t < s + n) { steps.push(`<code>gid ${b} ${fmt(t)}</code>: ${fmt(s)} ≤ ${fmt(t)} &lt; ${fmt(s + n)}, a tile of child 1 (N${sub(b - 1)}), so <code>gid ${b - 1} ${fmt(t - s)}</code> (line ${L1})`); t -= s; b -= 1; continue; }
    if (t < s) { steps.push(`<code>gid ${b} ${fmt(t)}</code>: ${fmt(t)} &lt; ${fmt(s)}, a tile of child 0, so ${fmt(n)} + ${fmt(t)} = ${fmt(n + t)} (line ${L2})`); break; }
    steps.push(`<code>gid ${b} ${fmt(t)}</code>: ${fmt(t)} ≥ ${fmt(s + n)}, a later child, so it keeps ${fmt(t)} (line ${L3})`); break;
  }
  return steps;
}
FIGS.nest = function (host) {
  host.innerHTML = `<div class="fig-h">Explorer: numbering the nest <span class="fig-sub"><code>nestShift</code>, <code>up</code>, <code>gid</code> and <code>loc</code> on real block sizes</span></div>
    <div class="nest-ctl"><label for="nest-b">Block N<sub>b</sub>, b =</label><select id="nest-b">${[1, 2, 3, 4, 5, 6].map(b => `<option value="${b}"${b === 2 ? ' selected' : ''}>${b} (${fmt(NT[b])} tiles)</option>`).join('')}</select>
    <label for="nest-t">tile t =</label><span class="stepper"><button type="button" id="nest-dec" aria-label="previous tile">−</button><input id="nest-t" type="number" min="0" value="10" inputmode="numeric"><button type="button" id="nest-inc" aria-label="next tile">+</button></span>
    <button type="button" class="chip" id="nest-orig">The original tile</button></div>
    <div class="nest-out" aria-live="polite"></div>
    <p class="fig-note">Block sizes: |N<sub>b</sub>| = 1, 9, 71, 559, 4,401, 34,649, 272,791 for b = 0 … 6, and nestShift b = |N<sub>b</sub>| (a Ξ and a Δ of the same level have the same number of tiles). These are computed in the page from the recursion of Table 1; the explorer's <code>gid</code>, <code>loc</code> and <code>up</code> follow ${mark('[[up]], [[gid]] and [[loc]]')} and agree with Lean's own values for every tile of N<sub>0</sub> … N<sub>3</sub>.</p>`;
  const selB = $('#nest-b', host), inT = $('#nest-t', host), out = $('.nest-out', host);
  function bar(segs, total, mark, title) {
    let x = 0;
    const parts = segs.map(s => { const w = Math.max(0.6, 100 * s.n / total), h = `<div class="bseg ${s.cls}" style="left:${x}%;width:${w}%"><span>${s.lab}</span></div>`; x += 100 * s.n / total; return h; }).join('');
    return `<div class="bar-t">${title}</div><div class="segbar">${parts}<div class="bmark" style="left:${(100 * (mark + 0.5) / total)}%"></div></div>`;
  }
  function render() {
    const b = +selB.value, total = NT[b], s = NS[b - 1], n = NT[b - 1];
    let t = Math.max(0, Math.min(total - 1, Math.floor(+inT.value || 0)));
    inT.value = t; inT.max = total - 1;
    const g = gid(b, t), part = t < s ? 'child 0 (a Ξ)' : t < s + n ? `child 1, which is N${sub(b - 1)}` : 'a later child';
    const ups = [0, 1, 2, 3].map(k => b + k <= 8 ? `N${sub(b + k)}: ${fmt(up(b, k, t))}` : '').filter(Boolean).join(' · ');
    out.innerHTML =
      bar([{ n: s, cls: 'c0', lab: 'child 0' }, { n, cls: 'c1', lab: `N${sub(b - 1)}` }, { n: total - s - n, cls: 'cr', lab: 'children 2–7' }], total, t, `Tile numbers in N${sub(b)} (0 … ${fmt(total - 1)}): tile ${fmt(t)} is in ${part}`) +
      bar([{ n, cls: 'c1', lab: `N${sub(b - 1)}` }, { n: s, cls: 'c0', lab: 'child 0' }, { n: total - s - n, cls: 'cr', lab: 'unchanged' }], total, g, `Nest numbers of the same tiles: <code>gid ${b} ${fmt(t)}</code> = ${fmt(g)}`) +
      `<ol class="trace">${gidTrace(b, t).map(x => `<li>${x}</li>`).join('')}</ol>` +
      `<p class="nest-res"><code>gid ${b} ${fmt(t)} = ${fmt(g)}</code> and <code>loc ${b} ${fmt(g)} = ${fmt(loc(b, g))}</code>. The same tile in larger blocks (<code>up ${b} k ${fmt(t)}</code>): ${ups}.</p>`;
  }
  selB.addEventListener('change', render);
  inT.addEventListener('input', render);
  $('#nest-dec', host).addEventListener('click', () => { inT.value = +inT.value - 1; render(); });
  $('#nest-inc', host).addEventListener('click', () => { inT.value = +inT.value + 1; render(); });
  $('#nest-orig', host).addEventListener('click', () => { inT.value = up(0, +selB.value, 0); render(); });
  render();
};

/* ---------- start ---------- */
document.body.appendChild(pop);
build();
bindOptions();
syncTicks();
bindNav();
if (location.hash) setTimeout(() => go(location.hash, false), 60);
})();
