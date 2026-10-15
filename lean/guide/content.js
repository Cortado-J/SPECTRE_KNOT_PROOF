/*
  The explanations shown by the proof map's Statement.lean page (statement.html), one entry per piece of SpectreKnot/Statement.lean.
  Every line of the file belongs to exactly one item (build_guide.py checks this). Items with clauses split their lines
  further; only the long definitions and the claims have clauses. In each item, `what` is the plain reading (always
  shown), `how` says how the Lean syntax says it (folded away until opened), `examples` are Lean's own output and
  `checks` are the reading's findings. `primer` is the short introduction to Lean at the top of the page.
  Markup inside the strings: [[id]] or [[id|text]] links to an item; [[L137]] links to a line.
  `writtenFor` is the SHA-256 of Statement.lean that these explanations were written for; the page warns if the file
  has changed since.
*/
window.GUIDE = {
writtenFor: '37e737d43ea0a4d73c16be376a4cd21e5b29f88c2bcbba7697b7d12abcb06419',
written: '15 Oct 2026',

sections: [
  { id: 's0', title: 'Preamble' },
  { id: 's1', title: '§1 Ports and pieces' },
  { id: 's2', title: '§2 Patches and strands' },
  { id: 's3', title: '§3 Supertiles' },
  { id: 's4', title: '§4 The nest' },
  { id: 's5', title: '§5 The theorems' },
  { id: 's6', title: '§6 The nest tiling and its one strand' },
  { id: 's7', title: '§7 Any chain of supertiles' },
],

/* ---------------------------------------------------------------------------------------------------------------- */
/* Lean for this file: what a reader new to Lean needs, in the order it is met. `code` is shown highlighted. */
primer: [
  { title: 'A definition',
    code: 'def N (b : Nat) : Patch := super b .Delta',
    text: `<code>def</code> names a value or a function. Each argument comes with its type, <code>(b : Nat)</code>; after
      the next colon is the type of the result; after <code>:=</code> the definition. Read: <code>N b</code> is the
      patch <code>super b .Delta</code>.` },
  { title: 'Applying a function',
    code: 'super (m + 1) ((Pattern.kids T).getD c .Gamma)',
    text: `No commas and no brackets round the arguments: <code>f x y</code> is <code>f</code> applied to <code>x</code>
      and <code>y</code>. Brackets only group. A function type <code>A → B → C</code> takes an <code>A</code> and a
      <code>B</code> and gives a <code>C</code>.` },
  { title: 'Dot notation',
    code: '(N b).tiles\nP.across p\np.2.1\n.Delta',
    text: `<code>x.f</code> is the field <code>f</code> of a record <code>x</code>, or the function <code>f</code> of
      <code>x</code>'s type applied to <code>x</code>: <code>P.across p</code> is <code>Patch.across P p</code>. On pairs,
      <code>.1</code> and <code>.2</code> are the two entries, so for a port <code>p = (t, i, s)</code>,
      <code>p.2.1</code> is <code>i</code>. A bare <code>.Delta</code> is <code>Kind.Delta</code>, where a kind is
      expected.` },
  { title: 'The basic types',
    code: 'Nat\nBool\nNat × Nat × Bool\nOption (Nat × Nat)\nList (Nat × Nat)',
    text: `<code>Nat</code> is 0, 1, 2, …; subtraction stops at 0, so <code>3 - 5 = 0</code>. <code>A × B</code> is the
      type of pairs. <code>Option A</code> is either <code>none</code> or <code>some x</code>: "maybe nothing", for
      instance nothing across an edge on the rim. <code>List A</code> is a finite list.` },
  { title: 'Definition by cases',
    code: 'def pieceEnd : Port → Port\n  | (t, 0, s) => (t, 1, s)\n  | (t, 1, s) => (t, 0, s)\n  | (t, i, s) => (t, i, !s)',
    text: `Each line <code>| pattern => result</code> is a case, and Lean uses the first that fits. A pattern can name
      the parts it matches (<code>t</code>, <code>s</code>) and can match numbers: <code>m + 2</code> matches every
      number from 2 up. A definition may call itself on smaller arguments (recursion).` },
  { title: 'Local names and small functions',
    code: 'let off := fun c => …\nfun (t\', j) => (t\', j, true)\n(· == (t₀, i))\nfun _ _ => none',
    text: `<code>let x := v</code> names <code>v</code> for what follows. <code>fun x => e</code> is a function without
      a name; <code>fun (t', j) => …</code> takes a pair apart. <code>_</code> is an argument that is ignored, and
      <code>(· == x)</code> is short for <code>fun y => y == x</code>.` },
  { title: 'Records',
    code: 'structure Patch where\n  tiles : Nat\n  glue : Nat → Nat → Option (Nat × Nat)\n  …\n⟨1, fun _ _ => none, …, []⟩',
    text: `A <code>structure</code> is a record type with named fields. <code>⟨a, b, c, d⟩</code> builds one from its
      fields in order, and <code>{ tiles := …, glue := … }</code> by name; <code>P.tiles</code> reads a field. A field
      whose type is a claim, as in <code>Chain</code>, holds a proof of that claim.` },
  { title: 'Claims and proofs',
    code: 'def TheoremA : Prop := ∀ m K, (super m K).NoClosedStrand\n-- in ProofA.lean:\ntheorem theoremA : TheoremA := …',
    text: `<code>Prop</code> is the type of claims. A <code>def</code> of type <code>Prop</code> only <em>states</em> a
      claim. Another file proves it with <code>theorem theoremA : TheoremA := …</code>, and Lean's kernel checks that
      the proof has exactly that type. This file holds definitions only, no proofs.` },
  { title: 'Logic',
    code: '∀ x, …\n∃ x, …\nA ∧ B    A ∨ B\nA → B    a ≠ b',
    text: `For all; there is; and; or; if … then (the same arrow as in function types); not equal. <code>∧</code> and
      <code>→</code> group to the right, so <code>A → B → C</code> reads "if A and B, then C".` },
  { title: 'Rules',
    code: 'inductive Follow : Port → Port → Prop\n  | leave {p : Port} : P.across (pieceEnd p) = none → Follow p (pieceEnd p)\n  | next {p q r : Port} : … → Follow q r → Follow p r',
    text: `<code>inductive R : … → Prop</code> with rules <code>| name : premises → conclusion</code> defines a
      relation that holds exactly when it can be derived by finitely many uses of the rules. That is how "follow the
      ribbon until it leaves the patch" and "on the same strand" are defined. Braces, <code>{p : Port}</code>, mark an
      argument Lean works out for itself.` },
  { title: 'Namespaces',
    code: 'namespace Patch\nvariable (P : Patch)\n…\nend Patch',
    text: `Names defined between <code>namespace X</code> and <code>end X</code> get the prefix <code>X.</code>, which
      is what makes dot notation work. <code>variable (P : Patch)</code> adds <code>P</code> as a first argument to
      every following definition that uses it.` },
  { title: 'Comments',
    code: '-- a line comment\n/- a block comment -/\n/-- a doc comment, attached to the definition after it -/',
    text: `Lean ignores comments, so nothing in them is checked: they say what the author meant. That is why each
      definition on this page is read against the paper as well as against its comment.` },
],

/* ---------------------------------------------------------------------------------------------------------------- */
items: [

{ id: 'header', section: 's0', kind: 'comment', title: 'The opening comment', lines: [1, 19],
  summary: 'What the file is for, the data it uses, and assumption (M).',
  what: `What the file is for, the two data files it uses, and the one assumption that links it to real tilings:
    (M), that real supertiles are glued like <code>super m K</code>. Lean ignores comments, so none of this is
    checked; it is the author's description of the code below.`,
  how: `<code>/-</code> opens a block comment and <code>-/</code> closes it ([[L19]]). <code>#</code> is decoration.`,
  checks: [
    { tone: 'data', title: 'Where Lean stops',
      text: `Every claim in this file is about the patches the file builds. That they are glued like the real
        supertiles is assumption (M), which rests on the spectre paper (Thms 2.2, 3.1, 4.1, 5.1) and on the paper's
        Prop 2.4 and Lemma 2.6. <code>Tests.lean</code> supports it: the level-2 supertiles built here equal, edge for
        edge, those built from the tile placements in exact arithmetic, and the strand counts of the paper's Table 5
        come out of these definitions.` },
  ] },

{ id: 'imports', section: 's0', kind: 'import', title: 'Imports', lines: [20, 23],
  summary: 'Loads Basic (Kind, iter) and the two generated data files.',
  what: `Loads three other files of the project. Every name used below that this file does not define comes from one of
    them, or from Lean's core library: <code>Kind</code> and <code>iter</code> from <code>Basic</code>;
    <code>Pattern.kids</code>, <code>Pattern.adj</code>, <code>Pattern.pside</code> (the paper's Tables 1–3) from
    <code>Data/Pattern.lean</code>; <code>Clusters.tiles</code>, <code>.glue</code>, <code>.rim</code>,
    <code>.vtx</code> (the nine level-1 supertiles) from <code>Data/Clusters.lean</code>.`,
  how: `<code>import A.B</code> loads the file <code>A/B.lean</code> and makes its definitions available. Lean's core
    library (<code>Nat</code>, <code>List</code>, <code>Option</code>, …) is always available; this project does not use
    Mathlib.`,
  extra: 'basic',
  examples: [
    { expr: 'Pattern.kids .Delta', out: '[Xi, Delta, Xi, Phi, Sigma, Pi, Phi, Gamma]',
      note: 'Table 1, the row for Δ: the kinds of its eight children, child 0 first.' },
    { expr: '(Pattern.adj .Delta).getD 1 []', out: '[some (7, 2), some (0, 5), none, some (2, 0), some (3, 0), some (4, 0)]',
      note: 'Table 2, Δ, child 1: side 0 of child 1 is side 2 of child 7; side 2 lies on the parent\'s rim; and so on.' },
    { expr: 'Pattern.pside .Delta',
      out: '[[(7, 5), (6, 4), (6, 3), (6, 2), (5, 4)],\n [(5, 3), (5, 2)],\n [(5, 1), (4, 2), (3, 4), (3, 3)],\n [(3, 2), (2, 4), (2, 3)],\n [(2, 2), (2, 1), (1, 2), (0, 4), (0, 3)],\n [(0, 2), (0, 1), (7, 0)]]',
      note: 'Table 3, Δ: side 0 of the parent is side 5 of child 7, then side 4 of child 6, …' },
  ],
  checks: [
    { tone: 'data', title: 'The statement is this file plus three',
      text: `Only <code>Kind</code> and <code>iter</code> are used from <code>Basic.lean</code>; both are shown below in
        full. <code>Data/Pattern.lean</code> and <code>Data/Clusters.lean</code> are generated (by
        <code>tools/gen_pattern.py</code> from <code>paper/code/hierarchy/combin_8.json</code>, and by
        <code>tools/gen_clusters.py</code> with <code>paper/code/exact/exact.py</code>). Lean takes their contents as
        given; whether they match the spectre paper is tested, not proved: it is part of assumption (M).` },
  ] },

{ id: 'ns', section: 's0', kind: 'namespace', title: 'namespace SpectreKnot.Statement', lines: [24, 25],
  summary: 'Prefixes every name in the file with SpectreKnot.Statement.',
  what: `Everything from here to the last line ([[L379]]) gets the prefix <code>SpectreKnot.Statement.</code>: the full
    name of <code>TheoremA</code> is <code>SpectreKnot.Statement.TheoremA</code>.`,
  how: `<code>namespace X</code> … <code>end X</code>. Inside it, names from the enclosing namespace
    <code>SpectreKnot</code> can be used without their prefix, which is why the file can write <code>Kind</code> and
    <code>Pattern.kids</code>.`,
  checks: [
    { tone: 'ok', title: 'The proofs prove these exact claims',
      text: `The proof files state, inside this same namespace, <code>theorem theoremA : TheoremA</code>
        (<code>ProofA.lean</code>), <code>theoremB_sharp</code> and <code>theoremB</code> (<code>ProofB.lean</code>),
        <code>nestModel</code> and <code>theoremB_strand</code> (<code>ProofStrand.lean</code>), <code>chainModel</code>
        and <code>theoremA_strand</code> (<code>ProofChain.lean</code>), <code>theoremB_exact</code>
        (<code>ProofExact.lean</code>) and <code>grandparent</code> (<code>ProofGrand.lean</code>). To rule out any
        confusion of names, the full names were checked directly: Lean accepts
        <code>example : SpectreKnot.Statement.TheoremA := SpectreKnot.Statement.theoremA</code>, and the same for the
        other eight.` },
  ] },

{ id: 'sec1', section: 's1', kind: 'section', title: 'Section heading', lines: [26, 27],
  what: `§1.`, how: `<code>/-! … -/</code> is a heading comment.` },

{ id: 'Port', section: 's1', kind: 'abbrev', title: 'Port', lines: [28, 32],
  summary: 'A ribbon end at an edge: (tile t, vertex i, s). s = true is R(vᵢ), s = false is L(vᵢ).',
  what: `A port is a ribbon end where a ribbon meets an edge of a tile. It is named by three things: the tile's number
    <code>t</code>; a vertex number <code>i</code> from 0 to 13; and a flag <code>s</code> saying which of the two ports
    beside vertex <code>i</code> is meant: <code>true</code> is R(v<sub>i</sub>), on the edge just after the corner
    (e<sub>i</sub>); <code>false</code> is L(v<sub>i</sub>), on the edge just before it (e<sub>i−1</sub>). So each tile
    has 28 ports. Click the ports in the figure below.`,
  how: `<code>abbrev Port := Nat × Nat × Bool</code>: a new name for an existing type, which Lean unfolds freely, so a
    <code>Port</code> simply <em>is</em> a triple. <code>×</code> groups to the right, so <code>Nat × Nat × Bool</code> is
    <code>Nat × (Nat × Bool)</code>: for a port <code>p</code>, the tile is <code>p.1</code>, the vertex
    <code>p.2.1</code> and the flag <code>p.2.2</code>. Nothing in the type restricts <code>i</code> to 0–13; where that
    matters it is said separately ([[IsPort]]; <code>q.2.1 &lt; 14</code> in [[TheoremB_strand]]).`,
  fig: 'tile',
  checks: [
    { tone: 'ok', title: 'Matches the paper',
      text: `Paper §3.1: R(v<sub>i</sub>) is the port on e<sub>i</sub> near v<sub>i</sub>, and L(v<sub>i</sub>) the port
        on e<sub>i−1</sub> near v<sub>i</sub>. On edge e<sub>i</sub> the two ports are R(v<sub>i</sub>) and
        L(v<sub>i+1</sub>). The vertices are numbered counter-clockwise; the figure is drawn from the paper's turning
        numbers.` },
  ] },

{ id: 'pieceEnd', section: 's1', kind: 'def', title: 'pieceEnd', lines: [33, 40],
  summary: 'The decoration: the other end of the piece that ends at a port.',
  what: `The decoration of the paper's Def 3.1. Inside every tile, 14 ribbon pieces pair up its 28 ports;
    <code>pieceEnd p</code> is the port at the other end of <code>p</code>'s piece. At v<sub>0</sub> and v<sub>1</sub>
    the two crossover pieces join R(v<sub>0</sub>) to R(v<sub>1</sub>) and L(v<sub>0</sub>) to L(v<sub>1</sub>); at each
    of the other twelve vertices a hook turns back round the corner, joining L(v<sub>i</sub>) to R(v<sub>i</sub>). The
    tile figure under [[Port]] shows this: click any port.`,
  how: `<code>def pieceEnd : Port → Port</code>, defined by cases (see the primer). <code>(t, 0, s)</code> fits every port
    at vertex 0 and names its tile <code>t</code> and flag <code>s</code>; one line covers both crossover pieces,
    because <code>s</code> is either <code>true</code> (R) or <code>false</code> (L). The cases are tried in order, so
    the last, <code>(t, i, s)</code>, applies to the vertices other than 0 and 1. <code>!s</code> is "not s": it swaps R
    and L. The tile <code>t</code> never changes: a piece lies inside one tile.`,
  examples: [
    { expr: '[pieceEnd (0,0,true), pieceEnd (0,0,false), pieceEnd (0,1,true), pieceEnd (0,1,false),\n pieceEnd (0,5,true), pieceEnd (0,5,false), pieceEnd (0,13,false)]',
      out: '[(0, 1, true), (0, 1, false), (0, 0, true), (0, 0, false), (0, 5, false), (0, 5, true), (0, 13, true)]' },
  ],
  checks: [
    { tone: 'ok', title: 'A true pairing, as in Def 3.1',
      text: `Applying <code>pieceEnd</code> twice gives back the port, and it never returns its own input; so the 28
        ports really are paired into 14 pieces: 12 hooks and the two crossover pieces. (The first fact is
        <code>pieceEnd_pieceEnd</code> in <code>Linked.lean</code>.)` },
  ] },

{ id: 'sec2', section: 's2', kind: 'section', title: 'Section heading', lines: [41, 42],
  what: `§2.`, how: `A heading comment.` },

{ id: 'Patch', section: 's2', kind: 'structure', title: 'Patch', lines: [43, 52],
  summary: 'A finite set of tiles and which of their edges are glued (plus rim and corners, for supertiles).',
  what: `A patch is a finite set of tiles with a record of which of their edges are glued together. Four fields:
    <code>tiles</code>, how many tiles (numbered 0 … tiles − 1); <code>glue t i</code>, what lies across edge
    e<sub>i</sub> of tile <code>t</code>: <code>some (t', j)</code> if it is the same edge as e<sub>j</sub> of tile
    <code>t'</code>, <code>none</code> if it is on the rim; <code>rim</code>, the boundary edges in order; and
    <code>vtx</code>, where the supertile's six corners fall along the rim, then the rim's length. There are no
    coordinates: the geometry enters only through which edges meet.`,
  how: `<code>structure Patch where</code>, one field per line, each <code>name : Type</code>. <code>glue : Nat → Nat →
    Option (Nat × Nat)</code> takes a tile number and an edge number. It has a value for every pair of numbers,
    including tiles that do not exist; only real tiles and edges 0–13 matter. Patches are built with
    <code>⟨…⟩</code> ([[L151]], [[L155]], [[L246]]) or by field names ([[L122]]).`,
  checks: [
    { tone: 'ok', title: 'The orientation convention',
      text: `The two tiles on either side of a shared edge run along it in opposite directions, so v<sub>i</sub> of
        <code>t</code> is v<sub>j+1</sub> of <code>t'</code> and v<sub>i+1</sub> of <code>t</code> is v<sub>j</sub> of
        <code>t'</code>, as the doc comment says. [[across]] relies on this.` },
    { tone: 'note', title: 'A Patch can be any record',
      text: `Nothing in the type forces <code>glue</code> to be consistent (if <code>t</code> is glued to <code>t'</code>,
        then <code>t'</code> back to <code>t</code>) or <code>rim</code> to list exactly the unglued edges. For the
        supertiles built in §3 both are proved in other files (<code>super_glueSymm</code> in <code>Linked.lean</code>;
        <code>good</code> in <code>ProofA.lean</code>). The theorems need no more than they say.` },
  ] },

{ id: 'nsPatch', section: 's2', kind: 'namespace', title: 'namespace Patch and variable P', lines: [53, 56],
  summary: 'The next definitions are Patch.IsPort, Patch.across, …, each taking a patch P first.',
  what: `Up to <code>end Patch</code> ([[L105]]) the definitions are <code>Patch.IsPort</code>,
    <code>Patch.across</code>, <code>Patch.Follow</code>, <code>Patch.turn</code> and so on, and each takes a patch
    <code>P</code> as its first argument.`,
  how: `<code>variable (P : Patch)</code> adds <code>(P : Patch)</code> to every following definition that mentions
    <code>P</code>. With the namespace this allows dot notation: <code>P.across p</code> means <code>Patch.across P
    p</code>, and <code>(N b).NoClosedStrand</code> means <code>Patch.NoClosedStrand (N b)</code>.` },

{ id: 'IsPort', section: 's2', kind: 'def', title: 'IsPort', lines: [57, 59],
  summary: 'p is a port of a real tile of the patch: tile < P.tiles and vertex < 14.',
  what: `<code>P.IsPort p</code>: the port <code>p</code> belongs to a real tile of the patch (tile number below
    <code>P.tiles</code>) and its vertex number is one of 0–13. Either flag is allowed.`,
  how: `The result type is <code>Prop</code>: <code>IsPort p</code> is a claim, not a computed <code>Bool</code>.
    <code>∧</code> is "and"; <code>p.1</code> is the tile and <code>p.2.1</code> the vertex (see [[Port]]).`,
  checks: [{ tone: 'ok', title: 'As intended', text: `Exactly the 28 ports of each of the patch's tiles.` }] },

{ id: 'across', section: 's2', kind: 'def', title: 'across', lines: [60, 67],
  summary: 'The straight-through rule: the port a ribbon continues as across an edge, or none on the rim.',
  what: `The straight-through rule of the paper's Def 3.2. Where a ribbon reaches an edge, it goes straight through the
    crossing point into the tile on the other side. <code>P.across p</code> is the port of that tile where it
    continues: across edge e<sub>i</sub> = e<sub>j</sub> of <code>t'</code>, R(v<sub>i</sub>) continues as
    R(v<sub>j</sub>) of <code>t'</code>; across e<sub>i−1</sub> = e<sub>j</sub>, L(v<sub>i</sub>) continues as
    L(v<sub>j+1</sub>). On the rim the answer is <code>none</code>. The figure below shows the four ports at one
    crossing point; click them.`,
  how: `<code>Port → Option Port</code>: the answer is an <code>Option</code>, because there may be no tile on the other
    side. Two cases, by the flag. Each looks up the edge with <code>P.glue</code> and converts the answer with
    <code>.map</code>, which leaves <code>none</code> as <code>none</code> and turns <code>some x</code> into
    <code>some (f x)</code>; so a rim edge gives <code>none</code> automatically. <code>(i + 13) % 14</code> is i − 1
    counted round the 14 vertices (<code>%</code> is the remainder), so that i = 0 gives 13; likewise
    <code>(j + 1) % 14</code> turns 13 into 0.`,
  fig: 'across',
  examples: [
    { expr: '(level1 .Delta).across (0,0,true)', out: 'some (7, 5, true)',
      note: 'In the level-1 Δ, edge e₀ of tile 0 is edge e₅ of tile 7.' },
    { expr: '(level1 .Delta).across (0,0,false)', out: 'some (1, 3, false)',
      note: 'L(v₀) lies on e₁₃; edge e₁₃ of tile 0 is edge e₂ of tile 1, so the ribbon continues as L(v₃) of tile 1.' },
    { expr: '(level1 .Delta).across (0,5,true)', out: 'none', note: 'Edge e₅ of tile 0 is on the rim.' },
  ],
  checks: [
    { tone: 'ok', title: 'Re-derived from the paper: both cases are right',
      text: `Def 3.2: if <code>t</code> and <code>t'</code> share an edge with ends x and y, the port of <code>t</code>
        near x joins the port of <code>t'</code> near y. Edge e<sub>i</sub> of <code>t</code> runs from v<sub>i</sub>
        to v<sub>i+1</sub>; <code>t'</code> runs it the other way, so v<sub>i+1</sub> of <code>t</code> is
        v<sub>j</sub> of <code>t'</code>. The port of <code>t</code> near v<sub>i</sub> is R(v<sub>i</sub>); it joins
        the port of <code>t'</code> near v<sub>j</sub> on e<sub>j</sub>, which is R(v<sub>j</sub>): [[L64]]. For
        L(v<sub>i</sub>), on e<sub>i−1</sub> = e<sub>j</sub> of <code>t'</code>, v<sub>i</sub> of <code>t</code> is
        v<sub>j</sub> of <code>t'</code>, so it joins the port of <code>t'</code> near v<sub>j+1</sub>, which is
        L(v<sub>j+1</sub>): [[L66]]. When the gluing is symmetric, applying <code>across</code> twice gives back the
        port.` },
  ] },

{ id: 'Follow', section: 's2', kind: 'inductive', title: 'Follow', lines: [68, 75],
  summary: 'P.Follow p r: following the ribbon from p, you leave the patch at the rim port r.',
  what: `Following a ribbon: from port <code>p</code>, go along its piece; if the far end is on the rim, stop there;
    otherwise cross the edge and carry on. <code>P.Follow p r</code> says that this ends, at the rim port
    <code>r</code>.`,
  how: `A relation defined by two rules (see "Rules" in the primer). Rule <code>leave</code>: if the far end of
    <code>p</code>'s piece has nothing across it, following from <code>p</code> leaves there. Rule <code>next</code>:
    if it continues across to <code>q</code>, and following from <code>q</code> leaves at <code>r</code>, then so does
    following from <code>p</code>. Because only finite derivations count, a ribbon that goes round for ever never gives
    any <code>Follow</code>: that is what makes this a test for loops.`,
  examples: [
    { expr: '-- following from R(v₀) of the original tile, which is tile 1 of N₁\n-- (computed with a short helper that applies pieceEnd and across in turn)',
      out: '(1,0,true) → (1,1,true) | (8,2,true) → (8,2,false) | (7,7,false) → (7,7,true)\n| (8,0,true) → (8,1,true) | (7,6,true) → (7,6,false) | (0,1,false) → (0,0,false)\n| (1,3,false) → (1,3,true) | (0,12,true) → (0,12,false) | (1,5,false) → (1,5,true)  leaves',
      note: 'Arrows are pieces, bars are edge crossings. Nine pieces, then edge e₅ of tile 1 is on the rim. So (N 1).Follow (1,0,true) (1,5,true) holds: eight uses of next and one of leave.' },
  ],
  checks: [
    { tone: 'ok', title: 'As intended',
      text: `Each step is fixed by the port, so <code>Follow</code> can be derived only along the actual ribbon, and its
        end <code>r</code> is a rim port.` },
  ] },

{ id: 'NoClosedStrand', section: 's2', kind: 'def', title: 'NoClosedStrand', lines: [76, 79],
  summary: 'From every port of the patch, following the ribbon leaves the patch.',
  what: `From every port of every tile of the patch, following the ribbon leads out of the patch in finitely many
    steps. So no strand closes up into a loop inside the patch.`,
  how: `<code>∀ p, P.IsPort p → ∃ r, P.Follow p r</code>: for every port <code>p</code> of <code>P</code> there is an
    <code>r</code> such that following from <code>p</code> leaves at <code>r</code>.`,
  checks: [
    { tone: 'ok', title: 'Why this means "no closed strand"',
      text: `A closed strand never reaches the rim, so its ports would have no <code>r</code>. Conversely, if following
        from <code>p</code> never ends, it must meet some port twice, since the patch has finitely many; and as every
        step can be undone (pieces and crossings are pairings when the gluing is symmetric), the first repeat is
        <code>p</code> itself: a loop.` },
  ] },

{ id: 'Linked', section: 's2', kind: 'inductive', title: 'Linked', lines: [80, 86],
  summary: 'P.Linked p q: q is reached from p by moves along pieces and across glued edges, inside P.',
  what: `Same strand. <code>P.Linked p q</code> says: starting at <code>p</code>, you can reach <code>q</code> by moving
    along pieces and straight across glued edges, any number of times, without leaving the patch.`,
  how: `Three rules: <code>refl</code>, <code>p</code> is reached from itself; <code>piece</code>, if <code>q</code> is
    reached, so is the other end of its piece; <code>edge</code>, if <code>q</code> is reached and continues across
    its edge as <code>q'</code>, then <code>q'</code> is reached. The start <code>p</code> is written before the colon,
    so it is fixed throughout.`,
  checks: [
    { tone: 'note', title: 'Reachability in one direction',
      text: `As defined, <code>Linked p q</code> means "q is reached from p". It is symmetric when the gluing is; for
        supertiles that is proved (<code>linked_symm</code>). Theorem B uses <code>Linked p q</code> exactly as
        written, so its meaning does not depend on that.` },
  ] },

{ id: 'turn', section: 's2', kind: 'def', title: 'turn', lines: [87, 91],
  summary: 'Turning about a point: the next corner round it, across the edge that ends there.',
  what: `A corner <code>(t, i)</code> is vertex v<sub>i</sub> of tile <code>t</code>. The edge e<sub>i−1</sub> ends
    there. If it is glued to edge e<sub>j</sub> of tile <code>t'</code>, the same point is vertex v<sub>j</sub> of
    <code>t'</code>: the next corner round the point. If the edge is on the rim there is no next corner
    (<code>none</code>).`,
  how: `<code>c.1</code> is the tile and <code>c.2</code> the vertex; <code>(c.2 + 13) % 14</code> is i − 1 counted
    round 14. The answer is just what <code>glue</code> says: the two tiles run along a glued edge in opposite
    directions, so the end v<sub>i</sub> of e<sub>i−1</sub> in <code>t</code> is the start v<sub>j</sub> of
    e<sub>j</sub> in <code>t'</code>.`,
  examples: [
    { expr: '(N 1).turn (0, 0)', out: 'some (1, 2)', note: 'Vertex v₀ of tile 0 of N₁ is vertex v₂ of tile 1.' },
  ],
  checks: [
    { tone: 'ok', title: 'One way round',
      text: `Each turn crosses the edge that ends at the vertex, so turning goes round the point in one sense. With
        symmetric gluing it can be undone (across e<sub>i</sub>), so no corner is reached from two others.` },
  ] },

{ id: 'turns', section: 's2', kind: 'def', title: 'turns', lines: [92, 96],
  summary: 'Turning n times about a point, across glued edges only.',
  what: `Turning <code>n</code> times from a corner: <code>some</code> of the corner reached, or <code>none</code> if
    the rim is reached on the way.`,
  how: `<code>Option.bind</code>: <code>none</code> stays <code>none</code>; from <code>some c'</code>, carry on with
    <code>turns n c'</code>. So one turn first, then <code>n</code> more.`,
  examples: [
    { expr: '(List.range 4).map fun n => (N 1).turns n (1, 0)', out: '[some (1, 0), some (8, 4), some (1, 0), some (8, 4)]',
      note: 'Two tiles round this point: after two turns the corner comes back.' },
    { expr: '(List.range 3).map fun n => (N 1).turns n (7, 0)', out: '[some (7, 0), none, none]',
      note: 'Vertex 0 of N₁, which is vertex v₀ of tile 7: the first turn reaches the rim.' },
  ] },

{ id: 'Surrounded', section: 's2', kind: 'def', title: 'Surrounded', lines: [97, 100],
  summary: 'Vertex v_i of tile t is surrounded: turning about it comes back to it.',
  what: `Turning about vertex v<sub>i</sub> of tile <code>t</code>, across glued edges only, comes back to where it
    started after some positive number of turns. So the tiles of the patch close up all round the point: it is not on
    the rim.`,
  how: `<code>∃ n, 0 < n ∧ …</code>: there is a positive <code>n</code> with <code>turns n (t, i) = some (t, i)</code>.`,
  checks: [
    { tone: 'ok', title: 'Not built into the definitions',
      text: `A vertex on the rim of a supertile is never surrounded: the corner beside the rim edge that ends there
        looks across the rim (<code>rim_not_surrounded</code>, proved). On instances, computed by Lean: of the 126
        corners of the tiles of N₁, 72 are surrounded in N₁, 115 in N₂ and all 126 in N₃.` },
    { tone: 'note', title: 'Corners, not points',
      text: `Where several tiles meet, the point is a corner of each. Turning about one of them visits the others, so
        they are surrounded or not together.` },
  ] },

{ id: 'side', section: 's2', kind: 'def', title: 'side', lines: [101, 104],
  summary: 'Side j of a supertile: its rim edges from vertex j to vertex j+1.',
  what: `Side <code>j</code> of a supertile: the stretch of its rim from vertex <code>j</code> to vertex
    <code>j + 1</code>.`,
  how: `<code>P.vtx.getD j 0</code> is entry <code>j</code> of <code>vtx</code> (the rim position of vertex
    <code>j</code>), or 0 if there is none. <code>drop k</code> skips the first <code>k</code> rim edges, and
    <code>take</code> keeps the next vtx[j+1] − vtx[j] of them.`,
  examples: [
    { expr: '(N 1).vtx', out: '[0, 10, 15, 23, 30, 40, 46]' },
    { expr: '(List.range 6).map fun j => ((N 1).side j).length', out: '[10, 5, 8, 7, 10, 6]',
      note: 'The side lengths of the level-1 Δ, as in the paper.' },
  ],
  checks: [
    { tone: 'ok', title: 'The defaults do not fire',
      text: `For every supertile of level 1 or more, <code>vtx</code> has seven entries, so the <code>getD … 0</code>
        defaults are never used. A single tile has an empty <code>vtx</code>, but its sides are never asked for.` },
  ] },

{ id: 'endPatch', section: 's2', kind: 'end', title: 'end Patch', lines: [105, 106],
  what: `Closes the namespace <code>Patch</code> opened on [[L53]].`, how: `<code>end Patch</code>.` },

{ id: 'sec3', section: 's3', kind: 'section', title: 'Section heading', lines: [107, 108],
  what: `§3.`, how: `A heading comment.` },

{ id: 'compose', section: 's3', kind: 'def', title: 'compose', lines: [109, 149],
  summary: 'Builds a supertile of kind T from its children, by Tables 1–3 (Prop 2.4 as a recipe).',
  what: `Builds a supertile from its children, following the paper's Prop 2.4 read as a recipe. The parent's tiles are
    the children's, numbered child by child. Gluing inside each child is kept. Where Table 2 says that side
    <code>j</code> of child <code>c</code> is side <code>j'</code> of child <code>c'</code>, the two sides are glued
    edge by edge, in opposite orders. The parent's rim and its six vertices are read off Table 3. This is the longest
    definition in the file; the steps are below.`,
  how: `<code>compose (T : Kind) (child : Nat → Patch)</code> takes the parent's kind and a function giving the
    <code>c</code>-th child. A chain of <code>let</code>s names helper values; then
    <code>{ tiles := …, glue := …, rim := …, vtx := … }</code> builds the parent field by field.`,
  fig: 'compose',
  clauses: [
    { lines: [109, 113], title: 'Doc comment and signature',
      what: `The recipe in words. The caller must pass children of the right kinds and level; [[super]] does.` },
    { lines: [114, 121], title: 'Helpers: n, off, owner, shift',
      what: `<code>n</code>, the number of children (8, or 7 for Γ). <code>off c</code>, the number of the first tile of
        child <code>c</code>: the total of the tiles of children 0 … c−1. <code>owner t</code>, the child containing
        parent tile <code>t</code>. <code>shift c e</code>, edge <code>e</code> of child <code>c</code> renumbered into
        the parent.`,
      how: `<code>off</code>: the list [0, …, c−1], each entry replaced by that child's tile count, then summed.
        <code>owner</code>: count the children whose first tile is at or before <code>t</code>, minus 1; this works
        because <code>off</code> starts at 0 and strictly increases (every child has at least one tile).`,
      examples: [{ expr: '-- off c for N₂ (a Δ of level 2), c = 0 … 8', out: '[0, 9, 18, 27, 36, 45, 54, 63, 71]',
        note: 'Seven children of 9 tiles, and the Γ child (last) with 8.' }] },
    { lines: [122, 123], title: 'tiles',
      what: `The parent has as many tiles as its children together.` },
    { lines: [124, 130], title: 'glue, inside a child',
      what: `For parent tile <code>t</code> and edge <code>i</code>: find its child <code>c</code> and its number
        <code>t₀</code> inside that child. If the child glues that edge, the parent glues it to the same edge,
        renumbered.`,
      how: `<code>glue := fun t i => …</code> defines the field as a function. <code>match … with</code> looks at the
        child's answer: <code>| some e => some (shift c e)</code>.` },
    { lines: [131, 135], title: 'glue, on a child\'s rim: which side, how far along',
      what: `Otherwise the edge is on the child's rim. Find its position <code>pos</code> in the child's rim list, the
        side <code>j</code> of the child that contains it, and how many edges of that side come before it
        (<code>o</code>).`,
      how: `<code>rim.findIdx? (· == (t₀, i))</code> is <code>some k</code> for the first position <code>k</code> holding
        <code>(t₀, i)</code>, and <code>.getD 0</code> takes the <code>k</code>. <code>j</code> counts the vertices at or
        before <code>pos</code>, minus 1, as <code>owner</code> does.` },
    { lines: [136, 143], title: 'glue, on a child\'s rim: Table 2',
      what: `Look up side <code>j</code> of child <code>c</code> in Table 2. If it lies on the parent's rim, the edge
        stays unglued. If it is side <code>j'</code> of child <code>c'</code>, glue the edge to the edge of that side
        that comes <code>o</code>-th from its <em>end</em>: the two children run along their shared boundary in
        opposite directions.`,
      how: `<code>((Pattern.adj T).getD c []).getD j none</code>: row <code>c</code> of <code>T</code>'s Table 2, then
        entry <code>j</code>. <code>s[s.length - 1 - o]?</code> is entry length−1−o of <code>s</code>, as an
        <code>Option</code>, and <code>.map (shift c')</code> renumbers it into the parent.`,
      examples: [
        { expr: '(N 2).glue 10 5', out: 'some (33, 8)',
          note: 'Tile 10 of N₂ is the original tile (tile 1 of child 1). Its edge e₅ is on N₁\'s rim at position 34. N₁\'s vertices are at [0, 10, 15, 23, 30, 40, 46], so j = 4 and o = 34 − 30 = 4. Table 2 (Δ, child 1, side 4) says: side 0 of child 3. That side has 10 edges; entry 10 − 1 − 4 = 5 is (6, 8), and child 3 starts at tile 27, giving (33, 8). And (N 2).glue 33 8 = some (10, 5): glued back.' }] },
    { lines: [144, 145], title: 'rim',
      what: `The parent's rim: for each piece <code>(c, j)</code> listed in Table 3, in order, side <code>j</code> of
        child <code>c</code>, backwards, renumbered.`,
      how: `<code>flatMap id</code> flattens Table 3's row (one list per parent side) into one list of pieces; the
        second <code>flatMap</code> replaces each piece by that side, reversed and renumbered, and joins the results.`,
      examples: [{ expr: '(N 2).rim.take 6', out: '[(69, 0), (69, 1), (69, 2), (63, 3), (63, 4), (54, 5)]',
        note: 'N₂ starts at side 5 of child 7 (the Γ, tiles 63–70), read backwards.' }] },
    { lines: [146, 149], title: 'vtx',
      what: `Vertex <code>J</code> of the parent sits where side <code>J</code> begins: after the pieces Table 3 lists
        for sides 0 … J−1. For J = 6 this is the length of the whole rim.`,
      examples: [{ expr: '(N 2).vtx', out: '[0, 42, 57, 91, 114, 156, 182]',
        note: 'N₂ has 71 tiles and a rim of 182 edges, as in the paper.' }] },
  ],
  checks: [
    { tone: 'ok', title: 'Directions are right',
      text: `Two patches with the same orientation that share a boundary run along it in opposite directions, so the
        o-th edge from one end is the o-th from the other end: [[L143]]. The parent's rim reverses each child's side
        because a parent's own orientation is opposite to its children's (the paper's Def 2.2). The data agree: the
        rim of N₁ begins (7, 13), (7, 12), (7, 11), tile edges in decreasing order.` },
    { tone: 'note', title: 'Silent fallbacks',
      text: `Several lookups have a fallback for "not found": <code>findIdx? … getD 0</code> ([[L133]]),
        <code>getD c []</code> and <code>getD j none</code> ([[L137]]), <code>s[…]?</code> and the subtraction
        <code>s.length - 1 - o</code>, which stops at 0 ([[L143]]). If the tables or the children were inconsistent,
        these would quietly give a wrong gluing instead of an error. They do not fire for the real supertiles: the
        proofs show, for every supertile of level 1 or more, that the rim list is exactly the unglued edges, each once,
        and that the gluing is symmetric; and <code>Tests.lean</code> checks level 2 against exact geometry, edge for
        edge. The definition alone does not guarantee it.` },
  ] },

{ id: 'tile', section: 's3', kind: 'def', title: 'tile', lines: [150, 152],
  summary: 'A patch of one tile: tile 0, nothing glued, rim = its 14 edges.',
  what: `A patch of a single tile: tile number 0, nothing glued, its 14 edges round the rim, and no hexagon corners.`,
  how: `<code>⟨1, fun _ _ => none, …, []⟩</code> gives the fields in order: one tile; a <code>glue</code> that ignores
    both arguments and returns <code>none</code>; the rim [(0,0), …, (0,13)]; an empty <code>vtx</code>.`,
  checks: [{ tone: 'ok', title: 'Only its gluing matters',
    text: `The <code>rim</code> and <code>vtx</code> of a single tile are never used: <code>compose</code> never takes
      level-0 children, because level 1 comes from the data.` }] },

{ id: 'level1', section: 's3', kind: 'def', title: 'level1', lines: [153, 156],
  summary: 'The nine level-1 supertiles, read from Data/Clusters.lean.',
  what: `The level-1 supertile of kind <code>K</code>: the spectre paper's Fig. 4.1 clusters (our Fig. 3), read from the
    data file.`,
  how: `<code>Clusters.glue K</code> has one entry per tile, each a list with one entry per edge. <code>.getD t []</code>
    picks the tile's list, then <code>.getD i none</code> the edge's entry.`,
  examples: [
    { expr: '((level1 .Delta).tiles, (level1 .Delta).rim.length, (level1 .Delta).vtx)',
      out: '(9, 46, [0, 10, 15, 23, 30, 40, 46])' },
    { expr: '(List.range 14).map fun i => (level1 .Delta).glue 1 i',
      out: '[some (8, 3), some (8, 2), some (0, 13), some (0, 12), some (0, 11), none, none,\n some (2, 2), some (2, 1), some (2, 0), some (3, 1), some (3, 0), some (8, 5), some (8, 4)]',
      note: 'Tile 1 is the original tile N₀ (child 1 of the Δ). Edges e₅ and e₆ are on the rim of N₁.' },
  ],
  checks: [{ tone: 'data', title: 'Data, trusted',
    text: `Computed by <code>paper/code/exact/exact.py</code> from the spectre paper's tile placements, in exact
      arithmetic. Lean takes it as given. Tests: level 2 built from this data matches the exact construction, and the
      side lengths match Prop 6.1. The proofs check by computation that each of the nine clusters has the signature
      the induction starts from (<code>good_one</code>).` }] },

{ id: 'super', section: 's3', kind: 'def', title: 'super', lines: [157, 163],
  summary: 'super m K: the supertile of level m and kind K.',
  what: `<code>super m K</code> is the supertile of level <code>m</code> and kind <code>K</code>. Level 0 is a single
    tile; level 1 is the data; every higher level is composed from children one level down, of the kinds Table 1
    lists.`,
  how: `Defined by cases on the level: <code>0, _</code> (any kind), <code>1, K</code>, and <code>m + 2, T</code> (level
    2 or more). Lean accepts the recursion because <code>super</code> calls itself only at a lower level.
    <code>.getD c .Gamma</code> reads entry <code>c</code> of Table 1's row, with a fallback that is never used.`,
  examples: [{ expr: '((N 2).tiles, (N 2).rim.length)', out: '(71, 182)' }],
  checks: [
    { tone: 'note', title: 'Level-0 Γ is one tile, not the Mystic',
      text: `In the paper the level-0 Γ is the two-tile Mystic; here <code>super 0 .Gamma</code> is a single tile. It
        makes no difference: level 0 is used only for N₀ (one tile, right), for <code>nestShift 0</code> (the size of a
        level-0 Ξ, one tile, right), and in Theorem A's level-0 case. <code>compose</code> never receives level-0
        children.` },
    { tone: 'note', title: 'A specification, not a fast program',
      text: `Evaluating <code>super</code> is quick up to level 3 and very slow beyond. That does not matter: the proofs
        reason about it rather than run it at high levels.` },
  ] },

{ id: 'sec4', section: 's4', kind: 'section', title: 'Section heading', lines: [164, 165],
  what: `§4.`, how: `A heading comment.` },

{ id: 'N', section: 's4', kind: 'def', title: 'N', lines: [166, 168],
  summary: 'N b: the block of the nest, the Δ-supertile of level b.',
  what: `The block N<sub>b</sub> of the nest: the Δ-supertile of level <code>b</code>. N₀ is the original tile. The
    explorer below follows a tile through the numbering of §4 and §6.`,
  how: `<code>def N (b : Nat) : Patch := super b .Delta</code>.`,
  examples: [{ expr: '((N 0).tiles, (N 1).tiles, (N 2).tiles, (N 3).tiles)', out: '(1, 9, 71, 559)' }],
  fig: 'nest' },

{ id: 'nestShift', section: 's4', kind: 'def', title: 'nestShift', lines: [169, 171],
  summary: 'Where N_b starts inside N_{b+1}: the number of tiles of child 0, a Ξ.',
  what: `Where N<sub>b</sub> starts inside N<sub>b+1</sub>. N<sub>b</sub> is child 1 of N<sub>b+1</sub>, and child 0 is a
    Ξ, so N<sub>b</sub>'s tiles come straight after those of a level-<code>b</code> Ξ.`,
  how: `<code>(super b .Xi).tiles</code>.`,
  examples: [{ expr: '(nestShift 0, nestShift 1, nestShift 2, nestShift 3)', out: '(1, 9, 71, 559)' }],
  checks: [{ tone: 'ok', title: 'Matches Table 1', text: `Δ's row of Table 1 begins Ξ, Δ: child 0 is a Ξ, child 1 a Δ.` }] },

{ id: 'up', section: 's4', kind: 'def', title: 'up', lines: [172, 176],
  summary: 'up b k t: tile t of N_b, renumbered as a tile of N_{b+k}.',
  what: `Tile <code>t</code> of N<sub>b</sub>, renumbered as a tile of N<sub>b+k</sub>: shift it into N<sub>b+1</sub>,
    then into N<sub>b+2</sub>, and so on, <code>k</code> times.`,
  how: `Two cases on <code>k</code>: zero steps leave <code>t</code>; otherwise add N<sub>b</sub>'s offset in
    N<sub>b+1</sub> and go up <code>k</code> more levels from <code>b + 1</code>.`,
  examples: [{ expr: '(List.range 5).map fun k => up 0 k 0', out: '[0, 1, 10, 81, 640]',
    note: 'The original tile is tile 0 of N₀, tile 1 of N₁, 10 of N₂, 81 of N₃ and 640 of N₄.' }] },

{ id: 'upPort', section: 's4', kind: 'def', title: 'upPort', lines: [177, 179],
  summary: 'A port of N_b as a port of N_{b+k}: same vertex and flag, renumbered tile.',
  what: `Port <code>p</code> of N<sub>b</sub> as a port of N<sub>b+k</sub>: the same vertex and flag, on the renumbered
    tile.`,
  how: `<code>(up b k p.1, p.2.1, p.2.2)</code>.` },

{ id: 'sec5', section: 's5', kind: 'section', title: 'Section heading', lines: [180, 181],
  what: `§5: the claims start here.`, how: `A heading comment.` },

{ id: 'TheoremA', section: 's5', kind: 'claim', title: 'TheoremA', lines: [182, 184],
  summary: 'No supertile of any level or kind contains a closed strand.',
  what: `For every level <code>m</code> and every kind <code>K</code>, the supertile <code>super m K</code> contains no
    closed strand.`,
  how: `A <code>def</code> whose value is a <code>Prop</code>: a claim, stated here and proved in <code>ProofA.lean</code>
    as <code>theorem theoremA : TheoremA</code>. The types of <code>m</code> (<code>Nat</code>) and <code>K</code>
    (<code>Kind</code>) are worked out from how they are used.`,
  checks: [
    { tone: 'ok', title: 'Says what the comment says',
      text: `All levels, including 0 (trivial) and 1 (the data), and all nine kinds.` },
    { tone: 'data', title: 'About supertiles; the plane is §7',
      text: `This is about single supertiles. The step to a whole tiling whose hierarchy covers the plane is
        [[TheoremA_strand]] in §7, which uses this theorem. What stays outside Lean is assumption (M).` },
  ] },

{ id: 'TheoremB', section: 's5', kind: 'claim', title: 'TheoremB', lines: [185, 193],
  summary: 'The nest has no boundary, no closed strand, and any two ports lie on one strand of a larger block.',
  what: `Three claims about the nest, joined by "and" (<code>∧</code>).`,
  how: `<code>A ∧ B ∧ C</code>, each part in brackets. Proved in <code>ProofB.lean</code> as <code>theorem theoremB :
    TheoremB</code>.`,
  clauses: [
    { lines: [185, 189], title: 'Doc comment and header', what: `The three claims in words.` },
    { lines: [190, 190], title: '(1) No boundary',
      what: `For every block N<sub>b</sub> with b ≥ 1, every tile <code>t</code> of it and every edge e<sub>i</sub>: two
        levels up, in N<sub>b+2</sub>, that edge is glued to something.`,
      how: `<code>up b 2 t</code> is the tile's number in N<sub>b+2</sub>. <code>isSome</code> is true for <code>some
        …</code> and false for <code>none</code>.`,
      checks: [{ tone: 'ok', title: 'Enough, with NestModel',
        text: `It says only that the edge is glued, not to what; [[NestModel]] (e) adds that it is glued to a different
          tile, which is glued back. Starting at b = 1 loses nothing: N₀'s tile is a tile of N₁.` }] },
    { lines: [191, 191], title: '(2) No closed strand',
      what: `No block contains a closed strand: the case K = Δ of [[TheoremA]].` },
    { lines: [192, 193], title: '(3) One strand eventually',
      what: `For any two ports <code>p</code>, <code>q</code> of a block N<sub>b</sub>, there is a <code>k</code> such that
        in N<sub>b+k</sub> they lie on the same strand.`,
      checks: [{ tone: 'ok', title: 'Not built into the definitions',
        text: `<code>Tests.lean</code> runs the same definitions along a different chain of supertiles (the paper's
          Remark 10.1) and finds three strands, not one. So (3) is a real property of the nest.` }] },
  ] },

{ id: 'TheoremB_sharp', section: 's5', kind: 'claim', title: 'TheoremB_sharp', lines: [194, 200],
  summary: 'For b ≥ 1: any two ports of N_b are on one strand of N_{b+4}, and of N_{b+3} if b is even.',
  what: `The paper's bound. For b ≥ 1, any two ports of N<sub>b</sub> lie on one strand of N<sub>b+4</sub>; and if
    <code>b</code> is even, already of N<sub>b+3</sub>.`,
  how: `The hypotheses are joined by <code>→</code>; <code>b % 2 = 0</code> says <code>b</code> is even.`,
  checks: [{ tone: 'ok', title: 'Matches the paper\'s Table 5',
    text: `N₁ (b = 1, odd): 10, 2, 2, then 1 strand four levels up. N₂ (b = 2, even): 37, 2, then 1 three levels up.
      b = 0 (the original tile) is left out here; Theorem B (3) covers it.` }] },

{ id: 'TwoStrands', section: 's5', kind: 'def', title: 'TwoStrands', lines: [201, 207],
  summary: 'k levels up, the ports of N_b lie on exactly two strands of N_{b+k}.',
  what: `Exactly two strands of N<sub>b+k</sub> pass through N<sub>b</sub>: there are two ports <code>p</code>,
    <code>q</code> of N<sub>b</sub> that are not on one strand of N<sub>b+k</sub>, and every port of N<sub>b</sub> is on
    the strand of one of them.`,
  how: `<code>¬</code> is "not". The ports are taken up to N<sub>b+k</sub> with <code>upPort</code>, as in
    [[TheoremB_sharp]].`,
  checks: [
    { tone: 'ok', title: 'Exactly two',
      text: `In a supertile, same strand is symmetric and transitive (<code>linked_symm</code>,
        <code>Linked.trans</code>), so the strands of <code>p</code> and <code>q</code> are two different strands and
        there is no third.` },
  ] },

{ id: 'TheoremB_exact', section: 's5', kind: 'claim', title: 'TheoremB_exact', lines: [208, 212],
  summary: 'For b ≥ 1: the ports of N_b lie on two strands of N_{b+2}, and, for odd b, of N_{b+3}.',
  what: `The paper's bound cannot be improved. For b ≥ 1 the ports of N<sub>b</sub> lie on exactly two strands of
    N<sub>b+2</sub>, and, if <code>b</code> is odd, on exactly two strands of N<sub>b+3</sub>. With [[TheoremB_sharp]]
    this is the last two rows of the paper's Table 5: 2, 1, 1 strands two, three and four levels up for even
    <code>b</code>, and 2, 2, 1 for odd <code>b</code>. Proved in <code>ProofExact.lean</code>.`,
  how: `<code>b % 2 = 1</code> says <code>b</code> is odd.`,
  checks: [
    { tone: 'ok', title: 'Matches the computed counts',
      text: `<code>Tests.lean</code> computes 10, 2, 2 strands one, two and three levels above N₁ (odd), and 37, 2 above
        N₂ (even), as in Table 5.` },
  ] },

{ id: 'Grandparent', section: 's5', kind: 'claim', title: 'Grandparent', lines: [213, 218],
  summary: 'For b ≥ 1: every vertex of every tile of N_b is surrounded by tiles of N_{b+2}.',
  what: `The paper's Lemma 8.3(a), the Grandparent Lemma, at the vertices of tiles. For b ≥ 1, every vertex of every
    tile of N<sub>b</sub> is surrounded in N<sub>b+2</sub>, so N<sub>b</sub> does not reach the rim of
    N<sub>b+2</sub>. Proved in <code>ProofGrand.lean</code>.`,
  how: `<code>up b 2 t</code> is the tile's number in N<sub>b+2</sub>; <code>i</code> runs over its 14 vertices.`,
  checks: [
    { tone: 'ok', title: 'Two levels are needed',
      text: `One level up is not enough: side 2 of N<sub>b</sub> lies on the rim of N<sub>b+1</sub>.
        <code>Tests.lean</code> finds corners of N₁ that are not surrounded in N₂, and of N₂ in N₃, while all are in N₃
        and N₄.` },
    { tone: 'ok', title: 'It gives Theorem B (1) again',
      text: `Turning about v<sub>i+1</sub> first crosses e<sub>i</sub>, so if v<sub>i+1</sub> is surrounded,
        e<sub>i</sub> is glued: every edge of N<sub>b</sub> is glued in N<sub>b+2</sub>, as [[TheoremB]] (1) says.` },
    { tone: 'data', title: 'Vertices of tiles, not points of the plane',
      text: `The paper's (a) is about points of the plane. Here a point is a vertex of tiles, and "not on the rim" means
        that the tiles close up round it. That real supertiles are glued like these patches is assumption (M).` },
  ] },

{ id: 'sec6', section: 's6', kind: 'section', title: 'Section heading', lines: [219, 220],
  what: `§6.`, how: `A heading comment.` },

{ id: 'gid', section: 's6', kind: 'def', title: 'gid', lines: [221, 230],
  summary: 'gid b t: the number, in the whole nest tiling, of tile t of N_b.',
  what: `Numbers all the tiles of the nest tiling 0, 1, 2, … so that every block N<sub>b</sub> gets the numbers
    0 … |N<sub>b</sub>| − 1. Inside N<sub>b+1</sub>, child 0 has the tiles 0 … nestShift b − 1, child 1 (= N<sub>b</sub>)
    the next |N<sub>b</sub>|, and later children the rest. A tile of child 1 keeps its number in N<sub>b</sub>; a tile of
    child 0 comes just after N<sub>b</sub>'s numbers; a tile of a later child keeps its own number. Try the explorer
    under [[N]].`,
  how: `Defined by cases on <code>b</code>, with <code>if … then … else if … then … else …</code>.`,
  examples: [
    { expr: '(List.range 9).map fun t => gid 1 t', out: '[1, 0, 2, 3, 4, 5, 6, 7, 8]',
      note: 'In N₁, tile 1 is the original tile (number 0), and tile 0 (child 0, a Ξ) gets number 1.' },
  ],
  checks: [{ tone: 'ok', title: 'One to one',
    text: `Child 1 goes to 0 … |N<sub>b</sub>| − 1 (by the same rule one level down), child 0 to the next nestShift b
      numbers, and the later children keep numbers that are at least nestShift b + |N<sub>b</sub>|. No two tiles share
      a number. This is [[NestModel]] (b).` }] },

{ id: 'loc', section: 's6', kind: 'def', title: 'loc', lines: [231, 238],
  summary: 'loc b g: the tile of N_b with nest number g; the inverse of gid b.',
  what: `The other way round: the tile of N<sub>b</sub> whose number in the nest tiling is <code>g</code>. It undoes the
    three cases of [[gid]], in the same order.`,
  how: `As for [[gid]].`,
  examples: [{ expr: '(List.range 9).map fun g => loc 1 g', out: '[1, 0, 2, 3, 4, 5, 6, 7, 8]' }] },

{ id: 'nestGlue', section: 's6', kind: 'def', title: 'nestGlue', lines: [239, 243],
  summary: 'The gluing of the whole nest tiling, read off a block two levels above the tile.',
  what: `The gluing of the whole nest tiling: what lies across edge e<sub>i</sub> of the tile numbered
    <code>g</code>. It is read off a block that contains the tile with two levels to spare.`,
  how: `From the inside out: <code>loc (g + 1) g</code> is the tile's number in N<sub>g+1</sub>; <code>up (g + 1) 2</code>
    its number in N<sub>g+3</sub>; <code>.glue … i</code> what N<sub>g+3</sub> has across edge e<sub>i</sub>;
    <code>.map</code> gives the neighbour its nest number.`,
  examples: [{ expr: '(List.range 14).map fun i => nestGlue 0 i',
    out: '[some (8, 3), some (8, 2), some (1, 13), some (1, 12), some (1, 11), some (33, 8), some (33, 7),\n some (2, 2), some (2, 1), some (2, 0), some (3, 1), some (3, 0), some (8, 5), some (8, 4)]',
    note: 'The original tile\'s neighbours, read from N₃. Edges e₅ and e₆, on N₁\'s rim, meet tile 33, which lies in N₂.' }],
  checks: [{ tone: 'ok', title: 'Why N_{g+3}',
    text: `Tile <code>g</code> lies in N<sub>g+1</sub>, because |N<sub>g+1</sub>| > g ([[NestModel]] (a)); generous, but
      simple. Two more levels make every edge glued (Theorem B (1)). [[NestModel]] (d) says that any block containing
      the tile gives the same answer, and (e) that the answer is never <code>none</code>.` }] },

{ id: 'nestTiling', section: 's6', kind: 'def', title: 'nestTiling', lines: [244, 247],
  summary: 'The nest tiling as one Patch, with glue = nestGlue; only glue is meaningful.',
  what: `The nest tiling as one patch whose gluing is <code>nestGlue</code>. Its tiles are all the numbers 0, 1, 2, …`,
  how: `<code>⟨0, nestGlue, [], []⟩</code>: <code>tiles = 0</code>, <code>glue = nestGlue</code>, empty
    <code>rim</code> and <code>vtx</code>.`,
  checks: [{ tone: 'note', title: 'tiles = 0 is a placeholder',
    text: `A <code>Patch</code> has a finite number of tiles, and this one has infinitely many, so the field is set to 0
      and means nothing. So <code>nestTiling.IsPort p</code> is false for every <code>p</code>, and
      <code>nestTiling.NoClosedStrand</code> would be true for a trivial reason. The file never uses either for
      <code>nestTiling</code>: [[TheoremB_strand]] quantifies directly over all ports with vertex below 14, on every tile
      number. Only <code>nestTiling.across</code> is used.` }] },

{ id: 'stepF', section: 's6', kind: 'def', title: 'stepF', lines: [248, 250],
  summary: 'One step forwards along a strand: along the piece, then across the edge.',
  what: `One step forwards along a strand of the nest tiling: from port <code>p</code> along its piece, then straight
    across that edge into the next tile.`,
  how: `<code>.getD x</code> takes the value out of <code>some</code>, or gives <code>x</code> for <code>none</code>.`,
  examples: [{ expr: 'stepF (0,0,true)', out: '(8, 2, true)',
    note: 'R(v₀) → R(v₁) along the crossover, then across edge e₁ of tile 0, which is edge e₂ of tile 8.' }],
  checks: [{ tone: 'ok', title: 'The fallback is never used',
    text: `If nothing were across, <code>stepF</code> would stay at <code>pieceEnd p</code>. [[NestModel]] (e) says every
      edge is glued, so this never happens.` }] },

{ id: 'stepB', section: 's6', kind: 'def', title: 'stepB', lines: [251, 253],
  summary: 'One step backwards: across the edge, then along the piece.',
  what: `One step backwards: straight across the edge at <code>p</code>, then along the piece to its other end. It
    undoes <code>stepF</code>.`,
  how: `<code>pieceEnd ((nestTiling.across p).getD p)</code>.`,
  examples: [{ expr: 'stepB (0,0,true)', out: '(8, 3, false)',
    note: 'Across edge e₀ of tile 0 to R(v₃) of tile 8, then along the hook at v₃ to L(v₃).' }] },

{ id: 'NestModel', section: 's6', kind: 'claim', title: 'NestModel', lines: [254, 268],
  summary: 'The nest tiling is a tiling and contains every block.',
  what: `The nest tiling is a tiling, and it is the union of the blocks. Six claims joined by "and" (the comment
    labels them (a)–(e), with two for (b)). Proved in <code>ProofStrand.lean</code>.`,
  clauses: [
    { lines: [254, 260], title: 'Doc comment and header', what: `The claims in words.` },
    { lines: [261, 261], title: '(a) Every number is a tile of some block',
      what: `Tile number <code>g</code> belongs to N<sub>g+1</sub>.` },
    { lines: [262, 262], title: '(b) gid then loc',
      what: `<code>gid b</code> sends the tiles of N<sub>b</sub> into 0 … |N<sub>b</sub>| − 1, and <code>loc b</code>
        undoes it.` },
    { lines: [263, 263], title: '(b) loc then gid',
      what: `And the other way round: <code>gid b</code> is a one-to-one numbering of N<sub>b</sub>'s tiles.` },
    { lines: [264, 264], title: '(c) A tile keeps its number one level up',
      what: `Seen as a tile of N<sub>b+1</sub>, a tile of N<sub>b</sub> has the same nest number.` },
    { lines: [265, 266], title: '(d) The nest tiling contains every block',
      what: `Whatever N<sub>b</sub> glues across an edge, the nest tiling glues the same way, with nest numbers.`,
      checks: [{ tone: 'ok', title: 'One way only, as it should be',
        text: `It says nothing about edges on a block's rim: in the nest tiling those are glued to tiles outside the
          block.` }] },
    { lines: [267, 268], title: '(e) Every edge glued, to another tile, and back',
      what: `Every edge of every tile is glued, to an edge of a different tile, and that edge is glued back.`,
      how: `<code>≠</code> is "not equal".`,
      checks: [{ tone: 'ok', title: 'What makes the strands well defined',
        text: `With (e), <code>across</code> pairs the ports of the nest tiling with no port left alone; with
          <code>pieceEnd</code>, this is the "strand system" that the paper's Lemma 3.4 needs.` }] },
  ] },

{ id: 'TheoremB_strand', section: 's6', kind: 'claim', title: 'TheoremB_strand', lines: [269, 285],
  summary: 'The ribbons of the nest tiling form one two-way infinite strand through every port.',
  what: `Theorem B in its final form. Start at R(v<sub>0</sub>) of the original tile, <code>(0, 0, true)</code>, and
    follow the ribbon forwards and backwards: no port is met twice, no piece is run twice, and every port of every
    tile is met. So the ribbons of the nest tiling form one two-way infinite strand. Proved in
    <code>ProofStrand.lean</code>.`,
  how: `Five claims joined by <code>∧</code>. <code>iter stepF k x</code> applies <code>stepF</code> to <code>x</code>,
    <code>k</code> times (<code>iter</code> is from <code>Basic.lean</code>; see [[imports]]). Below, x stands for
    <code>(0, 0, true)</code>, F<sup>k</sup>x for <code>iter stepF k x</code> and B<sup>k</sup>x for
    <code>iter stepB k x</code>.`,
  clauses: [
    { lines: [269, 277], title: 'Doc comment and header', what: `The five claims in words.` },
    { lines: [278, 278], title: '(1) Forwards, never the same port twice',
      what: `Different numbers of forward steps give different ports: F<sup>i</sup>x = F<sup>j</sup>x only if i = j.` },
    { lines: [279, 279], title: '(2) Backwards, never the same port twice', what: `The same for backward steps.` },
    { lines: [280, 280], title: '(3) Backwards never meets forwards',
      what: `A port reached backwards is never one reached forwards, except the start.` },
    { lines: [281, 281], title: '(4) No piece run twice',
      what: `A port reached forwards is never the other end of the piece of a port reached forwards.` },
    { lines: [282, 285], title: '(5) Every port is met',
      what: `Every port of every tile (any tile number, any vertex below 14) is reached forwards or backwards, or is the
        other end of the piece of one that is.`,
      how: `<code>∨</code> is "or". <code>q : Port</code> gives the type of <code>q</code>.` },
  ],
  checks: [
    { tone: 'ok', title: 'Strong enough to mean "one strand"',
      text: `Along the strand the ports come in the order …, B²x, pieceEnd(B²x), Bx, pieceEnd(Bx), x, pieceEnd(x), Fx,
        pieceEnd(Fx), F²x, … Clause (5) says that every port is in this list. Clauses (1)–(4) do not spell out every
        pair that must differ, but they need not: with [[NestModel]] (pieces and crossings pair up the ports, none with
        itself), (1) already rules out a closed strand, and then the paper's Lemma 3.4 (<code>closed_or_path</code>)
        makes all the ports in the list different.` },
    { tone: 'data', title: 'About nestTiling, not yet the plane',
      text: `That the real nest tiling is glued like <code>nestTiling</code> is assumption (M). Nothing here concerns
        other spectre tilings.` },
  ] },

{ id: 'sec7', section: 's7', kind: 'section', title: 'Section heading', lines: [286, 287],
  what: `§7.`, how: `A heading comment.` },

{ id: 'Chain', section: 's7', kind: 'structure', title: 'Chain', lines: [288, 296],
  summary: 'A chain X₁ ⊂ X₂ ⊂ ⋯ of supertiles, each a child of the next: a kind K m and a child position c m for every level m ≥ 1.',
  what: `A chain of supertiles X₁ ⊂ X₂ ⊂ X₃ ⊂ ⋯, each a child of the next. It is given by two sequences: the kind
    <code>K m</code> of X<sub>m</sub>, and the position <code>c m</code> of X<sub>m</sub> among the children of
    X<sub>m+1</sub>. Two conditions make them fit Table 1: <code>c m</code> is a real child number, and that child has
    kind <code>K m</code>. In a real tiling, the supertiles of levels 1, 2, 3, … that contain a given tile form such a
    chain. The nest is the chain with <code>K m = Δ</code> and <code>c m = 1</code>.`,
  how: `Four fields. <code>K</code> and <code>c</code> are sequences, written as functions of the level. The other two
    are conditions: a field whose type is a <code>Prop</code> holds a <em>proof</em> of that claim, so a
    <code>Chain</code> can only be built when the conditions hold.`,
  examples: [
    { expr: '-- the nest as a Chain (checked by Lean: both conditions hold)\ndef nestChain : Chain := ⟨fun _ => .Delta, fun _ => 1, fun _ _ => by decide, fun _ _ => rfl⟩',
      out: '(accepted)' },
  ],
  checks: [
    { tone: 'ok', title: 'Each block really is a child of the next',
      text: `X<sub>m+1</sub> = <code>super (m + 1) (K (m + 1))</code> is composed from the children
        <code>super m (kind c')</code>, with the kinds of Table 1's row ([[super]]). Child <code>c m</code> has kind
        <code>K m</code> by <code>child_kind</code>, so it is <code>super m (K m)</code> = X<sub>m</sub>.` },
    { tone: 'note', title: 'Any chain, covering or not',
      text: `Any two sequences that meet the two conditions make a <code>Chain</code>, whether or not its union covers
        the plane. [[Chain_Covers]] picks out the chains that do; [[TheoremA_strand]] assumes it.` },
  ] },

{ id: 'nsChain', section: 's7', kind: 'namespace', title: 'namespace Chain', lines: [297, 298],
  summary: 'The next definitions are Chain.block, Chain.shift, …, each taking a chain X.',
  what: `The definitions up to <code>end Chain</code> ([[L338]]) are <code>Chain.block</code>, <code>Chain.shift</code>,
    <code>Chain.up</code>, <code>Chain.gid</code>, <code>Chain.loc</code>, <code>Chain.Covers</code> and
    <code>Chain.Contains</code>.`,
  how: `Each takes <code>(X : Chain)</code> as its first argument explicitly; <code>X.block m</code> means
    <code>Chain.block X m</code>. Inside the namespace, plain <code>up</code>, <code>gid</code> and <code>loc</code> mean
    the chain's own versions, not those of §4 and §6; the links in the code follow that.` },

{ id: 'Chain_block', section: 's7', kind: 'def', title: 'Chain.block', alias: 'block', lines: [299, 301],
  summary: 'X.block m: the block X_m, the supertile super m (K m).',
  what: `The block X<sub>m</sub>: the supertile of level <code>m</code> and kind <code>K m</code>. For the nest chain it
    is <code>N m</code>.`,
  how: `<code>X.K</code> reads the field <code>K</code> of <code>X</code>.` },

{ id: 'Chain_shift', section: 's7', kind: 'def', title: 'Chain.shift', alias: 'shift', lines: [302, 305],
  summary: 'Where X_m starts inside X_{m+1}: the tiles of the children before it.',
  what: `Where X<sub>m</sub> starts inside X<sub>m+1</sub>: the number of tiles in the children that come before it.
    For the nest chain it is [[nestShift]].`,
  how: `For each child number <code>c'</code> below <code>c m</code>, the tile count of the level-<code>m</code>
    supertile of the kind Table 1 lists there; then the sum.`,
  checks: [{ tone: 'ok', title: 'The same sum as compose\'s off',
    text: `[[compose]] numbers the tiles of X<sub>m+1</sub> child by child, and its <code>off (c m)</code> sums the
      tiles of the children before <code>c m</code>, which are exactly these supertiles ([[super]]). So this is that
      offset.` }] },

{ id: 'Chain_up', section: 's7', kind: 'def', title: 'Chain.up', lines: [306, 310],
  summary: 'X.up m k t: tile t of X_m, renumbered as a tile of X_{m+k}.',
  what: `Tile <code>t</code> of X<sub>m</sub>, renumbered as a tile of X<sub>m+k</sub>: [[up]] of §4, with
    <code>X.shift</code> in place of <code>nestShift</code>.`,
  how: `Here <code>up</code> is <code>Chain.up</code> itself.` },

{ id: 'Chain_gid', section: 's7', kind: 'def', title: 'Chain.gid', lines: [311, 319],
  summary: 'X.gid m t: the number, in the union of the chain, of tile t of X_m.',
  what: `Numbers all the tiles of the union so that every block X<sub>m</sub> gets 0 … |X<sub>m</sub>| − 1: [[gid]] of
    §6, started at level 1 instead of level 0, and allowing several children before X<sub>m</sub>.`,
  how: `Levels 0 and 1 keep the number (level 0 is not part of the chain; it is there only to make the definition
    complete); level <code>m + 2</code> compares <code>t</code> with <code>X.shift (m + 1)</code> and
    <code>(X.block (m + 1)).tiles</code>, as in §6.`,
  checks: [{ tone: 'ok', title: 'One to one, for every chain',
    text: `The argument of [[gid]] works unchanged: X<sub>m+1</sub> goes to 0 … |X<sub>m+1</sub>| − 1, the earlier
      children (now possibly several) to the next <code>X.shift (m + 1)</code> numbers, and later children keep
      numbers that are already larger. This is [[ChainModel]] (b).` }] },

{ id: 'Chain_loc', section: 's7', kind: 'def', title: 'Chain.loc', lines: [320, 328],
  summary: 'X.loc m g: the tile of X_m with number g; the inverse of X.gid m.',
  what: `The other way round: the tile of X<sub>m</sub> whose number in the union is <code>g</code>. It undoes the cases
    of [[Chain_gid]], in the same order.`,
  how: `As for [[Chain_gid]].` },

{ id: 'Chain_Covers', section: 's7', kind: 'claim', title: 'Chain.Covers', alias: 'Covers', lines: [329, 332],
  summary: 'The chain covers the plane: every edge of every block is glued in some larger block.',
  what: `The chain covers the plane: every edge of every tile of every block is glued to something in some larger
    block. Then the union has no boundary.`,
  how: `<code>X.up m k t</code> is the tile's number in X<sub>m+k</sub>.`,
  checks: [
    { tone: 'ok', title: 'The nest chain covers',
      text: `For <code>K m = Δ</code> and <code>c m = 1</code>, <code>X.block m</code> is <code>N m</code> and
        <code>X.up</code> is [[up]], so [[TheoremB]] (1) gives <code>Covers</code> with <code>k = 2</code>. This follows
        from reading the definitions; the file does not state it as a separate claim.` },
    { tone: 'data', title: 'From tilings to Covers',
      text: `That the supertiles round a tile of a tiling whose hierarchy covers the plane form a chain with
        <code>Covers</code> is part of assumption (M) ([[L16]]–18).` },
  ] },

{ id: 'Chain_Contains', section: 's7', kind: 'claim', title: 'Chain.Contains', alias: 'Contains', lines: [333, 337],
  summary: 'G contains every block: whatever X_m glues, G glues the same, under the numbering X.gid.',
  what: `<code>G</code> is a gluing of the whole union that contains every block: whatever X<sub>m</sub> glues across an
    edge, <code>G</code> glues the same way, with the tiles' numbers in the union. The same condition as
    [[NestModel]] (d), with the gluing given instead of built.`,
  how: `<code>G</code> has the type of a patch's <code>glue</code>, <code>Nat → Nat → Option (Nat × Nat)</code>.` },

{ id: 'endChain', section: 's7', kind: 'end', title: 'end Chain', lines: [338, 339],
  what: `Closes the namespace <code>Chain</code> opened on [[L297]].`, how: `<code>end Chain</code>.` },

{ id: 'tilingOf', section: 's7', kind: 'def', title: 'tilingOf', lines: [340, 342],
  summary: 'The tiling with gluing G, as one Patch; only glue is meaningful.',
  what: `The tiling with gluing <code>G</code>, as one patch: its tiles are all the numbers 0, 1, 2, … As
    [[nestTiling]], with <code>G</code> for <code>nestGlue</code>.`,
  how: `<code>⟨0, G, [], []⟩</code>.`,
  checks: [{ tone: 'note', title: 'tiles = 0 is a placeholder',
    text: `As for [[nestTiling]]: <code>IsPort</code> and <code>NoClosedStrand</code> would mean nothing here, and are
      not used. [[TheoremA_strand]] quantifies over all ports with vertex below 14 directly.` }] },

{ id: 'Patch_forward', section: 's7', kind: 'def', title: 'Patch.forward', alias: 'forward', lines: [343, 345],
  summary: 'One step forwards along a strand of any patch: along the piece, then across.',
  what: `One step forwards along a strand of any patch: [[stepF]], with <code>nestTiling</code> replaced by
    <code>P</code>.`,
  how: `Written outside <code>namespace Patch</code> but with the full name <code>Patch.forward</code>, so dot notation
    works: <code>(tilingOf G).forward</code>.` },

{ id: 'Patch_backward', section: 's7', kind: 'def', title: 'Patch.backward', alias: 'backward', lines: [346, 348],
  summary: 'One step backwards: across the edge, then along the piece.',
  what: `One step backwards: [[stepB]] for any patch. It undoes <code>forward</code>.`,
  how: `<code>pieceEnd ((P.across p).getD p)</code>.` },

{ id: 'ChainModel', section: 's7', kind: 'claim', title: 'ChainModel', lines: [349, 364],
  summary: 'For every chain: its union is a tiling containing every block, and if the chain covers, it has no boundary.',
  what: `For every chain: its union, numbered by <code>X.gid</code>, is a tiling; a gluing containing every block
    exists; and if the chain covers the plane, any such gluing glues every edge, to a different tile, which is glued
    back. Proved in <code>ProofChain.lean</code>.`,
  clauses: [
    { lines: [349, 356], title: 'Doc comment and header', what: `The claims in words, for every chain.` },
    { lines: [357, 357], title: '(a) Every number is a tile of some block', what: `Number <code>g</code> belongs to X<sub>g+1</sub>.` },
    { lines: [358, 358], title: '(b) gid then loc', what: `<code>X.gid m</code> stays below |X<sub>m</sub>|, and <code>X.loc m</code> undoes it.` },
    { lines: [359, 359], title: '(b) loc then gid', what: `And the other way round: a one-to-one numbering.` },
    { lines: [360, 360], title: '(c) A tile keeps its number one level up', what: `Seen in X<sub>m+1</sub>, a tile of X<sub>m</sub> has the same number.` },
    { lines: [361, 361], title: '(d) A gluing exists',
      what: `There is a gluing of the whole union that contains every block.`,
      checks: [{ tone: 'ok', title: 'Why (d) matters',
        text: `[[TheoremA_strand]] assumes a gluing <code>G</code> with <code>X.Contains G</code>. Without (d) that
          assumption might be impossible to meet, and the theorem would say nothing.` }] },
    { lines: [362, 364], title: '(e) If the chain covers: every edge glued, to another tile, and back',
      what: `If the chain covers the plane, every gluing that contains every block glues every edge of every tile, to an
        edge of a different tile, which is glued back.`,
      checks: [{ tone: 'ok', title: 'Only one such gluing',
        text: `With <code>Covers</code>, every edge of every tile is glued in some block, so <code>Contains</code> fixes
          <code>G g i</code> for every <code>g</code> and every <code>i</code> &lt; 14. All gluings that contain every
          block agree there, so "for every <code>G</code>" in [[TheoremA_strand]] loses nothing.` }] },
  ] },

{ id: 'TheoremA_strand', section: 's7', kind: 'claim', title: 'TheoremA_strand', lines: [365, 378],
  summary: 'In the union of any chain that covers the plane, every strand is a two-way infinite path.',
  what: `Theorem A in strand form. In the union of any chain of supertiles that covers the plane, under any gluing that
    contains every block, follow the ribbon from any port forwards and backwards: no port is met twice, and no piece is
    run twice. So no strand is closed. It says nothing about how many strands there are. Proved in
    <code>ProofChain.lean</code>.`,
  how: `<code>∀ (X : Chain) (G : …),</code> names two variables with their types; the hypotheses follow, joined by
    <code>→</code>. <code>iter (tilingOf G).forward k p</code> is <code>k</code> forward steps from <code>p</code>.`,
  clauses: [
    { lines: [365, 373], title: 'Doc comment, header and hypotheses',
      what: `For every chain that covers, every gluing that contains it, and every port.` },
    { lines: [374, 374], title: '(1) Forwards, never the same port twice', what: `Different numbers of forward steps give different ports.` },
    { lines: [375, 375], title: '(2) Backwards, never the same port twice', what: `The same for backward steps.` },
    { lines: [376, 376], title: '(3) Backwards never meets forwards', what: `A port reached backwards is never one reached forwards, except the start.` },
    { lines: [377, 378], title: '(4) No piece run twice', what: `A port reached forwards is never the other end of the piece of a port reached forwards.` },
  ],
  checks: [
    { tone: 'ok', title: 'Strong enough for "no closed strand"',
      text: `A closed strand through <code>p</code> would bring it back to <code>p</code> after finitely many forward
        steps, against (1). As for [[TheoremB_strand]], (1) is enough with [[ChainModel]] (e), by the paper's Lemma
        3.4.` },
    { tone: 'note', title: 'Not empty',
      text: `The theorem assumes a chain that covers and a gluing that contains it. [[ChainModel]] (d) gives the gluing
        for every chain, and the nest chain covers (see [[Chain_Covers]]). So the theorem applies at least to the nest
        tiling.` },
    { tone: 'data', title: 'From here to tilings of the plane',
      text: `That a spectre tiling whose hierarchy covers the plane is, up to numbering, the union of such a chain is
        assumption (M). This matches the paper's Theorem A. Nothing here concerns fault tilings.` },
  ] },

{ id: 'end', section: 's7', kind: 'end', title: 'end SpectreKnot.Statement', lines: [379, 379],
  what: `Closes the namespace opened on [[L24]]. The file ends here.`, how: `<code>end SpectreKnot.Statement</code>.` },
],

/* The fields of Patch, for the pop-ups on tiles, glue, rim and vtx. */
fields: {
  tiles: `The number of tiles. They are numbered 0, 1, …, <code>tiles − 1</code>.`,
  glue: `What lies across edge e<sub>i</sub> of tile <code>t</code>: <code>none</code> if that edge is on the rim;
    <code>some (t', j)</code> if it is the same edge as edge e<sub>j</sub> of tile <code>t'</code>.`,
  rim: `The rim edges <code>(t, i)</code> in order round the boundary, in the supertile's own orientation, from its
    vertex 0.`,
  vtx: `The positions in <code>rim</code> of the supertile's vertices 0 … 5, then the rim's length: seven numbers.`,
},

/* ---------------------------------------------------------------------------------------------------------------- */
/* The chain from Lean's kernel to the paper's theorems. */
trust: [
  { status: 'build', title: 'Lean\'s kernel checks each proof',
    text: `Lean 4.34.1, core library only. Every proof in the project is checked by the kernel when
      <code>./build.sh</code> runs, and the build fails on any error; the repository's checks run it on every push.` },
  { status: 'build', title: 'No extra axioms, no gaps',
    text: `<code>#print axioms</code> (in <code>Axioms.lean</code>) lists, for each of the nine main theorems, only
      <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>: Lean's three standard axioms. No
      <code>sorryAx</code>, so no unfinished proof; no <code>Lean.ofReduceBool</code>, so no trust in compiled code.
      <code>build.sh</code> fails otherwise.` },
  { status: 'build', title: 'Each theorem proves exactly the claim written here',
    text: `<code>theorem theoremA : TheoremA</code> and the other eight are stated in this file's namespace, so Lean has
      checked each proof against the claim as written here.` },
  { status: 'read', title: 'The definitions say what the paper means',
    text: `This file, plus <code>Kind</code> and <code>iter</code> from <code>Basic.lean</code>. Lean cannot check
      this: it is a matter of reading. That is what this page is for.` },
  { status: 'tested', title: 'The data files hold the right tables',
    text: `Tables 1–3 and the nine level-1 clusters, generated from the paper's code. Tested, not proved: level 2
      built from them equals the exact-arithmetic construction edge for edge; the paper's strand counts come out; a
      different chain gives three strands, not one.` },
  { status: 'assumed', title: 'Assumption (M)',
    text: `Real supertiles are glued like <code>super m K</code>; a tiling whose hierarchy covers the plane is the
      union of a chain of supertiles that covers (<code>Chain</code>, <code>Covers</code>); and the real nest tiling is
      glued like <code>nestTiling</code>. Not formalised; it rests on the spectre paper (Thms 2.2, 3.1, 4.1, 5.1) and
      on the paper's Prop 2.4 and Lemma 2.6.` },
],

/* ---------------------------------------------------------------------------------------------------------------- */
/* Glossary: Lean notation and library names. Keys are tokens as they appear; '.name' keys are names after a dot. */
glossary: {
  'import': ['Keyword', 'Loads another Lean file; its definitions become available here.'],
  'namespace': ['Keyword', 'Starts a region in which every new name gets a prefix. Closed by <code>end</code>.'],
  'end': ['Keyword', 'Closes a namespace.'],
  'abbrev': ['Keyword', 'Defines a name for an existing term (here, a type) that Lean unfolds freely. <code>abbrev Port := Nat × Nat × Bool</code> makes Port and the triple type interchangeable.'],
  'theorem': ['Keyword', '<code>theorem name : Claim := proof</code> states a claim and proves it; Lean checks the proof. This file has no theorems: its claims are proved in other files.'],
  'def': ['Keyword', 'Defines a name: <code>def f (x : A) : B := body</code>. A <code>def</code> whose type is <code>Prop</code> states a claim without proving it.'],
  'structure': ['Keyword', 'Declares a record type with named fields, listed after <code>where</code>.'],
  'where': ['Keyword', 'Introduces the fields of a <code>structure</code>.'],
  'inductive': ['Keyword', 'Defines a type, or (ending in <code>Prop</code>) a relation, by rules listed with <code>|</code>. The relation holds exactly when it follows from the rules in finitely many steps.'],
  'variable': ['Keyword', 'Declares an argument that is added automatically to every following definition that mentions it.'],
  'match': ['Keyword', '<code>match x with | pattern => result | …</code>: definition by cases on the shape of <code>x</code>; the first pattern that fits is used.'],
  'with': ['Keyword', 'Part of <code>match x with</code>.'],
  'fun': ['Keyword', '<code>fun x => e</code> is a function without a name. <code>fun (t\', j) => …</code> takes a pair apart; <code>fun _ _ => none</code> ignores two arguments.'],
  'let': ['Keyword', '<code>let x := v</code> names a value for use in the rest of the expression.'],
  'if': ['Keyword', '<code>if c then a else b</code>. The condition is a claim Lean can decide, such as a comparison of numbers.'],
  'then': ['Keyword', 'Part of <code>if … then … else …</code>.'],
  'else': ['Keyword', 'Part of <code>if … then … else …</code>.'],
  'Prop': ['Type', 'The type of claims (propositions). A <code>Prop</code> is true or false; it is proved, not computed.'],
  'Nat': ['Type', 'The natural numbers 0, 1, 2, … Subtraction stops at 0: <code>3 - 5 = 0</code>.'],
  'Bool': ['Type', 'The two values <code>true</code> and <code>false</code>.'],
  'true': ['Value', 'One of the two values of <code>Bool</code>. In a port, it marks R(vᵢ).'],
  'false': ['Value', 'One of the two values of <code>Bool</code>. In a port, it marks L(vᵢ).'],
  'Option': ['Type', '<code>Option α</code>: either <code>none</code> or <code>some x</code> with <code>x : α</code>. Used for "there may be nothing here".'],
  'some': ['Value', '<code>some x</code>: an <code>Option</code> holding <code>x</code>.'],
  'none': ['Value', '<code>none</code>: an <code>Option</code> holding nothing. For <code>glue</code>, "this edge is on the rim".'],
  'List': ['Type', '<code>List α</code>: a finite list <code>[x₀, x₁, …]</code>.'],
  'List.range': ['List', '<code>List.range n</code> is <code>[0, 1, …, n-1]</code>.'],
  'id': ['Function', 'The function that returns its argument unchanged. <code>flatMap id</code> flattens a list of lists.'],
  '.length': ['List', 'The number of entries.'],
  '.map': ['List / Option', 'On a list: apply the function to every entry. On an <code>Option</code>: <code>none</code> stays <code>none</code>, <code>some x</code> becomes <code>some (f x)</code>.'],
  '.flatMap': ['List', 'Apply a function that returns a list to every entry, and join the results into one list.'],
  '.take': ['List', '<code>l.take k</code>: the first <code>k</code> entries (all of them if there are fewer).'],
  '.drop': ['List', '<code>l.drop k</code>: everything after the first <code>k</code> entries.'],
  '.reverse': ['List', 'The list backwards.'],
  '.sum': ['List', 'The sum of the entries.'],
  '.filter': ['List', '<code>l.filter f</code>: keep the entries <code>x</code> with <code>f x</code> true.'],
  '.getD': ['List / Option', 'On a list: <code>l.getD i d</code> is entry <code>i</code> (from 0), or the default <code>d</code> if there is none. On an <code>Option</code>: <code>o.getD d</code> is the value inside <code>some</code>, or <code>d</code> for <code>none</code>.'],
  '.findIdx?': ['List', '<code>l.findIdx? f</code>: <code>some</code> (position of the first entry <code>x</code> with <code>f x</code> true), or <code>none</code>.'],
  '.isSome': ['Option', '<code>true</code> for <code>some …</code>, <code>false</code> for <code>none</code>.'],
  '.bind': ['Option', '<code>o.bind f</code>: <code>none</code> stays <code>none</code>, and <code>some x</code> becomes <code>f x</code>, which may itself be <code>none</code>.'],
  ']?': ['List', '<code>l[i]?</code>: <code>some</code> (entry <code>i</code>), or <code>none</code> if the list is too short.'],
  '.1': ['Pair', 'The first entry of a pair. For a port, the tile.'],
  '.2': ['Pair', 'The second entry of a pair. For a port <code>p = (t, i, s)</code>, <code>p.2</code> is <code>(i, s)</code>, so <code>p.2.1</code> is the vertex and <code>p.2.2</code> the flag.'],
  'Kind': ['Basic.lean', 'The nine kinds of supertile: Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Phi, Psi (Γ Δ Θ Λ Ξ Π Σ Φ Ψ).'],
  '.Gamma': ['Kind', '<code>Kind.Gamma</code>, Γ. <code>.Gamma</code> is short for it where Lean knows a <code>Kind</code> is expected.'],
  '.Delta': ['Kind', '<code>Kind.Delta</code>, Δ: the kind of the nest\'s blocks.'],
  '.Xi': ['Kind', '<code>Kind.Xi</code>, Ξ: the kind of child 0 of a Δ.'],
  'iter': ['Basic.lean', '<code>iter f n x</code> applies <code>f</code> to <code>x</code>, <code>n</code> times: <code>iter f 0 x = x</code>, <code>iter f (n+1) x = f (iter f n x)</code>.'],
  'Pattern.kids': ['Data/Pattern.lean', 'Table 1: for each kind, the kinds of its children, child 0 first (8 children; 7 for Γ).'],
  'Pattern.adj': ['Data/Pattern.lean', 'Table 2: for each kind, child <code>c</code> and side <code>j</code>: <code>some (c\', j\')</code> if side <code>j</code> of child <code>c</code> is side <code>j\'</code> of child <code>c\'</code>, <code>none</code> if it lies on the parent\'s rim.'],
  'Pattern.pside': ['Data/Pattern.lean', 'Table 3: for each kind and each side <code>J</code> of the parent, the children\'s sides <code>(c, j)</code> that make it up, in the parent\'s order.'],
  'Clusters.tiles': ['Data/Clusters.lean', 'The number of tiles of each level-1 supertile: 8 for Γ, 9 for the others.'],
  'Clusters.glue': ['Data/Clusters.lean', 'For each level-1 supertile, tile and edge: the tile and edge glued to it, or <code>none</code>.'],
  'Clusters.rim': ['Data/Clusters.lean', 'The rim of each level-1 supertile, as tile edges in its own orientation, from its vertex 0.'],
  'Clusters.vtx': ['Data/Clusters.lean', 'The rim positions of the six vertices of each level-1 supertile, then its rim length.'],
  ':=': ['Notation', '"is defined as".'],
  '=>': ['Notation', 'Separates a pattern, or a function\'s argument, from the result.'],
  '|': ['Notation', 'Starts a case (in <code>match</code> or a definition by cases) or a rule (in <code>inductive</code>).'],
  ':': ['Notation', '<code>x : A</code> says that <code>x</code> has type <code>A</code>.'],
  '×': ['Notation', '<code>A × B</code>: the type of pairs. Groups to the right: <code>A × B × C</code> is <code>A × (B × C)</code>.'],
  '→': ['Notation', 'Between types: the type of functions. Between claims: "if … then …". Groups to the right.'],
  '∀': ['Notation', '"for all". <code>∀ x y, …</code> is "for all x and y, …".'],
  '∃': ['Notation', '"there is". <code>∃ r, …</code> is "there is an r such that …".'],
  '∧': ['Notation', '"and". Groups to the right.'],
  '∨': ['Notation', '"or".'],
  '¬': ['Notation', '"not": <code>¬ A</code> is the claim that <code>A</code> is false.'],
  '≠': ['Notation', '"is not equal to".'],
  '≤': ['Notation', '"is at most".'],
  '<': ['Notation', '"is less than".'],
  '=': ['Notation', 'Equality, as a claim.'],
  '==': ['Notation', 'Equality as a test that returns a <code>Bool</code>; used inside programs such as <code>findIdx?</code>.'],
  '%': ['Notation', 'Remainder: <code>(i + 13) % 14</code> is i − 1 counted round 14 (so 0 becomes 13).'],
  '!': ['Notation', '<code>!s</code>: "not s" for a <code>Bool</code>.'],
  '-': ['Notation', 'Subtraction. On <code>Nat</code> it stops at 0.'],
  '·': ['Notation', '<code>(· == x)</code> is short for <code>fun y => y == x</code>.'],
  '_': ['Notation', 'A placeholder: matches anything, or an argument that is ignored.'],
  '⟨': ['Notation', '<code>⟨a, b, c, d⟩</code> builds a structure from its fields in order.'],
  '⟩': ['Notation', 'Closes <code>⟨…⟩</code>.'],
  '{': ['Notation', 'In a rule, <code>{p : Port}</code> makes an argument implicit (Lean infers it). At [[L122]], <code>{ field := …, … }</code> builds a structure by field names.'],
},

/* Members of a chain X: X.block, X.up and so on (§7). */
members: {
  Chain: { K: 'Chain', c: 'Chain', block: 'Chain_block', shift: 'Chain_shift', up: 'Chain_up', gid: 'Chain_gid',
    loc: 'Chain_loc', Covers: 'Chain_Covers', Contains: 'Chain_Contains' },
},

/* Names that mean something only in part of the file. Entries with an id link to that item. */
scoped: [
  { name: 'P', lines: [55, 105], kind: 'Variable', text: 'The patch: declared by <code>variable (P : Patch)</code> on line 55, an automatic first argument of every definition up to <code>end Patch</code>.' },
  { name: 'child', lines: [113, 148], kind: 'Argument', text: '<code>child c</code>: the c-th child patch, passed to <code>compose</code>.' },
  { name: 'T', lines: [113, 162], kind: 'Argument', text: 'The kind of the parent supertile.' },
  { name: 'n', lines: [115, 148], kind: 'let', text: 'The number of children (line 115).' },
  { name: 'off', lines: [117, 148], kind: 'let', text: '<code>off c</code>: the number of the first tile of child c (line 117).' },
  { name: 'owner', lines: [119, 148], kind: 'let', text: '<code>owner t</code>: the child containing parent tile t (line 119).' },
  { name: 'shift', lines: [121, 148], kind: 'let', text: '<code>shift c e</code>: edge e of child c renumbered as an edge of the parent (line 121).' },
  { name: 't₀', lines: [127, 143], kind: 'let', text: 'The number of tile t within its child (line 127).' },
  { name: 'pos', lines: [133, 143], kind: 'let', text: 'Where the edge comes in its child\'s rim list (line 133).' },
  { name: 'o', lines: [135, 143], kind: 'let', text: 'How many edges of side j come before this one (line 135).' },
  { name: 'X', lines: [291, 378], kind: 'Variable', text: 'A chain of supertiles (see <code>Chain</code>, line 291).' },
  { name: 'G', lines: [333, 378], kind: 'Variable', text: 'A gluing of the whole tiling: what lies across edge i of the tile numbered g, as <code>G g i</code>.' },
  { name: 'K', lines: [292, 295], id: 'Chain' },
  { name: 'c', lines: [293, 295], id: 'Chain' },
  { name: 'up', lines: [297, 338], id: 'Chain_up' },
  { name: 'gid', lines: [297, 338], id: 'Chain_gid' },
  { name: 'loc', lines: [297, 338], id: 'Chain_loc' },
  { name: 'leave', lines: [68, 75], kind: 'Rule', text: 'Rule of <code>Follow</code>: leaving the patch at the far end of a piece.' },
  { name: 'next', lines: [68, 75], kind: 'Rule', text: 'Rule of <code>Follow</code>: crossing an edge and carrying on.' },
  { name: 'refl', lines: [80, 86], kind: 'Rule', text: 'Rule of <code>Linked</code>: zero moves.' },
  { name: 'piece', lines: [80, 86], kind: 'Rule', text: 'Rule of <code>Linked</code>: a move along a piece.' },
  { name: 'edge', lines: [80, 86], kind: 'Rule', text: 'Rule of <code>Linked</code>: a move across an edge.' },
],
};
