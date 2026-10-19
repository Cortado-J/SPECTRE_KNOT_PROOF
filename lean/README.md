# Lean formalisation (October 2026)

A formalisation of the proof of *The Spectre Knot* (`../paper/spectre_knot.pdf`) in Lean 4, **without Mathlib**.
Stage 1 (the pilot) formalised a few early results and tested the kernel on the finite computations. Stage 2 proved
Prop 5.4 (reduced composition) for every well-formed gluing. Stage 3 proved that the compositions of level-m
supertiles have the signature at every level m ≥ 1 (`Compose.parity_lemma`, the paper's Prop 7.4), by lengthening.
Stage 4 linked these abstract gluings to the supertiles of the statement file and proved **Theorem A** in its
combinatorial form (`Statement.theoremA`). Stage 5 proved **Theorem B** in the same form (`Statement.theoremB`,
`Statement.theoremB_sharp`), and then its final form by Lemma 3.4: the ribbons of the nest tiling form one two-way
infinite strand (`Statement.theoremB_strand`). Stage 6 proved Theorem A in the same final form for any chain of
supertiles: every strand of their union is a two-way infinite path (`Statement.theoremA_strand`). Stage 7 proved that
the bound of Theorem B is exact, the last two rows of the paper's Table 5 (`Statement.theoremB_exact`), and the
Grandparent Lemma's part (a) at the vertices of tiles (`Statement.grandparent`), and that the nest is a chain of
supertiles that covers, so that Theorem A in its final form is not vacuous (`Statement.nestCovers`). On 19 October 2026
the Signature Theorem itself became a claim of the statement file (`Statement.signatureTheorem`), after a comparison of
the paper with the Lean. Written by the AI
system (Claude), working with the owner, like everything else in this repository.

The paper was revised on 11 October 2026 so that its proofs of the signature (§7) and of the merging (§9.1) take the
routes this formalisation takes; see *How the formal proof relates to the paper* below.

## The statement file: start here

**`SpectreKnot/Statement.lean` is the file to read.** It holds every definition the main theorems use, and the
theorems themselves as claims, with short comments in plain English where they help (shortened on 13 Oct 2026; on
15 Oct 2026 `turn`, `turns`, `Surrounded`, `TwoStrands`, `TheoremB_exact` and `Grandparent` were added; later that
day infinite tilings got their own type, `Tiling`, with `straightThrough` and `NestCovers`, and assumption (M) was
split into its three parts; on 19 Oct 2026 `SignatureTheorem` was added, with the definitions it uses: the rim ports
`bport`, `RimChains`, the signature `HasSig` and the corners `cornerA`, `cornerB`). The proof map's page `statement.html` (written by `python3 proofmap/build.py`, and on the
website)
is the guided reading: a short introduction to Lean for this file, a suggested reading order, and then the whole file,
piece by piece, beside a plain reading of each piece, with how the Lean syntax says it (folded away), checks against
the paper, Lean's own output on examples, figures of the ports and the gluing, what each piece uses and where it is
used, and a glossary. The reading is in
`guide/content.js`; `python3 guide/build_guide.py` checks it, and the map's build fails, if the explanations no longer
cover every line. The file holds:

- §5: `SignatureTheorem` (the paper's Thm 7.6: every supertile of level m ≥ 1 is a disc at its rim and has the
  signature at its crossover corners A and B = A + ω_m), `TheoremA` (no supertile contains a closed strand), `TheoremB` (the nest has no boundary, no closed strand, and
  any two ports of a block lie on one strand of a larger block), `TheoremB_sharp` (the paper's bound: three levels
  up for even b, four for odd b), `TheoremB_exact` (the bound is exact: two strands two levels up, and three levels up
  for odd b) and `Grandparent` (every vertex of every tile of N_b is surrounded by tiles of N_{b+2});
- §6: infinite tilings (`Tiling`: a gluing of infinitely many tiles, with no number of tiles and no rim, so that the
  notions for finite patches cannot be applied to one), the nest tiling (`nestTiling`), `NestModel` (it is a tiling,
  and it contains every block) and `TheoremB_strand` (its ribbons form one two-way infinite strand through every
  port);
- §7: any chain of supertiles X₁ ⊂ X₂ ⊂ ⋯, each a child of the next (`Chain`); `ChainModel` (the union of the chain is
  a tiling containing every block, and, if the chain covers, that is if every edge is eventually glued, a tiling with
  no boundary), `TheoremA_strand` (in that case every strand of the union is a two-way infinite path: the paper's
  Theorem A) and `NestCovers` (the nest is a chain that covers, so `TheoremA_strand` is not vacuous).

The claims are combinatorial, about patches of tiles described by which edges are glued. The link to real tilings is
one assumption, (M), in three parts written out at the top of the file, none of them formalised (*What it does not
show*, below): real supertiles are glued like the ones the file builds (M1); a tiling whose hierarchy covers the plane
is the union of a chain that covers (M2); and the nest tiling is the union of the blocks and covers the plane (M3).
Every claim is proved, and Lean's kernel has checked each proof against exactly this statement: `signatureTheorem` in
`SpectreKnot/ProofGrand.lean`; `theoremA` in `SpectreKnot/ProofA.lean`; `theoremB` and `theoremB_sharp` in `SpectreKnot/ProofB.lean`; `nestModel` and
`theoremB_strand` in `SpectreKnot/ProofStrand.lean`; `chainModel`, `theoremA_strand` and `nestCovers` in
`SpectreKnot/ProofChain.lean`; `theoremB_exact` in `SpectreKnot/ProofExact.lean`; `grandparent` in
`SpectreKnot/ProofGrand.lean`.

What is proved is fixed by `Statement.lean` and the three files it imports (`Basic.lean`, `Data/Pattern.lean`,
`Data/Clusters.lean`). `TRUSTED.sha256` records their SHA-256, and the build fails if any of them changes without it
(`tools/check_trusted.py`). The end of `Axioms.lean` pins each of the eleven main theorems to its claim, so the build
also fails if a main theorem's statement changes.

How the statement's definitions are tested (`Tests.lean`; `TestsSlow.lean` with `./build.sh --slow`):

- the level-2 supertiles it builds from the tables equal, edge for edge, those built from the tile placements in
  exact arithmetic (`Data/Level2.lean`, from `exact.py`), with the same six vertices; the level-1 sides have the
  lengths of Prop 6.1;
- sizes: tiles 9, 71, 559, 4,401 and rims 46, 182, 758, 3,198 for Δ, and rims 44, 160, 652, 2,736 for Γ, as in the
  paper;
- the paper's Table 5 comes out of its definitions of "following a ribbon" and "the nest": N₀'s pieces lie on 5, 2, 1
  strands of N₁, N₂, N₃; N₁'s on 10, 2, 2 (and 1 in N₅, slow); N₂'s on 37, 2 (and 1 in N₅, slow);
- negative control: along the chain of the paper's Remark 10.1 the same definitions give 32, 3, 3 (and 3 in X₅,
  slow) strands, not one. So "one strand" is not built into the definitions;
- negative control for Theorem A (a theorem, `loopPatch_closed`): a one-tile patch with a made-up gluing that traps a
  ribbon fails `NoClosedStrand`. So "no closed strand" is not built into the definitions either;
- Theorem A in its final form applies to at least one chain (a claim of the statement, `NestCovers`): the nest, as a
  chain, covers. So `TheoremA_strand` is not true merely because no chain satisfies its hypothesis;
- negative control for Theorem A on real supertiles: with another decoration, the Spectre Knot's with its crossing
  moved from corner 0 to corner 5, the same gluing and the same rule for following a ribbon find closed strands (226 of
  the 252 ports of N₁ inside N₃), and with no crossing at all, already in a level-1 supertile. The Spectre Knot's own
  decoration, given in the same way, is `pieceEnd`, and gives none. So "no closed strand" comes from the design, not
  from the definitions or the gluing;
- the Grandparent Lemma on instances: every vertex of every tile of N₁ is surrounded in N₃, and of N₂ in N₄, but not
  one level up (side 2 of N_b lies on the rim of N_{b+1}); and a theorem (`rim_not_surrounded`): in a patch with the
  signature, no vertex on the rim is surrounded. So "surrounded" is not built into the definitions.

`Tests.lean` also checks the 18 compositions of Computation 7.3 at levels 1 and 2: they are well formed; the full and
the reduced walk agree from every port; at level 1 the runs number 52 (45 for Γ); the rims of the level-2 Γ and Δ have
160 and 182 edges; the base checkers hold and reject a wrong sign and non-adjacent corners. It also runs the paper's
two negative controls as the program does: with every child's corner B two vertices from A, all 18 compositions fail
Computation 7.3's check; with junctions 12 and 16 exchanged, Computation 9.2's check fails for both signs. `TestsSlow.lean` also
computes the conclusion of Prop 7.4 at level 2 directly. Tests are `#guard`s, not proofs, but the build fails if one
fails.

## How the formal proof relates to the paper

The formal proofs follow the paper's §§3–9 (as revised on 11 October 2026): the signature at every level by
lengthening (Lemmas 7.1 and 7.2, Computation 7.3, Prop 7.4, Thm 7.6), Theorem A by the covering argument of §7.4, and
the merging by the junction map (Computation 9.2, Lemmas 9.3 and 9.4, the proof of Thm 9.1). The differences are of
detail:

- **Strands** of a tiling are modelled as two fixed-point-free involutions on ports (`inside`, `across`), not as the
  strand graph of Def 3.3; Lemma 3.4 is stated for them (`StrandSystem.closed_or_path`). In a patch, a ribbon is
  followed port by port (`Follow`, `Linked`).
- **Tilings of the plane** are gluings of infinitely many tiles (`Tiling`), a type of their own: unlike a patch, a
  tiling has no number of tiles and no rim. Its strands are followed one step at a time (`Tiling.forward`,
  `Tiling.backward`), and the straight-through rule (`straightThrough`) is the same as in a patch.
- **Supertiles** are patches described by which edge of which tile is glued to which edge of which other tile, built
  from the tables by `compose` (Prop 2.4 read as a construction) on top of the nine level-1 supertiles, which are data.
  The paper's compositions C_T(L, d, ω) are `Comp.ofLens T L d ω`, gluings of boxes (`Gluing`).
- **Prop 5.4** (b) is proved from every port, not only from reduced ports; (c) is proved in the form used: if the
  reduced walk from every port at a mark reaches the rim, there is no closed strand. Prop 5.4 is proved for any
  well-formed gluing (`Gluing.WF`), which asks less than §5 does: each child's corners distinct, not adjacent, and
  nothing about the children's interiors. Marks are defined per child vertex (`smooth`), so the facts §5 argues from
  the angles at a vertex (a run of one child is a run of its partner; no third child touches it) are proved from the
  gluing alone.
- **Lemma 7.1** (lengthening) is proved in two steps: cutting an edge into three maps every walk to a walk with the same
  ends (`Gluing.Cut.OK.sim`), and lengthening a pair of glued sides by two edges *is* cutting one of their edges
  (`Compose.Move.OK.equiv`). The three crossings and two hooks of the new path are computed directly (`Sim.cross`),
  where the paper uses the zigzag lemma with n = 3. That a move creates no closed strand goes through Prop 5.4 (b), (c)
  (`Sim.noLoops`: every port at a mark after the cut is the image of a port before it); the paper argues directly.
- **Prop 7.4** carries the signature in the form `Gluing.Sig`, which finds each parent rim vertex by turning about a
  child's vertex (`Gluing.Rot`), not by Table 3, and asks a little more: that the Γ child's edges at A and B are parent
  rim edges. It does not carry the adjacency of A and B; that is read off Table 3 at tile level (`corners_nonSigma`,
  `corners_sigma`), and proved for the compositions separately (`parity_lemma_adj`).
- **Lemma 7.2** (reachability) is the induction `Compose.adm_sig` (and `adm_induct` for any property), backwards on
  the excess over the level-1 lengths, with the same choice of move as the paper's proof; its part (b) is the step of
  that induction, not a separate lemma.
- **Lemma 8.3** is used in form (b), that every edge of N_b is glued in N_{b+2} (`no_boundary`), proved from the tables
  as the paper notes. Form (a) is proved for the vertices of tiles (`grandparent`): every vertex of every tile of N_b is
  surrounded by tiles of N_{b+2}. The proof needs a fact the paper takes from the geometry: every supertile is a disc
  at its rim, that is, turning about each rim vertex runs from the tile beside one rim edge to the tile beside the
  other (`RimChains`, proved level by level from the nine level-1 clusters). For a vertex on side 2 of N_b it extends
  the table argument of (b) to vertices, where the paper's (a) uses eq. (side2) and that the closed sides 2 and 4 of
  N_{b+1} are disjoint. The step from tile vertices to points of the plane is part of (M3).
- **Computation 9.2 and Lemma 9.3.** The kernel computes the second part of Computation 9.2. The first part (a rim
  vertex strictly inside side 2 of N_m is a hook of N_{m+1}) is proved at tile level for every level, from the
  signature of N_{m+1} (`stretch_eq`, `adv_none`). For the two vertices a cut adds, Lemma 9.3's proof follows each new
  port two or three steps to the old port beside it (`NewWalk.lean`), where the paper uses the last part of the zigzag
  lemma.
- **Lemma 9.4** is used with "at least two edges from the ends", which is what the proofs need; it is also proved with
  five, as the paper states it (`lemma_9_4`).
- **Theorem A** is proved for any chain of supertiles whose union has every edge eventually glued (`TheoremA_strand`);
  that a tiling whose hierarchy covers the plane is such a union is (M2). The nest is such a chain (`NestCovers`).
- **Thm 9.1** is proved as the bound (`TheoremB_sharp`), and the last two rows of Table 5, which its proof gives, as
  `TheoremB_exact`: the paper's "distinct hooks are distinct arcs" is `hooks_apart`, by the ends of a strand
  (`Linked.ends`).

## Building

```
./build.sh          # about 10 minutes from clean (peak memory about 1.5 GB per kernel check); 3 minutes when cached
./build.sh --data   # first regenerate the data files from paper/code (python3, node)
./build.sh --slow   # also run TestsSlow.lean (level-5 checks, about 5 minutes more)
tools/check_data.sh # the data files are exactly what paper/code generates (about a minute)
tools/comparator.sh # leanprover's comparator: the main theorems prove exactly the claims (about 4 minutes)
```

`build.sh` fails if one of the files that fix what is proved has changed since `TRUSTED.sha256` was recorded
(`tools/check_trusted.py`); if any source uses, outside comments, `sorry`, `admit` or `native_decide`, or another way
round the kernel or the axiom check (`axiom`, `opaque`, `partial`, `unsafe`, `implemented_by`, `extern`,
`debug.skipKernelTC`, `ofReduceBool`; `tools/no_sorry.py`); if a `theorem` or a `have` lacks a comment
(`tools/check_comments.py`); if the build or a test fails, or a main theorem no longer proves exactly its claim (the end
of `Axioms.lean`); if a theorem listed in `Axioms.lean` has not reported its axioms, or depends on one other than Lean's
standard three (`propext`, `Classical.choice`, `Quot.sound`); or if `leanchecker`, which replays every declaration of
`SpectreKnot` through Lean's kernel, finds a problem (about 3 minutes). Names must be declared: the lakefile turns off
Lean's automatic binding of undeclared names (`autoImplicit`). CI also runs `tools/check_data.sh` whenever `paper/code/`
or the data change (`data.yml`).

`tools/comparator.sh` runs leanprover's [comparator](https://github.com/leanprover/comparator), a tool built to judge
whether proofs prove exactly the statements of a trusted file. It states each main theorem's claim, read from the pins
at the end of `Axioms.lean`, with `sorry` in a challenge file that imports only `Statement.lean` (in a temporary copy
of `lean/`, so that no `sorry` enters the sources); comparator then checks that each theorem of `SpectreKnot` has
exactly that statement, uses only Lean's standard axioms, and is accepted by the kernel. A negative control: with one
claim swapped for another in the challenge, it stops ("theorem statement do not match"). CI runs it in the public
repository. comparator builds in landrun, a sandbox meant for proofs from an untrusted source; where landrun is not
installed, the script uses comparator's development shim, which builds unsandboxed.

From clean, most of the time goes on the kernel computations: `CompFull` (the 18
compositions of Computation 7.3, about 2.5 minutes), `Tests` (about 1.5 minutes), `SigCheck` and `SkeletonWalks` (about
30 s each), then the level-1 checks (`PatchSig`, a few seconds) and the junction map (`StepMap`, a few seconds).

Toolchain: Lean 4.34.1 (pinned in `lean-toolchain`), core library only. In a claude.ai cloud container, elan cannot
resolve a toolchain because `release.lean-lang.org` is blocked, but GitHub release downloads work:

```
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
curl -sSL -o lean.tar.zst https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst
# unpack (tar --zstd, or python3 -m pip install zstandard), then:
mv lean-4.34.1-linux ~/.elan/toolchains/leanprover--lean4---v4.34.1
```

## What is formalised

Numbering as in the paper (revised 11 October 2026). The last column says how the Lean statement differs from the
paper's, starting with one of: *same*; *stronger*; *weaker*; *part* (only part of the result); *other form* (the same
content stated another way, or only for the patches the Lean builds, with what links them to the paper's); or *not in
the paper*. The proof map's build fails if a row does not say.

| paper | Lean | kind | what the Lean statement says | differs from the paper |
|---|---|---|---|---|
| Lemma 3.4 | `StrandSystem.closed_or_path` | proof | Strands are modelled as two fixed-point-free involutions on ports: `inside` (the pieces) and `across` (the straight-through rule). A strand is either closed, or a two-way infinite path that never passes a port or a piece twice. | other form: for strands given as two fixed-point-free involutions on ports, not the strand graph of Def 3.3; that every port is joined to exactly one other (degree 2) is built into this model, and proved for the nest tiling and for chains |
| Def 3.1, Lemma 4.4 (tile) | `tilePiece`, `tile_signature` | `decide` | The pilot's model of the tile: its 14 pieces as a pairing of its 28 ports, and the tile has the signature at (v₀, v₁). (The statement file has its own decoration, `pieceEnd`; the main theorems use that one.) | part: the tile only, in the pilot's model of it (the main theorems use `pieceEnd`); the Mystic is not treated separately |
| Lemma 5.1 (the Zigzag Lemma) | `Zigzag.zigzag` | proof, any `n` | Along a shared path of `n` edges, the two connections and where each hook goes, exactly as in the paper. Its core, `Zigzag.walk_core`, is what Prop 5.4 uses, and through it the lengthening. For odd `k` a hook is placed on the connection named by its end at u₀, the paper's by its end at u_n: the same connection. | same: for every length `n` |
| Lemma 4.2, Def 5.2 | `Gluing`, `FullReach`, `smooth`, `runLen`, `sigmaRed`, `RedReach` | definitions | A patch glued from children that each have the signature, in general (`Gluing`): the full walk of Lemma 4.2 as an inductive relation; marks (non-smooth child vertices: junctions, corners on either side, and a vertex whose two edges are glued to non-consecutive edges of one sibling, which no real patch has); runs; the reduced walk. | other form: definitions; the full walk of Lemma 4.2 is a relation defined by rules (Lemma 4.2 at tile level is the row for §7.1 below) |
| Prop 5.4(a) | `Gluing.prop_5_4_a` | proof | A child's vertex that is not a mark, with both edges on the parent's rim, is a hook of the parent. | other form: starts from a child vertex that is not a mark, with the edge after it on the parent's rim; the paper's first step, from a parent rim vertex that is not a mark to such a child vertex, is not formalised |
| Prop 5.4(b) | `Gluing.prop_5_4_b`, `Gluing.fullReach_unique` | proof | For every well-formed gluing and every port: the full walk and the reduced walk end at the same rim port; and the end of the full walk is unique. | stronger: from every port, not only from reduced ports |
| Prop 5.4(c), the form used | `Gluing.prop_5_4_c` | proof | If the reduced walk from every port at a mark reaches the rim, so does the full walk from every port: no closed strand. | weaker: only the form the proof uses, that if the reduced walk from every port at a mark reaches the rim no strand is closed; the count of closed strands, κ(P), is not formalised |
| Prop 6.1 | `sideLen_eq_letterLen` | proof + `decide` on Tables 1, 3, 4 | ℓ_m(K, j) depends only on the letter, for every m ≥ 1. Here ℓ_m is *defined* by the recursion of Prop 2.4(c) from the level-1 counts. | other form: ℓ_m is defined by the recursion of Prop 2.4(c); that `super m K` has these side lengths is proved (`Statement.good`: `Good.vtx`, `Good.len`); that actual supertiles do is (M1) |
| Prop 6.2 | `letterLen_fib` | proof | The Fibonacci closed forms. | same |
| Cor 6.3 | `letterLen_parity`, `sideLen_parity` | proof | Parities are the same at every level ≥ 1 (for the letters, and for the sides). | same |
| Lemma 6.4 | `dOff_fib`, `Statement.cornerA` | proof | d_m = 2F_{3m+1}, and δ_m − d_m = 2F_{3m}. Here d_m is defined from Table 3 (the pieces 0.2, 0.1, 7.0). The crossover corner of `super m K` lies at vertex 0, or for Σ at the point 2F_{3m+1} along side 5 (`cornerA`, in `SignatureTheorem`). | same: for `super m K`; that actual supertiles are so is Prop 2.4(d), part of (M1) |
| Lemma 6.5 | `bounds` | proof | Every side ≥ 5, d_m ≥ 6, δ_m − d_m ≥ 4. | same |
| §7.1, the compositions | `Compose.Comp.ofLens`, `Comp.toGluing`, `Comp.check` | definitions | C_T(L, d, ω) built from Tables 1–3, side by side: children with the signature at their corners (A at vertex 0, or for Σ at distance d along side 5; B = A + ω), sides glued in pairs reversing direction, the parent's rim from Table 3. "Has the signature", as §7.1 words it, is `Comp.check`; the induction of Prop 7.4 carries another form of it, `Gluing.Sig` (row for Prop 7.4). | same: definitions, as in §7.1 |
| Lemma 7.1 (lengthening) | `Gluing.Cut.OK.sim`, `Gluing.Cut.OK.sig`, `Compose.Move.OK.equiv`, `Compose.Move.OK.keep` | proof | Cutting one edge into three (shared by two children, or on the parent's rim) maps every walk to a walk with the same ends, and keeps the signature; "no closed strand" carries over by Prop 5.4 (c) and (b) (`Sim.noLoops`). Lengthening a glued pair of sides by two edges (and d by two if the cut lies before the Σ corner) gives the same gluing, port for port, as cutting one edge; so a move keeps the signature. | other form: lengthening is shown to be cutting an edge into three, which keeps the ends of every walk; the crossings of the new path are computed directly, not by the Zigzag Lemma; that a move creates no closed strand goes through Prop 5.4(b), (c) |
| Lemma 7.2 (reachability) | `Compose.Adm`, `Compose.adm_level`, `Compose.adm_sig`, `Compose.adm_induct` | proof | The admissible pairs (L, d) are those of the paper; (ℓ_m, d_m) is admissible for every m ≥ 1 (`adm_level`); every admissible pair other than (ℓ₁, d₁) comes by a move from one with less excess, with the paper's choice of move (the third edge of a side; on the Σ child's side 5 the second edge before the corner, or the second after it); so a property that holds at (ℓ₁, d₁) and survives such moves holds at every admissible pair (`adm_induct`). | other form: an induction principle (`adm_induct`; `adm_sig` for the signature), with the paper's choice of moves in both; the extra clause of (b), two edges from the ends, is the hypothesis of its step |
| Comp 7.3 | `Compose.compositions_level1`, `Compose.compositions_level1_signature`, `Compose.sig_base` | kernel computation + proof | The 18 compositions C_T(ℓ₁, d₁, ±1), built from Tables 1–4 and ℓ₁, d₁, glued port by port (Lemma 4.2). For each, the checker `Comp.check` returns `true`, and `Comp.check_sound` turns that into statements: the walk from every port ends on the rim, every parent rim vertex but the Γ child's corners is a hook, and the corners are adjacent and carry the crossover. `sig_base` states the same as `Gluing.Sig` (each parent rim vertex found by turning about a child's vertex, `Gluing.Rot`), the form the induction carries. | same: and the checker's `true` is proved to mean the signature (`Comp.check_sound`) |
| Prop 7.4 | `Compose.parity_lemma`, `Compose.parity_lemma_adj` | proof + kernel computation | For every m ≥ 1, every kind and both signs: C_T(ℓ_m, d_m, ω) is well formed and has the signature (`Gluing.Sig`): no strand closes up; every parent rim vertex is a hook except the Γ child's corners A and B; A and B lie on the parent's rim and carry the crossover (`parity_lemma`), and are adjacent, B after A in the children's sense if ω, before it otherwise (`parity_lemma_adj`). The induction carries the form `Gluing.Sig` (each parent rim vertex found by turning about a child's vertex), which leaves out adjacency and asks that the Γ child's edges at A and B lie on the parent's rim. | same: for every m ≥ 1, every kind and both signs |
| Comp 7.5 | `Statement.good_one` | kernel computation | The nine level-1 supertiles (from `exact.py`) have the signature, with A and B where the induction expects them. | same: on the level-1 supertiles computed by `exact.py`, which are input data, with A at vertex 0 (for Σ, d₁ along side 5) and B = A + ω₁. That this vertex is v₀ of the Mystic's first tile, the paper's recursive A, is not checked: the Lean has no Mystic |
| §7.1 (a supertile is its composition), with Lemma 4.2 | `Statement.Kids.follow_of_reach`, `Statement.Kids.noClosed`, `Statement.glue_rim`, `Statement.compose_no_default` | proof | In `compose T child`, if the children have the signature with the corners and side lengths of `Comp.ofLens`: across a child's rim edge, `compose` glues exactly what `Comp.mate` says; every walk of the composition is a strand of the parent; and the parent has no closed strand when the composition has none. So, at every level, `compose` never falls back on a default: an unglued edge of a child is found at its one place on the child's rim, and sides that Table 2 glues have equal lengths (`compose_no_default`). | other form: at tile level, for the supertiles that `compose` builds; that actual supertiles are built so is (M1) |
| Prop 2.4 for rims | `Statement.rim_edgeAt`, `Statement.own_rot`, `Statement.parent_vtx` | proof + table check | The parent's rim, read from Table 3, is the rim of the glued children: its positions are the children's unglued edges, each once; consecutive positions meet at a parent rim vertex (turning about it by Table 2: `rimTablesOk`); its six vertices are where the parent's side lengths put them. | part: only that Table 3 lists the rim of the glued children; Prop 2.4 itself is (M1) |
| Thm 7.6 | `Statement.signatureTheorem`, `Statement.good`, `Statement.Kids.parent_sig`, `Statement.theoremA` | proof + kernel computation | Every supertile `super m K` of level m ≥ 1 has the signature at tile level (`Patch.HasSig`): its rim list is exactly its unglued edges, each once; no strand closes; following the ribbon from each rim port leads to the other port at the same rim vertex, except at the corners A and B (vertex 0, or for Σ the point d_m along side 5), which cross over (`corners_nonSigma`, `corners_sigma`); B = A + ω_m in own order. The claim `SignatureTheorem` states this in the statement file, with A and B written out (`cornerA`, `cornerB`) and every supertile a disc at its rim (`RimChains`). Hence `TheoremA`: no supertile of any level or kind contains a closed strand. | other form: for the supertiles built from the tables (`super m K`, m ≥ 1); that actual supertiles are glued so is (M1) |
| **Theorem A** (the Daedalus Theorem) | `Statement.chainModel`, `Statement.theoremA_strand`, `Statement.nestCovers` | proof | For any chain of supertiles, each a child of the next: its union, with its tiles numbered so that every block keeps its own numbering, is a tiling containing every block (`ChainModel`; a `Tiling` that contains every block exists, its gluing chosen with `Classical.choice`). If the chain covers (every edge is eventually glued), every such tiling glues every edge, and every strand of the union is a two-way infinite path (`TheoremA_strand`): a closed strand would visit finitely many tiles, whose edges are all glued in one block (`all_glued_at`), and that block has no closed strand. The nest, as a chain, covers (`NestCovers`, from `no_boundary`), so the theorem applies to at least one chain. | other form: for the union of a chain of supertiles that covers (every edge eventually glued); that a tiling whose hierarchy covers the plane is such a union is (M2) |
| Comp 9.2 | `Statement.step_base` | kernel computation | In C_Δ(ℓ₁, d₁, ±1), the walk from every port of child 1 outside the interior of its side 2 ends at a port of the parent hook at the junction that `tgt` names (the paper's Table 6). | other form: the kernel computes the second part; the first is proved at tile level, for every level, from the signature of N_{m+1} (`Statement.stretch_eq`, `Statement.adv_none`) |
| Lemma 9.3 | `Statement.step_level`, `Statement.StepOK.move`, `Statement.step_tile`, `Statement.stretch_eq` | proof | The same at the level-m lengths, every m ≥ 1, both signs: carried from ℓ₁ by the moves of Lemma 7.2 (`adm_induct`), with cuts on child 1 kept two edges from the ends of its sides; a cut adds two vertices whose strands are those of the old vertices next to it (`NewWalk.lean`, followed port by port, where the paper uses the last part of the Zigzag Lemma). At tile level: a rim port of N_m lies, in N_{m+1}, on the strand of the hook at that junction; strictly inside N_m's side 2 the rim port is a hook of N_{m+1} itself. | same: for every m ≥ 1 and both signs |
| Lemma 9.4 | `Statement.lemma_9_4`, `Statement.inside_9`, `inside_12`, `inside_16`, `inside_17`, `inside_21`, `inside_stp` | proof | The junctions 9, 12, 16, 17, 21 lie inside sides 2, 3, 4, 4, 5 of N_{m+1}, and the inside of N_m's side 2 inside side 4, at least five edges from the ends (`lemma_9_4`, as the paper states it); the proofs use the form with two (`Inside`), which is what they need. | same: the paper's five edges, and the proofs' two |
| Lemma 8.3 (the Grandparent Lemma), in combinatorial form | `Statement.no_boundary`, `Statement.grandparent`, `Statement.chains_super`, `Statement.Patch.surrounded_or_chain`, `Statement.delta_cycles` | proof + kernel computation + table check | (b) Every edge of N_b (b ≥ 1) is glued in N_{b+2} (`no_boundary`). (a) Every vertex of every tile of N_b is surrounded by tiles of N_{b+2}: turning about it (`turn`, crossing the edge that ends there) comes back to it (`Grandparent`). Every supertile is a disc at its rim (`RimChains`: turning about each rim vertex runs from the tile beside one rim edge to the tile beside the other; the nine level-1 clusters by the kernel, then level by level, `Kids.rimChains`); every vertex is surrounded or on such a chain (`surrounded_or_chain`, by counting); in the Δ composition, turning about a vertex of child 1 off its side 2 comes round (two steps inside a side, three at a vertex by Table 2, `delta_cycles`), and so does turning about a vertex inside child 1's side 4, glued to child 3; child 1's side 2 lies inside side 4 of the parent. | part: (b) from the tables, as the paper's proof also does; (a) at the vertices of tiles, the step from those to points of the plane being (M3) |
| — | `Statement.super_glueSymm`, `Statement.linked_symm`, `Statement.super_noSelf` | proof + kernel computation | Every supertile's gluing is symmetric, and glues no tile to itself (the level-1 data checked by the kernel); so "same strand" (`Linked`) is symmetric there. | not in the paper: the paper takes these from the geometry |
| Thm 9.1, then **Theorem B** (combinatorial form) | `Statement.chain_even`, `Statement.chain_odd`, `Statement.theoremB_sharp`, `Statement.theoremB` | proof | Every port of N_b lies, in N_{b+3} (b even) or N_{b+4} (b odd), on the strand of the hook at junction 12; with symmetry, any two ports of N_b are on one strand there (`TheoremB_sharp`). With `no_boundary` and Theorem A, `TheoremB`. | same: the bounds of Thm 9.1, for every b ≥ 1; Theorem B here is for the blocks N_b, and its final form is the row below |
| Thm 9.1: the bound is exact (Table 5, last two rows) | `Statement.Patch.Linked.ends`, `Statement.hooks_apart`, `Statement.theoremB_exact` | proof | For b ≥ 1 the ports of N_b lie on exactly two strands of N_{b+2}, and for odd b of N_{b+3} (`TheoremB_exact`): every port reaches one of two hooks (junction 16 and the hook at junction 9 of N_{b+1} for even b; junctions 12 and 9 for odd b, then junction 16 and the hook at junction 9 of N_{b+2}), each is reached from a hook well inside a chosen side of N_b, and hooks at different rim vertices lie on different strands, since along a strand its two ends stay the same (`Linked.ends`). | same: the last two rows of Table 5, for every b ≥ 1; the rows for single values of b are computed by the tests, not proved |
| **Theorem B** (the Ariadne Theorem), final form | `Statement.nestModel`, `Statement.theoremB_strand` | proof + kernel computation | The nest tiling (`nestTiling`, a `Tiling`): its tiles numbered so that every block keeps its own numbering, and a gluing that contains every block's and glues every edge, to an edge of another tile, which is glued back (`NestModel`). Its ports form a `StrandSystem`. No strand is closed, since a closed strand would stay in one block, which has none (Theorem A); any two ports lie on one strand, since they do in a large enough block (`TheoremB_sharp`). So by Lemma 3.4 the strand through R(v₀) of the original tile is two-way infinite, never meets a port or a piece twice, and runs through every port (`TheoremB_strand`). | other form: for `nestTiling`, the union of the blocks; that it is the paper's nest tiling and covers the plane is (M3) |
| Remark 7.8 (corroboration) | `Skeletons.skeleton_walks`, `Skeletons.agrees_with_js` | kernel computation | The pilot's check: the reduced walk on the 18 skeletons exported from `synth.js` gives the signature, and finds the same non-hooks as `core/reduce.js`. Not used by the main results. | part: the skeleton walks of (3), on 18 skeletons exported from JavaScript, as corroboration; Def 5.3 and Cor 5.5 are not formalised |
| — | `Skeletons.negative_control`, `Compose.negative_control`, `Statement.loopPatch_closed` | kernel computation / proof | Corrupted inputs are rejected, so the checks and the definitions are not vacuous. | not in the paper: negative controls, so the checks and the definitions are not vacuous |

Data: `SpectreKnot/Data/Pattern.lean` (Tables 1–4, the level-1 side lengths, d₁) is generated from
`paper/code/hierarchy/combin_8.json` and `letters.json` by `tools/gen_pattern.py`. `Data/Clusters.lean` (the nine
level-1 supertiles at tile level) and `Data/Level2.lean` (level 2, for tests) are computed by `tools/gen_clusters.py`
with `paper/code/exact/exact.py` (exact arithmetic). `Data/Skeletons.lean` (for the pilot's check) is generated from
`synth.js` by `tools/gen_skeletons.js`. The two computations on compositions (Computation 7.3 and Computation 9.2) are
also done, separately, by `paper/code/hierarchy/compositions.py`.

## What the main results use

`tools/unused.lean` (run `lake env lean tools/unused.lean`) lists every declaration that the eleven main results
(`signatureTheorem`, `theoremA`, `theoremB`, `theoremB_sharp`, `nestModel`, `theoremB_strand`, `chainModel`,
`theoremA_strand`, `nestCovers`, `theoremB_exact`, `grandparent`) do not use. Everything else in `SpectreKnot/` is used
by them, including Prop 5.4 (b), (c) and the zigzag lemma's core. What they do not use is kept on purpose:

| not used by the main results | why it is kept |
|---|---|
| `Box.lean` (`tilePiece`, `tileBox`, `tile_signature`, …) | The pilot's model of the tile (Def 3.1, Lemma 4.4); the statement file has its own decoration. |
| `Skeleton.lean`, `SkeletonWalks.lean`, `Data/Skeletons.lean` | The pilot's run of the skeleton walks (Remark 7.8) on skeletons exported from JavaScript, and its agreement with `core/reduce.js`: corroboration. |
| `Zigzag.zigzag`, `Gluing.prop_5_4_a` (with `smooth_corner`), `Statement.lemma_9_4` (with `Inside5`, `inside5_of`), `Gluing.fullReach_unique`, `sideLen_parity`, `Compose.parity_lemma_adj` (with `sig_adj`, `ofLens_B'`), `Compose.compositions_level1_signature` | Results of the paper, formalised as stated there; the main proofs use other forms of them (`walk_core`, `letterLen_parity`, `parity_lemma`, `compositions_level1`). |
| `Skeletons.negative_control`, `Compose.negative_control` (with `spreadCorners`), `Statement.loopPatch_closed`, `Statement.rim_not_surrounded` | Negative controls: the checks and the definitions are not vacuous. |
| `Compose.allKinds`, `Gluing.redWalk`, `Gluing.redWalk_sound` | Used by the tests. |
| `Statement.compose_no_default` | Says outright that `compose` never uses its defaults; the main proofs use `glue_rim`, which implies it. |

The tool has one blind spot: a `@[simp]` lemma proved by `rfl` leaves no trace in the proofs that use it. It lists
`iter_zero`, which `iter_add` uses that way.

## What it does not show

- **The link with tilings of the plane: assumption (M)**, written out at the top of `Statement.lean` in three parts.
  The formal statements are about patches and tilings described by their gluing; each part is argued in the paper and
  none is formalised.
  - **(M1) Supertiles.** That the supertiles of an actual tiling are glued like `super m K`. It rests on the spectre
    paper and on the paper's §2: Thm 2.1 (the hierarchy, from the spectre paper), Prop 2.4 (the composition pattern
    holds at every level), Remark 2.5 (its cross-checks against the spectre paper's figures), Lemma 2.6 (rigidity)
    and Def 2.2 (own orientation, built into `compose`). In Lean, Tables 1–4 are simply data.
  - **(M2) Theorem A for tilings.** `TheoremA_strand` is about the union of a chain of supertiles that covers, that
    is, in which every edge is eventually glued. That a tiling whose hierarchy covers the plane is such a union is the
    first half of the proof in §7.4, about points of the plane.
  - **(M3) Theorem B for the nest tiling of the plane.** `TheoremB_strand` is about `nestTiling`, the union of the
    blocks `super b .Delta`. That this is the nest tiling of the paper, and that it covers the plane, is Prop 8.2 and
    Prop 8.4, which are geometric. Lemma 8.3(a), which Prop 8.4 uses, is formalised for the vertices of tiles
    (`Grandparent`); the step from those to points of the plane is part of (M3).
- **Lemma 4.1.** The box of a patch, as an involution on its rim ports with no fixed point and E arcs, is not stated:
  following a ribbon (`Follow`) plays the role of π_P, and only what the proofs use about it is proved.
- **Level 0 of the hierarchy.** The Lean starts from the nine level-1 supertiles as data. The Mystic (the level-0 Γ,
  Lemma 4.4) is inside them and is not treated separately.
- **The skeleton route.** Def 5.3 (skeletons and their equality), Cor 5.5 (where a hook goes) and the skeleton argument
  of Remark 7.8 (3) are not formalised (the pilot's skeleton walks are computed, not used). Nor are the label states
  and certificates of Remark 9.5 (3).
- **Exact counts.** The last two rows of Table 5 are proved (`TheoremB_exact`); the rows for each b (such as 10, 37,
  146, 613 strands one level up) are computed by the tests for small b, not proved for every b.
- **Remarks and the drawing.** Remark 3.5 (no single strand in a periodic tiling), Remark 3.6 (over and under), the
  drawing itself, Remark 10.1 (three strands along another chain; the tests compute its first counts) and §10 (faults).
- **Data are input.** Tables 1–4 come from `combin.js` (the composition pattern computed from the geometry, and checked
  against the spectre paper's figures by the paper's scripts); the level-1 supertiles come from `exact.py`. The Lean
  checks the level-1 supertiles' signature itself (`good_one`), but not that they are the spectre paper's clusters.

## Findings

1. **Toolchain.** Core Lean was enough throughout: `omega` did all the arithmetic, `decide` the table checks. The
   recurring friction was index normal forms (`k + 1 + 1` against `k + 2`; `3 * (k + 1) + 2` against `3 * k + 5`),
   fixed by explicit rewrites, and definitional unfolding: a `show` or `rw` that makes Lean unfold a large supertile
   can run out of time, so such steps state the unfolded form explicitly.
2. **The definitions work.** With the port model, Lemma 3.4 and the zigzag lemma went through without changes to the
   definitions; the zigzag lemma compiled first time. Its second connection comes from relabelling the first, not
   from a second proof.
3. **The kernel is fast enough.** The 18 reduced walks plus the agreement check take about 30 s. The 18 unreduced
   compositions (about 730 ports each) take about 2.5 minutes. The junction map at ℓ₁ takes a few seconds.
4. **Negative controls need care.** The first reduced-walk control was rejected by the consistency check, not by the
   walk. The first unreduced check did not test that the parent's corners are adjacent and carry the crossover; it
   relied on the Γ child having them. Both are fixed: the controls now fail for the intended reason, and the check
   tests the whole signature. Lesson: a checker's `true` means only what its code says, so the code (or a proof of
   its soundness) has to be read.
5. **Prop 5.4 (stage 2).** It went through as the paper argues it, with two changes that made it easier than
   expected. First, the reduced walk acts on the same ports as the full walk, so (b) is proved from every port, not
   only from the reduced ports at marks. Second, cyclic positions use explicit successor and predecessor functions
   instead of `mod`, which `omega` cannot handle with a variable modulus. Each run is a direct use of the zigzag
   lemma's core (`Zigzag.walk_core`); the `L` ports reuse the `R` case through the relabelling `Zigzag.swap`.
6. **Checkers now prove what they claim.** The pilot's unreduced check counted visits to infer "no closed strand",
   an argument that was never formalised. It now runs the walk from every port, and `Comp.check_sound` turns `true`
   into theorems. One kernel run needs about 1.5 GB, so the 18 runs are 18 separate theorems.
7. **A by-product.** The signature step is robust. In the full compositions at the level-1 lengths, lengthening any
   one glued pair of sides (or one rim side) by a single edge keeps the signature in all 18 cases, and so does
   changing d by one: 658 compositions in all, checked again on 19 Oct 2026 with the compositions of
   `paper/code/hierarchy/compositions.py`. So the parity condition is sufficient (which is all the proof uses); changed
   one pair at a time, it is not necessary. Non-adjacent corners do break it. None of this is needed by the proof.
8. **The signature at every level by lengthening (stage 3).** The paper at the time proved this on the reduced data:
   the skeleton depends only on the parities and an order condition (its old Lemma 7.1). The Lean proof took another
   route. Lengthening a glued pair of sides by two edges is the same, port for port, as cutting one of their shared
   edges into three; and cutting an edge maps every walk to a walk with the same ends (the strand passes two more hooks
   on each side). So the signature at (ℓ₁, d₁), computed once, carries over to every (L, d) reached by such steps. By
   Prop 6.2, Cor 6.3 and Lemma 6.4 these include every (ℓ_m, d_m). The Σ offset needs care: a cut before the Σ corner moves it
   on by two, and a cut on the Σ child's side 5 must avoid the corner. The induction runs backwards on the total
   excess over ℓ₁ (`adm_sig`). This route does not use the skeleton, but it does use Prop 5.4: after a cut, "no closed
   strand" needs checking only from the marks, whose walks are images of old walks (`Sim.noLoops`, by Prop 5.4 (c)
   and (b), and so the zigzag lemma's core). The paper now takes this route (§7.2); the skeleton route is its
   Remark 7.8.
9. **Lists made the signature hard to carry over; turning about a vertex made it easy.** `check` states the
   signature with the parent's rim as a list, which a cut changes in index-heavy ways. `Gluing.Sig` finds each parent
   rim vertex by turning about a child's vertex (`Gluing.Rot`), which a cut leaves alone. Its checker `sigCheck`
   needed a new kernel run, but only about 30 s for all 18 cases.
10. **Theorem A (stage 4).** The link to the statement file went as planned, in four parts: reading `compose`
    child by child (`compose_glue_def` is `rfl` once its `let`s are named; `compose_glue`); the parent's rim from
    Table 3 as a function of position (`ownGo`), with one table check (`rimTablesOk`: Table 3 lists each rim side of
    a child once, and consecutive pieces meet at a vertex by Table 2); Lemma 4.2 at tile level (`Bridge.lean`); and
    the parent's signature read off `Gluing.Sig` (`ParentSig.lean`), which needed two small facts about gluings:
    walks run backwards, and turning about a vertex is injective on rim vertices (`Reverse.lean`). The base is the
    nine level-1 clusters, checked by the kernel in a few seconds. In Lean, Theorem A rests on Tables 1–4, the
    level-1 data, the 18 compositions at level 1, Prop 5.4 (b), (c) and the lengthening; it does not use the
    skeleton or the exported skeletons.
11. **Theorem B (stage 5) by the junction map.** The paper at the time merged strands with label states and certified
    length comparisons. The Lean proof looks one level up at a time instead. In the Δ composition, every strand of
    child 1 (the previous block) runs to a parent hook at a *junction*, the vertex where a piece of Table 3 starts, and
    which junction depends only on where the strand leaves child 1: well inside side j, only on j. (Child 1's side 2
    lies on the parent's rim; the vertices strictly inside it are parent hooks themselves.) This map is checked by the kernel at ℓ₁ and
    carried to every level by the moves of the lengthening: a cut on child 1, kept two edges from the ends of its side,
    adds two vertices whose strands are those of the old vertices next to the cut (`NewWalk.lean`). The induction of
    `adm_sig`, written once for any property (`Compose.adm_induct`), does the rest. The junctions all lie well inside
    the parent's sides 2–5, so one level up the map is read side by side: from sides {2, 3, 4} (b even) or {4, 5}
    (b odd), every strand reaches junction 12 of N_{b+3} or N_{b+4}, the paper's bounds. "Same strand" also needed
    symmetry, so gluing is proved symmetric for every supertile. In Lean, Theorem B rests on Theorem A's inputs and
    three more kernel checks (the map at ℓ₁, both signs, and the symmetry of the level-1 gluing); it needs no
    certificates, and no separate computation for b = 1. The paper now takes this route (§9.1); the label states are
    its Remark 9.5.
12. **Lemma 3.4, applied.** The nest tiling is built as one tiling: its tiles are numbered so that every block keeps
    its own numbering (`gid`, `loc`), and its gluing is read off a block two levels above the tile. That every block
    gives the same answer (`NestModel` (d)) is the one non-trivial step: both answers, seen in a block above both,
    are the same gluing of the same tile. Two facts were needed that Theorem B did not use: no tile is glued to
    itself (so the straight-through rule has no fixed point; the level-1 data checked by the kernel), and a closed
    strand would stay in one block. Since the nest tiling's gluing is read two levels up, a closed strand is followed
    in the block two levels above one holding its tiles, where every edge of those tiles is glued (`no_boundary`). The
    rest is `closed_or_path` from the pilot, which since 19 Oct 2026 also states that the ports met backwards are
    distinct.
13. **Every theorem and every `have` carries a comment**, and hypotheses have descriptive names (`child_lt`,
    `glued`, `on_rim`, …); the variables of statements keep the paper's notation (`c` child, `j` side, `t` tile,
    `L` side lengths, `d`, `ω`, `μ`). `tools/check_comments.py` enforces the comments in `build.sh`.
14. **Theorem A for any chain (stage 6).** The nest argument of finding 12 works for any chain of supertiles, with
    two changes. There is no fixed number of levels after which an edge is glued (for the nest it is two, Lemma 8.3),
    so a gluing of the union cannot be read off one block and is chosen instead (`Classical.choice`); and the finitely
    many tiles of a closed strand have all their edges glued in one common block (`all_glued_at`, a finite maximum).
    Theorem A then needs only Theorem A for supertiles, not the junction map.

15. **The bound is exact (stage 7).** The paper's last step, "distinct hooks are distinct arcs", needed one new fact:
    along a strand its two ends on the rim stay the same (`Linked.ends`; every move along a strand can be undone, by the
    symmetry of the gluing), and the ends of a hook's strand are the hook's own two ports. The rest is the junction map
    of finding 11, read off once more: `first` now also says that a strand reaching side 2 of N_{b+1} does so at
    junction 9.
16. **The Grandparent Lemma at tile vertices (stage 7).** Turning about a tile vertex (`turn`) needs no new data: it is
    `glue` read at the edge that ends at the vertex. The proof needed one fact the paper takes from the geometry: every
    supertile is a disc at its rim (`RimChains`). It goes up level by level like the signature: a chain of the parent is
    made of the children's chains, joined as the abstract gluing turns about a child vertex (`Rot`, or backwards `RotB`,
    as the children are oriented), which `own_rot` already provides. Every other vertex is surrounded or on a chain, by
    counting (a pigeonhole argument, `surrounded_or_chain`). Then an argument on the tables: off its side 2, N_b is inside
    N_{b+1} (two steps of turning inside a side, three at a vertex of child 1, `delta_cycles`); its side 2 lies inside
    side 4 of N_{b+1}, which is glued to a sibling in N_{b+2}. That is the paper's proof of (b), carried to vertices; for
    (a) the paper argues instead that the closed sides 2 and 4 of N_{b+1} are disjoint. The kernel check of the nine level-1 clusters
    takes about a second.

## Size and time

About 13,000 hand-written lines of Lean, with the tests and the statement file; about a quarter of them are comments.
There are also 490 generated lines. By stage, in today's files:

- Stage 1, the pilot: `Basic` 52, `Box` 64, `Strands` 189, `Zigzag` 134, `Lengths` 284, `Skeleton` 168,
  `SkeletonWalks` 28.
- Stage 2, Prop 5.4: `Gluing` 227, `Prop54` 506, with `Compose` 184 and `CompFull` 99 (the compositions).
- Stage 3, the lengthening: `Subdivide` 951 (cutting an edge), `Move` 709 (lengthening is cutting), `Parity` 575
  (the induction), `Signature` 298, `SigCheck` 209, `Lens` 183.
- Stage 4, Theorem A for supertiles: `ParentRim` 515 (Table 3 as a rim), `ParentSig` 484 (the parent's signature),
  `Bridge` 437 (Lemma 4.2), `ProofA` 416 (the induction and the corners), `ComposeTiles` 277, `PatchSig` 183 (the
  tile-level signature, the level-1 check), `Reverse` 178.
- Stage 5, Theorem B: `StepMap` 843 (the junction map and its induction), `ProofStrand` 749 (the nest tiling and
  Lemma 3.4), `ProofB` 600 (the chain of sides, no boundary, Lemma 9.4, the theorems), `NestStep` 273 (one level up at
  tile level), `NewWalk` 227, `Linked` 218 (symmetry).
- Stage 6, Theorem A for chains: `ProofChain` 717 (with the nest as a chain that covers).
- Stage 7, the exact counts and the Grandparent Lemma: `ProofExact` 420, `Turn` 513, `ProofGrand` 480 (with the
  Signature Theorem as a claim).
- The statement file 476; tests 301; `Axioms.lean` 115.

## Assessment

Stages 4 to 7 prove Theorems A and B in the combinatorial form of the statement file, with the Signature Theorem, the
exact merging counts and the Grandparent Lemma, checked by Lean's kernel against `SignatureTheorem`, `TheoremA`,
`TheoremB`, `TheoremB_sharp`, `NestModel`, `TheoremB_strand`, `ChainModel`, `TheoremA_strand`, `NestCovers`,
`TheoremB_exact` and `Grandparent` as written there.
What stands between them and the paper's theorems is assumption (M), in its three parts, with the geometric facts about
the plane listed above, all stated in `Statement.lean`.
