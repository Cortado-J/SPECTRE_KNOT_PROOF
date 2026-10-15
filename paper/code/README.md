# The Spectre Knot: programs for the proof

This folder holds every program used in the paper *The Spectre Knot: one endless strand on an aperiodic monotile*
(`../spectre_knot.pdf`), with the logs of a full run (`logs/run_all.out`, from `./run_all.sh --all`). A17 and A18
need the spectre paper's PDF, which is not included; they were run separately with it on 12 Oct 2026 (its SHA-256 is
checked and printed in the logs) and gave the same logs as before. A22 downloads Kaplan's implementation of the
spectre's substitution (`spectre.js`, the program of the interactive application on the spectre authors' page,
https://cs.uwaterloo.ca/~csk/spectre/), which is published without a licence and so is not included; it was run
separately on 15 Oct 2026 (the file's SHA-256 is checked and printed in the log). Apart from these two inputs it is
self-contained: it reads nothing outside this folder.

## Running

```
./run_all.sh          # stage A: the computations the proof depends on, and quick corroboration (about 12 minutes on 4 cores)
./run_all.sh --all    # stage A and stage B: corroboration up to level 9 (about 1 hour; node heap capped at 6.5 GB)
./run_all.sh --b      # stage B only (needs the data files written by stage A)
./run_all.sh --kaplan # also A22: comparison with Kaplan's implementation of the substitution (downloads it)
SMKGS_PDF=/path/to/spectre-paper.pdf ./run_all.sh   # also A17-A18: comparison with Figs. 4.1 and 5.1 of the spectre paper
```

Each step writes one log in `logs/` and prints its last line. A step that fails stops the run with a non-zero
exit status. Requirements:

- node 18 or later (tested with v22);
- python 3 with `numpy` and `scipy` (used only by `hierarchy/certify.py`), `sympy` (`hierarchy/letters.py`),
  `matplotlib` (A16) and `pillow` (A17, A18); `pdftoppm` (poppler) for A17 and A18;
- `exact/exact.py` needs only the Python standard library; A22 needs node, the Python standard library and the
  internet.

## Two separate implementations (both written by the AI system)

- **JavaScript** (`core/` and most of `hierarchy/`): builds the supertiles with the key-point construction of the
  spectre paper (App. A) in floating point. Points are identified by rounding to 1/100 (`core/reduce.js`,
  `core/hier2.js`) or 1/1000 (`core/hier.js`). The rounding error is not bounded; the results are corroborated:
  `crosscheck/overlap.js` (same construction, snapping to 1/1000) finds distinct vertices at least 0.89 apart and
  identified points within 4e-12 of each other up to level 7; up to level 9 every rim has exactly E_m edges and every
  rim vertex has degree 2 (`core/hier2.js` stops otherwise); and every geometric computation the proof uses is
  repeated in exact arithmetic by `exact/exact.py`.
- **Python** (`exact/exact.py`): written separately and sharing no code with the JavaScript. Every vertex is an
  element of Z[zeta], zeta = e^(i pi/6), stored as four integers, so all identifications are exact. It recomputes
  the base data (levels 1 to 4) and the nest merging for bases 1 to 3, and compares its results with the
  JavaScript output.

A third implementation of the key-point construction, by Craig S. Kaplan, one of the spectre's authors, is the
program of their interactive application (`spectre.js`, JavaScript, floating point). It is the only program in these
checks that the AI system did not write. A22 (`crosscheck/kaplan_compare.py`, written by the AI system) runs it and
finds the same Table 1 and, tile for tile, the same supertiles as `exact/exact.py` up to level 4; and, from its tiles
alone, the level-1 vertices, side lengths and Sigma offset of `hierarchy/combin_8.json` and `letters.json`.

The two computations on compositions that the proof uses (Computations 7.3 and 8.6) need no geometry: they use only
the tables and the level-1 side lengths, with integers. `hierarchy/compositions.py` (Python, standard library only)
does them, and the Lean formalisation (`lean/` in the repository) does them again in its kernel; the two were written
separately (both by the AI system).

In the comments and printed output of the JavaScript programs, "exact" usually means the direct composition of
the actual tiles (floating point, with rounded keys), as opposed to the reduced walk. Exact arithmetic in the strict
sense is used only by `exact/exact.py`, the skeleton walks and symbolic run (integers) and the certificates.

The symbolic certificate for the merging (`hierarchy/certnest.js`) is checked twice: once by linear programming
proposals verified in exact rationals (`certify.py`), and once by the Fibonacci closed form with integers only
(`certify_fib.py`).

## Which script checks which statement

Numbering as in the paper.

| statement | what is computed | script | log |
|---|---|---|---|
| Def. 3.1, Lemma 4.4 | the tile's 14 pieces = 12 hooks + crossover at v0 v1; the Mystic has the signature | `core/tile.js`, `exact/exact.py` | A01, A13 |
| §3.2 (drawing) | every shared tile edge glues e_i to e_j with i+j odd, opposite directions, levels 1-4 | `exact/exact.py` | A13 |
| Thm 2.1(b), Prop. 2.4 | the six vertices of every kind (points where three supertiles meet): observed at levels 1-4, and at levels 5-6 to check the propagated ones | `hierarchy/vertices.js`, `exact/exact.py` | A02, A03, A13 |
| Prop. 2.4, Rem. 2.5 | the composition pattern C of m -> m+1, m = 1..7, all identical (exact for m <= 3); vertices propagated for m >= 5 and checked against observation at 5-6 | `hierarchy/combin.js`, `exact/exact.py` | A04, A13 |
| Prop. 2.4 (base of (*)) | the level-1 supertiles as hat/turtle clusters (odd edges lengthened to sqrt 3), fitted to a 300-dpi render of the spectre paper's Fig. 4.1: six dots found per cluster, proper similarity with residual < 1% of an edge (other matchings and other kinds >= 40 times worse), rim on the printed outline, first Mystic tile on the lighter shading, labels (read by hand, `crosscheck/fig41_labels.json`) = Table 4. Needs the spectre paper's PDF | `crosscheck/fig41_compare.py` | A17 |
| Prop. 2.4 (base of (*)) | the same clusters drawn for comparison by eye | `crosscheck/fig41_render.py` | `logs/A16_fig41_render.pdf` |
| Table 1, Prop. 2.4 (base of (*)) | Table 1 and every tile of every supertile, levels 0-4 (in order, with the kinds of the tiles), against Kaplan's implementation of the substitution (`spectre.js` from the spectre authors' page, SHA-256 checked, run in a context of its own with no access to node); from its tiles alone, the six vertices of every kind at level 1 (points where three level-1 supertiles meet), the side lengths l_1 and the Sigma offset d_1, against `hierarchy/combin_8.json` and `letters.json`; two altered copies (two children of Delta exchanged; one placement rule changed) rejected. Downloads `spectre.js` | `crosscheck/kaplan_compare.py`, `crosscheck/kaplan_run.js` | A22 |
| Prop. 2.4, Rem. 2.5 | C agrees with a hand encoding of the spectre paper's Fig. 5.1, all nine kinds, including the parent side labels (dictionary (*) in the proof of Prop. 2.4) | `crosscheck/fig51_compare.py` (encoding `crosscheck/fig51_encoding.json`) | A06 |
| Rem. 2.5 | two deliberately corrupted encodings (`crosscheck/neg_swap/`, `crosscheck/neg_label/`) are rejected | `crosscheck/fig51_compare.py` | A06b |
| Rem. 2.5 | the vertex dots and Gamma centres used by `fig51_compare.py` re-found on a 400-dpi render of Fig. 5.1 (within 2 px). Needs the spectre paper's PDF | `crosscheck/fig51_raster.py` | A18 |
| Rem. 2.5 | tiles of every supertile, levels 1-7, have disjoint interiors and fill the rim | `crosscheck/overlap.js` (levels 1-5; levels 6-7 take ~15 min) | B08, B13 |
| Prop. 6.1, 6.2, Cor. 6.3, Lemma 6.4 | side lengths by letter at levels 1-8, the recurrence, the Fibonacci closed forms, parities, the Sigma offset | `hierarchy/recur.js`, `hierarchy/letters.py` | A05, A07 |
| Comp. 7.3 | the 18 compositions C_T(l_1, d_1, ±1), built from Tables 1-3 and l_1, d_1 alone (no geometry, no skeleton): every port followed, the signature checked as worded; negative control (each child's corners two apart: all 18 fail) | `hierarchy/compositions.py` (also the Lean kernel: `lean/SpectreKnot/CompFull.lean`) | A19 |
| Comp. 7.5 | signature of the level-1 supertiles, exact (also levels 2-3 and 4, corroboration); the same in floating point | `exact/exact.py`, `hierarchy/checks.js` | A13, A08 |
| Comp. 9.2 | the junction map (Table 6) in C_Delta(l_1, d_1, ±1): every port of child 1 followed to its junction; negative control (junctions 12 and 16 exchanged: both signs fail) | `hierarchy/compositions.py` (also `lean/SpectreKnot/StepMap.lean`) | A19 |
| Rem. 7.8 (1), Rem. 9.5 (2) | corroboration: the compositions and the junction map at (l_m, d_m, ±1) for m = 2..4; every single move from (l_1, d_1), with both signs, keeps the signature (1,792 moves) and, on Delta with any cut on child 1 two edges clear of the ends of its side, the junction map (190 moves) | `hierarchy/compositions.py` | A19 |
| Rem. 7.8 (1) | corroboration: the moves that the proof of Lemma 7.2 chooses, followed from (l_2, d_2) and (l_3, d_3) back to (l_1, d_1) for every kind, each checked to be an allowed move between admissible pairs; from (l_2, d_2) every composition on the way checked to have the signature (both signs) and, for Delta, the junction map | `crosscheck/chain_check.py` | A20 |
| Rem. 9.5 (2) | corroboration: Table 6 on the actual blocks N_1 ⊂ N_2, N_2 ⊂ N_3, N_3 ⊂ N_4, built from the tiles in exact arithmetic by `exact/exact.py`; negative control (junctions 12 and 16 exchanged) | `crosscheck/junction_actual.py` | A21 |
| Rem. 7.8 (3) | corroboration: the 18 skeleton walks S_T(l_1, d_1, ±1); the parity lemma for skeletons with other lengths | `hierarchy/induction.js` | A09 |
| Rem. 7.8 (3) | corroboration: the same 18 skeletons equal the skeletons of the actual supertiles at levels 2-9 (the encoding records slightly more than Def. 5.3, e.g. rim-run parities) | `hierarchy/induction.js 9` | B15 |
| Prop. 5.4 (check) | reduced walk = exact composition at all 1,424 parent ports, levels 1-8 | `hierarchy/checks.js` | B02 |
| Rem. 9.5 (3) | corroboration: label states and their step, implemented numerically in `core/nest.js` and symbolically in `hierarchy/certnest.js` (function `runSym`) | `core/nest.js`, `hierarchy/certnest.js` | A14, A10 |
| Rem. 9.5 (3) | corroboration: symbolic label computation: 1,068 obligations (even b) and 1,038 (odd b), 1,407 distinct; 1,001 + 979 certified directly | `hierarchy/certnest.js` | A10 |
| Rem. 9.5 (3) | corroboration: the 67 + 59 remaining obligations (118 distinct), by the Fibonacci closed form / by Krylov-space certificates | `hierarchy/certify_fib.py`, `hierarchy/certify.py` | A12, A11 |
| Table 5, Rem. 9.5 (1) | b = 1, 2, 3: every ribbon followed in exact arithmetic to level 7; label computation for b = 1, 2, 3 | `exact/exact.py`, `core/nest.js` | A13, A14 |
| Table 5 | exact strand following through the nest, b = 1..6, to level 9 (b = 1..3 also in exact arithmetic) | `core/hier2.js`, `exact/exact.py` | B05, A13 |
| corroboration | signature, no loops and skeleton period 2 at levels 1-9; skeletons = F(C, parities, omega), built with stand-in lengths of the right parities (not literally S_T(l_1, d_1)) | `core/reduce.js`, `hierarchy/synth.js`, `hierarchy/synthown.js` | B01, B03, B04 |
| corroboration | label inputs rebuilt from (C, parities, omega) equal the exact ones, b = 1..6, to level 9 | `hierarchy/synthnest.js` | B07 |
| §3 (drawing) | the drawn ribbons (hand design in `drawing/engine.js`) realise the port pairing, levels 1-3 | `drawing/checkmodel.js` | B09 |
| Rem. 3.6 | the drawn pieces: containment, the single (transversal) crossing, angles of 45 degrees at the edges | `drawing/drawcheck.py` | B14 |
| App. A (sizes) | tile counts, rim lengths and shortest sides at levels 1-9 from Table 1 and the Fibonacci forms | `hierarchy/sizes.py` | A15 |
| illustration | N_b shares no vertex with the rim of N_{b+2} (b <= 5); edges of N_b on later rims; strands through N_1's tiles | `drawing/nestgap.js`, `nestrim.js`, `onetile.js` | B10-B12 |

## Files

- `core/hier.js`: Tile(1,1), the design's tile tangle, the key-point substitution of the spectre paper (App. A), direct port composition.
- `core/reduce.js`: typed-array composition; extracts the skeleton (marks, runs, partners, parities); the reduced
  walk `rcompose`; canonical encodings.
- `core/nest.js`: label propagation through the nest using the reduced walk (paper Remark 9.5).
- `core/hier2.js`: exact strand following with labels for several nest bases at once.
- `core/tile.js`: prints and checks the tile's pairing.
- `hierarchy/lib.js`: shared loader. `vertices.js`, `combin.js`, `recur.js`: vertices, the pattern C, the matrix M.
- `hierarchy/compositions.py`: the compositions C_T(L, d, omega) of Section 7.1 built from the tables alone and
  followed port by port: Computation 7.3, Computation 9.2 (the junction map), and their corroboration.
- `hierarchy/synth.js`: the skeleton S_T(lambda, d, omega) built from C and lengths alone (function `F`).
- `hierarchy/induction.js`: the 18 skeleton walks of Remark 7.8.
- `hierarchy/synthown.js`, `synthnest.js`: two-level data and label inputs rebuilt from (C, parities, omega).
- `hierarchy/certnest.js`, `certify.py`, `certify_fib.py`: the symbolic label computation and its certificates
  (Remark 9.5).
- `hierarchy/letters.py`: letters, recurrence, closed forms; writes `letters.json`.
- `hierarchy/checks.js`: crossover shape and reduced-versus-exact pairing at every level.
- `hierarchy/chains_label.js`: an experiment, not used in any proof: the label computation of Remark 9.5 run along an
  arbitrary chain of supertiles instead of the nest. Agrees with exact strand following on 60 chains up to level 8.
  It gives the evidence of Remark 10.1 (three strands along the chain Θ child 2 of Γ, Γ child 7 of Θ).
- `experiments/three_exact.py`, `experiments/three_label.js` (logs `three_exact.log`, `three_label.log`): the computations
  quoted in Remark 10.1, exact to level 8 and by labels to level 20. Experiments only; no proof uses them, and
  `run_all.sh` does not run them.
- `experiments/random_chains.js` (logs `random_chains_b1.log` to `_b3.log`, from `node random_chains.js <b> 30000 <b>`):
  the label computation along 30,000 chains chosen at random for each b = 1, 2, 3, to level 20 (about 10 minutes each);
  1 + 0 + 4 = 5 of the 90,000 do not reach a single arc by level 20 (Remark 10.1).
- `experiments/chains_compare.py` (log `chains_compare.log`): `hierarchy/chains_label.js` against exact strand following
  (`exact/exact.py`) on 60 chains chosen at random, to level 8 (about an hour, 10 GB). Experiments only, not run by
  `run_all.sh`.
- `exact/exact.py`: the second, separate exact implementation.
- `crosscheck/chain_check.py`, `crosscheck/junction_actual.py`: checks added by the AI review pass of 11 Oct 2026 (Remarks 7.8 and 8.9).
- `crosscheck/` (called `referee/` before 12 Oct 2026; second checks, all written by the AI): comparison with Fig. 5.1 (`fig51_compare.py` with the hand encoding `fig51_encoding.json` and
  `gamma_centres.json`; `blobs.py` and `anchor.py` first located the vertex dots on a 400-dpi render of the figure and are
  kept for the record; `fig51_raster.py` redoes this from the PDF), comparison with Fig. 4.1 (`fig41_compare.py` with
  the hand reading `fig41_labels.json`; `fig41_render.py` draws the clusters), overlap check (`overlap.js`), comparison
  with Kaplan's implementation of the substitution (`kaplan_compare.py`, which downloads it, and `kaplan_run.js`, which
  runs it).
- `drawing/`: the drawing engine with the hand-drawn design (`engine.js`) and checks that relate the drawing to the
  combinatorial model.
- Generated data (rewritten by stage A): `hierarchy/vertices_*.json`, `combin_8.json`, `M.json`, `letters.json`,
  `certnest_deferred.json`, `exact/exact_C.json`; stage B writes `hierarchy/F_9.json`.

## Provenance

These are frozen copies of the scripts in the development repository, with paths adjusted and some comments brought up to date (no change to the computations), plus `core/tile.js`, `hierarchy/induction.js`, `hierarchy/letters.py`,
`hierarchy/certify_fib.py` and `exact/exact.py`, which were written for the paper. The design is 0.1:01 (`fan21`
grid, spoke digits `01222222222222`). In the programs the sign omega_m of the paper is called `beta`.
