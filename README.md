# The Spectre Knot: the proof

The proof that the Spectre Knot, a Celtic-knot ribbon drawn on every tile of the spectre aperiodic monotile, joins into
a single endless strand in the nest tiling (the tiling grown outwards from a single tile, each block sitting in the same
place, child number 1, inside the next), and that in every spectre tiling whose supertiles fill the plane no strand
closes into a loop.

- `paper/`: the write-up of the proof (`spectre_knot.pdf`), its LaTeX, and in `paper/code/` every program the proof
  uses, with logs of a full run.
- `lean/`: the Lean 4 formalisation of the combinatorial part of the proof. Start with
  `lean/SpectreKnot/Statement.lean`; `lean/README.md` maps the paper to the Lean and says what is not formalised.
- `proofmap/`: generates the proof's website: every numbered result of the paper with its statement and proof, what it
  rests on and its Lean, the results as a graph, and `Statement.lean` line by line.

The pictures and the ideas, for everyone: [The Spectre Knot](https://cortado-j.github.io/SPECTRE_KNOT/).

**Made with AI.** An experiment in using AI (Claude, by Anthropic) for mathematical exploration, by Justin Roughley and
the AI working together. How: the public site's Made with AI page, https://cortado-j.github.io/SPECTRE_KNOT/made.html.
What has been checked, and what has not: https://cortado-j.github.io/SPECTRE_KNOT_PROOF/#checked. The paper has not
been peer reviewed.

The spectre was discovered in 2023 by David Smith, Joseph Samuel Myers, Craig S. Kaplan and Chaim Goodman‑Strauss
(*A chiral aperiodic monotile*, Combinatorial Theory 4(2), 2024). The knot: Justin Roughley came up with the original
idea of looking for a mono-stranded aperiodic knot, and then used AI to search for it (2026).

## Building

```
python3 proofmap/build.py             # the website into out/site/ (open out/site/index.html)
( cd lean && ./build.sh )             # the Lean, with the axiom check (needs elan)
( cd paper/code && ./run_all.sh )     # the proof's computations (about 12 minutes)
```

Licence: code MIT (`LICENSE`); the paper, text and pictures CC BY 4.0 (`LICENSE-CONTENT.md`).
