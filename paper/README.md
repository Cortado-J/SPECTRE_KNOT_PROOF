# The Spectre Knot: the paper

*The Spectre Knot: one endless strand on an aperiodic monotile*, by Justin Roughley.

| path | what |
|---|---|
| `spectre_knot.pdf` | the paper (built) |
| `tex/spectre_knot.tex`, `tex/refs.bib` | LaTeX source (amsart) and bibliography |
| `tex/figs/` | figures (vector PDF), made by `figures/make_figs.py` |
| `figures/` | figure scripts. The geometry comes from `code/exact/exact.py`; the ribbon shapes come from `figures/data/hand01b_norm.json`, a copy of the hand-drawn design |
| `code/` | **every program used in the proof**, with logs of a full run; see `code/README.md` |
| `../lean/` | the Lean 4 formalisation of the combinatorial part of the proof; see `lean/README.md` |
| `build.sh` | rebuilds the figures and the PDF |

## Rebuilding

```
./build.sh               # figures and PDF (about 2 minutes)
./build.sh --tex         # PDF only
code/run_all.sh          # re-run the proof's computations (about 12 minutes on 4 cores)
code/run_all.sh --all    # also the corroboration to level 9 (about 1 hour; node heap capped at 6.5 GB)
```

The paper uses TeX Live (amsart, newpx, TikZ, cleveref) and Python 3 with matplotlib for the figures.

## Status

How the proof, the programs and the text were made, and what has been checked: the paper's §1, *Use of AI and
verification status*.
