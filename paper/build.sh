#!/usr/bin/env bash
# Build the paper: figures (from the exact geometry in code/exact/exact.py) and the PDF.
#   ./build.sh            figures + PDF
#   ./build.sh --tex      PDF only (reuse tex/figs/*.pdf)
# Needs python3 with matplotlib, a TeX installation with latexmk, pdflatex, bibtex, newpx, tikz.
set -euo pipefail
cd "$(dirname "$0")"
if [ "${1:-}" != "--tex" ]; then
  (cd figures && python3 make_figs.py)
fi
(cd tex && latexmk -pdf -interaction=nonstopmode -halt-on-error spectre_knot.tex)
cp tex/spectre_knot.pdf spectre_knot.pdf
echo "wrote paper/spectre_knot.pdf"
