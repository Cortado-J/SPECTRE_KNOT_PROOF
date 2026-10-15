#!/usr/bin/env bash
# Re-run every computation used in the paper "The Spectre Knot". Logs go to logs/.
#
#   ./run_all.sh          stage A only: the computations the proof depends on, and quick corroboration (about 12 minutes
#                         on 4 cores)
#   ./run_all.sh --all    stage A and stage B (corroboration up to level 9; about 1 hour; node heap capped at 6.5 GB)
#   ./run_all.sh --b      stage B only (needs the data files written by stage A)
#   ./run_all.sh --kaplan also A22 (with stage A): downloads Kaplan's implementation of the substitution and compares
#
# A17-A18 compare with the figures of the spectre paper and run only if SMKGS_PDF points to its PDF. A22 needs the
# internet: its input, from the spectre authors' page, has no licence and is not included.
# Requirements: node >= 18; python3 with numpy and scipy (certify.py; scipy only proposes certificates, which are then
# checked in exact rational arithmetic), sympy, matplotlib (A16) and pillow; pdftoppm for A17-A18.
# See README.md for what each step establishes.
set -euo pipefail
cd "$(dirname "$0")"; ROOT=$PWD
A=1; B=0; K=0
for x in "$@"; do case $x in --all) B=1;; --b) A=0; B=1;; --kaplan) K=1;; *) echo "unknown option $x"; exit 2;; esac; done
BIG="--max-old-space-size=6500"
DIG=01222222222222
mkdir -p logs
run() { local log=$1; shift; printf '\n== %s  (> logs/%s)\n' "$*" "$log"; local t0=$SECONDS; "$@" > "logs/$log" 2>&1 || { echo "FAILED: $*  (see logs/$log)"; exit 1; }; echo "   $(tail -1 logs/$log)   [$((SECONDS - t0)) s]"; }

if [ $A = 1 ]; then
  echo "### Stage A: the computations the proof depends on (A01-A07, A13, A15-A16, A19), and quick corroboration"
  run A01_tile.log            node core/tile.js
  run A02_vertices_4_3.log    node $BIG hierarchy/vertices.js 4 3
  run A03_vertices_6_2.log    node $BIG hierarchy/vertices.js 6 2
  run A04_combin.log          node $BIG hierarchy/combin.js 8 hierarchy/vertices_4_3.json hierarchy/vertices_6_2.json
  run A05_recur.log           node hierarchy/recur.js hierarchy/combin_8.json
  run A06_fig51.log           python3 crosscheck/fig51_compare.py
  run A06b_fig51_negative.log bash -c 'for d in crosscheck/neg_swap crosscheck/neg_label; do echo "== negative control $d"; python3 crosscheck/fig51_compare.py $d | sed -n "/PROBLEMS/,+2p"; python3 crosscheck/fig51_compare.py $d | grep -q "^PROBLEMS" || { echo "NOT REJECTED: $d"; exit 1; }; done; echo "BOTH CORRUPTED ENCODINGS REJECTED"'
  run A07_letters.log         python3 hierarchy/letters.py
  run A13_exact.log           python3 exact/exact.py 4 --nest 1,2,3 --nestL 7
  run A19_compositions.log    python3 hierarchy/compositions.py 4
  run A15_sizes.log           python3 hierarchy/sizes.py
  run A16_fig41_render.log    python3 crosscheck/fig41_render.py logs/A16_fig41_render.pdf
  # Quick corroboration: A08 re-checks Computation 7.5 in floating point (a second program); the others are the
  # routes of the paper's Remarks 7.8 and 8.9, which the proof does not use since the paper's revision of
  # 11 October 2026. They are cheap, so they run here too.
  run A08_base_L3.log         env FAM=fan21 node $BIG hierarchy/checks.js $DIG 3
  run A09_induction.log       node hierarchy/induction.js
  run A10_certnest.log        node hierarchy/certnest.js 8
  run A11_certify.log         python3 hierarchy/certify.py
  run A12_certify_fib.log     python3 hierarchy/certify_fib.py
  run A14_nest_L7.log         env FAM=fan21 node $BIG core/nest.js $DIG 7 1,2,3
  # Checks from the AI review pass of 11 Oct 2026: the moves of Lemma 7.2 followed back from levels 2 and 3, and Table 6 on
  # the actual blocks N_1..N_4 (exact arithmetic).
  run A20_chain_check.log     python3 crosscheck/chain_check.py
  run A21_junction_actual.log python3 crosscheck/junction_actual.py
  # A17-A18 need the PDF of the spectre paper (not included): SMKGS_PDF=/path/to/paper.pdf ./run_all.sh
  if [ -n "${SMKGS_PDF:-}" ]; then
    run A17_fig41_compare.log  python3 crosscheck/fig41_compare.py "$SMKGS_PDF"
    run A18_fig51_raster.log   python3 crosscheck/fig51_raster.py "$SMKGS_PDF"
  else
    echo; echo "== A17, A18 skipped (set SMKGS_PDF to the spectre paper's PDF to compare with its Figs. 4.1 and 5.1)"
  fi
  # A22 downloads Kaplan's implementation of the substitution from the spectre authors' page: ./run_all.sh --kaplan
  if [ $K = 1 ]; then
    run A22_kaplan_compare.log python3 crosscheck/kaplan_compare.py
  else
    echo; echo "== A22 skipped (run with --kaplan to download Kaplan's implementation of the substitution and compare)"
  fi
fi

if [ $B = 1 ]; then
  echo "### Stage B: corroboration (direct composition in floating point, up to level 9)"
  run B01_reduce_L9.log       env FAM=fan21 node $BIG core/reduce.js $DIG 9
  run B02_checks_L8.log       env FAM=fan21 node $BIG hierarchy/checks.js $DIG 8
  run B03_synth_L9.log        node $BIG hierarchy/synth.js hierarchy/combin_8.json 9
  run B04_synthown_L9.log     node $BIG hierarchy/synthown.js 9
  run B05_hier2_L9.log        node $BIG core/hier2.js fan21 $DIG 9 1,2,3,4,5,6
  run B06_nest_L9.log         env FAM=fan21 node $BIG core/nest.js $DIG 9 1,2,3,4,5,6
  run B07_synthnest_L9.log    node $BIG hierarchy/synthnest.js 9 1,2,3,4,5,6 u8:4,u10:6,u20:8,u100:10,l1,l2,l3,l4,l1+2l2,3l1+2l3,l1+l2+l4,l2+l3+l5
  run B08_overlap_L5.log      node $BIG crosscheck/overlap.js 5
  run B09_checkmodel_L3.log   bash -c "cd drawing && node $BIG checkmodel.js 3"
  run B10_nestgap_L7.log      bash -c "cd drawing && node $BIG nestgap.js 7"
  run B11_nestrim_L7.log      bash -c "cd drawing && node $BIG nestrim.js fan21 $DIG 7"
  run B12_onetile_L5.log      bash -c "cd drawing && node $BIG onetile.js 5"
  run B13_overlap_L6_7.log    node $BIG crosscheck/overlap.js 7 all 6
  run B14_drawcheck.log       python3 drawing/drawcheck.py
  run B15_induction_L9.log    node $BIG hierarchy/induction.js 9
fi
echo; echo "done in $SECONDS s; logs in $ROOT/logs"
