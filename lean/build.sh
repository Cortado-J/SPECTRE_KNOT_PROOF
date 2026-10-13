#!/usr/bin/env bash
# Build the Lean pilot and check that the main theorems use no axioms beyond Lean's standard three
# (propext, Classical.choice, Quot.sound), that the sources contain no sorry, admit or native_decide, and that every
# theorem and every `have` carries a comment (tools/check_comments.py).
#
#   ./build.sh            build everything (needs elan and the toolchain in lean-toolchain)
#   ./build.sh --data     first regenerate the data files from paper/code (needs python3 and node)
#   ./build.sh --slow     also run the slower tests (TestsSlow.lean, about 2 minutes)
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
if [ "${1:-}" = "--data" ]; then
  python3 tools/gen_pattern.py
  node tools/gen_skeletons.js
  python3 tools/gen_clusters.py
fi
python3 tools/no_sorry.py || { echo "FAIL: sorry, admit or native_decide in the sources"; exit 1; }
python3 tools/check_comments.py || { echo "FAIL: a theorem or have without a comment"; exit 1; }
t0=$SECONDS
lake build 2>&1 | tee .lake-build.log | grep -vE '^(✔|⣿|info: )' || true
grep -q 'Build completed successfully' .lake-build.log || { echo "FAIL: build"; exit 1; }
if [ "${1:-}" = "--slow" ]; then lake build TestsSlow 2>&1 | grep -vE '^(✔|⣿|info: )' || true; lake build TestsSlow >/dev/null 2>&1 || { echo "FAIL: slow tests"; exit 1; }; echo "slow tests passed"; fi
# Axioms.lean prints one line per theorem: "'name' depends on axioms: [...]" (or "does not depend on any axioms").
axioms=$(grep -oE "depends on axioms: \[[^]]*\]" .lake-build.log | sed 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/ //g' | sort -u)
bad=$(printf '%s\n' "$axioms" | grep -vxE 'propext|Classical\.choice|Quot\.sound|' || true)
if [ -n "$bad" ]; then echo "FAIL: non-standard axioms: $bad"; exit 1; fi
n=$(grep -cE "depends on axioms|does not depend on any axioms" .lake-build.log || true)
echo "OK: build in $((SECONDS - t0)) s; $n theorems checked, axioms used: $(printf '%s ' $axioms)"
