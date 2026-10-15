#!/usr/bin/env bash
# Check with leanprover's comparator (https://github.com/leanprover/comparator) that the main theorems prove exactly
# the claims of Statement.lean, use only Lean's standard axioms, and are accepted by the kernel. comparator compares
# each theorem with a challenge file that states its claim with `sorry` and imports only Statement.lean (and so only
# the files that fix what is proved). This script writes that file, from the pins at the end of Axioms.lean, into a
# temporary copy of lean/, so that no `sorry` enters the sources, and runs comparator there.
#
#   tools/comparator.sh      about 4 minutes once the project is built (it reuses lean/.lake)
#
# Needs git and elan with this project's toolchain. The first run downloads comparator (its tag for Lean 4.34) and
# lean4export and builds them with this project's Lean, into $COMPARATOR_DIR (default ~/.cache/spectre-knot-comparator).
# comparator runs the builds in landrun, a sandbox meant for proofs from an untrusted source. Where landrun is not
# installed (or $COMPARATOR_LANDRUN not set), this uses comparator's own development shim, which runs them unsandboxed:
# enough for this repository's own proofs, built here anyway.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
DIR=${COMPARATOR_DIR:-$HOME/.cache/spectre-knot-comparator}
TAG=v4.34.0
if [ ! -x "$DIR/.lake/build/bin/comparator" ]; then
  rm -rf "$DIR"
  git clone -q --depth 1 --branch "$TAG" https://github.com/leanprover/comparator "$DIR"
  cp lean-toolchain "$DIR/lean-toolchain"
  (cd "$DIR" && lake build lean4export comparator >/dev/null)
fi
LANDRUN=${COMPARATOR_LANDRUN:-$(command -v landrun || echo "$DIR/scripts/fake-landrun.sh")}
case "$LANDRUN" in */fake-landrun.sh) echo "landrun not found: comparator's shim runs the builds unsandboxed" ;; esac

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cp -a . "$WORK/lean"
cd "$WORK/lean"
# The pins `example : Claim := proof` at the end of Axioms.lean name each main theorem and its claim.
pins=$(sed -nE 's/^example : ([A-Za-z0-9_.]+) := ([A-Za-z0-9_.]+)$/\2 \1/p' Axioms.lean)
[ -n "$pins" ] || { echo "FAIL: no pins found in Axioms.lean"; exit 1; }
{
  echo 'import SpectreKnot.Statement'
  echo
  while read -r proof claim; do echo "theorem $proof : $claim := sorry"; done <<< "$pins"
} > Challenge.lean
printf '\n[[lean_lib]]\nname = "Challenge"\n' >> lakefile.toml
names=$(while read -r proof claim; do printf '"%s",' "$proof"; done <<< "$pins")
cat > comparator.json <<EOF
{"challenge_module": "Challenge", "solution_module": "SpectreKnot", "theorem_names": [${names%,}],
 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
EOF
echo "comparator: $(wc -l <<< "$pins") theorems against the claims of Statement.lean"
COMPARATOR_LANDRUN="$LANDRUN" COMPARATOR_LEAN4EXPORT="$DIR/.lake/packages/lean4export/.lake/build/bin/lean4export" \
  lake env "$DIR/.lake/build/bin/comparator" comparator.json 2>&1 |
  grep -E '^(Building |Running |Lean default kernel|Your solution|uncaught exception|error)'
