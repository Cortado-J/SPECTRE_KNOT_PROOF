#!/usr/bin/env bash
# Regenerate the Lean's data files (SpectreKnot/Data/) from paper/code and fail unless they are exactly the committed
# ones, so that the Lean never proves things about tables the paper no longer uses. Run by CI (data.yml) whenever
# paper/code/ or the data change; about a minute (exact.py's exact arithmetic). Needs python3 and node.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 tools/gen_pattern.py >/dev/null
node tools/gen_skeletons.js >/dev/null
python3 tools/gen_clusters.py >/dev/null
git diff --exit-code --stat -- SpectreKnot/Data ||
  { echo "FAIL: the data files are not what paper/code generates. Run ./build.sh --data and commit them."; exit 1; }
echo "OK: the data files are what paper/code generates"
