#!/usr/bin/env bash
# capture_baseline.sh — Record baselines before any fix work begins.
# Run once from repo root. Outputs land in .sstack/fix-warning-and-allow/.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
OUT_DIR="$REPO_ROOT/.sstack/fix-warning-and-allow"

cd "$REPO_ROOT"

echo "=== Capturing test baseline ==="
bin/simple test 2>&1 | tee "$OUT_DIR/test_baseline.txt"

echo ""
echo "=== Capturing @allow count baseline ==="
{
  echo "# @allow baseline captured $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "# Format: COUNT CATEGORY"
  echo ""
  echo "## Total true @allow annotations in owned .spl (excludes vendor/*)"
  grep -rn '@allow(' \
    --include='*.spl' \
    src/lib src/app src/compiler src/compiler_rust/lib \
    --exclude-dir='vendor' \
    | grep -v '// *@allow' \
    | grep -v '^\s*//' \
    | sed 's/.*@allow(\([^)]*\)).*/\1/' \
    | sort | uniq -c | sort -rn
} | tee "$OUT_DIR/allow_baseline.txt"

echo ""
echo "=== Capturing clippy baseline ==="
bin/simple build lint 2>&1 | tee "$OUT_DIR/clippy_baseline.txt"

echo ""
echo "=== Baselines captured to $OUT_DIR ==="
echo "  test_baseline.txt"
echo "  allow_baseline.txt"
echo "  clippy_baseline.txt"
