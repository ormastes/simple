#!/usr/bin/env bash
# verify_ac6.sh — AC-6: bin/simple test shows no new failures vs test_baseline.txt.
# Runs full test suite, diffs FAILED lines against baseline.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

BASELINE="$REPO_ROOT/.sstack/fix-warning-and-allow/test_baseline.txt"
CURRENT="$REPO_ROOT/.sstack/fix-warning-and-allow/test_current.txt"

if [ ! -f "$BASELINE" ]; then
  echo "ERROR: Baseline not found at $BASELINE — run capture_baseline.sh first."
  exit 2
fi

echo "=== AC-6: No new test failures vs baseline ==="
bin/simple test 2>&1 | tee "$CURRENT"

# Extract FAILED lines from each
BASE_FAILS=$(grep -E 'FAILED|FAIL:' "$BASELINE" | sort || true)
CURR_FAILS=$(grep -E 'FAILED|FAIL:' "$CURRENT" | sort || true)

NEW_FAILS=$(comm -13 <(echo "$BASE_FAILS") <(echo "$CURR_FAILS") || true)

if [ -n "$NEW_FAILS" ]; then
  echo ""
  echo "FAIL: AC-6 — new test failures vs baseline:"
  echo "$NEW_FAILS"
  exit 1
fi

FIXED=$(comm -23 <(echo "$BASE_FAILS") <(echo "$CURR_FAILS") | wc -l || true)
echo ""
echo "PASS: AC-6 — no new failures. Fixed: $FIXED previously-failing test(s)."
