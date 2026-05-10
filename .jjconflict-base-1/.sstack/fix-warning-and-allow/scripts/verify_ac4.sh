#!/usr/bin/env bash
# verify_ac4.sh — AC-4: No cover-up fixes.
# Checks: no new skip() calls vs baseline git HEAD~,
# no TODO→NOTE conversions, no lint-rule deletions/disablements.
# Uses git diff against baseline commit stored in allow_baseline.txt or origin/main.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== AC-4: No cover-up fixes ==="

# Determine baseline ref: use origin/main if available, else HEAD~1
BASE_REF="origin/main"
if ! git rev-parse --verify "$BASE_REF" >/dev/null 2>&1; then
  BASE_REF="HEAD~1"
fi
echo "Comparing against: $BASE_REF"

DIFF=$(git diff "$BASE_REF" -- src/lib src/app src/compiler src/compiler_rust 2>/dev/null || true)

FAIL=0

# 1. No new skip() calls added
NEW_SKIP=$(echo "$DIFF" | grep -E '^\+[^+].*\bskip\(' | grep -v '^\+\s*//' || true)
if [ -n "$NEW_SKIP" ]; then
  echo "FAIL: New skip() calls added:"
  echo "$NEW_SKIP" | head -20
  FAIL=1
fi

# 2. No TODO→NOTE conversions (added lines with NOTE: that had matching TODO: removed)
NEW_NOTE=$(echo "$DIFF" | grep -E '^\+[^+].*\bNOTE:' || true)
REM_TODO=$(echo "$DIFF" | grep -E '^\-[^-].*\bTODO:' || true)
if [ -n "$NEW_NOTE" ] && [ -n "$REM_TODO" ]; then
  # Check if NOTE lines outnumber new feature context (heuristic: ratio > 0)
  NOTE_COUNT=$(echo "$NEW_NOTE" | wc -l)
  TODO_COUNT=$(echo "$REM_TODO" | wc -l)
  if [ "$TODO_COUNT" -gt 0 ] && [ "$NOTE_COUNT" -gt 0 ]; then
    echo "WARN: Possible TODO→NOTE conversions detected ($TODO_COUNT TODO removed, $NOTE_COUNT NOTE added)."
    echo "  Review manually — these may be legitimate if the context changed."
    echo "$NEW_NOTE" | head -10
  fi
fi

# 3. No lint rule files deleted or lint categories disabled
DELETED_LINT=$(echo "$DIFF" | grep -E '^--- a/src/compiler.*/lint/.*\.spl' || true)
if [ -n "$DELETED_LINT" ]; then
  echo "FAIL: Lint rule files deleted:"
  echo "$DELETED_LINT"
  FAIL=1
fi

# 4. No @allow added without reason comment
NEW_ALLOWS=$(echo "$DIFF" | grep -E '^\+[^+].*@allow\(' | grep -v '//[[:space:]]*reason:' || true)
if [ -n "$NEW_ALLOWS" ]; then
  echo "FAIL: New @allow(...) added without reason comment:"
  echo "$NEW_ALLOWS" | head -20
  FAIL=1
fi

# 5. No #[allow] added in Rust without reason comment
NEW_RUST_ALLOWS=$(echo "$DIFF" | grep -E '^\+[^+].*#\[allow\(' | grep -v '//[[:space:]]*reason:' || true)
if [ -n "$NEW_RUST_ALLOWS" ]; then
  echo "FAIL: New #[allow(...)] added in Rust without reason comment:"
  echo "$NEW_RUST_ALLOWS" | head -20
  FAIL=1
fi

if [ "$FAIL" -eq 1 ]; then
  echo ""
  echo "FAIL: AC-4 — cover-up patterns detected."
  exit 1
fi

echo "PASS: AC-4 — no skip(), rule deletions, or bare allows added."
