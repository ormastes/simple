#!/usr/bin/env bash
# verify_ac7.sh — AC-7: Each commit in this wave touches ≤5 files unless
# the commit message contains "bundle: <reason>" (U-A cascade exception).
# Compares commits on HEAD not in origin/main.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== AC-7: Atomic commits (≤5 files or bundle: tag) ==="

BASE_REF="origin/main"
if ! git rev-parse --verify "$BASE_REF" >/dev/null 2>&1; then
  echo "WARN: origin/main not found — using HEAD~10 as base"
  BASE_REF="HEAD~10"
fi

FAIL=0
COMMITS=$(git log --oneline "$BASE_REF..HEAD" --format="%H %s" 2>/dev/null || true)

if [ -z "$COMMITS" ]; then
  echo "No commits to check (HEAD == $BASE_REF)."
  echo "PASS: AC-7 — nothing to verify yet."
  exit 0
fi

while IFS= read -r line; do
  sha="${line%% *}"
  msg="${line#* }"
  file_count=$(git diff-tree --no-commit-id -r --name-only "$sha" 2>/dev/null | wc -l || true)
  if [ "$file_count" -gt 5 ]; then
    if echo "$msg" | grep -q 'bundle:'; then
      echo "  OK (bundle exception, $file_count files): $sha — $msg"
    else
      echo "  FAIL ($file_count files, no bundle tag): $sha — $msg"
      FAIL=1
    fi
  else
    echo "  OK ($file_count files): $sha — $msg"
  fi
done <<< "$COMMITS"

if [ "$FAIL" -eq 1 ]; then
  echo ""
  echo "FAIL: AC-7 — some commits exceed 5 files without a 'bundle: <reason>' tag."
  exit 1
fi

echo ""
echo "PASS: AC-7 — all commits are atomic (≤5 files or have bundle: tag)."
