#!/usr/bin/env bash
# Hook: Stop — Warn about incomplete work: failing tests, changes, TODOs
set -euo pipefail

ISSUES=0

# Check for uncommitted changes
if command -v jj &>/dev/null; then
  CHANGES=$(jj diff --stat 2>/dev/null || true)
  if [[ -n "$CHANGES" ]]; then
    echo "UNCOMMITTED CHANGES:"
    echo "$CHANGES" | tail -1
    ISSUES=$((ISSUES + 1))
  fi
fi

# Check for new TODOs in diff
if command -v jj &>/dev/null; then
  NEW_TODOS=$(jj diff 2>/dev/null | grep -P '^\+.*\b(TODO|FIXME)\b' | grep -v '^\+\+\+' || true)
  if [[ -n "$NEW_TODOS" ]]; then
    COUNT=$(echo "$NEW_TODOS" | wc -l)
    echo "NEW TODOs: $COUNT unresolved TODO/FIXME comments"
    ISSUES=$((ISSUES + 1))
  fi
fi

if [[ $ISSUES -eq 0 ]]; then
  exit 0
fi

echo ""
echo "Review the above before considering this session complete."

exit 0
