#!/usr/bin/env bash
# Hook: Stop — Warn about new TODO/FIXME lines introduced this session
set -euo pipefail

# Check if jj is available
if ! command -v jj &>/dev/null; then
  exit 0
fi

# Get diff of current changes
DIFF=$(jj diff 2>/dev/null || true)

if [[ -z "$DIFF" ]]; then
  exit 0
fi

# Find added TODO/FIXME lines (lines starting with +)
NEW_TODOS=$(echo "$DIFF" | grep -P '^\+.*\b(TODO|FIXME)\b' | grep -v '^\+\+\+' || true)

if [[ -n "$NEW_TODOS" ]]; then
  COUNT=$(echo "$NEW_TODOS" | wc -l)
  echo "NOTE: $COUNT new TODO/FIXME comment(s) introduced this session:"
  echo "$NEW_TODOS" | head -10
  if [[ $COUNT -gt 10 ]]; then
    echo "  ... and $((COUNT - 10)) more"
  fi
  echo "Consider: implement the TODO or track it with 'bin/simple todo-scan'"
fi

exit 0
