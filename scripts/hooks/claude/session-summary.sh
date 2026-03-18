#!/usr/bin/env bash
# Hook: Stop — Show session change summary
set -euo pipefail

if ! command -v jj &>/dev/null; then
  exit 0
fi

STAT=$(jj diff --stat 2>/dev/null || true)

if [[ -n "$STAT" ]]; then
  echo "SESSION SUMMARY:"
  echo "$STAT"
fi

exit 0
