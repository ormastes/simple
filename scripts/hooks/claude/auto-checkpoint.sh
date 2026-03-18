#!/usr/bin/env bash
# Hook: Stop — Auto-describe uncommitted changes as WIP checkpoint
set -euo pipefail

if ! command -v jj &>/dev/null; then
  exit 0
fi

# Check if there are uncommitted changes
CHANGES=$(jj diff --stat 2>/dev/null || true)

if [[ -n "$CHANGES" ]]; then
  # Only describe if the current change has no description yet
  CURRENT_DESC=$(jj log -r @ --no-graph -T 'description' 2>/dev/null || true)
  if [[ -z "$CURRENT_DESC" || "$CURRENT_DESC" == "(no description set)" ]]; then
    TIMESTAMP=$(date +%Y-%m-%dT%H:%M)
    jj describe -m "wip: auto-checkpoint $TIMESTAMP" 2>/dev/null || true
    echo "Auto-checkpoint: described current change as 'wip: auto-checkpoint $TIMESTAMP'"
  fi
fi

exit 0
