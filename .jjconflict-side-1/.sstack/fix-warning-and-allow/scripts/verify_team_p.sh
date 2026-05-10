#!/usr/bin/env bash
# verify_team_p.sh — Team P sub-test:
# grep for @allow(primitive_api...) in owned .spl without adjacent reason comment.
# Exits 1 if any bare primitive_api allow remains.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== Team P: No bare @allow(primitive_api...) in owned .spl ==="

BARE=$(grep -rn '@allow.*primitive_api' \
  src/lib src/app src/compiler src/compiler_rust/lib \
  --include='*.spl' \
  --exclude-dir='vendor' \
  | grep -v '^\([^:]*\):[0-9]*:[[:space:]]*#' \
  || true)

if [ -n "$BARE" ]; then
  # For each hit, check if preceding 2 lines contain "# reason:" (spl uses # comments, not //)
  REAL_BARE=()
  while IFS= read -r hit; do
    filepath="${hit%%:*}"
    rest="${hit#*:}"
    lineno="${rest%%:*}"
    start=$(( lineno > 2 ? lineno - 2 : 1 ))
    window=$(sed -n "${start},${lineno}p" "$filepath" 2>/dev/null || true)
    if ! echo "$window" | grep -qE '#[[:space:]]*reason:'; then
      REAL_BARE+=("$hit")
    fi
  done <<< "$BARE"

  if [ ${#REAL_BARE[@]} -gt 0 ]; then
    echo "FAIL: ${#REAL_BARE[@]} bare @allow(primitive_api...) without reason:"
    printf '  %s\n' "${REAL_BARE[@]}"
    exit 1
  fi
fi

echo "PASS: Team P — no bare @allow(primitive_api...) remaining."
