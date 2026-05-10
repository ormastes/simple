#!/usr/bin/env bash
# verify_ac2.sh — AC-2: All #[allow(...)] in owned Rust (compiler/src, driver/src)
# must have an inline or adjacent (within 2 lines prior) "// reason:" comment.
# Exits 1 if any bare allow is found; prints offending lines to stdout.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

COMPILER_SRC="src/compiler_rust/compiler/src"
DRIVER_SRC="src/compiler_rust/driver/src"

echo "=== AC-2: No bare #[allow(...)] in owned Rust (compiler + driver) ==="

BARE_ALLOWS=()

while IFS= read -r hit; do
  filepath="${hit%%:*}"
  rest="${hit#*:}"
  lineno="${rest%%:*}"
  # Check if the allow line itself or either of the 2 preceding lines contains "// reason:"
  # Use sed to extract lines (lineno-2) to lineno from file
  start=$(( lineno > 2 ? lineno - 2 : 1 ))
  window=$(sed -n "${start},${lineno}p" "$filepath" 2>/dev/null || true)
  if echo "$window" | grep -q '//[[:space:]]*reason:'; then
    : # has reason comment — OK
  else
    BARE_ALLOWS+=("$hit")
  fi
done < <(grep -rn '#\[allow(' "$COMPILER_SRC" "$DRIVER_SRC" --include='*.rs' | grep -v '//[[:space:]]*reason:' || true)

if [ ${#BARE_ALLOWS[@]} -gt 0 ]; then
  echo ""
  echo "FAIL: ${#BARE_ALLOWS[@]} bare #[allow(...)] without reason comment:"
  printf '  %s\n' "${BARE_ALLOWS[@]}"
  exit 1
fi

echo "PASS: AC-2 — all #[allow(...)] in owned Rust have reason comments."
