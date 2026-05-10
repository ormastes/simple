#!/usr/bin/env bash
# verify_ac1.sh — AC-1: bin/simple build lint reports 0 warnings in owned crates.
# Vendored paths (src/compiler_rust/vendor/**, src/runtime/vendor/**) are excluded.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

echo "=== AC-1: Rust clippy — 0 warnings in owned crates ==="
LINT_OUT=$(bin/simple build lint 2>&1)
echo "$LINT_OUT"

# Filter out vendor-path warnings
OWNED_WARNINGS=$(echo "$LINT_OUT" | grep -E '^\s*-->' | grep -v 'vendor/' || true)

if [ -n "$OWNED_WARNINGS" ]; then
  echo ""
  echo "FAIL: Owned-crate warnings found:"
  echo "$OWNED_WARNINGS"
  exit 1
fi

# Also check for 'warning:' lines that are not from vendor
WARNING_COUNT=$(echo "$LINT_OUT" | grep -E '^warning\[' | grep -v 'vendor/' | wc -l || true)
if [ "$WARNING_COUNT" -gt 0 ]; then
  echo ""
  echo "FAIL: $WARNING_COUNT owned-crate warning(s) reported."
  exit 1
fi

echo ""
echo "PASS: AC-1 — 0 owned-crate clippy warnings."
