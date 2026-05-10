#!/usr/bin/env bash
# verify_team_r.sh — Team R sub-tests:
#   1. cargo clippy --workspace --all-targets -- -D warnings (owned workspace only)
#   2. Rust unit test pass (cargo test --workspace)
#   3. Spipe regen check: bin/simple test src/compiler/70.backend/linker/test/
#      confirms no @allow in regenerated .spipe_wrapped_entry_*.spl files
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$REPO_ROOT"

RUST_DIR="src/compiler_rust"

echo "=== Team R: Rust clippy -D warnings ==="
(cd "$RUST_DIR" && cargo clippy --workspace --all-targets -- -D warnings 2>&1)
echo "PASS: cargo clippy clean."

echo ""
echo "=== Team R: Rust unit tests ==="
(cd "$RUST_DIR" && cargo test --workspace 2>&1)
echo "PASS: cargo test passed."

echo ""
echo "=== Team R (R-G): Spipe regen — no @allow in generated files ==="
bin/simple test src/compiler/70.backend/linker/test/ 2>&1

GENERATED_ALLOWS=$(find src/compiler/70.backend/linker/test/ \
  -name '*.spipe_wrapped_entry_*.spl' -o -name '.spipe_wrapped_entry_*.spl' 2>/dev/null \
  | xargs grep -l '@allow(' 2>/dev/null || true)

if [ -n "$GENERATED_ALLOWS" ]; then
  echo ""
  echo "FAIL: Team R (R-G) — @allow still present in generated spipe files:"
  echo "$GENERATED_ALLOWS"
  exit 1
fi

echo "PASS: Team R — all sub-tests green."
