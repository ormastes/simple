#!/bin/bash
# Double-click this file in Finder to build & run the standalone Tauri desktop app.
set -euo pipefail
cd "$(dirname "$0")"
echo "=== Building & launching Simple UI — Tauri Desktop ==="
echo "Project: $(pwd)"

mkdir -p dist
cp index.html dist/index.html

SIMPLE_BIN_PATH="${1:-../../bin/simple}"
ENTRY_PATH="${2:-../../examples/ui/hello_tauri.ui.sdn}"
shift $(( $# > 1 ? 2 : $# ))

echo "Standalone shell:"
echo "  SIMPLE_BIN=$SIMPLE_BIN_PATH"
echo "  ENTRY=$ENTRY_PATH"
echo "  EXTRA_ARGS=${*:-<none>}"

exec cargo run --manifest-path src-tauri/Cargo.toml -- "$SIMPLE_BIN_PATH" "$ENTRY_PATH" "$@"
