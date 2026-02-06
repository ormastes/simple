#!/usr/bin/env bash
# Link binaries from bin/rust/ to bin/simple/ for cross-platform compatibility

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

BIN_RUST="$PROJECT_ROOT/bin/rust"
BIN_SIMPLE="$PROJECT_ROOT/bin/simple"

echo "Creating binary symlinks..."

# Create bin/simple directory if it doesn't exist
mkdir -p "$BIN_SIMPLE"

# Define binaries to link
BINARIES=(
    "simple"
    "simple-fmt"
    "simple-lint"
    "simple-test"
    "smh_coverage"
)

# Create symlinks
for binary in "${BINARIES[@]}"; do
    if [ -f "$BIN_RUST/$binary" ]; then
        echo "  Linking $binary..."
        ln -sf "../rust/$binary" "$BIN_SIMPLE/$binary"
    else
        echo "  Warning: $BIN_RUST/$binary not found, skipping"
    fi
done

echo "✅ Binary links created in $BIN_SIMPLE"
echo ""
echo "Add to your PATH:"
echo "  export PATH=\"$BIN_SIMPLE:\$PATH\""
