#!/bin/bash
# Build bootstrap binaries for all platforms locally
# This script is for local development/testing

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "Building multi-platform bootstrap binaries..."
echo "Project root: $PROJECT_ROOT"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Platform configurations
declare -A PLATFORMS=(
    ["linux-x86_64"]="x86_64-unknown-linux-gnu"
    ["linux-arm64"]="aarch64-unknown-linux-gnu"
    ["linux-riscv64"]="riscv64gc-unknown-linux-gnu"
    ["macos-x86_64"]="x86_64-apple-darwin"
    ["macos-arm64"]="aarch64-apple-darwin"
    ["windows-x86_64"]="x86_64-pc-windows-msvc"
    ["windows-arm64"]="aarch64-pc-windows-msvc"
)

# Check if cross is installed
check_cross() {
    if ! command -v cross &> /dev/null; then
        echo -e "${YELLOW}Warning: 'cross' not installed${NC}"
        echo "Install with: cargo install cross --git https://github.com/cross-rs/cross"
        echo "Cross-compilation will be skipped."
        return 1
    fi
    return 0
}

HAS_CROSS=$(check_cross && echo "yes" || echo "no")

# Detect current platform
CURRENT_PLATFORM="unknown"
ARCH=$(uname -m)
OS=$(uname -s | tr '[:upper:]' '[:lower:]')

case "$ARCH" in
    x86_64) ARCH="x86_64" ;;
    aarch64|arm64) ARCH="arm64" ;;
    riscv64) ARCH="riscv64" ;;
esac

case "$OS" in
    linux) OS="linux" ;;
    darwin) OS="macos" ;;
esac

CURRENT_PLATFORM="${OS}-${ARCH}"
echo -e "${GREEN}Current platform: $CURRENT_PLATFORM${NC}"

# Create bootstrap directories
mkdir -p "$PROJECT_ROOT/bin/bootstrap"

# Build for each platform
for platform in "${!PLATFORMS[@]}"; do
    target="${PLATFORMS[$platform]}"
    echo ""
    echo "================================================"
    echo "Building: $platform ($target)"
    echo "================================================"

    # Determine if cross-compilation is needed
    needs_cross=false
    if [ "$platform" != "$CURRENT_PLATFORM" ]; then
        needs_cross=true
    fi

    # Skip if cross-compilation needed but cross not available
    if [ "$needs_cross" = true ] && [ "$HAS_CROSS" != "yes" ]; then
        echo -e "${YELLOW}Skipping $platform (cross-compilation not available)${NC}"
        continue
    fi

    # Add target if not already added
    echo "Adding target: $target"
    rustup target add "$target" 2>/dev/null || true

    # Build
    if [ "$needs_cross" = true ]; then
        echo "Using cross for $platform..."
        cross build --release --target "$target"
    else
        echo "Native build for $platform..."
        cargo build --release --target "$target"
    fi

    # Copy binary to bootstrap directory
    mkdir -p "$PROJECT_ROOT/bin/bootstrap/$platform"

    if [[ "$platform" == windows-* ]]; then
        ext=".exe"
    else
        ext=""
    fi

    source_bin="$PROJECT_ROOT/target/$target/release/simple_runtime$ext"
    dest_bin="$PROJECT_ROOT/bin/bootstrap/$platform/simple$ext"

    if [ -f "$source_bin" ]; then
        cp "$source_bin" "$dest_bin"
        chmod +x "$dest_bin"
        size=$(ls -lh "$dest_bin" | awk '{print $5}')
        echo -e "${GREEN}✓ Built: $dest_bin ($size)${NC}"
    else
        echo -e "${RED}✗ Failed: Binary not found at $source_bin${NC}"
    fi
done

echo ""
echo "================================================"
echo "Build Summary"
echo "================================================"

for platform in "${!PLATFORMS[@]}"; do
    if [[ "$platform" == windows-* ]]; then
        ext=".exe"
    else
        ext=""
    fi

    binary="$PROJECT_ROOT/bin/bootstrap/$platform/simple$ext"
    if [ -f "$binary" ]; then
        size=$(ls -lh "$binary" | awk '{print $5}')
        echo -e "${GREEN}✓ $platform: $size${NC}"
    else
        echo -e "${YELLOW}⊘ $platform: not built${NC}"
    fi
done

echo ""
echo -e "${GREEN}Bootstrap build complete!${NC}"
echo "Binaries located in: bin/bootstrap/"
