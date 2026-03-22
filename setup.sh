#!/bin/sh
# Simple Language — Platform Setup
#
# Detects the current OS and architecture, then creates:
#   bin/simple          → bin/release/<os>-<arch>/simple
#   bin/release/simple  → <os>-<arch>/simple
#
# Supported platforms:
#   linux-x86_64, linux-arm64, linux-riscv64
#   freebsd-x86_64
#   macos-x86_64, macos-arm64
#   windows-x86_64, windows-arm64
#
# Usage:
#   sh setup.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BIN_DIR="$SCRIPT_DIR/bin"
RELEASE_DIR="$BIN_DIR/release"

# ── Detect OS ──
detect_os() {
    case "$(uname -s)" in
        Linux*)     echo "linux" ;;
        Darwin*)    echo "macos" ;;
        FreeBSD*)   echo "freebsd" ;;
        CYGWIN*|MINGW*|MSYS*) echo "windows" ;;
        *)          echo "unknown" ;;
    esac
}

# ── Detect Architecture ──
detect_arch() {
    case "$(uname -m)" in
        x86_64|amd64)   echo "x86_64" ;;
        aarch64|arm64)  echo "arm64" ;;
        riscv64)        echo "riscv64" ;;
        *)              echo "unknown" ;;
    esac
}

OS="$(detect_os)"
ARCH="$(detect_arch)"
PLATFORM="${OS}-${ARCH}"

echo "Detected platform: $PLATFORM"

# ── Determine binary name ──
if [ "$OS" = "windows" ]; then
    BINARY_NAME="simple.exe"
else
    BINARY_NAME="simple"
fi

PLATFORM_BINARY="$RELEASE_DIR/$PLATFORM/$BINARY_NAME"

# ── Validate binary exists ──
if [ ! -f "$PLATFORM_BINARY" ]; then
    echo "Error: No binary found for platform '$PLATFORM'"
    echo "Expected: $PLATFORM_BINARY"
    echo ""
    echo "Available platforms:"
    for dir in "$RELEASE_DIR"/*/; do
        if [ -d "$dir" ]; then
            name="$(basename "$dir")"
            echo "  $name"
        fi
    done
    exit 1
fi

# ── Create bin/release/simple symlink ──
echo "Linking: bin/release/simple -> $PLATFORM/$BINARY_NAME"
rm -f "$RELEASE_DIR/simple"
cd "$RELEASE_DIR"
ln -s "$PLATFORM/$BINARY_NAME" simple
cd "$SCRIPT_DIR"

# ── Create bin/simple symlink ──
echo "Linking: bin/simple -> release/simple"
rm -f "$BIN_DIR/simple"
cd "$BIN_DIR"
ln -s release/simple simple
cd "$SCRIPT_DIR"

# ── Verify ──
if [ -x "$BIN_DIR/simple" ]; then
    VERSION=$("$BIN_DIR/simple" --version 2>/dev/null || echo "(version check failed)")
    echo ""
    echo "Setup complete: $VERSION"
    echo "Binary: $PLATFORM_BINARY"
else
    echo ""
    echo "Warning: bin/simple exists but is not executable"
    exit 1
fi
