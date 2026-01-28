#!/bin/bash
# Download mold linker binary for bundling with Simple.
#
# This script downloads pre-built mold binaries from GitHub releases.
# Mold 2.0+ is MIT licensed and can be freely distributed.
#
# Usage:
#   ./scripts/download-mold.sh [--version VERSION] [--output DIR]
#
# Examples:
#   ./scripts/download-mold.sh                     # Download to bin/mold
#   ./scripts/download-mold.sh --version 2.34.0    # Specific version
#   ./scripts/download-mold.sh --output /opt/mold  # Custom output dir

set -euo pipefail

# Configuration
MOLD_VERSION="${MOLD_VERSION:-2.34.0}"
OUTPUT_DIR="${OUTPUT_DIR:-bin}"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --version)
            MOLD_VERSION="$2"
            shift 2
            ;;
        --output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --help)
            echo "Usage: $0 [--version VERSION] [--output DIR]"
            echo ""
            echo "Download mold linker binary for bundling with Simple."
            echo ""
            echo "Options:"
            echo "  --version VERSION   Mold version to download (default: $MOLD_VERSION)"
            echo "  --output DIR        Output directory (default: bin)"
            echo ""
            echo "Environment variables:"
            echo "  MOLD_VERSION        Alternative way to set version"
            echo "  OUTPUT_DIR          Alternative way to set output directory"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Detect platform
PLATFORM="$(uname -s)-$(uname -m)"
echo "Detected platform: $PLATFORM"

# Determine download URL based on platform
case "$PLATFORM" in
    Linux-x86_64)
        ARCHIVE="mold-${MOLD_VERSION}-x86_64-linux.tar.gz"
        URL="https://github.com/rui314/mold/releases/download/v${MOLD_VERSION}/${ARCHIVE}"
        MOLD_BINARY_NAME="mold-linux-x86_64"
        ;;
    Linux-aarch64)
        ARCHIVE="mold-${MOLD_VERSION}-aarch64-linux.tar.gz"
        URL="https://github.com/rui314/mold/releases/download/v${MOLD_VERSION}/${ARCHIVE}"
        MOLD_BINARY_NAME="mold-linux-aarch64"
        ;;
    Darwin-x86_64)
        echo "Note: mold for macOS Intel - using Homebrew is recommended"
        echo "Install with: brew install mold"
        echo ""
        echo "Attempting to build from source..."
        ARCHIVE=""
        MOLD_BINARY_NAME="mold-macos-x86_64"
        ;;
    Darwin-arm64)
        echo "Note: mold for macOS Apple Silicon - using Homebrew is recommended"
        echo "Install with: brew install mold"
        echo ""
        echo "Attempting to build from source..."
        ARCHIVE=""
        MOLD_BINARY_NAME="mold-macos-aarch64"
        ;;
    *)
        echo "Unsupported platform: $PLATFORM"
        echo "Supported platforms: Linux-x86_64, Linux-aarch64, Darwin-x86_64, Darwin-arm64"
        exit 1
        ;;
esac

# Create output directory
mkdir -p "$OUTPUT_DIR"

# For Linux, download pre-built binary
if [[ -n "$ARCHIVE" ]]; then
    echo "Downloading mold v${MOLD_VERSION}..."
    echo "URL: $URL"

    # Create temp directory
    TEMP_DIR=$(mktemp -d)
    trap "rm -rf $TEMP_DIR" EXIT

    # Download and extract
    curl -L --progress-bar "$URL" | tar xz -C "$TEMP_DIR"

    # Find the mold binary in the extracted archive
    MOLD_BIN=$(find "$TEMP_DIR" -name "mold" -type f -executable | head -1)

    if [[ -z "$MOLD_BIN" ]]; then
        echo "Error: Could not find mold binary in archive"
        exit 1
    fi

    # Copy to output directory
    cp "$MOLD_BIN" "$OUTPUT_DIR/$MOLD_BINARY_NAME"
    chmod +x "$OUTPUT_DIR/$MOLD_BINARY_NAME"

    # Also create a symlink named just "mold"
    ln -sf "$MOLD_BINARY_NAME" "$OUTPUT_DIR/mold"

    echo "Successfully installed mold to $OUTPUT_DIR/$MOLD_BINARY_NAME"
    echo ""

    # Download license file
    echo "Downloading MIT license..."
    curl -sL "https://raw.githubusercontent.com/rui314/mold/v${MOLD_VERSION}/LICENSE" > "$OUTPUT_DIR/MOLD_LICENSE"
    echo "License saved to $OUTPUT_DIR/MOLD_LICENSE"

else
    # For macOS, check for Homebrew mold or suggest building from source
    if command -v mold &> /dev/null; then
        SYSTEM_MOLD=$(command -v mold)
        echo "Found system mold at: $SYSTEM_MOLD"
        echo "Copying to $OUTPUT_DIR/$MOLD_BINARY_NAME"
        cp "$SYSTEM_MOLD" "$OUTPUT_DIR/$MOLD_BINARY_NAME"
        chmod +x "$OUTPUT_DIR/$MOLD_BINARY_NAME"
        ln -sf "$MOLD_BINARY_NAME" "$OUTPUT_DIR/mold"
    else
        echo "Error: mold not found on this macOS system."
        echo ""
        echo "Please install mold using Homebrew:"
        echo "  brew install mold"
        echo ""
        echo "Then run this script again."
        exit 1
    fi
fi

# Verify installation
echo ""
echo "Verifying installation..."
"$OUTPUT_DIR/mold" --version

echo ""
echo "Installation complete!"
echo ""
echo "Binary location: $OUTPUT_DIR/mold"
echo "To use with Simple:"
echo "  export PATH=\"\$(pwd)/$OUTPUT_DIR:\$PATH\""
echo "  simple build --native your_program.spl"
