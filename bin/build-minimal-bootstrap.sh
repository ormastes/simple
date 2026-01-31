#!/bin/bash
# Build minimal bootstrap compiler with build-std + UPX compression
set -e

echo "======================================"
echo "Minimal Bootstrap Compiler Builder"
echo "======================================"
echo ""

# Check for UPX
if ! command -v upx &> /dev/null; then
    echo "Error: UPX is not installed"
    echo "Install with: sudo apt-get install upx"
    exit 1
fi

# Check for nightly + rust-src
if ! rustup toolchain list | grep -q nightly; then
    echo "Installing nightly toolchain..."
    rustup toolchain install nightly
fi

echo "Installing rust-src component..."
rustup component add rust-src --toolchain nightly 2>/dev/null || true

# Build with build-std
echo ""
echo "Building with build-std optimizations..."
echo "(This will take several minutes...)"
echo ""

cd rust
cargo +nightly build --profile bootstrap -p simple-driver \
    --target x86_64-unknown-linux-gnu

BINARY="../target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime"

# Check if build succeeded
if [ ! -f "$BINARY" ]; then
    echo "Error: Build failed - binary not found"
    exit 1
fi

# Backup uncompressed
echo ""
echo "Backing up uncompressed binary..."
cp "$BINARY" "$BINARY.uncompressed"

SIZE_BEFORE=$(du -h "$BINARY" | cut -f1)
echo "Size before UPX: $SIZE_BEFORE"

# Compress with UPX
echo ""
echo "Compressing with UPX (--best --lzma)..."
upx --best --lzma "$BINARY"

SIZE_AFTER=$(du -h "$BINARY" | cut -f1)

# Report
echo ""
echo "======================================"
echo "Build Complete!"
echo "======================================"
echo ""
echo "Uncompressed: $SIZE_BEFORE (backed up as simple_runtime.uncompressed)"
echo "Compressed:   $SIZE_AFTER"
echo ""
echo "Binary location:"
echo "  $BINARY"
echo ""
echo "Test with:"
echo "  $BINARY --version"
echo ""
