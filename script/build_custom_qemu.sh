#!/bin/bash
# Build Custom QEMU with Simple Language Semihosting Support
#
# Adds support for string interning operations (0x100-0x104) to QEMU RISC-V
#
# Timeline: 8-12 hours (mostly compilation time)
# Result: Custom qemu-system-riscv32 with string table support

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
QEMU_DIR="$PROJECT_ROOT/resources/qemu"
SOURCE_DIR="$QEMU_DIR/downloads/qemu-8.2.0"
BUILD_DIR="$QEMU_DIR/build/qemu-8.2.0-simple"
INSTALL_DIR="$QEMU_DIR/install/qemu-8.2.0-simple"

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Custom QEMU Build - Simple Language Semihosting Support     ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

# Step 1: Check prerequisites
echo "→ Checking prerequisites..."

if ! command -v gcc &> /dev/null; then
    echo "❌ Error: gcc not found"
    echo "Install: sudo apt install build-essential"
    exit 1
fi

if ! command -v pkg-config &> /dev/null; then
    echo "❌ Error: pkg-config not found"
    echo "Install: sudo apt install pkg-config"
    exit 1
fi

if ! pkg-config --exists glib-2.0; then
    echo "❌ Error: glib-2.0 not found"
    echo "Install: sudo apt install libglib2.0-dev"
    exit 1
fi

echo "✓ Prerequisites OK"
echo ""

# Step 2: Download QEMU source (if not already done)
if [ ! -d "$SOURCE_DIR" ]; then
    echo "→ QEMU source not found, downloading..."
    cd "$QEMU_DIR/downloads"

    if [ ! -f qemu-8.2.0.tar.xz ]; then
        curl -L --progress-bar \
            -o qemu-8.2.0.tar.xz \
            https://download.qemu.org/qemu-8.2.0.tar.xz
    fi

    tar -xf qemu-8.2.0.tar.xz
    echo "✓ QEMU source extracted"
else
    echo "✓ QEMU source found at $SOURCE_DIR"
fi

echo ""

# Step 3: Apply patch
echo "→ Applying Simple language semihosting patch..."

PATCH_FILE="$SOURCE_DIR/simple-semihosting-full.patch"

# Check if full patch exists
if [ ! -f "$PATCH_FILE" ]; then
    echo "❌ Error: Full patch not found at $PATCH_FILE"
    echo "   Expected: resources/qemu/downloads/qemu-8.2.0/simple-semihosting-full.patch"
    exit 1
fi

cd "$SOURCE_DIR"

# Apply patch
if patch -p1 --dry-run < "$PATCH_FILE" > /dev/null 2>&1; then
    patch -p1 < "$PATCH_FILE"
    echo "✓ Patch applied successfully"
elif grep -q "TARGET_SYS_WRITE_HANDLE" semihosting/arm-compat-semi.c; then
    echo "✓ Patch already applied"
else
    echo "❌ Error: Patch failed to apply"
    echo "Manual patching required - see: $PATCH_FILE"
    exit 1
fi

echo ""

# Step 4: Configure QEMU
echo "→ Configuring QEMU..."

mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"

"$SOURCE_DIR/configure" \
    --target-list=riscv32-softmmu,riscv64-softmmu \
    --prefix="$INSTALL_DIR" \
    --enable-debug \
    --disable-werror

echo "✓ Configuration complete"
echo ""

# Step 5: Build QEMU
echo "→ Building QEMU (this will take 30-60 minutes)..."
echo "   Parallel jobs: $(nproc)"
echo ""

make -j$(nproc)

echo ""
echo "✓ Build complete"
echo ""

# Step 6: Install
echo "→ Installing to $INSTALL_DIR..."

make install

echo "✓ Installation complete"
echo ""

# Step 7: Create symlink
echo "→ Creating symlink in resources/qemu/bin/..."

mkdir -p "$QEMU_DIR/bin"
ln -sf "$INSTALL_DIR/bin/qemu-system-riscv32" \
       "$QEMU_DIR/bin/qemu-system-riscv32-simple"
ln -sf "$INSTALL_DIR/bin/qemu-system-riscv64" \
       "$QEMU_DIR/bin/qemu-system-riscv64-simple"

echo "✓ Symlinks created"
echo ""

# Step 8: Test
echo "→ Testing custom QEMU..."

"$QEMU_DIR/bin/qemu-system-riscv32-simple" --version | head -1

echo ""
echo "╔════════════════════════════════════════════════════════════════╗"
echo "║  Build Complete!                                              ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""
echo "Custom QEMU installed to:"
echo "  $INSTALL_DIR"
echo ""
echo "Symlinks created:"
echo "  $QEMU_DIR/bin/qemu-system-riscv32-simple"
echo "  $QEMU_DIR/bin/qemu-system-riscv64-simple"
echo ""
echo "Test with interned binary:"
echo "  resources/qemu/bin/qemu-system-riscv32-simple \\"
echo "    -M virt -bios none \\"
echo "    -kernel examples/baremetal/hello_riscv32_interned.elf \\"
echo "    -nographic \\"
echo "    -semihosting-config enable=on"
echo ""
echo "Note: Full string table support requires additional implementation."
echo "      Current patch allows program to continue (returns success stub)."
