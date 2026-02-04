#!/bin/bash
# Build script for simple-ffi-wrapper package
#
# Usage: ./build.sh [--release]

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BUILD_DIR="$SCRIPT_DIR/build"
PROFILE="debug"

if [[ "$1" == "--release" ]]; then
    PROFILE="release"
fi

echo "Building simple-ffi-wrapper ($PROFILE)..."
echo ""

# Create build directory
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"

# Create Cargo.toml
cat > Cargo.toml << 'CARGO_EOF'
[package]
name = "simple-ffi-wrapper"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib", "rlib"]

[dependencies]
bdwgc-alloc = "0.6"
glob = "0.3"
hostname = "0.4"
libc = "0.2"
CARGO_EOF

# Create src directory
mkdir -p src

# Copy source files (rename .txt to .rs)
cp "$SCRIPT_DIR/src/lib.txt" src/lib.rs
cp "$SCRIPT_DIR/src/gc.txt" src/gc.rs
cp "$SCRIPT_DIR/src/env.txt" src/env.rs
cp "$SCRIPT_DIR/src/file_io.txt" src/file_io.rs
cp "$SCRIPT_DIR/src/runtime_value.txt" src/runtime_value.rs
cp "$SCRIPT_DIR/src/bootstrap_ffi.txt" src/bootstrap_ffi.rs

# Build
if [[ "$PROFILE" == "release" ]]; then
    cargo build --release
    LIB_DIR="target/release"
else
    cargo build
    LIB_DIR="target/debug"
fi

# Copy output to lib/
mkdir -p "$SCRIPT_DIR/lib"
if [[ -f "$LIB_DIR/libsimple_ffi_wrapper.so" ]]; then
    cp "$LIB_DIR/libsimple_ffi_wrapper.so" "$SCRIPT_DIR/lib/"
    echo "Built: lib/libsimple_ffi_wrapper.so"
fi
if [[ -f "$LIB_DIR/libsimple_ffi_wrapper.dylib" ]]; then
    cp "$LIB_DIR/libsimple_ffi_wrapper.dylib" "$SCRIPT_DIR/lib/"
    echo "Built: lib/libsimple_ffi_wrapper.dylib"
fi
if [[ -f "$LIB_DIR/libsimple_ffi_wrapper.a" ]]; then
    cp "$LIB_DIR/libsimple_ffi_wrapper.a" "$SCRIPT_DIR/lib/"
    echo "Built: lib/libsimple_ffi_wrapper.a"
fi

echo ""
echo "Build complete!"
echo "Library files are in: $SCRIPT_DIR/lib/"
