#!/bin/bash
# Double-click this file in Finder to build & run on iOS Simulator.
set -euo pipefail
cd "$(dirname "$0")"
echo "=== Building & launching Simple UI — iOS Simulator ==="

# Ensure Tauri CLI
if ! cargo tauri --version 2>/dev/null; then
    cargo install tauri-cli --version "^2"
fi

# Ensure iOS targets
rustup target add aarch64-apple-ios aarch64-apple-ios-sim x86_64-apple-ios 2>/dev/null || true

# Initialize iOS project if needed
if [ ! -d "src-tauri/gen/apple" ]; then
    echo "Initializing iOS project..."
    cargo tauri ios init
fi

echo "Starting iOS Simulator dev server..."
cargo tauri ios dev
