#!/bin/bash
# Double-click this file in Finder to build & run the Tauri desktop app.
set -euo pipefail
cd "$(dirname "$0")"
echo "=== Building & launching Simple UI — Tauri Desktop ==="
echo "Project: $(pwd)"

# Ensure Tauri CLI
if ! cargo tauri --version 2>/dev/null; then
    echo "Installing Tauri CLI..."
    cargo install tauri-cli --version "^2"
fi

echo "Starting Tauri dev server..."
cargo tauri dev
