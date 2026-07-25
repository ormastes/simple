#!/bin/bash
# Double-click this file in Finder to build & run on Android Emulator.
set -euo pipefail
cd "$(dirname "$0")"
echo "=== Building & launching Simple UI — Android Emulator ==="

# Ensure Tauri CLI
if ! cargo tauri --version 2>/dev/null; then
    cargo install tauri-cli --version "^2"
fi

# Auto-detect Android SDK
if [ -z "${ANDROID_HOME:-}" ]; then
    if [ -d "$HOME/Library/Android/sdk" ]; then
        export ANDROID_HOME="$HOME/Library/Android/sdk"
    fi
fi

if [ -z "${ANDROID_HOME:-}" ]; then
    echo "ERROR: ANDROID_HOME not set and Android SDK not found."
    echo "Install Android Studio first: https://developer.android.com/studio"
    exit 1
fi

# Find NDK
if [ -z "${NDK_HOME:-}" ] && [ -d "$ANDROID_HOME/ndk" ]; then
    NDK_VER=$(ls "$ANDROID_HOME/ndk" | sort -V | tail -1)
    export NDK_HOME="$ANDROID_HOME/ndk/$NDK_VER"
fi

echo "ANDROID_HOME=$ANDROID_HOME"
echo "NDK_HOME=${NDK_HOME:-not set}"

# Ensure Android targets
rustup target add aarch64-linux-android armv7-linux-androideabi x86_64-linux-android i686-linux-android 2>/dev/null || true

# Initialize Android project if needed
if [ ! -d "src-tauri/gen/android" ]; then
    echo "Initializing Android project..."
    cargo tauri android init
fi

echo "Starting Android Emulator dev server..."
cargo tauri android dev
