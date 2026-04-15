#!/bin/bash
# Double-click to build all platforms, launch emulators, and capture screenshots.
set -euo pipefail
cd "$(dirname "$0")"

CAPTURE_DIR="$(pwd)/screenshots"
mkdir -p "$CAPTURE_DIR"

echo "=== Simple UI — Multi-Platform Screenshot Capture ==="
echo "Output: $CAPTURE_DIR"
echo ""

# Ensure Tauri CLI
if ! cargo tauri --version 2>/dev/null; then
    cargo install tauri-cli --version "^2"
fi

# -------------------------------------------------------
# 1. Desktop (macOS Tauri)
# -------------------------------------------------------
echo "--- [1/3] Desktop Build ---"
cargo tauri build --debug 2>&1 | tail -5

# Launch in background, give it time to render, screenshot, kill
echo "Launching desktop app..."
cargo tauri dev &
DESKTOP_PID=$!
sleep 8

# Use screencapture on macOS
if command -v screencapture &>/dev/null; then
    screencapture -l $(osascript -e 'tell app "System Events" to get id of first window of process "simple-tauri-shell"' 2>/dev/null || echo "") "$CAPTURE_DIR/desktop_screenshot.png" 2>/dev/null || \
    screencapture "$CAPTURE_DIR/desktop_screenshot.png"
    echo "Saved: $CAPTURE_DIR/desktop_screenshot.png"
fi
kill $DESKTOP_PID 2>/dev/null || true
wait $DESKTOP_PID 2>/dev/null || true

# -------------------------------------------------------
# 2. iOS Simulator
# -------------------------------------------------------
if command -v xcrun &>/dev/null; then
    echo ""
    echo "--- [2/3] iOS Simulator ---"

    rustup target add aarch64-apple-ios aarch64-apple-ios-sim 2>/dev/null || true

    if [ ! -d "src-tauri/gen/apple" ]; then
        cargo tauri ios init
    fi

    # Find an available iPhone simulator
    SIM_UDID=$(xcrun simctl list devices available -j 2>/dev/null | \
        python3 -c "
import json,sys
data = json.load(sys.stdin)
devs = data.get('devices', {})
for rt, ds in devs.items():
    for d in ds:
        if 'iPhone' in d.get('name','') and d.get('isAvailable'):
            print(d['udid']); sys.exit()
" 2>/dev/null || true)

    if [ -n "$SIM_UDID" ]; then
        echo "Booting simulator: $SIM_UDID"
        xcrun simctl boot "$SIM_UDID" 2>/dev/null || true
        open -a Simulator 2>/dev/null || true
        sleep 3

        echo "Building & launching iOS app..."
        cargo tauri ios dev --no-watch &
        IOS_PID=$!
        sleep 20

        echo "Capturing iOS screenshot..."
        xcrun simctl io "$SIM_UDID" screenshot "$CAPTURE_DIR/ios_screenshot.png" 2>/dev/null && \
            echo "Saved: $CAPTURE_DIR/ios_screenshot.png" || \
            echo "WARNING: iOS screenshot failed"

        kill $IOS_PID 2>/dev/null || true
        wait $IOS_PID 2>/dev/null || true
    else
        echo "No iPhone simulator available. Install one via Xcode > Settings > Platforms."
    fi
else
    echo ""
    echo "--- [2/3] iOS Simulator — SKIPPED (no Xcode) ---"
fi

# -------------------------------------------------------
# 3. Android Emulator
# -------------------------------------------------------
if [ -z "${ANDROID_HOME:-}" ] && [ -d "$HOME/Library/Android/sdk" ]; then
    export ANDROID_HOME="$HOME/Library/Android/sdk"
fi

if [ -n "${ANDROID_HOME:-}" ] && [ -f "$ANDROID_HOME/emulator/emulator" ]; then
    echo ""
    echo "--- [3/3] Android Emulator ---"

    if [ -z "${NDK_HOME:-}" ] && [ -d "$ANDROID_HOME/ndk" ]; then
        NDK_VER=$(ls "$ANDROID_HOME/ndk" | sort -V | tail -1)
        export NDK_HOME="$ANDROID_HOME/ndk/$NDK_VER"
    fi

    rustup target add aarch64-linux-android x86_64-linux-android 2>/dev/null || true

    if [ ! -d "src-tauri/gen/android" ]; then
        cargo tauri android init
    fi

    # Find an AVD
    AVD_NAME=$("$ANDROID_HOME/emulator/emulator" -list-avds 2>/dev/null | head -1)

    if [ -n "$AVD_NAME" ]; then
        echo "Starting emulator: $AVD_NAME"
        "$ANDROID_HOME/emulator/emulator" -avd "$AVD_NAME" -no-audio &
        EMU_PID=$!

        echo "Waiting for emulator boot..."
        "$ANDROID_HOME/platform-tools/adb" wait-for-device 2>/dev/null
        sleep 15

        echo "Building & launching Android app..."
        cargo tauri android dev --no-watch &
        ANDROID_PID=$!
        sleep 25

        echo "Capturing Android screenshot..."
        "$ANDROID_HOME/platform-tools/adb" exec-out screencap -p > "$CAPTURE_DIR/android_screenshot.png" 2>/dev/null && \
            echo "Saved: $CAPTURE_DIR/android_screenshot.png" || \
            echo "WARNING: Android screenshot failed"

        kill $ANDROID_PID 2>/dev/null || true
        kill $EMU_PID 2>/dev/null || true
        wait $ANDROID_PID 2>/dev/null || true
        wait $EMU_PID 2>/dev/null || true
    else
        echo "No Android AVD found. Create one in Android Studio > Device Manager."
    fi
else
    echo ""
    echo "--- [3/3] Android Emulator — SKIPPED (no Android SDK) ---"
fi

# -------------------------------------------------------
# Summary
# -------------------------------------------------------
echo ""
echo "=== Done! ==="
echo "Screenshots:"
ls -la "$CAPTURE_DIR/"*.png 2>/dev/null || echo "  (none captured)"
echo ""
echo "Open screenshot folder:"
open "$CAPTURE_DIR" 2>/dev/null || true
