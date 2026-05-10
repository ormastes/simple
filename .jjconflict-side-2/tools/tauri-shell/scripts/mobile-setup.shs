#!/bin/bash
# mobile-setup.sh — Set up and build Tauri v2 mobile targets (iOS + Android)
#
# Prerequisites (macOS):
#   - Xcode installed (with iOS simulators)
#   - Android Studio installed (with SDK, NDK, emulator)
#   - Rust installed (rustup)
#   - Node.js installed
#
# Usage:
#   cd tools/tauri-shell
#   ./scripts/mobile-setup.sh setup     # Install Rust targets + Tauri CLI
#   ./scripts/mobile-setup.sh ios       # Build & run iOS simulator
#   ./scripts/mobile-setup.sh android   # Build & run Android emulator
#   ./scripts/mobile-setup.sh both      # Build both platforms
#   ./scripts/mobile-setup.sh capture   # Build, launch, and capture screenshots

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
SRC_TAURI="$PROJECT_DIR/src-tauri"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

log()   { echo -e "${GREEN}[mobile-setup]${NC} $*"; }
warn()  { echo -e "${YELLOW}[mobile-setup]${NC} $*"; }
error() { echo -e "${RED}[mobile-setup]${NC} $*" >&2; }

# ---------------------------------------------------------------------------
# setup — install all prerequisites
# ---------------------------------------------------------------------------
do_setup() {
    log "Installing Rust Android targets..."
    rustup target add \
        aarch64-linux-android \
        armv7-linux-androideabi \
        x86_64-linux-android \
        i686-linux-android

    log "Installing Rust iOS targets..."
    rustup target add \
        aarch64-apple-ios \
        aarch64-apple-ios-sim \
        x86_64-apple-ios

    log "Checking for Tauri CLI..."
    if ! cargo tauri --version 2>/dev/null; then
        log "Installing Tauri CLI..."
        cargo install tauri-cli --version "^2"
    else
        log "Tauri CLI already installed: $(cargo tauri --version)"
    fi

    # Verify Android SDK
    if [ -z "${ANDROID_HOME:-}" ]; then
        if [ -d "$HOME/Library/Android/sdk" ]; then
            export ANDROID_HOME="$HOME/Library/Android/sdk"
            warn "ANDROID_HOME not set, using: $ANDROID_HOME"
        else
            error "ANDROID_HOME not set and Android SDK not found at default location."
            error "Install Android Studio or set ANDROID_HOME."
        fi
    fi

    if [ -n "${ANDROID_HOME:-}" ]; then
        log "Android SDK: $ANDROID_HOME"
        # Check for NDK
        if [ -d "$ANDROID_HOME/ndk" ]; then
            NDK_VER=$(ls "$ANDROID_HOME/ndk" | sort -V | tail -1)
            log "NDK version: $NDK_VER"
            export NDK_HOME="$ANDROID_HOME/ndk/$NDK_VER"
        else
            warn "No NDK found. Install via Android Studio SDK Manager."
        fi
    fi

    # Verify Xcode
    if command -v xcodebuild &>/dev/null; then
        log "Xcode: $(xcodebuild -version | head -1)"
    else
        warn "Xcode not found. iOS builds will not work."
    fi

    log "Setup complete!"
}

# ---------------------------------------------------------------------------
# init — initialize mobile projects if needed
# ---------------------------------------------------------------------------
do_init() {
    cd "$PROJECT_DIR"

    if [ ! -d "$SRC_TAURI/gen/android" ]; then
        log "Initializing Android project..."
        cargo tauri android init
    else
        log "Android project already initialized."
    fi

    if [ ! -d "$SRC_TAURI/gen/apple" ]; then
        log "Initializing iOS project..."
        cargo tauri ios init
    else
        log "iOS project already initialized."
    fi
}

# ---------------------------------------------------------------------------
# ios — build and optionally run on iOS simulator
# ---------------------------------------------------------------------------
do_ios() {
    cd "$PROJECT_DIR"
    do_init

    log "Building iOS (simulator, debug)..."
    cargo tauri ios build --debug

    log "iOS build complete!"
    log "To run on simulator: cargo tauri ios dev"
}

# ---------------------------------------------------------------------------
# android — build and optionally run on Android emulator
# ---------------------------------------------------------------------------
do_android() {
    cd "$PROJECT_DIR"
    do_init

    log "Building Android (aarch64, debug)..."
    cargo tauri android build --target aarch64 --debug

    log "Android build complete!"
    log "APK location: $SRC_TAURI/gen/android/app/build/outputs/apk/"
    log "To run on emulator: cargo tauri android dev"
}

# ---------------------------------------------------------------------------
# capture — build, launch emulators, take screenshots
# ---------------------------------------------------------------------------
do_capture() {
    local CAPTURE_DIR="$PROJECT_DIR/screenshots"
    mkdir -p "$CAPTURE_DIR"

    log "=== Capturing GUI rendering on all platforms ==="

    # Desktop (Tauri)
    log "--- Desktop build ---"
    cd "$PROJECT_DIR"
    cargo tauri build --debug 2>&1 | tail -5
    log "Desktop build done."

    # iOS Simulator
    if command -v xcrun &>/dev/null; then
        log "--- iOS Simulator ---"
        do_init

        # Boot simulator
        local SIM_UDID
        SIM_UDID=$(xcrun simctl list devices available -j | \
            python3 -c "import json,sys; devs=json.load(sys.stdin)['devices']; \
            iphones=[d for vs in devs.values() for d in vs if 'iPhone' in d.get('name','') and d.get('isAvailable')]; \
            print(iphones[0]['udid'] if iphones else '')" 2>/dev/null || true)

        if [ -n "$SIM_UDID" ]; then
            log "Booting iOS Simulator: $SIM_UDID"
            xcrun simctl boot "$SIM_UDID" 2>/dev/null || true

            log "Building iOS for simulator..."
            cargo tauri ios dev --no-watch &
            local IOS_PID=$!
            sleep 15  # Wait for app to launch

            log "Capturing iOS screenshot..."
            xcrun simctl io "$SIM_UDID" screenshot "$CAPTURE_DIR/ios_screenshot.png"
            log "Saved: $CAPTURE_DIR/ios_screenshot.png"

            kill $IOS_PID 2>/dev/null || true
        else
            warn "No iOS simulator available. Skipping iOS capture."
        fi
    else
        warn "Xcode not found. Skipping iOS."
    fi

    # Android Emulator
    if [ -n "${ANDROID_HOME:-}" ] && [ -f "$ANDROID_HOME/emulator/emulator" ]; then
        log "--- Android Emulator ---"
        do_init

        # Find an AVD
        local AVD_NAME
        AVD_NAME=$("$ANDROID_HOME/emulator/emulator" -list-avds | head -1)

        if [ -n "$AVD_NAME" ]; then
            log "Starting Android emulator: $AVD_NAME"
            "$ANDROID_HOME/emulator/emulator" -avd "$AVD_NAME" -no-audio -no-window &
            local EMU_PID=$!

            log "Waiting for emulator to boot..."
            "$ANDROID_HOME/platform-tools/adb" wait-for-device
            sleep 10

            log "Building and installing Android APK..."
            cargo tauri android dev --no-watch &
            local ANDROID_PID=$!
            sleep 20

            log "Capturing Android screenshot..."
            "$ANDROID_HOME/platform-tools/adb" exec-out screencap -p > "$CAPTURE_DIR/android_screenshot.png"
            log "Saved: $CAPTURE_DIR/android_screenshot.png"

            kill $ANDROID_PID 2>/dev/null || true
            kill $EMU_PID 2>/dev/null || true
        else
            warn "No Android AVD found. Create one in Android Studio first."
        fi
    else
        warn "Android emulator not found. Skipping Android."
    fi

    log "=== Screenshot capture complete ==="
    log "Screenshots saved in: $CAPTURE_DIR/"
    ls -la "$CAPTURE_DIR/"
}

# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
case "${1:-help}" in
    setup)   do_setup ;;
    ios)     do_ios ;;
    android) do_android ;;
    both)    do_ios; do_android ;;
    capture) do_capture ;;
    init)    do_init ;;
    help|*)
        echo "Usage: $0 {setup|ios|android|both|capture|init}"
        echo ""
        echo "Commands:"
        echo "  setup    Install Rust targets, Tauri CLI, verify SDK/Xcode"
        echo "  init     Initialize Android and iOS Tauri projects"
        echo "  ios      Build for iOS simulator"
        echo "  android  Build for Android (aarch64)"
        echo "  both     Build both iOS and Android"
        echo "  capture  Build all, launch emulators, capture screenshots"
        echo ""
        echo "Prerequisites:"
        echo "  macOS with Xcode (for iOS)"
        echo "  Android Studio with SDK + NDK (for Android)"
        echo "  Rust (rustup), Node.js"
        ;;
esac
