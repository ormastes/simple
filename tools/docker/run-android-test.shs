#!/bin/bash
set -e

echo "[android-test] Starting Xvfb..."
Xvfb :99 -screen 0 1280x720x24 >/dev/null 2>&1 &
export DISPLAY=:99
sleep 1

echo "[android-test] Building APK..."
cd /app/tools/tauri-shell
cargo tauri android build --debug 2>&1 | tail -5
APK_PATH="/app/tools/tauri-shell/src-tauri/gen/android/app/build/outputs/apk/universal/debug/app-universal-debug.apk"

echo "[android-test] Starting Android emulator (headless)..."
cd /app
$ANDROID_HOME/emulator/emulator -avd test_device -no-window -no-audio -gpu swiftshader_indirect -no-boot-anim -no-snapshot &
EMU_PID=$!

echo "[android-test] Waiting for emulator to boot..."
$ANDROID_HOME/platform-tools/adb wait-for-device
# Wait for boot completion
timeout 120 sh -c 'while [ "$(adb shell getprop sys.boot_completed 2>/dev/null)" != "1" ]; do sleep 2; echo -n "."; done'
echo ""
echo "[android-test] Emulator booted!"

echo "[android-test] Installing APK..."
$ANDROID_HOME/platform-tools/adb install "$APK_PATH" 2>&1

echo "[android-test] Launching app..."
$ANDROID_HOME/platform-tools/adb shell am start -n com.simple.ui/.MainActivity 2>&1

echo "[android-test] Waiting for app to render..."
sleep 5

echo "[android-test] Taking screenshot..."
$ANDROID_HOME/platform-tools/adb exec-out screencap -p > /output/android_screenshot.png 2>/dev/null
echo "[android-test] Screenshot saved to /output/android_screenshot.png"
ls -lh /output/android_screenshot.png

echo "[android-test] App logs:"
$ANDROID_HOME/platform-tools/adb logcat -d -s "tauri-shell:*" "SimpleUI:*" "WebView:*" 2>&1 | tail -20

echo "[android-test] Done!"
kill $EMU_PID 2>/dev/null
