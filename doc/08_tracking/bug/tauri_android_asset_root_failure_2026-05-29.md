# Tauri Android Asset Root Failure

Date: 2026-05-29

## Summary

The Android Tauri shell previously installed and launched on the local emulator,
but the WebView content did not render the bundled UI. The visible screen
reported:

`Failed to request http://tauri.localhost/: error sending request for url (http://tauri.localhost/)`

Resolved on 2026-05-29 by restoring the complete Tauri source tree and
rebuilding the Android APK from source with the Android SDK environment set.

## Evidence

- Emulator: `simple-pixel-8-api36`, serial `emulator-5554`, Android 16 / API 36,
  x86_64.
- APK: `tools/tauri-shell/src-tauri/gen/android/app/build/outputs/apk/x86_64/debug/app-x86_64-debug.apk`.
- Install and launch succeeded:
  - `adb -s emulator-5554 install -r .../app-x86_64-debug.apk`
  - `adb -s emulator-5554 shell monkey -p com.simple.ui -c android.intent.category.LAUNCHER 1`
  - `adb -s emulator-5554 shell pidof com.simple.ui`
- Screenshot evidence:
  - `/tmp/simple-tauri-android-screenshot.png`
  - `/tmp/simple-tauri-android-screenshot-after-index.png`

## Attempted Fix

Added `tools/tauri-shell/src-tauri/gen/android/app/src/main/assets/index.html`
and tested a patched signed APK created from the existing x86_64 debug APK.
The app still displayed the same `http://tauri.localhost/` request failure.

## Historical Assessment Before Source Restore

Before the complete Tauri source tree was restored and rebuilt, the blocker was
not Android SDK/emulator availability. It was Tauri Android asset/protocol
routing for the root URL. The generated shell appeared to request
`http://tauri.localhost/`, but the old packaged/runtime path did not serve that
root request successfully.

The current checkout does not contain a complete source Tauri project. The
tracked tree under `tools/tauri-shell/src-tauri/` contains generated Android
files and build artifacts, but not `Cargo.toml`, `build.rs`, `tauri.conf.json`,
`src/lib.rs`, `src/main.rs`, or `../dist/index.html`. Those files are visible in
history before commit `a8569120c1`, which deleted them. The existing APK/native
library was therefore built from a previous source state, and adding
`app/src/main/assets/index.html` to the generated Android tree alone cannot
update the Rust/Tauri embedded asset table in
`libsimple_tauri_shell_lib.so`.

## Required Fix Applied

Restore or regenerate the complete Tauri source project, rebuild the Android
native library/APK so the embedded asset table includes the app root, then rerun
install, launch, screenshot, and logcat evidence on `emulator-5554`.

## Resolution Evidence

- Build environment:
  - `ANDROID_HOME=/usr/lib/android-sdk`
  - `ANDROID_SDK_ROOT=/usr/lib/android-sdk`
- Build commands:
  - `npm install --no-audit --no-fund`
  - `npm run prepare:dist`
  - `npx tauri android build --apk --target x86_64`
  - `npx tauri android build --debug --apk --target x86_64`
- Fresh APKs:
  - `tools/tauri-shell/src-tauri/gen/android/app/build/outputs/apk/universal/release/app-universal-release-unsigned.apk`
  - `tools/tauri-shell/src-tauri/gen/android/app/build/outputs/apk/universal/debug/app-universal-debug.apk`
- Emulator:
  - `simple-pixel-8-api36`, serial `emulator-5554`
- Install and launch:
  - `adb -s emulator-5554 install -r tools/tauri-shell/src-tauri/gen/android/app/build/outputs/apk/universal/debug/app-universal-debug.apk`
  - `adb -s emulator-5554 shell monkey -p com.simple.ui -c android.intent.category.LAUNCHER 1`
  - `adb -s emulator-5554 shell pidof com.simple.ui` returned PID `4275`
- Screenshot:
  - `/tmp/simple-tauri-android-rebuild-2026-05-29.png`
  - Shows the bundled Simple UI dashboard/demo mode, not the previous
    `Failed to request http://tauri.localhost/` failure page.
- Logcat:
  - `/tmp/simple-tauri-android-rebuild-2026-05-29.log`
  - Contains `Page loaded`, `window.__TAURI__: object`, `Tauri API found`,
    `Found core.invoke`, `Listening for 'render' events`, and
    `Demo UI activated (subprocess unavailable)`.

Status: asset-root failure fixed. The remaining warning is expected for this
build because no Android-compatible Simple runtime was bundled; the shell falls
back to demo mode.
