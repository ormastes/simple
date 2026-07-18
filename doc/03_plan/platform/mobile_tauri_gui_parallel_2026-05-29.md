# Mobile Tauri GUI Capability Parallel Note - 2026-05-29

## Scope

- Owned files: `src/app/ui.tauri/backend.spl`, `test/01_unit/app/ui/tauri_backend_spec.spl`.
- Avoided shared web render API, web pixel backend, browser renderer, and main restart docs.

## Finding

`TauriBackend.supports_touch()` was hard-coded to `false`, and the desktop Tauri capability list from the shared web render API also omits `Capability.Touch`. That is correct for the existing desktop Tauri target, but it incorrectly models Android and iOS Tauri WebViews.

## Decision

Keep `TauriBackend.new(port)` and `TauriBackend.new_with_policy(port, policy)` as desktop Tauri constructors with touch disabled. Add explicit mobile constructors:

- `TauriBackend.new_mobile(port)`
- `TauriBackend.new_android(port)`
- `TauriBackend.new_ios(port)`
- `TauriBackend.new_mobile_with_policy(port, policy)`

Mobile constructors set a backend-local `touch_supported` flag. `capabilities()` appends `Capability.Touch` only for those mobile instances, and `supports_touch()` returns the instance flag.

## Verification

Focused tests in `test/01_unit/app/ui/tauri_backend_spec.spl` now cover:

- desktop Tauri remains mouse/color/images/native dialog/notification capable and touch-disabled
- Android Tauri WebView is touch-capable
- iOS Tauri WebView is touch-capable

2026-05-29 continuation evidence:

- `SIMPLE_LIB=src timeout 60s bin/simple check src/app/ui.tauri/backend.spl test/01_unit/app/ui/tauri_backend_spec.spl test/01_unit/app/llm_dashboard/ios_mode_spec.spl test/01_unit/app/llm_dashboard/ios_css_spec.spl`
  passed.
- `SIMPLE_LIB=src timeout 60s bin/simple test test/01_unit/app/ui/tauri_backend_spec.spl --mode=interpreter --clean --format json`
  passed `6/6`.
- `SIMPLE_LIB=src timeout 60s bin/simple test test/01_unit/app/llm_dashboard/ios_mode_spec.spl --mode=interpreter --clean --format json`
  passed `4/4`.
- `SIMPLE_LIB=src timeout 60s bin/simple test test/01_unit/app/llm_dashboard/ios_css_spec.spl --mode=interpreter --clean --format json`
  passed `4/4`.

Source/platform evidence:

- Android Tauri asset-root failure is resolved after restoring the complete
  Tauri source tree and rebuilding the APK from source; see
  `doc/08_tracking/bug/tauri_android_asset_root_failure_2026-05-29.md`.
- `tools/tauri-shell/src-tauri/gen/apple/` is now present with generated
  Xcode project, Info.plist, LaunchScreen, assets, and native source.
- iOS simulator/device execution still requires an Apple host with `xcodebuild`
  and `simctl`; this Linux pass proves only source/contracts/generated output.

## 2026-06-26 renderer parity continuation

New aggregate wrapper:
`scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`.

Current evidence:

- Desktop production GUI/Web renderer parity source: pass via
  `build/production_gui_web_renderer_parity_evidence/evidence.env`.
- Tauri2 project contract: pass for `tools/tauri-shell` iOS and Android
  generated projects.
- iOS: pass on iPhone 17 Pro simulator via
  `scripts/check/check-tauri-ios-mobile-renderer-evidence.shs`; screenshot
  validation passed and logs include validator-backed Tauri render,
  WKWebView/iOS context, and Metal/CAMetalLayer markers with no failure marker.
- Android: pass. The arm64 `simple` runtime builds, is packaged into
  `lib/arm64-v8a/libsimple_mobile_runtime_exec.so`, and the rebuilt APK renders
  the mobile widget showcase through Tauri2 Android WebView.
- Android Vulkan: pass for the local host/emulator Vulkan translation lane. The
  evidence script leaves guest HWUI unchanged, starts the emulator with
  `-gpu host`, observes Apple M4 Vulkan markers in
  `build/tauri_android_mobile_renderer/emulator.out`, sees
  `[tauri-shell] render, html_len=` in logcat, validates the foreground
  `com.simple.ui` screenshot, and reports
  `tauri_mobile_renderer_parity_android_vulkan_log_status=pass`. Guest HWUI
  `skiavk`, `swiftshader`, and `lavapipe` remain crashing lanes on the local
  Pixel7 AVD and should not be recorded as the passing path.

The aggregate report now returns `tauri_mobile_renderer_parity_status=pass`.
