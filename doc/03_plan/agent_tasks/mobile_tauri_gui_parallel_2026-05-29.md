# Mobile Tauri GUI Capability Parallel Note - 2026-05-29

## Scope

- Owned files: `src/app/ui.tauri/backend.spl`, `test/unit/app/ui/tauri_backend_spec.spl`.
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

Focused tests in `test/unit/app/ui/tauri_backend_spec.spl` now cover:

- desktop Tauri remains mouse/color/images/native dialog/notification capable and touch-disabled
- Android Tauri WebView is touch-capable
- iOS Tauri WebView is touch-capable

2026-05-29 continuation evidence:

- `SIMPLE_LIB=src timeout 60s bin/simple check src/app/ui.tauri/backend.spl test/unit/app/ui/tauri_backend_spec.spl test/unit/app/llm_dashboard/ios_mode_spec.spl test/unit/app/llm_dashboard/ios_css_spec.spl`
  passed.
- `SIMPLE_LIB=src timeout 60s bin/simple test test/unit/app/ui/tauri_backend_spec.spl --mode=interpreter --clean --format json`
  passed `6/6`.
- `SIMPLE_LIB=src timeout 60s bin/simple test test/unit/app/llm_dashboard/ios_mode_spec.spl --mode=interpreter --clean --format json`
  passed `4/4`.
- `SIMPLE_LIB=src timeout 60s bin/simple test test/unit/app/llm_dashboard/ios_css_spec.spl --mode=interpreter --clean --format json`
  passed `4/4`.

Source/platform evidence:

- Android Tauri asset-root failure is resolved after restoring the complete
  Tauri source tree and rebuilding the APK from source; see
  `doc/09_bugs/tauri_android_asset_root_failure_2026-05-29.md`.
- `tools/tauri-shell/src-tauri/gen/apple/` is now present with generated
  Xcode project, Info.plist, LaunchScreen, assets, and native source.
- iOS simulator/device execution still requires an Apple host with `xcodebuild`
  and `simctl`; this Linux pass proves only source/contracts/generated output.
