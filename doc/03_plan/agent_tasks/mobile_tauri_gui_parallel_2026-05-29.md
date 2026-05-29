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
