<!-- codex-research -->
# Local Research: Android and iOS App Support

Date: 2026-04-24

Related domain research: `doc/01_research/domain/mobile_android_ios_app_support_2026-04-24.md`

## Executive Summary

The repo has a credible architectural seam for future Android and iOS app support, but that seam is currently at the shared UI session and host-backend layer, not at a finished mobile compiler/runtime target lane.

The strongest local fit is:

- reuse `UISession` and the typed widget/event model as the shared app model
- add Android/iOS host backends beside existing hosted backends
- use native platform shells or exported C ABI bridges before attempting a full repo-native mobile runtime stack

Current evidence shows mobile work exists mostly in `tools/tauri-shell`, while first-class Android/iOS support is not yet present in the main hosted platform matrix.

## Existing Reuse Points

### 1. Shared UI Session Is the Best Reuse Boundary

The cleanest reuse boundary for phone and tablet UI is the existing shared UI stack:

- `src/lib/common/ui/session.spl`
- `src/lib/common/ui/widget.spl`
- `src/lib/common/ui/backend.spl`
- `doc/07_guide/ui_stack_guide.md`

Why this matters:

- one widget tree
- one typed event model
- backend-specific rendering
- capability and lifecycle plumbing already exist

The backend trait already models cross-target concerns such as event polling, viewport size, mouse support, color support, image support, and touch support. That is the right abstraction level for phone/tablet adaptation.

### 2. Touch and Window Concepts Already Exist

The local UI stack is not desktop-only:

- `RenderBackend.supports_touch()` exists in `src/lib/common/ui/backend.spl`
- `UISession` records touch-oriented events in `src/lib/common/ui/session.spl`
- window and surface registries already exist in `src/lib/common/ui/access.spl` and `src/lib/common/ui/surface.spl`

This means mobile support does not need a brand-new app model. It needs backend and host-shell work.

### 3. Shared WM Stack Was Designed for More Host Backends

Architecture docs show the compositor/window-manager stack was explicitly designed for multiple host environments:

- `doc/04_architecture/shared_wm_stack.md`
- `src/os/compositor/host_compositor_entry.spl`

The host entry enum currently includes desktop/web-oriented backends such as:

- `Cocoa`
- `Win32`
- `Browser`
- `Electron`
- `WebCanvas`
- `Tui`

There is no Android or iOS backend variant today. That is the clearest missing local seam.

## Existing Mobile Evidence

### 1. Mobile Tooling Exists in Tauri Shell

There is real Android/iOS-related scaffolding under:

- `tools/tauri-shell/scripts/mobile-setup.shs`
- `doc/07_guide/testing/tauri_backend_container_testing.md`

This proves the repo has already explored mobile packaging and shell setup. But it is not the same as first-class platform support in the core hosted runtime.

### 2. Shared-WM Mobile Path Is Not Wired Through

The current Tauri app path routes shared-WM mode through a browser backend rather than a native mobile backend:

- `src/app/ui.tauri/async_app.spl`

The testing guide also documents Android container testing while noting that the Tauri shell rejects shared-WM mode today. That makes Tauri a prototype/bootstrap path, not the final architectural answer.

## FFI and Embedding Fit

The repo already has a strong foreign-function seam:

- `doc/07_guide/ffi/sffi.md`
- `src/compiler/80.driver/driver.spl`
- `src/compiler/80.driver/driver_public_api.spl`

Why this matters for mobile:

- Android host code can call exported C ABI through JNI/Kotlin glue
- iOS host code can call exported C ABI through Objective-C/Swift glue
- this avoids forcing the language to own native lifecycle and store packaging immediately

For near-term mobile support, shared-library output plus exported C ABI is a more realistic bridge than attempting immediate end-to-end app generation.

## Current Gaps

### 1. Platform Matrix Gap

The main hosted platform documentation currently lists hosted support around Linux/macOS/Windows/FreeBSD, not Android/iOS:

- `doc/07_guide/platform/platforms.md`

That means Android/iOS support should be treated as new platform work, not an extension of a supported lane.

### 2. No First-Class Mobile Backend Kind

Missing pieces include:

- Android host backend
- iOS host backend
- mobile lifecycle integration
- mobile input adaptation
- mobile packaging and signing pipeline owned by the main build flow

### 3. GUI Rendering Path Is Still Desktop/Web Skewed

Today’s strongest rendering paths are:

- desktop host windows
- browser/web-host shells
- TUI

There is not yet a proven repo-native mobile compositor/input backend pair.

## Local Recommendation

The best local integration seam is:

1. extend `UISession` + shared WM host integration first
2. add `Android` and `iOS` host backend kinds in the host compositor entry path
3. prototype through existing Tauri/mobile tooling only where it speeds validation
4. use exported C ABI/shared-library output for native host embedding when platform-native shells are required

## Local Pitfalls

| Pitfall | Why it matters locally |
|---|---|
| Treating Tauri mobile scaffolding as finished mobile support | The core hosted stack still lacks Android/iOS backend kinds and native lifecycle integration |
| Starting with compiler target catalog work | The more immediate blocker is host/UI integration, not code generation in isolation |
| Forcing one cross-platform GUI abstraction too early | The repo has reusable UI state and event abstractions, but not yet a proven mobile renderer/input path |
| Ignoring native embedding | Existing SFFI/export infrastructure is one of the strongest local assets for mobile adoption |

