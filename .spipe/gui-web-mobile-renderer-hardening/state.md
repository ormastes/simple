# Feature: GUI Web Mobile Renderer Hardening

## Raw Request
use spipe skill, harden simple gui, web renderer with chrome, electron backe metal rendering logs. and harden ios rendering. check event handling and rendering capture and performance and animation check also. improve coverage and system tests

## Task Type
feature

## Refined Goal
Harden the Simple GUI/Web/Tauri renderer evidence pipeline so production pass claims require real Chrome/Electron/Tauri capture, Metal-backed evidence where applicable, iOS/Android mobile renderer evidence, and structured event, performance, and animation coverage.

## Acceptance Criteria
- AC-1: Production GUI/web renderer parity evidence fails closed unless the renderer matrix, layout manifest, Tauri/Chrome surface capture, backend parity, font offload, raw Metal readback, and Electron event-routing evidence are all present and passing.
- AC-2: Electron event-routing evidence proves focus, window move, maximize, title-command keyboard input, body text input, pointer down/up, and no blur/tolerance.
- AC-3: Tauri mobile renderer parity evidence requires iOS WKWebView screenshot/layout evidence with Metal markers and Android WebView screenshot/layout evidence with Vulkan/skiavk markers.
- AC-4: Tauri mobile renderer parity evidence requires explicit live mobile event, capture provenance, performance, and animation proof before the full goal is marked complete.
- AC-5: Changed evidence wrappers have executable SSpec coverage and regenerated `doc/06_spec` manuals with `0 stubs`.
- AC-6: Matching `doc/07_guide`, `.codex/skills`, and `.claude/skills` process guidance documents the current verification contract.

## Scope Exclusions
No exclusion for the full goal; this state file records focused slices as they land and does not by itself prove every GUI/Web/mobile renderer surface is complete.

## Cooperative Review
N/A for this focused slice because the change is limited to existing shell evidence wrappers, SSpec contracts, and process docs.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- implementation: Added production GUI/web event-routing evidence to the parity wrapper and non-launching gate.
- implementation: Added Tauri mobile MDI proof validation for event routing, viewport capture, performance timer, animation frames, and CSS animation support on iOS and Android lanes.
- implementation: Added Electron production event-routing performance/animation proof to the live probe, production parity wrapper, non-launching gate, SSpec coverage, and process docs.
- implementation: Promoted Electron event-routing performance/animation rows through the aggregate GUI RenderDoc coverage audit and refreshed stale retained-performance/Metal production fixtures for the stricter gate.
- implementation: Hardened the live iOS WKWebView MDI renderer path after sync:
  delayed inline-shell reinjection now skips once MDI windows have opened,
  compact iOS logs can satisfy `openWindow` checks through raw JSON
  `windowId` markers, the iOS renderer wrapper launches the bundled MDI smoke
  entry, and MDI `openWindow`/`renderWindow` paths emit
  `[tauri-shell] render, html_len=` rows for the Metal render-log validator.
  Fresh live evidence passed in
  `build/tauri_ios_mobile_renderer_after_render_marker`: screenshot artifact,
  WKWebView/Metal render-log, MDI proof, event routing, capture, performance,
  latency, and animation statuses all reported `pass`.
- implementation: Hardened production/mobile wrapper evidence plumbing on the
  macOS host. `check-production-gui-web-renderer-parity-evidence.shs` now skips
  host-incompatible self-hosted Simple binaries during default discovery,
  classifies an explicit incompatible `SIMPLE_BIN` as
  `simple-bin-incompatible`, and emits single-line `jj --no-graph` source
  revisions. The mobile aggregate uses the same single-line source revision
  contract. SSpec coverage and regenerated manuals were updated for both
  wrappers.
- evidence: Live production parity without explicit `SIMPLE_BIN` selected
  `bin/release/aarch64-apple-darwin-macho/simple` and kept source revision
  single-line in `build/production_gui_web_renderer_parity_evidence/evidence.env`.
  The run still fails closed: layout manifest timed out, macOS Tauri/Chrome
  surface capture remains unavailable
  (`macos-wkwebview-snapshot-backend-unimplemented`,
  `chrome-live-capture-configured`), font offload is unavailable, and the
  macOS Metal render-log compare blocks on
  `pairwise-argb-diff,argb-source-evidence` even though raw Metal framebuffer
  readback and Electron/Chrome Metal browser backing pass.
- evidence: `BUILD_DIR=build/tauri_mobile_renderer_parity_after_mac_fix`
  mobile aggregate confirms iOS live WKWebView/Metal/MDI evidence passes
  (render log, screenshot, MDI event/capture/performance/animation all pass),
  Android is unavailable because `adb` is missing, and the aggregate correctly
  remains failed with `desktop-production-parity-source-not-pass` until the
  production parity blockers are resolved.
- implementation: Fixed the macOS Metal browser-backing ARGB mismatch by routing
  the Electron artifact capture through the existing offscreen OSR exact-sRGB
  path. The previous windowed `BrowserWindow.capturePage()` path produced
  deterministic display-compositor ICC-shifted fixture colors on macOS
  (`#2563eb` captured as `#3662e3`), while offscreen paint preserves the same
  sRGB solid colors as Chrome and Simple. The wrapper now emits
  `macos_metal_electron_capture_compositor_mode=offscreen-osr-exact-srgb` and
  `macos_metal_electron_capture_offscreen_paint=true`.
- evidence: `BUILD_DIR=build/macos-metal-browser-backing-after-offscreen-fix`
  `check-macos-metal-browser-backing-evidence.shs` passed with
  `macos_metal_pixel_comparison_status=pass`, all three pairwise diff rows
  `pass`, and identical Simple/Chrome/Electron ARGB checksums
  `329775811848360`. The strict Metal render-log compare then passed with
  `macos_metal_render_log_compare_status=pass` and
  `blocked_gate_count=0`. The production aggregate now forwards
  `production_gui_web_renderer_parity_metal_render_log_status=pass` and
  `production_gui_web_renderer_parity_metal_render_log_blocked_gate_count=0`,
  but the full production parity status remains failed on the existing
  `electron-layout-manifest-failed` timeout and surface/font evidence gaps.
