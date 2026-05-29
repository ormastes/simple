# GUI Renderer Restart Plan - 2026-05-29

## Goal

Complete the Simple GUI renderer restart across shared WM, Engine2D, web
rendering, TUI, mobile GUI apps, and browser checks without losing the
platform-specific proof status.

This plan extends `doc/03_plan/simple_gui_wm_restart_2026-05-28.md` and keeps
the work split so backend fixes, web parity, TUI checks, mobile readiness, and
browser verification can proceed in parallel.

## Parallel Lanes

- [ ] Engine2D CPU/Vulkan lane:
  prove CPU-backed rendering, compare against Vulkan-backed behavior where the
  host supports Vulkan, and fix CPU-backed rendering divergences in
  `src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl` or focused Engine2D
  specs.
- [x] Web/Tauri lane:
  compare pure Simple web rendering, browser-backed rendering, and Tauri v2
  backed rendering through `src/lib/common/ui/web_render_api.spl` and focused
  API specs; fix confirmed diffs in the shared web render API or pixel backend.
- [ ] UI-layer lane:
  prove the 2D UI layer can consume the Simple web rendering layer and the
  Tauri web rendering layer through the same artifact/capability contract.
- [x] TUI/Simple IDE lane:
  find and complete the editor TUI render completion plan, run focused TUI
  checks, and fix concrete Simple IDE TUI rendering gaps.
- [x] Android GUI lane:
  inspect Android Simple GUI app sources, contracts, and runnable host checks;
  fix host-verifiable Simple GUI code issues and record device/emulator gaps.
- [x] iOS GUI lane:
  fix source-level iOS app issues before device tests; on this Linux host,
  prove only source/contracts and record unavailable simulator/device evidence.
- [ ] Browser lane:
  run bounded browser or browser-contract checks for Simple web rendering and
  update evidence for any pure Simple versus browser-rendered differences.
- [ ] macOS ARM64 graphics lane:
  keep `doc/08_tracking/perf/graphics_2d_macos_arm64_2026-05-16.md` current
  with CPU, Metal, benchmark syntax, and unavailable-host evidence.

## Active Parallel Agents

- Engine2D CPU/Vulkan worker:
  `doc/03_plan/agent_tasks/engine2d_cpu_vulkan_parallel_2026-05-29.md`.
- Web/Tauri parity worker:
  `doc/03_plan/agent_tasks/web_tauri_parity_parallel_2026-05-29.md`.
- TUI/editor render worker:
  `doc/03_plan/agent_tasks/tui_editor_render_parallel_2026-05-29.md`.
- Android/iOS readiness explorer:
  read-only evidence for mobile source, docs, tests, and Linux-host limits.
- Browser/web explorer:
  read-only evidence for browser app, pure Simple web renderer, and bounded
  browser comparison checks.

## Completion Evidence Required

- [ ] Focused `bin/simple check` commands pass for every touched source/spec.
- [ ] Focused SPipe tests pass for Engine2D CPU behavior and shared web render
  API parity.
- [ ] Vulkan, Metal, Android emulator/device, iOS simulator/device, Cocoa, and
  browser-live evidence is either passed with exact commands or marked
  unavailable with the exact host/platform reason.
- [ ] Main restart plan links to the lane notes and distinguishes completed
  proof from Linux-host-limited contract checks.
- [ ] No final completion claim is made until every explicit lane above has
  direct evidence or an accepted platform-unavailable tracking entry.

## Current Linux Host Boundary

This host can run Simple interpreter checks, non-live SPipe specs, source
contracts, and some QEMU/browser checks if dependencies are installed. It
cannot directly prove macOS Cocoa, iOS simulator/device, or Apple Metal runtime
behavior. Android GUI can only be proven if the required Android SDK/emulator or
host-runnable contracts are present.

## Evidence Log

### 2026-05-29 Web/Tauri Lane

Files:
- `src/lib/common/ui/web_render_api.spl`
- `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
- `src/app/ui.browser/renderer.spl`
- `test/unit/app/ui/web_render_backend_api_spec.spl`
- `doc/03_plan/agent_tasks/web_tauri_parity_parallel_2026-05-29.md`

Result:
- Pure Simple browser URL rendering now builds a common
  `WebRenderRequest` before pixel rendering.
- The pixel backend default page helper now uses the shared request/full-HTML
  envelope instead of delegating directly to the low-level Simple Web default
  page helper.
- Focused coverage confirms the common URL request body matches the pixel
  facade URL request and that default page HTML uses the shared app envelope.

Verification:
```bash
SIMPLE_LIB=src bin/simple check src/lib/common/ui/web_render_api.spl src/lib/gc_async_mut/ui/web_render_pixel_backend.spl src/app/ui.browser/renderer.spl test/unit/app/ui/web_render_backend_api_spec.spl
SIMPLE_LIB=src bin/simple test test/unit/app/ui/web_render_backend_api_spec.spl --mode=interpreter --clean --format json
```

The check passed for all four files. The focused SPipe spec passed `7/7` in
2471 ms.

### 2026-05-29 Android/iOS Readiness Lane

Read-only mobile investigation found:
- Android generated Tauri output exists under
  `tools/tauri-shell/src-tauri/gen/android`, with APK artifacts in ignored
  build output.
- The generated Android config names product `Simple UI`, id `com.simple.ui`,
  Android min SDK `24`, and iOS min `14.0`.
- `tools/tauri-shell/src-tauri/gen/android/tauri.settings.gradle` contains a
  non-portable `/Users/ormastes/.cargo/...` path.
- `src/app/ui.tauri/backend.spl` currently reports `supports_touch() -> false`;
  mobile WebView touch needs a separate Android/iOS capability model.
- iOS dashboard mode, WKWebView auth bypass for `/agents`, no-store headers,
  and iOS CSS/meta injection are covered by source and unit specs.
- `tools/tauri-shell/src-tauri/gen/apple/` is absent although
  `doc/07_guide/mobile/ios_dev_guide.md` references committed/generated Apple
  output.

Verification:
```bash
SIMPLE_LIB=src bin/simple test test/unit/app/ui/tauri_backend_spec.spl --mode=interpreter --clean --format json
SIMPLE_LIB=src bin/simple test test/unit/app/llm_dashboard/ios_mode_spec.spl --mode=interpreter --clean --format json
SIMPLE_LIB=src bin/simple test test/unit/app/llm_dashboard/ios_css_spec.spl --mode=interpreter --clean --format json
```

Results on this Linux host:
- Tauri backend spec passed `4/4` in 635 ms.
- iOS mode spec passed `4/4` in 3166 ms.
- iOS CSS spec passed `4/4` in 51 ms.

Mobile Tauri capability fix:
- `src/app/ui.tauri/backend.spl` now keeps desktop Tauri touch-disabled while
  adding explicit `new_mobile`, `new_android`, `new_ios`, and
  `new_mobile_with_policy` constructors with `Capability.Touch`.
- `test/unit/app/ui/tauri_backend_spec.spl` now proves desktop remains
  touch-disabled and Android/iOS WebView instances are touch-capable.

Verification:
```bash
SIMPLE_LIB=src bin/simple check src/app/ui.tauri/backend.spl test/unit/app/ui/tauri_backend_spec.spl
SIMPLE_LIB=src bin/simple test test/unit/app/ui/tauri_backend_spec.spl --mode=interpreter --clean --format json
```

The check passed for both files. The focused Tauri spec passed `6/6` in
462 ms.

Remaining mobile platform blockers:
- Android APK install/launch/logcat evidence has not been run in this pass.
- iOS simulator/device proof is unavailable on this Linux host because
  `xcodebuild` and `simctl` are absent.
- Generated Android Gradle settings still contain a non-portable macOS path.
- `tools/tauri-shell/src-tauri/gen/apple/` is still absent while the iOS guide
  references generated Apple output.

### 2026-05-29 Browser/Web Lane

Read-only browser investigation found:
- Browser app entry and bridge paths:
  `examples/browser/mod.spl`, `examples/browser/render_adapter.spl`, and
  `examples/browser/ui_bridge.spl`.
- Pure Simple renderer paths:
  `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`,
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl`, and
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer.spl`.
- WM/browser integration paths:
  `src/os/compositor/browser_compositor_backend.spl`,
  `src/os/compositor/simple_web_window_renderer.spl`, and
  `src/os/compositor/web_render_surface.spl`.
- Browser comparison coverage exists in
  `test/system/wm_compare/html_compat_spec.spl`,
  `test/system/wm_compare/famous_site_corpus_spec.spl`,
  `test/perf/web_render_chrome/report_spec.spl`, and the baseline/fixture
  trees under `test/baselines/html_compat`,
  `test/fixtures/famous_site_corpus`, and
  `test/baselines/famous_site_corpus`.

Verification:
```bash
bin/simple test test/perf/web_render_chrome/report_spec.spl --mode=interpreter --clean --format json
bin/simple test test/system/wm_compare/html_compat_spec.spl --mode=interpreter --clean --format json
bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl --mode=interpreter --clean --format json --timeout 90
timeout 60s bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --mode=interpreter --no-cache
```

Results:
- Web render Chrome report spec passed `29/29`.
- HTML compatibility spec reported success with `11/11`, but the file entry
  also reported `Process exited with code 2`; track this as a harness/reporting
  inconsistency.
- Simple Web renderer spec failed `23/29`; likely failures are the final six
  background shorthand and attribute selector cases.
- Browser renderer spec exceeded a 60s bounded smoke check.

Remaining browser blockers:
- Fix or triage `simple_web_renderer_spec` background shorthand precedence and
  `[attr]`, `[attr=]`, `[attr^=]`, `[attr$=]` selector handling.
- Split or speed up `browser_renderer_spec` so web browser rendering has a
  bounded smoke check.
- Investigate JSON success/file-error mismatch in `html_compat_spec`.

### 2026-05-29 TUI/Simple IDE Lane

Files:
- `src/app/editor/tui_shell_panels.spl`
- `test/system/editor_tui_polish_spec.spl`
- `doc/03_plan/agent_tasks/tui_editor_render_parallel_2026-05-29.md`

Result:
- No exact `editor_tui_render_completion` artifact exists in the current repo.
- The closest active Simple IDE TUI render/polish spec was
  `test/system/editor_tui_polish_spec.spl`.
- `_tui_render_split_borders` no longer returns as a stub. It now renders
  vertical and horizontal ASCII borders for adjacent split pane rectangles and
  styles active-adjacent borders distinctly.
- The polish spec now points at the current editor file layout:
  `gui_shell_core.spl`, `gui_shell_render.spl`, and `tui_shell_panels.spl`.

Verification:
```bash
SIMPLE_LIB=src bin/simple check src/app/editor/tui_shell_panels.spl test/system/editor_tui_polish_spec.spl
SIMPLE_LIB=src bin/simple test test/system/editor_tui_polish_spec.spl --mode=interpreter --clean --format json
```

The check passed for both files. The focused Simple IDE TUI polish spec passed
`9/9` in 239 ms.

Remaining TUI blocker:
- Full recursive `SplitTree` ratio-driven layout remains broader editor layout
  work; this slice fixes the current adjacent-rect rendering path.

### 2026-05-29 Engine2D CPU/Vulkan Lane

Files:
- `test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl`
- `doc/03_plan/agent_tasks/engine2d_cpu_vulkan_parallel_2026-05-29.md`

Result:
- No concrete CPU-backed rendering divergence was found in focused checks.
- Added a compact core primitive parity baseline proving CPU rendering is
  deterministic and bit-exact against the software reference for clear,
  filled/outline rects, line, circle, filled circle, triangle, gradient, and
  clipping.

Verification:
```bash
SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl
SIMPLE_LIB=src bin/simple test test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl --mode=interpreter --clean --format json
```

The check passed for both files. The focused CPU/software parity spec passed
`2/2` in 1184 ms.

Additional worker evidence:
- Existing drawing, clip, mask, text, and primitives specs passed; primitives
  took about 90s and was flagged by the runner as a performance bug.
- `vulkaninfo --summary` completed and saw NVIDIA TITAN RTX, NVIDIA RTX A6000,
  and llvmpipe.

Remaining Engine2D blockers:
- Direct CPU-vs-Vulkan pixel parity remains blocked because an Engine2D Vulkan
  request probe fails with `function expects argument for parameter 'mode', but
  none was provided`.
- `test/integration/rendering/engine2d_backend_spec.spl` timed out at 60s
  during backend discovery/probing.
- `test/integration/rendering/engine2d_primitives_spec.spl` passes but is too
  slow for a quick restart smoke at about 90s.
