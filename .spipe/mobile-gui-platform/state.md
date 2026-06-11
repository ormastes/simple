# Feature: mobile-gui-platform

## Raw Request
> spipe dev skill, impl mobile gui with metal/vulkan process, drawing backend, and mobile (table/phone) layout in addition to desktop app layout. research web and how layout change to support table, phone, desktop app to support and change layout.. make it production level gui platform both mobile and desktop. check existing platforms. with sonnet make parallel agents to impl it. (however currently tauri gui is supported it should share interface and updated if needed)

## Task Type
feature

## Refined Goal
Make the Simple GUI a production-grade cross-form-factor platform: one widget/scene source renders through the native drawing backends (Engine2D Metal on macOS/iOS, Vulkan on Linux/Android) AND the Tauri webview backend, with a shared device-profile layer (phone / tablet / desktop + orientation) that selects adaptive layout variants at runtime, grounded in research of how existing platforms (web media queries, iOS size classes, Android window size classes, Flutter adaptive) restructure layout across form factors.

## Acceptance Criteria
- AC-1: Research doc exists at `doc/01_research/ui/responsive_layout/` covering (a) how web/iOS/Android/Flutter/desktop toolkits adapt layout across phone/tablet/desktop (breakpoints, size classes, adaptive navigation patterns) and (b) a survey of existing production GUI platforms with the patterns Simple adopts. Verifiable: file present, cites concrete platform mechanisms, ends with adopted-design decisions.
- AC-2: `DeviceClass` (phone/tablet/desktop) + `FormFactorProfile` layer in `src/lib/common/ui/` (extending `profile.spl`), derived from viewport size, touch capability, and platform hint; unit spec green covering boundary widths, orientation flips, and touch/no-touch.
- AC-3: Adaptive layout variants: a widget tree/builder can declare per-device-class layout (e.g., bottom-nav vs nav-rail vs sidebar; single vs multi column) and the layout engine re-selects on viewport resize/orientation change. Unit spec green proving the SAME tree yields phone/tablet/desktop layouts at 3 canonical viewports.
- AC-4: Native drawing-backend path: an adaptive responsive showcase app renders via Engine2D through the Metal backend on macOS with GPU evidence (gpu_frame_complete probe) at phone/tablet/desktop viewports; Vulkan backend path validated via engine2d strict-selection/probe spec (GPU hardware proof only where a Vulkan device exists).
- AC-5: Tauri backend shares the same interface: `generate_css` media breakpoints and the Tauri `RenderBackend` consume the SAME FormFactorProfile thresholds (single source of truth, no duplicated 600/1200 constants); Tauri mobile constructors map touch→DeviceClass. Spec green proving threshold parity between native layout selection and generated CSS.
- AC-6: Check app + gate: `responsive_showcase` check app renders the adaptive tree at 3 viewports with framebuffer/draw-IR evidence; check script wired and green; spec files registered so `bin/simple test` covers AC-2/3/5.

## Scope Exclusions
- No new on-device Android/iOS deployment in this pipeline (Tauri mobile lanes already proven 2026-06-06); only interface sharing/updating.
- No foldable/multi-window mobile, no gesture recognizers (swipe/pinch), no high-DPI asset pipeline — record as follow-ups if touched.
- No new GPU backends; reuse existing engine2d backend set.

## Research (phase 2 output)
- AC-1 doc: `doc/01_research/ui/responsive_layout/responsive_layout_platforms.md` (web/iOS/Android/Flutter/desktop survey + adopted design).
- Adopted design highlights: DeviceClass(Phone/Tablet/Desktop) selects INTERACTION policy only (touch target 44pt Apple / 48dp elsewhere / ~32px dense desktop, density, hover); window-scoped SizeClass selects layout STRUCTURE. Width breakpoints move 600/1200 → Material-aligned 600/840; height classes 480/900 added (landscape-phone → rail instead of bottom bar). Mobile-first min-width CSS. First scaffold: AdaptiveNavScaffold (bottom bar Compact → rail Regular → sidebar Expanded); second: ListDetailScaffold.
- Repo findings: Vulkan FFI is REAL (`ash`-based, feature-gated `vulkan` in src/compiler_rust/runtime; rt_vulkan_init at vulkan_graphics_runtime_core.rs:154; probe returns Unavailable w/o device, strict mode errors instead of silent fallback per sffi_dispatch.spl:57-75). No DeviceClass exists anywhere. CSS breakpoints hand-duplicated at src/app/ui.web/html.spl:2134/2150 (responsive_css). TauriBackend.touch_supported at src/app/ui.tauri/backend.spl:61, new_mobile/new_android/new_ios at :79-91. Existing responsive infra: profile.spl (SizeClass/Orientation/Breakpoints/LayoutProfile/ProfileResolver), builder.spl:560-630 (adaptive_stack/adaptive_sidebar/adaptive_grid/responsive/with_responsive_layout).

## Architecture / API Contract (phase 3 output)
- `src/lib/common/ui/form_factor.spl` (NEW):
  - `enum DeviceClass: Phone | Tablet | Desktop` with `to_wire() -> text` (lowercase).
  - `fn detect_device_class(platform: text, touch: bool, shortest_side: i32) -> DeviceClass` — desktop OS (macos/linux/windows) and not touch → Desktop; touch: shortest_side >= 600 → Tablet else Phone; unknown+no-touch → Desktop.
  - `struct FormFactorProfile: device: DeviceClass, layout: LayoutProfile, touch: bool, platform: text`
  - `fn compute_form_factor(viewport: Viewport, platform: text, touch: bool) -> FormFactorProfile`
  - Policy: `fn min_touch_target(device: DeviceClass, platform: text) -> i32` (44 apple-touch, 48 other-touch, 32 desktop); `fn supports_hover(device) -> bool`; `fn density_spacing(device) -> i32`.
- `profile.spl` (EDIT): `default_breakpoints()` → `Breakpoints(compact_max: 600, regular_max: 840)`; add `height_breakpoints() -> Breakpoints(480, 900)`; `compute_profile`/`ProfileResolver.update` classify vertical axis with height breakpoints. Terminal breakpoints unchanged.
- `src/lib/common/ui/adaptive_scaffold.spl` (NEW): `struct NavItem(id, label, icon, action)`; `fn adaptive_nav_scaffold(id, items: [NavItem], content: WidgetNode, ff: FormFactorProfile) -> WidgetNode` — width Compact → bottom nav (EXCEPT height Compact landscape → rail); Regular → nav rail; Expanded → sidebar. `fn list_detail_scaffold(id, list, detail, ff, show_detail: bool) -> WidgetNode` — two panes at Expanded, single pane below. Node ids/kinds must be assertable (e.g. prop nav_pattern=bottom|rail|sidebar).
- `src/app/ui.web/html.spl` (EDIT): `responsive_css(bp: Breakpoints)` interpolates bp values (mobile-first min-width form), generate_css passes `default_breakpoints()` — NO literal 600/840/1200 strings.
- `src/app/ui.tauri/backend.spl` (EDIT): `fn device_class(width: i32, height: i32) -> DeviceClass` on TauriBackend from touch_supported (+ platform hint field if needed).
- Check app: `examples/06_io/ui/responsive_showcase_gui.spl` (+ metal variant) rendering adaptive_nav_scaffold at 390x844 (phone), 1024x768 (tablet), 1440x900 (desktop) via engine2d; PPM evidence; script `scripts/check/check-responsive-showcase-evidence.shs`.

## Spec Files (phase 4)
- test/01_unit/lib/common/ui/form_factor_spec.spl (AC-2: boundaries 599/600/839/840, orientation flip, touch/no-touch, platform hints, wire strings, height classes)
- test/01_unit/lib/common/ui/adaptive_scaffold_spec.spl (AC-3: same items/content at 3 canonical viewports → bottom/rail/sidebar; landscape-phone → rail; resize re-selection via ProfileResolver; list_detail collapse)
- test/01_unit/lib/common/ui/responsive_css_parity_spec.spl (AC-5: generated CSS breakpoints == default_breakpoints() values; custom bp reflected; no stale 1200 media query; tauri touch→DeviceClass)

## Phase
spec (specs being written per slice, TDD inside each implementation agent)

## Log
- dev: Created state file with 6 acceptance criteria (type: feature), 2026-06-12.
- research: AC-1 doc written; Vulkan FFI verified real; seams pinned (2026-06-12).
- design: API contract above; breakpoint migration 600/1200→600/840 approved by research rationale (iPad-landscape/WinUI expanded zone) (2026-06-12).
- implement-C: responsive_css(bp) single-source breakpoints, boundary-exact media queries; parity spec green (6 tests).
- implement-A: form_factor + breakpoints 600/840 + height classes 480/900; spec green (29 tests); swept existing specs: test/01_unit/app/ui/profile_spec.spl updated 2 classify boundary tests (1199→839, 1200→840); 3 pre-existing failures unrelated to breakpoint change remain.
