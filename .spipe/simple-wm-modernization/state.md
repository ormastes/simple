# Feature: simple-wm-modernization

## Raw Request
$sp_dev impl do research deeply and impl >> for simple wm, os, to modern and user experience better than Mac OS. what animation or feature are needed find more.
to check quality of gui. how color checked? how each size and layout configured? research it. actually there is html/css theme. 
What to change?
any animation make more modern. find all, first apply and lets off when it is too verbose?
Add modern animation on windows manager.  
Open close like Mac animation.
widget support 
tranparency windows, command bar, task bar support
round scrollbar. round window. round widget. round taskbar.
left top window max, close, mini button.
Title bar icon, title, context, input textbox(browser, ide(vscode like))
make or find round icon for simple wm/os. make logic from icons to round modern icon converter if it is square icon.
animating bg
any other animations.

## Task Type
feature

## Refined Goal
Modernize the Simple Web WM shell with theme-driven rounded translucent window chrome, taskbar/icon treatment, and Mac-like open/minimize/close animations while keeping the server-authoritative WM protocol intact.

## Acceptance Criteria
- AC-1: Generated WM CSS defines explicit rounded window, widget, scrollbar, taskbar, titlebar, and icon styles using theme tokens instead of one-off inline styling.
- AC-2: Window creation, close, minimize, restore, and focus have CSS-driven motion states with a `prefers-reduced-motion` fallback.
- AC-3: Window chrome exposes left-top close/minimize/maximize controls plus icon and title regions that can be rendered consistently for browser/IDE-like surfaces.
- AC-4: Taskbar entries support rounded modern icons, running/minimized state, and translucent floating shell styling without requiring protocol schema changes.
- AC-5: The implementation is covered by focused static or unit checks that verify the generated CSS/JS contains the modern WM contracts.

## Scope Exclusions
Native compositor animations, new bitmap icon assets, and full visual parity with macOS are not required for the first implementation slice.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: feature).
- research: Added local/domain research and feature/NFR requirement options for the Simple Web WM modernization path.
- impl: Added generated CSS contracts for rounded translucent WM windows, taskbar, titlebar icon/context slots, round scrollbar/thumb styling, taskbar icons, animated background drift, and open/close/minimize/restore keyframes with reduced-motion fallback.
- impl: Added retained renderer and embedded-host lifecycle classes plus round icon helpers without changing the server-authoritative protocol schema.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter` passed 2/2.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl src/app/ui.web/wm_runtime_bridge.spl` passed; `node --check src/app/ui.web/wm.js` and `node --check src/app/ui.web/retained_renderer.js` passed.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md`; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added concise boolean SPipe assertions with `expect(condition)` and `expect_not(condition)`, plus SPIPE006 coverage for `.to_equal(true)` and `.to_equal(false)` boolean wrappers.
- verify: Simple-side checks passed for `test/unit/std/spec_expect_bool_shortcut_spec.spl`, `test/integration/app/spipe_quality_lint_spec.spl`, and `test/unit/app/ui/web_wm_modern_shell_spec.spl` after updating the WM spec to concise boolean assertions.
- verify: Rust lint parity tests passed for `test_spipe_false_boolean_wrapper_detected` and `test_spipe_concise_boolean_assertions_are_real_assertions`; existing warnings remain unrelated `last_value` unused-assignment warnings in interpreter block execution.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` after the concise assertion update; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added first-class WM titlebar command/input slot (`.wm-title-input` / `.wm-command-bar`) for browser/IDE-like surfaces, populated from existing command/url/path/workspace payload fields without changing the protocol schema.
- impl: Added widget/dialog pop-in motion, widget hover lift, stronger dock-like taskbar hover scale, and reduced-motion coverage for the new animated surfaces.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter` passed 3/3; `simple check` passed for `html.spl`, `wm_quality_contract.spl`, and the WM spec; `node --check` passed for `wm.js` and `retained_renderer.js`.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md`; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Strengthened WM GUI quality reporting with `contrast_ratio_x100`, extracted titlebar/window/input/taskbar pixel metrics, and `size_layout_configured` so color and layout quality are visible evidence instead of a single opaque boolean.
- verify: WM quality spec now asserts contrast ratio >= 4.50:1 equivalent (`contrast_ratio_x100 > 449`) plus concrete configured sizes: 38px titlebar, 200x120px minimum window, 140px title input minimum, and 26px taskbar icons. Focused WM spec and Simple checks passed.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` after the quality metric update; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added round modern icon normalization for taskbar, retained-surface titlebar, and embedded-host titlebar icons. URL/data/path icons are tagged as `square-to-round` and clipped through `.wm-icon-normalized-square`; text/app ids are converted into `.wm-icon-glyph` inside `.wm-round-icon`.
- verify: WM spec now checks the CSS converter contract and both JS helper paths (`_makeRoundIcon`, `_isImageIcon`, `square-to-round`, `glyph-to-round`). Focused WM spec, Simple checks, and `node --check` passed.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` after the round icon converter update; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added explicit WM motion verbosity control with `simple.wm.motion` localStorage support, `window.simpleWmSetMotion(preference)`, and `standard` / `reduced` / `off` normalization. Generated CSS now honors `:root[data-wm-motion=reduced]` and `:root[data-wm-motion=off]` in addition to OS-level `prefers-reduced-motion`.
- verify: WM spec now checks the motion verbosity CSS and browser-client preference hooks. Focused WM spec, Simple checks, and `node --check` passed.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` after the motion verbosity update; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added `generate_wm_modern_preview_html(theme)`, a standalone static WM visual preview fixture with representative modern windows, traffic-light controls, titlebar command inputs, rounded icon conversion, glass widgets, progress/status affordances, taskbar entries, and motion preference state.
- verify: WM spec now checks the standalone preview fixture markers and the quality contract includes `preview_fixture_ready`. Focused WM spec passed 4/4; Simple checks and `node --check` passed.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` after the preview fixture update; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added a global WM command palette shell contract (`.wm-command-palette`, input, list, command items, shortcuts) and included representative launcher/switch/settings actions in the modern preview fixture.
- verify: WM quality report now includes `command_palette_ready`, and the WM spec checks the generated CSS plus preview markers for the global command palette. Focused WM spec, Simple checks, and `node --check` passed.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` after the command palette update; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Made the command palette a live WM runtime feature in `wm.js`: it creates the palette DOM, opens with Cmd/Ctrl+K, supports Escape/ArrowUp/ArrowDown/Enter, filters commands, launches Simple IDE through the existing window command path, and exposes standard/reduced/off motion commands.
- verify: WM spec now checks runtime palette helpers and keyboard hook markers. Focused WM spec passed 4/4, focused Simple checks passed, and `node --check` passed for `wm.js` and `retained_renderer.js`.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` after the runtime command palette update; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added `write_wm_modern_preview_html(path, theme)` and `wm_modern_preview_evidence_report(path, theme)` so the modern WM preview can be emitted as a browser-loadable HTML artifact for screenshot/manual GUI review.
- verify: WM spec now writes `build/simple_wm_modern_preview.html`, verifies it exists through `rt_file_read_text`, checks preview markers, and checks the evidence report fields. Focused WM spec passed 5/5; focused Simple checks and `node --check` passed.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` after the preview artifact update; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Fixed WM preview visual layering by keeping the animated desktop background at z-index 0 and explicit windows at z-index 20; added `visual_layering_ready` to the WM quality contract.
- verify: Focused WM spec passed 5/5 after the layering regression assertion; Simple checks passed for `html.spl`, `wm_quality_contract.spl`, and `web_wm_modern_shell_spec.spl`; `node --check` passed for `wm.js` and `retained_renderer.js`.
- evidence: Captured `build/simple_wm_modern_preview.png` from `build/simple_wm_modern_preview.html` at 1440x900 with a 1000ms animation settle wait; visual evidence report written to `doc/09_report/simple_wm_modern_preview_2026-06-02.md`.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md`; docgen completed with 7 existing short-doc/link warnings and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Extended the pure Simple OS compositor scene HTML (`src/os/compositor/wm_scene.spl`) with modern WM markers: rounded translucent titlebar/panel chrome, left-top traffic lights, title icon/title/command/context slots, rounded command/taskbar surfaces, and gradient desktop background while preserving existing scene element kinds.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_scene_spec.spl --mode=interpreter` passed 20/20; `simple check` passed for `wm_scene.spl` and `wm_scene_spec.spl`; local SPIPE006 scan found no `to_equal(true/false)` in the touched WM scene path.
- verify: Adjacent unified renderer parity stayed green: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_unified_renderer_spec.spl --mode=interpreter` passed 9/9.
- docs: Regenerated `doc/06_spec/unit/os/compositor/wm_scene_spec.md`; modern chrome markers appear in the generated spec doc and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added OS-facing modern shell contracts in pure Simple: `ModernDockMetrics`, `modern_dock_metrics`, `dock_item_modern_icon_kind`, `modern_dock_summary`, `ModernTaskbarShellContract`, and `modern_taskbar_shell_summary` expose rounded translucent dock/taskbar sizing, round icon conversion, hover/motion timings, reduced motion, and disable-motion support for SimpleOS renderers.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_shell_contract_spec.spl --mode=interpreter` passed 3/3; `simple check` passed for `dock.spl`, `taskbar_shell.spl`, and the new spec; SPIPE006 scan found no boolean-wrapper assertions in the touched desktop shell path.
- docs: Generated `doc/06_spec/unit/os/desktop/modern_shell_contract_spec.md`; docgen completed with 7 short-doc/link warnings and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Wired the OS-facing modern shell contracts into actual output: `Dock.create` and `Dock.compute_position` now use `modern_dock_metrics()` for icon size, spacing, padding, height, and centering; `build_taskbar_shell_tree` annotates root, sections, pinned launchers, running windows, and tray items with modern rounded/translucent/motion/icon metadata.
- verify: Updated `modern_shell_contract_spec.spl` now checks created dock geometry and actual taskbar widget metadata; focused spec passed 5/5, `simple check` passed for the touched dock/taskbar/spec files, and the local SPIPE006 scan stayed clean.
- docs: Regenerated `doc/06_spec/unit/os/desktop/modern_shell_contract_spec.md`; the generated doc now includes the dock geometry and taskbar metadata scenarios, and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added host-neutral lifecycle motion helpers in `src/os/compositor/wm_action_applier.spl`: actions plus existing window state now derive `opening`, `closing`, `minimizing`, `restoring`, `focused`, `minimized`, or `idle` phases, matching CSS class names and standard/reduced/disable motion timing metadata without expanding every lifecycle window constructor.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_action_applier_spec.spl --mode=interpreter` passed 12/12; `simple check` passed for `wm_action_applier.spl` and its spec.
- docs: Regenerated `doc/06_spec/unit/os/compositor/wm_action_applier_spec.md`; docgen reported the existing applier manual as auto/stub but included the new lifecycle motion scenario, and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Wired lifecycle motion into rendered/inspectable compositor output with `lifecycle_windows_to_motion_wm_scene`; generated scene HTML now emits `.motion-window` nodes with `data-motion-phase`, `data-motion-class`, standard/reduced duration, and disable-motion attributes for opening/minimizing/restoring/closing-style states.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/os/compositor/wm_scene_spec.spl --mode=interpreter` passed 21/21; `simple check` passed for `wm_scene.spl` and its spec.
- docs: Regenerated `doc/06_spec/unit/os/compositor/wm_scene_spec.md`; docgen reported the existing scene manual as auto/stub but included the lifecycle motion projection scenario, and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Strengthened the combined modern WM readiness audit so release evidence now exposes the concrete GUI quality dimensions requested by the feature: color contrast, configured titlebar/window/input/taskbar sizes, command palette/title input readiness, visual layering, motion verbosity controls, round icon conversion, round scrollbars, and translucent shell status.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl` passed; `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter` passed 2/2; local SPIPE006 scan found no `to_equal(true/false)` in the touched readiness path.
- docs: Regenerated `doc/06_spec/unit/os/desktop/modern_wm_readiness_spec.md` with the expanded readiness assertions; docgen completed with the existing short-doc/link warnings and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added Web WM accessibility and interaction ergonomics to the quality contract: focus-visible rings for WM controls, expanded traffic-light hit areas, 44px command palette targets, ARIA-labelled preview traffic buttons, taskbar navigation labels, and command palette listbox/option roles.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl src/app/ui.web/wm_quality_contract.spl test/unit/app/ui/web_wm_modern_shell_spec.spl src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl` passed; focused Web WM spec passed 5/5; focused modern readiness spec passed 2/2; `node --check` passed for `wm.js` and `retained_renderer.js`; local SPIPE006 scan found no boolean-wrapper assertions in the touched WM path.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` and `doc/06_spec/unit/os/desktop/modern_wm_readiness_spec.md`; docgen completed with the existing short-doc/link warnings and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Brought the live Web WM runtime up to the same accessibility contract as the preview: runtime command palette lists now expose listbox/option/selected metadata; taskbar items expose navigation/button/tabindex labels and activate with Enter/Space; live and retained traffic-light buttons use descriptive close/minimize/maximize labels.
- verify: `node --check src/app/ui.web/wm.js` and `node --check src/app/ui.web/retained_renderer.js` passed; `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean` passed 5/5; focused readiness spec passed 2/2; `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- docs: Regenerated the Web WM and modern readiness mirrored spec docs after runtime accessibility parity; docgen completed with the existing short-doc/link warnings.
- impl: Added modern snap-assist window management to the Web WM: drag near left/right/top edges now shows a rounded translucent `.wm-snap-preview` drop zone, then sends existing move/resize commands with snapped half/full bounds on mouseup while keeping the server-authoritative protocol unchanged.
- impl: Added snap-assist and desktop-widget CSS/static preview evidence (`.wm-snap-preview`, `data-snap-zone`, `@keyframes wm-snap-pulse`, `.wm-desktop-widgets`, `@keyframes wm-widget-float`) with reduced/off motion coverage, plus `snap_assist_ready` and `desktop_widgets_ready` in the Web quality and combined readiness reports.
- verify: Focused checks passed for `html.spl`, `wm_quality_contract.spl`, `modern_wm_readiness.spl`, and their specs; `node --check src/app/ui.web/wm.js` passed; Web WM spec passed 5/5 and modern readiness spec passed 2/2 after snap-assist and desktop-widget coverage.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` and `doc/06_spec/unit/os/desktop/modern_wm_readiness_spec.md`; docgen completed with the existing short-doc/link warnings.
- impl: Added a Web WM window overview dialog opened from the command palette or `Cmd/Ctrl+O`; overview cards focus/restore DOM or Electron windows through the existing focus command path and remain covered by reduced/off motion CSS.
- verify: Focused checks passed again after adding `window_overview_ready`; Web WM spec passed 5/5, modern readiness spec passed 2/2, and docgen refreshed both mirrored manuals with existing warnings.
- impl: Added first-class desktop widget support to the Web WM runtime and preview: a translucent desktop widget shelf with clock, motion, and workspace widgets, command-palette toggle support, pointer event isolation, animated widget entry, collapsed state, and reduced/off motion coverage.
- impl: Added `desktop_widgets_ready` to the Web WM quality contract and combined SimpleOS modern WM readiness report so widget support is release-visible evidence instead of preview-only markup.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl src/app/ui.web/wm_quality_contract.spl test/unit/app/ui/web_wm_modern_shell_spec.spl src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl` passed; `node --check src/app/ui.web/wm.js` passed; Web WM spec passed 5/5 and modern readiness spec passed 2/2.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` and `doc/06_spec/unit/os/desktop/modern_wm_readiness_spec.md`; docgen completed with the existing short-doc/link warnings and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added a modern window overview surface to the Web WM runtime: command-palette and Cmd/Ctrl+O entry points, animated blurred full-screen overview, responsive window cards, active/minimized state labels, and existing focus command reuse so server-authoritative window state remains intact.
- impl: Added static preview and generated CSS evidence for the overview (`.wm-window-overview`, `.wm-overview-grid`, `.wm-overview-card`, `@keyframes wm-overview-in`) with reduced/off motion coverage, plus `window_overview_ready` in Web quality and combined OS readiness reports.
- verify: Focused checks passed for `html.spl`, `wm_quality_contract.spl`, `modern_wm_readiness.spl`, and their specs; `node --check src/app/ui.web/wm.js` passed; Web WM spec passed 5/5 and modern readiness spec passed 2/2 after overview coverage.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` and `doc/06_spec/unit/os/desktop/modern_wm_readiness_spec.md`; docgen completed with the existing short-doc/link warnings and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added a live WM control center for quick UX tuning: command-palette and Cmd/Ctrl+, entry points, glass control panel, motion standard/reduced/off controls, desktop widget toggle, and window overview launcher.
- impl: Added static preview/CSS evidence for the control center (`.wm-control-center`, `.wm-control-group`, `.wm-control-button`, `@keyframes wm-control-in`) and extended reduced/off motion selectors so the new panel also quiets down when motion is too verbose.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl src/app/ui.web/wm_quality_contract.spl test/unit/app/ui/web_wm_modern_shell_spec.spl src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl` passed; `node --check src/app/ui.web/wm.js` passed; Web WM spec passed 5/5 and modern readiness spec passed 2/2.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` and `doc/06_spec/unit/os/desktop/modern_wm_readiness_spec.md`; docgen completed with the existing short-doc/link warnings and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added a portable SimpleOS modern desktop affordance contract in `taskbar_shell.spl` for command palette, control center, window overview, desktop widgets, snap assist, and motion verbosity controls. The actual taskbar shell tree now carries matching `modern_*` metadata for OS renderers.
- impl: Added `os_affordances_ready` to the combined modern WM readiness report so Web-only affordances no longer count as complete unless the OS shell layer exposes the same portable metadata.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/os/desktop/taskbar_shell.spl test/unit/os/desktop/modern_shell_contract_spec.spl src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl` passed; boolean-wrapper scan found no `to_equal(true/false)` or literal boolean expectations in the touched OS files.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_shell_contract_spec.spl --mode=interpreter --clean` passed 7/7 and `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/unit/os/desktop/modern_wm_readiness_spec.spl --mode=interpreter --clean` passed 2/2.
- docs: Regenerated `doc/06_spec/unit/os/desktop/modern_shell_contract_spec.md` and `doc/06_spec/unit/os/desktop/modern_wm_readiness_spec.md`; docgen completed with existing short-doc/link warnings and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Strengthened GUI quality evidence with deterministic responsive layout metrics in the Web WM quality report: command palette max width, control center max width, desktop widget max width, overview card minimum width, and 44px touch target minimum. Added `responsive_layout_ready` to Web and combined readiness summaries.
- verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/wm_quality_contract.spl test/unit/app/ui/web_wm_modern_shell_spec.spl src/os/desktop/modern_wm_readiness.spl test/unit/os/desktop/modern_wm_readiness_spec.spl` passed; boolean-wrapper scan found no `to_equal(true/false)` or literal boolean expectations in the touched quality/readiness files.
- verify: Web WM spec passed 5/5 and modern readiness spec passed 2/2 with exact responsive metric assertions: palette 680px, control center 320px, desktop widget 260px, overview card 180px, touch target 44px.
- docs: Regenerated `doc/06_spec/unit/app/ui/web_wm_modern_shell_spec.md` and `doc/06_spec/unit/os/desktop/modern_wm_readiness_spec.md`; docgen completed with existing short-doc/link warnings and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Added SimpleOS compositor-rendered modern affordance surfaces to `wm_scene.spl`: translucent desktop widgets, WM control center, window overview cards, and a rounded snap preview. The combined readiness report now exposes `rendered_affordances_ready` so OS renderer evidence is checked separately from Web WM/static metadata.
- verify: Focused checks passed for `wm_scene.spl`, `wm_scene_spec.spl`, `modern_wm_readiness.spl`, and `modern_wm_readiness_spec.spl`; compositor scene spec passed 22/22 and modern readiness spec passed 2/2. Boolean-wrapper scan found no `to_equal(true/false)` or literal boolean expectations in the touched WM/OS files.
- docs: Regenerated `doc/06_spec/unit/os/compositor/wm_scene_spec.md` and `doc/06_spec/unit/os/desktop/modern_wm_readiness_spec.md`; docgen completed with existing short-doc/link warnings.
