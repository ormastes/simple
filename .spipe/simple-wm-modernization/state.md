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
