<!-- codex-design -->
# Tiny UI/Web/WM system test plan

## Scope and environment

This plan covers the retained Tiny Web/GUI host implementation and the
fail-closed optional-module/Vulkan, RV32, and size evidence boundaries. It does
not promote host source inspection to device, physical-input, allocator, or
closure evidence. Runtime execution requires a qualification receipt for a
pure-Simple self-hosted binary; the Rust seed is excluded.

Execution order is focused Web/GUI unit specs, Tiny browser integration, the
nine-scenario system SSpec, docgen, `sspec-maintain`, then the static delivery
guards. Any nonzero/signal exit, assertion failure, missing receipt, missing
scenario, stale mirror, or executable spec under `doc/06_spec` fails closed.

## Traceability

| Gate | Requirements | Evidence |
|---|---|---|
| H0 bounded core | REQ-003, 006, 007, 014, 015; NFR-004, 009-012 | pane/clip/hit, ABI, stream validation, overflow unit specs |
| H0-A retained arenas | REQ-003, 004, 005; NFR-004, 010-012 | twelve constructor-owned backing stores, logical counts, reset/reuse counters, render/navigation/edit/wheel loop |
| H1 differential | REQ-004, 005, 012 | normalized FTXUI cell and litehtml layout fixtures |
| H2 Tiny TUI | REQ-003, 004 | typed TUI captures and focus/action receipts |
| H3 host browser | REQ-001-006, 009, 011, 015 | software pixels, popup, focus/capture, scroll, navigation |
| H4 strict Vulkan | REQ-010; NFR-007 | device identity, submit/readback, explicit unavailable failure |
| R0 build/boot | REQ-011; NFR-008 | target/profile/closure hashes and boot receipt |
| R1 headless | REQ-003-006, 011 | RGB565 checksum, non-background count, state-changing input |
| R2 fullscreen | REQ-002, 011 | exact output bounds, present receipt, framebuffer capture |
| R3 input | REQ-002, 005, 011 | physical keyboard/pointer focus, text, scroll, capture |
| R4 modules | REQ-007-010, 014 | optional load, ABI rejection, base-without-pack proof |
| S0 size | REQ-008, 013; NFR-001-006 | ELF/PT_LOAD/map/symbol/dependency reports |

## Executable spec

Path: `test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl`

The frozen interfaces and B-10 through B-14 source repairs now exist. The executable source uses real host assertions and explicit `fail(...)` rows for unavailable H4/R4, R0-R4, and S0 evidence; those rows are completion blockers and are never skips or passing placeholders. The implementation lane uses these manual-visible steps:

1. `step("Boot the bounded Tiny browser profile")`
2. `step("Render the shared nested-pane page fullscreen")`
3. `step("Navigate controls with keyboard and pointer")`
4. `step("Scroll and clip nested content")`
5. `step("Open and dismiss a bounded popup")`
6. `step("Report backend, memory, dependency, and size evidence")`
7. `step("Initialize all bounded arenas before admitting runtime work")`
8. `step("Render and navigate repeatedly through retained logical extents")`
9. `step("Edit and wheel without rebuilding GUI or resolved-pane storage")`
10. `step("Compare allocation instrumentation with the initialization baseline")`

Reusable setup/checker helper names are frozen as `setup_tiny_browser_fixture`, `check_fullscreen_root`, `check_relative_panes`, `check_focus_and_capture`, `check_popup_damage`, `check_backend_honesty`, and `check_size_closure`. Any unavailable oracle remains `fail("tiny UI/Web/WM oracle not implemented")` until real evidence exists.

## Capture policy

- TUI: `build/test-artifacts/03_system/app/tiny_browser/feature/tiny_ui_web_wm/`.
- GUI: `doc/06_spec/image/03_system/app/tiny_browser/feature/tiny_ui_web_wm/`.
- RV32: typed binary/log/artifact receipts including frame checksum and QEMU command identity.
- Generated manual: `doc/06_spec/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.md` after the executable spec exists and docgen reports zero stubs.

The checked-in manual mirrors all nine source scenarios by hand because no admissible pure-Simple runner is available. Replace its fail-closed handoff notice only after the spec passes once, docgen reports zero stubs, and highest-capability manual review accepts the result.

## Quality gates

Use canonical matchers only. Every requirement needs a concrete observable, edge/error paths must include capacity, malformed input, ABI mismatch, missing backend, bad stream, and stale handle cases, and the generated manual must explain the primary flow without exposing setup mechanics.

## Complete requirement mapping

- H0: REQ-003, REQ-006, REQ-007, REQ-014, REQ-015; NFR-004, NFR-009, NFR-010, NFR-011, NFR-012.
- H0-A: REQ-003, REQ-004, REQ-005; NFR-004, NFR-010, NFR-011, NFR-012.
- H1/H2: REQ-004, REQ-005, REQ-012; NFR-009.
- H3: REQ-001, REQ-002, REQ-003, REQ-004, REQ-005, REQ-006, REQ-009, REQ-011, REQ-015; NFR-005, NFR-008, NFR-012.
- H4: REQ-010; NFR-007.
- R0/R1/R2/R3: REQ-001, REQ-002, REQ-003, REQ-005, REQ-006, REQ-011; NFR-004, NFR-008, NFR-009, NFR-010, NFR-011.
- R4: REQ-007, REQ-008, REQ-009, REQ-010, REQ-012, REQ-014, REQ-015; NFR-002, NFR-005, NFR-006, NFR-012.
- S0: REQ-008, REQ-013; NFR-001, NFR-002, NFR-003, NFR-005, NFR-006.

## Qualified-runtime resume

Resolve the admitted runtime from its qualification receipt, then execute each
unchanged criterion once in this order: focused Tiny Web/GUI unit specs, the
Tiny browser integration spec, the system SSpec, docgen, and the verification
guards named in the guide. Preserve the allocator receipt for the H0-A loop and
compare runtime allocation totals before and after render, navigation, edit,
and wheel. The source-level `allocation_count` is the fixed backing-store count,
not a substitute for runtime allocator evidence.

Current verdict: `TEST_BLOCKED`. This handoff did not execute those commands:
the known release binary crashes and the other binaries lack admission
receipts. Rust-seed results are excluded.
