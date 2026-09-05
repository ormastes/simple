# Tiny UI/Web/WM system specification

> **Fail-closed manual handoff (2026-08-16):** this Markdown mirrors the nine
> scenarios in the executable SSpec. It was updated by hand because no admitted
> pure-Simple self-hosted runtime is available. It is not docgen output and is
> not runtime PASS evidence. Current verdict: `TEST_BLOCKED`. Regenerate it only after the qualified runtime can
> execute the source.

Source: `test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl`

## Operator purpose

The specification checks the bounded fullscreen Tiny browser path from local
Web resources through layout, draw, software 2D, Tiny WM, and presentation. It
also keeps optional Vulkan/module, RV32, and size claims explicitly red until
their required artifacts exist.

## Preconditions

- Use an admitted pure-Simple self-hosted runtime and record its qualification
  receipt. The Rust bootstrap seed is never admissible evidence.
- Execute the system source once. Do not remove or skip fail-closed scenarios.
- Preserve captures under the paths recorded in the lane test plan.

## Operator workflow

The executable source exposes these literal manual steps:

1. `step("Boot the bounded Tiny browser profile")`
2. `step("Render the shared nested-pane page fullscreen")`
3. `step("Bind one sealed host with built-in ROM and VFS pages")`
4. `step("Navigate to ROM and then VFS while repainting each accepted page")`
5. `step("Initialize all bounded arenas before admitting runtime work")`
6. `step("Render and navigate repeatedly through retained logical extents")`
7. `step("Edit and wheel without rebuilding GUI or resolved-pane storage")`
8. `step("Compare allocation instrumentation with the initialization baseline")`
9. `step("Navigate controls with keyboard and pointer")`
10. `step("Scroll and clip nested content")`
11. `step("Clip nested popup content to the fullscreen root")`
12. `step("Open and dismiss a bounded popup")`
13. `step("Report backend, memory, dependency, and size evidence")`

Repeated uses of the render, navigation, and evidence steps are deliberate:
the fail-closed rows share operator vocabulary with the corresponding future
evidence-producing flows.

## Scenario matrix

| Scenario | Requirements | Expected result when fully qualified |
|---|---|---|
| Should present an admitted page as one fullscreen opaque root | REQ-001, REQ-002, REQ-005, REQ-006, REQ-011; NFR-004, NFR-009-012 | One opaque root, real pixels, CSS and controls |
| Should navigate built-in ROM and VFS resources through one bounded host | REQ-005, REQ-011; NFR-004, NFR-009, NFR-012 | Each accepted resource repaints and presents |
| Should reuse every Web and GUI arena across render navigation edit and wheel loops | REQ-003-005; NFR-004, NFR-010-012 | Twelve backing stores remain fixed while reuse and logical counts advance |
| Should route keyboard text and pointer events to visible controls | REQ-003-005; NFR-009, NFR-012 | Focus, edit, capture, scroll, damage, and present change |
| Should clip nested content and compose one bounded popup | REQ-002, REQ-003, REQ-009 | Absolute popup geometry and clipped coverage remain distinct |
| Should report bounded failure instead of rendering partial over-capacity input | REQ-015; NFR-004, NFR-010, NFR-012 | Typed failure and no partial checksum |
| Should block optional module and strict Vulkan claims until retained evidence exists | REQ-007-010, REQ-012, REQ-014-015; NFR-002, NFR-005-007, NFR-012 | Fails until descriptor parity and device readback exist |
| Should block RV32 completion until build framebuffer and physical input evidence exists | REQ-001-003, REQ-005-006, REQ-011; NFR-004, NFR-008-011 | Fails until fresh build, framebuffer, fullscreen, physical-input, and module receipts exist |
| Should block the 409600-byte closure claim until ELF and PT_LOAD evidence exists | REQ-008, REQ-013; NFR-001-003, NFR-005-006 | Fails until ELF/PT_LOAD and closure reports exist |

## Arena-reuse procedure

1. **Initialize all bounded arenas before admitting runtime work.** Create the
   browser and resource host, then require a successful arena receipt reporting
   twelve preallocated backing stores.
2. **Render and navigate repeatedly through retained logical extents.** Render
   one built-in page, navigate to ROM, and navigate back; every accepted page
   must advance the frame.
3. **Edit and wheel without rebuilding GUI or resolved-pane storage.** Focus the
   retained input, append text, then scroll a page larger than the viewport;
   both state changes must present.
4. **Compare allocation instrumentation with the initialization baseline.** The
   backing-store count must be unchanged, reuse must increase, logical token,
   node, style, and paint counts must be valid, and the presented checksum must
   match the renderer.

The receipt proves the intended owner/store discipline at the language level.
It does not by itself prove that the runtime performed zero hidden allocations;
that claim remains blocked until the qualified runtime supplies allocator
instrumentation for the same loop.

## Quality scorecard

| Field | Value |
|---|---|
| Source scenarios | 9 active, 0 skipped |
| Intentional fail-closed scenarios | 3 |
| Real-assertion/static traceability | Required before delivery |
| Runtime execution this handoff | `TEST_BLOCKED`: no admitted pure-Simple runtime |
| Runtime PASS | Not claimed |
| Manual provenance | Hand-mirrored, pending pure-Simple docgen |

## Findings and remediation

The three environmental rows deliberately call `fail(...)`; they are not
placeholders or skips. Replace a row only when its named descriptor/Vulkan,
RV32, or size artifacts exist and the admitted runner validates them. If the
arena-reuse flow changes, update its SSpec assertions, this procedure, the test
plan traceability row, and the lane state in the same commit.

## Evidence and provenance

- Executable source: `test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl`
- Test plan: `doc/03_plan/sys_test/tiny_ui_web_wm.md`
- Acceptance state: `.spipe/tiny_ui_web_wm/state.md`
- Runtime evidence: none accepted in this handoff; Rust-seed output is excluded.
- Static gate evidence: reported by the delivery session, not represented as a
  runtime or docgen receipt in this manual.

## Compatibility and limitations

The compatibility helpers may allocate standalone temporary arenas; the Tiny
browser product path retains its constructor-owned arenas. In-band allocation
counters prove stable owner/store discipline only. They do not prove hidden
runtime allocator behavior, strict Vulkan execution, RV32 framebuffer/input,
or the 409,600-byte closure.

The canonical open evidence and resume conditions are in
`doc/08_tracking/bug/tiny_ui_web_wm_integration_blockers_2026-08-14.md`.
