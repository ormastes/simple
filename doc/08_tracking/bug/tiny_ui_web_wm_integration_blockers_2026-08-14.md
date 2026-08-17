# Tiny UI/Web/WM integration blockers

Date: 2026-08-14
Status: open
Owner: Tiny stack merge owner
Final reviewer: highest-capability Tiny UI/Web/WM reviewer

## B-1 Integrated direct-present receipt is false

- Acceptance criteria: AC-6, AC-7, AC-9.
- Evidence: the third and final diagnostic cycle of `test/02_integration/lib/tiny/tiny_browser_stack_it_spec.spl` executed 4 scenarios, passed 2, and failed the first scenario at the expected `direct_present=true` assertion.
- Suspected boundary: value-owned state transfer between `src/os/apps/tiny_browser/app.spl` and `src/os/services/tiny_wm/model.spl`; the isolated Tiny WM unit scenario reports direct presentation correctly.
- Unblock condition: inspect the returned `TinyWmFrameReceipt` and root surface state with the pure-Simple runner, fix the owner-result transfer or policy defect, and pass the unchanged integration assertion.
- Resume command: `bin/simple test test/02_integration/lib/tiny/tiny_browser_stack_it_spec.spl --mode=interpreter --no-session-daemon --timeout 90` after a verified pure-Simple Stage-4 `bin/simple` is deployed.
- 2026-08-16 repair status: source fix prepared, not verified. `TinyBrowser` now mutates retained `self.wm`/`self.present` owners directly instead of mutating local value copies and then assigning them back. Interaction-only setup also admits the root before WM-gated keyboard/text dispatch. Unit/integration/system sources assert retained root state and direct-present identity; keep this bug open until the resume command passes once with the pure-Simple runner.

## B-2 Tiny Web glyph accessor is not verified

- Acceptance criteria: AC-4, AC-5, AC-7, AC-9.
- Evidence: the third diagnostic cycle rejected `char_at(index).ord()` because `ord` was unavailable in nested call context. After the mandatory cycle cap, `src/lib/nogc_sync_mut/tiny/web/paint.spl` was changed to the repository-used `text[index].ord()` form but was not rerun.
- Unblock condition: a focused pure-Simple source/test run proves the accessor and bootstrap-glyph emission without parser/runtime fallback.
- Resume command: run the Web paint unit spec once, then the integration spec only if the focused result passes.

## B-3 Required production runner and target evidence are absent

- Acceptance criteria: AC-10 through AC-14.
- Evidence: `bin/simple --version` emits the Rust bootstrap-seed warning. `sspec-maintain` is unreachable from that binary. No RV32 ELF, boot, framebuffer, input, module-closure, section, symbol, or PT_LOAD report has been generated for this lane.
- Unblock condition: deploy and identify a pure-Simple Stage-4 runner, complete host gates, then run R0-R4 and S0 in owned output/cache paths. R2/R3 remain mandatory; unavailable hardware requires an open capability-specific continuation record and cannot produce feature PASS.
- 2026-08-16 admission status: the core lane reports that both candidate pure-Simple admissions failed. No Tiny command was run with either candidate, and the Rust seed remains inadmissible.

## B-4 Descriptor parity and excluded-pack closure are not implemented

- Acceptance criteria: AC-8, AC-9, AC-10, AC-13.
- Evidence: `config/tiny/tiny_component_map.sdn` names stable classes/packs, but no retained generator receipt proves factory/destructor/dependency metadata, static/dynamic descriptor parity, or absence of excluded packs from the admitted base closure.
- Unblock condition: implement or identify the canonical generator/descriptor adapter, add real ABI mismatch and parity checks, retain the dependency closure, and replace the fail-closed H4/R4 system scenario only after those checks pass.

## B-5 Executable manual is intentionally fail-closed and stale

- Acceptance criteria: AC-9, AC-11, AC-12, AC-15.
- Evidence: the system source now traces every REQ/NFR, with explicit `fail(...)` scenarios for H4/R4, R0-R4, and S0. The checked-in generated manual predates those scenarios because no admissible pure-Simple docgen was available.
- Unblock condition: satisfy each retained blocker, replace only the corresponding fail-closed oracle with real assertions, run the system spec once, regenerate with `bin/simple spipe-docgen test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl --output doc/06_spec --no-index`, scan with `bin/simple sspec-maintain scan test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl`, and complete human/highest-capability manual review.

## B-6 Core boundedness and handle safety are unproven

- Acceptance criteria: AC-1, AC-3, AC-5, AC-10, AC-13; NFR-004, NFR-009, NFR-010, NFR-011, NFR-012.
- Prior review found post-init `TinyDrawWriter.words` growth, execution-local software-2D clip/translation stacks, unchecked rectangle/translation arithmetic, and an unchecked public pane lookup.
- 2026-08-16 source repair: `TinyDrawWriter` now preallocates its backing store and exposes a logical word count through `TinyDrawStreamV1.create_counted`; command writes are capacity-checked and atomic. `TinySoftware2D` preallocates its clip/translation stacks during creation and executes only the admitted logical word count. Rectangle edges, pane translation, and raster translation use saturating helpers; `TinyPaneStore.get` returns a typed result after generational validation. Focused boundary, stale-handle, counted-stream, and fixed-capacity assertions were added.
- Static evidence: commit `544428e1343550cf3f589d8d3a50511d7f4b93a9` passed the one-pass counted-stream consistency gate across ten exact source/spec paths: no stale raw writer-envelope consumers, all Web draw results carry a logical count, no post-init writer/software stack `push`, no placeholder/raw-runtime pattern, and `git diff --check` clean.
- Follow-up safety evidence: `3a159881208e52e8de0855799c808fe005aa2e2e` rejects overflow-sized software surfaces before area multiplication or pixel indexing, and `789daa9f3ba74a3d5752285e7d26e5451d2550c5` retires exhausted generational slots instead of wrapping identity back to generation one. Both have focused static boundary oracles only.
- Remaining risk: no admitted pure-Simple runner has compiled or executed these paths, and static inspection cannot establish the allocator/value-semantics behavior of array transfer or complete pixel-index safety. B-6 therefore remains open.
- Ownership: Tiny common/pane/draw/software-2D core owner; this product lane records but does not edit those paths.
- Unblock condition: compile and run the focused core/product criteria once with an admitted pure-Simple runner, then capture retained allocation and boundary evidence proving that counted array transfer and raster indexing satisfy the no-GC profile.

## B-7 Tiny WM/browser ports still allocate after initialization

- Acceptance criteria: AC-6, AC-7, AC-10, AC-13; NFR-004, NFR-011, NFR-012.
- 2026-08-16 source repair: WM surface/damage storage and browser present/input storage are preallocated and mutated by logical count; `TinyPresentPortV1.begin_frame` and `TinyWmFrameReceipt` carry explicit damage counts, and the input port uses a bounded ring. Follow-up `cda76b5e357d2af31281f5ddf386229b7f1720fa` also preallocates the retained presentation pixel buffer, copies validated pixels/scalars in place, and adds a source-surface mutation isolation oracle.
- Remaining risk and unblock condition: compile and execute the exact capacity/overflow scenarios with an admitted pure-Simple runner, then capture retained allocation evidence proving no post-init array allocation or value-copy allocation at the port boundary. B-7 remains open until that evidence exists.

## B-8 Tiny WM service-form parity is absent

- Acceptance criteria: AC-6, AC-9, AC-10, AC-13; REQ-009, REQ-014.
- 2026-08-16 source repair: optional `TinyWmServiceCapsule` implements the same `TinyWmPortV1`, validates ABI admission, delegates to the linked kiosk, and has focused source coverage for parity and rejection. It remains outside `std.tiny` exports and the smallest closure; commit `b3ac80d951f8ac4c0f3fdb5d661dac5b45c690b3` preserves the slice.
- Unblock condition: compile and execute the linked/service parity and ABI-rejection spec with an admitted pure-Simple runner, prove excluded-pack closure, and replace only the corresponding fail-closed system evidence.

## B-9 Browser resource/navigation and visible popup product flow are incomplete

- Acceptance criteria: AC-7, AC-9, AC-10, AC-13; REQ-005, REQ-011, REQ-015.
- 2026-08-16 source repair: the browser binds a sealed bounded memory host, uses the optional compatible `TinyWebHostPortV2` existence query to distinguish valid-empty resources from misses, retains provider/path/resource state across accepted navigation, and repaints/presents the loaded page. `open_visible_popup` emits separate popup draw content through counted TinyDrawStream/software-2D and records visible-pixel/present receipts. Follow-up `b170f8bd370fbdef992873a6f29d4dd8d1cd0faa` adds integration/system source scenarios that register built-in, ROM, and VFS pages through one port and require ROM/VFS navigation to repaint and retain exact provider/path/page state.
- Remaining risk and unblock condition: compile and run the resource/navigation/popup unit, integration, and system criteria with an admitted pure-Simple runner; add or prove the required built-in/ROM/VFS fixture parity; then replace only the matching fail-closed evidence. B-9 remains open.

## B-10 Frozen draw envelope and presentation payload are bypassed

- Acceptance criteria: AC-2, AC-5, AC-6, AC-7, AC-13; REQ-006, REQ-009, REQ-010, REQ-014; NFR-005, NFR-007, NFR-012.
- Evidence: production ports and browser/backend calls pass raw `[i32]` streams rather than `TinyDrawStreamV1`; `TinyPresentPortV1` and `TinyMemoryPresent` receive damage only and never bind the rendered pixels, surface handle, format, or checksum being presented.
- Unblock condition: route the validated versioned envelope through `Tiny2DBackendV1`, bind a concrete rendered surface/readback identity into presentation, reject ABI/capability mismatches, and prove the presented checksum matches the software raster output.
- 2026-08-16 repair status: source and focused specs now carry `TinyDrawStreamV1` through `Tiny2DBackendV1`, validate ABI/capabilities before mutation, expose `TinyRenderedSurfaceV1`, and make the memory present port validate/retain the surface identity, pixels, format, frame ID, and checksum. Keep B-10 open until the admitted pure-Simple unit/integration commands prove trait conformance, value semantics, and exact presented checksum.

## B-11 Web/CSS and base component behavior are disconnected

- Acceptance criteria: AC-3, AC-4, AC-7, AC-10; REQ-003, REQ-004, REQ-005, REQ-012; NFR-009, NFR-010, NFR-012.
- Evidence: parsed nodes discard general attributes; the CSS parser has no production consumer; no `TinyWebHostPortV1` implementation is bound; style/title content can enter ordinary text layout; Row, Column, Stack, List, and ScrollPane are metadata without their required layout/draw/event behavior.
- Unblock condition: preserve admitted attributes, consume bounded CSS in computed style/layout, suppress non-rendered document content, bind built-in/ROM/VFS through the frozen host port, and prove every base component through the shared pane invariant at unit/integration/system levels.
- 2026-08-16 repair status: source and focused specs now preserve bounded selector/control attributes, suppress head/title/style and `display:none`, consume bounded CSS in layout/paint, provide and bind a sealed `TinyWebMemoryHost`, map browser controls from the rendered layout, and implement Row/Column/Stack/List/ScrollPane shared-pane behavior. The valid-empty-resource ambiguity remains active and no execution evidence exists.

## B-12 Event routing does not drive the retained frame

- Acceptance criteria: AC-6, AC-7, AC-9, AC-10; REQ-002, REQ-003, REQ-005, REQ-011; NFR-008, NFR-009, NFR-012.
- Evidence: GUI edits and wheel scrolling change state without invalidating layout, emitting a new draw stream, adding damage, or presenting a new frame. Browser dispatch does not use the WM-routed content identity to constrain GUI dispatch, so popup or outside-root input can reach underlying controls.
- Unblock condition: make event results drive deterministic state -> layout -> draw -> damage -> present, enforce WM target/capture ownership before GUI dispatch, and retain before/after pixel plus structured event receipts.
- 2026-08-16 repair status: browser source now rejects GUI delivery outside the WM root owner and routes accepted edits, wheel, and capture changes through draw, damage, surface-bound present, and structured before/after receipts. Keep B-12 open until focused integration/system execution proves the event target, frame ID, damage, pixel/checksum change, and present sequence.

## B-13 WM identity and registry uniqueness are unsafe

- Acceptance criteria: AC-2, AC-6, AC-8, AC-13; REQ-002, REQ-007, REQ-009, REQ-014, REQ-015; NFR-004, NFR-010, NFR-012.
- Evidence: root surface capacity is not rejected, popup removal can reuse list-index handles, focus/routing may retain removed content, clipped popup bounds overwrite the true resolved geometry, and static registration checks duplicate class IDs only within the incoming module rather than across registered modules.
- Unblock condition: use stable generational surface slots, clear/reassign focus and routing on lifecycle changes, retain separate resolved bounds/effective clip, enforce root/surface capacity, reject cross-module class collisions, and add lifecycle/ABI mismatch coverage.
- 2026-08-16 repair status: source and unit specs now use generational surface slots, reject root/duplicate-content capacity errors, preserve absolute bounds separately from effective clip, retire/reuse popup slots with new generations, clear/reassign lifecycle routing state, and reject cross-module class collisions. Keep B-13 open until the ABI-registry and Tiny-WM focused specs pass once with the admitted pure-Simple runner.

## B-14 Web and GUI transient arenas still allocate after initialization

- Acceptance criteria: AC-1, AC-3, AC-4, AC-7, AC-10, AC-13; REQ-003, REQ-004, REQ-005; NFR-004, NFR-010, NFR-011, NFR-012.
- Evidence: after `TinyBrowser.create`, page render and input paths still construct or grow arrays in `TinyGuiState.bounded/add/resolved_panes`, `tiny_html_tokenize`, `tiny_web_parse`, `tiny_css_parse`, `tiny_web_compute_styles`, `tiny_web_resolve_panes`, and `tiny_web_paint`; browser control installation replaces `self.gui` with a newly bounded state. Bounds reject excess logical records, but they do not prove the accepted no-GC profile performs no hidden post-initialization allocation.
- Architecture conflict: the detail design requires indexed DOM/style/layout arenas and a bounded text pool, while current Web values expose growable arrays and GUI hit testing creates a fresh resolved-pane array per event.
- Unblock condition: introduce preallocated node/token/stack/declaration/style/layout/paint/GUI/pane backing stores with separate logical counts, reset them in place for navigation/repaint, remove per-event resolved-pane construction, preserve typed capacity receipts, and run allocation-instrumented render/navigation/edit/wheel loops once with an admitted pure-Simple runtime. B-14 must remain open until both functional and zero-hidden-allocation evidence pass.

## Checkpoint review correction

Highest-capability static review of commit `6a72812917a205eb471e4b921fd9b6cd04dca187` found two stale popup assertions that expected clipped dimensions in `resolved`. Follow-up `eb6e0f568303d650355b2d53b25de4b69d7a9f31` distinguishes absolute `resolved = 40x40` from effective `clip = 20x20`; the reviewer returned `PASS-for-checkpoint` for that corrected criterion. This does not close any blocker that requires pure-Simple execution or the deliberate fail-closed H4/RV32/S0 scenarios.
