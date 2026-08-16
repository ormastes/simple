# Feature: tiny-ui-web-wm

## Raw Request

`$sp_dev impl tiny app and lib with the plan with pherallel agents with guide and higher model review`

## Task Type

feature

## Refined Goal

Implement and verify a pure-Simple, bounded Tiny Lib/UI/Web/Draw/2D/WM stack and linked fullscreen Tiny Browser profile that follows the selected architecture, preserves shared UI/WM semantics through adapters, and demonstrates a mandatory execution closure no larger than 409,600 bytes on RV32 SimpleOS.

## Acceptance Criteria

- AC-1: `src/lib/nogc_sync_mut/tiny/` provides bounded common, pane, event, module ABI, GUI, web, draw, and software-2D owners with no hidden post-init allocation, no production stubs, and focused unit coverage of success, capacity, malformed-input, stale-handle, invalid-stream, clip, transform, and hit-test branches.
- AC-2: `TinyModuleV1`, `TinyRect`, `TinyPane`, `TinyEvent`, `TinyDrawStreamV1`, `TinyWebHostPortV1`, `Tiny2DBackendV1`, `TinyWmPortV1`, `TinyPresentPortV1`, and `TinyInputPortV1` are frozen shared interfaces; Simple APIs retain wrapper types and only explicit static/dynamic ABI codecs use numeric POD fields.
- AC-3: the base component set (Pane, Row, Column, Stack, Text, Spacer, Divider, Border, Button, Checkbox, TextInput, List, ScrollPane, Progress) lays out, draws, focuses, and dispatches applicable events through one relative-pane invariant, proven at unit, integration, and system boundaries.
- AC-4: Tiny Web parses the selected bounded HTML/CSS profile from built-in/ROM/VFS resources, computes deterministic block/inline layout, emits TinyDrawStream, supports links/buttons/text input/focus/scrolling, and returns explicit receipts for malformed, unsupported, or over-budget input.
- AC-5: the software Tiny 2D backend validates and executes the base stream into RGB565 and ARGB8888 with deterministic checksums; strict Tiny Vulkan is an optional adapter that either proves device submission/readback or reports unavailable without silent fallback.
- AC-6: linked Tiny WM kiosk owns one output, one output-sized opaque root, bounded popups, keyboard/pointer focus, capture, relative geometry, clipping, bounded damage, direct-present selection, and explicit frame receipts; the service form uses the same TinyWmPortV1 contract and is not required for the smallest cold-start closure.
- AC-7: `src/os/apps/tiny_browser/` boots the admitted built-in or VFS page through Tiny Web -> TinyDrawStream -> software Tiny 2D -> linked Tiny WM and proves visible controls receive keyboard, text, pointer, click, scroll, focus, capture, and popup events; static screenshots alone are insufficient.
- AC-8: every public tiny class has stable class/module IDs, capabilities, factory/destructor metadata, static registration, optional current-SFM/dynSMF descriptor mapping, and one authoritative generated legacy/FTXUI/litehtml/tiny mapping; optional packs are absent from profiles that exclude them.
- AC-9: the executable system SSpec at `test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl` traces every REQ/NFR, uses real assertions and typed captures, and generates `doc/06_spec/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.md` as a zero-stub operator manual; `doc/06_spec` contains no executable `.spl` specs.
- AC-10: host gates H0-H4 pass once each with retained evidence: bounded unit tests, normalized FTXUI/litehtml differential fixtures, Tiny TUI capture, interactive software browser, and strict Vulkan pass or explicit unavailable classification.
- AC-11: RV32 gates R0-R4 retain fresh lane-owned evidence for build/boot, headless RGB565 checksum and state-changing synthetic input, fullscreen output, physical keyboard/pointer path, and optional-module ABI handling; unavailable R2/R3 rows remain open with linked TODO/resume plans and block feature completion.
- AC-12: S0 proves the stripped static ELF and sum of mandatory PT_LOAD file payloads are each at most 409,600 bytes; any claimed dynamic profile also proves its cold-start mandatory closure is at most 409,600 bytes and reports sections, symbols, dependencies, per-module deltas, and reserve usage.
- AC-13: dependency, lint, duplication, branch-coverage, direct-env/runtime, focused source checks, MCP/LSP core smoke where required, stub-prevention, and production-readiness verification pass without importing full compositor/full Web renderer/host adapters/optional packs into the base closure.
- AC-14: a highest-capability reviewer audits every acceptance criterion, frozen contract, broad exclusion, generated-manual quality, evidence identity, and done claim after lower-model sidecar work is merged; unresolved findings remain active.
- AC-15: knowledge is updated in the existing research/requirements/architecture/design/plan artifacts, a reachable `doc/07_guide/` Tiny stack guide, `doc/00_llm_process/feature_expert/tiny_ui_web_wm/skill.md`, and relevant UI/OS layer-expert skill; every discovered gap not fixed has a `doc/08_tracking/bug/` record with file/line and unblock condition. Workflow/skill/command docs are N/A unless implementation changes SPipe or evidence-wrapper behavior; if it does, those documents and the generated manual must be refreshed before verify.

## Scope Exclusions

The first mandatory closure excludes JavaScript, TLS, unrestricted networking, media, advanced typography, flex/grid/table layout, gradients, animation, general desktop window policy, taskbar, workspaces, multi-output, remote WM IPC, and statically linked Vulkan loader/driver. These remain future packs and cannot be silently used by the base profile.

## Cooperative Review

- Lower-model sidecars: Tiny common/pane/draw; Tiny web/GUI; Tiny 2D/WM; test and mapping census. Sidecars own disjoint paths and cannot change frozen interfaces.
- Merge owner: `/root` primary Tiny stack integrator.
- Final reviewer: `/root` highest available normal model after all lanes report evidence.
- Frozen interfaces: `TinyModuleV1`, `TinyRect`, `TinyPane`, `TinyEvent`, `TinyDrawStreamV1`, `TinyRenderedSurfaceV1`, `TinyWebHostPortV1`, `Tiny2DBackendV1`, `TinyWmPortV1`, `TinyPresentPortV1`, `TinyInputPortV1`. `TinyRenderedSurfaceV1` is the contract-owner-approved B-10 repair receipt and remains pending executable conformance evidence.
- Manual steps: `step("Boot the bounded Tiny browser profile")`, `step("Render the shared nested-pane page fullscreen")`, `step("Navigate controls with keyboard and pointer")`, `step("Scroll and clip nested content")`, `step("Open and dismiss a bounded popup")`, `step("Report backend, memory, dependency, and size evidence")`.
- Helpers: `setup_tiny_browser_fixture`, `check_fullscreen_root`, `check_relative_panes`, `check_focus_and_capture`, `check_popup_damage`, `check_backend_honesty`, `check_size_closure`.
- Placeholder policy: any unavailable helper must call `fail("tiny UI/Web/WM oracle not implemented")`; silent no-ops, unconditional passes, and fabricated evidence are forbidden.
- Generated-manual review owner: primary integrator, followed by final highest-capability review.

## Runtime Boundary Decision

- runtime_need: none for the initial common/pane/draw/gui/web/WM semantic implementation.
- facade_checked: current resource/input/present and app I/O facades will be reused when target integration begins.
- chosen_path: reuse-facade; add-smallest-owner-facade only after evidence shows a missing seam.
- rejected_shortcuts: raw `rt_*` imports in specs/app leaves, direct backend field pokes, fixture-only rendering paths, Rust-seed fallback, full compositor import, full Web renderer import, and fabricated framebuffer/device receipts.

## Phase

implementation-active

## Current evidence ledger (2026-08-16)

- AC-6/AC-7: code fix prepared for retained WM/present mutation, root admission before interaction routing, exact direct-present geometry, pointer capture/release, and wheel routing. Unit/integration/system sources were updated; pure-Simple execution is pending and no PASS is claimed.
- AC-8: incomplete. The component map exists, but generated factory/destructor/dependency metadata, static/dynamic descriptor parity, excluded-pack closure evidence, and optional-module ABI evidence are missing.
- AC-9: incomplete. The executable source now traces every REQ/NFR and retains H4/RV32/S0 as explicit `fail(...)` scenarios. The checked-in manual is marked stale pending pure-Simple docgen and manual review.
- AC-10: incomplete. No new H0-H4 result was run in this handoff; H4 lacks strict Vulkan device submission/readback evidence.
- AC-11: incomplete. R0-R4 have no fresh lane-owned RV32 artifacts; the system spec fails closed instead of omitting these rows.
- AC-12: incomplete. S0 has no stripped ELF/PT_LOAD/section/symbol/dependency/module-delta/reserve receipt.
- AC-13: incomplete. Focused test, lint, duplicate, source, direct-runtime, branch coverage, and production-readiness gates have not passed with a pure-Simple runner.
- AC-14: incomplete. Highest-capability review remains assigned to `/root` after executable evidence exists.
- AC-15: source knowledge, plan, guide, experts, and blocker record were refreshed for this handoff; final knowledge acceptance remains blocked on verification/manual regeneration.

The 2026-08-16 independent highest-capability review returned `STATUS: FAIL`, not merely runner-blocked. It found production-contract gaps in the raw draw-stream/present path, disconnected CSS/resource-host semantics, missing component implementations, event routing without repaint/present, WM identity/focus defects, registry ambiguity, and broader post-init allocation. These remain active as B-10 through B-13; the three fail-closed system rows are truthful blockers, not completion evidence.

The subsequent source-only repair wave prepared B-10 through B-13 fixes and focused test sources: versioned draw envelopes and surface-bound presentation; CSS/attribute/hidden-content and base-container behavior; WM-constrained event-to-frame updates; and generational WM/registry uniqueness. These are implementation progress only. B-10 through B-13 stay open until an admitted pure-Simple runner compiles and passes the preserved focused commands; browser/host integration and valid-empty-resource representation still require merge-owner resolution.

The 2026-08-16 no-GC audit adds B-14: Web token/parser/CSS/layout/paint arrays and GUI node/resolved-pane arrays still grow after `TinyBrowser.create`, and browser control installation replaces the GUI arena. Logical limits alone do not prove NFR-011. The required repair is preallocated backing plus logical counts/reset-in-place and allocation-instrumented render/navigation/event evidence.

Core source repair now preallocates counted DrawStream storage and software-2D execution stacks, uses saturating rectangle/pane/translation arithmetic, and validates public pane lookup generationally. The ten-path counted-stream follow-up is commit `544428e1343550cf3f589d8d3a50511d7f4b93a9` with one-pass `STATIC_PASS`. NFR-004/NFR-009/NFR-010/NFR-011 remain active because no admitted pure-Simple runner or retained-allocation evidence has proved these paths.

Product source repair preallocates WM/present/input storage, adds explicit logical damage counts, and copies presented pixels into a retained preallocated buffer (`cda76b5e357d2af31281f5ddf386229b7f1720fa`). NFR-011 remains active under B-7 until exact capacity scenarios and retained-allocation evidence run with an admitted pure-Simple runner.

REQ-009 service parity and the complete AC-7 product flow remain active, but source implementations now exist: an optional non-exported WM service capsule/parity spec (B-8), plus V2 valid-empty resource admission, retained navigation/repaint, separately rasterized visible popup content, and built-in/ROM/VFS integration/system parity scenarios at `b170f8bd370fbdef992873a6f29d4dd8d1cd0faa` (B-9). Executable parity and product receipts remain required before either blocker closes.

Verification commands are recorded in `doc/03_plan/agent_tasks/tiny_ui_web_wm.md`. The Rust seed is inadmissible and was not used in this handoff.

## Log

- dev: Created state file with 15 acceptance criteria (type: feature); froze interfaces, scenario vocabulary, cooperative lanes, runtime decision, knowledge gates, and strict RV32/size completion boundaries.
- implement: Parallel common/pane, draw/2D, and GUI/Web lanes added the initial bounded source and unit specs; primary lane added linked Tiny WM, browser integration, component mapping, guide/expert knowledge, integration/system specs, and a zero-stub generated manual.
- evidence: Tiny WM diagnostic 4/4, Tiny Draw diagnostic 6/6, and Tiny 2D diagnostic 5/5 used a Rust bootstrap seed and are not final PASS. Common/Web checks timed out or remained unexecuted. The browser integration stopped at the mandatory third cycle with 2/4 passing; open blockers are recorded in `doc/08_tracking/bug/tiny_ui_web_wm_integration_blockers_2026-08-14.md`.
- phase: implementation remains active; AC-1 through AC-15 are not complete and no verify/release claim is made.
- implement (2026-08-16): removed browser-local copies of retained WM/present owners, admitted the kiosk root before interaction-only dispatch, added linked `TinyWmPortV1` conformance, tightened direct-present geometry, and added wheel/capture evidence sources.
- trace audit (2026-08-16): added explicit fail-closed H4/RV32/S0 scenarios for previously omitted REQ-007/008/010/012-014 and NFR rows; marked the generated manual stale pending pure-Simple regeneration.
- doc/wiki refactor inventory: updated the canonical agent plan, guide, generated-manual handoff notice, feature/layer experts, state, and integration blocker record. Workflow/skill/command docs are N/A because no SPipe or wrapper behavior changed.
- checkpoint review (2026-08-16): highest-capability review found stale popup geometry assertions in the integration/system sources. Follow-up `eb6e0f568303d650355b2d53b25de4b69d7a9f31` now proves the source-level distinction between absolute `resolved = 40x40` and effective `clip = 20x20`; re-review returned `PASS-for-checkpoint`. Full verification remains incomplete and no executable PASS is claimed.
- bounded source follow-up (2026-08-16): commits through `544428e1343550cf3f589d8d3a50511d7f4b93a9` add typed/saturating core safety, optional WM service parity source, V2 resource/navigation and visible-popup source, fixed-capacity WM/browser storage, and counted preallocated draw execution. The latest ten-path slice passed one static consistency gate with unchanged tree file count; all executable blockers remain open.
- product evidence follow-up (2026-08-16): `b170f8bd370fbdef992873a6f29d4dd8d1cd0faa` adds built-in/ROM/VFS navigation scenarios, and `cda76b5e357d2af31281f5ddf386229b7f1720fa` retains validated presented pixels in preallocated storage with mutation-isolation coverage. Both have runner-independent static evidence only.
- no-GC audit (2026-08-16): recorded B-14 for post-initialization Web/GUI transient arena growth; no zero-allocation claim is permitted until its source and instrumented runtime gate are complete.
