# Simple slim UI — parallel-agent dispatch briefs

**Date:** 2026-09-05  
**Starting source revision:** `e0432cd7be29668138a4c47bf270cb5243ead8e4`  
**Companion design:** `simple_slim_tui_gui_kernel_plugin_design_parallel_plan_2026-09-05.md`  
**Status:** Proposed work instructions. These agents have not been launched and the implementation/benchmark tasks are not marked complete.

## Common instructions for every agent

Read the companion design and your actual files at the assigned integration SHA. Source observations in the design are not measured results. Preserve existing public features, state authority, layout/presentation boundaries, value/COW semantics, and error/validation behavior. Do not introduce a new plugin runtime, grammar, UI tree, public IR, or a mandatory third-party backend.

Work in one isolated branch/worktree. Record the baseline, current integration parent, source hashes and executable hashes. Own only the paths in the ledger. An integrator may edit a shared entry file only after its previous owner has released it; “integration owner” is not permission for simultaneous edits. Proposed paths must be checked against the repository before creating them.

Use two reviewers: one familiar with the affected UI behavior and one familiar with its implementation/runtime layer. Keep mechanical movement, refactoring and optimization separate. Produce explicit test counts and raw evidence. No-input, skipped, bootstrap-only, headless, silent-fallback and blank-window runs are not successful UI performance tests.

A newly found correctness issue receives a separate ticket and baseline characterization. Do not silently preserve a known defect as a requirement, but do not disguise a semantic change as a performance-only patch either. Do not weaken Unicode, clipping, error handling, receipts, or stream admission to achieve a lower number.

### Required handoff record

```text
WORK_PACKAGE:
STATUS: implemented | partial | blocked | investigate
BASE_SHA:
HEAD_SHA:
MERGED_INTEGRATION_SHA: not-yet-integrated | SHA
OWNED_PATHS:
CHANGED_PATHS:
PUBLIC_CONTRACT_CHANGE: none | separately-approved-reference
SOURCE_OBSERVATION:
MEASURED_CAUSE:
PATCH_SUMMARY:
FEATURE_PROFILE_HASH:
BINARY_AND_DEPENDENCY_HASHES:
TEST_COMMANDS:
EXPECTED_ASSERTION_COUNT:
PASS / FAIL / SKIP / BLOCKED_COUNTS:
DIFFERENTIAL_ORACLE:
SABOTAGE_CASE:
RAW_PERFORMANCE_ARTIFACTS:
BEFORE_AFTER_METRICS:
LOADED_AND_INITIALIZED_PROVIDERS:
INSTRUMENTATION_AND_CACHE_STATE:
KNOWN_FAILURES:
OWNERSHIP_RELEASE:
```

A missing measurement is `NOT_MEASURED`, never zero. An implementation can be useful but remain uncertified until the integrated benchmark passes.

## A00 — baseline, contracts, integration

**Branch:** `perf/ui-slim/A00-integration`.

**Own:** source ownership ledger, workload definitions and recipe decisions; shared public façades/import roots only during exclusive integration windows. Do not edit an active agent’s file.

**Work:** identify qualified native TUI and displayed GUI entry paths; freeze the baseline executables; inventory required providers and actual import/link/runtime closure. Confirm which generic composition pieces are landed. The proposed async kernel-plugin directory was absent at the inspected path; do not assume a missing library API exists. Publish exact platform-adapter ownership before A07 edits production code.

**Deliver:** frozen workload/ABI/feature contract, artifact manifest, ownership map, required/later/absent capability matrix, integration sequence, rollback route.

**Acceptance:** every implementation agent has a bounded task and exact files; the GUI baseline demonstrably presents a window and handles input; existing full/demo features remain assigned to a recipe. A build incapable of running the product is a documented blocker, not a valid baseline.

## A01 — benchmark and evidence harness

**Branch:** `perf/ui-slim/A01-bench-harness`.

**Own, proposed:** `test/helpers/ui_slim/**`, `test/05_perf/ui_slim/**`, dedicated runner/evidence scripts; no production UI.

**Work:** implement H0/T0/T1/T2/G0/G1/G2/L0/X1 fixture orchestration. Measure parent-launch milestones, real input readiness, presentation observation when supported, steady/peak memory, mappings, threads and idle behavior. Keep diagnostics separate from timing. Require an exclusive runner lock and immutable executable identities.

**Sabotage:** a program that returns zero without a window; a blank frame; a counter-only GUI probe; a stale binary; a benchmark running during a build; a missing input response. All must be rejected or classified accurately.

**Deliver:** machine-readable raw samples and reports, feature/backend lock, observer limits, repeatability characterization. Do not fabricate “cold” runs merely by restarting a process.

## A02 — common composition adapter

**Branch:** `perf/ui-slim/A02-composition-adapter`.

**Own, proposed:** `src/lib/nogc_sync_mut/tiny/common/composition_adapter.spl` and dedicated adapter tests. Generic provider ABI and the existing Tiny registry remain read-only unless A00 transfers a specific file.

**Work:** bridge Tiny module/class admission to the existing common provider-query authority. Provide a sealed static composition path without directory scanning or a mandatory dynamic loader. Cache admitted coarse interfaces; retain capability/version checks and exact provider identity. Use the existing codecs, not assumed native struct packing.

**Sabotage:** duplicate module/class, wrong ABI, missing required interface, forbidden capability, provider release while a surface/callback is alive.

**Acceptance:** static and dynamic routes expose equivalent supported behavior; no per-cell FFI; no new registry/lifecycle authority; no mandatory async thread pool just to use one UI provider.

## A03 — normal TUI screen amplification

**Branch:** `perf/ui-slim/A03-screen-batching`.

**Own:** `src/app/ui.tui/screen.spl`; proposed dedicated normal-screen optimization tests. Do not edit `async_app.spl` or Tiny files.

**Work:** characterize `_screen_replace_row`, `put_text`, and `draw_hline`. Implement a proven-equivalent single-cell span fast path. Evaluate a private owned frame builder that copies/publishes once rather than rebuilding the row table for each character. Preserve the current public value-returning interface.

**Sabotage:** snapshot retained before drawing; negative start; clipping at the right edge; multi-character `ch`; ANSI reset/style inheritance; combining and wide input; zero-length line. Unproven cases retain the old route.

**Acceptance:** output and aliasing parity; measured row-table copies and allocation counts decrease for the targeted workload. Do not state text concatenation complexity without checking the compiled lane.

## A04 — Tiny layout and child metadata

**Branch:** `perf/ui-slim/A04-tiny-layout`.

**Own:** `src/lib/nogc_sync_mut/tiny/gui/state.spl` and new layout-specific tests/private helpers assigned by A00. Existing pane geometry contracts are read-only.

**Work:** replace repeated parent lookup and sibling scans with a checked indexed path and per-parent running offsets. Preserve the existing resolved-pane result and layout ordering. Build reusable child counts, ordinals, and extents if their consumer contract can remain private.

**Sabotage:** generation mismatch, externally modified node data, invalid parent, mixed nested row/column/stack/list/scroll, saturation/overflow boundaries. Handle or reject violated invariants as the existing contract requires; do not blindly trust a public array.

**Acceptance:** old/new resolved geometry and hit-related data match; valid append-ordered tree work scales linearly in the targeted pass. Publish the private workspace contract before A05 consumes it.

## A05 — Tiny cell buffer and terminal renderer

**Branch:** `perf/ui-slim/A05-tiny-tui`.

**Own:** `src/lib/nogc_sync_mut/tiny/tui/cell.spl`, `render.spl`, and dedicated tests. A04’s files are read-only.

**Work:** add private reusable frame/scratch execution while preserving `tiny_tui_render` returned-value semantics. Avoid repeated text-array construction where a correct iterator/cache exists. Consume A04 child metadata instead of repeated list/scroll scans. Use actual allocation behavior rather than assumptions about `push`.

**Sabotage:** two retained rendered snapshots, changed text between frames, resize up/down, stale generations, clipped nodes, capacity failure, invalid dimension products.

**Acceptance:** cell/attribute output parity; no stale cached text/panes; zero or explicitly accounted warmed fixed-scene allocations. Any changed cell representation must remain internal and must not alter public text semantics.

## A06 — event waiting and file watching

**Branch:** `perf/ui-slim/A06-event-wait`.

**Own:** `src/app/ui.tui/async_app.spl`, exclusively assigned private wait/watch helper files and dedicated tests. A00 may edit its entry imports only after ownership is released.

**Work:** replace periodic polling with event/deadline waiting where supported while keeping the channel/producer architecture. Preserve cancellation, quit and file reload. Avoid redundant immutable source reads when the parser interface allows it. A no-watch compiled fixture may omit watching; the existing file-based live-reload application may not.

**Sabotage:** input arrives while entering wait, close during wait, continuous producer stream, rapid same-size file rewrite, parse error, deleted file, resize and quit back-to-back.

**Acceptance:** no lost events or starvation; unchanged live-reload behavior; reduced unnecessary idle wakes and measured input latency. Record legitimate timer/platform wakes instead of claiming impossible absolute zero.

## A07 — GUI rendering and actual presentation

**Branch:** `perf/ui-slim/A07-gui-render`.

**Own:** `src/lib/nogc_sync_mut/tiny/engine2d/software.spl`; one actual host presentation adapter only after A00 assigns its exact path; dedicated tests.

**Work:** profile per-pixel checks/conversion and receipt/checksum work. Add a validated span path where generated code still repeats invariant work. Preserve stream validation, errors and receipts. Connect the qualified G1/G2 fixture to an actual displayed surface using the existing route.

**Sabotage:** wrong pixel format/capability, malformed draw stream, clipped/translated overflow edge, public pixel mutation before receipt, pending callback at window close.

**Acceptance:** pixel/receipt/status parity and displayed input response. RGB565 currently uses `[i32]` slots: do not claim a packed two-byte buffer, or change its public contract as an unreviewed optimization. Checksum caching requires complete mutation tracking; otherwise keep it correct and report its cost.

## A08 — C terminal comparisons

**Branch:** `perf/ui-slim/A08-c-terminal-refs`.

**Own, proposed:** reference-only termbox2/ncursesw fixture directories and lockfiles; no production backend replacement.

**Work:** implement matched terminal setup, greeting, input and cleanup. Freeze exact upstream revision/options. Record terminfo, wide-character settings, linked dependencies and platform limits. A Simple wrapper comparison uses the same library configuration as direct C.

**Sabotage:** redirected nonterminal output, failed initialization, partial writes, unknown terminal, resize, incorrect restored state. Do not report a noninteractive stdout program as T1.

**Acceptance:** harness-verified T1/T2 scope, complete closure accounting, and repeatable executable identity. Promotion of a production provider is a later A00 decision, not this agent’s authority.

## A09 — C/C++ GUI comparisons

**Branch:** `perf/ui-slim/A09-gui-refs`.

**Own, proposed:** reference-only Nuklear/microui/FLTK fixture/build directories; optional LVGL embedded lane; upstream notices and feature locks.

**Work:** separate widget-core timing from full native-window timing. Include window/input/renderer/font resources for C widget cores; preserve each library’s correct build flags across translation units. Use A01’s G1/G2 contracts and state nonmatching capabilities explicitly.

**Sabotage:** command output without presentation, missing fonts, silent backend substitution, an immediate exit, and a visible greeting that never accepts input.

**Acceptance:** honest layer categorization and full dependency/memory accounting. No replacement of Simple’s state authority or default GUI; unsupported platform lanes are visible blockers.

## A10 — dependency and demand-load packs

**Branch:** `perf/ui-slim/A10-pack-closure`.

**Own, proposed:** exact product/pack metadata and closure reports assigned by A00. Existing shared entry roots and implementation files owned by other agents are read-only.

**Work:** map each present feature to required startup, declared first use, or absent-in-product. Separate requirement from static/dynamic placement. Propose coarse feature packs and submit root/import changes to A00 for exclusive integration. Keep source-driven parsing, internationalized text and user-selected GPU features required when the application contract requires them.

**Sabotage:** unrelated optional pack absent at startup; required pack missing; optional pack incompatible on first use; provider accidentally opened by an umbrella import; metadata that implies a compiler subprocess on native hello startup.

**Acceptance:** source/link/map/activation evidence agrees with the recipe, full functionality remains reachable, and X1 measures the deferred cost.

## A11 — independent release certification

**Branch:** `perf/ui-slim/A11-certification`.

**Own, proposed:** cross-mode system scenarios, review receipts and final evidence reports. No production patches; failures return to their owner.

**Work:** rebuild final integrated artifacts; verify source and feature hashes; run old/new, static/dynamic and platform lanes; inspect visual and semantic results; review no-load and sabotage probes. Reconcile every claimed improvement with raw samples and uncertainty.

**Acceptance:** issue one of `CERTIFIED`, `PARTIAL_WITH_BLOCKERS`, or `REJECTED`, with reasons. List failures, unavailable observers, unmeasured memory categories and unsupported targets. A collection of agent-local passing tests is not final certification.

## Scheduling and first slice

Wave 0 establishes contracts and qualified baselines. Wave 1 runs A02/A03/A04 and reference fixture development. Wave 2 integrates their frozen interfaces with A05/A06/A07/A10. Wave 3 integrates, measures on an exclusive runner, and certifies.

**Smallest useful implementation slice:** immutable baseline + A03 horizontal batching + A04 checked linear layout + old/new differential tests + one measured existing-backend TUI workload. This yields attributable improvements without waiting for foreign libraries or a full async kernel-plugin implementation. The next slice adds GUI presentation qualification and event/buffer reuse; product-pack cutover follows verified contracts.
