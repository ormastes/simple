# Feature: UI CLI LLM Access

## Raw Request
$sp_dev do with agents teams with detail guide and design and higher model review after task done. ui has gui/tui rendering. ui add cli interface. check t32 gui access. use same way and same rule, make logics to common library.  let wm also has same cli interface to list windows like t32 windows. 
Concept is same as t32 gui access way. it is way to llm easy access app.

## Task Type
feature

## Refined Goal
Add a shared T32-style `UiCliAccess` command contract that lets LLMs discover, inspect, find, act on, and review history for GUI and TUI application surfaces, while UI and WM expose the same normalized window-list interface.

## Acceptance Criteria
- AC-1: Research maps the existing T32 GUI-access commands, output rules, error behavior, and safety rules to the new `UiCliAccess` contract, with every supported parity point and intentional difference documented.
- AC-2: `ui windows list` and `wm windows list` expose the same deterministic window-record schema, ordering, filtering, empty-state behavior, and structured errors; records identify stable window ID, title, owner/app, surface kind, state, geometry, focus/visibility, and parent when available, without fabricating unavailable values.
- AC-3: The UI CLI can snapshot and surface both GUI and TUI windows through stable machine-readable output, including explicit headless, unavailable-backend, stale-window, and unsupported-rendering states.
- AC-4: The UI CLI supports the T32-style LLM access loop for `snapshot`, `surface`, `find`, `act`, and `history`; focused scenarios prove discovery, target selection, a safe GUI action, a safe TUI action, and observable post-action history.
- AC-5: UI and WM frontends delegate command parsing, window normalization, filtering, sorting, serialization, history/error rules, and shared safety validation to common-library owners; app-specific adapters contain only source/render/action integration, and duplication checks find no divergent frontend copies.
- AC-6: Human-readable CLI output and deterministic UTF-8 structured output are both documented and tested, including help, malformed arguments, unknown commands, unknown/stale IDs, zero windows, and inaccessible display/backend cases.
- AC-7: Executable SSpec scenarios use the manual-facing steps `Start UI access`, `List active windows`, `Inspect TUI rendering`, `Inspect GUI rendering`, `Find an interactive target`, `Act on the target`, and `Review access history`; unfinished helpers fail explicitly with `assert(false)` or `fail(...)` and no placeholder output can pass.
- AC-8: The lane includes local/domain research, selected feature and NFR requirements, architecture, GUI/TUI/CLI mockups, detail design, system-test plan, executable specs, generated operator manual, implementation plan, and a detailed LLM/operator guide that demonstrates UI and WM workflows without requiring source-code reading.
- AC-9: The canonical `check-ui-cli-access` gate fails closed on common-contract, UI/WM parity, GUI/TUI inspection, find/action/history, schema, safety, or generated-manual regressions and passes once against the final implementation.
- AC-10: Agent-team execution records independent T32-reference, common-contract, UI adapter, WM adapter, and evidence/docs lanes with a merge owner; after integration, the highest-capability available model reviews and explicitly accepts architecture, implementation, safety, focused evidence, generated-manual quality, exclusions, and the final done claim.
- AC-11: Final verification confirms all changed workflow/tooling contracts are synchronized across applicable `doc/07_guide`, `doc/06_spec`, `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, and `.gemini/commands` surfaces, and confirms no executable `*_spec.spl` exists under `doc/06_spec`.

## Scope Exclusions
- Replacing the GUI renderer, TUI renderer, window manager, or T32 implementation.
- Pixel-perfect cross-backend equivalence unless research shows it is part of the existing T32 access contract; structured rendering and evidence remain required.
- Remote transport, authentication, packaging, release, and non-UI application introspection unless required by the selected requirements.
- New window-management capabilities unrelated to the T32-style LLM access loop; actions remain limited by the shared safety rules and existing application capabilities.

## Cooperative Review
- Sidecar lanes: T32 reference/contract research; common `UiCliAccess` contract; GUI/TUI UI adapters; WM window-list adapter; SSpec evidence, generated manual, and detailed guide.
- Merge owner: primary Codex agent in the `ui-cli-llm-access` lane; unrelated dirty files and concurrent feature lanes are excluded.
- Final reviewer: primary highest-capability Codex model after all lane outputs are integrated; it must explicitly accept behavior, architecture, shared logic, safety, exclusions, evidence, generated-manual quality, and completion status.
- Shared interface: `UiCliAccess`.
- Command concepts: `ui windows list`, `wm windows list`, `snapshot`, `surface`, `find`, `act`, and `history`; research must reuse established repo spellings where they already exist.
- Manual step helpers: `step("Start UI access")`, `step("List active windows")`, `step("Inspect TUI rendering")`, `step("Inspect GUI rendering")`, `step("Find an interactive target")`, `step("Act on the target")`, and `step("Review access history")`.
- Setup/checker helpers: `setup_ui_cli_access` and `check-ui-cli-access`, subject to established repo naming discovered in research.
- Fail-fast placeholders: any temporary helper must call `assert(false)` or `fail(...)`; fabricated window, rendering, action, or history evidence is forbidden.
- Generated-manual owner: evidence/docs lane agent generates and reviews the mirrored manual as an operator document; merge owner repairs unclear steps/captures, and final reviewer explicitly accepts it.

## Research Summary

### Existing Code
- `src/lib/common/ui/access_types.spl:6-61` — versioned semantic surfaces/nodes/events and canonical IDs.
- `src/lib/common/ui/access_snapshot.spl:29-68` and `access_query.spl:11-72` — backend-neutral snapshot, find, text, and JSON owners.
- `src/lib/common/ui/win_text_access.spl:1-230` — existing TRACE32/Simple UI/host-WM/compositor normalization and action validation; its upward `WindowInfo` import is the layering gap.
- `src/app/ui/cli_entry.spl:1-120` — deployed `simple ui` entry lacks access-protocol dispatch.
- `src/app/play/main.spl:83-220` — advertises WM access commands but currently plans instead of executing them live.
- `src/app/t32_cli/commands.spl:58-63` and `mod.spl:28-89` — canonical T32 list/capture command and parity registry precedent.

### Reusable Modules
- `common.ui.access` — snapshot/surface/find/action metadata/history/serialization; no parallel CLI model is needed.
- `common.ui.win_text_access` — cross-source envelope, shared query, staleness, capabilities, and action validation.
- Live `UISession`, compositor GTTI, and `std.play.wm` adapters — existing GUI/TUI/compositor/host-WM sources.

### Domain Notes
- Official TRACE32 live window names are non-unique and Z-order is unstable; common output must generate scoped identity and deterministic ordering.
- WAI-ARIA, UIA, AX, AT-SPI, and WebDriver BiDi support semantic trees, opaque/stale-detectable IDs, advertised actions, and distinct unavailable/disabled/busy/unsupported errors.
- RFC 8259, JSON Schema, POSIX CLI rules, and MCP support UTF-8 versioned JSON, clean stdout, nonzero failures, capability checks, bounded calls, and auditable actions.

### Open Questions
- NONE; feature and NFR alternatives that materially change scope are presented for required user selection.

<!-- sdn-diagram:id=ui-cli-llm-access-context -->
```sdn
ui_cli_llm_access:
  frontends: [simple_ui_cli, simple_play_wm_cli]
  common: [UiAccessSnapshot, WinTextSnapshot, find, serialize, safety, history]
  adapters: [ui_gui_tui_session, compositor, host_wm, trace32_reference]
  evidence: [unit, integration, sspec_manual, perf, check_ui_cli_access]
```

## Requirements
- REQ-1 (AC-1): map official and repository T32 window/capture/action/history/error behavior and document supported parity and differences.
- REQ-2 (AC-2): expose UI and WM window lists through one normalized, deterministic, stable-identity schema with explicit unavailable values.
- REQ-3 (AC-3): snapshot/surface live GUI and TUI sessions with typed headless/backend/stale states.
- REQ-4 (AC-4): support snapshot/surface/find/act/history, capability-check each action, refresh afterward, and append correlated history.
- REQ-5 (AC-5): keep normalization/query/serialization/safety common and live enumeration/capture/action execution adapter-owned; remove the common core's backend-type dependency.
- REQ-6 (AC-6): provide deterministic human and UTF-8 structured modes with versioning, clean streams, stable errors, and bounded output.
- REQ-7 (AC-7): write manual-first executable scenarios with the recorded steps and fail-fast placeholders.
- REQ-8 (AC-8): deliver research, selected requirements, architecture/design/mockups/plans/spec/manual, and detailed LLM/operator guide.
- REQ-9 (AC-9): add one fail-closed focused checker covering common/UI/WM/schema/safety/manual evidence.
- REQ-10 (AC-10): execute recorded team lanes and require highest-capability merged-result review.
- REQ-11 (AC-11): synchronize applicable workflow/spec/guide surfaces and enforce the generated-spec layout guard.
- REQ-12 (user clarification): share the command descriptor/result/error/output/safety grammar across T32 GUI, UI, and WM access while keeping source execution adapter-owned.
- REQ-13 (architecture correction): use the existing UI test API as the live cross-process GUI/TUI transport and keep persisted-store fallback read-only.

## Selected Requirements
- Feature: F1-A, F2-A, F3-A, F4-A, F5-A — established command roots, full safe semantic loop, existing common model with adapter conversion, UI plus host-WM top-level coverage, and human plus versioned JSON output.
- NFR: N1-A, N2-A, N3-A — balanced interactive performance, capability-checked policy-eligible actions, and additive command/schema compatibility.
- Final documents: `doc/02_requirements/feature/ui_cli_llm_access.md` and `doc/02_requirements/nfr/ui_cli_llm_access.md`; option drafts were deleted after selection.

## Architecture

### Module Plan
| Module | Path | Role | Change |
|---|---|---|---|
| Shared grammar | `src/lib/common/ui/access_cli_grammar.spl` | descriptor/request/result/error/safety/output grammar and rendering | New |
| Common access | `src/lib/common/ui/access.spl`, `win_text_access.spl` | exports and backend-type decoupling | Modified |
| T32 adapter | `src/app/t32_cli/{commands,types,render,mod}.spl` | shared GUI grammar mapping with T32-only compatibility | Modified |
| UI adapter | `src/app/ui/access_cli.spl`, `cli_entry.spl` | existing test-API client and read-only store fallback | New/Modified |
| WM adapter | `src/app/play/wm_access_cli.spl`, `main.spl` | live list/conversion/action replacing planned output | New/Modified |
| Evidence | `scripts/check/check-ui-cli-access.spl` | Pure Simple focused checker | New |

### Dependency Map and Decisions
- T32/UI/WM siblings import `common.ui.access_cli_grammar`; common imports no sibling backend type; no cycle.
- Existing `UiAccessSnapshot`/`WinTextSnapshot` remain payloads; no CLI tree/history model.
- T32/UI/WM share `AccessCommandDescriptor`, `AccessOperation`, `AccessRequest`, `AccessResult`, `AccessError`, `AccessSafety`, and `AccessOutputMode`.
- Live UI CLI uses the existing loopback `/api/test/ui/*` service; explicit DB fallback is read-only and rejects `act`.
- Source adapters own parsing/enumerate/capture/refresh/act; common owns descriptor validation, normalization, query, rendering, safety preflight, errors, and history rules.
- Ordinary composition is selected; MDSOC weaving, generic registries, new services, and renderer changes are rejected.

<!-- sdn-diagram:id=ui-cli-llm-access-architecture -->
```sdn
ui_cli_access:
  frontends: [t32_cli, simple_ui_cli, simple_play_wm]
  shared_grammar: [descriptor, request, result, error, safety, output]
  payloads: [UiAccessSnapshot, WinTextSnapshot]
  live_adapters: [t32_remote, ui_test_api, host_wm]
  fallback: ui_access_store_read_only
```

### Public API and Coverage
- Signatures and file-level algorithms: `doc/05_design/ui_cli_llm_access.md`.
- Full decisions/startup/hot paths/invalidation/perf: `doc/04_architecture/ui_cli_llm_access.md` and TLDR.
- REQ-UCLA-001..025 and NFR-UCLA-001..022 are mapped in the architecture and system plan.

## Specs

### Spec Files and Manual
- `test/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.spl` — 17 fail-closed scenarios.
- `doc/06_spec/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access_spec.md` — generated complete, 0 stubs; primary GUI/TUI flows and typed captures visible.
- `doc/03_plan/sys_test/ui_cli_llm_access.md` — three-scenario traceability for every selected REQ/NFR.

### Manual Shape
- Visible: live TUI, live GUI, live WM, output/error/safety, help, and live test-API transport flows.
- Folded: architecture parity, identity, environment, ownership, hot-path/perf, manual-quality, and final gates.
- Captures: TUI for terminal flows, GUI for live GUI flow, protocol for JSON/errors/gates.

## Detail Design
- CLI/TUI design: `doc/05_design/ui_cli_llm_access_tui.md`.
- GUI design: `doc/05_design/ui_cli_llm_access_gui.md`.
- Data/module/algorithm design: `doc/05_design/ui_cli_llm_access.md`.
- Operator/LLM guide: `doc/07_guide/app/ui/ui_cli_llm_access.md`.
- Agent lanes/merge/review: `doc/03_plan/agent_tasks/ui_cli_llm_access.md`.

## Phase
implementation-blocked

## Log
- dev: Created state file with 11 acceptance criteria (type: feature) after parallel acceptance-criteria, scope, and cooperative-review passes; primary model merged and broadened the access loop to preserve the full T32-style LLM-access request.
- research: Three local and three official-domain sidecar passes identified the existing common access core, live adapter/dispatcher gaps, standards constraints, and five feature plus three NFR decision groups; primary highest-capability review merged the results and rejected a parallel CLI model.
- requirements: User selected the recommended F1-A/F2-A/F3-A/F4-A/F5-A and N1-A/N2-A/N3-A bundles; final REQ/NFR documents were written and option drafts removed.
- requirements-clarification: User required shared architecture grammar with T32 GUI access; added REQ-UCLA-024, AC-UCLA-08, and NFR-UCLA-021 before design.
- architecture-correction: Highest-capability review found that a separate UI CLI cannot own the live `UISession`; added the existing `/api/test/ui/*` service as the live transport and limited database fallback to reads.
- design: Architecture, TLDR, CLI/TUI/GUI/detail design, operator guide, agent plan, system plan, failing SSpec, and mirrored manual were produced by three sidecars and merged by the highest-capability model; review corrected the executable T32 root, live UI transport, Pure Simple checker, manual visibility, and capture kinds.
- design-tooling-note: `spipe-docgen` reported 0 stubs, but the current `bin/simple` identified itself as a Rust bootstrap seed; final evidence must use a restored pure-Simple self-hosted binary and must not repeat the completed design docgen cycle unless the spec changes.
- implementation: Integrated the shared grammar, T32 mapping, live UI loopback adapter, host-WM adapter, advertised-action/capability preflight, correlated bounded history, non-mutating persisted reads, normalized human/JSON output, multi-surface snapshots, and the focused Pure Simple checker.
- verification-progress: Directly importing `std.nogc_sync_mut.io.http_sffi` resolved the `HttpResponse` type erasure. A typed `DbError` conversion helper resolved the next ambiguous-method failure.
- verification-blocker: The third cache-preserving native build still linked a stale cached interface and generated an unsafe unresolved stub for newly restored `UiAccessStore.open_existing`, although the owner method now exists. Stop at the mandatory cycle cap; next run must invalidate only the access-store/native interface cache before rebuilding. No final acceptance artifact, commit, sync, or push was performed.
- verification-progress-2: `--no-incremental` rebuilt 713 modules and removed the feature-specific unresolved store stub. The base gate, shared grammar, and T32 compatibility passed. Restored the concurrently dropped WM history descriptor/command and bounded correlated store path; simplified numeric parsing to the standard `to_int()` path.
- verification-blocker-2: The rendered TUI scenario first exposed a stale `column` builder call, which was corrected to the current children-array API. The final allowed rebuild then terminated `live-tui-loop` with `Illegal instruction` (exit 132). Stop at the three-cycle cap; next continuation should take one native stack trace before editing. No final acceptance artifact, commit, sync, or push was performed.
- verification-blocker-3: Native debugging located the SIGILL at a null indirect target in `render_tui_widget`. Replacing wildcard hub imports with exact imports did not resolve it; an acyclic extended-to-core dispatcher split compiled cleanly (713 modules, no feature-specific unresolved stub) but `live-tui-loop` still exited 132. The base, shared-grammar, and T32-compatibility scenarios remain passed and must not be rerun. Stop at the mandatory three-cycle cap; the next fresh session should inspect the post-split native stack/symbol lowering before further edits. No final acceptance artifact, highest-capability review, commit, sync, or push was performed.
- verification-progress-3: The post-split native stack proved the remaining SIGILL was the core widget-kind match's missing default for layout-only containers. Added the minimal no-op fallback; the clean 713-module self-hosted build now exits normally instead of reaching compiler `ud2`.
- verification-blocker-4: `live-tui-loop` now fails only its `rendered.contains("Run")` witness; the diagnostic render is empty or control-only at the checker boundary. The mandatory three-cycle cap was reached after clean native rebuilds, so no further rebuild was started. Next continuation should inspect raw rendered bytes or compare the existing focused TUI screen specs before changing renderer code. Previously passed base/shared-grammar/T32 scenarios remain trusted. No final acceptance artifact, highest-capability review, commit, sync, or push was performed.
- verification-progress-4: Raw-byte and GDB inspection proved the final `Screen` object was valid (40x10, ten rows) but unchanged. Native widget records contained nil kinds because of a redundant `WidgetKind.from_wire(...).to_wire()` round-trip, and `require_widget_record` missed matching records through struct-array iteration. The shared store now keeps the validated wire kind directly and uses indexed record/property lookups; native dispatch subsequently observed `panel` and `button` and called both renderers with label `Run`.
- verification-blocker-5: `Screen.put_styled` returns a new screen, but its text-row array payload is lowered to repeated tagged immediates (`0x3`) at the row replacement boundary. Replacing indexed row assignment with a shared copy-on-write helper, then removing its inline conditional, still did not make `live-tui-loop` pass after the third clean 713-module rebuild. Stop at the mandatory cycle cap. The next continuation should inspect the post-helper return payload once, then either use a proven existing native text-array update primitive or fix the compiler owner with a minimal array-of-text regression. Previously passed base/shared-grammar/T32 scenarios must not be rerun. No final acceptance artifact, highest-capability review, commit, sync, or push was performed.
- verification-progress-5: Team review and native disassembly corrected the diagnosis: the replacement argument is already tagged nil (`0x3`) on entry to `_screen_replace_row`; array storage is not the source. `Screen.new` initially holds ten valid text rows, and the renderer reaches `panel`/`button`, but `put_text`'s final interpolation returns nil because imported ANSI globals are zero. The generated call loads `dashboard.render.colors.RESET` despite `screen.spl` importing `app.ui.render.ansi.RESET`, exposing both missing heap-global initialization and a same-short-name resolution collision in the Pure Simple Cranelift entry closure. Converting palettes to `const` did not change the result and was reverted. The screen helper now uses the repo-proven fresh fixed-size text-array/indexed-copy pattern; `Screen.new` uses one repeat allocation.
- verification-blocker-6: The third clean rebuild still failed `live-tui-loop` at the visible render witness. Stop at the mandatory cycle cap. Next continuation must add a minimal native imported-text-global regression that distinguishes (1) correct qualified symbol selection and (2) module initializer execution, then fix the Pure Simple compiler/link owner; do not add renderer-local ANSI literals or raw runtime aliases. Previously passed base/shared-grammar/T32 scenarios remain trusted. No final acceptance artifact, highest-capability review, commit, sync, or push was performed.
- verification-progress-6: Native symbols proved dotted module names were treated inconsistently: use resolution could fall back to the first same-name global, while generated init callers referenced `_dot_` names but Linux Cranelift/LLVM emitted raw-dot init symbols. The Rust owner now matches raw and `_dot_` module spellings, uses one portable module-init symbol helper in both backends, preserves typed BOOL untagging, and has order-reversed collision plus init-symbol regression tests passing.
- safety-progress: Spark audits found and local fixes closed missing-session UI dispatch, persisted-property loss/legacy read-only schema compatibility, WM list/action source divergence, unbounded WM subprocesses, Linux per-window subprocesses, macOS unactionable IDs, missing shared action preflight, and absent post-action correlation. Focused WM tests and affected-file checks pass; the broader handler suite still has two pre-existing Draw-IR failures, so it is not a feature PASS.
- guide-progress: Spark reconciliation corrected the operator guide and architecture/detail/GUI/TUI designs to the actual command roots, adapter-owned parsing, JSON envelope, WM v1 limits, conceptual inspector status, and current verification state.
- verification-blocker-7: Three isolated stage/checker rebuild strategies reached existing bootstrap limits: the Rust seed fails the documented bootstrap-main MIR/backend verifier gate, and the working pure-Simple stage tool emits a tiny non-self-hosting stage binary. The reordered Rust regressions pass, but a corrected native feature checker cannot yet be produced to rerun `live-tui-loop`. Per the cycle cap, stop native rebuild retries until the self-host bootstrap gate is restored. No final acceptance artifact, highest-capability acceptance, commit, sync, or push was performed.
- verification-unblock: A later shared bootstrap produced real 117–122 MiB stage2/stage3 self-host artifacts, proving blocker-7 is cleared. Those artifacts predate the dotted-module compiler fix, so acceptance still requires one isolated canonical rebuild after the active shared bootstrap lane exits.
- spark-audit-2: Three small-model audits confirmed 15 checker scenarios remain and exposed source-string gates that print stronger claims than they prove. Final acceptance must strengthen or narrow those predicates, run live TUI first, and reserve `final` for the evidence-backed highest-capability review artifact.
- wm-safety-progress: WM now has bounded text/path/coordinate inputs, required correlation-store writes, a request deadline checked across inventory/action/observation, and finite per-process timeouts. Focused testing exposed that interpreter `text.to_i64()` and `text.to_int()` accept non-numeric `"x"` on this path; a manual ASCII coordinate validator replaced them, but the three-cycle test cap was reached before rerunning it.
- verification-progress-7: The isolated canonical full bootstrap rebuilt the Rust seed/native runtime with the dotted-module fixes and passed real stage2/stage3 self-hosting. The focused checker then rebuilt cleanly from 713 modules. Two native nil-receiver traces were removed at shared owners by replacing class/struct-array `for` iteration with indexed traversal in descriptor lookup and access query; snapshot JSON now preserves node properties instead of emitting `{}`.
- evidence-progress: Source-string-only gates were replaced or narrowed with executable descriptor parity, deterministic ordering/truncation, output-envelope, error mapping, empty-state, disabled/busy/confirmation/input, ownership, and artifact predicates. Added a separate-process web fixture and transport gate that drives windows/find/act/history through the CLI, verifies service-stop and read-only DB behavior, and captures real GUI images; live TUI writes before/after terminal captures.
- verification-blocker-8: On the third allowed live-TUI cycle, the checker stopped crashing/SIGILL and exited normally with status 1, but emitted no failure diagnostic and wrote no TUI captures, so failure remains before the end of `_ui_loop_ok` (likely another base/common predicate). Stop at the mandatory cycle cap. Next fresh turn should add fail labels around `_base_ok` subcalls or run the distinct `setup` scenario once, then fix only the identified shared owner. No remaining scenarios, final review, commit, sync, or push were run.
- verification-current-2026-07-11: Later work eliminated native base/render crashes, made Unicode TUI rendering and the visible `Run` witness pass, secured canonical action validation, and isolated request parsing into `--scenario json-parser`. The exact 86-byte/four-field predicate now routes UI test and handler parsing through the existing native-proven MCP core extractor, with duplicate scanners deleted; targeted source checks and diff check pass. The settled 715-module checker compiles/links, but the third focused `json-parser` cycle still SIGSEGVs. Stop at the mandatory parser cap. Next fresh turn: take exactly one GDB backtrace on `build/bootstrap/ui-cli-access-retry/check-ui-cli-access --scenario json-parser` before editing; do not run live TUI until this focused gate passes. Pending review items: correct/test pure-runtime `rt_index_get` raw-vs-boxed index handling (logical index 8), retain only newest 64 access events, and implement real per-surface tree/focus ownership. `FR-COMPILER-013` tracks safe builtin `list + [item]` fresh-copy-then-push optimization including alias and packed-array constraints. No GUI/WM final scenarios, guards, highest-capability acceptance, commit, sync, or push were run.
- parser-blocker-current: The required focused backtrace now proves the MCP core extractor wrapper is correct and the crash is inside `find_sub`: `haystack.bytes()` calls a zero/unrelocated `rt_string_bytes` slot; `needle.bytes()` would do the same. A static binding audit also proves the linked generic index path passes boxed indices to a raw array getter, so logical index 1+ is wrong and index 8 must be the regression boundary. Stop at the mandatory third parser cycle. Next fresh turn must fix/root native `.bytes()` closure emission and reconcile the boxed `rt_index_get` -> raw `rt_array_get` boundary, rebuild the canonical self-host/runtime once, then run only `json-parser`. `FR-COMPILER-013` was restored as an isolated request block plus canonical DB row after a concurrent rollback removed both. No broad live gate or final acceptance work was run.
- parser-root-fix-prepared: Higher review pinpointed `runtime_symbol_is_codegen_root` omitting synthesized `rt_string_bytes`; added that root plus a focused Rust assertion. Pure simple-core now keeps boxed `rt_index_get/set` ABI, unboxes once, dispatches strings to `rt_string_char_at`, and uses raw array get/set helpers to prevent logical index 8 from being decoded twice. The focused `json-parser` gate now also checks array index 8 and text index 1. These source fixes are unverified until the next canonical self-host/runtime rebuild; do not claim PASS from source inspection.
- parser-linker-root-verified-2026-07-11: Added `rt_string_bytes` to the final native linker's explicit ELF retention roots and strengthened its Rust regression to build a runtime archive, apply the production `-u` roots, link with section GC, run the binary, and confirm the symbol remains in the final table; the focused Rust test passed. A canonical full bootstrap then passed stage 3. Three fresh checker-build cycles all stopped before link on unrelated existing Pure-Simple LLVM verification failures in Vulkan/inline-asm/compiler modules, so the mandatory cap was reached. Do not run another checker build in this session and do not claim `json-parser` PASS; next fresh turn should first isolate why the checker entry closure pulls/recompiles those failing compiler modules or recover the exact previously successful narrow build manifest, then build once, inspect `rt_string_bytes` in the final binary, and run only `--scenario json-parser`.
- parser-core-c-owner-2026-07-12: Removed the `app.io.mod` hub from checker/UI/WM access paths by reusing `std.nogc_sync_mut.io_runtime`; `deps fast` now reports UI access at 9 transitive files, WM at 4, and no cycles. A fresh 715-module Cranelift checker linked, but `nm` still showed `U rt_string_bytes`; the one parser run exited 139. A final trace build proved the current Rust native-project linker is the real owner, selects `/tmp/.../core_c_runtime/libsimple_runtime.a`, and omits `rt_string_bytes` because that generated Core-C archive does not define it. Added the missing Core-C ABI implementation and `CORE_REQUIRED_RUNTIME_SYMBOLS` entry; do not rebuild again this turn because the three-cycle cap is reached. Next fresh turn: run the focused core-C runtime ABI test, rebuild canonical stage2/checker once, require `T rt_string_bytes`, then run only `json-parser`.
- history-multisurface-progress-2026-07-12: Shared in-memory access recording now retains newest 64, matching persisted storage; the hot-path checker executes the 65-event boundary and no longer emits unsupported `full_tree_scans=0`/reparse/cache claims. `SurfaceManager` now retains per-surface focus with indexed struct-array traversal; `UISession` saves/restores tree/focus across active-surface switches and syncs after dispatch; session snapshots enumerate each real surface/tree rather than relabeling one global tree. Existing HTTP/session specs were strengthened for `main#title`, `popup#ok_btn`, and focus restoration. Self-hosted unit/check commands were bounded and terminated after producing no output, so these source changes remain unverified and must not be claimed PASS.
- history-multisurface-review-2026-07-12: Spark review found and the primary model corrected ring-buffer sequence/revision freeze, newest-first history parity with persisted storage, invalid active-surface fallback, stale focus after tree replacement, active-main update isolation, active surface replacement/profile reload, close fallback, gated-open bypass, empty-manager activation, and semantic command canonical prefixes. Tests now assert sequence 206 after truncation, newest-first ordering, both real main/popup node trees, active replacement, main update isolation, focus restoration, and close fallback. Core-C ABI evidence now includes a direct `rt_string_bytes("abc")` byte-array probe and public header declaration. These changes are source-reviewed but not executed because the turn's native build cap and bounded self-host check wait were exhausted.
- runtime-decision-2026-07-12: runtime_need=`rt_string_bytes` parity in the selected Core-C bootstrap runtime; facade_checked=existing MCP JSON extractor plus existing Simple/Rust runtime implementations; chosen_path=`runtime-owned-change`; rejected_shortcuts=parser-local scanner, raw UI alias, unresolved stub, whole-archive workaround, or fabricated checker pass.
- core-c-parser-pass-2026-07-12: A duplicate concurrent `module_init_symbol` definition first blocked the focused Rust build and was removed at the shared backend. The Core-C required-ABI probe then exposed status 18; restoring the owner bounds guard made the third/final ABI cycle pass. Canonical full bootstrap passed stage 3, the checker linked with defined `T rt_string_bytes`, and the third/final `json-parser` cycle passed all four fields plus array/text index regressions. GDB proved the intermediate empty result came from `read_string_end`: `.bytes()` produced packed raw bytes that `.to_i64()` decoded again; both shared scanners now reuse the existing tagged-int `rt_string_bytes` path.
- restored-sidecar-fixes-2026-07-12: Sync had dropped the reviewed ABA, semantic routing, bounded max-sequence snapshot, and canonical action identity fixes. Guided small-model review rediscovered all four and restored them with focused assertions. Primary review then moved semantic/HTTP validation before surface activation so rejected commands/actions cannot mutate active surface, and added the missing empty-snapshot 64-event assertion. Focused interpreter unit runs hung silently for 150 seconds and were terminated as inconclusive; they are not PASS evidence.
- live-tui-blocker-2026-07-12: The final reviewed checker rebuild passed `setup`, but `live-tui-loop` SIGSEGVed. GDB cycle 2 located a null indirect call in `ui.tui.screen._to_chars`; disassembly proved it was the unresolved native lowering for `result + [item]`. The three shared screen occurrences now reuse `result.push(item)`, matching the existing `FR-COMPILER-013` request instead of adding a workaround abstraction. The third/final TUI cycle still exited 139, so the mandatory cap is reached: stop without another trace/rebuild. GUI/WM/transport/manual/final review remain gated and no PASS/commit/sync/push is allowed.
- live-tui-progress-2026-07-12: Fresh guided traces found two later move hazards in the checker: `backend` was reused after `set_active_backend`, and event fields were repeatedly searched. Caching `is_tui` before the move and matching exact correlated payloads removed both crashes. A concurrent jj commit briefly inserted conflict markers during one build; that binary was rejected, `workspace update-stale` restored the authoritative conflict-free runtime, and the next clean 694-module checker linked. `live-tui-loop` now renders and exits normally, but the retained snapshot shows the dispatched action payload as a decimalized moved pointer instead of `run`. The handler now clones the required action for correlation/event ownership and removes redundant resolution of a guaranteed-nonempty requested action. The three-cycle cap is reached before rebuilding this last fix; next turn rebuild once and run only `live-tui-loop`. GUI/WM/transport/manual/final remain gated; no PASS or sync.
- native-action-payload-blocker-2026-07-12: Guided review accepted the ownership intent, but native `text.clone()` lowered incorrectly to `List.clone()` and crashed in `ObjectStore.alloc`. Replacing it with fresh JSON extraction removed that crash, yet the third/final TUI cycle still records the `UIEvent.Action("run")` payload as a decimal pointer (`679740705`) while request/result text remains correct. This proves the remaining owner is native text-bearing enum/callback/pattern lowering, not JSON or handler ownership. Recorded `doc/08_tracking/bug/native_enum_text_payload_decimalized_2026-07-12.md`. Stop at the cap; next turn create/run one minimal native enum-text regression and fix the compiler owner before rebuilding the UI checker. GUI/WM/transport/manual/final remain gated; no PASS/sync.
