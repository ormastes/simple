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
- Source adapters own enumerate/capture/refresh/act; common owns parse/normalize/query/render/safety/error/history rules.
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
design-done

## Log
- dev: Created state file with 11 acceptance criteria (type: feature) after parallel acceptance-criteria, scope, and cooperative-review passes; primary model merged and broadened the access loop to preserve the full T32-style LLM-access request.
- research: Three local and three official-domain sidecar passes identified the existing common access core, live adapter/dispatcher gaps, standards constraints, and five feature plus three NFR decision groups; primary highest-capability review merged the results and rejected a parallel CLI model.
- requirements: User selected the recommended F1-A/F2-A/F3-A/F4-A/F5-A and N1-A/N2-A/N3-A bundles; final REQ/NFR documents were written and option drafts removed.
- requirements-clarification: User required shared architecture grammar with T32 GUI access; added REQ-UCLA-024, AC-UCLA-08, and NFR-UCLA-021 before design.
- architecture-correction: Highest-capability review found that a separate UI CLI cannot own the live `UISession`; added the existing `/api/test/ui/*` service as the live transport and limited database fallback to reads.
- design: Architecture, TLDR, CLI/TUI/GUI/detail design, operator guide, agent plan, system plan, failing SSpec, and mirrored manual were produced by three sidecars and merged by the highest-capability model; review corrected the executable T32 root, live UI transport, Pure Simple checker, manual visibility, and capture kinds.
- design-tooling-note: `spipe-docgen` reported 0 stubs, but the current `bin/simple` identified itself as a Rust bootstrap seed; final evidence must use a restored pure-Simple self-hosted binary and must not repeat the completed design docgen cycle unless the spec changes.
