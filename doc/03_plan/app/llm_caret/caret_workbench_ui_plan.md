# Caret Workbench UI — Implementation Plan, Acceptance Matrix and Backlog

**Date:** 2026-11-14
**Target:** `ormastes/simple`, `release/1.0.0`
**Status:** Proposed plan; not a release-readiness certificate. Nothing in this program is release-qualified.

Related docs:
- Research: [caret_workbench_ui_research_2026-11-14.md](../../../01_research/app/llm_caret/caret_workbench_ui_research_2026-11-14.md)
- Design: [caret_workbench_ui.md](../../../05_design/app/llm_caret/caret_workbench_ui.md)
- Requirements: [caret_workbench_ui.md](../../../02_requirements/app/llm_caret/caret_workbench_ui.md)
- TLDR: [caret_workbench_ui_plan_tldr.md](caret_workbench_ui_plan_tldr.md)

## Lane status 2026-11-14

Status as of 2026-11-14 after landing. "landed (pure core)" means the unit-tested pure module is merged on `release/1.0.0`; it is NOT wired into the running TUI/GUI unless the note says so, and runtime/native is verification-pending for every lane.

| Lane | Backlog rank | Requirements | Status | PR |
|---|---|---|---|---|
| smux-owner | 1 | (unblocks CU-003) | landed; native scenario needs a native rebuild + SIMPLE_BINARY | #9211 |
| identity-binding (pane binding) | 2 | REQ-CARET-UI-001, REQ-CARET-UI-002 | landed (pure core); views not wired, provider/generation still constant | #9200 |
| ext-manifest-v2 | 3 | REQ-CARET-EXT-001, REQ-CARET-EXT-002 | landed; host registers/drops v2 contributions, nothing consumes them yet | #9207 |
| ide-tui-profile | 4 | REQ-CARET-EXT-003 | landed; TUI and GUI share one activation plan | #9201 |
| tui-cell-writer | 5 | REQ-CARET-UI-003 | landed | #9202 |
| leader-keys | 5 | REQ-CARET-UI-004 | landed (pure core); not wired into the TUI loop, no F10 remap | #9212 |
| observer (core) | 6 | REQ-CARET-OBS-001..003 | landed (pure core); no IO wiring | #9203 |
| trace-view-provider | 7 | REQ-CARET-TRC-001..003 | landed (pure core); no IDE view wiring | #9214 |

### Waves 2-3 (2026-11-15) — wiring into production callers

| Lane | Requirements | Status | PR |
|---|---|---|---|
| session identity | REQ-CARET-UI-001/002 | landed; real provider, restart ledger bumps generation, stale drafts rejected, terminal label from binding | #9233, #9287 |
| key resolver | REQ-CARET-UI-004 | landed; `cs` keys routed through `route_workbench_key`, leader n/p/1-9 -> `/switch` | #9234 |
| observer adapters | REQ-CARET-OBS-* | landed; observation builder, provider adapters, status text | #9237 |
| extension lifecycle | REQ-CARET-EXT-* | landed; deactivate drops pending invocations, context keys, builtin caret ext | #9242 |
| trace view render | REQ-CARET-TRC-* | landed; `trace_view_lines`, view state, impact edges | #9243 |
| observer live (F) | CU-008/009/010 | landed; hook_bridge -> observer log -> TUI/GUI status; bridge_worker is a separate process (log not shared) | #9294 |
| cs terminal surface (G) | CU-005 | landed; leader m, byte-safe chunk carry, guarded raw send | #9295 |
| IDE trace views (H) | CU-006/011 | landed; `view.show trace.explorer`, keybinding `when`, caret.* -> `/switch`; controller holds no snapshot yet | #9301 |
| roster (I) | CU-001/004 | landed; pin/MRU/fuzzy `/switch`, detach keeps real children alive | #9313 |
| P6 gates (J) | CU-015/016 | bug-resolve + MCP close gate; workaround revert candidates in `check_dbs` | #9315 |
| P7 checklist (K) | CU-020 | `/capabilities` in `cs` from live probes; remote/fleet blocked | #9317 |
| cs generation (L) | CU-019/002 | live generation from the pid ledger in cs | #9330 |
| editor snapshot (M) | CU-011/014 | lazy canonical snapshot in `view.show` | #9329 |
| when + expires (N) | CU-006/016 | `when` on views/commands; `expires=` workarounds; check_dbs passes today | #9334 |
| TUI captures (O) | CU-017 | cell-width captures; 3 visibility-blocked specs now execute | #9332 |
| shell views (P) | CU-006 | TUI/GUI shells use `visible_view_ids` | #9343 |
| trace staleness (Q) | CU-013/014 | staleness producers + exact-edge corpus | #9342 |
| CI close gate (R) | CU-015 | blocking `check-bug-close-evidence.shs` | #9341 |

### Acceptance CU-001..CU-020 (2026-11-15)

All evidence is the seed interpreter on Windows. **No row is native-verified; every row is at best "met (interpreter)" and the program is not release-qualified.** P8 (release qualification) is open.

| CU | Status | Evidence / gap | Resume |
|---|---|---|---|
| CU-001 | partial | `roster_order_spec` 8/8; no 50-agent/5-host scale run, no attention grouping | scale spec on a Linux host with fleet transport |
| CU-002 | met (interpreter) | `caret_workbench_generation_spec`: 1,000 seeded ops, 3 sessions, >20 restarts, 0 wrong sends (#9330) | native run |
| CU-003 | met (interpreter) | `caret_workbench_e2e_spec` 2/2 ("unbound terminal"), `caret_workbench_prod_spec` 2/2 | native run with `LLM_CARET_NATIVE_BIN` |
| CU-004 | met (interpreter) | `caret_workbench_detach_spec` 1/1 (real children survive detach/switch) | native run |
| CU-005 | partial | `key_chunker_spec` 10/10; never driven against a live smux pane | live `cs` + smux pane capture |
| CU-006 | met (interpreter) | `caret_shell_visible_views_spec` 3/3: TUI and GUI shells list the same ids via `visible_view_ids`, false `when` hides in both, no eager load (#9343); `when_contribution_spec` 5/5 | native run; production `set_context_keys` caller |
| CU-007 | met (interpreter) | `deactivation_hygiene_spec` 10/10 | native run |
| CU-008 | partial | `observer_live_spec` 3/3, `observer_builder_spec` 13/13; no 10-minute live quiet-build run | timed live run |
| CU-009 | met (interpreter) | `observer_live_spec` approval -> "needs you" in TUI+GUI, replay no dup | native run |
| CU-010 | partial | lifecycle folded at render; disconnected host not observable (no fleet) | blocked on fleet transport |
| CU-011 | met (interpreter) | `trace_view_snapshot_spec` 9/9: list/show/refs equal the canonical service for the same snapshot (#9329) | native run; UI selection of show/refs |
| CU-012 | met (interpreter) | `ide_view_provider` badge rollup specs | native run |
| CU-013 | met (interpreter) | `impact_corpus_spec` 3/3: exact incoming/outgoing reverse-impact edges over a feature→req→design→spec→code→bug corpus (#9342) | native run |
| CU-014 | met (interpreter) | `trace_view_producer_spec` 4/4: `source_present` from pinned blob sha, `expected_generation` from the built graph; deleted/changed blob and bumped graph show one explicit line, no other-revision content (#9342) | native run; git-index/commit snapshots; reload path |
| CU-015 | met (interpreter) | CLI + MCP gate (`bug_close_gate_spec` 5/5, `bugdb_close_gate_spec` 3/3, #9315) and blocking CI/push gate `check-bug-close-evidence.shs` with 8 selftest fixtures (#9341) | native run |
| CU-016 | met (interpreter) | `workaround_revert_candidates_spec` 5/5 incl. `expires=` (#9334), `bug_linked_workarounds_spec` 10/10; candidates never applied | native run |
| CU-017 | partial | `caret_workbench_tui_cells_spec` 4/4: 80x24 + 120x40 Korean/emoji, real key routing, captures in `build/test-artifacts/caret_workbench/` (#9332); high-DPI desktop + screen reader blocked | GUI capture host |
| CU-018 | blocked | no cold/warm CPU/RSS/frame measurements | perf lane on native build |
| CU-019 | met (interpreter) | `caret_workbench_generation_spec`: real child restart bumps generation; gen-1 approval/draft/command receipts rejected (#9330) | native run |
| CU-020 | blocked | `capability_checklist_spec` 7/7; no provider reports loaded skills (Claude SessionStart payload carries none) and the workbench has no first-use hint surface | provider skill reporting upstream |

Open TODOs: `activation_hook_spec` now executes (8/10) with 2 genuine failures — `doc/08_tracking/bug/activation_hook_builtin_registry_unreachable_2026-11-15.md`; `capability_truth_spec` 11/11 and `chat_tui_runtime_spec` 21/21 now execute. P8 release qualification is open: it needs a native/self-hosted build (resume: the sanctioned `scripts/bootstrap/bootstrap-from-scratch.sh`, then rerun every row above with the native binary). Pre-existing base failures in `agent_workspace_spec` (2/9), `lifecycle_spec` (1), `runtime_security_spec` (1).

## Plan sections 12 to 14

## 12. Implementation phases, dependencies and release gates

| Phase | Priority / changes | Definition of done |
|---|---|---|
| **P0 — Baseline and unblock** | Pin release SHA, record actual `caret cs` and IDE GUI/TUI screenshots at 80×24, 120×40, 1440×900; inventory states/shortcuts; reproduce/resolve native smux owner bug; record provider/platform matrix and current SSPEC | Native and interpreted selected-agent→pane wiring verified; baseline evidence saved; no synthetic completion |
| **P1 — One identity/state owner** | `PaneBinding`, provider identity and session generation, ordered event projection, status axes, attention inbox and snapshot age; deprecate `MANAGED_PROVIDER`/constant generation path | Select/switch/input/approval never targets wrong process; reconnect does not spawn duplicate; missing evidence says Unknown |
| **P2 — IDE contribution v2** | Add view containers, native view providers, panels, status/timeline, context keys, activation/dispose; `--tui --profile caret` parity | One IDE shell can host Caret + editor + native Trace view; plugin load/unload no lifecycle side effects |
| **P3 — Interaction and layouts** | Roster, quick switch/MRU/pins, composer and target banner, attention overlays, child-agent hierarchy, source/tabs/previews, responsive/keyboard, GUI/TUI state parity | 50-agent navigation and input targeting, CJK/IME and focus all tested |
| **P4 — Observers/stall** | Provider event adapters, screen grammar packs, process/job heartbeats, confidence explanation, suspected-stall and conservative recovery | Real/recorded multi-provider tests distinguish quiet work, approval, crash, quota and disconnect |
| **P5 — Traceability** | Embed native Slop view; feature×layer/lifecycle matrix; refs/impact/gaps/changed files; source/SSPEC/bug/result deep links; qualification-aware badges | Same exact snapshot/edges/receipts in TUI, GUI, SDN/CLI and docs; structural-only not green |
| **P6 — Review and CI gates** | Worktree/diff/merge review, bug reproducer/prevention, workaround expiry/revert candidate, feature completion obligations | Bug/feature close prohibited by service/CI when proof missing; no UI-only overrides |
| **P7 — Fleet and skills** | Remote host/account panel, child orchestration, context hints/skills task setup, provider capability catalog, mobile after desktop qualified | No credential leak, remote reconnect continuity, accurate per-provider capability and guidance |
| **P8 — Release qualification** | Windows/Linux/macOS native; FreeBSD where backend is declared, TUI/GUI accessibility, performance, benchmarks, failure injection, screenshots; docs/CI | Published evidence report with all blockers, supported matrices and rollback option |

### 12.1 First useful release cut

Ship P0–P3 and a **limited P4 structured observer for installed Codex/Claude versions** first, after real tests. Keep other agents terminal-compatible with honest `unknown` semantic fields. P5 can follow without redoing session/extension architecture; trace view is useful even before full execution qualification if prominently marked structural-only. Do not wait for mobile, every plugin or a 1,000-agent scale run to deliver the first reliable UI.

### 12.2 Migration/compatibility

- Keep existing `caret cs` command grammar and session IDs where identity can be reconciled; deprecate duplicate render paths through adapters, not simultaneous process owners.
- Version persisted layout, session and provider observer packs. Produce read-only migration preview and reversible backup; never silently attach a historical session to the wrong worktree.
- Gate new UI behind a profile/feature flag until native smux binding and IDE plugin contract parity are proven; fallback attaches the **same existing session** or explains why attachment is unavailable.
- Add `Caret: Diagnose Setup` command: executable/provider version, detected smux owner, remote host, supported parser pack, build/toolchain, available trace index, last test receipts, missing capability. Never display `Connected` before actual handshake.

## 13. Requirements → SSPEC → CI acceptance matrix

Add stable `REQ-CARET-UI-*`, `REQ-CARET-EXT-*`, `REQ-CARET-TRC-*`, `REQ-CARET-OBS-*` IDs and nonfunctional criteria under existing `doc/02_requirements/...`; trace to real SPipe SSPEC and generated manuals in the repository's layout. The rows below are **proposed acceptance IDs**, not existing passing tests.

| ID | Requirement / test oracle | Scope |
|---|---|---|
| CU-001 | 50 agents/5 hosts, stable attention groups, pin/MRU/fuzzy search and exact selection | GUI+TUI interaction |
| CU-002 | 1,000 switch/focus/draft/scroll operations deliver 0 messages to wrong `(id,generation)` | Session/e2e |
| CU-003 | Selected agent displayed terminal process/pane validated by owner receipt; unbound pane explicitly marked | Native smux e2e |
| CU-004 | Closing/detaching any view does not kill agent; stop action affects only authorized target | Lifecycle |
| CU-005 | Input to focused CLI keeps VT/UTF-8/escape and smux `Ctrl+B` fidelity; unknown chord passes through | Linux/macOS/Windows PTY/ConPTY |
| CU-006 | IDE TUI and GUI Caret profile activate same logical views; no all-plugin eager load | Extension host |
| CU-007 | Extension deactivation cleans command/view/event subscribers; no session or worktree deletion | Plugin lifecycle |
| CU-008 | Terminal quiet during 10-minute active builder job heartbeat never marked confirmed hang | Observer negative |
| CU-009 | Question/approval prompt structured event creates correct attention; text-only ambiguous prompt does not auto-authorize | Provider adapter/security |
| CU-010 | CLI PID exit, child crash, rate limit, parent waiting children, disconnected host each distinguished | State classifier |
| CU-011 | Trace list/show/refs/ref-file match canonical service result for exact snapshot; GUI and TUI parity | Trace query |
| CU-012 | `pass`, `not_run`, `stale`, `incomplete`, `missing`, `waived` never flatten to green complete | Qualification/UI |
| CU-013 | Feature→requirement→research/design→acceptance/unit/integration→code→bug/commit reverse-impact exact edges | Graph closure |
| CU-014 | Missing blob, graph delta mismatch, cancelled/stale async request cannot display another revision's source | Snapshot safety |
| CU-015 | Bug close with no reproducer/prevention receipt is rejected by backend/CI, not only disabled button | Bug gate |
| CU-016 | Workaround expiry/fix generates explicit revert candidate; dirty worktree remains unchanged until authorized | Recovery |
| CU-017 | 80×24, 120×40, desktop, high DPI, Korean/emoji, keyboard, screen reader; actual user-event captures | Accessibility/render |
| CU-018 | CPU/RSS/startup/frame/trace query results measured with cold/warm runs and failure injection | Performance |
| CU-019 | Reconnect/session-generation race: old approvals, drafts and command receipts cannot target restarted child | Reliability/security |
| CU-020 | Provider skill checklist shows actual loaded capability, first-use hints decay, no unrelated provider instruction injection | Skills/help |

**Test placement proposal:**

- Unit: `test/01_unit/app/llm_caret/feature/caret_ui_*.spl` (or actual existing unit convention), `test/01_unit/app/slop/*`, `test/01_unit/app/traceability/*`, IDE extension v2 specs.
- Integration: `test/02_integration/app/ide/feature/caret_extension_*.spl`, mux + observer + trace projection.
- System: `test/03_system/app/llm_caret/feature/caret_workbench_ui_spec.spl`, `caret_agent_observation_spec.spl`, `caret_traceability_ui_spec.spl`, plus native `workspace_cli_system_spec.spl` and platform matrix.
- Generated/manual docs: `doc/06_spec/{01_unit,02_integration,03_system}/.../*.md`, native captures under the declared image/evidence paths. Do not place executable `.spl` under `doc/06_spec/`.
- New requirement/research/design/architecture/plan docs link to the same IDs through existing traceability checker. CI first enforces structural mapping, then exact eligible evidence and acceptance; never introduce a hard commit gate based only on unfinished P0 CLI qualification.

### 13.1 Test methodology

Use deterministic recorded provider event streams/PTY transcripts **and** actual native CLI/PTY/ConPTY on supported hosts. Mock the collector for unit tests but assert a real child echo/transform marker and authoritative pane correlation in system tests. Test renderer screenshots at several sizes, text/cell state and AX accessibility tree. Record source revision, test binary, toolchain, provider version, host OS, environment profile, snapshot and artifact hashes. Do not count zero-case test runs or source-only static pages as UI success. Re-run only affected checks after a meaningful change; avoid unbounded repeated green checks.

### 13.2 Release and CI policy

1. Branch/PR preflight: manifest v1/v2 decode, action permission/static contract, trace metadata/MD links, system-spec inventory and keybinding conflict analysis.
2. Native target job: package Caret/IDE profile, launch smux owner, real input/focus/screen, renderer, Unicode and frontend interaction. Windows native owner bug is a blocker until fixed, not silently skipped.
3. Traceability qualification: snapshot-bound identity, all required references, reproducible bug tests, prevention, runner receipts and applicable performance results. `missing/skipped/partial` is incomplete.
4. Approval gate: cross-provider session targeting, worktree deletion/merge/revert, remote process control and permission requests are checked by actual owner. UI-only confirmation insufficient.
5. Report gate: generate matrix and per-feature links with exact source/test/artifact IDs, include incomplete and failure states, publish only when diagnostic generation succeeds; `--check` is non-mutating.

## 14. Prioritized implementation backlog by concrete source seam

| Rank | Files/owners | Immediate implementation |
|---|---|---|
| 1 | `agent_workspace.spl`, smux owner/launch; recent Windows bug | Fix native entrypoint mismatch and prove owner attach/reattach before UI promises |
| 2 | `workbench/session_source.spl`, `pane_source.spl`, `session_contract.spl`, manager/process owner | Provider and generation identity; process↔pane binding; typed session projection |
| 3 | `src/lib/editor/extensions/{manifest,manifest_sdn,contract,host,registry}.spl` | V2 view/panel/timeline/status contributions and lifecycle |
| 4 | `src/app/ide/main.spl`, `src/app/editor/{gui_shell,tui_shell}.spl` | `--profile caret` native GUI/TUI activation, shared workbench view tree |
| 5 | `cs_dashboard.spl`, `cs_main.spl`, `workbench/tui_view.spl`, `gui_page.spl`, `gui_layout.spl` | Unified roster/attention/composer; real preview; richer labels; CJK cell writer; keyboard nav |
| 6 | new `app/llm_caret/observer/` + existing provider adapters | Event/hook/PTY detectors and resource/process correlation |
| 7 | `src/app/slop/*`, `src/app/traceability/*`, editor extension | Trace explorer/matrix/evidence in IDE with snapshot pinning |
| 8 | existing VCS/agent workspace/builder/test/bug DB owners | Review, worktree diff, trace impact, bug/exception/CI close gates |
| 9 | Spipe skill registry and Caret setup UI | Skills checklist, provider capability probes, contextual help/hints |
| 10 | system specs, platform CI, docs/evidence | Screen captures, load/latency, host matrix, rollout/rollback |
