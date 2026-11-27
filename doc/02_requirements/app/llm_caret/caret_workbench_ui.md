# Caret Workbench UI — Requirements

**Date:** 2026-11-14
**Status:** Proposed requirements derived from plan section 13 (acceptance rows CU-001..CU-020) and section 11 (NFRs). They are not existing passing tests and nothing here is release-qualified.

Related docs:
- Research: [caret_workbench_ui_research_2026-11-14.md](../../../01_research/app/llm_caret/caret_workbench_ui_research_2026-11-14.md)
- Design: [caret_workbench_ui.md](../../../05_design/app/llm_caret/caret_workbench_ui.md)
- Plan: [caret_workbench_ui_plan.md](../../../03_plan/app/llm_caret/caret_workbench_ui_plan.md)
- TLDR: [caret_workbench_ui_tldr.md](caret_workbench_ui_tldr.md)

Source plan section numbers refer to `caret_suite_final_ui_extension_traceability_plan_2026-11-14.md`, split across the design (sections 3-11, 15), research (1, 2, 16) and plan (12-14) docs. Phase column is P0-P8 from plan section 12.

## UI family

| ID | Statement | Plan § | CU row | Phase |
|---|---|---|---|---|
| REQ-CARET-UI-001 | A session, its provider child and its smux pane are bound by stable IDs plus generation. A pane without a validated binding is shown as "unbound terminal", never as a specific agent's chat. | 3.2, 10 | CU-003 | P1 |
| REQ-CARET-UI-002 | Input and drafts never reach a wrong `(session, generation)`. A draft stays bound to its originating target until the user retargets; wrong-generation mutations are refused. | 6.4, 11.2 | CU-002 | P1 |
| REQ-CARET-UI-003 | The terminal grid writer is width-aware (terminal cells, not bytes) for CJK, full-width characters, combining marks and emoji. | 4.3, 11.3 | CU-017 | P3 |
| REQ-CARET-UI-004 | The TUI has a configurable leader key (default `Ctrl+G`) with raw passthrough of unknown chords and `Ctrl+G Ctrl+G` sending the literal byte. `Ctrl+B` stays the smux prefix. | 6.1, 6.3 | CU-005 | P3 |
| REQ-CARET-UI-005 | The roster handles 50 agents across 5 hosts with stable attention groups, pin, MRU and fuzzy search with exact selection. | 4.2, 6.4 | CU-001 | P3 |
| REQ-CARET-UI-006 | Closing or detaching a view never kills an agent; stop affects only an authorized target. | 5.2, 6.4 | CU-004 | P3 |
| REQ-CARET-UI-007 | Reconnect and generation races: old approvals, drafts and command receipts cannot target a restarted child. | 11.2 | CU-019 | P1 |
| REQ-CARET-UI-008 | Layouts at 80x24, 120x40 and desktop, high DPI, Korean/emoji input, keyboard-only and screen-reader access are verified with real user-event captures. | 11.3 | CU-017 | P8 |
| REQ-CARET-UI-009 | The task skill checklist shows what was actually loaded versus requested; first-use hints decay; no unrelated provider instructions are injected. | 9 | CU-020 | P7 |

## EXT family

| ID | Statement | Plan § | CU row | Phase |
|---|---|---|---|---|
| REQ-CARET-EXT-001 | Extension manifest v2 (`simple.ide.extension/2`) adds view, panel, status and timeline contributions (plus view containers) through the shared extension host. | 5.1, 5.3 | CU-006 | P2 |
| REQ-CARET-EXT-002 | v1 manifests (`simple.ide.extension/1`) decode unchanged; unknown fields or versions fail with a diagnostic. | 5.1 | CU-006 | P2 |
| REQ-CARET-EXT-003 | `simple ide --tui --profile caret` activates the same logical views as the GUI profile, with no eager load of all builtin apps. | 5.5 | CU-006 | P2 |
| REQ-CARET-EXT-004 | Extension deactivation disposes commands, views, subscriptions and keybindings without stopping sessions or deleting worktrees. | 5.2 | CU-007 | P2 |

## OBS family

| ID | Statement | Plan § | CU row | Phase |
|---|---|---|---|---|
| REQ-CARET-OBS-001 | Session state is reported on independent axes (lifecycle, transport, turn, progress, attention, resource) with an evidence-confidence value; unknown is never shown as zero. | 7.1 | CU-010 | P4 |
| REQ-CARET-OBS-002 | A stall classification table (structured approval, quiet work, suspected stall, failure, waiting on children, quota wait, disconnect) drives the UI. A terminal quiet during an active job heartbeat is never a confirmed hang. There is no automatic kill or speculative ping. | 7.3 | CU-008, CU-010 | P4 |
| REQ-CARET-OBS-003 | The attention inbox de-duplicates by `(session, generation, operation, kind)`. A text-only ambiguous prompt never auto-authorizes an action. | 7.4, 7.2 | CU-009 | P4 |

## TRC family

| ID | Statement | Plan § | CU row | Phase |
|---|---|---|---|---|
| REQ-CARET-TRC-001 | Evidence badges (`pass`, `not_run`, `stale`, `incomplete`, `missing`, `waived`) are never flattened to a green or complete state. | 8.3 | CU-012 | P5 |
| REQ-CARET-TRC-002 | Until an evaluator and receipt admission ship, the trace view shows the banner "Structural only — verification not available". | 8.3 | CU-012 | P5 |
| REQ-CARET-TRC-003 | Trace list, show, refs and refs-file in IDE views match the canonical query service for the exact snapshot, with GUI and TUI parity. | 8.2 | CU-011 | P5 |
| REQ-CARET-TRC-004 | Feature to requirement to research/design to acceptance/unit/integration to code to bug/commit reverse-impact uses exact typed edges. | 8.3, 8.4 | CU-013 | P5 |
| REQ-CARET-TRC-005 | A missing blob, graph delta mismatch or stale async response never displays another revision's source. | 8.7 | CU-014 | P5 |
| REQ-CARET-TRC-006 | Bug close without a reproducer and prevention receipt is rejected by the backend or CI, not only by a disabled button. | 8.5 | CU-015 | P6 |
| REQ-CARET-TRC-007 | Workaround expiry or bug fix produces an explicit revert candidate; a dirty worktree is unchanged until authorized. | 8.5 | CU-016 | P6 |

## NFR family

| ID | Statement | Plan § | CU row | Phase |
|---|---|---|---|---|
| REQ-CARET-NFR-001 | CPU, RSS, startup, frame latency, terminal throughput and trace query time are measured cold and warm with failure injection. Budgets in plan 11.1 are targets to measure, not claims. | 11.1 | CU-018 | P8 |
| REQ-CARET-NFR-002 | Service-side checks of session, generation, host, worktree and principal precede any input, approval, interrupt, stop, delete, merge or revert; terminal and provider text is untrusted. | 11.2 | CU-019 | P1 |
