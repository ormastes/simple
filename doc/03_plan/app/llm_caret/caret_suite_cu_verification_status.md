# Caret Suite CU-001..020 Verification Status (2026-11-17)

Source plan: `caret_suite_final_ui_extension_traceability_plan.md` (copied
verbatim from the 2026-11-14 owner plan; acceptance table near its line 639).
Companion: `caret_workbench_ui_plan.md`.

Method: `CU-0xx` tags grepped under `test/` and `src/` on
`origin/release/1.0.0`. "Spec exists" means a spec file carries the tag. These
specs are interpreter-lane specs; this pass did NOT re-run them, so interpreter
evidence is "spec present, last-run result not re-verified here".
**Native verification is PENDING for every row** — the native bootstrap is in
progress, and no row is claimed PASS without native evidence.

| CU | Requirement (short) | Specs tagged | Interp/static | Native |
|----|---------------------|--------------|---------------|--------|
| CU-001 | 50 agents/5 hosts, grouping, pin/MRU/search | workbench/roster_order, fleet_transport, fleet_gaps | spec present (loopback) | PENDING |
| CU-002 | 0 wrong-`(id,generation)` deliveries | workbench_session_identity | spec present (partial; no 1,000-op e2e) | PENDING |
| CU-003 | pane bound by owner receipt | workbench_session_identity | spec present (partial; no native smux e2e) | PENDING |
| CU-004 | closing view does not kill agent | workbench/roster_order | spec present (partial) | PENDING |
| CU-005 | VT/UTF-8/Ctrl+B input fidelity | tui_entry_keys, leader_keys, key_resolver, key_chunker | spec present; no PTY/ConPTY run | PENDING |
| CU-006 | IDE TUI/GUI same views, lazy load | ide/{ide_tui_profile_parity, caret_shell_visible_views, caret_shell_focus_publish, caret_profile_views, caret_context_keys, caret_context_keys_clear}, observer/skill_{replay_dedup,dedup_cap} | spec present | PENDING |
| CU-007 | extension deactivation cleanup | none | MISSING | PENDING |
| CU-008 | quiet build heartbeat never "hang" | observer/provider_heartbeat, observer_live, observer_stall_classifier | spec present | PENDING |
| CU-009 | structured prompt attention; no auto-authorize | observer_attention_inbox, observer_live, observer_stall_classifier | spec present | PENDING |
| CU-010 | exit/crash/rate-limit/disconnect distinguished | observer_live, fleet_transport, fleet_gaps, observer_stall_classifier | spec present | PENDING |
| CU-011 | trace query GUI/TUI parity | editor/trace_view_snapshot | spec present (partial) | PENDING |
| CU-012 | statuses never flatten to green | none | MISSING | PENDING |
| CU-013 | reverse-impact exact edges | traceability/impact_corpus | spec present | PENDING |
| CU-014 | no cross-revision source display | editor/trace_view_snapshot, trace_view_producer | spec present | PENDING |
| CU-015 | bug close rejected without receipts (backend) | bug_resolve/bug_close_gate, mcp/bugdb_close_gate, mcp/bugdb_resource_loads, bug/workaround_autoretire | spec present | PENDING |
| CU-016 | workaround revert candidate, dirty WT untouched | bug/workaround_revert_candidates, bug/workaround_autoretire | spec present | PENDING |
| CU-017 | sizes/DPI/Korean/a11y captures | workbench/gui_dpi_a11y, workbench_tui_cell_writer | spec present; no real user-event captures | PENDING |
| CU-018 | CPU/RSS/startup/frame measured | none | MISSING | PENDING |
| CU-019 | reconnect generation race | workbench_session_identity | spec present (partial) | PENDING |
| CU-020 | provider skill checklist, hint decay | observer/{skill_hint, provider_skill_report, codex_skill_signal}, workbench/capability_checklist | spec present | PENDING |

Spec paths are under `test/01_unit/app/` (`llm_caret/` unless another dir is
named). Gaps: CU-007, CU-012, CU-018 have no tagged spec — TODO add specs.
