# MCP/LSP source-tool audit against the intent-view plan (2026-11-12)

Scope: REQ-MCP-2-2 (plan §2.2) first audit deliverable, narrowed to the seven
named defects. Baseline `origin/release/1.0.0` (`4449288fc57`), worktree
`C:/dev/wt/p1-mcpview`, phase-1 seed `bin/simple.exe` (Rust seed banner).
Evidence is `file:line` at that baseline plus a spec or handshake run here.
This is not `capability_audit.sdn`; the per-frontend x operation x language x
backend matrix remains OPEN.

## Runs used as evidence

| Run | Result |
|---|---|
| R1 `bin/simple.exe run src/app/mcp/main.spl < build/mcpview/probe_in.jsonl` (initialize, initialized, `tools/call source_open path=test/fixture/source_view/outline.spl`) | initialize answered; tools/call produced NO reply, stderr: `error: semantic: src/app/mcp/main.spl:79:5: in call to mcp_source_wrap_result_v1 ... method parse_outline not found on type TreeSitter` |
| R2 `bin/simple.exe test test/02_integration/app/mcp/source_open_intent_view_spec.spl` (pre-fix) | `SPEC FILE VERDICT ... executed=7 passed=0 failed=7`; every in-process `source_open` structural open died with the same `parse_outline` error |

## Findings (7 named defects + 2 found while auditing)

| # | Plan defect | Baseline evidence | Status at baseline |
|---|---|---|---|
| 1 | Empty call-hierarchy success | `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl:645-665`: `_handle_call_hierarchy_direction` now runs `incoming-calls`/`outgoing-calls` and parses edges with a truncation note (`:661-663`), but `:655-656` and `:664-665` still answer `[]` when the query exits non-zero, prints nothing, or the item fails to parse. | PARTIAL: real edges exist; a failed query is still reported as an empty success. |
| 2 | Raw reader forced numbers / full-file output | `src/app/mcp/main_lazy_diag_tools.spl:192-199` (`simple_read` prefixes every line with `N \| `), `:204` runs `simple check` on every read, no byte bound. `source_open` (`src/app/source_view/service.spl:284-285`) passes `numbers=false` and bounds raw/outline pages (`max_bytes` 1..8192, `:235-236`). | OPEN for `simple_read`; the bounded path exists only in `source_open`, which was unrunnable (R1). |
| 3 | False "clean" status | `main_lazy_diag_tools.spl:76-82` `diagnostic_check_status` no longer maps exit 0 to clean on its own (`:76` comment, 124 -> timed out, >=125 -> failed); `:208` still appends the status to every `simple_read`. | PARTIAL: status wording fixed; no Windows-drive/warning-on-success spec cited by this audit. |
| 4 | Deletion / multi-file / version in code actions | `src/lib/nogc_sync_mut/lsp/lsp_code_action.spl:163` still emits `"version": null` for every reconstructed document edit; `:217-219` legacy path requires `newText` to be a string (empty string accepted, so deletion is representable); `:190-205` validates nested multi-document edits and rejects duplicate URIs. | PARTIAL: version is never bound to a buffer revision on the legacy path. |
| 5 | Synthetic debug results | `src/app/mcp/main_lazy_debug_tools.spl:267-294`: `get_variables`, `stack_trace`, `evaluate` route to `_debug_unavailable` (`:85-99`), which asks `central_debug_service_v1_authorize` and returns `status`/`operation`/`reason`/receipt, never `main:1` frames or echoed expressions. | FIXED at baseline (honest unsupported); real backend execution still OPEN. |
| 6 | Ambiguous agent-global requester state | `src/app/mcp/main_session_state.spl:11-16` keeps one process-global `_MCP_LAST_READ_PATH`, set by every `simple_read` (`main_lazy_diag_tools.spl:189`); `src/app/simple_lsp_mcp/session_state.spl:31-37` `lsp_resolve_requester` falls back to `last_read` with only a label. One MCP process shared by two agents gets the other agent's requester. | OPEN. |
| 7 | Missing dialect-specific admission | No `shebang`/`dialect` handling under `src/app/mcp`, `src/app/simple_lsp_mcp`, `src/lib/nogc_sync_mut/source` (grep, 0 hits). `service.spl:252-253` admits structure only by `.spl` suffix and reports `native_structure_provider_unavailable_for_language` otherwise. | OPEN; the truthful refusal is in place, no SDN/SHS provider or dialect resolution. |
| 8 | (found) `source_open` structural modes unrunnable | `src/compiler/90.tools/source_outline_v1.spl:6-7` imports `TreeSitter` from `treesitter.outline` and calls `parser.parse_outline()` (`:79`), but that method lives in the façade `src/compiler/10.frontend/treesitter.spl:44-45`, which is never imported on this route. R1 and R2 reproduce it from both the stdio server and `dispatch_tool`. | OPEN at baseline; fixed in the §7/§8 slice PR (free function `treesitter_parse_outline_v1`). |
| 9 | (found) tool schema lacks intent/help | `src/app/mcp/tool_table.spl:472-475` advertises `path/mode/target/depth/max_nodes/cursor/start_byte/max_bytes/snapshot_id` only; no `intent`, no help affordance beyond the `[ess] [adv]` footer string (`service.spl:214`). | OPEN at baseline; added in the §7/§8 slice PR. |

## Consequences for the plan rows

- REQ-MCP-2-2: this report is the narrowed first deliverable; `capability_audit.sdn` stays OPEN.
- REQ-MCP-7-1/7-2/7-3/7-4/8-1/8-2: implemented in the follow-up PR with
  `test/02_integration/app/mcp/source_open_intent_view_spec.spl` (in-process +
  real stdio handshake on the seed). 7-5/7-6/7-7/7-8/8-3 remain OPEN.
- Defects 1, 4, 6, 7 need their own slices: fail-closed call-hierarchy errors,
  revision-bound `version`, per-agent requester binding, dialect admission.
