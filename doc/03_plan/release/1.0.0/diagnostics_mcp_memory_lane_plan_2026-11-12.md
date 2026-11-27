# 1.0.0 implementation lanes: unified diagnostics, MCP/LSP intent views, memory hardening

Date: 2026-11-12. Owner decisions: Fable-only lanes, parallel implementation,
CMM/T32 parser shares the Simple parser infrastructure, approach B (adapter
first) for the diagnostics core.

## Inputs (all design-only at the start of this plan)

| Plan | Register | Implemented at start |
| --- | --- | --- |
| `inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md` | `doc/02_requirements/feature/release100_memory_mcp_lsp.md` REQ-MCP-1..13 (126 rows) | 0 rows |
| `inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md` | same register, REQ-MEM (93 rows) | 0 rows |
| `inputs_2026-11-12/unified_diagnostics_parser_recovery_fix_suggestions_plan_2026-11-12.md` | REQ-DIAG-001..015 (this plan) | 0; the 2026-11-11 "implemented" table was never found in any worktree and is rebuilt |

## Lanes (parallel, one worktree + one `work/*` branch each, Fable)

| Lane | Branch | Owns (files) | Delivers | Gate |
| --- | --- | --- | --- | --- |
| diag-P1 contract | `work/diag-p1-contract` | `src/compiler/00.common/diagnostics/**`, new `src/lib/common/diagnostics/**`, `src/compiler/10.frontend/` shared token/span/line-start + recovery driver surface (exported, not rewritten) | `DiagnosticBatchV1`, `DiagnosticActionIndex`, batch status enum, byte<->UTF-16 `source_position`, re-exports; CMM-consumable parser-infra facade | REQ-DIAG-001/002/003 specs green |
| diag-P2 simple emit | `work/diag-p2-simple-emit` | `src/compiler/80.driver/driver_parse_diagnostic.spl`, `src/compiler/95.interp/interpreter/errors.spl`, `src/app/cli/query_diagnostics.spl`, `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl` | typed emit at parser/type sites, typed query API, LSP unsaved-overlay `didChange`, nonzero check / no artifact | REQ-DIAG-004/005/006 |
| diag-P3 cmm | `work/diag-p3-cmm` | `examples/10_tooling/trace32_tools/cmm_lsp/**`, `t32_lsp_mcp/tools.spl`, `src/app/t32_mcp_server/**` | typed CMM codes at producer, bounded recovery on the shared parser infra, UTF-16 spans, `diagnostics_v1` in MCP | REQ-DIAG-004/007, Journey B |
| diag-P4 markdown | `work/diag-p4-markdown` | `src/app/md_lsp/**`, `src/lib/editor/services/md_*.spl`, `src/lib/editor/services/diagnostics.spl` | MD1xxx codes on exact tokens, real publishDiagnostics, graph invalidation, import-safe transport split | REQ-DIAG-008/009, Journey C |
| diag-P5 fix service | `work/diag-p5-fix` (starts after P1 lands) | `src/lib/common/diagnostics/fix_*.spl`, LSP codeAction paths | multi-candidate ranking, revision-checked edit transaction | REQ-DIAG-010/011, Journeys D/F |
| mcp-views | `work/p1-mcp-intent-views-20261112` (running) | `src/app/mcp/main_lazy_source_tools.spl` + register rows | §2.2 audit, §7/§8 intent-based open | REQ-MCP-2-2, 7-x, 8 |
| mem-hardening | `work/mem-p1-ownership` | per plan §1-§3 owners (semantic checks under `src/compiler/35.semantics/param_effects/`) | first increment: strict no-GC bypass policy + diagnostics truth, from the plan's phase 1 | first REQ-MEM rows with executed specs |
| P6 verify (root) | `work/diag-p6-verify` (after P2-P5) | e2e/negative/perf specs, guides, generated manuals | REQ-DIAG-012..015 | `STATUS: PASS` |

Rules for every lane: TDD (red then green, both reported), modern SSpec,
no source-text oracles, no `pass_todo`, land small PRs on `release/1.0.0`
with `--admin --merge` after self-review, flip the register rows the PR
closes, record blocked rows explicitly. Shared files not in a lane's "Owns"
column are read-only for that lane; request the owner.
