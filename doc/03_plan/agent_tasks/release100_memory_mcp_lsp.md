<!-- codex-design -->
# Release 1.0.0 memory and MCP/LSP agent tasks

Status: active; no lane below implies full feature completion. Root is merge owner and final normal-capability reviewer. Branch: `work/release100-hardening-20261106`, isolated worktree `/private/tmp/simple-release100-hardening-20261106`, initial release base `e2ce7042552`. Preserve the original checkout's unrelated dirty work and other sessions' PRs.

| Lane | Owned work | Handoff and next unblock condition |
|---|---|---|
| memory_audit | Full memory requirement/evidence audit; assigned `src/compiler/80.driver/{driver_pipeline_passes,driver_hir_pipeline_support,driver_types}.spl`, `test/01_unit/compiler/driver/aot_borrow_gate_fail_closed_spec.spl`, `test/01_unit/compiler/semantics/param_effects/driver_nogc_param_effect_gate_spec.spl`, focused guide/bug/wiki; root owns comment-only `driver_aot_pipeline.spl` change | Prove semantic-policy ownership, fix strict no-GC bypass without widening borrow scopes, exact/adjacent controls; hand full remaining AC/FV/route ledger to root |
| mcp_lsp_audit | Full MCP/LSP audit; assigned `main_lazy_diag_tools*` and dedicated tests/docs | Fix empty-file/warning/path reliability, preserve structured LSP work; identify actual dispatch chain and real executable evidence |
| source_view | New shared source contracts/session/projection modules, `main_lazy_source_tools.spl`, focused tests/docs; root-coordinated `main_dispatch.spl`, `tool_table.spl`, `main_static_tools.spl` wiring | Frozen interfaces below; produce truthful bounded raw/range mappings. Per-method folded outline and semantic capability remain unimplemented until demonstrated |
| debug_truth | `main_lazy_debug_tools.spl` and focused debug capability regression/docs, coordinated with root | Reject placeholder successful debugger answers through central DebugService unsupported receipts; real RPC/target/provider implementation and execution evidence remain open |
| release_gates | Read-only runtime/provenance/bootstrap and release-gate investigation | Identify an admitted exact pure-Simple runtime or retain precise missing receipt/producer prerequisite; the inspected build has failed; retain that terminal result and identify a new admitted candidate without treating a stale PID as a live wait |
| traceability | New `release100_memory_mcp_lsp` requirements/NFR/architecture/design/test-plan/agent-task Markdown only | Retain full input scope and unresolved evidence; no source edits or acceptance claims |
| root | Scope, interface freeze, integration, independent review, complete gates and release-targeted PR landing | Resolve cross-lane edits, inspect evidence and review comments, merge only verified owned changes; full goal remains open until every obligation is proved |

Lower-model sidecars: N/A; the current parallel agents directly perform evidence-sensitive review. Root also owns generated-manual quality review. Repair authors cannot be sole authority for their own runtime/proof acceptance.

## Shared contracts and test conventions

Root has frozen source-view V1 names: `SourceSnapshotV1`, `SourceRangeV1`, `SourceSelectionV1`, `SourceProjectionV1`, `SourceViewPreferencesV1`; `source_view_session_new_v1`, `source_view_set_preferences_v1`, `source_view_commit_open_v1`, `source_project_ranges_v1`, and `source_project_raw_v1`. `main_lazy_source_tools.spl` consumes them with root-coordinated dispatch/registration wiring. These names define the current foundation boundary, not complete folded-outline or semantic implementation. Preserve existing helpers where available. New scenario flow vocabulary: `step("Open an immutable source snapshot")`, `step("Inspect bounded source context")`, `step("Apply a versioned preference")`, `step("Reject stale or unauthorized evidence")`, and `step("Validate mandatory ownership checking")`. Proposed setup/checker names are `setup_source_view_session`, `check_exact_source_ranges`, `check_session_preference_receipt`, and `check_ownership_admission`; owners may adopt existing canonical names instead with root review before use. These are planning names, not implemented helpers. Unresolved oracle bodies must use `assert(false)` or `fail(...)`, never placeholder PASS, and block verification.

## Completion discipline

Run each unchanged passing criterion once. Each retry changes implementation or adds new evidence; obey the applicable three-cycle skill cap and never exceed the repository six-cycle ceiling. Retain command, source/build/runtime identities, exit/result, executed cardinality and artifact paths. Unavailable host/provider rows remain open with named owner and exact resume prerequisite. Do not reinterpret documentation-only progress as product completion.

Land with a PR targeting `release/1.0.0`; root reviews exact diff and comments before owner-authorized merge. Tags/publication are outside this request. A partial slice may be independently reviewable, but cannot close the user's full selected plans.
