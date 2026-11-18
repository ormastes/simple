# MCP compatibility diagnostic truth

The legacy `simple_read` contract still returns numbered source and runs the existing bounded check. The separate source-view route owns folded projections and sessions; this compatibility path does not claim those features.

Reads use `file_read_result`, so an empty file is readable and missing/failed reads remain errors. Text compatibility diagnostics locate numeric line/column fields after path prefixes, including Windows drive letters and colon-containing paths. The text and JSON formatters share location detection.

Read, edit and multi-edit results retain diagnostics even when the check exits successfully. Timeout, producer failure, missing output, and unverified text completeness are distinct from findings. A successful exit with no parsed diagnostics is not proof of a clean canonical DiagnosticV1 analysis. The compatibility formatter still does not preserve multiline labels or macro provenance; the planned structured diagnostic store must supply those.

Runtime admission is pending: the installed v1.0.0-beta binary is not admitted Stage4 and fails before the new regressions in bounded_bytes.spl. Do not advertise this source repair as deployed behavior until an admitted MCP binary and public-interface smoke pass.

<!-- antigravity-early-defect-detection-2026-11-18 -->

## Structured `simple_lsp_mcp` diagnostic envelope and non-blocking adapter (`WP-08`, 2026-11-18)

Extended by [early_defect_detection_2026-11-18.md](../../03_plan/compiler/early_defect_detection_2026-11-18.md) (`ED-01`, `ED-07`, `ED-10`, `ED-T05`, `ED-T29`) across `src/app/simple_lsp_mcp/lsp_diagnostics_structured_v1.spl`, `src/app/simple_lsp_mcp/tools.spl`, and `src/app/simple_lsp_mcp/protocol.spl`:

### Structured Diagnostic Envelope (`lsp_diagnostics_structured_v1.spl`)

LLM agents consume structured JSON diagnostic receipts (`schema_version: 1`) rather than scraping human CLI text (`ED-10`). Every `simple_lsp_mcp` structured diagnostic response carries:

- `status`: `"complete" | "incomplete" | "timed_out" | "failed" | "unavailable"`.
- `completeness`: `"pass" | "fail" | "incomplete" | "timed_out" | "unavailable"`, paired with boolean `clean` (`true` strictly when `status == "complete"`, `completeness == "pass"`, and `diagnostics.len() == 0`).
- `coverage`: `LspDiagCoverageV1` (`{syntax_checked, semantic_checked, lint_checked, source, reason}`), setting `lint_checked: true` only when lint actually executed without a parse/block abort (per-rule count `CoverageReceiptV1` integration is a future phase extension).
- `snapshot_hash`: content hash (`s1-...`) of the target file snapshot (or `"missing"` when absent).
- `policy_digest`: deterministic `DiagnosticRulePolicy` digest (`p1-...`, or `"policy-unavailable"` when policy text is absent; `WP-04`).
- `task_handle`: opaque handle (`lsp-diag-task-<seq>`) backed by the bounded 64-entry in-memory ring buffer (`_LSP_DIAG_TASK_ENTRIES`) for polling timed-out, incomplete, or gated requests (`lsp_diagnostics` accepts `task_handle` polls without requiring `file`).
- `diagnostics`: `LspStructuredDiagItemV1` items (`id`, `code`, `severity`, `message`, `file`, `line`, `col`, `end_line`, `end_col`, `source`).
- `ranked_fixes`: `LspRankedFixV1` candidates preconditioned on `required_snapshot_hash` and `expected_text` (`confidence`, `applicability`, `preconditions`, `replacement`).
- `next_actions`: explicit `LspNextActionV1` agent continuation actions with `kind` in `poll_task`, `run_targeted_check`, `inspect_diagnostics`, `enable_or_retry_diagnostics`, or `apply_ranked_fix`.

### Bounded Source-Mode Adapter and Startup Closure (`ED-T29`)

To preserve `simple_lsp_mcp`'s lightweight startup closure (importing only `.json_helpers`, `.lsp_command_metrics`, and `app.io.minimal_runtime_ops` — zero `app.io.mod` or `compiler.*` imports) and avoid nested CLI subcommand deadlocks (`[C12]`), the v1 adapter resolves diagnostics in order:

1. Poll `task_handle` in the 64-entry task ring buffer when supplied, upgrading immediately to an admitted cache hit if one has materialized for `(file, snapshot_hash, policy_digest)`.
2. Serve an admitted `DiagnosticBatchV1` cache hit (`SIMPLE_DIAGNOSTIC_BATCH_CACHE_FILE` or `<file>.diag.batch.json`) only when both `source_hash`/`snapshot_hash` and `target_profile.policy_digest` match the active snapshot and policy.
3. When `SIMPLE_LSP_ENABLE_DIAGNOSTICS=1` is enabled, run a synchronous bounded `process_run_bounded` check (`run src/app/cli/query.spl check <file> --format json` in source mode; `check --format=json <file>` with `check --json <file>` fallback in native mode); when gated off, return `status: "unavailable"` with a registered `task_handle` and `next_actions` guidance immediately. Asynchronous background `TaskRunner` `"analysis"` job dispatch is reserved as a future phase extension.

### Never Summarize Non-Complete Statuses as Clean

An envelope with `status` or `completeness` in `incomplete`, `timed_out`, `failed`, `pending`, or `unavailable` must **never** be summarized or formatted as `"clean"`, `"pass"`, or `"0 issues"` — even when `diagnostics` is empty (`ED-07`, `ED-T05`). Only `status == "complete"` over the requested scope with zero policy-violating findings constitutes a clean diagnostic verdict.
