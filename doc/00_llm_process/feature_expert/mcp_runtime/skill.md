# Feature Expert: MCP Runtime Verification

## Scope

Own the Simple MCP and Simple LSP MCP production-wrapper verification path:
`src/app/mcp/`, `src/app/simple_lsp_mcp/`, `bin/simple_mcp_server`,
`bin/simple_lsp_mcp_server`, the stdio integration spec, and the native smoke.

## Canonical evidence

```bash
bin/simple check src/app/mcp
bin/simple check src/app/simple_lsp_mcp
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
sh scripts/check/check-mcp-native-smoke.shs
```

Require an executed scenario verdict; wrapper-contract markers alone do not
prove the servers. Native smoke also requires admitted, hash-bound MCP and LSP
artifacts under `bin/release/<triple>/`.

## Interpreter performance boundary

Explicit `CompileMode.Interpret` entries must not bulk-load all of `src/app`,
`src/lib`, `src/compiler`, and `src/runtime`. Imports are resolved lazily by
`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl`.
The owner condition is in
`src/compiler/80.driver/driver_source_pipeline_loading.spl`. A regression
usually appears as 600+ source warnings, multi-gigabyte RSS, and CPU-guard
termination before the first scenario.

Current deployment caveat and resume evidence:
`doc/08_tracking/bug/mcp_stdio_interpreter_gate_exceeds_cpu_guard_2026-08-10.md`.

## Runtime-symbol boundary

MCP app code must use Simple facades. If JIT reports an unresolved `rt_*`
symbol, first prove the Simple facade, interpreter extern, and native runtime
implementation exist. Only then repair the central JIT runtime provider; never
add an MCP-local extern or accept interpreter fallback as native performance.

## 2026-08-28 — context-mode/ponytail parity lane
- `simple_ctx_execute*` now caps returned stdout at 100 KB (60/40 head+tail,
  `ctx_smart_truncate`), indexing the full output under `exec:<ts>`;
  `simple_ctx_search` gained query stopwords, a substring fallback
  (`match=substring`) and byte-length BM25 with a candidate prefilter.
- New hooks: `grep_hint.shs`, `agent_routing.shs` (routing block +
  Bash→general-purpose subagent upgrade, jq, idempotent); Bash hint retuned
  (recall on real >20-line results 2.9%→90.4%); net blocker heredoc-safe.
- Research/matrix: `doc/01_research/app/mcp/context_mode_ponytail_originals_vs_mimic_2026-08-28.md`;
  plan `doc/03_plan/app/mcp/context_ponytail_parity_plan.md`.
- Gotchas: `.spl` string literals collapse `}}`→`}` (bug filed); source-mode
  stdio server stalls mid-workload under load (bug filed) — measure
  handler-level.

## 2026-09-03 — code burn + toolchain log-opt plugins
- `simple_token_burn` (`main_lazy_telemetry.spl`, `tok_burn_rows`/`tok_burn_text`)
  groups the SAME ledger `simple_token_stats` reads, by `feature/tool`, ranked
  on `bytes_returned`. It answers "where did the budget go"; stats answers "how
  much did the mimics save". A row with `tokens_saved=0` is normal (a search
  result had no raw capture behind it), not a defect.
- `simple_log_optimize` + `main_lazy_log_opt.spl`: per-toolchain log filters as
  SDN descriptors under `config/log_opt/` (`SIMPLE_LOG_OPT_DIR` overrides).
  `detect`/`keep`/`drop` rows, substring match with `^` anchoring, `keep` beats
  `drop`. Adding a toolchain = adding a file; that is the whole dynamic-loading
  story, and it is deliberately not regex (a bad regex would fail the capture).
  Ships clang, rust, ninja, cmake, simple.
- Wired into `ctx_cap_exec_stdout` BEFORE the size cap — that ordering is the
  point: blind truncation drops the one `FAILED:` past the cap, classification
  keeps it. The RAW text is still what `ctx_index_text` stores, so a dropped
  line stays reachable via `simple_ctx_search`.
- Each application records `logopt/logopt:<name>`, so burn attribution per
  plugin is free.
- Spec `test/01_unit/app/mcp/log_opt_burn_spec.spl` (7 examples). Sabotage that
  bites: invert keep-before-drop in `log_opt_apply` → 6 passed / 1 failed.
- Host gotcha (this Mac, 2026-09-03): the deployed `bin/simple` is
  bootstrap-only — no `test`, no `run` — so specs here run on
  `src/compiler_rust/target/release/simple run <spec>`; attribute accordingly.
  `spipe-docgen` on that seed dies with `error[E1002]: function spec_kw_line
  not found`, so no generated manual for this spec yet.
- Recorded todo: `tok_record_at` re-reads the whole ledger on every append
  (O(n^2)); harmless at stats volume, but the log-opt path appends on every
  claimed exec, so it will matter first there.
