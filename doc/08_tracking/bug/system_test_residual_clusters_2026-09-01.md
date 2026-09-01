# test/03_system residual failure clusters after the 2026-09-01 mechanical repairs

Date: 2026-09-01
Status: OPEN (residual). Five causes FIXED in PR #217; this record covers what is left.
Evidence base: 474 genuine (ran-and-failed) specs from `/tmp/suite4.log`, re-baselined
against a seed built from `origin/main` c0cae452481. The stale log was **not** stale:
49 of 49 sampled specs still failed on the fresh seed before any edit.

## Fixed in PR #217 (for context, not open work)

| # | cause | sites | verification |
|---|-------|-------|--------------|
| 1 | local `fn verify` helper stripped by merge `e274cd33719` (present at `4edef8fab8e`) | 391 specs / 840 calls | 318/318 batch specs rc=0 |
| 2 | accumulator half-renamed `sum`->`total`, declaration left `var sum = 0` | 155 | included above |
| 3 | grafted `tag = "odd"` in an unreachable else, `tag` undeclared, oracle nonsense | 33 | smoke 14/19/21 19/19 pass |
| 4 | `use M.*` where module `M.spl` defines a class also named `M`: the module dict shadows the class, so `M.new(..)` hits `method new not found on type dict` | 15 specs | Cursor_spec 0/4 -> 4/4 |
| 5 | 70 product fns in `src/app/llm_caret/claude_full/**` declared `-> nil` (a transliteration of TypeScript `void`); Simple's unit type is `()`, so these were non-unit returns with no return | 70 fns | WebSocketTransport_spec 0/7 -> 7/7 |

Cause 4 is worth a language-level decision rather than per-spec rewrites: a
module whose basename equals a type it defines is a silent shadowing trap. Either
the class should win in a glob import, or the collision should be a diagnostic.
Today it degrades into a confusing `type dict` error at the call site.

## OPEN cluster R1 — `test/03_system/check/**` host-evidence guards (~87 specs)

These are NOT defects to fix. They assert on real host evidence that does not
exist in this environment, and they fail correctly:

- `expected #!/bin/sh` / `simple_bin_status=forbidden` / `- reason=simple-bin-forbidden`
  — the guard rejects the Rust seed because no self-hosted `bin/simple` is deployed.
  The RED is the guard working, exactly as `.claude/rules/bootstrap.md` intends.
- Vulkan / RenderDoc / Electron / Metal / D3D12 capture-evidence gates — no capture
  artifacts on this host.
- `simpleos_kernel_fabricated_rt_symbol_guard_spec` — "no parseable pass/fail
  summary in test output; refusing synthetic pass". Fail-closed by design.

Do not "repair" these by weakening the assertion or the underlying
`scripts/check/*.shs`. They go green when a self-hosted binary and real capture
evidence are present, and not before.

## OPEN cluster R2 — `test/03_system/tools/**` long tail (26 specs)

After causes 4 and 5, 14 of 40 tools specs are green. The remaining 26 are
heterogeneous and each needs its own look. Sub-groups observed:

- **Missing build artifact.** `mcp/mcp_perf_regression_spec` asserts
  `bin/simple_mcp_server exists`; it is not built here. Same family:
  `mcp/mcp_lazy_perf_spec`.
- **Version-string drift.** `repl/repl_basic_eval_system_spec` and
  `repl/repl_error_recovery_system_spec` expect `Simple Language REPL v0.2.0`.
- **Foreign absolute paths baked into expectations.** `spipe/llm_finetune_retry6_*`
  and `retry7_*` expect `file:///mnt/data/wt-suite/examples/...` — another
  worktree's path. These can never pass outside that tree and should be made
  repository-relative.
- **Remaining transliteration artifacts.** `simple_lab/lab_hardening_spec` and
  `lab_robustness_spec` report "Common mistake detected: Use struct literal:
  Type { field: value }"; `llm/claude_full/utils/direct_member_message_spec`
  reports "undefined field 'message' on value of type 'nil'". Same TS-port
  origin as cause 5 but a different shape, so cause 5's fix does not cover them.

The spipe absolute-path sub-group is the highest-value item left: it is a real
portability defect, not an environment gap.
