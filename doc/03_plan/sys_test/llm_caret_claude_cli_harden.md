# LLM Caret Claude CLI Harden — System Test Plan

Date: 2026-07-25

## Scope

This bounded plan covers `REQ-LLM-CARET-CLAUDE-TRACE-001..005` and
`NFR-LLM-CARET-TRACE-001..004`. It maps the direct 25-file Caret surface before
CLI and TUI execution. It is narrower than the separate full-parity plan and
must never be reported as every Claude function working.

## Executable gate

- Spec:
  `test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl`
- Manual:
  `doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.md`
- Checker: `scripts/check/check-llm-caret-claude-cli-trace.shs`
- Report: `doc/09_report/llm_caret_claude_cli_traceability.md`
- Symbol inventory: `doc/09_report/llm_caret_claude_cli_symbols.tsv`

## Scenario map

| Requirement/NFR | Scenario | Evidence |
|---|---|---|
| TRACE-001..002 | report/checker/inventory artifacts | All three paths exist |
| TRACE-001..002, TRACE NFR-003 | MDSOC and Claude/Simple report mapping | Required report sections and key roots/symbols |
| TRACE NFR-001..004 | offline deterministic derivation | No provider/network command; stable filesystem/sort/temp cleanup |
| TRACE-003..005 | exact computed closure | Final independent comparator: 25/25 files, 7,198/7,198 LOC, 506/506 declarations |

## Current result and boundary

The standalone checker passed once before the final security refactor, at
7,285 LOC and 515 declarations. The session guard forbids repeating an
already-green gate. After the no-temp local-Torch refactor, an independent
read-only reconciliation produced the final expected checker values:

```text
llm_caret_source_files=25
llm_caret_mapped_files=25
llm_caret_source_loc=7198
llm_caret_mapped_loc=7198
llm_caret_symbol_count=506
llm_caret_symbol_traced_count=506
independent_missing_symbols=0
independent_stale_symbols=0
```

The trace checker itself was not rerun against those final inputs. The modern
SSpec/manual are synchronized but unexecuted because a qualified
self-hosted runtime is absent. This direct map excludes the 848-file
`claude_full` parts bin and does not prove provider transport, cached CLI, or
real TUI behavior.

## Execution order

1. Run the checker once after direct Caret sources/report/inventory change.
2. With a qualified self-hosted runtime, execute the SSpec once in interpreter
   mode and require a nonzero example count plus exit zero.
3. Run docgen once and require `0 stubs`; review the visible four-scenario flow.
4. Continue shipped CLI process tests.
5. Continue component TUI tests, then the cached-artifact PTY gate.

## Pass/fail criteria

Pass requires exact current counts, checker exit zero, the final PASS marker,
executed SSpec assertions, and a current manual. Missing report/inventory rows,
network/provider invocation, stale exact counts, zero examples, or missing
qualified runtime is a failure/blocker.

## Manual policy

The four primary scenarios remain visible. Helper/checker source is folded.
The manual must state whether scenarios executed and must not infer live Claude,
full-parity, CLI-process, or PTY behavior from the static trace.
