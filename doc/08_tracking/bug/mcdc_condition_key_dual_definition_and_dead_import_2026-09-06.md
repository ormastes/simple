# Two pre-existing MC/DC runner defects, surfaced 2026-09-06
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Both were exposed while verifying unrelated work on the test runner, and
both are **pre-existing** — verified by `git diff` over every touched runner
file: zero occurrences of either symbol in any ADDED line
(`src/app/test_runner_new/test_runner_main.spl`,
`src/lib/nogc_sync_mut/test_runner/{test_executor_parsing,test_runner_coverage,test_runner_execute,test_runner_files}.spl`).

## 1. `mcdc_condition_key` has two co-compiled definitions with different signatures

The compiler warns:

```
warning: public function `mcdc_condition_key` has 2 co-compiled definitions with
2 differing signatures ((McdcConditionResult)->text vs (text,i64)->text); JIT call
sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to
the last definition when types are ambiguous — a fallback hit may still dispatch
to the wrong one.
```

The warning states the hazard precisely: an ambiguous call site can dispatch
to the WRONG function. In an MC/DC key builder that is a correctness problem,
not a style one — a mis-dispatched condition key silently mis-attributes
coverage obligations.

Fix is the one the warning names: rename the conflicting helper so the two
are distinct.

## 2. `extract_compiler_mcdc_obligation_manifest` is imported but not provided

```
[use-warning] 'extract_compiler_mcdc_obligation_manifest' is named in
`use std.test_runner.test_executor_parsing.{...}` but module
'src/std/nogc_async_mut/test_runner/test_executor_parsing.spl' does not
provide it (imported from src/std/nogc_sync_mut/test_runner/test_runner_execute.spl)
```

This is the same class the SFFI lane hit on 2026-09-05, where
`debug/remote/ptrace.spl` and `dwarf.spl` imported raw `rt_*` names that
`std.sffi.debug` never exported: the use-warning is silent in ordinary
output and **every call through the name died**. Whatever calls this one is
either dead or failing the same way.

Worth checking together: whether the manifest extractor was renamed or moved
and one side of the rename was missed, which would also explain defect 1.

## How they surfaced

Running the runner over a three-spec fixture directory
(`SIMPLE_BINARY=<debug seed> ... run src/app/test_runner_new/main.spl <dir>`)
prints both on the way to `[setup] mcdc-native-preflight: 8918ms`. Neither
aborts the run, which is why they have gone unnoticed.

