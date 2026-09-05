# Interpreter `run` path: text.index_of(needle, start) ignores the start offset

- **Date:** 2026-07-03
- **Severity:** P2 (silent wrong result; turns scan loops into infinite loops)
- **Status:** source fixed in the active pure-Simple evaluator; execution pending
- **Repro:**

```spl
val s = "a\nb\nc"
print s.index_of("\n", 2) ?? -1   # prints 1 under `bin/simple run`; expected 3
```

## Observed

Under the interpreter `run` path the two-argument form returns the first
occurrence from position 0, ignoring `start`. Any `while pos <= s.len(): val
next = s.index_of("\n", pos) ...` line scanner therefore never advances and
hangs forever (found while fixing the test-runner greenwash bug: the lib copy
of `bdd_summary_counts` hung once its earlier chained-call error was fixed).

## Expected

`index_of(needle, start)` searches from `start`, matching compiled-path
behavior (e.g. `src/app/test_runner_new/test_executor_parsing.spl` relies on
this pattern and works compiled).

## Workaround

Use `split("\n")` iteration instead of offset scanning in code that must run
interpreted (applied in `src/lib/nogc_sync_mut/test_runner/test_runner_single.spl`).

## Resolution (2026-07-16)

The active `_EvalOps` text-method owner now evaluates the second argument,
propagates evaluation errors, and forwards the integer start offset to the
host string search. One-argument behavior is unchanged and missing matches
normalize to `-1`. Focused behavior and source-owner contracts cover offsets
before, between, and after matches. Executable self-host verification remains
pending under the current no-build restriction.
