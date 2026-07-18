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

## Recurrence (2026-07-18): directory-mode `test` hang, same deployed-seed gap

Hit again independently while root-causing a genuine indefinite hang in
`simple test <directory>` on the FRESH bootstrap seed
(`src/compiler_rust/target/bootstrap/simple`, and the `bin/release/simple`
subprocess it spawns for each test file) — see
[[test_runner_fresh_seed_silent_noop_2026-07-17]]. `parse_test_output` /
`extract_error_message` / `output_has_zero_pass_summary` /
`extract_coverage_sdn` / `strip_coverage_blocks` in
`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl` all used the
`while pos <= len(): next = output.index_of("\n", pos); ...; pos = next + 1`
scan pattern this doc describes. Minimal repro against the deployed seed
confirmed the exact symptom again:

```spl
val s = "aa\nbb\ncc\ndd"
var pos = 3
print s.index_of("\n", pos) ?? -1   # prints 2 (first match), not 5 — pos never advances
```

Confirms the 2026-07-16 source fix has **not reached the deployed
`bin/release/x86_64-unknown-linux-gnu/simple` binary** (it still prints the
"this Rust-built Simple binary is a bootstrap seed only" warning on every
invocation, i.e. the "release" binary in this checkout is itself an
undeployed seed copy, not a rebuilt self-hosted binary) — this is the same
redeploy-wall class as other 2026-07-17 bugs
(`host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17`). Applied
the same `.split("\n")` workaround already used in
`test_runner_single.spl::bdd_summary_counts` to all five functions in
`test_executor_parsing.spl`. Left `checkpoint.spl`'s
`parse_quoted_field`-style single-shot `line.index_of("\"", first_quote + 1)`
call unfixed (not in a scan loop, so it silently returns `""` instead of
hanging — lower severity, out of scope for the hang fix, flagged here for
whoever redeploys the interpreter fix).
