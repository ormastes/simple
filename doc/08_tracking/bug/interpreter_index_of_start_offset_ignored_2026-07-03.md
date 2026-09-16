# Interpreter `run` path: text.index_of(needle, start) ignores the start offset

## Re-verified 2026-09-13 — seed lane clean; pure-Simple lane still unverified (LEFT OPEN)

**Lane caveat (added in the same 2026-09-13 pass, after review):** this entry is
filed against the **pure-Simple / self-hosted** lane, which the run recorded
below does NOT exercise. No self-hosted binary is deployed on this host —
`bin/release/simple.exe`, `bin/release/x86_64-pc-windows-msvc/simple.exe` and
`bin/release/x86_64-pc-windows-gnu/simple.exe` all print the Rust
bootstrap-seed banner. Running the repro through the pure-Simple CLI on the
seed (`simple run src/app/cli/main.spl -- run <repro>`) emitted only lint
diagnostics and never executed the program, so that substitute lane does not
work either. The seed result below therefore shows only that the **seed** does
not exhibit the defect; it does NOT discharge the pure-Simple fix.
**This entry stays OPEN pending a deployed self-hosted binary.**

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

Ran the exact repro from the entry header:

```spl
fn main():
    val s = "a\nb\nc"
    print(s.index_of("\n", 2) ?? -1)
```

Result: prints `3` — the expected value. The reported wrong answer `1`
(start offset ignored) does not reproduce, so offset scan loops no longer
hang. The Resolution (2026-07-16) note said "executable self-host
verification remains pending"; that is now discharged on the seed lane
(measured). The pure-Simple self-hosted lane is still unverified here.

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
