# Test runner false green: nonzero child exit after a clean assertion tally was silently forgiven (both runner layers)

Status: FIXED (this record), regression specs pending follow-up (see below)
Date: 2026-09-01

## Summary

`bin/simple test <spec>` (dispatches to the pure-Simple app,
`src/app/cli/dispatch/table.spl:102-107` -> `src/app/test_runner_new/main.spl`)
reported **PASS with rc=0** for a spec file whose `describe`/`it` examples all
passed but whose `fn main()` then failed at runtime (proven with an
unresolved-function call; the same shape covers a crash, an abort, or any
other error path that returns to the driver epilogue rather than calling the
process-control `exit()` builtin directly). The child actually exited 1; the
runner discarded that and reported the file green.

A second, narrower instance of the same class was found and fixed in the
Rust seed's own built-in (non-default) test runner
(`src/compiler_rust/driver/src/cli/test_runner/execution.rs`, reached only via
the `handle_test_rust` fallback registered alongside the pure-Simple `test`
command in `src/compiler_rust/driver/src/main.rs:533-539` — "Testing stays
pure-Simple unless the explicit repair-only override... is set").

## Root cause 1 (primary, live on every `simple test <spec>` invocation)

`src/app/test_runner_new/test_runner_single.spl`, function
`parse_spec_file_verdict` (was line 362) and its caller (was line ~1220-1226,
the `exit_code_spurious` bypass).

The driver (`src/compiler_rust/driver/src/cli/basic.rs`,
`report_spec_file_verdict`) prints one authoritative line per spec file,
always, on stdout, last:

```
SPEC FILE VERDICT: <path> outcome=<OK|ERROR|CRASHED|TERMINATED|TIMEOUT|NOT_RUN> declared>=N executed=N passed=N failed=N skipped=N dropped=N
```

This line is emitted whenever the module "ran to completion" in the sense of
returning to the epilogue normally — which includes `SpecOutcome::Ok` (truly
clean) **and** `SpecOutcome::Error`/`Crashed` (something went wrong, but the
process didn't hard-kill itself before the epilogue could run). Only `OK`
means nothing went wrong at all.

`test_runner_single.spl` added an `exit_code_spurious` bypass (bug:
`spec_runner_describe_tail_expression_exit_code`) to fix a real, different
problem: when `describe(...)` is literally the tail expression of an
implicit/explicit `fn main()`, its return value — an example count, not a
status — becomes the process's exit code, so a wholly-passing spec could exit
1 for no real reason. The bypass trusts the verdict line over the exit code
whenever `has_verdict==1 and executed>0 and dropped==0 and failed==0`.

**The bug: this `verdict_clean` check never looked at `outcome=`.** It
accepted `outcome=ERROR` exactly the same as `outcome=OK`, as long as the
example counts happened to look clean — which they will, because the BDD
table is tallied from the `describe`/`it` blocks that already ran cleanly
*before* the later failure in `fn main()` happened. Measured:

```
SPEC FILE VERDICT: .../pass_then_die_spec.spl outcome=ERROR declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0
error[E1002]: function `spec_main` not found
warning: test-runner: child exit 1 contradicted by a clean SPEC FILE VERDICT; trusting the verdict
Results: 1 total, 1 passed, 0 failed
PASS .../pass_then_die_spec.spl
rc=0
```

despite the child having genuinely exited 1 on a real runtime error.

### Fix

`parse_spec_file_verdict` now also extracts the `outcome=<WORD>` field
(new helper `extract_word_after`) and returns it; `verdict_clean` now also
requires `verdict_outcome == "OK"`. The `spec_runner_describe_tail_expression_exit_code`
shape still gets forgiven (its verdict is genuinely `outcome=OK`); the
runtime-error-after-clean-assertions shape (`outcome=ERROR`) no longer is.

Verified (checked-in `bin/simple.exe`, no rebuild needed — this fix lives in
`.spl` source, read fresh on every run):

```
$ bin/simple.exe test pass_then_die_spec.spl ; rc=$?
SPEC FILE VERDICT: ... outcome=ERROR declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0
Results: 2 total, 1 passed, 1 failed
FAIL .../pass_then_die_spec.spl
rc=1                                   # was rc=0/PASS before this fix

$ bin/simple.exe test ordinary_pass_spec.spl ; rc=$?     # negative control
Results: 1 total, 1 passed, 0 failed
PASS .../ordinary_pass_spec.spl
rc=0                                   # unchanged

$ bin/simple.exe test tail_expr_spec.spl ; rc=$?          # the ORIGINAL bug this bypass exists for
SPEC FILE VERDICT: ... outcome=OK declared>=0 executed=1 passed=1 failed=0 skipped=0 dropped=0
warning: test-runner: child exit 1 contradicted by a clean SPEC FILE VERDICT; trusting the verdict
Results: 1 total, 1 passed, 0 failed
PASS .../tail_expr_spec.spl
rc=0                                   # still correctly forgiven (outcome=OK)
```

## Root cause 2 (secondary, non-default Rust fallback runner)

`src/compiler_rust/driver/src/cli/test_runner/execution.rs`, function
`child_exit_error` (all three call sites: `run_test_file_safe_mode`,
the in-process SMF execution path, `run_test_file_native_mode`).

```rust
fn child_exit_error(exit_code: i32, passed: usize, failed: usize) -> Option<String> {
    if exit_code != 0 && failed == 0 && passed == 0 {
        Some(format!("Process exited with code {}", exit_code))
    } else {
        None
    }
}
```

Only fired when **both** `passed==0` and `failed==0` (the fully-vacuous
case). A run with `passed>0, failed==0` and a non-zero exit code produced
`None` — no error recorded — and every downstream consumer
(`TestRunResult::success()`, `artifact.rs`'s `Status:` line,
`print_result`'s PASSED/FAILED label, `total_failed` summation) reads only
`.failed`/`.passed`, never `.error`, so a message alone would not have been
enough even if one had been set: the file's `failed` count itself had to be
bumped.

This runner is not the default for `simple test` (see `main.rs:533-539`), but
is registered as a fallback handler on the same `test` command name, so it is
one config flag away from being live, and was clearly capable of the exact
same false-green class in isolation (proven by unit test before the fix:
`test_zero_failure_bdd_summary_does_not_create_exit_error` asserted
`child_exit_error(1, 1, 0) == None`, i.e. it locked in the bug as expected
behaviour).

### Fix

Replaced `child_exit_error` with `reconcile_child_exit_status(exit_code,
passed, failed, output) -> (failed, error)`, wired into all three call
sites. On a non-zero exit with `failed==0`:
- if the child's own `SPEC FILE VERDICT:` line reports `outcome=OK
  dropped=0` (`verdict_reports_clean_ok`), the same legitimate
  tail-expression shape is forgiven, mirroring the `.spl` fix's own gate;
- otherwise `failed` is bumped to `1` and an explanatory error is attached,
  so the file is genuinely counted as failed everywhere `.failed` is
  consulted, not merely annotated.

The vacuous case (`passed==0 && failed==0`) is unchanged: still left
untouched with a diagnostic message, so the caller's `executed_nothing()`
gate can classify it as ERROR rather than inventing a pass or fail count.

Verified with `cargo test --release -p simple-driver --lib
test_runner::execution` (39 tests before the outcome-gate addendum, 41 after,
including two new fixtures: `test_nonzero_exit_with_clean_ok_verdict_is_forgiven`
and `test_nonzero_exit_with_error_outcome_verdict_still_fails`).

## Blast-radius table

Measured against the checked-in `bin/simple.exe` (pure-Simple `test`
dispatch), before and after the `.spl` fix, unless noted:

| case | before fix | after fix | mechanism |
|---|---|---|---|
| (a1) pass-then-`exit(N)` directly in `fn main()` | correctly FAIL/rc=1 | unchanged FAIL/rc=1 | `exit()` is `std::process::exit` (`interpreter_extern/mod.rs:315`) — a real, immediate process kill. It never returns to the driver epilogue, so NO `SPEC FILE VERDICT:` line is ever printed for this shape, `verdict_clean` was never true, and the exit-code-trusting bypass never fired. This half of the class was never broken. |
| (a2) pass-then-runtime-error in `fn main()` (proven with an unresolved function call; same shape covers any error that unwinds to a normal `Err` return rather than a raw `exit()`) | **FALSE GREEN — PASS/rc=0** | FAIL/rc=1 | The runtime error is caught and returned as `Err`, which DOES reach `report_spec_file_verdict` (outcome=ERROR), so a verdict line WAS printed, and the outcome-blind bypass trusted it. This is the bug this record fixes. |
| (b) SEGFAULT/stack-overflow crash after assertions pass | correctly FAIL/rc=1 (measured: `blow_stack` infinite recursion after one passing assertion) | unchanged | Caught by the pre-existing `code == -1 or code == 143 or code == 144` signal-death branch (`test_runner_single.spl` ~line 1096), independent of the verdict-trusting bypass — a killed process prints no verdict line either. |
| (c) abort mid-run (a later `it` never reached because an earlier one calls `exit(N)`) | correctly FAIL/rc=1 (measured: two-`it` spec, second one calls `exit(9)` before its own assertion) | unchanged | Same as (a1): raw `exit()` kills the process before any verdict line, so the fail-closed "no verdict" path applies. |
| (d) zero executed examples (`pending(...)`, vacuous file) | correctly FAIL/rc=1 (measured: `Results: 1 total, 0 passed, 1 failed, 1 skipped`) | unchanged | Pre-existing fail-closed zero-executed guard (`test_runner_single.spl`, the `real_executed == 0` branch); unrelated to this bug and not weakened by this fix. |
| (e) timeout-killed spec | not independently re-measured here (see reasoning) | unchanged | Routed through the dedicated `SpecOutcome::Timeout` classification (`basic.rs`), which is explicitly excluded from `is_verified()`/`drop_check_applies()` and carries its own exit code (`SPEC_TIMEOUT_EXIT`) and verdict text (`outcome=TIMEOUT`); `test_runner_single.spl`'s `has_verdict_line`/timeout branch (~line 1116-1119) handles it before ever reaching the `exit_code_spurious` bypass, since `outcome=TIMEOUT != "OK"` even if it were reached. Not the same code path as this bug. |

Net: the false-green class in this record was narrow but real — it required
(1) all BDD examples that DID run to have passed, AND (2) a later,
non-process-killing failure in `fn main()`. Every other shape in the (a)-(e)
family was already correctly handled by pre-existing, unrelated guards.

## Files changed

- `src/app/test_runner_new/test_runner_single.spl` — `parse_spec_file_verdict`
  now returns `outcome`; new `extract_word_after` helper; `verdict_clean`
  requires `outcome == "OK"`.
- `src/compiler_rust/driver/src/cli/test_runner/execution.rs` —
  `child_exit_error` replaced by `reconcile_child_exit_status` (+ new
  `verdict_reports_clean_ok` helper), wired into all three child-process call
  sites; test module updated/extended.

## Unix impact

Both fixes are platform-independent by construction:

- The `.spl` fix is pure string parsing over the child's captured stdout/
  stderr text (`extract_word_after`, the `outcome==` comparison) — no
  platform-conditional code exists or is needed. `simple test` on Linux/macOS
  reads this exact source file every run, so the fix is live there
  immediately, with no separate build or deploy step (same "no build needed"
  property CLAUDE.md documents for any `src/lib`/`src/app` change to the
  interpreted layer).
- The Rust fix (`reconcile_child_exit_status`) does not touch any
  `#[cfg(unix)]`/`#[cfg(windows)]` branch in `execution.rs`; it operates on
  the already-captured `(exit_code, stdout, stderr)` tuple after
  `wait_with_timeout` returns, which is where the two platforms' process
  APIs already converge to a single representation.

Because the fix makes a non-zero child exit override a previously-trusted
clean tally, it is expected to **surface latent failures that were being
silently forgiven on Linux and macOS too** — any spec file, on any platform,
whose `describe`/`it` examples pass but whose `fn main()` later errors
non-fatally was reading as green before this fix and will now read red. That
is the fix working, not a regression; any such flip should be investigated
as the real (previously invisible) bug it is, not reverted.
