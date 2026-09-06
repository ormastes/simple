# `bin/simple test <spec>` exits 0 with NO output at all, and the Rust runner caches by spec mtime only

- **Filed:** 2026-09-06
- **Status:** OPEN — reported, not fixed. Two independent defects in the test
  command are recorded here because both were hit in the same session and both
  manufacture false greens.
- **Severity:** High for a verification tool — a test command that reports
  nothing and exits 0 is indistinguishable from a passing run to any caller,
  human or CI.
- **Component:** `bin/simple test` dispatch —
  `src/compiler_rust/driver/src/main.rs:198`
  (`dispatch_to_simple_app("src/app/test_runner_new/test_runner_single.spl", ...)`)
  and the Rust fallback runner's result cache.
- **Host:** `bin/release/aarch64-unknown-linux-gnu/simple`, 50093192 bytes,
  mtime 2026-09-06 09:59 (aarch64 Linux, 20 cores). Worktree
  `.claude/worktrees/agent-aedac6d07c110fa8a` at `a12a19eb775`.

## Defect 1 — the DEFAULT (pure-Simple) single-spec runner prints nothing and exits 0

`bin/simple test <one spec>` routes to the pure-Simple
`src/app/test_runner_new/test_runner_single.spl`
(`main.rs:198`, gated by `test_should_use_single_runner`). In this worktree that
path produces **no verdict, no summary, and no per-test output whatsoever**, and
exits 0, in about 2.7 s.

Reproduced on three different specs, including a three-line one written for the
purpose so a spec-content explanation is ruled out:

```
$ time bin/simple test build/wi/probe_spec.spl > probe.log 2>&1; echo "exit=$?"
real    0m2.703s
exit=0
$ grep -viE 'warning|^ |^\||^$|^Use |^Example|-->' probe.log
Build and use the pure-Simple bin/simple instead.

Replace '#[runtime_intrinsics]' with '@runtime_intrinsics'
```

That is the entire non-warning output. `probe_spec.spl` is:

```simple
describe "Probe":
    it "adds":
        expect(1 + 1).to_equal(2)
```

Same result for `test/01_unit/compiler_core/interpreter/ops_spec.spl` and
`test/01_unit/compiler/interpreter/todo_builtin_spec.spl` — both real,
committed specs. No `SPEC FILE VERDICT:` line is emitted, although the format
exists and is asserted on elsewhere
(`src/compiler_rust/driver/src/cli/basic.rs:314,1121`;
`src/compiler_rust/driver/src/cli/test_runner/execution.rs:208`).

The documented escape hatch works and prints a real summary:

```
$ SIMPLE_TEST_RUNNER_RUST=1 bin/simple test build/wi/probe_spec.spl
Files: 1
Passed: 1
Failed: 0
✓ All tests passed!
```

`SIMPLE_TEST_RUNNER_RUST` must be exactly `"1"`
(`temporary_rust_test_runner_override`, `main.rs`).

**Why this is worse than a crash.** `.claude/rules/testing.md` already warns
that "`simple test <ABSOLUTE path>` runs nothing and exits 0". This is the same
failure mode on a RELATIVE path, i.e. on the exact invocation the rules file
recommends (`bin/simple test path/to/spec.spl`). Any lane that runs the default
command and checks only the exit code is currently green on a runner that
executed nothing.

**Not diagnosed here:** whether `test_runner_single.spl` fails to load, loads
and finds no examples, or writes its results somewhere other than stdout.
`dispatch_to_simple_app` returns `Option<i32>`; it returned `Some(0)`, so the
app was reached and reported success.

## Defect 2 — the Rust runner caches by SPEC file mtime, not by the source under test

With `SIMPLE_TEST_RUNNER_RUST=1`, a second run of an unchanged spec prints:

```
Skipped 1 unchanged test(s) (cached)
Files: 1
Passed: 3
Failed: 0
Duration: 0ms
```

This is correct behaviour for an unchanged world, but the cache key does not
include the code the spec exercises. Measured directly: with a spec importing
`compiler.core.interpreter.eval`, DELETING the short-circuit lines from
`eval_binary` and re-running reported `Passed: 3 / Failed: 0 (cached)` —
a green verdict for a tree whose interpreter was deliberately broken. `touch`ing
the spec and re-running reported the truth, `Passed: 1 / Failed: 2`.

This bites hardest on exactly the workflow the repo encourages: a `src/**` edit
needs no build, so the natural loop is "edit source, re-run spec" — and that
loop is precisely the one the cache gets wrong.

**Workaround until fixed:** `touch <spec>` before every A/B measurement, and
never trust a run whose output contains `Skipped ... (cached)` as evidence about
source you just changed.

**Suggested fix direction (not implemented):** fold a digest of the spec's
transitive `.spl` import closure into the cache key, the same way
`object_cache_key` already folds `compiler_fingerprint()` (see
`.claude/rules/commands.md` § "A `src/lib/**` change needs NO build").

## Evidence trail

Both defects were hit while producing the executable proofs recorded in
`interp_logical_short_circuit_2026-07-15.md`,
`interp_mixed_numeric_arithmetic_2026-07-15.md`,
`interp_while_body_scope_leak_2026-07-15.md` and
`interp_match_expr_binding_scope_leak_2026-07-15.md`, and the fix recorded in
`interp_scope_slot_reuse_stale_bucket_heads_2026-09-06.md`. Every measurement in
those records therefore states its lane as
`SIMPLE_TEST_RUNNER_RUST=1 bin/simple test` and `touch`es the spec first.
