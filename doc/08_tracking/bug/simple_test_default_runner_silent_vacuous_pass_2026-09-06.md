# `bin/simple test <spec>` exits 0 with NO output at all, and the Rust runner caches by spec mtime only

- **Filed:** 2026-09-06
- **Status:** FIXED 2026-11-11 — verified fixed on release tip: Defect 2's
  `source_tree_stamp` cache key is landed and live-verified on the refreshed
  seed; Defect 1 does not reproduce on the refreshed seed (default runner
  emits a full verdict). See the dated addendum at the end of this file.
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

## Defect 2 fix (2026-11-09) — fix-implemented-verification-pending

`result_cache.rs` now keys each cached verdict on a `source_tree_stamp`
(FNV-1a over path+mtime(ns)+size of every `.spl`/`.sdn` under `src/`,
excluding `compiler_rust`/`vendor`, plus the runner exe's mtime+size), stored
as an 8th column. A cached PASS replays only when the spec AND the stamp
match; legacy rows (no column) never match. Conservative: any source/runner
change re-runs everything — no stale PASS. Repro/prevention cargo tests:
`stamp_changes_when_imported_module_changes`, `empty_tree_without_exe_never_matches`.
cargo not run (disk < 30 GB). Defect 1 not reproduced on Windows seed (see claim notes).

---

## Addendum 2026-11-11 — lane runner7: FIXED verified on release tip (no lane code change)

Verified on the refreshed Windows seed (`bin/simple.exe` at HEAD
`68ab3383080f`, 2026-11-11):

**Defect 1 (default runner silent vacuous pass) — not reproducible.** The
default single-spec route (no `SIMPLE_TEST_RUNNER_RUST`) on a trivial probe
spec prints a real verdict and summary:
`SPEC FILE VERDICT: ... outcome=OK declared>=1 executed=1 passed=1 failed=0`
plus `Results: 1 total, 1 passed, 0 failed`, rc=0. Same observed on every
default-route spec run this lane performed (e.g.
`test/01_unit/compiler/parser/unsafe_identifier_block_header_spec.spl` ->
verdict line present, 4/4). The aarch64-Linux 2026-09-06 silent-exit state is
gone on this tip.

**Defect 2 (Rust runner cache keyed on spec mtime only) — fix live-verified.**
The 2026-11-09 `source_tree_stamp` change is present in source
(`src/compiler_rust/driver/src/cli/test_runner/result_cache.rs:208,243` — FNV-1a
over path+mtime(ns)+size of every `.spl`/`.sdn` under `src/` plus the runner
exe stamp, as the 8th cache column) and effective in the deployed binary:
1. Second run of an unchanged spec: `Skipped 1 unchanged test(s) (cached)` — cache hit.
2. `touch src/lib/nogc_sync_mut/spec.spl` (existing 70154-byte file in the
   spec's transitive closure; mtime-only change, git content clean): the next
   run RE-EXECUTED the spec (no `Skipped` line, ~600 ms real run) — an
   mtime-only change to imported source invalidates the cache.
3. Following run: `Skipped 1 unchanged` again — stable cache otherwise.

Verdict: both manufactured-false-green paths are closed on current tip. No lane
code change was needed; this addendum plus the status flip are the change.
