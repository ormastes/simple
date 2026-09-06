# Test runner's ulimit caps make `simple test <dir>` unusable on macOS (2026-09-05)

## Status
PARTIALLY FIXED. Blocker (1) below is fixed in this working tree; blocker (2)
is OPEN and still fails every spec. Blocks the acceptance checkbox
`All formula tests pass (100% coverage)` in BOTH
`test/03_system/plan_acceptance/excel_to_math_lib_migration_spec.spl` and
`..._synthesis_spec.spl` (REQ-EXCEL-MATH-LIB-001 / REQ-EXCEL-MATH-SYN-002),
whose oracle is `<binary> test test/01_unit/app/office/sheets/` exiting 0.

## Measured symptom
```
$ SIMPLE_BINARY=<abs debug seed> <abs debug seed> test test/01_unit/app/office/sheets/
Results: 79 total, 0 passed, 79 failed
```
Every one of the 79 files reports `outcome=ERROR ... executed=1 passed=0
failed=1`. Yet each spec passes when run directly:
```
$ src/compiler_rust/target/debug/simple run test/01_unit/app/office/sheets/math_bridge_spec.spl
15 examples, 0 failures
```
So the 79 reds are the RUNNER, not the specs.

## Blocker 1 (FIXED here): `ulimit -v` is unimplemented on Darwin
`src/lib/nogc_sync_mut/io/resource_scope.spl` built the child's limit prefix as
`ulimit -v <kb> || exit 125; ...`. Darwin's kernel has no RLIMIT_AS, so every
shell rejects it -- verified on this host for both:
```
$ /bin/bash -c 'ulimit -v 1048576 && echo VOK'
/bin/bash: line 0: ulimit: virtual memory: cannot modify limit: Invalid argument
$ /bin/sh -c 'ulimit -v 1048576 && echo VOK'
/bin/sh: line 0: ulimit: virtual memory: cannot modify limit: Invalid argument
```
so `|| exit 125` killed EVERY bounded child with an infrastructure failure,
surfacing as `Error: Compilation failed: /bin/bash: line 0: ulimit: virtual
memory: cannot modify limit: Invalid argument`.

Fix landed: `_rlimit_as_enforceable()` (a single `file_exists` stat on
`/System/Library/CoreServices/SystemVersion.plist`, not a `uname` subprocess,
because this runs once per bounded child spawn) omits ONLY the `-v` clause on
Darwin and emits a loud stderr line naming the unenforceable cap. It does not
fail open silently, and `-t` / `-u` / `-n` keep their fail-closed
`|| exit 125`. Unlike `ulimit -u`, no substitute shell exists for this: it is a
kernel gap, not a shell gap, so a `_limit_shell`-style fallback is impossible.

Verified: the `Invalid argument` failures are gone and the advisory line
appears instead.

## Blocker 2 (OPEN): `ulimit -u 64` is a per-UID cap, not a per-test cap
With blocker 1 fixed the suite still reports 79/79, now with EMPTY stderr
(`Error: Compilation failed: `). Reproducing the runner's own compile step
byte-for-byte shows why:
```
$ /bin/sh -c "ulimit -u 64 2>/dev/null || true; exec timeout --kill-after=5s 65s \
    '<abs debug seed>' 'compile' 'test/01_unit/app/office/sheets/math_bridge_spec.spl' '-o' '/tmp/mb.smf'"
timeout: fork system call failed: Resource temporarily unavailable
rc=125
```
RLIMIT_NPROC is per-UID and counts every process the user ALREADY has, so
capping it at 64 on an interactive workstation (this host's soft limit is 4000,
with hundreds of processes live) makes the very next `fork` fail. The runner
never sees a useful error because `process_ops.spl` writes the ulimit with
`2>/dev/null || true` -- correctly, since the ulimit itself succeeds; the
failure lands later, in `timeout`'s fork, with its stderr classified as an
empty compile failure.

Default: `src/app/test_runner_new/test_runner_args.spl:95` `var max_procs = 64`
(and a hardcoded twin at `test_runner_execute.spl:682`). 64 is only safe inside
a container with a dedicated UID. There is no `--max-procs` flag; the only
escape is `--no-limits`, which drops every cap at once.

### Why this was NOT fixed here
Any repair is a policy change to shared test infrastructure: either raise the
default (which weakens the fork-bomb bound the cap exists for), or make the cap
RELATIVE (current UID process count + budget), which is the semantically
correct fix but needs a process-count probe on the spawn path. Both belong to
the test-runner owner, not to a formula-migration lane. Deliberately left open
rather than papered over.

## Blocker 3 (OPEN, and the DOMINANT one): `spipe_empty_examples` does not
## recognise `assert_*` as a real assertion
With `--no-limits` (every cap dropped, so blockers 1 and 2 are both out of the
way) the suite is STILL `Results: 79 total, 0 passed, 79 failed`, again with
`Error: Compilation failed: ` and empty stderr. `simple test` uses
`run_test_file_native` -- compile-first -- and the compile is what fails:

```
$ src/compiler_rust/target/debug/simple compile test/01_unit/app/office/sheets/math_bridge_spec.spl -o /tmp/mb2.smf
error: compile failed (...): lint: error: SPipe example has no real assertion
       or sanctioned skip [spipe_empty_examples]  --> line 25, column 1
  ... (repeated for every example in the file)
```

The sheets specs assert with `assert_true(...)` / `assert_equal(...)`.
`SPipeChecker::is_assertion_like` (`src/compiler_rust/compiler/src/lint/
checker_spipe.rs:600-615`) recognises only `expect(` / `expect_not(` / the
`to_*(` matchers / bare `expect <subject>`. `assert_*` is absent, so every
example in every one of the 79 files is judged assertion-free and the
deny-level lint fails the compile.

This is a lint FALSE POSITIVE, not a defect in the 79 specs: `assert_true` is
enforcing. Proof --
```
describe "assert_true is a real assertion":
    it "fails on a false condition":
        step("assert a deliberately false condition")
        assert_true(1 == 2)
```
runs to `✗ fails on a false condition`. And the specs themselves are green on
the interpreter path, which does not lint: `simple run
test/01_unit/app/office/sheets/math_bridge_spec.spl` -> `15 examples, 0
failures`.

### Why this was NOT fixed here
`is_assertion_like` lives in the RUST SEED. Repo policy is to fix behaviour in
pure Simple, and a seed edit additionally requires rebuilding
`src/compiler_rust/target/debug/simple` -- the exact binary other concurrent
sessions are using as their verification lane. Adding the `assert_*` family to
the allowlist is the right fix and is a few lines, but it belongs to a
seed/lint lane that can rebuild and re-deploy safely.

## Fix order
Blockers 3, then 2, then (already done) 1. Fixing 1 alone does not move the
`Results:` line; it only replaces one failure mode with the next.

## Related
Matches the previously recorded "Memory limit 16GB lie" class -- a per-UID
`ulimit` misfire being reported as a memory/compilation problem.
