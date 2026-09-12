# Test runner's ulimit caps make `simple test <dir>` unusable on macOS (2026-09-05)

**Status:** OPEN (unverified 2026-09-12)

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

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).

---

## Update 2026-09-12 (macOS arm64, `origin/main` @ `b9667d6584f`)

**Blocker 1 (`ulimit -v` on Darwin) — confirmed FIXED and now observable.** Every
bounded child spawn on this host prints the advisory line the record describes,
and no `Invalid argument` failure remains:

```
[resource-scope] address-space cap of 2147483648 bytes NOT enforced:
  RLIMIT_AS (`ulimit -v`) is unimplemented on this platform; cpu/pid/fd caps still apply
```

**Blocker 2 (`ulimit -u 64` is per-UID) — the hardcoded twin is FIXED here; the
default is deliberately left alone.**

What this change does: `run_test_file_safe_mode`
(`src/app/test_runner_new/test_runner_execute.spl`) hardcoded `max_procs = 64`
alongside `memory_bytes = 512MB`, `cpu_seconds = 30` and `max_fds = 256`, and
**ignored `options.no_limits`** — while every other lane in that same file gates
its caps on it (`if options.no_limits: 0 else: options.max_procs`, lines 168, 517,
572). So the one documented escape hatch from a per-UID cap silently did nothing
in safe mode. It now honours `--no-limits` like every sibling lane. This is the
"hardcoded twin at `test_runner_execute.spl:682`" this record names.

What this change does **not** do, on purpose: it does not raise the default (that
weakens the fork-bomb bound the cap exists for) and it does not make the cap
relative to the current UID's process count (the semantically correct fix, which
needs a process-count probe on the spawn path). The record's original reasoning
on both stands. What is no longer true is that a user hitting the per-UID wall has
no escape in safe mode.

**Repro status, stated honestly.** The record's own oracle — `simple test
test/01_unit/app/office/sheets/`, 79 files — was **not** reproduced to completion
here: this is a heavily shared host (load average 22, 20+ concurrent `simple`
processes from peer sessions) and the run was abandoned after 5 of 79 files rather
than left to distort the measurement. What *was* measured, on the pure-Simple
runner from source with the Sep-12 seed and the **default** caps in force
(`max_procs = 64`, no `--no-limits`):

| target | rc | result |
|---|---|---|
| single red spec | 1 | `Results: 1 total, 0 passed, 1 failed` |
| single green spec | 0 | `Results: 1 total, 1 passed, 0 failed` |
| 2-file directory (incl. `math_bridge_spec.spl`, one of the 79) | **0** | `Results: 16 total, 16 passed, 0 failed` |

`math_bridge_spec.spl` is the exact spec the record shows failing under the
runner, and it passes here with the cap applied — so the `timeout: fork system
call failed` shape did not reproduce on this host today. That is evidence the
symptom is host- and load-dependent (RLIMIT_NPROC counts the UID's *existing*
processes), **not** evidence that the per-UID cap is safe. A default of 64 is
still only sound inside a container with a dedicated UID.

**Status: PARTIALLY RESOLVED.** The `--no-limits` escape now works in safe mode.
The per-UID default remains as filed and this record stays OPEN for it; the
correct fix is still a relative cap (current UID process count + budget), and
that still belongs to the test-runner owner as a policy change.

Related: `doc/08_tracking/bug/macos_deployed_test_runner_load_only_greenwash_2026-09-12.md`
(the deployed mac binaries do not execute `it` bodies at all, and the new gate
`scripts/check/check-test-runner-executes-bodies.shs` that catches it).
