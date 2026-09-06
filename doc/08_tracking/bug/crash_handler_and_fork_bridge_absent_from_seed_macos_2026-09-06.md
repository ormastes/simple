# BUG: the C crash handler and the fork bridge are absent from the Rust seed, so Phase 2 of the SIGSEGV hardening plan cannot be verified

**Status:** OPEN (blocked on a compiler deploy; no code fix attempted)
**Found:** 2026-09-06, macOS aarch64 (Darwin 25.5.0)
**Binary under test:** `src/compiler_rust/target/debug/simple` (the only binary
this lane is permitted to use; a bootstrap is forbidden this session)
**Blocks:** the first example of
`test/03_system/plan_acceptance/serial_sigsegv_and_test_hardening_spec.spl`
("A null-pointer deref in compiled mode recovers into a backtrace, not a bare
process crash"), i.e. Phase 2 of
`doc/03_plan/infra/audit/serial_sigsegv_and_test_hardening.md`.

## What the plan promises

`rt_install_crash_handler` (`src/runtime/runtime.c:2755`) installs
`_spl_crash_handler` for SIGSEGV/SIGBUS. That handler is real and complete: it
classifies `si_code` through `_spl_fault_class` (`runtime.c:2709`), writes
`[simple-runtime] Fatal: <signame> at address <addr> (si_code=N: <class>)` plus
a `Backtrace:` dump with async-signal-safe `write()`, and ends in
`_exit(128 + signum)`. `runtime.c:1647` calls it at process start.

The acceptance oracle asks for a spec that drives a genuine fault through it:
fork a child, crash it, and read `rt_fork_parent_stderr()` /
`rt_fork_parent_signaled()` the way
`src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl` already does.

## What is actually in the permitted binary

```
$ nm src/compiler_rust/target/debug/simple | grep -cE 'rt_fork_child_setup|rt_fork_parent_wait|rt_fork_parent_stderr|rt_fork_parent_signaled'
0
$ nm src/compiler_rust/target/debug/simple | grep -cE 'rt_install_crash_handler'
0
$ nm src/compiler_rust/target/debug/simple | grep -cE 'rt_ptr_write_i64'
2
```

The fork bridge and the crash handler are not linked into this binary at all.
Only the raw pointer primitive is.

## Behavioural confirmation

```
extern fn rt_ptr_write_i64(addr: i64, offset: i64, value: i64)

fn main():
    print "before"
    rt_ptr_write_i64(0, 0, 1)
    print "after"
```

```
before
rc=134
```

`134` is SIGABRT (a Rust-side abort), not `139` (`128 + SIGSEGV`), and no
`[simple-runtime] Fatal:` banner and no `Backtrace:` appear on stderr. The C
crash handler is not installed in this process. This is the "bare process
crash" the oracle exists to rule out — the oracle is honestly RED here.

## Why nothing was changed

Writing the promised fork test into
`test/01_unit/lib/crash/crash_bundle_spec.spl` would satisfy the acceptance
oracle's `contains("rt_fork_parent_wait")` needle while turning
`crash_bundle_spec.spl` itself red on this host, because
`rt_fork_child_setup` / `rt_fork_parent_wait` are unbacked here and an unbacked
extern returns nil silently (see
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`). That trades
one honest red for a green that asserts nothing plus a new red elsewhere.
`test/01_unit/lib/crash/crash_bundle_spec.spl` was therefore left untouched and
the acceptance example left failing.

## Unblock condition

A deployed binary that links `src/runtime/` (the C runtime archive), verified
by the `nm` counts above becoming non-zero and by the probe returning `rc=139`
with the `[simple-runtime] Fatal: SIGSEGV ... (si_code=...)` + `Backtrace:`
banner. At that point the spec to write asserts, on the parent side:
`rt_fork_parent_wait(pid, 10000) == 139`, `rt_fork_parent_signaled() == false`
(the handler intercepted and `_exit()`ed, so the child is WIFEXITED, not
WIFSIGNALED — asserting `true` here would be asserting the failure mode), and
`rt_fork_parent_stderr()` containing both `[simple-runtime] Fatal:` and
`Backtrace:`.
