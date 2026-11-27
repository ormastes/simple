# BUG: the C crash handler and the fork bridge are absent from the Rust seed, so Phase 2 of the SIGSEGV hardening plan cannot be verified
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** fix-implemented-verification-pending (Core-C crash handler implemented 2026-11-26; awaits admitted Stage-4 macOS run of `crash_bundle_spec.spl`)
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


## Re-triage 2026-11-04 (release/1.0.0, macOS M4) — BLOCKED, not a seed defect

Root cause: the defect's layer is the binary under test, not missing code.
Both halves already exist in the C runtime and compile cleanly on Darwin:
`clang -fsyntax-only` reports 0 errors for `src/runtime/runtime_fork.c`
(`rt_fork_parent_wait` at :33) and `src/runtime/runtime.c` (crash handler), and
`scripts/bootstrap/p3-manual-link-stage3.shs:94` links `runtime_fork` into the
self-hosted binary. The Rust seed is bootstrap-only (CLAUDE.md "Default tooling"),
so adding a second Rust copy of the fork bridge/crash handler to it would be a
twin with no consumer, and would not exercise the C handler the plan verifies.

Blocker: no ADMITTED self-hosted macOS Stage 2+ binary exists today — lane1
(2026-11-04 06:01Z) built s2d but sanity was refused by the memory reserve
(7943 MiB < 12288). Unblock unchanged: on an admitted macOS binary, the `nm`
counts become non-zero and the null-write probe returns rc=139 with the
`[simple-runtime] Fatal: SIGSEGV` + `Backtrace:` banner; then write the fork spec
described under "Unblock condition". BSD: same C sources (POSIX fork/sigaction);
no BSD-specific change.

## Update 2026-11-04 — C contract verified natively; specs written and gated

**Verified natively (macOS arm64, Darwin 25.5.0, Apple clang):**
`src/runtime/test/rt_fork_crash_handler_selfcheck.c` links the real
`runtime.c` + `runtime_fork.c` and drives both directly (build line in its
header). Result: `crash child rc=139`, `15 checks, 0 failures`. It proves:
fork bridge captures a clean child's stdout/stderr/exit code; a forked child
that calls `rt_install_crash_handler()` and writes through NULL exits 139 with
`signaled == false` and stderr carrying `[simple-runtime] Fatal:`, `si_code=`
and `Backtrace:`; without the handler the raw signal is observed
(`signaled == true`). No C defect was exposed — the runtime code is correct;
the gap is purely that the Rust seed does not link it.

**Specs written (pending a self-hosted run):** the last describe block of
`test/01_unit/lib/crash/crash_bundle_spec.spl` now drives a real forked clean
child and a real forked null-write crash (asserting rc 139, `signaled ==
false`, banner + `Backtrace:`), exactly the unblock-condition contract above.
Both examples are wrapped in `skip_on_interpreter`, so on the Rust seed they
report an explicit skip (measured on seed `release100-7a0e6fe516f-20261031`:
`5 total, 5 passed, 0 failed, 2 skipped`) rather than a silent-nil vacuous
pass.

**Still pending:** run that spec on an admitted self-hosted macOS binary
(bootstrap lane) and confirm the two examples execute and pass; then flip this
record to FIXED.

---

## Addendum 2026-11-11 — lane seed2 — verdict STALE

Triage-first pass, batch 2, judged against the refreshed seed (bin/simple.exe,
build-commit 0791c2b7f4a7, 2026-11-11 refresh #8184). The row's premise — missing
code in the seed — was already disproven by the 2026-11-04 re-triage and native
selfcheck; nothing about the 2026-11-11 refresh changes the classification.

**Why STALE, not LIVE/SUPERSEDED:** the defect as filed ("handler + fork bridge
absent from the Rust seed") is not a code gap. Both halves exist and are correct
in `src/runtime/` (`rt_install_crash_handler` real POSIX impl at runtime.c:3244,
`_WIN32` stub at :3257 returning 0; `runtime_fork.c` is a `_WIN32` stub
deliberately — fork has no Windows equivalent). Adding a Rust-seed twin was
already ruled out 2026-11-04 as "a twin with no consumer". On the refreshed
Windows seed the `nm` counts for `rt_fork_*` / `rt_install_crash_handler` are 0
by platform design, not by omission; the macOS SIGSEGV/fork contract itself was
proven correct natively on macOS arm64 2026-11-04 (rc=139, signaled==false,
banner + Backtrace:, 15/15 checks). The residual blocker — an *admitted
self-hosted macOS Stage-2+ binary* — belongs to the macOS bootstrap admission
lane, not to this Windows P3 lane and not to `src/compiler_rust`.

**Seed-smoke (this lane's proof):**
`SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe test
test/01_unit/lib/crash/crash_bundle_spec.spl --mode=interpreter --no-cache`
-> `outcome=OK declared>=5 executed=5 passed=5 failed=0` and summary
`5 total, 5 passed, 0 failed, 2 skipped` — byte-identical to the expectation
recorded 2026-11-04 on the old seed (`release100-7a0e6fe516f-20261031`). The
two fork examples (`check_fork_bridge_captures_clean_child`,
`check_null_write_hits_crash_handler`) report an explicit interpreter skip, not
a silent-nil vacuous pass, exactly as designed.

**Cycles:** 0 (no live defect; no fix attempted). Evidence: this addendum +
seed-smoke transcript in `build/review/p3fix-seed2-20261111.sdn`.

## 2026-11-13 triage (P3 misc-a lane, work/p3-misc-a-20261113)

**STALE/SUPERSEDED (confirmed)** — seed2: not a code gap — handler + fork bridge exist in src/runtime by platform design; macOS SIGSEGV/fork contract proven natively 2026-11-04. Residual (admitted self-hosted macOS binary) belongs to the macOS bootstrap admission lane.

---

## Update 2026-11-26 — Core-C crash handler gap found and fixed; Darwin runtime test green

### Audit findings (`nm` + Core-C link inspection)
- `nm -g /private/tmp/simple-rc-build-20261122/p3-self-v3-20261124/manual-successor-v14/simple` (macOS arm64 Stage-3 self-hosted binary) exports `_rt_fork_child_setup`, `_rt_fork_parent_wait`, `_rt_fork_parent_stderr`, `_rt_fork_parent_signaled`, `_rt_fork_child_exit`, `_rt_ptr_write_i64`, and `_spl_init_args`, **but did NOT export `_rt_install_crash_handler`**.
- `nm -g /private/tmp/simple-rc-build-20261122/runtime-refresh-20261123/artifacts/libsimple_native_all.a` exports only `_rt_fork_shared_heap_v1` and `_rt_fork_shared_heap_wait_v1` (the Rust staticlib deliberately omits the C fork bridge and crash handler).
- **Root cause in C runtime:** Core-C native builds (`runtime_core_c_sources_v1()` in `src/compiler/70.backend/backend/runtime_compiler.spl:1077` and `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:539`) link `runtime_native.c` + `runtime_fork.c` and **exclude `runtime.c`**. Previously, `rt_install_crash_handler`, `_spl_crash_handler`, and `_spl_fault_class` lived **only** in `src/runtime/runtime.c`, and `runtime_native.c`'s `spl_init_args()` did not call `rt_install_crash_handler()`. As a result, Core-C binaries neither installed the crash handler at startup nor resolved `extern fn rt_install_crash_handler() -> i64`.

### Fix implemented
- Extracted `_spl_fault_class`, `_spl_crash_handler`, and `rt_install_crash_handler_impl` into `src/runtime/runtime_crash_handler_impl.h` (also hardening `_spl_crash_handler` against NULL `siginfo_t*` and clamping `snprintf` return length before `write()`).
- Declared `int64_t rt_install_crash_handler(void);` in `src/runtime/runtime.h`.
- Updated `src/runtime/runtime.c` (`SPL_RUNTIME_NATIVE_TWIN` wrapper) and `src/runtime/runtime_native.c` (strong `rt_install_crash_handler` definition + `rt_install_crash_handler()` call in `spl_init_args()`).
- Added `runtime_crash_handler_impl.h` to `src/compiler_rust/runtime/build.rs` and `rt_install_crash_handler` (`same`) to `scripts/check/runtime_bundle_duplicate_symbols_baseline.txt`.

### RED -> GREEN evidence (macOS arm64, Darwin)
- **RED:** Strict Core-C link of `src/runtime/test/rt_fork_crash_handler_selfcheck.c` (without `runtime.c`) failed:
  `Undefined symbols for architecture arm64: "_rt_install_crash_handler"` (`exit=1`).
- **GREEN:** Added `test/01_unit/runtime/rt_fork_crash_handler_darwin_test.c` and `test/01_unit/runtime/rt_fork_crash_handler_darwin_test.shs`. Running `sh test/01_unit/runtime/rt_fork_crash_handler_darwin_test.shs` passes:
  - Core-C (`runtime_native.c` + `runtime_fork.c`, strict link): `rt_fork_crash_handler_darwin_test: 24 checks, 0 failures` (clean exit `rc=0`, `spl_init_args` + explicit `rt_install_crash_handler` null-write `rc=139`, `SIGBUS` `rc=138`, `signaled==false`, `[simple-runtime] Fatal:`, `si_code=`, `Backtrace:`, and raw `SIG_DFL` `signaled==true`).
  - Legacy (`runtime.c` + `runtime_fork.c`): `rt_fork_crash_handler_darwin_test: 24 checks, 0 failures`.
  - Darwin Mach-O linkage: `runtime_native.o` strong `external _rt_install_crash_handler`, `runtime.o` `weak external _rt_install_crash_handler`; 4-config `-fsyntax-only` checks pass on both TUs.
  - Existing `src/runtime/test/rt_fork_crash_handler_selfcheck.c` linked strictly against Core-C: `crash child rc=139`, `15 checks, 0 failures`.

### Remaining verification
- Re-running `test/01_unit/lib/crash/crash_bundle_spec.spl` in compiled mode on an admitted Stage-4 macOS self-hosted binary rebuilt with this Core-C fix remains pending (compiler rebuild skipped here under the 24 GiB host memory guard).
