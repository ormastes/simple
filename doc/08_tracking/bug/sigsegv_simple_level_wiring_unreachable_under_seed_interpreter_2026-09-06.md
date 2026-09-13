# SIGSEGV cannot be wired into the Simple signal layer: no C→Simple fault bridge, and the fork externs are absent from the seed interpreter

- **Filed:** 2026-09-06
- **Area:** runtime / signals / test harness
- **Blocks:** 3 of the 6 remaining open boxes in
  `doc/03_plan/infra/audit/serial_sigsegv_and_test_hardening.md` — Phase 2
  ("Test: deliberate null deref in compiled mode produces backtrace"),
  Phase 5 ("Wire SIGSEGV into the Simple signal layer") and Phase 5
  ("Add `on_segfault(fn)` callback registration for user code").
- **Extends:** `doc/08_tracking/bug/crash_signal_bundle_extern_gap_2026-07-29.md`
  (which already names the missing extern signatures for a crash→Simple bridge).
- **Acceptance oracles left RED by this:** the three same-named examples in
  `test/03_system/plan_acceptance/serial_sigsegv_and_test_hardening_spec.spl`.

## Facts measured 2026-09-06 on this host (macOS, `src/compiler_rust/target/debug/simple`)

1. **A SIGSEGV handler cannot hand control back to Simple.**
   `_spl_crash_handler` (`src/runtime/runtime.c`) is installed with
   `SA_SIGINFO | SA_RESETHAND` and ends in `_exit(128 + signum)`. A synchronous
   fault handler may not return — returning re-executes the faulting
   instruction — so no Simple callback can run *after* it, and running one
   *inside* it needs a C→Simple callback bridge that does not exist in either
   runtime. An `on_segfault(fn)` registration added today would therefore be a
   registration nothing could ever invoke.

2. **Routing SIGSEGV through the existing Simple signal API would be actively
   harmful, not merely useless.** `signal_handler_install`
   (`src/lib/nogc_sync_mut/io/signal_stubs.spl`) installs `_spl_signal_handler`,
   a latch that sets a flag and RETURNS, polled later by
   `signal_dispatch_pending`. For SIGSEGV that is an unbreakable fault loop,
   and the `sigaction` call would also displace the C crash handler, losing the
   faulting address, the backtrace and the new `si_code` classification.
   *Mitigated in this change*: `signal_handler_install` now refuses
   SIGILL(4)/SIGFPE(8)/SIGSEGV(11) and returns false. SIGBUS is deliberately not
   refused — it is 7 on Linux and 10 on macOS/BSD, where those numbers are
   SIGEMT and SIGUSR1, so a hardcoded number would refuse a legitimate SIGUSR1
   latch. Closing that needs a platform-aware signal-number table (open).

3. **The fork externs are not registered in the seed interpreter**, so no spec
   can drive a real forked crash from Simple today. Probe
   (`scratchpad/probe_fork_crash.spl`, externs copied verbatim from
   `src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl:41-49`):

   ```
   ERROR rt_interp_call error: ... "unknown extern function: rt_fork_child_setup"
   rc=139
   ```

   `/usr/bin/grep -rn 'rt_fork_parent_wait' src/compiler_rust/compiler/src/`
   finds it only under `pipeline/native_project/tests.rs` — there is no
   `insert_simple!("rt_fork_child_setup", ...)` in
   `compiler/src/interpreter_extern/mod.rs`. The fork bridge exists only for
   natively-built programs.

   Note the failure mode: an unregistered extern here is **fatal (rc 139)**, not
   the "silent nil" described in
   `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`.

4. **The Rust seed does not run `runtime.c`'s crash handler at all.** Probe
   (`scratchpad/probe_segv.spl`) dereferences address 8 via the registered
   `rt_volatile_read_u8`:

   ```
   rc=139        # and NOTHING else on stderr
   ```

   A process running `runtime.c`'s handler would have printed
   `[simple-runtime] Fatal: SIGSEGV at address 0x8 (si_code=...)` plus a
   backtrace. It printed neither, so `spl_init_args` →
   `rt_install_crash_handler` is not on the seed's startup path.
   Consequence: the `si_code` classification added to `_spl_crash_handler` on
   2026-09-06 is real and compiles clean (`cc -fsyntax-only src/runtime/runtime.c`,
   0 errors) but is only observable from a **natively built** Simple program
   that links the C runtime archive — it is not live for anything run through
   the seed. The same applies to the `WIFSIGNALED` inspection added to
   `spl_prefetch_wait`.

   Also note the interpreter's `rt_volatile_read_u64(0)` is rejected outright by
   `checked_mmio_addr` ("requires a positive non-null host address"), so a
   *null* deref cannot even be expressed through that path — address 8 is the
   nearest genuine wild-pointer probe.

## Unblock condition

Any ONE of these makes the three boxes implementable:

- Register the `rt_fork_*` family in `compiler/src/interpreter_extern/mod.rs` so
  a spec can fork, crash a child, and read `rt_fork_parent_stderr()` /
  `rt_fork_parent_signaled()` — this alone unblocks Phase 2's test, and is the
  smallest change.
- Add a crash→Simple bridge with the signatures already filed in
  `crash_signal_bundle_extern_gap_2026-07-29.md` (a last-words hook invoked from
  `_spl_crash_handler` before `_exit`, plus a `si_code` accessor) — this unblocks
  both Phase 5 boxes.
- Deploy a natively built full-CLI `bin/simple` (blocked separately on bootstrap).

Until then the three acceptance examples are correctly RED and
`serial_sigsegv_and_test_hardening_spec.spl` keeps `# @tag:in-development`.
