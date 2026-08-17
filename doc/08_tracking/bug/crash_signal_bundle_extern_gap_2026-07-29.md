---
id: crash_signal_bundle_extern_gap_2026-07-29
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
severity: medium
discovered: 2026-07-29
discovered_by: lane DS7 (mission-critical robustness plan, Batch D, crash-native)
related: src/runtime/runtime.c
related: src/lib/nogc_sync_mut/crash/crash_bundle.spl
related: doc/07_guide/platform/misc/crash_containment.md
---

# No Simple-reachable hook from SIGSEGV/SIGABRT into CrashBundleV1 — needs new externs

## What exists today (verified by reading the C source, not assumed)

`src/runtime/runtime.c` already installs an **always-on** signal handler:

- `rt_install_crash_handler()` (runtime.c:1921-1932) installs `sigaction` for
  `SIGSEGV` and `SIGBUS` with `SA_SIGINFO | SA_RESETHAND`.
- It is called unconditionally from `spl_init_args()` (runtime.c:1301), so
  every process built on this runtime has it active from startup — nothing
  needs to opt in.
- The handler `_spl_crash_handler` (runtime.c:1898-1919) is async-signal-safe:
  it uses `write(STDERR_FILENO, ...)` (never `fprintf`/`malloc`), prints the
  signal name + fault address, then `backtrace_symbols_fd` for a raw stack
  dump, then `_exit(128 + signum)`.
- **SIGABRT is not covered** — only SIGSEGV/SIGBUS.
- `spl_panic()` (runtime.c:1845-1875) is separate and NOT signal-context: it
  runs on the normal call stack, writes a best-effort crash file to
  `$SIMPLE_LOG_DIR` or `/tmp/simple_crash_<pid>.log` via `fopen`/`fprintf`
  (safe there, since it's not called from a signal handler), then `exit(1)`.

## The gap

None of the above is reachable from Simple (`.spl`) code:

1. **No extern exposes `rt_install_crash_handler` to `.spl`.** It's called
   automatically in C; there is no way for Simple code to know it ran, query
   its state, or replace/augment its behavior.
2. **No signal → Simple callback path exists.** `_spl_crash_handler` cannot
   safely call into the Simple interpreter/JIT runtime (allocation, GC roots,
   and CrashBundleV1's own std.log/std.fs machinery are all signal-unsafe) —
   this is not a small binding gap, it needs either (a) a signal-safe raw
   memory snapshot written by the C handler that a *separate*, later,
   non-signal-context process/thread reads and turns into a CrashBundleV1, or
   (b) a `sigaltstack`-based deferred mechanism. Both are new runtime design,
   not a one-line extern add.
3. **SIGABRT has no handler at all** (`rt_install_crash_handler` only touches
   SIGSEGV/SIGBUS) — `abort()` calls (assert failures in C dependencies,
   `std::terminate`-style paths) currently produce no backtrace and no crash
   file.
4. **No register/CPU-context capture.** `_spl_crash_handler`'s `ucontext`
   parameter is explicitly discarded (`(void)ucontext;`, runtime.c:1899) — it
   is received but never read. A `CrashBundleV1` with real register values
   needs this decoded (arch-specific: `ucontext_t.uc_mcontext.gregs[...]` on
   Linux x86_64, different fields on aarch64/riscv).

## What would be needed to close it (concrete signatures, not stubbed)

New externs, roughly:

```c
// Register a raw-memory scratch buffer (allocated in advance, outside the
// signal handler) that _spl_crash_handler writes a minimal, POD-only
// snapshot into before falling through to the existing backtrace+exit path.
// Must be called from non-signal context at startup.
int64_t rt_crash_register_scratch(void* buf, int64_t buf_len);

// Read back whether the LAST process exit was a captured crash, and drain
// the scratch buffer's raw bytes. Intended to be called by a *new* process
// (supervisor/relaunch) or, for in-process consumption, from an atexit
// handler if the crash path chose exit() over _exit() for a given signal
// class (SIGABRT does, if added — see point 3 above; SIGSEGV/SIGBUS use
// _exit() and cannot run atexit handlers, so those need the scratch-buffer
// path, not atexit).
int64_t rt_crash_scratch_len(void);
int64_t rt_crash_scratch_read(void* out_buf, int64_t out_len);

// Extend rt_install_crash_handler to also catch SIGABRT (SA_RESETHAND is
// already used, so this is additive, not a behavior change for existing
// SIGSEGV/SIGBUS callers).
int64_t rt_install_crash_handler_with_abort(void);
```

Scratch-buffer contents (POD only, no pointers into GC/interpreter heap):
signal number, `si_addr`, decoded register set for the host arch, up to N
raw `void*` backtrace frames (symbolized later, on the Simple side, from
`backtrace()`'s raw addresses — `backtrace_symbols_fd` itself is
signal-safe but produces text, not a structured POD the .spl side can parse
cheaply; prefer capturing raw `void*[]` frames and deferring symbolization).

## What was built instead (this lane, no bootstrap required)

`src/lib/nogc_sync_mut/crash/crash_bundle.spl` — `CrashBundleV1`, a
structured, SDN-serializable bundle callers can build from `.spl` code that
already has a message and can run normal (non-signal-context) code: panic
sites, `Result`/`?`-propagated fatal errors, or any panic-adjacent hook.
Captures: version, best-effort build id (currently always `""` — no BuildId
manifest was found anywhere under `src/lib`, see search below), timestamp
(`rt_time_now_unix_micros`), pid (`rt_getpid`), caller-classified fault kind,
message, source location, and the trailing N `std.log` ring records (via a
newly-exported `RingBackend` surface in `src/lib/log.spl` — previously
module-internal, now reachable; see that file's "DS7 crash-bundle capture"
export comment). No register/signal capture — that's exactly the gap
documented above, left honestly absent rather than fabricated.

Also searched for an existing `BuildId`/build-manifest concept to populate
`build_id`: none found under `src/lib` (`grep -rl "BuildId\|build_id"
src/lib` returns nothing). If one gets added later, `CrashBundleV1.capture`
is the single place to wire it in.

## Disposition

Filed, not stubbed. Do not add a fake register/context field to
`CrashBundleV1` to make it "look" like real signal capture — the honest
minimal bundle (data model + panic/log-ring capture + SDN serialization) is
what's reachable without the runtime work above.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**STILL-OPEN, confirmed by CONTENT.** `grep -rn rt_install_crash_handler src/lib/`
returns exactly one line, `crash_bundle.spl:6`, and it is inside a COMMENT. No
`extern fn rt_install_crash_handler` is declared anywhere under `src/lib/`, so no
Simple-reachable hook exists. Unchanged.
