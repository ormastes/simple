# Browser jail: seccomp is a deny-list and in-process browsers are unjailed

- **Date**: 2026-08-15
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  ALLOW-list; problem 3 partially addressed: honest sandbox posture surface +
  refusal gate landed, worker routing still open; problem 2 still open)
- **Area**: runtime (C), app/browser, os/hosted
- **Research**: `doc/01_research/app/browser/browser_sandbox_model_research_2026-08-15.md`

## Problems

1. **seccomp deny-list**: `rt_browser_renderer_sandbox_enter`
   (`src/runtime/runtime_process.c:2384`) installs a seccomp-BPF filter whose
   default action is `SECCOMP_RET_ALLOW` (`:2372`) with a list of denied
   syscalls. Any syscall not on the list — including future kernel additions —
   is allowed. Standard browser practice is an ALLOW-list with default
   `SECCOMP_RET_KILL_PROCESS`.
2. **No namespaces / privilege drop**: the jail sets rlimits, `no_new_privs`,
   and Landlock, but does not unshare user/net/PID namespaces or drop uid, so
   a compromised renderer retains direct network reach unless every net
   syscall stays on the deny-list.
3. **In-process browsers bypass the jail**: only the hosted renderer worker
   (`src/os/hosted/hosted_browser_renderer_worker.spl:1249`, broker
   `hosted_browser_renderer_process.spl:1595`) enters the jail. The
   in-process browsers under `src/app/browser/**` and `src/os/apps/*browser*`
   evaluate page script in the host process with no OS confinement.

## Required fix (Phase 2 of the research doc)

- Convert the seccomp filter to an ALLOW-list with `KILL_PROCESS` default;
  enumerate the worker's actual syscall set (strace under the spec suite).
- Unshare user+net (+PID where possible) namespaces before entering the jail.
- Route the in-process browsers' page-script execution through the jailed
  renderer worker instead of the host process.

## Fixed 2026-08-15 (this change)

1. **seccomp ALLOW-list (problem 1: FIXED).**
   `browser_renderer_apply_seccomp` (`src/runtime/runtime_process.c`, applied
   by `rt_browser_renderer_sandbox_enter`) is now an ALLOW-list with default
   `SECCOMP_RET_KILL_PROCESS`: only read/write/readv/writev, close,
   fstat(/64), mmap(/2)/munmap/mprotect/mremap/brk/madvise, futex(+time64),
   clocks/nanosleep/gettimeofday, exit/exit_group, rt_sigreturn/sigreturn/
   sigaltstack/rt_sigaction/rt_sigprocmask/restart_syscall, epoll*/poll/
   ppoll(+time64), getrandom, sched_yield, getpid/gettid are allowed. The
   architecture check and (on x86_64) the x32-ABI kill are kept; the preinit
   startup deny filter (fork/exec/socket) is unchanged. Any other syscall —
   including future kernel additions — kills the process.
   Proven natively by a new self-check
   (`src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c`):
   a forked child enters the REAL jail via `rt_browser_renderer_sandbox_enter`
   (preinit contract simulated: argv[0]=marker, empty envp, fds 0..3 only),
   read/write on inherited pipe fds succeed, then `socket()` KILLS the child
   with SIGSYS (not the old EPERM deny-list behaviour). PASS on this host.
   Operational note discovered while testing: the jail's RLIMIT_NOFILE=4
   means the in-jail Landlock ruleset fd only allocates when the worker holds
   fds 0..3 only — a worker with a higher open fd fails `sandbox_enter`.
2. **Honest sandbox posture for the in-process browser (problem 3: partial).**
   New `src/app/browser/sandbox_status.spl`: `SIMPLE_BROWSER_SANDBOX=1`
   requests jailed rendering; `browser_sandbox_status()` reports
   requested/jailed/mode/reason fail-closed. `src/app/browser/main.spl` gained
   `--sandbox-status` and a gate: a sandbox request is REFUSED (exit 1, honest
   message) rather than served unjailed — never a silent sandboxed claim.
   Spec: `test/01_unit/app/browser/browser_sandbox_status_spec.spl`
   (3 examples, green).

## Still open (exact remainder)

- **Worker routing (problem 3 core)**: route `src/app/browser`'s page
  rendering (render_adapter/browser_engine_pixels_at) through the sandboxed
  renderer worker via the broker `hosted_browser_renderer_process.spl`
  (`HostedBrowserRendererProcess`, ~3.5k lines). When it lands, flip
  `browser_sandbox_worker_routing_available()` in
  `src/app/browser/sandbox_status.spl` (the single flip-line) and the refusal
  gate becomes the jailed path automatically. `src/os/apps/*browser*` remain
  unjailed too.
- **Namespaces / uid drop (problem 2)**: unchanged — no unshare(user/net/PID),
  no uid drop.
- Verification gap noted 2026-08-15: `bin/simple test
  test/01_unit/os/hosted/hosted_browser_renderer_worker_spec.spl` times out at
  the test-daemon's 120s worker budget on this host (pre-existing; the
  deployed `bin/simple` is a prebuilt binary that does not contain this C
  change, so the timeout is unrelated to the ALLOW-list).

## Interim mitigation (landed 2026-08-15)

Engine-level capability gate: untrusted page script
(`JsRuntime.new_browser`) is denied `require("process"/"os"/…)` and
`process.exit/cwd/nextTick` at native dispatch —
`src/lib/{gc_async_mut,nogc_sync_mut}/js/engine/interpreter_native.spl`,
spec `test/01_unit/lib/js/js_native_confinement_spec.spl`.

## Landing note (2026-08-15)

The seccomp ALLOW-list conversion, honest browser sandbox surface, and the
engine2d enum alias-path comparison fixes landed in origin/main commit
`f549cda1991a442a5678a129a4ae4d70c80ea760` (11 files, all pre-push guards +
C-runtime compile verified against the committed tree). NOTE: that commit's
message text was mislabeled by a landing-script heredoc bug — it repeats the
prior commit's "strict-create enum identity, vendored rspirv repair" subject
instead of describing the seccomp/sandbox/enum work it actually contains. The
TREE is correct; only the message is wrong. Force-push is disallowed here, so
the message was not amended.
