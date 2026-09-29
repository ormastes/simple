# Missing library TRACE32 stop polling breaks full CLI bootstrap link

## Symptom and cause

Linux full CLI native link from main `9a091` reports undefined
`Trace32Client.wait_for_stop`. `src/lib/nogc_sync_mut/debug/remote/exec/adapter_trace32.spl`
imports the library protocol client and calls this method from `wait_halt`.
The library class omitted it. The separate app protocol class has a method
with that name, but it sleeps and forces `Break`, which does not implement
waiting for natural target completion.

## Repair

The library protocol client now exposes
`wait_for_stop(timeout_ms: i32) -> Result<text, text>`.
It polls `EVAL STATE.RUN()` using the existing error parser and boolish state
normalizer, returning `Ok("stopped")` only for an observed false state.
The execution manager accepts the returned stop reason as text.

One monotonic deadline bounds polling, each command receives its remaining
budget through the existing `process_run_timeout` owner facade, and sleeps
are capped at 50ms and the remaining budget. A nonpositive timeout fails
before launching a command. Malformed state, protocol errors and transport
errors propagate as errors. The method never sends `Break`.

The existing status snapshot API and other commands retain their behavior.
Existing hardware status coverage expects `TRUE` or `FALSE` from
`STATE.RUN()` in `test/02_integration/t32_hw/25_status_snapshot_spec.spl`.

## Focused regression evidence

`test/01_unit/lib/debug/trace32/wait_for_stop_spec.spl` imports the production
client and exercises it through a local command transport. Scenarios cover
initially stopped, running then stopped, continuously running timeout, stalled
transport timeout, malformed state, transport failure, successful-exit
protocol error, and nonpositive timeout. Command logs assert no forced halt.
The fixture uses a path containing spaces to exercise direct argv handling.

Execution evidence is pending the root bootstrap lane's self-hosted runtime.
The attempted Windows focused check with the cached workspace release path
exited 1 before giving a code verdict: that executable identifies itself as
a Rust bootstrap seed and reports no admitted self-hosted check worker.
The seed is not used for a fallback verdict. This repair does not claim a
bootstrap or regression PASS before the self-hosted lane verifies it.

An equivalent eight-case native assertion harness was then submitted to the
admitted Linux Stage2 compiler (runtime capsule SHA
`ab17b585b56ddc09a79703b93f252b2586752cb5f474ec5dcfd9a7e6e6b596a1`),
with the pinned LLVM 23 toolchain, strict no-delegate/no-stub flags and
`core-c-bootstrap` runtime bundle. The single compile reached its 180-second
guard with exit 124, an empty diagnostic log and no binary. The assertions
did not execute. Before the guard, the compiler was runnable, with no direct
child, 7.4% CPU and a sampled RSS of 42,432 KiB at 2m52s. This snapshot is
not a measured peak RSS, and the observation does not identify the startup
stage or establish an unsupported construct.

Evidence directory on the D-backed Linux workspace:
`/mnt/simple-bootstrap-6b2/bootstrap-tools-lane-review-20260929/trace32/`.
Preserved files are `native-build.log`, `process-before-guard.txt`, and
`compiler-state-before-guard.txt`. The temporary harness and exact invocation
remain under the isolated checkout's ignored `build/trace32-review/`.
There was no identical compile retry.

## Release compatibility review (2026-09-29)

The exact original backport imported `sleep_ms` from `app.io.time_ops`, whose
release export list does not contain that name. Import the canonical
`std.nogc_sync_mut.io.time_ops` owner instead.

The app `process_run_timeout` Unix implementation rounds a positive subsecond
budget up to one second and permits ten seconds of SIGTERM grace. That does
not implement this polling method's millisecond deadline. The new
`process_run_bounded_direct` app owner facade forwards to the existing bounded
runtime capture without PATH preflight or process-governor acquisition outside
the deadline. The polling command limits each output capture to 4096 bytes.
The POSIX runtime owner uses a monotonic deadline and kills the owned process
group on timeout; the Windows owner receives the same millisecond budget.

The stalled transport assertion now requires a 200ms request to return within
800ms, and a second fixture ignores SIGTERM. These tests have NOT been run
with a qualifying self-hosted runtime: the installed release binary identifies
as a Rust seed, and the available pure Stage2 capsule has native-build only.
Source review and direct-env guard passed; dynamic compatibility, target
imports, protected admission, and release qualification remain pending.
The added compatibility fix changes the original exact-backport patch identity;
its original preparation receipt cannot attest to this updated head.
