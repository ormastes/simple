# FreeBSD bootstrap native-file timeouts detach live workers

Status: scoped admission safety fix implemented; focused regression checks pass.
Full compiler build, FreeBSD deployment, independent review and performance
comparison remain pending.

## Scope and identities

- Frozen guest source: `de37d9879ae74e1521df0f75e6aa0c48d2dea955`.
- Active FreeBSD LLVM native-build authority SHA-256:
  `0dc164a611cff051dbaac3156e88c933516b2cd80541e903187404b3a1f4a37f`.
- Guest PID 12893, FreeBSD ARM64/KVM, 20 vCPUs, 36 GiB RAM.
- Active command specifies `--threads 10`, LLVM and an existing private cache;
  it has no timeout override. Source default is 300 seconds.
- This is the Rust bootstrap authority, not a performance measurement of the
  resulting pure-Simple Phase 2 compiler.

## Observations

At 2026-10-04 04:44:36 UTC, `ps -H` reported twelve active `compile-*` threads.
In particular TID 109485 `compile-__init__.sp` had consumed 6:13.35 CPU time,
and TID 109508 `compile-llvm.spl` had consumed 5:25.22 CPU time; both remained
runnable near 99% CPU. CPU time alone exceeds the 300-second wall deadline.
The same threads were subsequently still runnable at CPU times 6:33.62 and
5:45.48. These are thread CPU times; FreeBSD's displayed ELAPSED was the
process elapsed time, so it is not used as a thread-age measurement.

At process elapsed 59:15, RSS was 2,747,884 KiB. Guest free memory was about
21.4 GiB; vmstat showed roughly 50% idle CPU and negligible disk throughput.
These samples do not establish an RSS leak or paging bottleneck. They do show
the requested compiler parallelism is not a hard lifetime bound on workers.

The native logfile did not yet contain a terminal timeout summary. Parallel
results are collected before the complete failures are reported, so absence
of the final summary is not evidence that every file remains within deadline.

## Exact source lifecycle

`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:639` sets the
default file timeout to 300. `driver/src/cli/native_build.rs:139` uses it.
`native_project/compiler.rs:1056` spawns an OS thread per file.
`wait_for_compiler_thread`, lines 1137-1139, returns an error on timeout and
drops the JoinHandle without joining or cancelling its worker. Dropping a
JoinHandle detaches that worker. The rayon task then returns, and the pool can
admit another file while the timed-out worker is still compiling. Its owned
AST/MIR/backend state remains live, and its eventual result is no longer
persisted by the caller. Sequential compilation has the same lifecycle risk.

## Focused reproduction

`evidence/timeout_lifecycle.rs` contains the exact wait function from the frozen
source plus a controlled worker. A one-second timeout returns while the
worker is demonstrably alive. The fixture then explicitly releases and drains
the worker, avoiding abandoned test work. Host rustc execution completed once:

`REPRODUCED: timeout returned after 1.000735439s; worker was still alive; fixture worker subsequently released and drained`

This proves the lifecycle defect; it does not benchmark full compiler speed.

## Repair constraints

- Never kill Rust/LLVM threads asynchronously or free their live state.
- An unconditional join after timeout would allow a nonterminating file to
  block forever and is not a valid bounded-time repair.
- Worker-owned admission permits can prevent oversubscription, but permit
  acquisition must itself avoid hanging indefinitely behind timed-out workers.
- A smaller fail-stop design can stop admitting additional files after the
  first timeout, preserve already completed cache objects, and report remaining
  files as unattempted. It needs explicit diagnostic/tests for sequential
  facades and parallel admission. A timeout means the build already failed;
  this design changes how much subsequent error collection is attempted.
- True hard per-file cancellation with continued bounded progress requires a
  process boundary or cooperative compiler cancellation. That is wider work.
- Keep the live build untouched; retain successful private cache entries.

Acceptance requires no replacement admission after timeout, actual successful
compilation behavior unchanged, bounded caller completion, explicit failure
receipts, and controlled tests releasing all fixture workers. Any speed/RSS
claim additionally needs paired immutable-compiler workload measurements.

## Implemented repair and verification limits

A phase-shared `NativeCompileAdmission` now rejects new work with
`NOT_ATTEMPTED: previous native worker timed out; refusing replacement admission`
after the first timed-out wait. The state is shared across serial facade
compilation and subsequent parallel fanout, and separately spans the sequential
fallback. It is set before the timed-out scheduler slot returns. An admission
that raced before the flag is set belongs to a different existing bounded
scheduler slot; it cannot increase the configured number of outstanding workers.
Ordinary compile errors continue collecting further diagnostics. Completed
objects follow the existing cache write path unchanged.

Already running workers are not forcibly cancelled. Their scheduler waits retain
the existing file deadline, then the failed build can terminate with at most its
original worker budget still outstanding. This is explicitly a fail-stop policy
for timeout safety; remaining module execution is not claimed complete. Hard
per-file cancellation while keeping all other modules running requires process
isolation or cooperative cancellation in a later change.

Two in-tree unit tests were extracted with the exact admission and wait functions
and compiled using host rustc: **2 passed**, finished in 1.00 s. They exercise a
real one-second worker timeout, suppression of replacement callbacks, normal
error continuation, and two already admitted workers whose waits return within
a bounded observation window. Test workers are explicitly released and drained.
The initial extraction needed the enclosing file's Duration import; this was a
fixture extraction issue, not a production source failure. No full compiler
crate build was attempted during the resource-constrained bootstrap.

No paired p50/p95 or peak-RSS improvement is claimed. This patch enforces
resource bounds after failure; the live compiler was not changed or restarted.
