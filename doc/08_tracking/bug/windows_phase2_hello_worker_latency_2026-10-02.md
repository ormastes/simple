# Windows Phase2 hello compile exceeds twelve minutes

Status: open; observed during bounded bootstrap qualification, not a diagnosed
compiler defect. No passing hello result was available at this observation.

## Terminal result

The third attempt terminated before its 1200-second timeout with
`rss-cap-exceeded`: aggregate process-tree peak 5,865,692 KiB against a
5,859,375 KiB cap. The outer resource receipt records child exit 88 and
the Job Object receipt records `quiescent=1`. Parent PID35956 and worker
PID31052 are gone. No hello executable or compile exit file was produced;
stderr still contained only the workarounds warning. D had approximately
102.885 GiB free, so disk pressure did not cause this failure.

The aggregate includes both parent and worker; child RSS alone is not
headroom evidence. Preserve the passing Phase2 build and the failed hello4
receipts. The three-cycle retry limit is reached, and Phase3/4 did not launch.

## Reproduction and identity

The retained `D:/dev/bootstrap-phase2-selective-windows/hello4/run-once.shs`
invokes `diagnostic5/output/stage2-diagnostic.exe native-build --backend llvm`
with the pinned runtime snapshot, documented SCV cold initialization and
`SIMPLE_COMPILER_TRACE=1`. The wrapper limits compilation to 1200 seconds,
with an additional 30-second termination grace, plus process-tree memory and
physical-D guards. Do not restart this attempt merely to obtain diagnostics.

Producer SHA256:
`81500d1a16010b2fcd911e4a04cc2ada8d9d44dcf5037f1cadb47a1906c92b7d`.
The producer build passed with 2 compiled and 1,115 cached modules, zero
failed modules, and a quiescent successful guard receipt.

## Observation

At 12.4 minutes elapsed, parent PID35956 had consumed 444.578125 CPU seconds
and used approximately 1,249 MiB RSS. Its child PID31052 had been alive for
4.8 minutes, consumed 280.859375 CPU seconds, and used approximately 130 MiB
RSS. The owner identified the child as the same candidate executing
`run src/app/cli/native_build_worker.spl`. The parent's waiting thread alone
does not indicate a deadlock: the child was actively consuming CPU.

`hello4/compile.stderr.log` contained only the existing workarounds coverage
warning, without stage-level progress. These observations cannot identify
HIR, MIR, code generation, or linking as the source of the latency. There is
no comparable baseline supporting a percentage regression claim.

## Authorized diagnostic continuation and source observations

The user subsequently authorized exactly one additional instrumented Windows
attempt. Hello5 reuses the same candidate and hello4 cache with unchanged
6,000,000,000-byte aggregate cap, 1200-second compile timeout and disk guard.
It adds worker-spawn, phase-profile and memory-snapshot diagnostics, plus a
bounded external process-tree sampler pinned to PID and creation time. This
exception does not reset the attempt count or authorize another retry.

Two source observations constrain interpretation of the measurements:

- `bootstrap_main.spl` handles the marked internal worker `run` route with
  a direct call to compiled `cli_native_build_with_environment_variant_policy_v1`.
  The child's `run` argument alone is not evidence of source interpretation.
- `app/compiler_entrypoint/inventory_events.spl` explicitly bypasses the
  valid-cursor warm path when `cold_init` is true and requests a complete
  source inventory replacement. The retained wrapper keeps
  `SIMPLE_SCV_INVENTORY_COLD_INIT=1`, so frontend-cache reuse does not imply
  warm inventory preparation. This is a possible contributor to parent
  pre-spawn latency, not a demonstrated explanation of worker RSS growth.

Do not modify the live diagnostic run. Preserve its inventory cursor/pointer
identity and terminal traces before considering a subsequent warm invocation.

## Remaining verification

Preserve the terminal compile/run exits and owned-process quiescence receipt.
A successful hello requires compiling and executing the resulting binary,
not merely a linked compiler, version output, or an active worker.
Use bounded startup/worker stage instrumentation to locate the elapsed time
before changing compiler semantics or cache identity. This is the third
bounded Windows hello attempt; a failure does not authorize another retry
under the repository's three-cycle rule. Keep the successful Phase2 image,
runtime snapshot and phase-specific caches intact.
