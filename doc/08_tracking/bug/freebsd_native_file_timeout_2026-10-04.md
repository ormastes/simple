# FreeBSD Stage 2 native file timeouts (2026-10-04)

## Observed result

The frozen FreeBSD ARM64 producer was release commit `de37d9879ae74e1521df0f75e6aa0c48d2dea955`, canonical source snapshot `2078163f38572e189de6c70c09519ce0381062e711044043352bfe3a5736b2b3`. The guest used KVM, 20 vCPUs, 36 GiB RAM, and 10 admitted native workers. The canonical Stage 2 command did not set `SIMPLE_NATIVE_FILE_TIMEOUT`, so each file had the default 300-second deadline.

| Backend | Compiled | Reused | Failed | Peak RSS | Phase 1 runtime SHA-256 |
| --- | ---: | ---: | ---: | ---: | --- |
| LLVM | 1,147 | 0 | 32 | 3,130,696 KiB | `0dc164a611cff051dbaac3156e88c933516b2cd80541e903187404b3a1f4a37f` |
| Cranelift | 1,135 | 0 | 44 | 2,264,692 KiB | `d0fa5645ce9819476eee8f63bde9ffe2104a13cce1abc36286aa925328d9419f` |

Each failed file was reported as `timeout (300s)`; no separate native compiler error or RSS-cap failure was reported. Fourteen paths failed in both backends, including parser, linker, CLI, and `src/lib/nogc_sync_mut/env/__init__.spl` (4,258 bytes). The remaining 18 LLVM and 30 Cranelift paths differ. Both managers aborted Stage 2; neither emitted an admitted Stage 2 compiler. These counts do not prove that the modules are defective or that longer waits will succeed.

Preserved receipts and backend-private object caches are under `build/freebsd/phase2-run-20261003/terminal-de37-{llvm,cranelift}/` in `/home/yoon/dev/simple-freebsd-phase2-qemu-20261003`. The LLVM cache contains 1,147 objects; the Cranelift cache contains 1,135. Before reuse, bind each run to its exact source snapshot, backend, Phase 1 runtime, Stage 2 cache scope and args hash. Changing timeout changes the command/args hash; cache reuse must be observed, never assumed.

## Timeout behavior and landed fix

In the de37 Rust seed, `wait_for_compiler_thread` returns `timeout (300s)` when its channel wait expires, but dropping its `JoinHandle` leaves the compile thread running. A later scheduler slot could admit a replacement while the old worker still consumed CPU and memory. The tracked reproduction in `doc/08_tracking/bug/freebsd_native_timeout_worker_admission_2026-10-04.md` observed workers with more than 300 seconds of CPU time. Release PR #2429 (`b8be1a850af`) subsequently stopped replacement admission after a timeout. That safety fix does not shorten the first slow compilation or establish that a full FreeBSD build passes.

The old wait function also classified every `recv_timeout` error as a timeout, including channel disconnection if a worker exited before sending. The accompanying source fix distinguishes disconnection from an expired deadline: a finished worker returns its join result, while a disconnected worker still running retains the positive deadline. Focused tests cover panic before signal, disconnect while still running, positive timeout, zero timeout, and timeout admission. This diagnostic defect is not proven to have caused the de37 failures.

## Run policy and focused check

The canonical script accepts numeric `SIMPLE_NATIVE_FILE_TIMEOUT`; unset means 300 seconds. Setting `SIMPLE_NATIVE_FILE_TIMEOUT=0` adds `--timeout 0`, which the Rust seed implements as `JoinHandle::join()` without a per-file deadline. This disables only the native per-file timeout. The bootstrap session, manager, RSS, disk and external operational guards remain required; a stuck compiler can then wait indefinitely until an outer guard or operator ends the run. A positive bounded value such as `1800` is also supported if retaining a file deadline is preferred. Do not edit transcripts or admission receipts to change this setting.

The current user request prioritizes a new FreeBSD bootstrap on the latest release. Freeze one reviewed release source identity before compiling, use backend-specific output/cache and runtime receipts, and invoke the canonical manager with an explicit environment prefix such as `SIMPLE_NATIVE_FILE_TIMEOUT=0`. Run LLVM and Cranelift managers sequentially because they share bootstrap authority. Retain the 20-vCPU request, choose memory/native-worker count from measured host headroom at launch, and keep the outer resource guards. Do not infer cache validity from the old de37 caches after a source or seed change.

If the new full bootstrap stalls, a focused diagnostic target is `src/lib/nogc_sync_mut/env/__init__.spl`, a 4,258-byte file that timed out in both old backends. Record wall/CPU time, live worker count, compiler phase, and cache scope; a serial compile versus bounded fanout can separate intrinsic work from contention. The old logs alone do not identify which mechanism dominates. No retry, Hello World run, or subsystem product test has passed on the de37 FreeBSD source.
