# Bootstrap distributed builder: local evidence

Date: 2026-09-30. Inspected source: `af2ccf6ea6f791a6c51ba6d3e646147ce96469a3`.
Implementation checkout: `D:/wk-bootstrap-manager-resume-20260930`.

The restart report and policy in `D:/wk-bootstrap-restart-handoff-20260930`
are the retained requirements. The current instruction resumes work and says
cached bootstrap scripts continue concurrently; they must not wait for the new
manager. Adopt the manager after both compiler and manager qualification.

## Existing owners

- `src/compiler/80.driver/driver_build/parallel.spl`: local process execution
  through `build_parallel` and `build_supervised`. The production codegen path
  still calls serial `build` in `driver_aot_native_output.spl`.
- `src/app/cli/native_build_main.spl`: real parse/HIR shard process dispatch.
  `native_build_worker.spl` is an internal whole-build interpreted entrypoint;
  it is not a native per-module worker.
- `src/compiler/80.driver/cache/package_scc_scheduler.spl`: pure SCC scheduling.
  The semantic cache daemon is a storage service, not a compilation worker pool.
- `src/app/io/process_ops.spl` and `file_ops.spl`: application process and file
  facades; the new app must not declare private environment/process externs.
- `src/lib/common/crypto/sha256.spl`: existing canonical text identity hash.

No standalone distributed compilation manager was identified by the scoped
source and plan search. The new entrypoint is new implementation, not activation
of an already qualified feature. Seven-plan item 6 does not identify a complete
distributed-manager implementation or authoritative final umbrella plan.

## Process boundary

`doc/03_plan/compiler/native_codegen/step5_real_parallelism_plan_2026-09-04.md`
describes frozen MIR capsules holding live heap objects with no complete decoder.
Its LLVM IR-file boundary permits real workers without moving those pointers.
Parent compilation emits immutable IR; workers produce objects; compiler parent
checks capsule identity and publishes cache receipts. That covers codegen only:
frontend/SCC isolation requires its own admitted module request boundary.

The old `build_supervised` dispatches topological order before dependencies
complete, frees timed-out slots after kill without a confirmed reap, accepts an
empty declared artifact, and has no durable attempt or remote transport protocol.
It cannot be used unchanged as the requested manager.

## Preserved boundaries

Do not reopen the revoked Linux image or the rejected PR #2132 investigation.
Do not transplant the broad main tree to release. Do not rewrite bootstrap
receipts or mutate a live compiler's input tree. Preserve old cache directories
and record actual hits separately from cache-file inventory.

This document records inspection, not worker execution or bootstrap completion.
