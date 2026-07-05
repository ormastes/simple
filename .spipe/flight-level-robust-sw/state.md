# Feature: flight-level-robust-sw

## Raw Request
use spark intensively, $sp_dev  make flight level sw, in simple compiler, simple os(baremetal), nvme fw. and update skill about robust sw in spipe. simple and simple os's thread, process and coroutine harden and harden in baremetal and formal verification. However, do what is difficult to opus/gpt-5.5 medium or higher should do or short and important tasks after deep plan.

## Task Type
feature

## Refined Goal
Define and enforce a SPipe robust-software lane for flight-level Simple compiler, SimpleOS baremetal, NVMe firmware, and thread/process/coroutine hardening evidence, with formal-verification gates that cannot be satisfied by generated artifacts or single interleaving tests alone.

## Acceptance Criteria
- AC-1: The SPipe lane state lists the robust-software scope across compiler, SimpleOS baremetal, NVMe firmware, and concurrency/runtime surfaces.
- AC-2: SPipe skill and guide guidance require mission-critical SimpleOS release evidence through `sh scripts/check/check-simpleos-mission-critical-release.shs` with `release_blockers=none`, not only the hardening matrix.
- AC-3: Formal evidence guidance distinguishes generated Lean/BYL/RTL artifacts from durable manual proof entry points and requires a post-regeneration gate.
- AC-4: Thread/process/coroutine starvation, fairness, race-condition, scheduler, channel, lock, or resource-lifecycle claims require a concurrency/resource model gate or an explicit blocker.
- AC-5: NVMe firmware and baremetal work cites the current in-repo example/research lanes and does not claim real hardware, QEMU, or formal proof coverage unless the matching gate exists and passes.
- AC-6: Broad findings from Spark/other lower-model sidecars are treated as input only; a normal/high-capability reviewer owns final acceptance.

## Phase
dev-in-progress

## Log
- dev: Created SPipe state with 6 acceptance criteria and Spark sidecar plan for the flight-level robust software lane.
- guide: Added `doc/07_guide/app/spipe/mission_critical_robust_sw.md` so SPipe robust-software lanes have an operator-facing gate contract.
- evidence: Mission-critical formal prerequisites checked with `sh scripts/check/check-simpleos-mission-critical-prereqs.shs`; result blocked with missing `sby,yosys,smt-solver`.
- blocker: No `sby`, `yosys`, `boolector`, `z3`, `nix`, `conda`, `micromamba`, or local OSS CAD Suite path was found on this host; `sudo -n true` requires a password.
- setup: `scripts/setup/setup-simpleos-formal-env.shs --print-install` now documents the no-sudo OSS CAD Suite option: source `/path/to/oss-cad-suite/environment`, then rerun the prereq and mission-critical release gates.
- nvme: `test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl` now boots/checks `build/nvme_fw_rv32.elf` and requires `ALL RV32 NVME FW CHECKS PASS` when firmware media exists, instead of accepting the stock `build/os/simpleos_riscv32.elf` as firmware runtime evidence.
- evidence: Focused NVMe RV32 spec passed after the path correction by taking the fail-closed missing-media branch for absent `build/nvme_fw_rv32.elf`.
- blocker: `sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` was attempted once and interrupted after about five minutes with no output; the native-build worker had to be terminated, so runtime firmware PASS evidence remains unproven.
- nvme: `examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` now passes `--timeout`, wraps native-build with a shorter outer timeout, and writes `build/test-artifacts/nvme_fw_rv32_build.{out,err}` so the firmware build fails diagnosably instead of hiding behind the native-build worker's long default timeout.
- evidence: `NVME_RV32_BUILD_TIMEOUT_SECS=1 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` exited `124` with `NVME_RV32_BUILD_FAILED code=124 timeout=1s out=build/test-artifacts/nvme_fw_rv32_build.out err=build/test-artifacts/nvme_fw_rv32_build.err`.
- process: `test/01_unit/runtime/process_is_running_spec.spl` now kills and reaps the long-lived async child after the liveness poll, and covers repeated terminal cleanup as a safe no-op after a child has already exited.
- evidence: `bin/simple test test/01_unit/runtime/process_is_running_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 8 examples, including `treats repeated terminal cleanup as a safe no-op`.
- note: A draft repeat wait with `process_wait(pid, 0)` timed out the test daemon after the child had already been reaped; the accepted gate uses bounded `process_wait(pid, 100)` for terminal-idempotence evidence.
- coroutine: `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl` and `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` now cover post-completion `join()` idempotence and safe no-op carrier drain.
- evidence: `bin/simple test test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 3 examples.
- evidence: `bin/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter --clean --timeout 90 --sequential` passed 4 examples.
- thread: `std.concurrent.thread` now passes callable values to `rt_thread_spawn_isolated*` instead of forcing a `closure as i64` cast, so the interpreter owner hook can execute public thread closures without a function-to-integer cast failure.
- thread: the interpreter `rt_thread_join` terminal no-op now returns `0`, matching the native runtime's invalid-handle result for repeated joins on the public `i64` API.
- evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 1 example after rebuilding `simple-driver`.
- evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/nogc_sync_mut/concurrent_thread_pointer_spawn_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 1 example after rebuilding `simple-driver`.
- concurrency: `simple check` now rejects `thread_spawn_with_args` from `std.concurrent.cooperative_green` through the active lightweight check worker and the Rust fallback check helper.
- evidence: `SIMPLE_BIN=src/compiler_rust/target/debug/simple sh test/05_perf/profile_scripts/concurrency_api_contract_test.shs` passed with `concurrency_api_contract=true`, `checked_in_misuse_fixtures=30`, `total_misuse_fixtures=41`, and `positive_fixtures=6`.
