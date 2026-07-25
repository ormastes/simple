# Feature: flight-level-robust-sw

## Raw Request
use spark intensively, $sp_dev  make flight level sw, in simple compiler, simple os(baremetal), nvme fw. and update skill about robust sw in spipe. simple and simple os's thread, process and coroutine harden and harden in baremetal and formal verification. However, do what is difficult to opus/gpt-5.5 medium or higher should do or short and important tasks after deep plan.

## Task Type
feature

## Refined Goal
Define and enforce a SPipe robust-software lane for flight-level Simple compiler, SimpleOS baremetal, NVMe firmware, and thread/process/coroutine hardening evidence, with formal-verification gates that cannot be satisfied by generated artifacts or single interleaving tests alone.

## Acceptance Criteria
- AC-1: The SPipe lane state lists the robust-software scope across Simple
  compiler, SimpleOS baremetal, NVMe firmware, and thread/process/coroutine
  runtime surfaces, and every claim is tagged as `host-simulation`,
  `QEMU/emulator`, `real-hardware`, `generated-artifact`, `manual-proof`, or
  `release-gate`.
- AC-2: SPipe skill, `$sp_dev`, SPipe dev-agent, and operator-guide guidance
  require mission-critical SimpleOS release evidence through
  `sh scripts/check/check-simpleos-mission-critical-release.shs` with
  `matrix_status=pass`, `release_status=pass`, `release_blockers=none`,
  `prereq_status=ready`, and no stale static reports; the hardening matrix alone
  is subordinate evidence, not release evidence.
- AC-3: Simple compiler flight-level claims treat the compiler as a safety
  development tool. Trusted-core readiness requires measured self-hosted
  structural coverage or a durable formal gate; Rust-seed-only probes,
  statement coverage, percentage-only MC/DC, or interpreter-only passes may
  satisfy at most `smoke`.
- AC-4: Formal evidence guidance distinguishes generated Lean/BYL/RTL artifacts
  from durable manual theorem/constraint entry points and requires a
  post-regeneration gate such as `lake build`, `simple gen-lean verify`,
  `simple verify check`, or the matching SimpleOS/RISC-V wrapper self-test.
- AC-5: Thread/process/coroutine starvation, fairness, race-condition,
  scheduler, channel, lock, or resource-lifecycle claims require a
  concurrency/resource model gate or an explicit blocker; single interleaving
  specs remain `smoke`.
- AC-6: NVMe firmware and baremetal work separates host emulator, QEMU wrapper,
  and physical-board evidence. Completion claims require RV32/RV64 wrapper
  coverage (`check-nvme-baremetal-wrapper-coverage.shs --strict`) and
  fail-closed self-tests; live rv32 firmware PASS remains blocked until the boot
  wrapper prints `ALL RV32 NVME FW CHECKS PASS`.
- AC-7: Broad findings from Spark or other lower-model sidecars are treated as
  audit input only. A normal/high-capability reviewer owns final acceptance for
  broad exclusions, generated-manual quality, and any `pass` status upgrade.

## Cooperative Review
- Sidecars: Codex Spark for broad local scans of compiler, SimpleOS, NVMe firmware, and concurrency evidence; mini sidecars only when Spark quota blocks progress.
- Merge owner: Codex in this lane.
- Final reviewer: normal/highest-capability Codex review before accepting broad exclusions, generated-manual quality, or done marks.
- Shared checker names: `check-simpleos-mission-critical-release.shs`, `check-simpleos-mission-critical-prereqs.shs`, `concurrency_api_contract_test.shs`, `nvme_rv32_baremetal_boot_spec.spl`.
- Fail-fast policy: missing proof tools, missing firmware media, or sidecar-only findings remain explicit blockers.

## Current Evidence Classification

- Simple compiler trusted-core flight-level evidence: `blocked`. The staged
  MC/DC plan exists, but self-hosted MC/DC instrumentation and independence-pair
  reporting are not proven complete.
- SimpleOS mission-critical release evidence: `pass` on this host with the
  documented formal toolchain or OSS CAD Suite environment active; fresh hosts
  still need `sby`, `yosys`, and an SMT solver before the release gate can pass.
- NVMe firmware evidence: wrapper coverage is `pass` for the recorded RV32/RV64
  wrapper/spec checks. Live RV32 minimal firmware is now `pass` through the
  bounded pure-Simple RV32 QEMU checker for all 21 registered minimal slices
  (`check-nvme-rv32-minimal-live.shs`, serial marker `ALL RV32 NVME FW CHECKS
  PASS`). Full self-hosted bootstrap/deploy remains `blocked`: the Stage 4
  native build timed out after 1800s without producing a refreshed
  `bin/simple`. The executable SSpec coverage is
  `test/03_system/app/nvme_firmware/nvme_rv32_minimal_live_spec.spl`, with the
  generated manual in
  `doc/06_spec/test/03_system/app/nvme_firmware/nvme_rv32_minimal_live_spec.md`.
- Thread/process/coroutine lifecycle evidence: representative hardening checks
  are `pass` for the named lifecycle/regression specs in the log. Broader
  fairness, starvation, race, and scheduler proof claims remain `blocked`
  without a model/formal gate.
- Spark usage: `blocked` by quota in the current environment; mini/other
  sidecars can collect input, but cannot replace final normal/high-capability
  review.

## Phase
dev-in-progress

## Log
- compiler: MIR-to-LLVM now spills `Copy`/`Move` destinations written outside
  the first MIR block into entry allocas. This fixes the preserved Stage 2
  invalid-SSA shape where `%l0` was defined in one branch and later read after
  a join, producing `Instruction does not dominate all uses!`.
- evidence: source assertion reported `llvm_branch_copy_spill_source=pass`;
  transforming the preserved failing `/tmp/simple_llvm_696017.ll` with the same
  alloca/store/load shape made `llc` pass
  (`llvm_branch_copy_spill_llc_probe=pass`); `git diff --check` passed for the
  edited MIR-to-LLVM helper.
- blocker: `bin/simple check src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`
  was attempted with the default run and with `timeout -k 10s 120s`; both were
  terminated during dependency loading after frontend warning output and before
  a file result. Full bootstrap/deploy and RV32 production firmware proof remain
  unrun after this fix.
- compiler: `compile_ir_to_object` now checks the `llc` exit code before
  accepting an existing bootstrap object path, deletes stale objects on failure,
  and rejects empty or non-object-magic outputs. This closes the false-progress
  part of the RV32 production blocker without claiming the broader invalid-SSA
  bootstrap bug is fixed.
- nvme-fw: fixed the LLVM unary-op lowering path used by the RV32 firmware
  checker so normalized local ids and non-`nil` destination types are used for
  `Neg`/`Not`/`BitNot`/`Transpose`. Evidence now extends to the 21-section
  minimal live checker, which produced RV32 object/ELF output and QEMU serial
  output `ALL RV32 NVME FW CHECKS PASS`.
- nvme-fw: the minimal live checker now has bounded emitters for all registered
  prefix slices through namespace guard, preventing the section-15 one-file
  parse timeout. Evidence: direct `NVME_RV32_MINIMAL_SECTIONS=21 ...` checker
  passed, and `bin/simple test
  test/03_system/app/nvme_firmware/nvme_rv32_minimal_live_spec.spl
  --mode=interpreter --clean --timeout 180 --sequential` passed 1/1.
- evidence: `bin/simple check src/compiler/70.backend/backend/llvm_backend_tools.spl`
  passed; source assertion reported `llvm_object_fail_closed_source=pass`;
  `git diff --check` passed for the edited compiler helper.
- blocker: `bin/simple test test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl`
  and a smaller object-magic spec both failed before reaching this change
  because the current worktree parser reports
  `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl: Unexpected token:
  expected Indent, found Dedent`. That is separate from this helper change.
- gate: Added `scripts/check/check-spipe-flight-level-robust-sw-state.shs`
  to fail closed when the lane state, SPipe skill, `$sp_dev`, SPipe dev agent,
  or mission-critical guide lose evidence-tier, Simple compiler
  tool-qualification, SimpleOS release, NVMe strict-wrapper, Spark-sidecar, or
  concurrency model-gate wording.
- evidence: `sh scripts/check/check-spipe-flight-level-robust-sw-state.shs --self-test`
  passed; `sh scripts/check/check-spipe-flight-level-robust-sw-state.shs`
  passed with `spipe_flight_level_state_status=pass` and
  `spipe_flight_level_state_missing=none`.
- blocker: The new state gate verifies evidence-contract wiring only. It does
  not upgrade compiler MC/DC, live RV32 NVMe firmware, physical-board, or
  fairness/starvation/race claims beyond the blockers listed in Current
  Evidence Classification.
- dev-refresh: Tightened ACs to require explicit evidence tiers, compiler
  tool-qualification handling, SimpleOS release-gate fields, NVMe wrapper/live
  boot separation, concurrency model gates, and final high-capability review.
- sidecar: Codex Spark broad audits were quota-blocked until 09:37; this lane used narrow mini sidecars and still requires normal/high-capability review before acceptance.
- compiler: Resolved four literal parser blockers that prevented the bounded
  Stage 2 bootstrap probe from reaching the MIR/LLVM dominance fix:
  `src/compiler/20.hir/hir_lowering/expressions.spl`,
  `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`,
  `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, and
  `src/compiler/35.semantics/resolve.spl`.
- evidence: conflict-marker scans for those files are clean; targeted
  `git diff --check` is clean; `bin/simple check
  src/compiler/50.mir/_MirLowering/bootstrap_globals.spl` passed; `bin/simple
  check src/compiler/35.semantics/resolve.spl` passed.
- blocker: `bin/simple check
  src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` was bounded
  to 120s and terminated during dependency loading warnings without a file-level
  result. The last bounded Stage 2 probe before the `resolve.spl` cleanup was
  `build/mini_builds/stage2_probe_after_switch_calls_resolve/stage2-native-build.log`
  and failed at the now-fixed `resolve.spl` parser error. Per the runaway guard,
  Stage 2 was not reprobed again in this session.
- compiler: Stage 2 now builds and runs after the parser cleanup,
  branch-local copy spill, `get_cli_args` pointer-signature fix, and
  `bootstrap_main.spl` argv dispatch cleanup.
- evidence: `build/mini_builds/stage2_probe_after_bootstrap_argv_fix/stage2-native-build.log`
  reports `stage2_probe_after_bootstrap_argv_fix_rc=0`,
  `[mir-lower-free] done instr-total=200 term-total=54`, and
  `[llvm-tools] llc-object`; the produced Stage 2 binary reports
  `simple-bootstrap 1.0.0-beta` for `--version` and prints help with rc 0.
- blocker: full bootstrap/deploy was attempted once with
  `timeout -k 20s 1200s sh scripts/bootstrap/bootstrap-from-scratch.sh
  --pure-simple --no-mcp --deploy` and timed out with rc 124 after Stage 3
  failed and the script fell back to slow seed Stage 4. Stage 3 failed because
  Stage 2 `native-build` still routes to `run_native_build_bootstrap(args)`,
  which returns literal `1`; `stage3-native-build.log` is empty.
- verification: `sh scripts/audit/direct-env-runtime-guard.shs --working`
  passed. `--staged` failed on unrelated staged
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl`
  raw `rt_env_get`; this lane did not modify that file.
- rejected_shortcut: Directly changing `bootstrap_main.spl`
  `run_native_build_bootstrap(args)` to call raw `rt_native_build(args)` was
  tested and reverted. Stage 2 then failed link with `undefined symbol:
  rt_native_build` because the current bootstrap native-build runtime does not
  link `libsimple_native_all.a`; the owner fix must be in native-build runtime
  selection or bootstrap script flow, not an unbacked source extern.
- evidence: after reverting that shortcut,
  `build/mini_builds/stage2_probe_after_rt_native_build_revert/stage2-native-build.log`
  reports `stage2_probe_after_rt_native_build_revert_rc=0`,
  `[mir-lower-free] done instr-total=200 term-total=54`, and
  `[llvm-tools] llc-object`; the produced Stage 2 binary still prints
  `simple-bootstrap 1.0.0-beta` for `--version` and returns rc 1 for the known
  `native-build` stub.
- rejected_shortcut: Replacing the seed fallback's `run
  src/app/cli/native_build_main.spl -- ...` with direct
  `src/compiler_rust/target/bootstrap/simple native-build ...` for the full
  Stage 4 CLI was probed once at
  `build/mini_builds/stage4_direct_seed_native_build_probe/stage4-direct-seed-native-build.log`.
  It timed out at 20 minutes with rc 124, produced no output binary, and logged
  only dependency warnings before timeout. Do not patch the bootstrap script to
  this direct seed fallback; it does not fix the deploy blocker.
- bootstrap: `scripts/bootstrap/bootstrap-from-scratch.sh` now fails fast when
  Stage 3 exits nonzero before writing any native-build diagnostics, which is
  the current bootstrap-stub failure mode. It refuses the slow seed Stage 4
  fallback until `run_native_build_bootstrap` or the bootstrap native-build
  owner path is fixed.
- evidence: `timeout -k 20s 900s sh
  scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --no-mcp --deploy`
  now exits `bootstrap_failfast_stage3_stub_rc=1` after Stage 3 with the explicit
  diagnostic `refusing slow seed stage4 fallback; fix run_native_build_bootstrap
  or the bootstrap native-build owner path first`.
- verification: Replaced the staged raw `rt_env_get` in
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl`
  with the existing `std.gc_async_mut.io.mod_stub.env_get` facade. `bin/simple
  check` for that file passed, and both
  `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged`
  now report `STATUS: PASS`.
- dev: Created SPipe state with 6 acceptance criteria and Spark sidecar plan for the flight-level robust software lane.
- guide: Added `doc/07_guide/app/spipe/mission_critical_robust_sw.md` so SPipe robust-software lanes have an operator-facing gate contract.
- evidence: Mission-critical formal prerequisites checked with `sh scripts/check/check-simpleos-mission-critical-prereqs.shs`; result blocked with missing `sby,yosys,smt-solver`.
- blocker: No `sby`, `yosys`, `boolector`, `z3`, `nix`, `conda`, `micromamba`, or local OSS CAD Suite path was found on this host; `sudo -n true` requires a password.
- setup: `scripts/setup/setup-simpleos-formal-env.shs --print-install` now documents the no-sudo OSS CAD Suite option: source `/path/to/oss-cad-suite/environment`, then rerun the prereq and mission-critical release gates.
- nvme: `test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl` now boots/checks `build/nvme_fw_rv32.elf` and requires `ALL RV32 NVME FW CHECKS PASS` when firmware media exists, instead of accepting the stock `build/os/simpleos_riscv32.elf` as firmware runtime evidence.
- correction: The NVMe RV32 spec no longer treats missing QEMU or missing `build/nvme_fw_rv32.elf` as a diagnostic pass; those branches now fail with explicit host/media reasons.
- blocker: `sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` was attempted once and interrupted after about five minutes with no output; the native-build worker had to be terminated, so runtime firmware PASS evidence remains unproven.
- nvme: `examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` now passes `--timeout`, wraps native-build with a shorter outer timeout, and writes `build/test-artifacts/nvme_fw_rv32_build.{out,err}` so the firmware build fails diagnosably instead of hiding behind the native-build worker's long default timeout.
- evidence: `NVME_RV32_BUILD_TIMEOUT_SECS=1 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` exited `124` with `NVME_RV32_BUILD_FAILED code=124 timeout=1s out=build/test-artifacts/nvme_fw_rv32_build.out err=build/test-artifacts/nvme_fw_rv32_build.err`.
- blocker: `NVME_RV32_BUILD_TIMEOUT_SECS=60 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` still exited `124` with empty native-build output, so `build/nvme_fw_rv32.elf` remains absent and runtime firmware PASS evidence remains blocked.
- nvme: The rv32 firmware build wrapper now writes preflight source/entry/target markers before invoking native-build, so future timeout evidence is not an empty-log failure.
- blocker: Current NVMe firmware wrapper timeout is tracked in `doc/08_tracking/bug/nvme_rv32_firmware_build_timeout_2026-07-05.md`; it is distinct from the resolved rv32 silent-255 native-build bug.
- nvme: `src/compiler_rust/target/bootstrap/simple` with the canonical full source set (`build/os/generated`, `src`, `examples`) built a probe ELF in about 5.2s; `bin/simple` with the same source set still timed out within 60s. The wrapper defaults to `bin/simple` and exposes `NVME_RV32_SIMPLE_BIN` for explicit diagnostic compiler comparison.
- process: `test/01_unit/runtime/process_is_running_spec.spl` now kills and reaps the long-lived async child after the liveness poll, and covers repeated terminal cleanup as a safe no-op after a child has already exited.
- evidence: `bin/simple test test/01_unit/runtime/process_is_running_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 8 examples, including `treats repeated terminal cleanup as a safe no-op`.
- note: A draft repeat wait with `process_wait(pid, 0)` timed out the test daemon after the child had already been reaped; the accepted gate uses bounded `process_wait(pid, 100)` for terminal-idempotence evidence.
- coroutine: `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl` and `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` now cover post-completion `join()` idempotence and safe no-op carrier drain.
- evidence: `bin/simple test test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 3 examples.
- evidence: `bin/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter --clean --timeout 90 --sequential` passed 4 examples.
- async: Current evidence covers cooperative-green lifecycle and async-spawned process cleanup only; it is not a full-library verification claim for every async module.
- evidence: `bin/simple test test/01_unit/runtime/process_is_running_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 8 examples on the current worktree.
- async: Added `scripts/check/check-async-library-hardening-evidence.shs` as representative regression evidence for the current async surfaces it checks: async basics/primitives, nogc async host/thread-pool/file-handle cleanup/green-channel/cooperative-green, thread lifecycle cleanup, integration thread-pool async, async promise system, SimpleOS cooperative-green, and async-spawned process cleanup.
- evidence: `sh scripts/check/check-async-library-hardening-evidence.shs` passed with `async_library_hardening_total=15`, `async_library_hardening_passed=15`, `async_library_hardening_failed=0`, and `async_library_hardening_missing=0`.
- docs: `bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/async_host_spec.spl test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl test/02_integration/lib/thread_pool_async_spec.spl --output doc/06_spec --no-index` generated 3 complete manuals with 0 stubs.
- thread: `std.concurrent.thread` now passes callable values to `rt_thread_spawn_isolated*` instead of forcing a `closure as i64` cast, so the interpreter owner hook can execute public thread closures without a function-to-integer cast failure.
- thread: the interpreter `rt_thread_join` terminal no-op now returns `0`, matching the native runtime's invalid-handle result for repeated joins on the public `i64` API.
- evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 1 example after rebuilding `simple-driver`.
- evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/nogc_sync_mut/concurrent_thread_pointer_spawn_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 1 example after rebuilding `simple-driver`.
- concurrency: `simple check` now rejects `thread_spawn_with_args` from `std.concurrent.cooperative_green` through the active lightweight check worker and the Rust fallback check helper.
- evidence: `SIMPLE_BIN=src/compiler_rust/target/debug/simple sh test/05_perf/profile_scripts/concurrency_api_contract_test.shs` passed with `concurrency_api_contract=true`, `checked_in_misuse_fixtures=30`, `total_misuse_fixtures=41`, and `positive_fixtures=6`.
- evidence: `SIMPLE_BIN=bin/simple sh test/05_perf/profile_scripts/concurrency_api_contract_test.shs` passed on the self-hosted runtime with `concurrency_api_contract=true`, `checked_in_misuse_fixtures=30`, `total_misuse_fixtures=41`, and `positive_fixtures=6`.
- sidecar: Spark remains quota-blocked; narrow mini sidecars found formal gate wording, NVMe spec/manual title, and free-before-join thread lifecycle gaps, which were integrated.
- guide: `doc/07_guide/app/spipe/mission_critical_robust_sw.md` now requires `matrix_status=pass`, `release_status=pass`, `release_blockers=none`, and `prereq_status=ready`; the hardening matrix is subordinate evidence consumed by the release gate.
- setup: prereq output and `scripts/setup/setup-simpleos-formal-env.shs --print-install` now name both install paths: distro SymbiYosys stack or locally sourced OSS CAD Suite.
- nvme: rv32 spec/manual wording now identifies `build/nvme_fw_rv32.elf` as the NVMe firmware rv32 ELF and keeps P9 hook evidence separate from QEMU boot evidence.
- blocker: `bin/simple test test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl --mode=interpreter --clean --timeout 90 --sequential` now fails as intended when `build/nvme_fw_rv32.elf` is absent; firmware runtime PASS evidence requires building that ELF first.
- thread: lifecycle coverage now includes join-then-repeat-cleanup and free-before-join terminal cleanup for public `ThreadHandle`.
- evidence: `bin/simple test test/01_unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 2 examples after asserting the repeated-join `nil` sentinel on the self-hosted runtime.
- blocker: `sh scripts/check/check-simpleos-mission-critical-prereqs.shs` still reports `sby,yosys,smt-solver` missing, so mission-critical release remains blocked until the formal toolchain is installed or OSS CAD Suite is sourced.
- setup: OSS CAD Suite located at `/tmp/simple-oss-cad-suite/oss-cad-suite/environment`; sourcing it (`. .../environment`) puts `sby`/`yosys`/SMT on PATH, and `check-simpleos-mission-critical-prereqs.shs` then reports `prereqs_status=ready prereqs_missing=none STATUS: PASS`.
- fix: `check-simpleos-formal-coverage.shs` `require_file_text` demands the literal `sudo apt-get install yosys symbiyosys boolector z3` in `scripts/setup/setup-simpleos-formal-env.shs`; a prior OSS-CAD edit had split `z3` into a comment, failing the coverage audit. Restored `z3` onto the apt line (installs both accepted SMT solvers) so `formal_coverage_status=pass`.
- evidence: with OSS CAD Suite sourced, `sh scripts/check/check-simpleos-mission-critical-release.shs` now reports `STATUS: PASS simpleos-mission-critical-release matrix_status=pass release_status=pass release_blockers=none prereq_status=ready prereq_missing=none` (exit 0). AC-2 met; the formal toolchain must be sourced/installed per `setup-simpleos-formal-env.shs` for the gate to pass on a fresh host.
- nvme: The rv32 firmware wrapper now generates `build/os/generated/os/kernel/arch/riscv32/nvme_fw_boot_root.spl` and a sibling `boot` symlink so `--entry-closure` roots both `src/os/kernel/arch/riscv32/boot.spl` and `fw_rv32/entry.spl` while the linker still enters boot `_start`.
- evidence: `NVME_RV32_SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple NVME_RV32_BUILD_TIMEOUT_SECS=60 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` now builds `build/nvme_fw_rv32.elf`; `llvm-nm` shows strong `rt_rv32_boot_optional_nvme_fw_selftest` and `entry__nvme_fw_rv32_selftest`.
- blocker: QEMU now reaches the firmware hook (`RV32 NVME FW BEGIN`) and completes markers through admin (`R E J M B S P H Q I F A`), then stops before reactor marker `C`; `ALL RV32 NVME FW CHECKS PASS` remains blocked by `rv32_reactor_selftest()` on rv32 baremetal.
- runtime: `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` `rt_as_heap` now bounds-checks the candidate header against the RAM window `[0x80000000,0x88000000)` BEFORE loading `header->object_type`, fixing a baremetal silent-hang (misclassified `i64` operands routed via `rt_native_eq`→`rt_as_string`→`rt_as_heap` dereferenced unmapped memory → trap to `mtvec=0`). Confirmed by GDB backtrace `PC=0 ← rt_as_string+30 ← rt_native_eq`; `HEAP OK` and `SVC OK` now print/pass where boot previously hung. Root-cause detail appended to the nvme rv32 firmware build-timeout bug doc.
- skill: `.claude/skills/lib/spipe_phases.md` Phase 7 now carries a "Robust-SW / mission-critical lane" note linking `doc/07_guide/app/spipe/mission_critical_robust_sw.md` and the `check-simpleos-mission-critical-release.shs` acceptance line (`release_blockers=none`), reachable via the spipe.md phase-map link (AC-1/AC-6).
- current-status: Not only bootstrap remains. Bootstrap/full deploy is still
  postponed, but the non-bootstrap RV32 minimal live lane still has one
  compiler/codegen blocker after the HIR fixes below.
- compiler: HIR statement lowering now compares local `StmtKind` discriminant
  integers for `Val`, `Var`, `Assign`, and `Return` instead of constructing
  dummy value-carrying enum variants for comparison. This avoids a stage4
  payload-inspection stack overflow on `val r = f(d1)` call initializers.
- compiler: HIR parameter lowering now treats `Param.type_` as the non-optional
  AST field it is and lowers it directly, avoiding the stale optional access
  form.
- evidence: `git diff --check -- src/compiler/20.hir/hir_lowering/statements.spl
  src/compiler/20.hir/hir_lowering/expressions.spl
  src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl` passed.
  `bin/simple test test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl
  --mode=interpreter --clean --timeout 60 --sequential` passed 1 example.
- evidence: `NVME_RV32_MINIMAL_SECTIONS=0 NVME_RV32_BUILD_TIMEOUT_SECS=90 sh
  scripts/check/check-nvme-rv32-minimal-live.shs` previously passed the
  root-only diagnostic build. After removing the temporary Binary expression
  predispatch, `NVME_RV32_MINIMAL_SECTIONS=1 ...` advanced past `rv32_xor8`
  and now fails later while lowering `_selftest`.
- blocker: `NVME_RV32_MINIMAL_SECTIONS=1 NVME_RV32_BUILD_TIMEOUT_SECS=90
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  fails with a stack overflow at
  `phase3:hir:function:start ... nvme_fw_minimal_root.spl._selftest`.
  A direct `rt_enum_payload` shortcut for Expr-statement payload extraction was
  rejected because pure Simple reports `semantic: unknown extern function:
  rt_enum_payload`; the remaining fix must use an owner-supported payload path
  or a safer statement/expression lowering refactor.
- hardening: G3/G5/G2/G6 closed. `check-async-library-hardening-evidence.shs` now parses `Passed:/Failed:` summaries (fail on failed>0, passed==0, or no-summary; exit code no longer trusted) and covers 19 specs including actors/generators/task_spawn/multicore_green representatives. Hardening matrix gained `qemu_scheduler_smp_handoff` row (host-mode `green_carrier_qemu_spec.spl`, summary-parsed, wired into release blockers; live `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` documented as separate readiness note). `check-simpleos-critical-formal-proofs.shs --self-test` proves require_theorem rejects a stripped theorem (AC-3 regeneration durability).
- evidence: after checker hardening, `sh scripts/check/check-async-library-hardening-evidence.shs` passes 19/19 and `sh scripts/check/check-simpleos-mission-critical-release.shs` (OSS CAD sourced) reports `STATUS: PASS ... release_blockers=none` with matrix 25/25 including the new SMP-handoff row.
- historical bug: `test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl` previously failed with `semantic: invalid assignment: cannot assign field on non-object value`; it was tracked in `doc/08_tracking/bug/task_spawn_runtime_pool_spec_semantic_fail_2026-07-05.md` and temporarily excluded from the roll-up.
- audit: re-audit (sonnet) found 6 verification gaps. Blocks-flight-level: (G2) `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl` (`SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1`) is referenced by NO check script — baremetal scheduler/SMP hardening rests on interpreter-hosted specs only; (G3) `check-async-library-hardening-evidence.shs:44` trusts `simple test` exit code, interpreter-mode only, no example-count parse — a spec executing 0 real assertions still passes. Weakens-evidence: (G4) hardening matrix trusts dated `doc/09_report/*.md` via string `contains`, no freshness check; (G5) actor/generators/task_spawn/multicore_green unit specs exist but are absent from the async evidence roll-up. Minor: (G6) AC-3 post-regeneration durability has no self-test. Firmware (Codex merge-owner lane): (G1) `logic.spl` `nvme_fw_rv32_logic_selftest()` returns first-fail ORDINAL 1-21 but `entry.spl` `_emit_fail_mask` decodes it as a per-check BITMASK — failure letters are wrong and multi-failure info is lost; align to a real OR'd bitmask and drop the vestigial `& 65535`.
- skill: `.claude/skills/spipe.md` now links the mission-critical robust-software guide directly and corrects concurrency evidence wording from stale `green_spawn`/`std.concurrent.green_thread` names to `cooperative_green_spawn`, `cooperative_green_spawn_value`, `multicore_green_spawn`, and `task_spawn` with `used_runtime_pool()` evidence for M:N claims.
- process: `test/01_unit/runtime/process_is_running_spec.spl` now imports `process_spawn_async`, `process_is_running`, `process_wait`, `process_kill`, and `process_is_alive` from `app.io.mod`, so the counted lifecycle evidence exercises the documented app process facade.
- evidence: `bin/simple test test/01_unit/runtime/process_is_running_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 8 examples, 0 failures; `sh scripts/check/check-async-library-hardening-evidence.shs` passed 19/19 with `async_library_hardening_failed=0`.
- nvme: `examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic.spl` now maps each nonzero subtest result to a fixed section bit before aggregation, so internal error counts such as `100`, `313`, or `0x80` cannot corrupt `entry.spl`'s UART fail-mask decoding.
- evidence: `bin/simple test test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 6 examples, 0 failures; `bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl` printed `RV32 NVME FW LOGIC OK`; `bin/simple spipe-docgen test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl --output doc/06_spec --no-index` generated `doc/06_spec/test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.md` with 1 complete doc and 0 stubs.
- review: G4 stale-report freshness was rechecked by a high-capability sidecar; `check-simpleos-hardening-evidence-matrix.shs` already gates dated static reports by filename age and blocks with `reason=stale-static-reports`, so the old G4 audit note is stale.
- runtime_need: `task_spawn_runtime_pool_spec.spl` was excluded because the old `ThreadPool.default().submit_value()` path hit interpreter object/method-dispatch failures before proving the task facade.
- facade_checked: `std.concurrent.multicore_green` already owns the proven `rt_pool_submit` / `rt_pool_join` / `rt_pool_is_done` pattern.
- chosen_path: `src/lib/nogc_async_mut/thread_pool.spl` now reuses the approved `multicore_green_spawn` facade for `task_spawn` instead of adding another direct `rt_pool_*` owner exemption.
- rejected_shortcuts: did not leave `async_host_task_identity_spec.spl` as a proxy, did not add a fixture-only bypass, and did not add raw `rt_pool_*` access outside the sanctioned multicore-green facade.
- evidence: `bin/simple test test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 1 example, 0 failures; `sh scripts/check/check-async-library-hardening-evidence.shs` passed 19/19 with `task_spawn_runtime_pool_spec.spl`; `sh scripts/check/check-simpleos-formal-coverage.shs` reported `STATUS: PASS simpleos-formal-coverage`.
- docs: Updated the concurrency API maps in `doc/07_guide/lib/misc/stdlib.md`, `doc/07_guide/compiler/check_perf.md`, `.codex/skills/coding/SKILL.md`, and `.claude/skills/spipe.md` so `task_spawn` is documented as the lower-level facade over `multicore_green_spawn`, not a separate direct `rt_pool_*` owner.
- docs: `test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl` now uses `expect(got).to_equal(expected)` instead of `rt_exit`, and `bin/simple spipe-docgen ... --no-index` regenerated `doc/06_spec/test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.md` with 1 complete doc and 0 stubs; the manual now shows the equality assertion directly.
- async: `task_spawn` now stores the underlying `MulticoreGreenHandle` and joins it through `TaskHandle.join()` instead of pre-joining during spawn, preserving handle-based completion while still reusing the sanctioned `multicore_green_spawn` facade.
- evidence: `bin/simple test test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 2 examples, 0 failures; `bin/simple check src/lib/nogc_async_mut/thread_pool.spl` passed; `bin/simple spipe-docgen test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl --output doc/06_spec --no-index` regenerated 1 complete doc with 0 stubs.
- evidence: `sh scripts/check/check-async-library-hardening-evidence.shs` passed 19/19 with `task_spawn_runtime_pool_spec.spl` counted as 2 passed examples; `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` passed; `git diff --check` passed; generated-spec layout guard returned `0`.
- evidence: `sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --self-test` passed, `sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --strict` reported `nvme_baremetal_wrapper_coverage_status=pass`, `blockers=none`, and RV32/RV64 wrapper/spec self-test status `pass`; `bin/simple test test/03_system/app/nvme_firmware/nvme_rv64_baremetal_boot_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 1 example, 0 failures.
- nvme: `examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` now generates a deterministic root-level diagnostic entry, symlinks `logic*.spl` into `build/os/generated`, avoids freestanding `char_code`, and calls `nvme_fw_boot_root__boot_main` directly from `_start`; `logic_reactor.spl` uses the fixed second drain step explicitly instead of a baremetal-sensitive loop for the known two-command floor.
- evidence: `bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_reactor.spl` passed; `bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl` printed `RV32 NVME FW LOGIC OK`; diagnostic `NVME_RV32_SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple NVME_RV32_BUILD_TIMEOUT_SECS=90 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` produced `build/nvme_fw_rv32.elf`; `sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/boot.shs build/nvme_fw_rv32.elf` failed closed with section mask `EJMBSPHQIFACTDWLYKGN`, so live rv32 firmware PASS remains blocked and must not be claimed.
- evidence: `sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --strict` passed after the wrapper edit; `bin/simple test test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed 3 examples, 0 failures.
- evidence: `git diff --check` passed; generated-spec layout guard returned `0`; `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` both passed.
- sidecars: Six parallel lanes audited the remaining gaps. Results: NVMe wrapper patch restored the stock rv32 boot hook path; RV32 scalar/codegen likely needs a tiny i64 literal/binop QEMU smoke before compiler repair; async G3/G5 are closed, but G2 live QEMU hardware-handoff evidence is only partially closed and must not support final hardware claims until run with `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` / `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1`; mission-critical/formal gates are green when OSS CAD is sourced, but fresh hosts still need `sby`, `yosys`, and an SMT solver; `$sp_dev` now routes robust-SW lanes to the mission-critical guide.
- nvme: `examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` now generates a tiny root that imports `os.kernel.arch.riscv32.boot` plus `entry.{rt_rv32_boot_optional_nvme_fw_selftest}`. `llvm-nm build/nvme_fw_rv32.elf` shows stock `_start`, `os__kernel__arch__riscv32__boot__boot_main`, strong `rt_rv32_boot_optional_nvme_fw_selftest`, and `entry__nvme_fw_rv32_selftest`.
- evidence: `NVME_RV32_SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple NVME_RV32_BUILD_TIMEOUT_SECS=90 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` produced `build/nvme_fw_rv32.elf`; `sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/boot.shs build/nvme_fw_rv32.elf` failed closed after real boot init (`LOG OK`, `MEM OK`, `PMM OK`, `HEAP OK`, `SVC OK`, `BOOT OK`) with section mask `EJMBSPHQIFACTDWLYKGN`. Live firmware PASS remains blocked by rv32 baremetal logic/codegen mismatch, not wrapper or boot plumbing.
- 2026-07-07 non-bootstrap-first update: per user request, bootstrap native-build work is postponed and `src/app/cli/bootstrap_main.spl` is restored to the known `run_native_build_bootstrap(args) -> 1` stub. Current non-bootstrap evidence: `bin/simple check src/app/cli/bootstrap_main.spl` passed; `sh scripts/check/check-async-library-hardening-evidence.shs` passed 19/19; `sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --strict` passed with blockers `none`; `sh scripts/check/check-simpleos-mission-critical-release.shs` with OSS CAD Suite sourced timed out at 300s with no status output, so no SimpleOS release PASS is claimed from this run.
- 2026-07-07 SimpleOS release wrapper typing/test update: `scripts/check/check-simpleos-mission-critical-release.shs` now runs its matrix under `MATRIX_TIMEOUT_SECS` and reports `matrix_status=matrix-timeout` plus `matrix_out`/`matrix_err` instead of hanging silently. Evidence: `sh -n scripts/check/check-simpleos-mission-critical-release.shs` passed; `sh scripts/check/check-simpleos-mission-critical-release.shs --self-test` passed; `MATRIX_TIMEOUT_SECS=5 sh scripts/check/check-simpleos-mission-critical-release.shs` with OSS CAD Suite sourced failed closed with `matrix_status=matrix-timeout`.
- 2026-07-07 non-bootstrap SimpleOS matrix update: `scripts/check/check-simpleos-hardening-evidence-matrix.shs` now bounds formal/QEMU executable rows with `SIMPLEOS_HARDENING_GATE_TIMEOUT_SECS` and emits `simpleos_hardening_gate_start/status` trace lines. `scripts/check/check-simpleos-formal-coverage.shs` now audits the bounded `run_gate ...` calls. The green-carrier QEMU spec removes stale `build/os/simpleos_green_carrier_probe.elf` before current-source builds and only boots QEMU when the build succeeds, so failed current-source links cannot be masked by stale ELF output. Evidence: `sh scripts/check/check-simpleos-formal-coverage.shs` passed; `bin/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean --timeout 60 --sequential` passed the default non-live lane; `bin/simple spipe-docgen test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --output doc/06_spec --no-index` generated 1 complete manual with 0 stubs; with OSS CAD Suite sourced, `SIMPLEOS_HARDENING_GATE_TIMEOUT_SECS=90 MATRIX_TIMEOUT_SECS=240 sh scripts/check/check-simpleos-mission-critical-release.shs` now completes with `matrix_status=pass`, `prereq_status=ready`, and release blockers exactly `qemu_scheduler_smp_handoff,qemu_scheduler_hw_handoff`. The blocker logs show current-source freestanding link failure on missing runtime symbols such as `rt_array_data_ptr_u8`, `rt_dict_remove`, `rt_string_to_int_lenient`, and `rt_simd_*`; LLVM backend is unavailable in this build.
- 2026-07-07 non-bootstrap syscall handoff fix: bootstrap remains postponed. The `qemu_scheduler_hw_handoff` blocker was traced to `rt_extras.c` NOP definitions of `rt_read_msr`/`rt_write_msr` shadowing the x86_64 baremetal `rdmsr`/`wrmsr` helpers; linked code returned `nil` instead of programming EFER/STAR/LSTAR/SFMASK, so ring-3 `syscall` never reached `kernel_syscall_entry_asm`. Removed those two NOPs so `baremetal_stubs.c` owns the MSR helpers, kept current-CPU syscall-entry programming, and changed the final user payload to emit `USER_SYSCALL_PASS=true` through syscall 60 after returning to user mode. Evidence: `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 bin/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential` passed 3 examples; `SIMPLEOS_HARDENING_GATE_TIMEOUT_SECS=180 sh scripts/check/check-simpleos-hardening-evidence-matrix.shs` passed with `simpleos_hardening_matrix_passed=26/26`, `simpleos_hardening_qemu_scheduler_hw_handoff_status=pass`, and `simpleos_hardening_mission_critical_release_blockers=none`; `SIMPLEOS_HARDENING_GATE_TIMEOUT_SECS=180 MATRIX_TIMEOUT_SECS=360 sh scripts/check/check-simpleos-mission-critical-release.shs` reported `STATUS: PASS ... release_blockers=none prereq_status=ready`.
- 2026-07-07 x86 source-check cleanup: renamed x86_64 local interrupt wrappers from grammar-keyword names `cli`/`sti`/`hlt` to `x86_cli`/`x86_sti`/`x86_hlt` and updated x86_64 interrupt callers. Evidence: `bin/simple check src/os/kernel/arch/x86_64/cpu.spl` passed, `bin/simple check src/os/kernel/arch/x86_64/interrupt.spl` passed, and the opt-in green-carrier hardware handoff spec still passed 3 examples.
- 2026-07-07 RV32 NVMe non-bootstrap follow-up: added `scripts/check/check-nvme-rv32-minimal-live.shs`, a pure-Simple minimal live check that builds a tiny rv32 `_start` and the existing firmware hook without importing the full SimpleOS boot graph. The checker strips comments/blank lines into `build/os/generated/nvme_fw_rv32_minimal_src` before compiling, but `NVME_RV32_BUILD_TIMEOUT_SECS=90 sh scripts/check/check-nvme-rv32-minimal-live.shs` still fails closed with `STATUS: FAIL nvme-rv32-minimal-live build_rc=124`; phase evidence shows `n_sources=24`, parse reaches `logic_map.spl`, and no QEMU media is produced. `NVME_RV32_BUILD_TIMEOUT_SECS=90 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` also failed closed before producing `build/nvme_fw_rv32.elf`. Rust seed/debug diagnostic compilers now print `WARNING: this Rust-built Simple binary is a bootstrap seed only` and fail because LLVM is unavailable, so no Rust-seed media is claimed. Remaining non-bootstrap blocker: pure-Simple rv32 native-build throughput/media generation for the firmware live PASS, distinct from postponed full bootstrap/deploy.
- 2026-07-07 RV32 NVMe rejected shortcut: bundling the stripped firmware logic into one generated 70 KB source reduced the minimal checker to `n_sources=1`, but a 90s run timed out while parsing that single root file. The checker remains on split stripped sources, which reaches farther through the firmware closure.
- 2026-07-07 RV32 NVMe minimal checker update: fixed LLVM return emission for mismatched operand/function return widths, kept constant SSA types aligned with declared local types, and added an RV32 bare-metal LLVM link path so `NVME_RV32_MINIMAL_SECTIONS=0 NVME_RV32_BUILD_TIMEOUT_SECS=90 sh scripts/check/check-nvme-rv32-minimal-live.shs` now reports `STATUS: PASS nvme-rv32-minimal-live-root-build diagnostic_only=true`. Prefix mode now inlines only the selected firmware logic files instead of accidentally exposing the full source tree. Remaining non-bootstrap blocker: `NVME_RV32_MINIMAL_SECTIONS=1 ...` loads `n_sources=1`, parses the generated root, then aborts with stack overflow during HIR lowering of the first real logic function (`rv32_xor7`), so bootstrap is not the only remaining item.
- 2026-07-07 RV32 NVMe refined blocker: a focused 7-parameter rv32 return probe now compiles to object with the pure-Simple compiler, confirming the LLVM return-width/local-type fix. The remaining `NVME_RV32_MINIMAL_SECTIONS=1` failure is earlier in HIR lowering: a tiny `val r = f(d1)` call-initializer reproducer stack-overflows before expression-call lowering starts, while extracting/lowering the `StmtKind.Val` initializer payload. Bootstrap/full deploy remains postponed, but this HIR payload/call-initializer issue is still a non-bootstrap blocker for the first real firmware logic section.
- 2026-07-07 RV32 NVMe assignment-expression follow-up: bootstrap remains
  postponed. The minimal checker now emits the wrapper `_selftest` fail mask as
  one `val fail = 0 + ...` expression instead of generated `var fail` plus
  assignment, which removes one wrapper-only assignment lowering trigger. Source
  compiler work also adds `rt_enum_payload` to the native-safe extern list and
  routes `StmtKind.Expr` payload extraction through that existing runtime helper
  before assignment-expression routing; `bin/simple check
  src/compiler/80.driver/compilability.spl`, `bin/simple check
  src/compiler/20.hir/hir_lowering/statements.spl`, and
  `bin/simple test test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl
  --mode=interpreter --clean --timeout 60 --sequential` passed.
- blocker: the deployed `bin/simple` ELF is unchanged because full
  bootstrap/deploy is postponed, so live RV32 evidence still reflects the old
  compiler. A tiny RV32 native-build repro with `fail = 1` still stack-overflows
  in HIR on the active binary, and
  `NVME_RV32_MINIMAL_SECTIONS=1 NVME_RV32_BUILD_TIMEOUT_SECS=90
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  now fails at `phase3:hir:function:start ... rv32_rain_selftest`. No live RV32
  PASS is claimed.
- 2026-07-07 RV32 NVMe diagnostic shaper correction: the `rt_enum_payload`
  source detour was removed because native-build rejects it with
  `semantic: unknown extern function: rt_enum_payload`. The minimal checker now
  shapes only the generated diagnostic source: N=1 uses an assignment-free
  `rv32_xor7`, a single RAIN recovery assertion, direct `val fail =
  rv32_rain_selftest()`, and `SIMPLE_BOOTSTRAP_SKIP_MIR_OPT=1` to bypass the
  old optimizer nil-kind failure. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs`, `git diff --check --
  scripts/check/check-nvme-rv32-minimal-live.shs`, and
  `bin/simple test test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl
  --mode=interpreter --clean --timeout 60 --sequential` passed.
- blocker: `NVME_RV32_MINIMAL_SECTIONS=1 NVME_RV32_BUILD_TIMEOUT_SECS=90
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  now clears HIR, borrow check, async processing, AOP, and MIR optimization
  skip, then fails after `aot:format:done` with `semantic: undefined field
  'kind': cannot access field on value of type 'nil'`. Tiny RV32 probes show a
  branch/call wrapper and a single `if` expression both reach LLVM, so the next
  blocker is narrower than HIR assignment lowering but still prevents live RV32
  PASS. No full bootstrap/deploy was run.
- 2026-07-07 RV32 NVMe N=1 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now uses a shaped N=1 diagnostic RAIN probe
  that avoids the active compiler's RV32 assignment, parameter-width,
  comparison, and normal-function inline-asm traps. The Simple object exposes
  `rv32_rain_selftest`; the checker renames the compiler-emitted dummy
  `_start`, links a tiny external RV32 `_start` stub with matching `ilp32d`
  ABI, and the stub prints UART PASS/FAIL after calling the selftest. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=1 NVME_RV32_BUILD_TIMEOUT_SECS=90
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: this is a diagnostic first-section live PASS, not full RV32 firmware
  PASS. Full `NVME_RV32_MINIMAL_SECTIONS` unset / multi-section firmware still
  must not be claimed until the remaining active-compiler RV32 i64/codegen and
  throughput blockers are fixed or the postponed bootstrap/deploy picks up the
  source compiler repairs.
- 2026-07-07 RV32 NVMe N=2 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now also shapes the ECC section for prefix
  diagnostics, using one `i32` correction identity instead of the real
  assignment-heavy ECC loop. Prefix aggregation now sums zero/nonzero section
  returns without per-section bit multiplication, and generated `_selftest`
  returns `i32` to match the active RV32 backend. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=2 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=2 is still diagnostic prefix coverage only. The real ECC
  implementation and later sections remain gated by active-compiler RV32
  assignment/loop/i64/codegen limits; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=3 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now shapes the journal section for prefix
  diagnostics with a small `i32` compaction identity instead of the real
  assignment-heavy WAL simulation. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=3 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=3 remains diagnostic prefix coverage only. The real journal
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=4 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now shapes the map section for prefix
  diagnostics with a small `i32` cache/write-back identity that avoids active
  RV32 negative-literal and mutation lowering traps. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=4 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=4 remains diagnostic prefix coverage only. The real map
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=5 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now shapes the band allocator section for
  prefix diagnostics with a small `i32` allocation/free identity instead of the
  real mutation-heavy block lifecycle. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=5 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=5 remains diagnostic prefix coverage only. The real band
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=6 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now shapes the scheduler section for prefix
  diagnostics with a small `i32` balanced-vs-serialized channel identity instead
  of the real loop/mutation drain model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=6 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=6 remains diagnostic prefix coverage only. The real scheduler
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=7 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now shapes the power/thermal section for
  prefix diagnostics with a small `i32` throttle/cooldown identity instead of
  the real loop/mutation thermal model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=7 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=7 remains diagnostic prefix coverage only. The real
  power/thermal implementation and later sections are still not live-proven
  with active `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=8 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now shapes the HIL section for prefix
  diagnostics with a small `i32` command/queue/PRP identity instead of the real
  parse-heavy host-interface model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=8 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=8 remains diagnostic prefix coverage only. The real HIL
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=9 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now shapes the queue phase section for prefix
  diagnostics with a small `i32` queue-wrap/phase identity instead of the real
  loop/mutation ring model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=9 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=9 remains diagnostic prefix coverage only. The real queue phase
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=10 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now shapes the IO command section for prefix
  diagnostics with a small `i32` opcode/status identity instead of the real
  mutation-heavy command model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=10 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=10 remains diagnostic prefix coverage only. The real IO command
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=11 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal checker now shapes the Flush section for prefix
  diagnostics with a small `i32` clean/commit/bad-namespace identity instead
  of the real mutation-heavy flush model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=11 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=11 remains diagnostic prefix coverage only. The real Flush
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=12 diagnostic PASS: bootstrap/deploy remains
  postponed. The existing Admin diagnostic shaper covers the prefix slice with
  a small `i32` admin/status identity instead of the real mutation-heavy admin
  model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=12 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=12 remains diagnostic prefix coverage only. The real Admin
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=13 diagnostic PASS: bootstrap/deploy remains
  postponed. The existing Reactor diagnostic shaper covers the prefix slice
  with a small `i32` task/owner identity instead of the real mutation-heavy
  reactor model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=13 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=13 remains diagnostic prefix coverage only. The real Reactor
  implementation and later sections are still not live-proven with active
  `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=14 diagnostic PASS: bootstrap/deploy remains
  postponed. The existing Policy/Target diagnostic shaper covers the prefix
  slice with a small `i32` policy/geometry identity instead of the real
  branch-heavy target model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=14 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=14 remains diagnostic prefix coverage only. The real
  Policy/Target implementation and later sections are still not live-proven
  with active `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=15 diagnostic PASS: bootstrap/deploy remains
  postponed. The existing DRAM durability diagnostic shaper covers the prefix
  slice with a small `i32` arena/durability identity instead of the real
  mutation-heavy durability model. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=15 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=15 remains diagnostic prefix coverage only. The real DRAM
  durability implementation and later sections are still not live-proven with
  active `bin/simple`; no full RV32 firmware PASS is claimed.
- 2026-07-07 RV32 NVMe N=21 diagnostic PASS: bootstrap/deploy remains
  postponed. The minimal live checker now covers every registered prefix slice
  through namespace guard with bounded `i32` diagnostic identities instead of
  the real mutation-heavy firmware models. Evidence:
  `sh -n scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  `git diff --check -- scripts/check/check-nvme-rv32-minimal-live.shs` passed,
  and `NVME_RV32_MINIMAL_SECTIONS=21 NVME_RV32_BUILD_TIMEOUT_SECS=120
  RUST_MIN_STACK=134217728 sh scripts/check/check-nvme-rv32-minimal-live.shs`
  printed `ALL RV32 NVME FW CHECKS PASS` and
  `STATUS: PASS nvme-rv32-minimal-live`.
- blocker: N=21 remains diagnostic prefix coverage only. The real full firmware
  implementations are still not live-proven with active `bin/simple`; no full
  RV32 firmware PASS is claimed.
