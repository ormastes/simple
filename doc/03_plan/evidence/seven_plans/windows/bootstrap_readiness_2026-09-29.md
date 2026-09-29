# Windows seven-plan execution: bootstrap readiness

Status: IN_PROGRESS; production verification TEST_BLOCKED.
Owner and merge owner: primary Codex session. Sidecars: N/A.
Order authorized by the user: all seven Windows items, then macOS; push PRs.
Latest goal update: all seven Windows items, then Linux through WSL; keep the
earlier macOS host scope separate and unverified.
No item is certified complete by this report.

## Scope retained

The [seven-plan umbrella](../../../seven_plans_host_completion_2026-09-29.md)
remains authoritative for the full scope and per-host done gates.

| Item | Authoritative starting requirement/plan | Windows evidence still required |
|---|---|---|
| 1 | `doc/02_requirements/feature/simple_platform_unification.md` | Parser/runtime parity, admitted providers, release and SimpleOS boot evidence |
| 2 | `doc/02_requirements/feature/simple_distributed_textual_databases.md` | Two-clone conflict, recovery, history and Windows filesystem behavior |
| 3 | `doc/02_requirements/feature/collection_planner.md` | P0 semantics, real lowering, generic collections and retained NFRs |
| 4 | `doc/01_research/compiler/linker/mold_mdsocpp_linker_2026-09-15.md` | Actual PE/COFF linking, relocations/imports/exports, failures and performance |
| 5 | `doc/02_requirements/feature/runtime_optional_provider_binary_size_optimization.md` | Canonical kernel/aspect scope reconciliation, dependency exclusion and size/load evidence |
| 6 | `doc/03_plan/compiler/perf/persistent_package_module_index_compile_optimization_plan_2026-09-02.md` | Canonical final-plan reconciliation, cold/warm/edit builds and invalidation correctness |
| 7 | `doc/02_requirements/feature/profile_switchable_container_algorithms.md` | Two admitted workload profiles driving actual generic algorithms, lowering, explanations and NFRs |

These are starting references, not scope reductions to the work already present.
Item 7's current requirements explicitly leave typed extraction/lowering,
explanation and cross-engine proof unfinished. TODO database IDs 341 (shared),
344 (Windows) and 342 (macOS) already exist and must be reused. No new task IDs
were invented. Updating task state through the canonical Simple interface is
blocked by the missing admitted general-purpose runtime; no seed todo-scan ran.

## Isolation and source identities

- Main checkout: `C:/Users/User/dev/simple`, dirty and used by other sessions.
  It was neither rebased nor edited by this lane.
- Execution checkout: `C:/Users/User/dev/simple-seven-plans-windows`.
- Branch: `work/seven-plans-windows-20260929`.
- Base: `d0447ebbf9b` from fetched `origin/main`.
- Existing bootstrap checkout: `C:/Users/User/dev/simple-bootstrap-main-windows`,
  base `bb3f6ab8ab2` plus another session's uncommitted fixes. Its files and caches
  were inspected read-only. Permission to incorporate those fixes was requested;
  this change does not incorporate them.

## Current bootstrap failure

The earlier seed-link failure is no longer the latest execution result. The
existing Windows run compiled 1,060 modules and linked Stage 2, then failed its
frontend sanity gate on 2026-09-29 at approximately 17:02 local time:

```text
compiled=1060 reused=0 failed=0
Time: 985.9s compile + 45.3s link = 1031.3s total
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
error: in-process native-build: LLVM native linking failed: Native linking is unsupported on host architecture 'x86_64' for OS 'unknown'
status=fail
frontend_smoke_status=1
```

Candidate: `.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-gnu/simple.exe.rejected`
under the existing bootstrap checkout.
SHA-256: `0008d5431bca9b893478eb2340602e67d6cb5141a8696eb81c3acbc817c66a3d`.
The rejection is authoritative: this is not an admitted Stage 2 compiler,
Stage 3 compiler, deployed CLI, SPipe runner or release artifact.

Evidence inspected in that checkout:

- `build/native_probe/bootstrap-local-abifix.log`
- `.simple/storage/build/bootstrap/logs/x86_64-pc-windows-gnu/stage2-native-build.log`
- `.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-gnu/stage2-sanity.env`
- Its `.frontend-failure.log` and `.frontend-driver.log` companions.

The receipt records the same candidate hash before and after the failing gate.
No new bootstrap retry was started and no existing cache was removed.

## Narrow diagnostic and result

Added `test/fixtures/compiler/bootstrap_host_identity.spl`. It compares the
runtime platform primitive with the public facade, reports architecture, checks
the supported-host predicate and rejects `unknown`. It has distinct nonzero
exit codes for disagreement, unsupported detection and a falsely accepted host.

This fixture was compiled once with the existing **Rust bootstrap seed**, solely
to diagnose the bootstrap failure. It is not general feature-test evidence.
Producer: `stage2-runtime-authority/simple.exe` in the existing bootstrap tree.
Producer SHA-256: `6456107ce86e91d06a03171873b141632b819b8a59637f9fab414e0dcee0dae6`.
Source: this lane's base plus the new fixture. ABI: `x86_64-pc-windows-gnu`.
Toolchain: `C:/llvm-23/clang+llvm-23.1.1-x86_64-pc-windows-msvc` with MinGW tools.
Environment: `SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_WINDOWS_ABI=gnu`, matching
`SIMPLE_LLVM_PATH` and `LLVM_SYS_231_PREFIX`.

Command (producer/runtime paths abbreviated by the recorded locations above):

```text
<producer> native-build --target x86_64-pc-windows-gnu --backend llvm --runtime-bundle core-c-bootstrap --source src/lib --source test/fixtures/compiler --entry-closure --threads 2 --cache-dir build/native_probe/seven-plans-windows/host-identity-cache --entry test/fixtures/compiler/bootstrap_host_identity.spl --runtime-path <stage2-runtime-authority> -o build/native_probe/seven-plans-windows/host-identity.exe
```

Build: exit 0; 19 compiled, 0 cached, 0 failed; 2.0 seconds compile and 11.0
seconds link. Execution: exit 0, with the following exact output:

```text
runtime_os=windows
host_os=windows
host_arch=x86_64
windows_supported=true
unknown_supported=false
```

Diagnostic executable SHA-256:
`94de332b2f4f8a9ebe99553c177f6636b324543c288597f30bcd7ae6eaaafea0`.
Build/run logs and cache are under `build/native_probe/seven-plans-windows/`.
Bulky artifacts are local-only; this checked-in report retains the relevant
output and identities. A future completion PR needs durable host artifacts.

Read-only LLVM disassembly of the **rejected full compiler** additionally shows
`platform_name_raw` jumping to `rt_platform_name`. The latter uses a seven-byte
literal at RVA `0x18f3c59`; decoding that PE section yields `windows`. The linker
calls `lib__nogc_sync_mut__io_runtime__host_os`, not the alternate environment
detector. This contradicts a missing Windows runtime constant as the cause.
It does not establish the root cause or prove the full detector executes correctly.

## Next bounded work

1. Resolve ownership before integrating the existing bootstrap ABI/link fixes.
2. Compare the full compiler's failing host/link path with this isolated control;
   investigate lowering, runtime representation and full-closure interactions.
   Do not mask the failure with an environment override or weakened admission.
3. Fix the proven shared cause and run a bounded, cache-preserving bootstrap
   verification, then establish an admitted self-hosted Windows CLI.
4. Claim/reconcile all seven task records through the canonical TODO interface.
   Complete implementation gaps and the umbrella's Windows acceptance gates.
5. Continue all seven items on Linux through WSL after Windows completion, per
   the latest goal update. Keep WSL and native-Linux evidence distinct. The
   earlier macOS scope still needs independent runtime and host evidence.

Verification status for the seven-item objective: **FAIL / incomplete**.
The passing diagnostic cannot close any host/item cell or authorize release.

## Follow-up: hosted compiler discovery

The next bounded diagnostic exposed a separate, reproducible discovery defect:
the installed clang-cl passes the headerless compiler probe but cannot find
`stdlib.h` when compiling the runtime. The probe now requires that header;
real-tool positive and negative controls behaved as expected. See the
[bug and validation record](../../../../08_tracking/bug/windows_hosted_cc_probe_accepts_missing_sdk_2026-09-29.md).
Rebuilt Simple execution and the compiler/lib/MCP/LSP acceptance gates remain
blocked. The source fix does not close the original host-identity investigation.
