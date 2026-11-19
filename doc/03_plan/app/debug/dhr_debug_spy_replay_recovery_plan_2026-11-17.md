# Debug, Spy, Record/Replay, and Dynamic Module Recovery (DHR): Plan and Progress

Source: the consolidated design and research document from 2026-11-17, audited against
`release/1.0.0` @ `2a3cfc2eb7d`. That document is the design. This file holds only
the phase order, progress, and next steps. Section numbers below (§) refer to the
design document.

## Rules carried from the design

- Reuse the existing owners: KPF (generation and lifecycle), DebugServiceV1 (sessions
  and receipts), XraySpyV1 and the observer contract (observation), and SOSIX
  (platform). Do not add a second loader, debugger, or supervisor.
- Fail closed. An unsupported, missing, or diverged operation never reports success,
  and replay never falls back silently to live values.
- When off, the feature is absent: the default bootstrap and release closure gains no
  imports, buffers, or hooks.
- Code replacement, state rollback, crash containment, and deterministic replay are
  four separate guarantees. Prove each one separately.

## Phases

| Phase | Work | Exit gate | Status |
|---|---|---|---|
| P0 | Truthful capabilities: repair the defects listed in §1 | No unsupported operation reports success | **done** (#10357 #10363 #10366 #10369 #10370 #10371 #10372 #10373) |
| P1 | Protect the baseline: absent/prepared/active profiles, real off-identity comparison | OFF-01..08 evidence | **partial**: OFF-01 measured clean; OFF-02 blocked on host |
| P2 | Failure evidence: assert/fault record, independent broker, deadlines | Real assert and fault, plus a no-debugger test | **in progress** |
| P3 | Host managed recovery: isolated interpreter worker, state roots, effect fencing | A V2 failure restores a verified V1 without duplicate effects | **in progress** |
| P4 | Unified native generation lifetime (legacy loader → KPF, retention pin) | Concurrent old/new execution with safe retirement | **in progress**: `share_pin` (#10379) |
| P5 | Shared Spy plus bare-metal emitter, with a separate replay event family | Bounded operation, disclosed loss | **in progress**: replay-ring loss disclosed (#10378) |
| P6 | Portable semantic replay | Scoped deterministic replay with no live fallback | todo |
| P7 | rr / TTD / QEMU / TRACE32 backends | Per-target capability receipts | todo |
| P8 | Caret / IDE recovery and replay UI | Session-preserving upgrades | todo |
| P9 | Research: native macOS recorder, physical multicore replay | Feasibility first | not on critical path |

## P0 progress

| ID | Defect (§1) | Fix | Evidence |
|---|---|---|---|
| RR-01 | `bm_replay_core`: `pop_kind` advanced the head, so the value readers returned the NEXT event's data | Value readers read the slot of the last popped event | `test/03_system/tools/replay_baremetal_core_spec.spl` (2 new cases) |
| RR-02 | `os/kernel/replay/hooks.spl`: timer/random replay silently returned live values at end-of-log, on a wrong event kind, or (timer only) a wrong source | Reports `TimerMismatch`/`RandomMismatch` divergence | `test/03_system/tools/replay_kernel_fail_closed_spec.spl` |
| RR-04 | `HardwareReplayController.reverse_step/continue` returned `Ok` after only truncating the event list | Return `Err("unsupported: ...")` | same spec |
| DBG-T32 | `t32_debug_service_adapter_v1` and `dbgeng_debug_service_adapter_v1` were absent (left on unlanded merge `a8244005f9b`) | Restored (#10363, #10366) | adapter specs 8/8 and 3/3 |
| DBG-EVB | `evidence_bundle_writer_v1` imported by `embedded_dump_service_v1` but absent | Restored under `nogc_sync_mut/debug` (file I/O owner) (#10363) | writer 4/4, dump service 2/2 |
| DBG-OCD | OpenOCD `mdw`/`reg` parsers returned `[]`/`0`; TCL commands printed addresses in decimal after `0x` | Real parsers; `format_hex` in commands | `test/01_unit/os/realtime/openocd_probe_parse_spec.spl` 4/4, adapter spec 5/5 |

| DBG-WD | `T32Watchdog.guarded_op` ignored `operation_timeout_ms`; `kill_on_hang` ran a machine-wide `pkill` | Post-hoc overrun detection (labelled: not cancellation); global kill removed (#10370) | `t32_watchdog_deadline_spec` 2/2 (real module) |
| DBG-FC | `FailureCapture` recorded only a cycle while implying a checkpoint/memory capture | Keeps pc/sp or signal/pid, pins event-tail range, states what was not captured (#10371) | `test/01_unit/os/kernel/failure_capture_spec.spl` 3/3 |
| DBG-T32P | `Trace32Probe` never compiled (absent `t32_break`/`t32_go`, `std.os` path); stale SFFI shapes; unconditional success; `reset` sent `Break` | Ops via `T32_Cmd`, real SFFI shapes, results propagated (#10372) | `t32_probe_sffi_spec` 5/5 |
| RR-03 | Kernel/realtime Replay mode read the logged schedule decision and discarded it | `replay_hook_schedule` now returns the tid to run; `Scheduler.schedule_on_cpu` dispatches the logged tid in Replay (live pick stays queued). Wrong kind, end-of-log, or a non-runnable logged tid is a `ScheduleMismatch` divergence and nothing is dispatched (P6 follow-up) | replay_kernel_fail_closed_spec 13/13 |
| RR-05 | `HardwareReplayController.restore_checkpoint` said "checkpoint restored" | Says registers and watched RAM only; device/IRQ/DMA not restored | — |

P0 exit gate met for the §1 defect list. Every listed operation now either works or reports its failure or limit.

## P1 progress (protect the baseline)

| Gate | Result | Evidence / blocker |
|---|---|---|
| OFF-01 dependency closure | **0 optional providers in the compiler-kernel closure** (370 files reached at release tip `5e13df306b1`+) | DHR-OFF-01 assertion added to `scripts/check/check-core-lib-closure.shs` (BFS over every reached file, CORE or not; selftest fixture 7/7). The containing row `push-core-lib-closure` is advisory and already red for an unrelated reason: 83 non-core files beyond its 177-entry baseline. So the assertion reports, but does not yet block. |
| OFF-02 generated output | **blocked on this host** | `check-xray-static-off-identity.shs` refuses Rust-seed compilers by design and needs a pure-Simple compiler. None is deployed on the Windows host. Its own selftest also fails here (`clean-pair expected rc=0 got rc=1`). Needs a Linux run with a deployed self-hosted binary. |
| OFF-03..08 | not run | Bootstrap stages, runtime behaviour, prepared-idle budget, toggle, PE/Mach-O/firmware parity |

## P2/P3 progress

| Item | Result | Evidence / limit |
|---|---|---|
| P3 core: `KpfRecoveryTransaction` (#10375) | retention pin (GEN-04), epoch fence (REC-04), effect-aware rollback blocking on acknowledged/unknown writes (REC-02/03), Applied/Blocked/Rejected receipts | `recovery_transaction_spec` 8/8; mutation check fails REC-02 |
| P3 worker exit → transaction (#10376) | crash, deadline, or protocol violation of the candidate worker fails the candidate; a clean close does not | `recovery_worker_spec` 6/6 (pure policy). Real-subprocess: `real_worker_integration_spec` 3/3 on Windows 2026-11-19 (Git Bash `/bin/sh` child; the 0/3 was bare `.len` on arrays in codec/transport/protocol, not the spawn). It proves a real child crash yields `WorkerCrashed`; feeding that real exit into `kpf_recover_on_worker_exit` is not yet one spec |
| P2 failure slot (`FailureSlotV1`) | bounded first-fault-wins record with the valid marker set last; broker `take()`; first consumer is the worker-exit path (capture before restart) | `failure_slot_v1_spec` 4/4 (DBG-06 nested fault) |
| P2 interpreter assert → slot | **wired behind the `dhr` build feature**: `publish_assert_failure` in `failure_slot_v1.spl` (gate: `SIMPLE_FEATURES` lists `dhr`) is called from the 70.backend interpreter assert branch inside `@when(feature = "dhr")`, so a default build has no import or call. `check-core-lib-closure.shs` now drops feature-only `@when` blocks from the scan (selftest 8/8), so OFF-01 stays clean in both default (370 reached) and `--kernel-binary` (462 reached) modes | `failure_slot_assert_hook_spec` 5/5 on the seed (profile on → Assert record; off → slot empty). **Not verified:** the interpreter call site itself. The seed runs specs on its Rust interpreter, and no `SIMPLE_FEATURES=dhr` self-hosted build exists on this host. The K0 core interpreter (`10.frontend/core/interpreter/eval_builtins.spl`) and the MIR interpreter are not wired |
| P2 native signal → slot | **not wired** | Needs the externs in `doc/08_tracking/bug/crash_signal_bundle_extern_gap_2026-07-29.md` |
| Phase-3 build | Windows Stage-2 bootstrap (cranelift, dynload) | **Stage 2 links and passes sanity; compiler tests not yet run.** The A64 link failure is fixed by #10400; Stage 2 then built 1588/1588 modules and passed sanity. The Stage 2 tool rows refused because the reserve override was dropped; fixed by #10414. The rerun at `90845b3d882` is blocked by host commit exhaustion: ~3 GB of commit free, C: full so the pagefile can't grow, and rustc OOMs in the seed build. Needs host headroom, then a rerun. |

## Next

1. Fix or route the Stage-2 link bug above, then rerun the build. Once a pure-Simple binary exists, rerun OFF-02 and the DHR specs on it.
2. Chain a real `fake_real_worker.shs` crash exit into `kpf_recover_on_worker_exit` in one spec (transport half is green on Windows, see P3 row).
3. Verify the P2 assert hook on a `SIMPLE_FEATURES=dhr` self-hosted build: a failing `assert` under `simple run` must leave an Assert record in the process slot.
