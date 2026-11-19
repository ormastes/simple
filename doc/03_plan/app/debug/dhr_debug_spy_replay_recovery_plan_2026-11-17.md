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
| P4 | Unified native generation lifetime (legacy loader → KPF, retention pin) | Concurrent old/new execution with safe retirement | **in progress**: `share_pin` (#10379); legacy `DynLib` reload/unload under KPF pins (`DynlibGenerationHostV1`, see P4 progress) |
| P5 | Shared Spy plus bare-metal emitter, with a separate replay event family | Bounded operation, disclosed loss | **in progress**: replay-ring loss disclosed (#10378); bounded bare-metal Spy emitter `std.spy.bm_spy_emitter` (observer-contract kinds, drop-newest, in-stream Loss record, separate from the replay ring; `spy_baremetal_emitter_spec` 10/10); host drain adapter `std.nogc_sync_mut.trace.bm_spy_drain_v1.BmSpyDrainV1` pops ring records into observer-contract `TraceEventV1` values in order (Loss record -> disclosed `Loss` control event, `payload0` = lost count, at the gap position; unknown kind code fails the drain), drained stream folds through `trace_profile_fold_v1` (`spy_baremetal_drain_trace_spec` 5/5). Shared Spy intake: `XraySpyV1.ingest(events)` appends drained events to the same store `collect()` fills (all-or-nothing; per-context strictly increasing sequence; only site-bearing Entry/Exit/TailExit and site-less Loss with count > 0, else `InvalidArgument`), and `XraySpyV1.lost()` reports Loss `payload0` from the store plus the resident channel's loss counter; ingested bare-metal events profile identically to a direct fold and mix with collected channel events (`xray_spy_ingest_v1_spec` 7/7, `xray_spy_backend_v1_spec` 11/11). Not yet wired to a target hook or a live bare-metal transport (drain runs over the in-process emitter only) |
| P6 | Portable semantic replay | Scoped deterministic replay with no live fallback | **in progress**: layer-neutral core `std.replay.portable_replay` (`src/lib/nogc_async_mut_noalloc/replay/portable_replay.spl`): (kind, scope, value) events in a fixed ring allocated once, no allocation on the record/replay path; Record appends, Replay returns the logged value and never the live one, kind/scope mismatch and exhausted log are divergences returning a fail-closed value, events outside the one explicitly opened scope are live and unlogged, record overflow drops newest and is disclosed (`replay_portable_core_spec` 12/12). Portability proof: realtime `rr_hook_random` runs on the core (`replay_realtime_random_portable_spec` 7/7, pinned on the pre-P6 ring first; `realtime/replay_spec` 10/10, `replay_baremetal_core_spec` 32/32 unchanged). Open: the realtime adapter keeps its pre-P6 live fallback on divergence; random reads are no longer ordered against the ring's other kinds; kernel, bare-metal and the other realtime hooks still use their own encodings |
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
| P3 worker exit → transaction (#10376) | crash, deadline, or protocol violation of the candidate worker fails the candidate; a clean close does not | `recovery_worker_spec` 6/6 (pure policy). Real-subprocess: `real_worker_integration_spec` 3/3 on Windows 2026-11-19 (Git Bash `/bin/sh` child; the 0/3 was bare `.len` on arrays in codec/transport/protocol, not the spawn). Chained receipt: `real_worker_integration_spec` 5/5 on Windows 2026-11-19 (seed interpreter) — a real crashed V2 child's `exit_status()` fed to `kpf_recover_on_worker_exit` gives Applied/Restored, V1 active, V2 inactive, a WorkerExit record in the FailureSlotV1; a real protocol clean close stays in Probation with no record. Mutation check (flip the V2-inactive assert) fails that case (4 passed, 1 failed) |
| P2 failure slot (`FailureSlotV1`) | bounded first-fault-wins record with the valid marker set last; broker `take()`; first consumer is the worker-exit path (capture before restart) | `failure_slot_v1_spec` 4/4 (DBG-06 nested fault) |
| P2 interpreter assert → slot | **wired behind the `dhr` build feature**: `publish_assert_failure` in `failure_slot_v1.spl` (gate: `SIMPLE_FEATURES` lists `dhr`) is called from the 70.backend interpreter assert branch inside `@when(feature = "dhr")`, so a default build has no import or call. `check-core-lib-closure.shs` now drops feature-only `@when` blocks from the scan (selftest 8/8), so OFF-01 stays clean in both default (370 reached) and `--kernel-binary` (462 reached) modes | `failure_slot_assert_hook_spec` 5/5 on the seed (profile on → Assert record; off → slot empty). **Not verified:** the interpreter call site itself. The seed runs specs on its Rust interpreter, and no `SIMPLE_FEATURES=dhr` self-hosted build exists on this host. The K0 core interpreter (`10.frontend/core/interpreter/eval_builtins.spl`) and the MIR interpreter are not wired |
| P2 native signal → slot | **not wired** | Needs the externs in `doc/08_tracking/bug/crash_signal_bundle_extern_gap_2026-07-29.md` |
| Phase-3 build | Windows Stage-2 bootstrap at `27d436682c5` (cranelift, dynload; includes #10400 #10414 #10438–#10447) | **Stage 2 built, passed sanity and was admitted. The full-CLI compiler-test row was killed by the host RSS cap.** `compiler_cli_build` reached HIR module 1313/4084 in 83 min, then hit `rss-cap-exceeded` at peak 14.8 GB against a 14.76 GB cap. The bootstrap budgets this 32 GB host at one small-host worker; its own policy line puts a one-worker full-CLI build at about 30 GB. This is a host-capacity limit, not a code failure. Stage 3/full CLI needs a host with ≥ 64 GB RAM. |

## P4 progress (unified native generation lifetime)

| Item | Result | Evidence / limit |
|---|---|---|
| `share_pin` (#10379) | a live pin can take a second lease on a retired generation (GEN-02/03) | see #10379 |
| Legacy `DynLib` under KPF pins | `DynlibGenerationHostV1` (`src/lib/nogc_sync_mut/sffi/dynlib_generation_v1.spl`) binds each legacy-loaded `DynLib` to one `KpfGenerationTable` generation. `publish` is the reload (old generation retired, still mapped); `begin_call`/`end_call` hold a KPF pin for a whole caller operation; `unload` runs `collect` first and calls `DynLib.close()` only when it accepts, so a pinned generation is refused with `GenerationStillPinned` and stays live | `dynlib_generation_spec` 5/5 on Windows 2026-11-20 (seed interpreter), real `kernel32.dll` loads through `DynLib.load_checked`, liveness read from `dynlib_lifetime_owner_v1`. Mutation (close before `collect`) fails 2 cases. **Open:** `DynI64FnSlot` cached slots still use only the per-call lifetime owner; Linux/macOS not run; no self-hosted binary run |
| `DynLoader` opt-in reload path | `DynLoaderReloadV1` (same file) keeps one `DynlibGenerationHostV1` per DynLoader path key. `reload(path, provider_id, digest)` loads a fresh mapping and publishes it as that path's active generation; `call_checked` takes a lease for the whole call; `unload(path, generation)` closes a retired mapping only after its last lease ends. It shares no state with the `DynLoader` singleton, so existing callers are unchanged. It is a sibling type, not a `DynLoader` method, because `dynlib_generation_v1` imports `sffi/dynamic` | `dynlib_generation_spec` 10/10 on Windows 2026-11-20 (seed interpreter, real `kernel32.dll`): 5 new cases cover a lease held across reload (unload refused, old lib live), collect/close after `end_call`, a lease held only for the duration of `call_checked`, an unknown path refused, and the singleton cache identity unchanged. Mutation (drop the lease release in `call_checked`) fails 1 case. **Open:** no existing caller (`sffi_call`, torch/cuda loaders) migrated; `DynLoader.call*` still has no reload; Linux/macOS not run; no self-hosted binary run |

## Next

1. Fix or route the Stage-2 link bug above, then rerun the build. Once a pure-Simple binary exists, rerun OFF-02 and the DHR specs on it.
2. Done 2026-11-19: real crash→rollback receipt is one spec (`real_worker_integration_spec`, see P3 row). Open: the receipt ran on the Rust-seed interpreter, not a self-hosted binary, and the child's native exit code is not read (`exit_status()` classifies by protocol close / termination only).
3. Verify the P2 assert hook on a `SIMPLE_FEATURES=dhr` self-hosted build: a failing `assert` under `simple run` must leave an Assert record in the process slot.
