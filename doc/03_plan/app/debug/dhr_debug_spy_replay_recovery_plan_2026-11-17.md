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
| P0 | Truthful capabilities: repair the defects listed in §1 | No unsupported operation reports success | **done** (#10357 #10363 #10366 #10369 #10370 #10371 #10372 + this) |
| P1 | Protect the baseline: absent/prepared/active profiles, real off-identity comparison | OFF-01..08 evidence | **in progress** |
| P2 | Failure evidence: assert/fault record, independent broker, deadlines | Real assert and fault, plus a no-debugger test | todo |
| P3 | Host managed recovery: isolated interpreter worker, state roots, effect fencing | A V2 failure restores a verified V1 without duplicate effects | todo |
| P4 | Unified native generation lifetime (legacy loader → KPF, retention pin) | Concurrent old/new execution with safe retirement | todo |
| P5 | Shared Spy plus bare-metal emitter, with a separate replay event family | Bounded operation, disclosed loss | todo |
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
| RR-03 | Kernel/realtime Replay mode read the logged schedule decision and discarded it | A different live tid, wrong kind, or end-of-log is a `ScheduleMismatch` divergence. Enforcing the logged tid on the scheduler is P6 | replay_kernel_fail_closed_spec 8/8 |
| RR-05 | `HardwareReplayController.restore_checkpoint` said "checkpoint restored" | Says registers and watched RAM only; device/IRQ/DMA not restored | — |

P0 exit gate met for the §1 defect list. Every listed operation now either works or reports its failure or limit.

## Next: P1 (protect the baseline)

1. OFF-01: dependency closure. Show that the default bootstrap/release import closure contains no recorder, replay, or debug-provider module (`os.kernel.replay`, `std.replay`, `trace.xray_*`, `debug.remote`). Add a fail-closed check script that walks `use` edges from the bootstrap CLI entry.
2. OFF-02: run `check-xray-static-off-identity.shs` against a real candidate/baseline pair, not only its self-test, and record the receipt.
3. Then P2 (assert/fault record → broker) and P3 (host managed recovery on KPF workers).
