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
| P0 | Truthful capabilities: repair the defects listed in §1 | No unsupported operation reports success | **in progress** |
| P1 | Protect the baseline: absent/prepared/active profiles, real off-identity comparison | OFF-01..08 evidence | todo |
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

## Next (P0 remainder, in order)

1. `os/realtime/replay/hooks.spl`: Replay mode reads the logged schedule/IRQ decisions but never enforces them. The scheduler must consume the forced tid. (Done: io_read/random mismatches now count as divergences.)
2. `RemoteReplayAdapter.restore_checkpoint` and `reverse_*` truncate the event log. Callers must not treat this as a target state restore.
3. T32 probe signature does not match SFFI. `t32_watchdog` timeout is not enforced.
4. `failure_capture.spl`: metadata only. Implement real capture, or reject the capability honestly.

Then P1 (off-identity gate beyond scanner self-test), P2, and P3.
