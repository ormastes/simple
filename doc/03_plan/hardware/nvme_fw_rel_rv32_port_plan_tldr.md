# NVMe FW `rel_*` rv32 port (TL;DR)

> **Status (2026-07-19): NOT NOW — tracked follow-up.** `fw_rv32` is a
> bare-metal **self-test/logic floor** for 23 `fw/` subsystems (scalar
> free-fns + oracle cases, zero arrays, zero state, zero imports from `fw/`),
> not a running product. `rel_*` (6 policy lanes + `nd_types`, 1,013 lines) is
> **not yet wired as a production caller** in `fw/` (no `fil.spl`/`ftl.spl`
> mount) and rv32 is outside the reliability-engine architecture's scope.
> Porting now would validate logic the firmware doesn't run yet.

If/when triggered (rel_* lands in the FTL maintenance tick): all 13
`NUM_BLOCKS`-length `[i64]` arrays are representable in the existing
`logic_band_core.spl` idiom (element passed as scalar param, never resident)
but the porting unit is **per-field**, not per-mutator — `rel_health_note_read`
alone touches 4 fields. `nd_types.spl`/`RelLadderState` are array-free and
port ~1:1. The existing anti-drift guard (`logic_map_lba_cases.spl` after the
2026-07-18 `1024`→`3072` fix) is a regression oracle, not a source-of-truth
cross-check — recommend a host-only `logic_rel_drift_check.spl` asserting
`fw_rv32` literals equal `fw/` constants directly, outside the boot-linked
graph.

Full plan: `nvme_fw_rel_rv32_port_plan.md`.

<!-- sdn-diagram:id=rel_rv32_port_gate -->
```
fw/rel_* (unwired) ──[FTL tick wiring]──► fw/rel_* (production) ──►
                                            fw_rv32/logic_rel_*_core.spl
today: ▲ here — self-test-only, port deferred until wired
```
