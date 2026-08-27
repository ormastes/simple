# Replay Vm Facade Specification

> Tests covering gc_async_mut replay VM facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Vm Facade Specification

## Scenarios

### gc_async_mut replay VM facades

#### re-exports VM config and device kind helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports VM config and device kind helpers
   - Expected: cfg.memory_mb equals `0`
   - Expected: cfg.replay_mode.to_text() equals `live`
   - Expected: DeviceIoKind.Interrupt.to_i32() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports VM config and device kind helpers")
val cfg = VmConfig.default_rv32(0)

expect(cfg.memory_mb).to_equal(0)
expect(cfg.replay_mode.to_text()).to_equal("live")
expect(DeviceIoKind.Interrupt.to_i32()).to_equal(2)
```

</details>

#### re-exports virtual timer and serial devices

- re-exports virtual timer and serial devices
   - Expected: timer.pending_irq() equals `7`
   - Expected: serial.tx_buffer[0] equals `0x41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports virtual timer and serial devices")
var timer = VirtualTimer.create("timer0", 7)
timer.mmio_write(0x14, 1, 4)
timer.mmio_write(0x08, 10, 4)
timer.tick(10)

var serial = VirtualSerial.create("uart0", 10)
serial.mmio_write(0x00, 0x41, 1)

expect(timer.pending_irq()).to_equal(7)
expect(serial.tx_buffer[0]).to_equal(0x41)
```

</details>

#### re-exports replay driver

- re-exports replay driver
   - Expected: driver.get_cycle_count() equals `0`
   - Expected: driver.io_event_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports replay driver")
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)

expect(driver.get_cycle_count()).to_equal(0)
expect(driver.io_event_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/replay/vm/replay_vm_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut replay VM facades.
- gc_async_mut replay VM facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e7a6eeb776c1f4d8e216f7b0e5f4a4f6ff790af5708550b46d0880368f3aaea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e7a6eeb776c1f4d8e216f7b0e5f4a4f6ff790af5708550b46d0880368f3aaea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e7a6eeb776c1f4d8e216f7b0e5f4a4f6ff790af5708550b46d0880368f3aaea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/replay/vm/replay_vm_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/replay/vm/replay_vm_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/replay/vm/replay_vm_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/replay/vm/replay_vm_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/replay/vm/replay_vm_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/replay/vm/replay_vm_facade_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports VM config and device kind helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/replay/vm/replay_vm_facade_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports virtual timer and serial devices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/replay/vm/replay_vm_facade_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports replay driver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
