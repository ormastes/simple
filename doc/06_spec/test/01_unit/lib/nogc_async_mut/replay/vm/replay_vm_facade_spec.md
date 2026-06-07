# Replay Vm Facade Specification

> <details>

<!-- sdn-diagram:id=replay_vm_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_vm_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_vm_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_vm_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Vm Facade Specification

## Scenarios

### nogc_async_mut replay VM facades

#### re-exports VM config and device kind helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)

expect(cfg.memory_mb).to_equal(0)
expect(cfg.replay_mode.to_text()).to_equal("live")
expect(DeviceIoKind.Interrupt.to_i32()).to_equal(2)
```

</details>

#### re-exports virtual timer and serial devices

1. var timer = VirtualTimer create
2. timer mmio write
3. timer mmio write
4. timer tick
5. var serial = VirtualSerial create
6. serial mmio write
   - Expected: timer.pending_irq() equals `7`
   - Expected: serial.tx_buffer[0] equals `0x41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var driver = VmReplayDriver create
   - Expected: driver.get_cycle_count() equals `0`
   - Expected: driver.io_event_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/nogc_async_mut/replay/vm/replay_vm_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut replay VM facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
