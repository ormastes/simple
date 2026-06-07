# UNO Q Adapter Specification

> Verifies `UnoQAdapter` creation, port defaults, OpenOCD argument generation, probe configuration, and `MemoryMap.uno_q()` factory. Does NOT test live OpenOCD connectivity (gated by D-6: requires external probe).

<!-- sdn-diagram:id=adapter_uno_q_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adapter_uno_q_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adapter_uno_q_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adapter_uno_q_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UNO Q Adapter Specification

Verifies `UnoQAdapter` creation, port defaults, OpenOCD argument generation, probe configuration, and `MemoryMap.uno_q()` factory. Does NOT test live OpenOCD connectivity (gated by D-6: requires external probe).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UNOQ-PORT |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/debug/remote/exec/adapter_uno_q_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies `UnoQAdapter` creation, port defaults, OpenOCD argument generation,
probe configuration, and `MemoryMap.uno_q()` factory. Does NOT test live
OpenOCD connectivity (gated by D-6: requires external probe).

## Behavior

- Default ports: GDB 27333, telnet 27444, TCL 27666 (no collision with H7/R4)
- Default probe: `interface/stlink.cfg`
- OpenOCD args include `target/stm32u5x.cfg` and the probe config
- `MemoryMap.uno_q()` has SRAM1-only conservative layout (D-5)
- Adapter starts disconnected

## Scenarios

### UnoQAdapter port defaults

#### AC-3: default gdb port is 27333

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = default_uno_q_gdb_port()
expect(port).to_equal(27333)
```

</details>

#### AC-3: default telnet port is 27444

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = default_uno_q_telnet_port()
expect(port).to_equal(27444)
```

</details>

#### AC-3: default tcl port is 27666

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = default_uno_q_tcl_port()
expect(port).to_equal(27666)
```

</details>

### UnoQAdapter openocd args

#### AC-3: openocd args contain stm32u5x.cfg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = uno_q_openocd_args("interface/stlink.cfg")
expect(args).to_contain("stm32u5x.cfg")
```

</details>

#### AC-3: openocd args contain probe config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = uno_q_openocd_args("interface/stlink.cfg")
expect(args).to_contain("interface/stlink.cfg")
```

</details>

#### AC-3: openocd args with jlink probe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = uno_q_openocd_args("interface/jlink.cfg")
expect(args).to_contain("interface/jlink.cfg")
```

</details>

### UnoQAdapter construction

#### AC-3: new() has gdb_port 27333

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = UnoQAdapter.new()
expect(adapter.gdb_port).to_equal(27333)
```

</details>

#### AC-3: new() starts disconnected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = UnoQAdapter.new()
expect(adapter.connected).to_equal(false)
```

</details>

#### AC-3: new() has default stlink probe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = UnoQAdapter.new()
expect(adapter.probe_cfg).to_equal("interface/stlink.cfg")
```

</details>

#### AC-3: with_probe overrides probe_cfg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = UnoQAdapter.with_probe("interface/cmsis-dap.cfg")
expect(adapter.probe_cfg).to_equal("interface/cmsis-dap.cfg")
```

</details>

#### AC-3: with_ports overrides gdb_port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = UnoQAdapter.with_ports(9999, 9998)
expect(adapter.gdb_port).to_equal(9999)
```

</details>

#### AC-3: with_ports overrides telnet_port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = UnoQAdapter.with_ports(9999, 9998)
expect(adapter.telnet_port).to_equal(9998)
```

</details>

### MemoryMap uno_q

#### AC-3: code_start is 0x20002000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mm = MemoryMap.uno_q()
expect(mm.code_start).to_equal(0x20002000)
```

</details>

#### AC-3: code_end is 0x20020000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mm = MemoryMap.uno_q()
expect(mm.code_end).to_equal(0x20020000)
```

</details>

#### AC-3: data_start is 0x20020000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mm = MemoryMap.uno_q()
expect(mm.data_start).to_equal(0x20020000)
```

</details>

#### AC-3: data_end is 0x2002E000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mm = MemoryMap.uno_q()
expect(mm.data_end).to_equal(0x2002E000)
```

</details>

#### AC-3: stack_top is 0x20030000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mm = MemoryMap.uno_q()
expect(mm.stack_top).to_equal(0x20030000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
