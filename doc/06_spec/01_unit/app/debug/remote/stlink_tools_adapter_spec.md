# Stlink Tools Adapter Specification

> <details>

<!-- sdn-diagram:id=stlink_tools_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stlink_tools_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stlink_tools_adapter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stlink_tools_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stlink Tools Adapter Specification

## Scenarios

### StLinkToolsAdapter config factories

#### stlink-tools config for STM32H7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.stlink_tools("002600213137510833333639", "test.bin")
expect(cfg.adapter_type).to_equal("stlink-tools")
expect(cfg.architecture).to_equal("002600213137510833333639")
```

</details>

#### stlink-tools config for STM32WB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.stlink_tools("0671FF555755846687041216", "test.bin")
expect(cfg.architecture).to_equal("0671FF555755846687041216")
```

</details>

#### stlink-tools config has no host

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.stlink_tools("serial", "test.bin")
expect(cfg.host).to_equal("")
```

</details>

#### stlink-tools config has port 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.stlink_tools("serial", "test.bin")
expect(cfg.port).to_equal(0)
```

</details>

### StLinkToolsAdapter capabilities

#### has reset capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = MockStLinkAdapter.create()
expect(adapter.can_reset()).to_equal(true)
```

</details>

#### has memory capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = MockStLinkAdapter.create()
expect(adapter.can_read_memory()).to_equal(true)
```

</details>

#### does NOT have halt capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = MockStLinkAdapter.create()
expect(adapter.can_halt()).to_equal(false)
```

</details>

#### does NOT have step capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = MockStLinkAdapter.create()
expect(adapter.can_step()).to_equal(false)
```

</details>

#### does NOT have breakpoint capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = MockStLinkAdapter.create()
expect(adapter.can_set_breakpoint()).to_equal(false)
```

</details>

#### does NOT have register capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = MockStLinkAdapter.create()
expect(adapter.can_read_registers()).to_equal(false)
```

</details>

### StLinkToolsAdapter name

#### adapter name is stlink-tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = MockStLinkAdapter.create()
expect(adapter.name()).to_equal("stlink-tools")
```

</details>

#### adapter is attached after creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = MockStLinkAdapter.create()
expect(adapter.is_attached()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/stlink_tools_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StLinkToolsAdapter config factories
- StLinkToolsAdapter capabilities
- StLinkToolsAdapter name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
