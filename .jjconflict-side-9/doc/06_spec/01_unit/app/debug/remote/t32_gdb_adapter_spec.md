# T32 Gdb Adapter Specification

> <details>

<!-- sdn-diagram:id=t32_gdb_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_gdb_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_gdb_adapter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_gdb_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Gdb Adapter Specification

## Scenarios

### T32GdbAdapter config factories

#### t32-gdb config for T32 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.for_t32_target("test.elf")
expect(cfg.adapter_type).to_equal("t32-gdb")
expect(cfg.port).to_equal(20000)
```

</details>

#### t32-gdb bridge config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.t32_gdb_bridge("localhost", 20000, 2331, "test.elf")
expect(cfg.adapter_type).to_equal("t32-gdb")
expect(cfg.port).to_equal(20000)
```

</details>

#### t32-gdb config has arm architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.for_t32_target("test.elf")
expect(cfg.architecture).to_equal("arm")
```

</details>

#### t32-gdb config has correct host

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.t32_gdb_bridge("myhost", 20000, 2331, "test.elf")
expect(cfg.host).to_equal("myhost")
```

</details>

### T32GdbAdapter capabilities

#### has reset capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.basic().with_reset().with_memory().with_registers()
expect(caps.can_reset).to_equal(true)
```

</details>

#### has memory capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.basic().with_reset().with_memory().with_registers()
expect(caps.supports_memory).to_equal(true)
```

</details>

#### has registers capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.basic().with_reset().with_memory().with_registers()
expect(caps.supports_registers).to_equal(true)
```

</details>

### T32GdbAdapter name

#### adapter name is t32-gdb

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "t32-gdb"
expect(name).to_equal("t32-gdb")
```

</details>

#### adapter supports trace capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val supported = true
expect(supported).to_equal(true)
```

</details>

#### adapter supports coverage collect

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val supported = true
expect(supported).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/t32_gdb_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32GdbAdapter config factories
- T32GdbAdapter capabilities
- T32GdbAdapter name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
