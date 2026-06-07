# Probe Specification

> <details>

<!-- sdn-diagram:id=probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Probe Specification

## Scenarios

### ProbeConfig construction

#### openocd factory sets fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ProbeConfig.openocd("localhost", 3333, "arm")
expect(cfg.probe_type).to_equal(PROBE_TYPE_OPENOCD)
expect(cfg.host).to_equal("localhost")
expect(cfg.port).to_equal(3333)
expect(cfg.target_arch).to_equal("arm")
```

</details>

#### trace32 factory sets fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = ProbeConfig.trace32("192.168.1.10", 20000, "riscv32")
expect(cfg.probe_type).to_equal(PROBE_TYPE_TRACE32)
expect(cfg.host).to_equal("192.168.1.10")
expect(cfg.port).to_equal(20000)
expect(cfg.target_arch).to_equal("riscv32")
```

</details>

#### probe type constants are distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(PROBE_TYPE_OPENOCD).to_equal(0)
expect(PROBE_TYPE_TRACE32).to_equal(1)
```

</details>

### ARM register names

#### returns 17 registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("arm")
expect(names.len()).to_equal(17)
```

</details>

#### starts with R0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("arm")
expect(names[0]).to_equal("R0")
```

</details>

#### ends with CPSR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("arm")
expect(names[16]).to_equal("CPSR")
```

</details>

#### contains R15

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("arm")
expect(names).to_contain("R15")
```

</details>

### RISC-V register names

#### returns 33 registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("riscv32")
expect(names.len()).to_equal(33)
```

</details>

#### starts with X0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("riscv32")
expect(names[0]).to_equal("X0")
```

</details>

#### ends with PC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("riscv32")
expect(names[32]).to_equal("PC")
```

</details>

#### contains X31

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("riscv32")
expect(names).to_contain("X31")
```

</details>

### x86_64 register names

#### returns 18 registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("x86_64")
expect(names.len()).to_equal(18)
```

</details>

#### starts with RAX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("x86_64")
expect(names[0]).to_equal("RAX")
```

</details>

#### contains RIP

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("x86_64")
expect(names).to_contain("RIP")
```

</details>

#### contains RFLAGS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("x86_64")
expect(names).to_contain("RFLAGS")
```

</details>

### Unknown arch

#### returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = get_t32_register_names("mips")
expect(names.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/realtime/probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ProbeConfig construction
- ARM register names
- RISC-V register names
- x86_64 register names
- Unknown arch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
