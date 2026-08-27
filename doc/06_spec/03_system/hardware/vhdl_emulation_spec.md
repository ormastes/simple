# Vhdl Emulation Specification

> <details>

<!-- sdn-diagram:id=vhdl_emulation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_emulation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_emulation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_emulation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Emulation Specification

## Scenarios

### VHDL emulation portable smoke

#### records simulator phases

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phases = ["elaborate", "simulate", "compare"]
expect(phases.len()).to_equal(3)
expect(phases[1]).to_equal("simulate")
```

</details>

#### records signal value shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val signal_name = "clk"
val value = "1"
expect(signal_name).to_equal("clk")
expect(value).to_equal("1")
```

</details>

#### records backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = "vhdl"
expect(backend).to_equal("vhdl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/vhdl_emulation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VHDL emulation portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
