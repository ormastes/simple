# Mlk S02 100t Assumption Validation Specification

> <details>

<!-- sdn-diagram:id=mlk_s02_100t_assumption_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mlk_s02_100t_assumption_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mlk_s02_100t_assumption_validation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mlk_s02_100t_assumption_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mlk S02 100t Assumption Validation Specification

## Scenarios

### MLK-S02-100T assumption validation campaign

#### locks the launch plan to the assumption-only MLK lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_text("scripts/mlk_s02_100t_assumption_validation.shs")
expect(script).to_contain("scripts/mlk_s02_100t_generated_linux.shs")
expect(script).to_contain("mlk_s02_100t_assumed_unverified.xdc")
expect(script).to_contain("--allow-assumed-board-top")
expect(script).to_contain("--allow-unsafe-assumed-bitstream")
expect(script).to_contain("ARCH_MODE=\"both\"")
expect(script).to_contain("rv32 rv64")
```

</details>

<details>
<summary>Advanced: records the staged matrix and assumption ledger for each arch</summary>

#### records the staged matrix and assumption ledger for each arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_text("scripts/mlk_s02_100t_assumption_validation.shs")
expect(script).to_contain("generated Linux behavioral gate")
expect(script).to_contain("assumption-only synth")
expect(script).to_contain("assumption-only place/route")
expect(script).to_contain("assumption-only bitstream")
expect(script).to_contain("hardware programming")
expect(script).to_contain("UART observation")
expect(script).to_contain("Linux launch attempt")
expect(script).to_contain("Assumption Ledger")
expect(script).to_contain("confirmed by toolchain only")
expect(script).to_contain("confirmed by programming only")
expect(script).to_contain("confirmed by UART/LED hardware behavior")
expect(script).to_contain("still unknown")
```

</details>


</details>

#### keeps linux launch gated behind staged artifacts and a boot delivery command

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = read_text("scripts/mlk_s02_100t_assumption_validation.shs")
expect(script).to_contain("boot delivery command not configured")
expect(script).to_contain("linux_stage_ready()")
expect(script).to_contain("staged_boot_artifact_path")
expect(script).to_contain("--prepare-only --skip-ghdl")
expect(script).to_contain("--skip-ghdl --skip-synth --skip-program")
expect(script).to_contain("assumption-only wrapper ties memory off and drives uart_tx idle-high; Linux boot proof is blocked")
expect(script).to_contain("if [ \"$linux_status\" = \"pass\" ]; then")
```

</details>

#### documents the assumption validation runner in the assumed profile guide

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guide = read_text("doc/07_guide/hardware/mlk_s02_100t_assumed_profile.md")
expect(guide).to_contain("scripts/mlk_s02_100t_assumption_validation.shs")
expect(guide).to_contain("build/fpga/mlk_s02_100t/assumption_validation/")
expect(guide).to_contain("confirmed by UART/LED hardware behavior")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MLK-S02-100T assumption validation campaign

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
