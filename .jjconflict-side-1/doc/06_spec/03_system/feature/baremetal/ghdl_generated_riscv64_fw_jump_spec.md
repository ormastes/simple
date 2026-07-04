# Ghdl Generated Riscv64 Fw Jump Specification

> <details>

<!-- sdn-diagram:id=ghdl_generated_riscv64_fw_jump_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ghdl_generated_riscv64_fw_jump_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ghdl_generated_riscv64_fw_jump_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ghdl_generated_riscv64_fw_jump_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ghdl Generated Riscv64 Fw Jump Specification

## Scenarios

### Generated RV64 FW_JUMP GHDL smoke

#### runner script exists and is syntax-valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(GENERATED_RUNNER)).to_equal(true)
val result = rt_process_run("bash", ["-n", GENERATED_RUNNER])
expect(result[2]).to_equal(0)
```

</details>

<details>
<summary>Advanced: runs a generated RV64 FW_JUMP smoke program</summary>

#### runs a generated RV64 FW_JUMP smoke program _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not runner_tools_available():
    expect(1).to_equal(1)
else:
    val result = rt_process_run_timeout("bash", [GENERATED_RUNNER, GENERATED_SMOKE, "--timeout=30"], 120000)
    if result[2] == 2:
        expect(1).to_equal(1)
    else:
        val output = result[0] + result[1]
        expect(result[2]).to_equal(0)
        expect(output).to_contain("GENERATED_RV64_FW_JUMP: PASS")
        expect(output).to_contain("PASS_WORD: 42")
        expect(output).to_contain("PRIV_MODE: 1")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/baremetal/ghdl_generated_riscv64_fw_jump_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Generated RV64 FW_JUMP GHDL smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
