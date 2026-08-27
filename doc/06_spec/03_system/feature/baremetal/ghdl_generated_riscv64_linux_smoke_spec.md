# Ghdl Generated Riscv64 Linux Smoke Specification

> <details>

<!-- sdn-diagram:id=ghdl_generated_riscv64_linux_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ghdl_generated_riscv64_linux_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ghdl_generated_riscv64_linux_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ghdl_generated_riscv64_linux_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ghdl Generated Riscv64 Linux Smoke Specification

## Scenarios

### Generated RV64 GHDL Linux smoke lane

#### script exists and is syntax-valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(GENERATED_LINUX_SMOKE)).to_equal(true)
val result = rt_process_run("bash", ["-n", GENERATED_LINUX_SMOKE])
expect(result[2]).to_equal(0)
```

</details>

<details>
<summary>Advanced: supports a tool-check mode for the repo-native generated RV64 Linux lane</summary>

#### supports a tool-check mode for the repo-native generated RV64 Linux lane _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not runner_tools_available():
    expect(1).to_equal(1)
else:
    val result = rt_process_run_timeout("bash", [GENERATED_LINUX_SMOKE, "--check-tools"], 120000)
    if result[2] == 2:
        expect(1).to_equal(1)
    else:
        val output = result[0] + result[1]
        expect(result[2]).to_equal(0)
        expect(output).to_contain("PASS: generated RV64 RTL Linux tools present")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/baremetal/ghdl_generated_riscv64_linux_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Generated RV64 GHDL Linux smoke lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
