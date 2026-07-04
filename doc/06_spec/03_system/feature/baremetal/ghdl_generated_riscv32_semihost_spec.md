# Ghdl Generated Riscv32 Semihost Specification

> <details>

<!-- sdn-diagram:id=ghdl_generated_riscv32_semihost_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ghdl_generated_riscv32_semihost_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ghdl_generated_riscv32_semihost_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ghdl_generated_riscv32_semihost_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ghdl Generated Riscv32 Semihost Specification

## Scenarios

### Generated RV32 GHDL semihosting

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
<summary>Advanced: runs hello semihost ELF through the generated core</summary>

#### runs hello semihost ELF through the generated core _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not runner_tools_available():
    return "skip: ghdl or riscv objcopy not available"
val result = run_ghdl_output(HELLO_ELF, 120000)
val output = result[0]
expect(result[1]).to_equal(0)
expect(output).to_contain("Hello, RISC-V 32!")
expect(output).to_contain("SEMIHOST TEST")
expect(output).to_contain("Success")
expect(output).to_contain("Test PASSED")
expect(output).to_contain("Cycles:")
```

</details>


</details>

<details>
<summary>Advanced: runs SPipe semihost ELF through the generated core</summary>

#### runs SPipe semihost ELF through the generated core _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not runner_tools_available():
    return "skip: ghdl or riscv objcopy not available"
val result = run_ghdl_output(SPIPE_ELF, 120000)
val output = result[0]
expect(result[1]).to_equal(0)
expect(output).to_contain("Baremetal Semihosting")
expect(output).to_contain("hello_semihost")
expect(output).to_contain("1 examples, 0 failures")
expect(output).to_contain("Test PASSED")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Generated RV32 GHDL semihosting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
