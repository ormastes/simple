# Ghdl Generated Riscv32 Mailbox Specification

> <details>

<!-- sdn-diagram:id=ghdl_generated_riscv32_mailbox_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ghdl_generated_riscv32_mailbox_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ghdl_generated_riscv32_mailbox_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ghdl_generated_riscv32_mailbox_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ghdl Generated Riscv32 Mailbox Specification

## Scenarios

### Generated RV32 GHDL mailbox

#### runner script exists and is syntax-valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(GENERATED_MAILBOX_RUNNER)).to_equal(true)
val result = rt_process_run("bash", ["-n", GENERATED_MAILBOX_RUNNER])
expect(result[2]).to_equal(0)
```

</details>

<details>
<summary>Advanced: runs a generated RV32 mailbox shell-contract smoke</summary>

#### runs a generated RV32 mailbox shell-contract smoke _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not runner_tools_available():
    return "skip: ghdl or riscv binutils not available"
val result = rt_process_run_timeout("bash", [GENERATED_MAILBOX_RUNNER, GENERATED_MAILBOX_SMOKE, "--timeout=30"], 120000)
val output = result[0] + result[1]
expect(result[2]).to_equal(0)
expect(output).to_contain("OK")
expect(output).to_contain("RESULT: pass=1 value=42")
expect(output).to_contain("[GHDL-GEN-MB] PASS")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/baremetal/ghdl_generated_riscv32_mailbox_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Generated RV32 GHDL mailbox

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
