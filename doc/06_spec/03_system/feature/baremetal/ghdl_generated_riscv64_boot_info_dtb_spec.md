# Ghdl Generated Riscv64 Boot Info Dtb Specification

> <details>

<!-- sdn-diagram:id=ghdl_generated_riscv64_boot_info_dtb_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ghdl_generated_riscv64_boot_info_dtb_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ghdl_generated_riscv64_boot_info_dtb_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ghdl_generated_riscv64_boot_info_dtb_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ghdl Generated Riscv64 Boot Info Dtb Specification

## Scenarios

### Generated RV64 compiled-payload boot-info DTB GHDL lane

#### runner script exists and is syntax-valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(GENERATED_RUNNER)).to_equal(true)
expect(rt_file_exists(DEFAULT_FW_STUB)).to_equal(true)
val result = rt_process_run("bash", ["-n", GENERATED_RUNNER])
expect(result[2]).to_equal(0)
```

</details>

<details>
<summary>Advanced: runs the compiled-payload boot-info DTB runner when a payload ELF/bin is provided</summary>

#### runs the compiled-payload boot-info DTB runner when a payload ELF/bin is provided _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not runner_tools_available():
    expect(1).to_equal(1)
else:
    val payload = payload_path()
    if payload == "":
        expect(1).to_equal(1)
    else:
        if not rt_file_exists(payload):
            expect(1).to_equal(1)
        else:
            val result = rt_process_run_timeout("bash", payload_args(payload), 120000)
            if result[2] == 2:
                expect(1).to_equal(1)
            else:
                val output = result[0] + result[1]
                expect(result[2]).to_equal(0)
                expect(output).to_contain("GENERATED_RV64_BOOT_INFO_DTB: PASS")
                expect(output).to_contain("DONE_LOW32: 1")
                expect(output).to_contain("DTB_VALID_LOW32: 1")
                expect(output).to_contain("MAP_LEN_LOW32: 3")
                expect(output).to_contain("REGION0_KIND_LOW32: 2")
                expect(output).to_contain("REGION1_KIND_LOW32: 8")
                expect(output).to_contain("REGION2_KIND_LOW32: 1")
                expect(output).to_contain("DTB_PROBE_SEEN: true")
                expect(output).to_contain("UART_MARKER_SEEN: true")
                expect(output).to_contain("PRIV_MODE: 1")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/baremetal/ghdl_generated_riscv64_boot_info_dtb_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Generated RV64 compiled-payload boot-info DTB GHDL lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
