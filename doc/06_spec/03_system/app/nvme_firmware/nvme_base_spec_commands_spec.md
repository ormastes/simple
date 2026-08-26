# nvme_base_spec_commands_spec

> Runs the host controller lifecycle and rv32-compatible scalar firmware command floor through the selected self-hosted Simple runtime. This is command-semantic evidence, not RV32 ELF boot or physical OpenSSD evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_base_spec_commands_spec

Runs the host controller lifecycle and rv32-compatible scalar firmware command floor through the selected self-hosted Simple runtime. This is command-semantic evidence, not RV32 ELF boot or physical OpenSSD evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/nvme_base_spec_commands.md |
| Plan | doc/03_plan/sys_test/nvme_base_spec_commands.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl` |
| Updated | 2026-07-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the host controller lifecycle and rv32-compatible scalar firmware command
floor through the selected self-hosted Simple runtime. This is command-semantic
evidence, not RV32 ELF boot or physical OpenSSD evidence.

The scenarios cover the required controller and namespace Identify data, legal
and illegal queue lifecycle transitions, NVM command families, admin command
guards, reserved fields, Abort, and backpressure. A separate scenario proves a
missing runtime cannot produce passing evidence.

## Syntax

Set `NVME_RV32_SIMPLE_BIN` to the self-hosted Simple executable, then run this
file through `simple test --mode=interpreter`.

## Examples

`NVME_RV32_SIMPLE_BIN=build/bootstrap/full/x86_64-unknown-linux-gnu/simple simple test test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl --mode=interpreter`

## Claim Boundary

Passing proves the host model and scalar firmware command floor. It does not
prove a freshly linked RV32 ELF, QEMU boot, OpenSSD ARM/Zynq execution, NAND
media behavior, PCIe interoperability, or power-loss durability.

## Scenarios

### NVMe base-spec command floor

#### should identify the controller and enforce IO queue lifecycle rules

- Run the host-facing controller lifecycle demo
   - Expected: code equals `0`
- Verify Identify Controller and Identify Namespace results
- Verify legal queue order and invalid binding rejection
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the host-facing controller lifecycle demo")
val (out, err, code) = _run_simple(FW + "/nvme_main.spl")
expect(code).to_equal(0)

step("Verify Identify Controller and Identify Namespace results")
expect(out).to_contain("identify controller ok")
expect(out).to_contain("controller reports max IO queues")
expect(out).to_contain("namespace size == LBA_COUNT")

step("Verify legal queue order and invalid binding rejection")
expect(out).to_contain("create IO CQ 1")
expect(out).to_contain("create IO SQ 1 -> CQ 1")
expect(out).to_contain("SQ -> missing CQ rejected")
expect(out).to_contain("delete bound CQ rejected")
expect(out).to_contain("delete SQ 1 ok")
expect(out).to_contain("delete CQ 1 ok")
_expect_no_fail_marker(out, "host controller lifecycle")
```

</details>

#### should pass the rv32-compatible admin and NVM command floor

- Run the scalar firmware command checker
   - Expected: code equals `0`
- Verify admin, queue, opcode, and NVM command families
- Verify reserved-field, namespace, Abort, and backpressure guards
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the scalar firmware command checker")
val (out, err, code) = _run_simple(RV32 + "/base_spec_check.spl")
expect(code).to_equal(0)

step("Verify admin, queue, opcode, and NVM command families")
expect(out).to_contain("NVME-ADMIN-IDENTIFY-FEATURES-LOG-FORMAT-FW PASS")
expect(out).to_contain("NVME-QUEUE-PHASE-CREATE-DELETE PASS")
expect(out).to_contain("NVME-HIL-OPCODE-BOUNDS PASS")
expect(out).to_contain("NVME-NVM-READ-WRITE-ZEROES-DSM-TRIM PASS")
expect(out).to_contain("NVME-NVM-FLUSH PASS")

step("Verify reserved-field, namespace, Abort, and backpressure guards")
expect(out).to_contain("NVME-FEATURE-RESERVED-FIELD-GUARD PASS")
expect(out).to_contain("NVME-NAMESPACE-RESERVED-FIELD-GUARD PASS")
expect(out).to_contain("NVME-ABORT-BACKPRESSURE PASS")
expect(out).to_contain("NVME BASE SPEC CHECKS PASS")
_expect_no_fail_marker(out, "rv32 command floor")
```

</details>

#### should fail closed when the selected Simple runtime is missing

- Select a runtime path that cannot exist
- Verify the missing runtime cannot produce passing evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select a runtime path that cannot exist")
val (out, err, code) = _run("NVME_RV32_SIMPLE_BIN=/definitely/missing/simple; \"$NVME_RV32_SIMPLE_BIN\" run " + RV32 + "/base_spec_check.spl")

step("Verify the missing runtime cannot produce passing evidence")
expect(code).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/nvme_base_spec_commands.md`
- **Plan:** `doc/03_plan/sys_test/nvme_base_spec_commands.md`
- **Research:** `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`


</details>
