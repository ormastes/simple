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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should identify the controller and enforce IO queue lifecycle rules
- Run the host-facing controller lifecycle demo
   - Expected: code equals `0`
- Verify Identify Controller and Identify Namespace results
- Verify legal queue order and invalid binding rejection
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should identify the controller and enforce IO queue lifecycle rules")
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

- should pass the rv32-compatible admin and NVM command floor
- Run the scalar firmware command checker
   - Expected: code equals `0`
- Verify admin, queue, opcode, and NVM command families
- Verify reserved-field, namespace, Abort, and backpressure guards
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should pass the rv32-compatible admin and NVM command floor")
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

- should fail closed when the selected Simple runtime is missing
- Select a runtime path that cannot exist
- Verify the missing runtime cannot produce passing evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed when the selected Simple runtime is missing")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dbcd847be3ccb7f745e4881e37e751b75a6e73a45e09a5e2c777939598270ba6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dbcd847be3ccb7f745e4881e37e751b75a6e73a45e09a5e2c777939598270ba6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dbcd847be3ccb7f745e4881e37e751b75a6e73a45e09a5e2c777939598270ba6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=85 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should identify the controller and enforce IO queue lifecycle rules' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should identify the controller and enforce IO queue lifecycle rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pass the rv32-compatible admin and NVM command floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pass the rv32-compatible admin and NVM command floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:104:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed when the selected Simple runtime is missing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed when the selected Simple runtime is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
