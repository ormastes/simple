# Linux RISC-V QEMU login evidence

> This scenario runs the pinned RV64 Linux QEMU terminal producer only when all live media exists and the operator opts in. Otherwise it publishes an explicit blocker contract. Historical logs, source markers, and fixture transcripts cannot satisfy the live branch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linux RISC-V QEMU login evidence

This scenario runs the pinned RV64 Linux QEMU terminal producer only when all live media exists and the operator opts in. Otherwise it publishes an explicit blocker contract. Historical logs, source markers, and fixture transcripts cannot satisfy the live branch.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/os/evidence/linux_riscv_qemu_login_evidence_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario runs the pinned RV64 Linux QEMU terminal producer only when all
live media exists and the operator opts in. Otherwise it publishes an explicit
blocker contract. Historical logs, source markers, and fixture transcripts
cannot satisfy the live branch.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Build the listed media, set `SIMPLE_EVIDENCE_LINUX_RISCV_LOGIN=1`, and run this
spec. Review the ordered boot, login, and shell transcript; a missing input is
reported with the exact resume command instead of a PASS.

## Scenarios

### REQ-EVS-006/007 Linux RISC-V QEMU login evidence

#### captures a current ordered login transcript or reports its exact blocker

- Capture the feature evidence
- Verify the structured evidence
   - Expected: capture.exit_code equals `0`
   - Expected: capture.transcript_path equals `LINUX_LOG`
   - Expected: checked.diagnostic equals `ok`
   - Expected: checked.first_expected_index equals `-1`
- verify blocker
- Render the evidence for review
- Publish the showcase link


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val missing = prepare_evidence_workspace()
val capture = capture_linux_login_evidence(missing)

step("Verify the structured evidence")
if capture.status == "captured":
    expect(capture.exit_code).to_equal(0)
    expect(capture.transcript_path).to_equal(LINUX_LOG)
    val policy = scenario_text_evidence_policy(
        true,
        true,
        [ScenarioTextMask.version, ScenarioTextMask.duration],
        5000
    )
    val checked = check_text_evidence(
        capture.transcript,
        [
            "login:",
            "UART_TX_INPUT=root",
            "simple-riscv#",
            "UART_TX_INPUT=ls /",
            "SIMPLE_RISCV_LINUX_LOGIN_LS_PASS",
            "RISCV_LINUX_TERMINAL_PROBE_STATUS=PASS",
            "RISCV_QEMU_MEDIA_ORACLE_STATUS=PASS"
        ],
        policy
    )
    expect(checked.diagnostic).to_equal("ok")
    expect(checked.first_expected_index).to_equal(-1)
    expect(checked.normalized_transcript).to_contain(
        "RISCV_QEMU_MEDIA_ORACLE_STATUS=PASS"
    )
else:
    verify_blocker(capture)

step("Render the evidence for review")
val rendered = (
    "status: " + capture.status + "\n" +
    "reason: " + capture.reason + "\n" +
    "resume: " + capture.resume_command
)
expect(rendered).to_contain("status: " + capture.status)
expect(rendered).to_contain(
    "scripts/os/check_riscv_linux_qemu.shs rv64"
)

step("Publish the showcase link")
val publication = publish_scenario_evidence_status(
    "linux.riscv.login",
    ["REQ-EVS-006", "REQ-EVS-007"],
    "test/03_system/os/evidence/linux_riscv_qemu_login_evidence_spec.spl",
    capture.status,
    capture.reason,
    "qemu-riscv64",
    "serial",
    capture.resume_command
).unwrap()
expect(publication).to_equal(
    "build/test-artifacts/03_system/os/evidence/" +
    "linux_riscv_qemu_login_evidence/evidence.sdn"
)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/evidence_showcase.md`
- **Plan:** `doc/03_plan/sys_test/evidence_showcase.md`
- **Design:** `doc/05_design/evidence_showcase.md`
- **Research:** `doc/01_research/local/evidence_showcase.md`


</details>
