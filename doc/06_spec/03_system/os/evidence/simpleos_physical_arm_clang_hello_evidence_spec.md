# Physical ARM SimpleOS Clang hello evidence

> Fails closed until one canonical runner binds the physical board, flashed image, in-guest Clang build, filesystem execution, and retained transcript.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physical ARM SimpleOS Clang hello evidence

Fails closed until one canonical runner binds the physical board, flashed image, in-guest Clang build, filesystem execution, and retained transcript.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/os/evidence/simpleos_physical_arm_clang_hello_evidence_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Fails closed until one canonical runner binds the physical board, flashed
image, in-guest Clang build, filesystem execution, and retained transcript.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Run the resume action shown by the scenario after a canonical physical-board
runner exists. QEMU, host compilation, render-only evidence, or a transcript
without board identity cannot satisfy this contract.

## Scenarios

### REQ-EVS-017 physical ARM SimpleOS Clang hello evidence

#### should fail closed until the canonical board receipt exists

- Capture the physical ARM board Clang hello evidence
- Verify the board compile filesystem execution and transcript boundary
   - Expected: status equals `blocked`
   - Expected: blocker equals `ARM_CLANG_HELLO_BLOCKER`
- Render the exact blocker for operator review
- Publish only the blocked showcase contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the physical ARM board Clang hello evidence")
val status = "blocked"
val blocker = ARM_CLANG_HELLO_BLOCKER

step("Verify the board compile filesystem execution and transcript boundary")
expect(status).to_equal("blocked")
expect(blocker).to_equal(ARM_CLANG_HELLO_BLOCKER)

step("Render the exact blocker for operator review")
expect(blocker).to_contain("guest-clang-fs-run")

step("Publish only the blocked showcase contract")
expect(ARM_CLANG_HELLO_RESUME).to_contain(
    "canonical physical ARM SimpleOS evidence runner"
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
