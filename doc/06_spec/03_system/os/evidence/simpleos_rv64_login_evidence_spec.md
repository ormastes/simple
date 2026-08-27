# SimpleOS RV64 QEMU login evidence

> This scenario invokes the production serial-shell runner only with an explicit live opt-in and a current kernel. Its independent ordered oracle requires a post-password shell prompt and real command responses. Echoed commands, source markers, historical logs, and the runner's current permissive exit cannot produce a login PASS.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS RV64 QEMU login evidence

This scenario invokes the production serial-shell runner only with an explicit live opt-in and a current kernel. Its independent ordered oracle requires a post-password shell prompt and real command responses. Echoed commands, source markers, historical logs, and the runner's current permissive exit cannot produce a login PASS.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/os/evidence/simpleos_rv64_login_evidence_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario invokes the production serial-shell runner only with an explicit
live opt-in and a current kernel. Its independent ordered oracle requires a
post-password shell prompt and real command responses. Echoed commands, source
markers, historical logs, and the runner's current permissive exit cannot
produce a login PASS.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Build the RV64 kernel, set `SIMPLE_EVIDENCE_SIMPLEOS_RV64_LOGIN=1`, and run this
spec. Review the ordered boot, password, prompt, and command-response transcript;
missing live inputs remain explicit blockers.

## Scenarios

### REQ-EVS-006/007 SimpleOS RV64 QEMU login evidence

#### captures ordered login and shell responses or reports its exact blocker

- Capture the feature evidence
- Verify the structured evidence
   - Expected: capture.transcript_path equals `SIMPLEOS_LOG`
- "SimpleOS RV64
   - Expected: checked.diagnostic equals `ok`
   - Expected: checked.first_expected_index equals `-1`
- "SimpleOS RV64
- verify blocker
- Render the evidence for review
- Publish the showcase link


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val missing = prepare_evidence_workspace()
val capture = capture_simpleos_login_evidence(missing)

step("Verify the structured evidence")
if capture.status == "captured":
    expect(capture.transcript_path).to_equal(SIMPLEOS_LOG)
    val policy = scenario_text_evidence_policy(
        true,
        true,
        [ScenarioTextMask.address, ScenarioTextMask.duration],
        40
    )
    val checked = check_text_evidence(
        capture.transcript,
        [
            "SimpleOS RV64 serial console - network unavailable, UART management active.",
            "Type 'help' for commands.",
            "login: root",
            "password-field:",
            "simpleos-rv64> ls",
            "SYS",
            "simpleos-rv64> info",
            "SimpleOS RV64 (riscv64) - serial console fallback",
            "simpleos-rv64> launch /sys/apps/clang --version"
        ],
        policy
    )
    expect(checked.diagnostic).to_equal("ok")
    expect(checked.first_expected_index).to_equal(-1)
    expect(checked.normalized_transcript).to_contain(
        "launched /sys/apps/clang pid="
    )
    expect(checked.normalized_transcript).to_contain(
        "SimpleOS RV64 (riscv64) - serial console fallback"
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
    "test/03_system/os/evidence/simpleos_rv64_login_evidence_spec.spl"
)

step("Publish the showcase link")
val publication = publish_scenario_evidence_status(
    "simpleos.riscv.login",
    ["REQ-EVS-006", "REQ-EVS-007"],
    "test/03_system/os/evidence/simpleos_rv64_login_evidence_spec.spl",
    capture.status,
    capture.reason,
    "qemu-riscv64",
    "serial-shell",
    capture.resume_command
).unwrap()
expect(publication).to_equal(
    "build/test-artifacts/03_system/os/evidence/" +
    "simpleos_rv64_login_evidence/evidence.sdn"
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
