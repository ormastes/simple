# @manual: primary

> Purpose: Prove that SimpleOS process tool artifact.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that SimpleOS process tool artifact.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/process_tool_artifact_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that SimpleOS process tool artifact.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-001
doc/01_research/local/REQ-OS-001.md
doc/03_plan/sys_test/REQ-OS-001.md
doc/04_architecture/REQ-OS-001.md
doc/05_design/REQ-OS-001.md

## Scenarios

### SimpleOS process tool artifact

#### binds ps to canonical path and bounded list_tasks owner

- Verify: binds ps to canonical path and bounded list_tasks owner
   - Expected: process_tool_canonical_path_v1("ps") equals `/usr/bin/ps`
   - Expected: value.entry_source_owner equals `os.apps.coreutils.ps`
   - Expected: value.source_owner equals `os.tools.proc.ps_tool`
   - Expected: value.max_tasks equals `256`
   - Expected: value.max_args equals `32`
   - Expected: value.help_line equals `usage: ps [-a] [-l] [-p PID]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: binds ps to canonical path and bounded list_tasks owner")
val contract = process_tool_artifact_contract_v1("ps")
expect(contract.is_ok()).to_be(true)
expect(process_tool_canonical_path_v1("ps")).to_equal("/usr/bin/ps")
if val Ok(value) = contract:
    expect(value.entry_source_owner).to_equal("os.apps.coreutils.ps")
    expect(value.source_owner).to_equal("os.tools.proc.ps_tool")
    expect(value.max_tasks).to_equal(256)  # oracle: 256 — named expected value from the requirement
    expect(value.max_args).to_equal(32)  # oracle: 32 — named expected value from the requirement
    expect(value.help_line).to_equal("usage: ps [-a] [-l] [-p PID]")
    expect(process_tool_artifact_contract_valid_v1(value)).to_be(true)
else:
    fail("missing ps contract")
```

</details>

#### rejects unknown commands and stays blocked without loader authority

- Verify: rejects unknown commands and stays blocked without loader authority
   - Expected: result.exit_code equals `126`
   - Expected: result.code equals `PROCESS_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE`
   - Expected: result.canonical_path equals `/usr/bin/ps`
   - Expected: result.artifact_digest equals ``
   - Expected: result.admission_receipt_id equals ``
   - Expected: result.loader_authority_state equals `absent`
   - Expected: unknown.exit_code equals `127`
   - Expected: unknown.code equals `PROCESS_TOOL_COMMAND_UNKNOWN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: rejects unknown commands and stays blocked without loader authority")
expect(process_tool_artifact_contract_v1("top").is_err()).to_be(true)
val result = launcher_dispatch_process_tool_v1("ps", [])
expect(result.exit_code).to_equal(126)  # oracle: 126 — named expected value from the requirement
expect(result.code).to_equal("PROCESS_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE")
expect(result.canonical_path).to_equal("/usr/bin/ps")
expect(result.artifact_digest).to_equal("")
expect(result.admission_receipt_id).to_equal("")
expect(result.loader_authority_state).to_equal("absent")

val unknown = launcher_dispatch_process_tool_v1("not-ps", [])
expect(unknown.exit_code).to_equal(127)  # oracle: 127 — named expected value from the requirement
expect(unknown.code).to_equal("PROCESS_TOOL_COMMAND_UNKNOWN")
expect(unknown.ok).to_be(false)
```

</details>

#### publishes a concrete package identity with an explicit blocker

- Verify: publishes a concrete package identity with an explicit blocker
   - Expected: value.package_name equals `simpleos-process-tools`
   - Expected: value.blocker equals `target-artifact-and-loader-token-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: publishes a concrete package identity with an explicit blocker")
val identity = process_tool_package_identity("ps")
expect(identity.is_ok()).to_be(true)
if val Ok(value) = identity:
    expect(value.package_name).to_equal("simpleos-process-tools")
    expect(value.blocker).to_equal("target-artifact-and-loader-token-unavailable")
    expect(process_tool_package_identity_blocked_v1(value)).to_be(true)
else:
    fail("missing process package identity")
```

</details>

#### returns usage errors before process enumeration for malformed bounded arguments

- Verify: returns usage errors before process enumeration for malformed bounded arguments
   - Expected: run_ps(["-p"]) equals `2`
   - Expected: run_ps(["-p", "not-a-pid"]) equals `2`
   - Expected: run_ps(excessive) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-001
step("Verify: returns usage errors before process enumeration for malformed bounded arguments")
expect(run_ps(["-p"])).to_equal(2)
expect(run_ps(["-p", "not-a-pid"])).to_equal(2)
var excessive: [text] = []
var i = 0
while i < 33:
    excessive.push("-a")
    i = i + 1
expect(run_ps(excessive)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8d05f54a4a80af4b7513d6f674dd18f8d84e61d0bc2f015a825c1cce9024b174`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d05f54a4a80af4b7513d6f674dd18f8d84e61d0bc2f015a825c1cce9024b174`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d05f54a4a80af4b7513d6f674dd18f8d84e61d0bc2f015a825c1cce9024b174`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/process_tool_artifact_contract_spec.spl
mirror: doc/06_spec/01_unit/os/process_tool_artifact_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/process_tool_artifact_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/process_tool_artifact_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/process_tool_artifact_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/process_tool_artifact_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/process_tool_artifact_contract_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds ps to canonical path and bounded list_tasks owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/process_tool_artifact_contract_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown commands and stays blocked without loader authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/process_tool_artifact_contract_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes a concrete package identity with an explicit blocker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
