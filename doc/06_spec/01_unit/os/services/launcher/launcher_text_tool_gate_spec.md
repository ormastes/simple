# Launcher Text Tool Gate Specification

> Tests covering launcher text tool artifact gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Launcher Text Tool Gate Specification

## Scenarios

### launcher text tool artifact gate

#### fails closed without an admitted grep artifact token

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails closed without an admitted grep artifact token
   - Expected: result.exit_code equals `LAUNCHER_TEXT_TOOL_BLOCKED`
   - Expected: result.code equals `TEXT_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE`
   - Expected: result.canonical_path equals `/usr/bin/grep`
   - Expected: result.artifact_digest equals ``
   - Expected: result.admission_receipt_id equals ``
   - Expected: result.loader_authority_state equals `absent`
   - Expected: result.pid equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed without an admitted grep artifact token")
val result = launcher_dispatch_text_tool_v1("grep", ["--version"])
expect(result.ok).to_be(false)
expect(result.exit_code).to_equal(LAUNCHER_TEXT_TOOL_BLOCKED)
expect(result.code).to_equal("TEXT_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE")
expect(result.canonical_path).to_equal("/usr/bin/grep")
expect(result.artifact_digest).to_equal("")
expect(result.admission_receipt_id).to_equal("")
expect(result.loader_authority_state).to_equal("absent")
expect(result.pid).to_equal(-1)
```

</details>

#### rejects unknown text tool identities

- rejects unknown text tool identities
   - Expected: result.exit_code equals `LAUNCHER_TEXT_TOOL_UNKNOWN`
   - Expected: result.canonical_path equals ``
   - Expected: result.loader_authority_state equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects unknown text tool identities")
val result = launcher_dispatch_text_tool_v1("sed", [])
expect(result.ok).to_be(false)
expect(result.exit_code).to_equal(LAUNCHER_TEXT_TOOL_UNKNOWN)
expect(result.canonical_path).to_equal("")
expect(result.loader_authority_state).to_equal("absent")
```

</details>

#### does not parse operands before loader admission

- does not parse operands before loader admission
   - Expected: result.exit_code equals `LAUNCHER_TEXT_TOOL_BLOCKED`
   - Expected: result.code equals `TEXT_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not parse operands before loader admission")
var args: [text] = ["needle"]
var i = 0
while i < 130:
    args = args.push("file-{i}")
    i = i + 1
val result = launcher_dispatch_text_tool_v1("grep", args)
expect(result.ok).to_be(false)
expect(result.exit_code).to_equal(LAUNCHER_TEXT_TOOL_BLOCKED)
expect(result.code).to_equal("TEXT_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/launcher/launcher_text_tool_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering launcher text tool artifact gate.
- launcher text tool artifact gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a183c662100b0653235e49121bfae12fa55af2d6cc0fff07f1e7c832860e3587`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a183c662100b0653235e49121bfae12fa55af2d6cc0fff07f1e7c832860e3587`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a183c662100b0653235e49121bfae12fa55af2d6cc0fff07f1e7c832860e3587`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/services/launcher/launcher_text_tool_gate_spec.spl
mirror: doc/06_spec/01_unit/os/services/launcher/launcher_text_tool_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/launcher/launcher_text_tool_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/launcher/launcher_text_tool_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/launcher/launcher_text_tool_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/launcher/launcher_text_tool_gate_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed without an admitted grep artifact token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/launcher/launcher_text_tool_gate_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown text tool identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/launcher/launcher_text_tool_gate_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not parse operands before loader admission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
