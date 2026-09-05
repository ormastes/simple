# Simpleos Arm64 Server Receipt Parser Specification

> Tests covering SimpleOsServerExecutionReceiptV1 parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Arm64 Server Receipt Parser Specification

## Scenarios

### SimpleOsServerExecutionReceiptV1 parser

#### should accept complete byte and reboot evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should accept complete byte and reboot evidence
   - Expected: parsed.is_ok() is true
   - Expected: parsed.unwrap().http_file_verified is true
   - Expected: parsed.unwrap().db_reboot_verified is true
   - Expected: parsed.unwrap().target_credential_zeroization_verified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should accept complete byte and reboot evidence")
val parsed = parse_simpleos_server_execution_receipt_v1(valid_arm_server_receipt())
expect(parsed.is_ok()).to_equal(true)
expect(parsed.unwrap().http_file_verified).to_equal(true)
expect(parsed.unwrap().db_reboot_verified).to_equal(true)
expect(parsed.unwrap().target_credential_zeroization_verified).to_equal(true)
```

</details>

#### should reject a substituted HTTP body hash

- should reject a substituted HTTP body hash
   - Expected: parse_simpleos_server_execution_receipt_v1(forged).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject a substituted HTTP body hash")
val forged = valid_arm_server_receipt().replace(
    "http_observed_sha256=772260f72b55b342bf50c825f6793df48ff4cc292c4dd966394b390f10393594",
    "http_observed_sha256=1123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")
expect(parse_simpleos_server_execution_receipt_v1(forged).is_err()).to_equal(true)
```

</details>

#### should reject missing fresh-process shutdown evidence

- should reject missing fresh-process shutdown evidence
   - Expected: parse_simpleos_server_execution_receipt_v1(forged).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject missing fresh-process shutdown evidence")
val forged = valid_arm_server_receipt().replace(
    "fresh_qemu_processes=2", "fresh_qemu_processes=1")
expect(parse_simpleos_server_execution_receipt_v1(forged).is_err()).to_equal(true)
```

</details>

#### should reject duplicate receipt fields

- should reject duplicate receipt fields
   - Expected: parse_simpleos_server_execution_receipt_v1(forged).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject duplicate receipt fields")
val forged = valid_arm_server_receipt() + "mode=qemu-arm64-cpu\n"
expect(parse_simpleos_server_execution_receipt_v1(forged).is_err()).to_equal(true)
```

</details>

#### should reject an unverified target credential wipe

- should reject an unverified target credential wipe
   - Expected: parse_simpleos_server_execution_receipt_v1(forged).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject an unverified target credential wipe")
val forged = valid_arm_server_receipt().replace(
    "target_credential_zeroization=verified",
    "target_credential_zeroization=unverified")
expect(parse_simpleos_server_execution_receipt_v1(forged).is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOsServerExecutionReceiptV1 parser.
- SimpleOsServerExecutionReceiptV1 parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `f53768ed96315ed27fa273e041057d14e9e4c5a4be99325cf295a113bb0d45de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f53768ed96315ed27fa273e041057d14e9e4c5a4be99325cf295a113bb0d45de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f53768ed96315ed27fa273e041057d14e9e4c5a4be99325cf295a113bb0d45de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl
mirror: doc/06_spec/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept complete byte and reboot evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept complete byte and reboot evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a substituted HTTP body hash' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a substituted HTTP body hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing fresh-process shutdown evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing fresh-process shutdown evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl:93:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject duplicate receipt fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/server/simpleos_arm64_server_receipt_parser_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an unverified target credential wipe' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
