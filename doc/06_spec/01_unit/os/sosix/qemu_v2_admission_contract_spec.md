# Qemu V2 Admission Contract Specification

> Tests covering SOSIX QEMU v2 structural admission contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu V2 Admission Contract Specification

## Scenarios

### SOSIX QEMU v2 structural admission contract

#### accepts the closed direct-kernel eight-artifact record without granting trust

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts the closed direct-kernel eight-artifact record without granting trust
   - Expected: parsed.receipt.artifact_count equals `8`
   - Expected: parsed.reason equals `collector-v2-record-structurally-valid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts the closed direct-kernel eight-artifact record without granting trust")
val parsed = sosix_qemu_v2_structural_admission_parse(_v2_admission_record())
expect(parsed.structurally_valid).to_be(true)
expect(parsed.receipt.artifact_count).to_equal(8)
expect(parsed.reason).to_equal("collector-v2-record-structurally-valid")
```

</details>

#### rejects missing, reordered, duplicated, and unknown record fields

- rejects missing, reordered, duplicated, and unknown record fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects missing, reordered, duplicated, and unknown record fields")
val record = _v2_admission_record()
expect(sosix_qemu_v2_structural_admission_parse(
    record.replace("firmware_path=none\n", "")).structurally_valid).to_be(false)
expect(sosix_qemu_v2_structural_admission_parse(
    record.replace("status=pass\nevidence_sha256=", "evidence_sha256=") +
    "status=pass\n").structurally_valid).to_be(false)
expect(sosix_qemu_v2_structural_admission_parse(
    record + "status=pass\n").structurally_valid).to_be(false)
expect(sosix_qemu_v2_structural_admission_parse(
    record + "verified=true\n").structurally_valid).to_be(false)
```

</details>

#### rejects noncanonical counts and false direct-kernel firmware claims

- rejects noncanonical counts and false direct-kernel firmware claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects noncanonical counts and false direct-kernel firmware claims")
val record = _v2_admission_record()
expect(sosix_qemu_v2_structural_admission_parse(
    record.replace("artifact_count=8", "artifact_count=08")).structurally_valid).to_be(false)
expect(sosix_qemu_v2_structural_admission_parse(
    record.replace("artifact_count=8", "artifact_count=9")).structurally_valid).to_be(false)
expect(sosix_qemu_v2_structural_admission_parse(
    record.replace("firmware_sha256=none", "firmware_sha256=sha256:" + "a" * 64)).structurally_valid).to_be(false)
```

</details>

#### rejects dirty source identity and malformed hash fields

- rejects dirty source identity and malformed hash fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects dirty source identity and malformed hash fields")
val record = _v2_admission_record()
expect(sosix_qemu_v2_structural_admission_parse(
    record.replace(":clean", ":dirty")).structurally_valid).to_be(false)
expect(sosix_qemu_v2_structural_admission_parse(
    record.replace("evidence_sha256=0123", "evidence_sha256=ABCD")).structurally_valid).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/qemu_v2_admission_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SOSIX QEMU v2 structural admission contract.
- SOSIX QEMU v2 structural admission contract

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `365b21fcecac5b459096026679bd8e7da34ede40896c9eebc4a5378c0acf65be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `365b21fcecac5b459096026679bd8e7da34ede40896c9eebc4a5378c0acf65be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `365b21fcecac5b459096026679bd8e7da34ede40896c9eebc4a5378c0acf65be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/sosix/qemu_v2_admission_contract_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/qemu_v2_admission_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/qemu_v2_admission_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/qemu_v2_admission_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/qemu_v2_admission_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/qemu_v2_admission_contract_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the closed direct-kernel eight-artifact record without granting trust' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/qemu_v2_admission_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects missing, reordered, duplicated, and unknown record fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/qemu_v2_admission_contract_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects noncanonical counts and false direct-kernel firmware claims' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
