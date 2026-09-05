# Freebsd Bootstrap Qemu Preflight Specification

> Tests covering FreeBSD QEMU bootstrap bounded preflight.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Freebsd Bootstrap Qemu Preflight Specification

## Scenarios

### FreeBSD QEMU bootstrap bounded preflight

#### accepts canonical memory and key paths containing spaces without live execution

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts canonical memory and key paths containing spaces without live execution
   - Expected: code equals `0`
   - Expected: stderr equals ``
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_checks") equals `19`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_order") equals `PREFLIGHT_ORDER`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_reason") equals `none`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_status") equals `pass`
   - Expected: stdout does not contain `Smoke test PASSED`
   - Expected: stdout does not contain `Full bootstrap PASSED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts canonical memory and key paths containing spaces without live execution")
val (stdout, stderr, code) = step_freebsd_bootstrap_preflight("")
expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(receipt_value(stdout, "freebsd_qemu_preflight_checks")).to_equal("19")
expect(receipt_value(stdout, "freebsd_qemu_preflight_order")).to_equal(PREFLIGHT_ORDER)
expect(receipt_value(stdout, "freebsd_qemu_preflight_reason")).to_equal("none")
expect(receipt_value(stdout, "freebsd_qemu_preflight_status")).to_equal("pass")
expect(stdout.contains("Smoke test PASSED")).to_equal(false)
expect(stdout.contains("Full bootstrap PASSED")).to_equal(false)
```

</details>

#### rejects an invalid port with its exact reason before live prerequisites

- rejects an invalid port with its exact reason before live prerequisites
   - Expected: code equals `1`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_checks") equals `19`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_order") equals `PREFLIGHT_ORDER`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_reason") equals `port`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_status") equals `fail`
   - Expected: stdout does not contain `Smoke test PASSED`
   - Expected: stdout does not contain `Full bootstrap PASSED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an invalid port with its exact reason before live prerequisites")
val (stdout, _stderr, code) = step_freebsd_bootstrap_preflight(
    "QEMU_PORT=not-a-port")
expect(code).to_equal(1)
expect(receipt_value(stdout, "freebsd_qemu_preflight_checks")).to_equal("19")
expect(receipt_value(stdout, "freebsd_qemu_preflight_order")).to_equal(PREFLIGHT_ORDER)
expect(receipt_value(stdout, "freebsd_qemu_preflight_reason")).to_equal("port")
expect(receipt_value(stdout, "freebsd_qemu_preflight_status")).to_equal("fail")
expect(stdout.contains("Smoke test PASSED")).to_equal(false)
expect(stdout.contains("Full bootstrap PASSED")).to_equal(false)
```

</details>

#### rejects a leading-hyphen guest user with its exact reason

- rejects a leading-hyphen guest user with its exact reason
   - Expected: code equals `1`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_checks") equals `19`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_order") equals `PREFLIGHT_ORDER`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_reason") equals `user`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_status") equals `fail`
   - Expected: stdout does not contain `Smoke test PASSED`
   - Expected: stdout does not contain `Full bootstrap PASSED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a leading-hyphen guest user with its exact reason")
val (stdout, _stderr, code) = step_freebsd_bootstrap_preflight(
    "QEMU_USER=-root")
expect(code).to_equal(1)
expect(receipt_value(stdout, "freebsd_qemu_preflight_checks")).to_equal("19")
expect(receipt_value(stdout, "freebsd_qemu_preflight_order")).to_equal(PREFLIGHT_ORDER)
expect(receipt_value(stdout, "freebsd_qemu_preflight_reason")).to_equal("user")
expect(receipt_value(stdout, "freebsd_qemu_preflight_status")).to_equal("fail")
expect(stdout.contains("Smoke test PASSED")).to_equal(false)
expect(stdout.contains("Full bootstrap PASSED")).to_equal(false)
```

</details>

#### refuses a present image without a trusted media digest

- refuses a present image without a trusted media digest
   - Expected: code equals `1`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_reason") equals `admitted_media`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_status") equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a present image without a trusted media digest")
val (stdout, _stderr, code) = step_freebsd_bootstrap_preflight(
    "SIMPLE_FREEBSD_MEDIA_SHA256=")
expect(code).to_equal(1)
expect(receipt_value(stdout, "freebsd_qemu_preflight_reason")).to_equal("admitted_media")
expect(receipt_value(stdout, "freebsd_qemu_preflight_status")).to_equal("fail")
```

</details>

#### refuses a present image whose trusted digest mismatches

- refuses a present image whose trusted digest mismatches
   - Expected: code equals `1`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_reason") equals `admitted_media`
   - Expected: receipt_value(stdout, "freebsd_qemu_preflight_status") equals `fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a present image whose trusted digest mismatches")
val zero_digest = "0000000000000000000000000000000000000000000000000000000000000000"
val (stdout, _stderr, code) = step_freebsd_bootstrap_preflight(
    "SIMPLE_FREEBSD_MEDIA_SHA256=" + zero_digest)
expect(code).to_equal(1)
expect(receipt_value(stdout, "freebsd_qemu_preflight_reason")).to_equal("admitted_media")
expect(receipt_value(stdout, "freebsd_qemu_preflight_status")).to_equal("fail")
```

</details>

#### keeps PASS evidence scoped to the FreeBSD QEMU preflight contract

- keeps PASS evidence scoped to the FreeBSD QEMU preflight contract
   - Expected: source does not contain `Smoke test PASSED`
   - Expected: source does not contain `Full bootstrap PASSED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps PASS evidence scoped to the FreeBSD QEMU preflight contract")
val source = file_read(SCRIPT)
expect(source).to_contain("freebsd_qemu_preflight_status=pass")
expect(source).to_contain("freebsd_qemu_preflight_status=fail")
expect(source.contains("Smoke test PASSED")).to_equal(false)
expect(source.contains("Full bootstrap PASSED")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/freebsd_bootstrap_qemu_preflight_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FreeBSD QEMU bootstrap bounded preflight.
- FreeBSD QEMU bootstrap bounded preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4fa9d6c26e7f64fc1b166b648837b8947d3ebb11fa9eaa0562755d5d4d0cc3d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fa9d6c26e7f64fc1b166b648837b8947d3ebb11fa9eaa0562755d5d4d0cc3d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fa9d6c26e7f64fc1b166b648837b8947d3ebb11fa9eaa0562755d5d4d0cc3d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/freebsd_bootstrap_qemu_preflight_spec.spl
mirror: doc/06_spec/03_system/check/freebsd_bootstrap_qemu_preflight_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/check/freebsd_bootstrap_qemu_preflight_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/freebsd_bootstrap_qemu_preflight_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/freebsd_bootstrap_qemu_preflight_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/check/freebsd_bootstrap_qemu_preflight_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/freebsd_bootstrap_qemu_preflight_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts canonical memory and key paths containing spaces without live execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/freebsd_bootstrap_qemu_preflight_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an invalid port with its exact reason before live prerequisites' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/freebsd_bootstrap_qemu_preflight_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a leading-hyphen guest user with its exact reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
