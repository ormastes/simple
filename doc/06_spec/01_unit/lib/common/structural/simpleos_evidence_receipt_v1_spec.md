# Simpleos Evidence Receipt V1 Specification

> Tests covering SimpleOS evidence receipt v1 validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Evidence Receipt V1 Specification

## Scenarios

### SimpleOS evidence receipt v1 validation

#### accepts a complete bounded QEMU candidate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
```

</details>

#### pins stable environment and diagnostic spellings

- pins stable environment and diagnostic spellings


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins stable environment and diagnostic spellings")
assert_equal(
    simpleos_evidence_environment_to_text(SimpleOsEvidenceEnvironment.QemuSystem),
    "qemu_system"
)
assert_equal(
    simpleos_evidence_receipt_error_to_text(SimpleOsEvidenceReceiptError.InvalidDigest),
    "invalid_digest"
)
```

</details>

#### rejects an unknown schema before admission

- rejects an unknown schema before admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an unknown schema before admission")
var r = _valid_receipt()
r.schema_version = 2
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.UnsupportedSchema)
```

</details>

#### rejects a malformed digest rather than coercing it

- rejects a malformed digest rather than coercing it


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a malformed digest rather than coercing it")
var r = _valid_receipt()
r.binary_hash = "NOT-A-DIGEST"
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.InvalidDigest)
```

</details>

#### rejects missing canonical identity

- rejects missing canonical identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects missing canonical identity")
var r = _valid_receipt()
r.requirement_id = ""
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.MissingIdentity)
```

</details>

#### rejects peer-controlled text above its bound

- rejects peer-controlled text above its bound


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects peer-controlled text above its bound")
var r = _valid_receipt()
r.protocol_profile = _repeated("x", 257)
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.TextTooLong)
```

</details>

#### rejects control characters on direct typed ingress

- rejects control characters on direct typed ingress


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects control characters on direct typed ingress")
var r = _valid_receipt()
r.owner = "owner\nforged"
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.InvalidText)
```

</details>

#### rejects a QEMU row without firmware identity

- rejects a QEMU row without firmware identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a QEMU row without firmware identity")
var r = _valid_receipt()
r.firmware_profile = ""
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.MissingTargetIdentity)
```

</details>

#### rejects a physical row without board identity

- rejects a physical row without board identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a physical row without board identity")
var r = _valid_receipt()
r.environment = SimpleOsEvidenceEnvironment.PhysicalBoard
r.board_identity = ""
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.MissingTargetIdentity)
```

</details>

#### rejects a native row without machine identity

- rejects a native row without machine identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a native row without machine identity")
var r = _valid_receipt()
r.environment = SimpleOsEvidenceEnvironment.NativeHost
r.board_identity = ""
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.MissingTargetIdentity)
```

</details>

#### rejects an empty argv and an empty executable name

- rejects an empty argv and an empty executable name


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an empty argv and an empty executable name")
var no_args = _valid_receipt()
no_args.exact_argv = []
assert_equal(
    simpleos_evidence_receipt_validate(no_args).error,
    SimpleOsEvidenceReceiptError.InvalidArgumentCount
)
var no_program = _valid_receipt()
no_program.exact_argv = [""]
assert_equal(
    simpleos_evidence_receipt_validate(no_program).error,
    SimpleOsEvidenceReceiptError.InvalidArgumentCount
)
```

</details>

#### rejects an empty or oversized artifact set

- rejects an empty or oversized artifact set


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an empty or oversized artifact set")
var empty = _valid_receipt()
empty.artifact_hashes = []
assert_equal(
    simpleos_evidence_receipt_validate(empty).error,
    SimpleOsEvidenceReceiptError.InvalidArtifactCount
)
var oversized = _valid_receipt()
oversized.artifact_hashes = _too_many_hashes()
assert_equal(
    simpleos_evidence_receipt_validate(oversized).error,
    SimpleOsEvidenceReceiptError.InvalidArtifactCount
)
```

</details>

#### rejects an empty observed-step set

- rejects an empty observed-step set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an empty observed-step set")
var r = _valid_receipt()
r.steps = []
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.InvalidStepCount)
```

</details>

#### rejects non-monotonic step sequence

- rejects non-monotonic step sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects non-monotonic step sequence")
var r = _valid_receipt()
r.steps = [SimpleOsEvidenceStepV1(
    sequence: 4,
    behavior_id: "REQ-001-capability-ledger",
    outcome: "validated",
    exit_code: 0,
    artifact_hash: _hash()
)]
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.InvalidSequence)
```

</details>

#### rejects producer self-review

- rejects producer self-review


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects producer self-review")
var r = _valid_receipt()
r.reviewer = r.owner
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.ReviewerConflict)
```

</details>

#### rejects invalid performance samples

- rejects invalid performance samples


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid performance samples")
var r = _valid_receipt()
r.performance_samples = [SimpleOsPerformanceSampleV1(
    sequence: 1,
    metric_value_milli: 0,
    elapsed_us: 0 - 1,
    max_rss_bytes: 0
)]
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.InvalidPerformanceSampleCount)
```

</details>

#### rejects missing signature binding

- rejects missing signature binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects missing signature binding")
var r = _valid_receipt()
r.signature = ""
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.MissingSignature)
```

</details>

#### rejects end time before start time

- rejects end time before start time


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects end time before start time")
var r = _valid_receipt()
r.finished_unix_us = 999
val check = simpleos_evidence_receipt_validate(r)
assert_false(check.ok)
assert_equal(check.error, SimpleOsEvidenceReceiptError.InvalidTimeRange)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS evidence receipt v1 validation.
- SimpleOS evidence receipt v1 validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-001-capability-ledger`
- `REQ-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a59d05c6790d24ec9e6adcaaebc9e7bda63ccc7a016f2552a56ab86292a754c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a59d05c6790d24ec9e6adcaaebc9e7bda63ccc7a016f2552a56ab86292a754c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a59d05c6790d24ec9e6adcaaebc9e7bda63ccc7a016f2552a56ab86292a754c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_spec.spl
mirror: doc/06_spec/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_spec.spl:99:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts a complete bounded QEMU candidate' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins stable environment and diagnostic spellings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown schema before admission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a malformed digest rather than coercing it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
