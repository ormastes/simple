# Capability Ledger Specification

> Tests covering SimpleOS capability ledger owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Ledger Specification

## Scenarios

### SimpleOS capability ledger owner

#### accepts a complete blocked row without inferring Pass

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a complete blocked row without inferring Pass
   - Expected: result.ok is true
   - Expected: result.ledger.rows.len() equals `1`
   - Expected: result.ledger.rows[0].status equals `SimpleOsCapabilityStatus.Blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts a complete blocked row without inferring Pass")
val result = simpleos_capability_ledger_commit(
    simpleos_capability_ledger_v1(),
    [blocked_candidate("REQ-001", "ledger", "rv64")])
expect(result.ok).to_equal(true)
expect(result.ledger.rows.len()).to_equal(1)
expect(result.ledger.rows[0].status).to_equal(SimpleOsCapabilityStatus.Blocked)
```

</details>

#### does not promote a receipt-bound Pass row without an owned cryptographic verifier

- does not promote a receipt-bound Pass row without an owned cryptographic verifier
   - Expected: simpleos_capability_candidate_validate(candidate).ok is true
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not promote a receipt-bound Pass row without an owned cryptographic verifier")
val candidate = pass_candidate("REQ-001", "ledger", "x86_64", "r-1")
expect(simpleos_capability_candidate_validate(candidate).ok).to_equal(true)
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission_for(candidate.receipt)])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("cryptographic-verifier-unavailable")
```

</details>

#### rejects a self-consistent receipt without service admission context

- rejects a self-consistent receipt without service admission context
   - Expected: result.ok is false
   - Expected: result.failure equals `SimpleOsCapabilityLedgerFailure.AdmissionRequired`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a self-consistent receipt without service admission context")
val candidate = pass_candidate("REQ-001", "ledger", "x86_64", "r-no-context")
val result = simpleos_capability_ledger_commit(
    simpleos_capability_ledger_v1(), [candidate])
expect(result.ok).to_equal(false)
expect(result.failure).to_equal(SimpleOsCapabilityLedgerFailure.AdmissionRequired)
```

</details>

#### rejects an admission context without explicit signature verification

- rejects an admission context without explicit signature verification
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an admission context without explicit signature verification")
val candidate = pass_candidate("REQ-001", "ledger", "x86_64", "r-unverified")
var admission = admission_for(candidate.receipt)
admission.signature_verified = false
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("verification-outcome")
```

</details>

#### rejects a substituted hash and leaves the parent ledger unchanged

- rejects a substituted hash and leaves the parent ledger unchanged
   - Expected: result.ok is false
   - Expected: result.ledger.rows.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a substituted hash and leaves the parent ledger unchanged")
val candidate = pass_candidate("REQ-001", "ledger", "x86_64", "r-2")
var admission = admission_for(candidate.receipt)
admission.current_image_hash = HASH_A
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.ledger.rows.len()).to_equal(0)
expect(result.reason).to_contain("current-hash-binding")
```

</details>

#### sorts candidates by the complete row key before committing

- sorts candidates by the complete row key before committing
   - Expected: result.ok is true
   - Expected: result.ordered_keys[0] equals `simpleos_capability_row_key(second.row)`
   - Expected: result.ordered_keys[1] equals `simpleos_capability_row_key(first.row)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("sorts candidates by the complete row key before committing")
val first = blocked_candidate("REQ-002", "wm", "x86_64")
val second = blocked_candidate("REQ-001", "ledger", "x86_64")
val result = simpleos_capability_ledger_commit(
    simpleos_capability_ledger_v1(), [first, second])
expect(result.ok).to_equal(true)
expect(result.ordered_keys[0]).to_equal(simpleos_capability_row_key(second.row))
expect(result.ordered_keys[1]).to_equal(simpleos_capability_row_key(first.row))
```

</details>

#### rejects duplicate keys atomically

- rejects duplicate keys atomically
   - Expected: result.ok is false
   - Expected: result.reason equals `duplicate-key`
   - Expected: result.ledger.rows.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects duplicate keys atomically")
val first = blocked_candidate("REQ-001", "ledger", "rv64")
val second = blocked_candidate("REQ-001", "ledger", "rv64")
val result = simpleos_capability_ledger_commit(
    simpleos_capability_ledger_v1(), [first, second])
expect(result.ok).to_equal(false)
expect(result.reason).to_equal("duplicate-key")
expect(result.ledger.rows.len()).to_equal(0)
```

</details>

#### rejects duplicate artifact hashes or blocker paths

- rejects duplicate artifact hashes or blocker paths
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects duplicate artifact hashes or blocker paths")
var candidate = pass_candidate("REQ-001", "ledger", "x86_64", "r-dup-artifact")
var duplicate_row = candidate.row
duplicate_row.artifacts = [HASH_A, HASH_A]
duplicate_row.artifact_paths = ["build/a", "build/a"]
candidate.row = duplicate_row
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission_for(candidate.receipt)])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("artifacts")
```

</details>

#### requires a bounded artifact path on blocker rows

- requires a bounded artifact path on blocker rows
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires a bounded artifact path on blocker rows")
var candidate = blocked_candidate("REQ-003", "board", "rv64")
var missing_path_row = candidate.row
missing_path_row.artifact_paths = []
candidate.row = missing_path_row
val result = simpleos_capability_ledger_commit(
    simpleos_capability_ledger_v1(), [candidate])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("artifact-paths")
```

</details>

#### does not consume a nonce when cryptographic verification is unavailable

- does not consume a nonce when cryptographic verification is unavailable
   - Expected: first_result.ok is false
   - Expected: first_result.ledger.consumed_nonces.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not consume a nonce when cryptographic verification is unavailable")
val first = pass_candidate("REQ-001", "ledger", "x86_64", "r-retained")
val first_result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [first], [admission_for(first.receipt)])
expect(first_result.ok).to_equal(false)
expect(first_result.reason).to_contain("cryptographic-verifier-unavailable")
expect(first_result.ledger.consumed_nonces.len()).to_equal(0)
```

</details>

#### does not inspect batch nonce replay before cryptographic admission

- does not inspect batch nonce replay before cryptographic admission
   - Expected: result.ok is false
   - Expected: result.ledger.rows.len() equals `0`
   - Expected: result.ledger.consumed_nonces.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not inspect batch nonce replay before cryptographic admission")
val first = pass_candidate("REQ-001", "ledger", "x86_64", "r-3")
var second = pass_candidate("REQ-002", "ledger", "x86_64", "r-4")
var second_receipt = second.receipt
second_receipt.nonce = first.receipt.nonce
second.receipt = second_receipt
var second_row = second.row
second_row.receipt_nonce = first.receipt.nonce
second.row = second_row
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [first, second],
    [admission_for(first.receipt), admission_for(second.receipt)])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("cryptographic-verifier-unavailable")
expect(result.ledger.rows.len()).to_equal(0)
expect(result.ledger.consumed_nonces.len()).to_equal(0)
```

</details>

#### rejects a performance promotion without ten samples

- rejects a performance promotion without ten samples
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a performance promotion without ten samples")
val candidate = pass_candidate("NFR-002", "performance", "x86_64", "r-perf")
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission_for(candidate.receipt)])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### does not treat QEMU TCG samples as native performance evidence

- does not treat QEMU TCG samples as native performance evidence
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not treat QEMU TCG samples as native performance evidence")
var candidate = pass_candidate("NFR-002", "performance", "x86_64", "r-perf-tcg")
var performance_receipt = candidate.receipt
performance_receipt.performance_workload = "http_db_loopback"
performance_receipt.performance_unit = "microseconds_milli"
performance_receipt.performance_warmup_count = 2
performance_receipt.performance_cpu_identity = "tcg-cpu"
performance_receipt.performance_frequency_hz = 1000000
performance_receipt.performance_noise_profile = "controlled"
performance_receipt.performance_comparable = true
performance_receipt.performance_samples = ten_samples()
candidate.receipt = performance_receipt
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### rejects QEMU KVM-like samples as non-native

- rejects QEMU KVM-like samples as non-native
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects QEMU KVM-like samples as non-native")
val candidate = performance_candidate(
    "r-perf-kvm", "http_db_loopback", "microseconds_milli",
    SimpleOsEvidenceEnvironment.QemuSystem, "qemu-kvm", 1000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### rejects a workload outside the closed performance vocabulary

- rejects a workload outside the closed performance vocabulary
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a workload outside the closed performance vocabulary")
val candidate = performance_candidate(
    "r-perf-workload", "unknown_workload", "microseconds_milli",
    SimpleOsEvidenceEnvironment.NativeHost, "native", 1000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### rejects a unit that is not canonical for the workload

- rejects a unit that is not canonical for the workload
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a unit that is not canonical for the workload")
val candidate = performance_candidate(
    "r-perf-unit", "http_db_loopback", "bytes_per_second_milli",
    SimpleOsEvidenceEnvironment.NativeHost, "native", 1000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### rejects runner evidence not marked comparable even when the service context is

- rejects runner evidence not marked comparable even when the service context is
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects runner evidence not marked comparable even when the service context is")
val candidate = performance_candidate(
    "r-perf-not-comparable", "http_db_loopback", "microseconds_milli",
    SimpleOsEvidenceEnvironment.NativeHost, "native", 1000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### cannot weaken the canonical metric budget through admission context

- cannot weaken the canonical metric budget through admission context
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("cannot weaken the canonical metric budget through admission context")
val candidate = native_performance_candidate("r-perf-budget", 6000000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
admission.performance_configured_max_rss_bytes = 999999999u64
admission.performance_baseline_value = 1u64
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### rejects noisy native performance samples

- rejects noisy native performance samples
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects noisy native performance samples")
var candidate = native_performance_candidate("r-perf-noisy", 1000, 1000)
var receipt = candidate.receipt
var noisy = ten_samples()
var i: i64 = 0
while i < noisy.len():
    var sample = noisy[i]
    sample.metric_value_milli = if i % 2 == 0: 1000 else: 3000
    noisy[i] = sample
    i = i + 1
receipt.performance_samples = noisy
candidate.receipt = receipt
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### rejects native samples over the canonical budget

- rejects native samples over the canonical budget
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects native samples over the canonical budget")
val candidate = native_performance_candidate("r-perf-over", 6000000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### rejects native metric regression against the admitted baseline

- rejects native metric regression against the admitted baseline
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects native metric regression against the admitted baseline")
val candidate = native_performance_candidate("r-perf-regression", 1100, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### rejects native samples over the RSS regression ceiling

- rejects native samples over the RSS regression ceiling
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects native samples over the RSS regression ceiling")
val candidate = native_performance_candidate("r-perf-rss", 1000, 1101)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### rejects a service fixture hash absent from verified receipt artifacts

- rejects a service fixture hash absent from verified receipt artifacts
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a service fixture hash absent from verified receipt artifacts")
val candidate = native_performance_candidate("r-perf-fixture", 1000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
admission.performance_fixture_hash = HASH_B
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("performance-admission")
```

</details>

#### validates stable native performance but still requires the cryptographic verifier

- validates stable native performance but still requires the cryptographic verifier
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("validates stable native performance but still requires the cryptographic verifier")
val candidate = native_performance_candidate("r-perf-native", 1000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val result = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(result.ok).to_equal(false)
expect(result.reason).to_contain("cryptographic-verifier-unavailable")
```

</details>

#### projects performance without granting ledger admission authority

- projects performance without granting ledger admission authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("projects performance without granting ledger admission authority")
val candidate = native_performance_candidate(
    "r-perf-projection", 1000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_external_comparability_verified = true
val projection = simpleos_capability_performance_projection(
    candidate, admission)
expect(projection.applicable).to_be(true)
expect(projection.admissible).to_be(true)
val commit = simpleos_capability_ledger_commit_with_admission(
    simpleos_capability_ledger_v1(), [candidate], [admission])
expect(commit.ok).to_be(false)
expect(commit.reason).to_contain("cryptographic-verifier-unavailable")
```

</details>

#### fails a performance projection closed when runtime inputs are absent

- fails a performance projection closed when runtime inputs are absent
   - Expected: projection.reason equals `performance-evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails a performance projection closed when runtime inputs are absent")
val candidate = native_performance_candidate(
    "r-perf-projection-missing", 1000, 1000)
var admission = admission_for(candidate.receipt)
admission.performance_fixture_hash = ""
val projection = simpleos_capability_performance_projection(
    candidate, admission)
expect(projection.applicable).to_be(true)
expect(projection.admissible).to_be(false)
expect(projection.reason).to_equal("performance-evidence")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/evidence/capability_ledger_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS capability ledger owner.
- SimpleOS capability ledger owner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `81e12323a183b571e79b1ba4399647f7749c3f0c75fc478242606e8a5051ac64`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81e12323a183b571e79b1ba4399647f7749c3f0c75fc478242606e8a5051ac64`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81e12323a183b571e79b1ba4399647f7749c3f0c75fc478242606e8a5051ac64`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/services/evidence/capability_ledger_spec.spl
mirror: doc/06_spec/01_unit/os/services/evidence/capability_ledger_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/evidence/capability_ledger_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/evidence/capability_ledger_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/evidence/capability_ledger_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/evidence/capability_ledger_spec.spl:228:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a complete blocked row without inferring Pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/evidence/capability_ledger_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not promote a receipt-bound Pass row without an owned cryptographic verifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/evidence/capability_ledger_spec.spl:248:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a self-consistent receipt without service admission context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
