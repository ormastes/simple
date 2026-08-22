# Fail-Closed Evidence Receipt

> Verifies the evidence receipt behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fail-Closed Evidence Receipt

Verifies the evidence receipt behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented |
| Requirements | doc/01_research/domain/simpleos_production_host_master_plan.md §21.4 |
| Source | `test/01_unit/lib/spec/evidence_receipt_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the evidence receipt behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Evidence receipt: fully honest receipt

#### passes every fail-closed rule

- Verify: passes every fail-closed rule
- Build a complete, fresh, honest receipt
- Verify artifact presence, freshness, honesty, and arch support all pass
   - Expected: outcome.passed is true
   - Expected: outcome.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-A11-EVD
step("Verify: passes every fail-closed rule")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build a complete, fresh, honest receipt")
val r = honest_receipt()

step("Verify artifact presence, freshness, honesty, and arch support all pass")
val outcome = receipt_verify(r, true, 1500, 1000)
expect(outcome.passed).to_equal(true)
expect(outcome.reason).to_equal("ok")
```

</details>

#### serializes to SDN without corrupting brace-sensitive content

- Verify: serializes to SDN without corrupting brace-sensitive content
- Serialize the honest receipt to SDN text


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-A11-EVD
step("Verify: serializes to SDN without corrupting brace-sensitive content")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Serialize the honest receipt to SDN text")
val sdn = receipt_to_sdn(honest_receipt())
expect(sdn).to_contain("evidence_receipt:")
expect(sdn).to_contain("commit: abc123")
expect(sdn).to_contain("result: PASS")
```

</details>

### Evidence receipt: missing artifact = FAIL

#### fails with a distinct missing_artifact reason when the file is absent

- Verify: fails with a distinct missing_artifact reason when the file is absent
- Verify a receipt whose declared artifact does not exist on disk
   - Expected: outcome.passed is false
   - Expected: outcome.rule equals `artifact_present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-A11-EVD
step("Verify: fails with a distinct missing_artifact reason when the file is absent")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify a receipt whose declared artifact does not exist on disk")
val r = honest_receipt()
val outcome = receipt_verify(r, false, 1500, 1000)
expect(outcome.passed).to_equal(false)
expect(outcome.rule).to_equal("artifact_present")
expect(outcome.reason).to_contain("missing_artifact")
```

</details>

#### fails when no artifact is declared at all

- Verify: fails when no artifact is declared at all
- Verify a receipt that declares no artifact
   - Expected: rule_outcome.passed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-A11-EVD
step("Verify: fails when no artifact is declared at all")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify a receipt that declares no artifact")
val base = honest_receipt()
val r = EvidenceReceipt(
    commit: base.commit, source_digest: base.source_digest,
    compiler_digest: base.compiler_digest, image_digest: base.image_digest,
    target: base.target, firmware: base.firmware,
    machine_or_qemu: base.machine_or_qemu, test_id: base.test_id,
    test_version: base.test_version, start_time: base.start_time,
    duration: base.duration, result: base.result, metrics: base.metrics,
    logs: base.logs, artifacts: "", failure_reason: base.failure_reason
)
val rule_outcome = receipt_artifact_present(r, true)
expect(rule_outcome.passed).to_equal(false)
expect(rule_outcome.reason).to_contain("missing_artifact")
```

</details>

### Evidence receipt: stale artifact = FAIL

#### fails with a distinct stale_artifact reason when the artifact predates the run

- Verify: fails with a distinct stale_artifact reason when the artifact predates the run
- Verify a receipt whose artifact mtime is before the run's start_time
   - Expected: outcome.passed is false
   - Expected: outcome.rule equals `artifact_fresh`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-A11-EVD
step("Verify: fails with a distinct stale_artifact reason when the artifact predates the run")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify a receipt whose artifact mtime is before the run's start_time")
val r = honest_receipt()
val outcome = receipt_verify(r, true, 500, 1000)
expect(outcome.passed).to_equal(false)
expect(outcome.rule).to_equal("artifact_fresh")
expect(outcome.reason).to_contain("stale_artifact")
```

</details>

### Evidence receipt: hosted fallback in a bare-metal test = FAIL

#### fails with a distinct hosted_fallback reason

- Verify: fails with a distinct hosted_fallback reason
- Verify a bare_metal-target receipt that recorded a hosted fallback
   - Expected: outcome.passed is false
   - Expected: outcome.rule equals `execution_honest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-A11-EVD
step("Verify: fails with a distinct hosted_fallback reason")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify a bare_metal-target receipt that recorded a hosted fallback")
val base = honest_receipt()
val r = EvidenceReceipt(
    commit: base.commit, source_digest: base.source_digest,
    compiler_digest: base.compiler_digest, image_digest: base.image_digest,
    target: "bare_metal", firmware: base.firmware,
    machine_or_qemu: "hosted_fallback", test_id: base.test_id,
    test_version: base.test_version, start_time: base.start_time,
    duration: base.duration, result: base.result, metrics: base.metrics,
    logs: base.logs, artifacts: base.artifacts, failure_reason: base.failure_reason
)
val outcome = receipt_verify(r, true, 1500, 1000)
expect(outcome.passed).to_equal(false)
expect(outcome.rule).to_equal("execution_honest")
expect(outcome.reason).to_contain("hosted_fallback_in_baremetal")
```

</details>

### Evidence receipt: interpreter fallback in a native-perf test = FAIL

#### fails with a distinct interpreter_fallback reason

- Verify: fails with a distinct interpreter_fallback reason
- Verify a native_perf-target receipt that recorded an interpreter fallback
   - Expected: outcome.passed is false
   - Expected: outcome.rule equals `execution_honest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-A11-EVD
step("Verify: fails with a distinct interpreter_fallback reason")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify a native_perf-target receipt that recorded an interpreter fallback")
val base = honest_receipt()
val r = EvidenceReceipt(
    commit: base.commit, source_digest: base.source_digest,
    compiler_digest: base.compiler_digest, image_digest: base.image_digest,
    target: "native_perf", firmware: base.firmware,
    machine_or_qemu: "interpreter_fallback", test_id: base.test_id,
    test_version: base.test_version, start_time: base.start_time,
    duration: base.duration, result: base.result, metrics: base.metrics,
    logs: base.logs, artifacts: base.artifacts, failure_reason: base.failure_reason
)
val outcome = receipt_verify(r, true, 1500, 1000)
expect(outcome.passed).to_equal(false)
expect(outcome.rule).to_equal("execution_honest")
expect(outcome.reason).to_contain("interpreter_fallback_in_native_perf")
```

</details>

### Evidence receipt: unsupported architecture cannot silently pass

#### fails with a distinct unsupported_arch reason when result claims PASS

- Verify: fails with a distinct unsupported_arch reason when result claims PASS
- Verify a receipt for an unsupported architecture that claims PASS
   - Expected: outcome.passed is false
   - Expected: outcome.rule equals `arch_supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-A11-EVD
step("Verify: fails with a distinct unsupported_arch reason when result claims PASS")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify a receipt for an unsupported architecture that claims PASS")
val base = honest_receipt()
val r = EvidenceReceipt(
    commit: base.commit, source_digest: base.source_digest,
    compiler_digest: base.compiler_digest, image_digest: base.image_digest,
    target: base.target, firmware: base.firmware,
    machine_or_qemu: "unsupported", test_id: base.test_id,
    test_version: base.test_version, start_time: base.start_time,
    duration: base.duration, result: "PASS", metrics: base.metrics,
    logs: base.logs, artifacts: base.artifacts, failure_reason: base.failure_reason
)
val outcome = receipt_verify(r, true, 1500, 1000)
expect(outcome.passed).to_equal(false)
expect(outcome.rule).to_equal("arch_supported")
expect(outcome.reason).to_contain("unsupported_arch_claims_pass")
```

</details>

#### passes when the same architecture correctly reports unsupported (not PASS)

- Verify: passes when the same architecture correctly reports unsupported (not PASS)
- Verify an unsupported-arch receipt that honestly reports 'unsupported'
   - Expected: outcome.passed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-HARDEN-A11-EVD
step("Verify: passes when the same architecture correctly reports unsupported (not PASS)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify an unsupported-arch receipt that honestly reports 'unsupported'")
val base = honest_receipt()
val r = EvidenceReceipt(
    commit: base.commit, source_digest: base.source_digest,
    compiler_digest: base.compiler_digest, image_digest: base.image_digest,
    target: base.target, firmware: base.firmware,
    machine_or_qemu: "unsupported", test_id: base.test_id,
    test_version: base.test_version, start_time: base.start_time,
    duration: base.duration, result: "unsupported", metrics: base.metrics,
    logs: base.logs, artifacts: base.artifacts, failure_reason: "arch not available"
)
val outcome = receipt_verify(r, true, 1500, 1000)
expect(outcome.passed).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/01_research/domain/simpleos_production_host_master_plan.md §21.4`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c9168dd8065ac7fa7d52fbf95040a05c8f29dba616b3cdc21dc902ee6709746`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c9168dd8065ac7fa7d52fbf95040a05c8f29dba616b3cdc21dc902ee6709746`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c9168dd8065ac7fa7d52fbf95040a05c8f29dba616b3cdc21dc902ee6709746`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/spec/evidence_receipt_spec.spl
mirror: doc/06_spec/01_unit/lib/spec/evidence_receipt_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/spec/evidence_receipt_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/spec/evidence_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/spec/evidence_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
