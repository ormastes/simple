# Simpleos Performance V1 Specification

> Tests covering SimpleOS canonical performance admission v1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Performance V1 Specification

## Scenarios

### SimpleOS canonical performance admission v1

#### admits stable native evidence and computes nearest-rank percentiles

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits stable native evidence and computes nearest-rank percentiles
   - Expected: result.stats.p50 equals `100u64`
   - Expected: result.stats.p95 equals `105u64`
   - Expected: result.stats.p99 equals `105u64`
   - Expected: result.stats.max equals `105u64`
   - Expected: result.stats.max_rss_bytes equals `100000u64`
   - Expected: result.admitted_value equals `105u64`
   - Expected: samples[0] equals `105u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("admits stable native evidence and computes nearest-rank percentiles")
val samples = [105u64, 96u64, 104u64, 97u64, 103u64, 98u64, 102u64, 99u64, 101u64, 100u64]
var evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, samples)
evidence.baseline_value = 105u64
val result = simpleos_performance_admit(evidence)
expect(result.ok).to_be(true)
expect(result.stats.p50).to_equal(100u64)
expect(result.stats.p95).to_equal(105u64)
expect(result.stats.p99).to_equal(105u64)
expect(result.stats.max).to_equal(105u64)
expect(result.stats.max_rss_bytes).to_equal(100000u64)
expect(result.admitted_value).to_equal(105u64)
expect(samples[0]).to_equal(105u64)
```

</details>

#### binds every selected NFR budget to its exact unit percentile and limit

- binds every selected NFR budget to its exact unit percentile and limit
   - Expected: simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.WarmServerStartup, 1u64).limit equals `125000u64`
   - Expected: simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.HttpDbLoopback, 1u64).limit equals `5000u64`
   - Expected: simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.SshEstablish, 1u64).limit equals `125000u64`
   - Expected: simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.WindowManagerFirstFrame, 1u64).limit equals `250000u64`
   - Expected: simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.InputToPresent, 1u64).limit equals `25000u64`
   - Expected: frame.admission_percentile equals `99u64`
   - Expected: frame.limit equals `16700u64`
   - Expected: simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.FsMetadata, 1u64).limit equals `2500u64`
   - Expected: throughput.unit equals `SimpleOsPerformanceUnitV1.BytesPerSecond`
   - Expected: throughput.direction equals `SimpleOsPerformanceDirectionV1.HigherIsBetter`
   - Expected: throughput.admission_percentile equals `50u64`
   - Expected: throughput.limit equals `104857600u64`
   - Expected: simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.SimpleCompileRun, 1u64).limit equals `2500000u64`
   - Expected: simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.CCompileLinkRun, 1u64).limit equals `2500000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("binds every selected NFR budget to its exact unit percentile and limit")
expect(simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.WarmServerStartup, 1u64).limit).to_equal(125000u64)
expect(simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.HttpDbLoopback, 1u64).limit).to_equal(5000u64)
expect(simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.SshEstablish, 1u64).limit).to_equal(125000u64)
expect(simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.WindowManagerFirstFrame, 1u64).limit).to_equal(250000u64)
expect(simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.InputToPresent, 1u64).limit).to_equal(25000u64)
val frame = simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.WindowManagerSteadyFrame, 1u64)
expect(frame.admission_percentile).to_equal(99u64)
expect(frame.limit).to_equal(16700u64)
expect(simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.FsMetadata, 1u64).limit).to_equal(2500u64)
val throughput = simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.FsSequentialThroughput, 1u64)
expect(throughput.unit).to_equal(SimpleOsPerformanceUnitV1.BytesPerSecond)
expect(throughput.direction).to_equal(SimpleOsPerformanceDirectionV1.HigherIsBetter)
expect(throughput.admission_percentile).to_equal(50u64)
expect(throughput.limit).to_equal(104857600u64)
expect(simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.SimpleCompileRun, 1u64).limit).to_equal(2500000u64)
expect(simpleos_performance_canonical_budget(SimpleOsPerformanceWorkloadV1.CCompileLinkRun, 1u64).limit).to_equal(2500000u64)
```

</details>

#### rejects too few samples and all non-native timing evidence

- rejects too few samples and all non-native timing evidence
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.TooFewSamples`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.NonNativeCannotPass`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.NonNativeCannotPass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects too few samples and all non-native timing evidence")
var evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, [10u64, 10u64])
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.TooFewSamples)
evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
evidence.host = SimpleOsPerformanceHostV1.QemuKvm
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.NonNativeCannotPass)
evidence.host = SimpleOsPerformanceHostV1.QemuTcg
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.NonNativeCannotPass)
```

</details>

#### rejects weakened budgets and noncanonical hashes

- rejects weakened budgets and noncanonical hashes
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.InvalidBudget`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.InvalidHash`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.InvalidHash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects weakened budgets and noncanonical hashes")
var evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
var changed_budget = evidence.budget
changed_budget.limit = 999999u64
evidence.budget = changed_budget
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.InvalidBudget)
evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
evidence.fixture_hash = "0123456789ABCDEF0123456789abcdef0123456789abcdef0123456789abcdef"
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.InvalidHash)
evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
evidence.binary_hash = "bad"
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.InvalidHash)
```

</details>

#### rejects noisy, absolute-budget, and direction-aware regression failures

- rejects noisy, absolute-budget, and direction-aware regression failures
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.NoisySamples`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.AbsoluteBudgetExceeded`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.Regression`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.Regression`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects noisy, absolute-budget, and direction-aware regression failures")
var evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, [1u64, 1u64, 1u64, 1u64, 1u64, 100u64, 100u64, 100u64, 100u64, 100u64])
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.NoisySamples)
evidence = evidence_for(SimpleOsPerformanceWorkloadV1.FsMetadata, stable_samples(3000u64))
evidence.baseline_value = 3000u64
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.AbsoluteBudgetExceeded)
evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(106u64))
evidence.baseline_value = 100u64
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.Regression)
evidence = evidence_for(SimpleOsPerformanceWorkloadV1.FsSequentialThroughput, stable_samples(104857600u64))
evidence.baseline_value = 120000000u64
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.Regression)
```

</details>

#### admits exact five-percent CV and rejects a just-over boundary

- admits exact five-percent CV and rejects a just-over boundary
   - Expected: exact.stats.cv_basis_points equals `500u64`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.NoisySamples`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("admits exact five-percent CV and rejects a just-over boundary")
var evidence = evidence_for(
    SimpleOsPerformanceWorkloadV1.WarmServerStartup,
    [950u64, 1050u64, 950u64, 1050u64, 950u64, 1050u64, 950u64, 1050u64, 950u64, 1050u64])
evidence.baseline_value = 1050u64
val exact = simpleos_performance_admit(evidence)
expect(exact.ok).to_be(true)
expect(exact.stats.cv_basis_points).to_equal(500u64)
evidence = evidence_for(
    SimpleOsPerformanceWorkloadV1.WarmServerStartup,
    [950u64, 1050u64, 950u64, 1050u64, 949u64, 1051u64, 949u64, 1051u64, 949u64, 1051u64])
evidence.baseline_value = 1051u64
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.NoisySamples)
```

</details>

#### rejects missing, zero, or summary-mismatched raw RSS evidence

- rejects missing, zero, or summary-mismatched raw RSS evidence
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.InvalidSample`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.InvalidSample`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.NonComparable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects missing, zero, or summary-mismatched raw RSS evidence")
var evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
evidence.rss_samples = [100000u64]
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.InvalidSample)
evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
var zero_rss = stable_samples(100000u64)
zero_rss[4] = 0u64
evidence.rss_samples = zero_rss
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.InvalidSample)
evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
var mismatched_rss = stable_samples(100000u64)
mismatched_rss[9] = 100001u64
evidence.rss_samples = mismatched_rss
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.NonComparable)
```

</details>

#### rejects campaign identities absent from the bounded verified artifact set

- rejects campaign identities absent from the bounded verified artifact set
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.NonComparable`
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.NonComparable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("rejects campaign identities absent from the bounded verified artifact set")
var evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
evidence.artifact_hashes = [FIXTURE_HASH, BINARY_HASH, IMAGE_HASH,
                            BASELINE_HASH]
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.NonComparable)
evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
evidence.artifact_hashes = [FIXTURE_HASH, BINARY_HASH, IMAGE_HASH,
                            CONFIG_HASH, BASELINE_HASH, CONFIG_HASH]
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.NonComparable)
```

</details>

#### fails closed on arithmetic overflow

- fails closed on arithmetic overflow
   - Expected: simpleos_performance_admit(evidence).error equals `SimpleOsPerformanceErrorV1.Overflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("fails closed on arithmetic overflow")
var evidence = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(18446744073709551615u64))
evidence.baseline_value = 18446744073709551615u64
expect(simpleos_performance_admit(evidence).error).to_equal(SimpleOsPerformanceErrorV1.Overflow)
```

</details>

#### admits exactly five percent and rejects beyond it for both directions and RSS

- admits exactly five percent and rejects beyond it for both directions and RSS
   - Expected: simpleos_performance_admit(latency).error equals `SimpleOsPerformanceErrorV1.Regression`
   - Expected: simpleos_performance_admit(throughput).error equals `SimpleOsPerformanceErrorV1.Regression`
   - Expected: simpleos_performance_admit(latency).error equals `SimpleOsPerformanceErrorV1.Regression`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("admits exactly five percent and rejects beyond it for both directions and RSS")
var latency = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(105u64))
latency.baseline_value = 100u64
expect(simpleos_performance_admit(latency).ok).to_be(true)
latency = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(106u64))
latency.baseline_value = 100u64
expect(simpleos_performance_admit(latency).error).to_equal(SimpleOsPerformanceErrorV1.Regression)
var throughput = evidence_for(SimpleOsPerformanceWorkloadV1.FsSequentialThroughput, stable_samples(114000000u64))
throughput.baseline_value = 120000000u64
expect(simpleos_performance_admit(throughput).ok).to_be(true)
throughput = evidence_for(SimpleOsPerformanceWorkloadV1.FsSequentialThroughput, stable_samples(113999999u64))
throughput.baseline_value = 120000000u64
expect(simpleos_performance_admit(throughput).error).to_equal(SimpleOsPerformanceErrorV1.Regression)
latency = evidence_for(SimpleOsPerformanceWorkloadV1.WarmServerStartup, stable_samples(100u64))
latency.baseline_rss_bytes = 100u64
latency.max_rss_bytes = 105u64
expect(simpleos_performance_admit(latency).ok).to_be(true)
latency.max_rss_bytes = 106u64
expect(simpleos_performance_admit(latency).error).to_equal(SimpleOsPerformanceErrorV1.Regression)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/simpleos_performance_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS canonical performance admission v1.
- SimpleOS canonical performance admission v1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-018`
- `REQ-SSPEC-COMMON`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ede0d225589baa8f34d8bdb84d2b54671f7b8e986d5dbd184c046d53bcb8c854`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ede0d225589baa8f34d8bdb84d2b54671f7b8e986d5dbd184c046d53bcb8c854`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ede0d225589baa8f34d8bdb84d2b54671f7b8e986d5dbd184c046d53bcb8c854`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/common/simpleos_performance_v1_spec.spl
mirror: doc/06_spec/01_unit/common/simpleos_performance_v1_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/common/simpleos_performance_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/simpleos_performance_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/simpleos_performance_v1_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/common/simpleos_performance_v1_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits stable native evidence and computes nearest-rank percentiles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/simpleos_performance_v1_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds every selected NFR budget to its exact unit percentile and limit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/simpleos_performance_v1_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects too few samples and all non-native timing evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
