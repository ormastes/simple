# Test Result Cache Specification

> Tests covering TestResultCache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Result Cache Specification

## Scenarios

### TestResultCache

#### invalidates cache when dependency content changes without changing size

- invalidates cache when dependency content changes without changing size
   - Expected: entry.result_status equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("invalidates cache when dependency content changes without changing size")
dir_create_all(runner_cache_spec_root)
val cache_path = runner_cache_test_path("runner_cache.sdn")
val test_path = runner_cache_test_path("sample_spec.spl")
val dep_path = runner_cache_test_path("dep_a.spl")

file_write(test_path, "describe \"sample\":\n    it \"runs\":\n        expect(1).to_equal(1)\n")
file_write(dep_path, "alpha")

val cache = test_result_cache_new(cache_path)
cache.record_result(test_path, [dep_path], 1, 0, 0, 12)
cache.save()

file_write(dep_path, "omega")

val reloaded = test_result_cache_load(cache_path)
val entry = reloaded.check_freshness(test_path, [dep_path])

expect(entry.result_status).to_equal(-1)
```

</details>

#### invalidates cache when dependency set no longer matches recorded dependencies

- invalidates cache when dependency set no longer matches recorded dependencies
   - Expected: entry.result_status equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("invalidates cache when dependency set no longer matches recorded dependencies")
dir_create_all(runner_cache_spec_root)
val test_path = runner_cache_test_path("sample_spec.spl")
val dep_a = runner_cache_test_path("dep_a.spl")
val dep_b = runner_cache_test_path("dep_b.spl")

file_write(test_path, "describe \"sample\":\n    it \"runs\":\n        expect(1).to_equal(1)\n")
file_write(dep_a, "dep-a")
file_write(dep_b, "dep-b")

val cache = test_result_cache_new(runner_cache_test_path("runner_cache.sdn"))
cache.record_result(test_path, [dep_a, dep_b], 1, 0, 0, 12)

val entry = cache.check_freshness(test_path, [dep_a])

expect(entry.result_status).to_equal(-1)
```

</details>

#### invalidates cache when a tracked dependency is removed

- invalidates cache when a tracked dependency is removed
   - Expected: entry.result_status equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("invalidates cache when a tracked dependency is removed")
dir_create_all(runner_cache_spec_root)
val test_path = runner_cache_test_path("sample_spec.spl")
val dep_path = runner_cache_test_path("dep_a.spl")

expect(file_write(test_path, "describe sample")).to_be(true)
expect(file_write(dep_path, "dependency")).to_be(true)

val cache = test_result_cache_new(runner_cache_test_path("runner_cache.sdn"))
cache.record_result(test_path, [dep_path], 1, 0, 0, 12)
expect(file_delete(dep_path)).to_be(true)

val entry = cache.check_freshness(test_path, [dep_path])

expect(entry.result_status).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner_new/test_result_cache_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TestResultCache.
- TestResultCache

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `23d0394f1c5c94582b8f15e8269d4d49a5334266b577a7144d9586edd1f2edef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `23d0394f1c5c94582b8f15e8269d4d49a5334266b577a7144d9586edd1f2edef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `23d0394f1c5c94582b8f15e8269d4d49a5334266b577a7144d9586edd1f2edef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/unit/app/test_runner_new/test_result_cache_spec.spl
mirror: doc/06_spec/unit/app/test_runner_new/test_result_cache_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner_new/test_result_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner_new/test_result_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner_new/test_result_cache_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/app/test_runner_new/test_result_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_runner_new/test_result_cache_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates cache when dependency content changes without changing size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/test_result_cache_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates cache when dependency set no longer matches recorded dependencies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/test_result_cache_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates cache when a tracked dependency is removed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
