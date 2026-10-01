# Smoke Test Specification

> Tests covering Smoke Testing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smoke Test Specification

## Scenarios

### Smoke Testing

#### SmokeTestConfig

#### creates default config

- creates default config


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default config")
# val config = SmokeTestConfig.default()
# expect config.timeout_secs == 30.0
# expect config.retry_attempts == 3
# expect config.retry_delay_secs == 5.0
# expect config.fail_fast == true
expect true
```

</details>

#### creates custom config

- creates custom config


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates custom config")
# val config = SmokeTestConfig(
#     timeout_secs: 60.0,
#     retry_attempts: 5,
#     retry_delay_secs: 10.0,
#     fail_fast: false
# )
# expect config.timeout_secs == 60.0
expect true
```

</details>

#### SmokeTestSuite

#### adds tests to suite

- adds tests to suite


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds tests to suite")
# val suite = SmokeTestSuite.new()
#     .test("homepage", \: check_homepage())
#     .test("database", \: check_database())
#
# expect suite.tests.len() == 2
expect true
```

</details>

#### runs all tests

- runs all tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs all tests")
# var test1_ran = false
# var test2_ran = false
#
# val suite = SmokeTestSuite.new()
#     .test("test1", \: { test1_ran = true; true })
#     .test("test2", \: { test2_ran = true; true })
#
# suite.run()
# expect test1_ran
# expect test2_ran
expect true
```

</details>

#### collects results

- collects results


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects results")
# val suite = SmokeTestSuite.new()
#     .test("expect true", \: true)
#     .test("fail", \: false)
#
# val results = suite.run()
# expect results.len() == 2
expect true
```

</details>

#### Test execution

#### expect truees when test returns true

- expect truees when test returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expect truees when test returns true")
# val suite = SmokeTestSuite.new()
#     .test("expect trueing", \: true)
#
# val results = suite.run()
# expect results[0].is_expect true()
expect true
```

</details>

#### fails when test returns false

- fails when test returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when test returns false")
# val suite = SmokeTestSuite.new()
#     .test("failing", \: false)
#
# val results = suite.run()
# expect results[0].is_fail()
expect true
```

</details>

#### times out slow tests

- times out slow tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("times out slow tests")
# val config = SmokeTestConfig.default().with(timeout_secs: 1.0)
# val suite = SmokeTestSuite.new(config)
#     .test("slow", \:
#         time.sleep(2.0)
#         true
#     )
#
# val results = suite.run()
# match results[0]:
#     Timeout(_): expect true
#     _: expect false, "Should have timed out"
expect true
```

</details>

#### Retry logic

#### retries failed tests

- retries failed tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retries failed tests")
# var attempt_count = 0
# val config = SmokeTestConfig.default().with(retry_attempts: 3)
#
# val suite = SmokeTestSuite.new(config)
#     .test("flaky", \:
#         attempt_count = attempt_count + 1
#         attempt_count >= 3  # Pass on 3rd attempt
#     )
#
# suite.run()
# expect attempt_count == 3
expect true
```

</details>

#### stops retrying after success

- stops retrying after success


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops retrying after success")
# var attempt_count = 0
# val config = SmokeTestConfig.default().with(retry_attempts: 5)
#
# val suite = SmokeTestSuite.new(config)
#     .test("succeeds early", \:
#         attempt_count = attempt_count + 1
#         attempt_count >= 2  # Pass on 2nd attempt
#     )
#
# suite.run()
# expect attempt_count == 2  # Not all 5 attempts
expect true
```

</details>

#### waits between retries

- waits between retries


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("waits between retries")
# val config = SmokeTestConfig.default().with(
#     retry_attempts: 2,
#     retry_delay_secs: 0.1
# )
#
# val start = time.now()
# val suite = SmokeTestSuite.new(config)
#     .test("failing", \: false)
#
# suite.run()
# val elapsed = time.now() - start
# expect elapsed >= 0.1  # At least one delay
expect true
```

</details>

#### Fail fast

#### stops on first failure when fail_fast is true

- stops on first failure when fail_fast is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops on first failure when fail_fast is true")
# var test2_ran = false
# val config = SmokeTestConfig.default().with(fail_fast: true)
#
# val suite = SmokeTestSuite.new(config)
#     .test("fail", \: false)
#     .test("should not run", \: { test2_ran = true; true })
#
# suite.run()
# expect not test2_ran
expect true
```

</details>

#### runs all tests when fail_fast is false

- runs all tests when fail_fast is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs all tests when fail_fast is false")
# var test2_ran = false
# val config = SmokeTestConfig.default().with(fail_fast: false)
#
# val suite = SmokeTestSuite.new(config)
#     .test("fail", \: false)
#     .test("should run", \: { test2_ran = true; true })
#
# suite.run()
# expect test2_ran
expect true
```

</details>

#### Result checking

#### all_expect trueed returns true when all expect true

- all_expect trueed returns true when all expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all_expect trueed returns true when all expect true")
# val suite = SmokeTestSuite.new()
#     .test("test1", \: true)
#     .test("test2", \: true)
#
# val results = suite.run()
# expect suite.all_expect trueed(results)
expect true
```

</details>

#### all_expect trueed returns false when any fail

- all_expect trueed returns false when any fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all_expect trueed returns false when any fail")
# val suite = SmokeTestSuite.new()
#     .test("expect true", \: true)
#     .test("fail", \: false)
#
# val results = suite.run()
# expect not suite.all_expect trueed(results)
expect true
```

</details>

#### Real-world scenarios

#### HTTP health check

- HTTP health check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HTTP health check")
# val suite = SmokeTestSuite.new()
#     .test("homepage loads", \:
#         val resp = http.get("https://example.com/")
#         resp.status == 200
#     )
#
# val results = suite.run()
# # Would expect true if example.com is up
expect true
```

</details>

#### Database connectivity

- Database connectivity


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Database connectivity")
# val suite = SmokeTestSuite.new()
#     .test("database ping", \:
#         db.ping().is_ok()
#     )
#
# val results = suite.run()
expect true
```

</details>

#### API endpoint

- API endpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("API endpoint")
# val suite = SmokeTestSuite.new()
#     .test("API health", \:
#         val resp = http.get("https://api.example.com/health")
#         resp.status == 200 and resp.body["status"] == "ok"
#     )
#
# val results = suite.run()
expect true
```

</details>

#### Reporting

#### formats Pass result

- formats Pass result


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats Pass result")
# val result = SmokeTestResult::Pass(
#     test_name: "homepage",
#     duration_ms: 123.45
# )
# val formatted = result.format()
# expect formatted.contains("✅")
# expect formatted.contains("homepage")
# expect formatted.contains("123.45")
expect true
```

</details>

#### formats Fail result

- formats Fail result


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats Fail result")
# val result = SmokeTestResult::Fail(
#     test_name: "database",
#     error: "Connection refused",
#     attempt: 3
# )
# val formatted = result.format()
# expect formatted.contains("❌")
# expect formatted.contains("database")
# expect formatted.contains("Connection refused")
expect true
```

</details>

#### formats Timeout result

- formats Timeout result


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats Timeout result")
# val result = SmokeTestResult::Timeout(test_name: "slow_api")
# val formatted = result.format()
# expect formatted.contains("⏱")
# expect formatted.contains("slow_api")
expect true
```

</details>

#### Integration

#### works with deployment pipeline

- works with deployment pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with deployment pipeline")
# # Deploy to staging
# deploy_to_staging("v2.0.0")
#
# # Run smoke tests
# val suite = SmokeTestSuite.new()
#     .test("staging health", \: check_staging())
#
# val results = suite.run()
# if not suite.all_expect trueed(results):
#     rollback_deployment()
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/smoke_test_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Smoke Testing.
- Smoke Testing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ff7736b68d5a8849523084ddb4e956d24ee163f88168b0f7404cb946a4114c6b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ff7736b68d5a8849523084ddb4e956d24ee163f88168b0f7404cb946a4114c6b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ff7736b68d5a8849523084ddb4e956d24ee163f88168b0f7404cb946a4114c6b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/smoke_test_spec.spl
mirror: doc/06_spec/unit/lib/common/smoke_test_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/smoke_test_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/smoke_test_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/smoke_test_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates default config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/smoke_test_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates custom config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/smoke_test_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds tests to suite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
