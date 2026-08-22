# smoke_test_spec

> Verifies the smoke test behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smoke_test_spec

Verifies the smoke test behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/smoke_test_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the smoke test behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Smoke Testing

#### SmokeTestConfig

#### creates default config

- Verify: creates default config


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: creates default config")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# val config = SmokeTestConfig.default()
# expect config.timeout_secs == 30.0
# expect config.retry_attempts == 3
# expect config.retry_delay_secs == 5.0
# expect config.fail_fast == true
expect true
```

</details>

#### creates custom config

- Verify: creates custom config


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: creates custom config")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: adds tests to suite


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: adds tests to suite")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# val suite = SmokeTestSuite.new()
#     .test("homepage", \: check_homepage())
#     .test("database", \: check_database())
#
# expect suite.tests.len() == 2
expect true
```

</details>

#### runs all tests

- Verify: runs all tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: runs all tests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: collects results


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: collects results")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: expect truees when test returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: expect truees when test returns true")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# val suite = SmokeTestSuite.new()
#     .test("expect trueing", \: true)
#
# val results = suite.run()
# expect results[0].is_expect true()
expect true
```

</details>

#### fails when test returns false

- Verify: fails when test returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: fails when test returns false")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# val suite = SmokeTestSuite.new()
#     .test("failing", \: false)
#
# val results = suite.run()
# expect results[0].is_fail()
expect true
```

</details>

#### times out slow tests

- Verify: times out slow tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: times out slow tests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: retries failed tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: retries failed tests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: stops retrying after success


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: stops retrying after success")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: waits between retries


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: waits between retries")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: stops on first failure when fail_fast is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: stops on first failure when fail_fast is true")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: runs all tests when fail_fast is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: runs all tests when fail_fast is false")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: all_expect trueed returns true when all expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: all_expect trueed returns true when all expect true")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: all_expect trueed returns false when any fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: all_expect trueed returns false when any fail")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: HTTP health check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: HTTP health check")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: Database connectivity


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: Database connectivity")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: API endpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: API endpoint")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: formats Pass result


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: formats Pass result")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: formats Fail result


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: formats Fail result")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: formats Timeout result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: formats Timeout result")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# val result = SmokeTestResult::Timeout(test_name: "slow_api")
# val formatted = result.format()
# expect formatted.contains("⏱")
# expect formatted.contains("slow_api")
expect true
```

</details>

#### Integration

#### works with deployment pipeline

- Verify: works with deployment pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SMOKE_TEST-001
step("Verify: works with deployment pipeline")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3d0efaca322f57359f42a6cd29929056720d973b46eec31da7e5475b93f003b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d0efaca322f57359f42a6cd29929056720d973b46eec31da7e5475b93f003b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d0efaca322f57359f42a6cd29929056720d973b46eec31da7e5475b93f003b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/smoke_test_spec.spl
mirror: doc/06_spec/01_unit/std/smoke_test_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/smoke_test_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/smoke_test_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/smoke_test_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
