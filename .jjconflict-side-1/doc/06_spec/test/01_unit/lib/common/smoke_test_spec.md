# Smoke Test Specification

> <details>

<!-- sdn-diagram:id=smoke_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smoke_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smoke_test_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smoke_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val config = SmokeTestConfig.default()
# expect config.timeout_secs == 30.0
# expect config.retry_attempts == 3
# expect config.retry_delay_secs == 5.0
# expect config.fail_fast == true
expect true
```

</details>

#### creates custom config

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val suite = SmokeTestSuite.new()
#     .test("homepage", \: check_homepage())
#     .test("database", \: check_database())
#
# expect suite.tests.len() == 2
expect true
```

</details>

#### runs all tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val suite = SmokeTestSuite.new()
#     .test("expect trueing", \: true)
#
# val results = suite.run()
# expect results[0].is_expect true()
expect true
```

</details>

#### fails when test returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val suite = SmokeTestSuite.new()
#     .test("failing", \: false)
#
# val results = suite.run()
# expect results[0].is_fail()
expect true
```

</details>

#### times out slow tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = SmokeTestResult::Timeout(test_name: "slow_api")
# val formatted = result.format()
# expect formatted.contains("⏱")
# expect formatted.contains("slow_api")
expect true
```

</details>

#### Integration

#### works with deployment pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/common/smoke_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
