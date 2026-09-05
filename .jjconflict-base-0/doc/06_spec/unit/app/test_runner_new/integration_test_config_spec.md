# Integration Test Config Specification

> Tests covering Integration Test Config.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration Test Config Specification

## Scenarios

### Integration Test Config

#### loads live values from config/simple.test.sdn

- loads live values from config/simple.test.sdn
   - Expected: find_config_file().ends_with(CONFIG_FILENAME) is true
   - Expected: config.parallel is false
   - Expected: config.timeout_seconds equals `120`
   - Expected: config.cpu_threshold equals `70.0`
   - Expected: config.memory_threshold equals `70.0`
   - Expected: config.throttle_enabled is true
   - Expected: config.run_spec_tests is true
   - Expected: config.run_sdoctests is true
   - Expected: config.run_slow_tests is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads live values from config/simple.test.sdn")
env_set("CI", "")
val config = TestConfig.load()

expect(find_config_file().ends_with(CONFIG_FILENAME)).to_equal(true)
expect(config.parallel).to_equal(false)
expect(config.timeout_seconds).to_equal(120)
expect(config.cpu_threshold).to_equal(70.0)
expect(config.memory_threshold).to_equal(70.0)
expect(config.throttle_enabled).to_equal(true)
expect(config.run_spec_tests).to_equal(true)
expect(config.run_sdoctests).to_equal(true)
expect(config.run_slow_tests).to_equal(false)
```

</details>

#### applies ci overrides after loading file config

- applies ci overrides after loading file config
   - Expected: config.ci_mode is true
   - Expected: config.run_slow_tests is true
   - Expected: config.fail_fast is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies ci overrides after loading file config")
env_set("CI", "true")
val config = TestConfig.load()

expect(config.ci_mode).to_equal(true)
expect(config.run_slow_tests).to_equal(true)
expect(config.fail_fast).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner_new/integration_test_config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Integration Test Config.
- Integration Test Config

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `b16f1111720a10e26dfc93915ac14aaed06fa2604e834be90d1cc0b98b0abbad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b16f1111720a10e26dfc93915ac14aaed06fa2604e834be90d1cc0b98b0abbad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b16f1111720a10e26dfc93915ac14aaed06fa2604e834be90d1cc0b98b0abbad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/test_runner_new/integration_test_config_spec.spl
mirror: doc/06_spec/unit/app/test_runner_new/integration_test_config_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner_new/integration_test_config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner_new/integration_test_config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner_new/integration_test_config_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_runner_new/integration_test_config_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads live values from config/simple.test.sdn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/integration_test_config_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies ci overrides after loading file config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
