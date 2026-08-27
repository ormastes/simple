# Std Benchmark Specification

> Tests covering Benchmarking Library.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Std Benchmark Specification

## Scenarios

### Benchmarking Library

<details>
<summary>Advanced: default config has correct warmup</summary>

#### default config has correct warmup _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- default config has correct warmup
   - Expected: config.warmup_iterations equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("default config has correct warmup")
val config = benchmark_config_default()
expect(config.warmup_iterations).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: default config has correct measurement iterations</summary>

#### default config has correct measurement iterations _(slow)_

- default config has correct measurement iterations
   - Expected: config.measurement_iterations equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("default config has correct measurement iterations")
val config = benchmark_config_default()
expect(config.measurement_iterations).to_equal(100)
```

</details>


</details>

<details>
<summary>Advanced: default config has correct sample size</summary>

#### default config has correct sample size _(slow)_

- default config has correct sample size
   - Expected: config.sample_size equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("default config has correct sample size")
val config = benchmark_config_default()
expect(config.sample_size).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: quick config has warmup of 1</summary>

#### quick config has warmup of 1 _(slow)_

- quick config has warmup of 1
   - Expected: config.warmup_iterations equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("quick config has warmup of 1")
val config = benchmark_config_quick()
expect(config.warmup_iterations).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: quick config has sample size of 3</summary>

#### quick config has sample size of 3 _(slow)_

- quick config has sample size of 3
   - Expected: config.sample_size equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("quick config has sample size of 3")
val config = benchmark_config_quick()
expect(config.sample_size).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: custom config has correct sample size</summary>

#### custom config has correct sample size _(slow)_

- custom config has correct sample size
   - Expected: config.sample_size equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("custom config has correct sample size")
val config = BenchmarkConfig(
    warmup_iterations: 1,
    measurement_iterations: 50,
    sample_size: 5,
    outlier_threshold: 1.5
)
expect(config.sample_size).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats nanoseconds</summary>

#### format_time formats nanoseconds _(slow)_

- format_time formats nanoseconds
   - Expected: has_ns is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("format_time formats nanoseconds")
val result = format_time(500.0)
val has_ns = _text_contains(result, "ns")
expect(has_ns).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats microseconds</summary>

#### format_time formats microseconds _(slow)_

- format_time formats microseconds
   - Expected: has_us is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("format_time formats microseconds")
val result = format_time(1500.0)
val has_us = _text_contains(result, "us")
expect(has_us).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats milliseconds</summary>

#### format_time formats milliseconds _(slow)_

- format_time formats milliseconds
   - Expected: has_ms is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("format_time formats milliseconds")
val result = format_time(1500000.0)
val has_ms = _text_contains(result, "ms")
expect(has_ms).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats seconds</summary>

#### format_time formats seconds _(slow)_

- format_time formats seconds
   - Expected: has_s is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("format_time formats seconds")
val result = format_time(1500000000.0)
val has_s = _text_contains(result, "s")
expect(has_s).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/std_benchmark_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Benchmarking Library.
- Benchmarking Library

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5677356fcb6c1bcbfa4318e07ce52ff041dc0aa32663d80496f6972a6734d70c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5677356fcb6c1bcbfa4318e07ce52ff041dc0aa32663d80496f6972a6734d70c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5677356fcb6c1bcbfa4318e07ce52ff041dc0aa32663d80496f6972a6734d70c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/05_perf/std_benchmark_spec.spl
mirror: doc/06_spec/05_perf/std_benchmark_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/std_benchmark_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/std_benchmark_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/std_benchmark_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/std_benchmark_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default config has correct warmup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/std_benchmark_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default config has correct measurement iterations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/std_benchmark_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default config has correct sample size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
